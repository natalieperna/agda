{-# LANGUAGE CPP, PatternGuards #-}

module Agda.Compiler.MAlonzo.Compiler where

#if __GLASGOW_HASKELL__ <= 708
import Prelude hiding (foldl, mapM_, mapM, sequence, concat)
#endif

import Control.Applicative
import Control.Monad.Reader hiding (mapM_, forM_, mapM, forM, sequence)
import Control.Monad.State  hiding (mapM_, forM_, mapM, forM, sequence)

import Data.Generics.Geniplate
import Data.Foldable hiding (any, all, foldr, sequence_)
import Data.Function
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable hiding (for)
import Data.Monoid hiding ((<>))

import Numeric.IEEE

import qualified Agda.Utils.Haskell.Syntax as HS

import System.Directory (createDirectoryIfMissing)
import System.FilePath hiding (normalise)

import Agda.Compiler.CallCompiler
import Agda.Compiler.Common
import Agda.Compiler.MAlonzo.Misc
import Agda.Compiler.MAlonzo.Pretty
import Agda.Compiler.MAlonzo.Primitives
import Agda.Compiler.MAlonzo.HaskellTypes
import Agda.Compiler.MAlonzo.Pragmas
import Agda.Compiler.ToTreeless
import Agda.Compiler.Treeless.Unused
import Agda.Compiler.Treeless.Erase
import Agda.Compiler.Treeless.SplitPLet
import Agda.Compiler.Backend

import Agda.Interaction.FindFile
import Agda.Interaction.Imports
import Agda.Interaction.Options

import Agda.Syntax.Common
import Agda.Syntax.Fixity
import qualified Agda.Syntax.Abstract.Name as A
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Internal as I
import Agda.Syntax.Internal.Names (namesIn)
import qualified Agda.Syntax.Treeless as T
import Agda.Syntax.Literal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Level (reallyUnLevelView)

import Agda.TypeChecking.CompiledClause

import Agda.Utils.FileName
import Agda.Utils.Functor
import Agda.Utils.IO.Directory
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Pretty (prettyShow, Pretty)
import qualified Agda.Utils.IO.UTF8 as UTF8
import qualified Agda.Utils.HashMap as HMap
import Agda.Utils.Singleton
import Agda.Utils.Tuple

import Paths_Agda

#include "undefined.h"
import Agda.Utils.Impossible

-- The backend callbacks --------------------------------------------------

ghcBackend :: Backend
ghcBackend = Backend ghcBackend'

ghcBackend' :: Backend' GHCOptions GHCOptions GHCModuleEnv IsMain [HS.Decl]
ghcBackend' = Backend'
  { backendName           = "GHC"
  , backendVersion        = Nothing
  , options               = defaultGHCOptions
  , commandLineFlags      = ghcCommandLineFlags
  , isEnabled             = optGhcCompile
  , preCompile            = ghcPreCompile
  , postCompile           = ghcPostCompile
  , preModule             = ghcPreModule
  , postModule            = ghcPostModule
  , compileDef            = ghcCompileDef
  , scopeCheckingSuffices = False
  }

--- Options ---

data GHCOptions = GHCOptions
  { optGhcCompile :: Bool
  , optGhcCallGhc :: Bool
  , optGhcFlags   :: [String]
  , optGhcGeneratePatternLet :: Bool
  }

defaultGHCOptions :: GHCOptions
defaultGHCOptions = GHCOptions
  { optGhcCompile = False
  , optGhcCallGhc = True
  , optGhcFlags   = []
  , optGhcGeneratePatternLet = False
  }

ghcCommandLineFlags :: [OptDescr (Flag GHCOptions)]
ghcCommandLineFlags =
    [ Option ['c']  ["compile", "ghc"] (NoArg enable)
                    "compile program using the GHC backend"
    , Option []     ["ghc-dont-call-ghc"] (NoArg dontCallGHC)
                    "don't call GHC, just write the GHC Haskell files."
    , Option []     ["ghc-flag"] (ReqArg ghcFlag "GHC-FLAG")
                    "give the flag GHC-FLAG to GHC"
    , Option []     ["ghc-generate-pattern-let"] (NoArg genPLet)
                    "make the GHC backend generate pattern lets"
    ]
  where
    enable      o = pure o{ optGhcCompile = True }
    dontCallGHC o = pure o{ optGhcCallGhc = False }
    ghcFlag f   o = pure o{ optGhcFlags   = optGhcFlags o ++ [f] }
    genPLet     o = pure o{ optGhcGeneratePatternLet = True }

--- Top-level compilation ---

ghcPreCompile :: GHCOptions -> TCM GHCOptions
ghcPreCompile ghcOpts = do
  allowUnsolved <- optAllowUnsolved <$> pragmaOptions
  when allowUnsolved $ genericError $ "Unsolved meta variables are not allowed when compiling."
  return ghcOpts

ghcPostCompile :: GHCOptions -> IsMain -> Map ModuleName IsMain -> TCM ()
ghcPostCompile opts isMain mods = copyRTEModules >> callGHC opts isMain mods

--- Module compilation ---

type GHCModuleEnv = Maybe CoinductionKit

ghcPreModule :: GHCOptions -> ModuleName -> FilePath -> TCM (Recompile GHCModuleEnv IsMain)
ghcPreModule _ m ifile = ifM uptodate noComp yesComp
  where
    uptodate = liftIO =<< isNewerThan <$> outFile_ <*> pure ifile

    noComp = do
      reportSLn "compile.ghc" 2 . (++ " : no compilation is needed.") . show . A.mnameToConcrete =<< curMName
      Skip . hasMainFunction <$> curIF

    yesComp = do
      m   <- show . A.mnameToConcrete <$> curMName
      out <- outFile_
      reportSLn "compile.ghc" 1 $ repl [m, ifile, out] "Compiling <<0>> in <<1>> to <<2>>"
      stImportedModules .= Set.empty  -- we use stImportedModules to accumulate the required Haskell imports
      Recompile <$> coinductionKit

ghcPostModule :: GHCOptions -> GHCModuleEnv -> IsMain -> ModuleName -> [[HS.Decl]] -> TCM IsMain
ghcPostModule _ _ _ _ defs = do
  m      <- curHsMod
  imps   <- imports
  code   <- inlineHaskell
  hsImps <- haskellImports
  writeModule $ HS.Module m [] imps (map fakeDecl (hsImps ++ code) ++ concat defs)
  hasMainFunction <$> curIF

ghcCompileDef :: GHCOptions -> GHCModuleEnv -> Definition -> TCM [HS.Decl]
ghcCompileDef = definition

-- Compilation ------------------------------------------------------------

--------------------------------------------------
-- imported modules
--   I use stImportedModules in a non-standard way,
--   accumulating in it what are acutally used in Misc.xqual
--------------------------------------------------

imports :: TCM [HS.ImportDecl]
imports = (hsImps ++) <$> imps where
  hsImps :: [HS.ImportDecl]
  hsImps = [unqualRTE, decl mazRTE]

  unqualRTE :: HS.ImportDecl
  unqualRTE = HS.ImportDecl mazRTE False $ Just $
              (False, [ HS.IVar $ HS.Ident x
                      | x <- [mazCoerceName, mazErasedName] ++
                             map treelessPrimName [T.PAdd, T.PSub, T.PMul, T.PQuot, T.PRem, T.PGeq, T.PLt, T.PEqI, T.PEqF] ])

  imps :: TCM [HS.ImportDecl]
  imps = List.map decl . uniq <$>
           ((++) <$> importsForPrim <*> (List.map mazMod <$> mnames))

  decl :: HS.ModuleName -> HS.ImportDecl
  decl m = HS.ImportDecl m True Nothing

  mnames :: TCM [ModuleName]
  mnames = Set.elems <$> use stImportedModules

  uniq :: [HS.ModuleName] -> [HS.ModuleName]
  uniq = List.map head . List.group . List.sort

--------------------------------------------------
-- Main compiling clauses
--------------------------------------------------

-- | Note that the INFINITY, SHARP and FLAT builtins are translated as
-- follows (if a 'CoinductionKit' is given):
--
-- @
--   type Infinity a b = b
--
--   sharp :: a -> a
--   sharp x = x
--
--   flat :: a -> a
--   flat x = x
-- @

definition :: GHCOptions -> Maybe CoinductionKit -> Definition -> TCM [HS.Decl]
-- ignore irrelevant definitions
{- Andreas, 2012-10-02: Invariant no longer holds
definition _ kit (Defn Forced{}  _ _  _ _ _ _ _ _) = __IMPOSSIBLE__
definition _ kit (Defn UnusedArg _ _  _ _ _ _ _ _) = __IMPOSSIBLE__
definition _ kit (Defn NonStrict _ _  _ _ _ _ _ _) = __IMPOSSIBLE__
-}
definition _ kit Defn{defArgInfo = info, defName = q} | isIrrelevant info = do
  reportSDoc "compile.ghc.definition" 10 $
    text "Not compiling" <+> prettyTCM q <> text "."
  return []
definition ghcOpts kit Defn{defName = q, defType = ty, theDef = d} = do
  reportSDoc "compile.ghc.definition" 10 $ vcat
    [ text "Compiling" <+> prettyTCM q <> text ":"
    , nest 2 $ text (show d)
    ]
  pragma <- getHaskellPragma q
  checkTypeOfMain q ty $ do
    infodecl q <$> case d of

      _ | Just (HsDefn r hs) <- pragma -> setCurrentRange r $ do
        -- Make sure we have imports for all names mentioned in the type.
        hsty <- haskellType q
        ty   <- normalise ty
        sequence_ [ xqual x (HS.Ident "_") | x <- Set.toList (namesIn ty) ]

        -- Check that the function isn't INLINE (since that will make this
        -- definition pointless).
        inline <- (^. funInline) . theDef <$> getConstInfo q
        when inline $ warning $ UselessInline q

        return $ fbWithType hsty (fakeExp hs)

      -- Special treatment of coinductive builtins.
      Datatype{} | Just q == (nameOfInf <$> kit) -> do
        let infT = unqhname "T" q
            infV = unqhname dPrefix q
            a    = ihname "a" 0
            b    = ihname "a" 1
            vars = [a, b]
        return [ HS.TypeDecl infT
                             (List.map HS.UnkindedVar vars)
                             (HS.TyVar b)
               , HS.FunBind [HS.Match infV
                                      (List.map HS.PVar vars)
                                      (HS.UnGuardedRhs HS.unit_con)
                                      emptyBinds]
               ]
      Constructor{} | Just q == (nameOfSharp <$> kit) -> do
        let sharp = unqhname dPrefix q
            x     = ihname "x" 0
        return $
          [ HS.TypeSig [sharp] $ fakeType $
              "forall a. a -> a"
          , HS.FunBind [HS.Match sharp
                                 [HS.PVar x]
                                 (HS.UnGuardedRhs (HS.Var (HS.UnQual x)))
                                 emptyBinds]
          ]
      Function{} | Just q == (nameOfFlat <$> kit) -> do
        let flat = unqhname dPrefix q
            x    = ihname "x" 0
        return $
          [ HS.TypeSig [flat] $ fakeType $
              "forall a. a -> a"
          , HS.FunBind [HS.Match flat
                                 [HS.PVar x]
                                 (HS.UnGuardedRhs (HS.Var (HS.UnQual x)))
                                 emptyBinds]
          ]

      Axiom{} -> return $ fb axiomErr
      Primitive{ primName = s } -> fb <$> primBody s

      Function{} -> function pragma $ functionViaTreeless q

      Datatype{ dataPars = np, dataIxs = ni, dataClause = cl, dataCons = cs }
        | Just (HsData r ty hsCons) <- pragma -> setCurrentRange r $ do
        computeErasedConstructorArgs q
        ccscov <- constructorCoverageCode q (np + ni) cs ty hsCons
        return $ tvaldecl q (dataInduction d) 0 (np + ni) [] (Just __IMPOSSIBLE__) ++ ccscov
      Datatype{ dataPars = np, dataIxs = ni, dataClause = cl, dataCons = cs } -> do
        computeErasedConstructorArgs q
        (ars, cds) <- unzip <$> mapM condecl cs
        return $ tvaldecl q (dataInduction d) (List.maximum (np:ars) - np) (np + ni) cds cl
      Constructor{} -> return []
      Record{ recPars = np, recClause = cl, recConHead = con }
        | Just (HsData r ty hsCons) <- pragma -> setCurrentRange r $ do
        let cs = [conName con]
        computeErasedConstructorArgs q
        ccscov <- constructorCoverageCode q np cs ty hsCons
        return $ tvaldecl q Inductive 0 np [] (Just __IMPOSSIBLE__) ++ ccscov
      Record{ recClause = cl, recConHead = con, recFields = flds } -> do
        computeErasedConstructorArgs q
        let c = conName con
        let noFields = length flds
        let ar = I.arity ty
        cd <- snd <$> condecl c
        return $ tvaldecl q Inductive noFields ar [cd] cl
      AbstractDefn -> __IMPOSSIBLE__
  where
  function :: Maybe HaskellPragma -> TCM [HS.Decl] -> TCM [HS.Decl]
  function mhe fun = do
    ccls <- mkwhere <$> fun
    case mhe of
      Just (HsExport r name) -> do
        t <- setCurrentRange r $ haskellType q
        let tsig :: HS.Decl
            tsig = HS.TypeSig [HS.Ident name] (fakeType t)

            def :: HS.Decl
            def = HS.FunBind [HS.Match (HS.Ident name) [] (HS.UnGuardedRhs (hsVarUQ $ dname q)) emptyBinds]
        return ([tsig,def] ++ ccls)
      _ -> return ccls

  functionViaTreeless :: QName -> TCM [HS.Decl]
  functionViaTreeless q = caseMaybeM (toTreeless q) (pure []) $ \ treeless -> do

    used <- getCompiledArgUse q
    let dostrip = any not used

    e <- if dostrip then closedTerm ghcOpts (stripUnusedArguments used treeless)
                    else closedTerm ghcOpts treeless
    let (ps, b) = lamView e
        lamView :: HS.Exp -> ([HS.Pat], HS.Exp)
        lamView = h id
          where
            h acc e = case stripTopCoerce e of
              HS.Lambda ps b -> h (acc . (ps ++)) b
              b                -> (acc [], b)
        stripTopCoerce (HS.Lambda ps b) = HS.Lambda ps $ stripTopCoerce b
        stripTopCoerce e =
          case hsAppView e of
            [c,  e] | c == mazCoerce -> e
            _                        -> e

        funbind f ps b = HS.FunBind [HS.Match f ps (HS.UnGuardedRhs b) emptyBinds]

    -- The definition of the non-stripped function
    (ps0, _) <- lamView <$> closedTerm ghcOpts (foldr ($) T.TErased $ replicate (length used) T.TLam)
    let b0 = foldl HS.App (hsVarUQ $ duname q) [ hsVarUQ x | (~(HS.PVar x), True) <- zip ps0 used ]

    doAbstractPLet <- optAbstractPLet <$> commandLineOptions
    mCCF <- if doAbstractPLet then getCrossCallFloat q else return Nothing
    let patVars :: HS.Pat -> [HS.Name] -> [HS.Name] -- difference list
        patVars (HS.PVar v) = (v :)
        patVars (HS.PLit _) = id
        patVars (HS.PAsPat v p) = (v :) . patVars p
        patVars HS.PWildCard = id
        patVars (HS.PBangPat p) = patVars p
        patVars (HS.PApp _c ps) = foldr patVars `flip` ps
        patVars (HS.PatTypeSig p _ty) = patVars p
        patVars (HS.PIrrPat p) = patVars p
        patExpr :: HS.Pat -> HS.Exp
        patExpr (HS.PVar v) = HS.Var $ HS.UnQual v
        patExpr (HS.PLit lit) = HS.Lit lit
        patExpr (HS.PAsPat v p) = HS.Var $ HS.UnQual v
        patExpr HS.PWildCard = __IMPOSSIBLE__
        patExpr (HS.PBangPat p) = patExpr p
        patExpr (HS.PApp c ps) = foldl (\ f p -> HS.App f $ patExpr p) (HS.Var c) ps
        patExpr (HS.PatTypeSig p ty) = HS.ExpTypeSig (patExpr p) ty
        patExpr (HS.PIrrPat p) = patExpr p
    let pbindsView :: [HS.Decl] -> ([HS.Name], [HS.Decl], [HS.Decl])
        pbindsView = h id id
            where
               h accv accp (HS.TypeSig _ _ : binds) = h accv accp binds
                 -- \edcomm{WK}{In principle it would be better to keep |TypeSig|s.}
               h accv accp (pb@(HS.PatBind pat _ _) : binds)
                 = h (accv . patVars pat) (accp . (pb :)) binds
               h accv accp binds
                 | Just ((name, e) , binds') <- hsVarBindView binds
                 = h (accv . (name :)) (accp . (hsVarBind name e :)) binds'
                 | otherwise = (accv [], accp [], binds)

        pletView :: HS.Exp -> ([HS.Name], [HS.Decl], HS.Exp)
        pletView = h id id id
          where
            h accv accp accb e = case stripTopCoerce e of
              HS.ExpTypeSig e _ty -> h accv accp accb e
              HS.Let (HS.BDecls ds) b
                | (pvars, pbinds, binds') <- pbindsView ds
                -> h (accv . (pvars ++))
                     (accp . (pbinds ++))
                     (accb . (if null binds' then id
                              else HS.Let (HS.BDecls binds')))
                     b
              _ -> (accv [], accp [], accb e)
    let mdv = case mCCF of
            Nothing -> Nothing
            Just ccf -> let
              (hspvars, hspbinds, hsbody) = pletView b
              qdv = dvname q
              dvcall = case stripTopCoerce hsbody of
                 HS.Var (HS.UnQual v) | v `elem` foldr patVars hspvars ps -> hsbody
                 _ -> foldl  (\ f p -> HS.App f $ patExpr p) (HS.Var $ HS.UnQual qdv)
                             $ ps ++ map HS.PVar hspvars
              dvbinding = funbind qdv (ps ++ map HS.PVar hspvars) hsbody
              dubody = foldr (\ b -> HS.Let (HS.BDecls [b])) dvcall hspbinds
             in Just (dubody, dvbinding)
    return $ case mdv of
      Nothing -> if dostrip
        then [ funbind (dname q) ps0 b0
             , funbind (duname q) ps b ]
        else [ funbind (dname q) ps b ]
      Just (dubody, dvbinding) -> if dostrip
        then [ funbind (dname q) ps0 b0
             , funbind (duname q) ps dubody
             , dvbinding ]
        else [ funbind (dname q) ps dubody
             , dvbinding ]

  mkwhere :: [HS.Decl] -> [HS.Decl]
  mkwhere (HS.FunBind [m0, HS.Match dn ps rhs emptyBinds] : fbs@(_:_)) =
          [HS.FunBind [m0, HS.Match dn ps rhs bindsAux]]
    where
    bindsAux :: Maybe HS.Binds
    bindsAux = Just $ HS.BDecls fbs

  mkwhere fbs = fbs

  fbWithType :: HaskellType -> HS.Exp -> [HS.Decl]
  fbWithType ty e =
    [ HS.TypeSig [unqhname dPrefix q] $ fakeType ty ] ++ fb e

  fb :: HS.Exp -> [HS.Decl]
  fb e  = [HS.FunBind [HS.Match (unqhname dPrefix q) []
                                (HS.UnGuardedRhs $ e) emptyBinds]]

  axiomErr :: HS.Exp
  axiomErr = rtmError $ "postulate evaluated: " ++ show (A.qnameToConcrete q)

constructorCoverageCode :: QName -> Int -> [QName] -> HaskellType -> [HaskellCode] -> TCM [HS.Decl]
constructorCoverageCode q np cs hsTy hsCons = do
  checkConstructorCount q cs hsCons
  ifM (noCheckCover q) (return []) $ do
    ccs <- List.concat <$> zipWithM checkConstructorType cs hsCons
    cov <- checkCover q hsTy np cs hsCons
    return $ ccs ++ cov

-- | Environment for naming of local variables.
--   Invariant: @reverse ccCxt ++ ccNameSupply@
data CCEnv = CCEnv
  { ccNameSupply :: NameSupply  -- ^ Supply of fresh names
  , ccCxt        :: CCContext   -- ^ Names currently in scope
  , ccGenPLet    :: Bool        -- ^ From optGhcGeneratePatternLet
  }

type NameSupply = [HS.Name]
type CCContext  = [HS.Name]

mapNameSupply :: (NameSupply -> NameSupply) -> CCEnv -> CCEnv
mapNameSupply f e = e { ccNameSupply = f (ccNameSupply e) }

mapContext :: (CCContext -> CCContext) -> CCEnv -> CCEnv
mapContext f e = e { ccCxt = f (ccCxt e) }

-- | Initial environment for expression generation.
initCCEnv :: GHCOptions -> CCEnv
initCCEnv ghcOpts = CCEnv
  { ccNameSupply = map (ihname "v") [0..]  -- DON'T CHANGE THESE NAMES!
  , ccCxt        = []
  , ccGenPLet    = optGhcGeneratePatternLet ghcOpts
  }

-- | Term variables are de Bruijn indices.
lookupIndex :: Int -> CCContext -> HS.Name
lookupIndex i xs = fromMaybe __IMPOSSIBLE__ $ xs !!! i

type CC = ReaderT CCEnv TCM

freshNames :: Int -> ([HS.Name] -> CC a) -> CC a
freshNames n _ | n < 0 = __IMPOSSIBLE__
freshNames n cont = do
  (xs, rest) <- splitAt n <$> asks ccNameSupply
  local (mapNameSupply (const rest)) $ cont xs

-- | Introduce n variables into the context.
intros :: Int -> ([HS.Name] -> CC a) -> CC a
intros n cont = freshNames n $ \xs ->
  local (mapContext (reverse xs ++)) $ cont xs

checkConstructorType :: QName -> HaskellCode -> TCM [HS.Decl]
checkConstructorType q hs = do
  ty <- haskellType q
  return [ HS.TypeSig [unqhname "check" q] $ fakeType ty
         , HS.FunBind [HS.Match (unqhname "check" q) []
                                (HS.UnGuardedRhs $ fakeExp hs) emptyBinds]
         ]

checkCover :: QName -> HaskellType -> Nat -> [QName] -> [HaskellCode] -> TCM [HS.Decl]
checkCover q ty n cs hsCons = do
  let tvs = [ "a" ++ show i | i <- [1..n] ]
      makeClause c hsc = do
        a <- erasedArity c
        let pat = HS.PApp (HS.UnQual $ HS.Ident hsc) $ replicate a HS.PWildCard
        return $ HS.Alt pat (HS.UnGuardedRhs $ HS.unit_con) emptyBinds

  cs <- zipWithM makeClause cs hsCons
  let rhs = case cs of
              [] -> fakeExp "()" -- There is no empty case statement in Haskell
              _  -> HS.Case (HS.Var $ HS.UnQual $ HS.Ident "x") cs

  return [ HS.TypeSig [unqhname "cover" q] $ fakeType $ unwords (ty : tvs) ++ " -> ()"
         , HS.FunBind [HS.Match (unqhname "cover" q) [HS.PVar $ HS.Ident "x"]
                                (HS.UnGuardedRhs rhs) emptyBinds]
         ]

closedTerm :: GHCOptions -> T.TTerm -> TCM HS.Exp
closedTerm ghcOpts v = hsCast <$> term v `runReaderT` initCCEnv ghcOpts

-- For export to MAlonzo.Primitives via MAlonzo/Compiler.hs-boot
closedTerm' :: T.TTerm -> TCM HS.Exp
closedTerm' = closedTerm defaultGHCOptions

-- | In @addAsPats xs numBound tp pat@, recurse through @tp@ to find all
--   single constructor @TCase@s and replace @PVar@s of the same scrutinee
--   with appropriate @PAsPat@s, until @TErased@ is reached.
--   @xs@ contains all necessary variables introduce by the initial call
--   in @term@, with @numBound@ indicating the number of introduced
--   of variables introduced by the caller used in @PApp@s and the top let.
addAsPats :: [HS.Name] -> Nat -> TTerm -> HS.Pat -> CC HS.Pat
addAsPats xs numBound
  tp@(TCase sc _ _ [TACon c cArity tp'])
  pat = case xs !!! (numBound - 1 - sc) of
    Just scName -> do
      erased <- lift $ getErasedConArgs c
      hConNm <- lift $ conhqn c
      let oldPat = HS.PVar scName
      let vars = take cArity $ drop numBound xs
      let newPat = HS.PAsPat scName $ HS.PApp hConNm $ map HS.PVar [ x | (x, False) <- zip vars erased ]
      let pat' = replacePats oldPat newPat pat
      addAsPats xs (numBound + cArity) tp' pat'
    Nothing -> __IMPOSSIBLE__
addAsPats _ _ TErased pat = return pat
addAsPats _ _ _ _ = __IMPOSSIBLE__ -- Guaranteed by splitPLet

-- | In @replacePats old new p@, replace all instances of @old@ in @p@
--   with @new@
replacePats :: HS.Pat -> HS.Pat -> HS.Pat -> HS.Pat
replacePats old new p@(HS.PVar _) = if old == p then new else p
replacePats old new (HS.PAsPat sc p) = HS.PAsPat sc $ replacePats old new p
replacePats old new p@(HS.PApp q pats) =
  HS.PApp q $ map (replacePats old new) pats
replacePats _ _ p = __IMPOSSIBLE__ -- Guaranteed by addAsPats

-- | Extract Agda term to Haskell expression.
--   Erased arguments are extracted as @()@.
--   Types are extracted as @()@.
term :: T.TTerm -> CC HS.Exp
term tm0 = asks ccGenPLet >>= \ genPLet -> case tm0 of
  T.TVar i -> do
    x <- lookupIndex i <$> asks ccCxt
    return $ hsVarUQ x
  T.TApp (T.TDef variant f) ts -> do
    used <- lift $ getCompiledArgUse f
    isCompiled <- lift $ isJust <$> getHaskellPragma f  -- #2248: no unused argument pruning for COMPILE'd functions
    let given   = length ts
        needed  = length used
        missing = drop given used
    (prefix, us) <- case variant of
          T.TDefDefault | and used -> return (dPrefix, [])
          T.TDefDefault            -> return (duPrefix, [])
          T.TDefAbstractPLet _ -> return (dvPrefix, [])
            -- intros k $ \ ns -> return (dvPrefix, map (HS.Var . HS.UnQual) ns)
    lift $ reportSDoc "treeless.opt.float.ccf" 50
      $ text ("-- MAlonzo.term : TDef " ++ shows variant (' ' : show f))
      $$ nest 4 (vcat
        [ text "ts = " <+> nest 7 (vcat $ map pretty ts)
        , text "used = " <+> nest 7 (pretty used)
        , text "missing = " <+> nest 10 (pretty missing)
        , text ("not isCompiled && any not used = " ++ show (not isCompiled && any not used))
        , text "tm0 = " <+> nest 6 (pretty tm0)
        ])
    if not isCompiled && any not used
      then if any not missing then term (etaExpand (needed - given) tm0) else do
        f <- lift $ HS.Var <$> xhqn prefix f  -- used stripped function
        -- flip (foldl HS.App) us <$>
        (f `apps` [ t | (t, True) <- zip ts $ used ++ repeat True ])
      else do
        t' <- term (T.TDef variant f)
        t' `apps` ts
  T.TApp (T.TCon c) ts -> do
    kit <- lift coinductionKit
    if Just c == (nameOfSharp <$> kit)
      then do
        t' <- HS.Var <$> lift (xhqn dPrefix c)
        apps t' ts
      else do
        (ar, _) <- lift $ conArityAndPars c
        erased  <- lift $ getErasedConArgs c
        let missing = drop (length ts) erased
            notErased = not
        case all notErased missing of
          False -> term $ etaExpand (length missing) tm0
          True  -> do
            f <- lift $ HS.Con <$> conhqn c
            f `apps` [ t | (t, False) <- zip ts erased ]
  T.TApp t ts -> do
    t' <- term t
    t' `apps` ts
  T.TLam at -> do
    (nm:_) <- asks ccNameSupply
    intros 1 $ \ [x] ->
      hsLambda [HS.PVar x] <$> term at

  TLet _ (TCase 0 _ _ [TACon _ _ _])
    | genPLet
    , Just (PLet {pletNumBinders = numBinders, eTerm = TLet t1 tp}, tb) <- splitPLet tm0
    -> do
        t1' <- term t1
        intros 1 $ \[x] -> do
          intros numBinders $ \xs -> do
            tb' <- term tb
            p <- addAsPats (x:xs) 1 tp (HS.PVar x)
            return $ hsPLet p (hsCast t1') tb'

  T.TLet t1 t2 -> do
    t1' <- term t1
    intros 1 $ \[x] -> do
      t2' <- term t2
      return $ hsLet x (hsCast t1') t2'

  T.TCase sc ct def alts -> do
    sc' <- term (T.TVar sc)
    alts' <- traverse (alt sc) alts
    def' <- term def
    let defAlt = HS.Alt HS.PWildCard (HS.UnGuardedRhs def') emptyBinds

    return $ HS.Case (hsCast sc') (alts' ++ [defAlt])

  T.TLit l -> return $ literal l
  T.TDef variant q -> do
    isCompiled <- lift $ isJust <$> getHaskellPragma q
    if True -- isCompiled
    then do
      -- case variant of
      --   T.TDefAbstractPLet vs -> lift $ do
      --     reportSDoc "treeless.opt.float.codegen" 30 $ text ("-- TDefAbstractPLet isCompiled: " ++ show q)
      --   _ -> return ()
      HS.Var <$> (lift $ xhqn dPrefix q)
    else term (T.TApp tm0 [])
  T.TCon q   -> term (T.TApp (T.TCon q) [])
  T.TPrim p  -> return $ compilePrim p
  T.TUnit    -> return HS.unit_con
  T.TSort    -> return HS.unit_con
  T.TErased  -> return $ hsVarUQ $ HS.Ident mazErasedName
  T.TError e -> return $ case e of
    T.TUnreachable ->  rtmUnreachableError
  where apps =  foldM (\ h a -> HS.App h <$> term a)
        etaExpand n t =
          foldr (const T.TLam)
                (T.mkTApp (raise n t) [T.TVar i | i <- [n - 1, n - 2..0]])
                (replicate n ())


compilePrim :: T.TPrim -> HS.Exp
compilePrim s = HS.Var $ hsName $ treelessPrimName s

alt :: Int -> T.TAlt -> CC HS.Alt
alt sc a = do
  case a of
    T.TACon {T.aCon = c} -> do
      intros (T.aArity a) $ \ xs -> do
        erased <- lift $ getErasedConArgs c
        hConNm <- lift $ conhqn c
        mkAlt (HS.PApp hConNm $ map HS.PVar [ x | (x, False) <- zip xs erased ])
    T.TAGuard g b -> do
      g <- term g
      b <- term b
      return $ HS.Alt HS.PWildCard
                      (HS.GuardedRhss [HS.GuardedRhs [HS.Qualifier g] b])
                      emptyBinds
    T.TALit { T.aLit = LitQName _ q } -> mkAlt (litqnamepat q)
    T.TALit { T.aLit = l@LitFloat{},   T.aBody = b } -> mkGuarded (treelessPrimName T.PEqF) (literal l) b
    T.TALit { T.aLit = LitString _ s , T.aBody = b } -> mkGuarded "(==)" (litString s) b
    T.TALit {} -> mkAlt (HS.PLit $ hslit $ T.aLit a)
  where
    mkGuarded eq lit b = do
      b  <- term b
      sc <- term (T.TVar sc)
      let guard =
            HS.Var (HS.UnQual (HS.Ident eq)) `HS.App`
              sc `HS.App` lit
      return $ HS.Alt HS.PWildCard
                      (HS.GuardedRhss [HS.GuardedRhs [HS.Qualifier guard] b])
                      emptyBinds

    mkAlt :: HS.Pat -> CC HS.Alt
    mkAlt pat = do
        body' <- term $ T.aBody a
        return $ HS.Alt pat (HS.UnGuardedRhs $ hsCast body') emptyBinds

literal :: Literal -> HS.Exp
literal l = case l of
  LitNat    _ _   -> typed "Integer"
  LitFloat  _ x   -> floatExp x "Double"
  LitQName  _ x   -> litqname x
  LitString _ s   -> litString s
  _               -> l'
  where
    l'    = HS.Lit $ hslit l
    typed = HS.ExpTypeSig l' . HS.TyCon . rtmQual

    -- ASR (2016-09-14): See Issue #2169.
    -- Ulf, 2016-09-28: and #2218.
    floatExp :: Double -> String -> HS.Exp
    floatExp x s
      | isNegativeZero x = rte "negativeZero"
      | isNegativeInf  x = rte "negativeInfinity"
      | isInfinite x     = rte "positiveInfinity"
      | isNegativeNaN x  = rte "negativeNaN"
      | isNaN x          = rte "positiveNaN"
      | otherwise        = typed s

    rte = HS.Var . HS.Qual mazRTE . HS.Ident

    isNegativeInf x = isInfinite x && x < 0.0
    isNegativeNaN x = isNaN x && not (identicalIEEE x (0.0 / 0.0))

hslit :: Literal -> HS.Literal
hslit l = case l of LitNat    _ x -> HS.Int    x
                    LitFloat  _ x -> HS.Frac   (toRational x)
                    LitChar   _ x -> HS.Char   x
                    LitQName  _ x -> __IMPOSSIBLE__
                    LitString _ _ -> __IMPOSSIBLE__
                    LitMeta{}     -> __IMPOSSIBLE__

litString :: String -> HS.Exp
litString s =
  HS.Var (HS.Qual (HS.ModuleName "Data.Text") (HS.Ident "pack")) `HS.App`
    (HS.Lit $ HS.String s)

litqname :: QName -> HS.Exp
litqname x =
  rteCon "QName" `apps`
  [ hsTypedInt n
  , hsTypedInt m
  , HS.Lit $ HS.String $ show x
  , rteCon "Fixity" `apps`
    [ litAssoc (fixityAssoc fx)
    , litPrec  (fixityLevel fx) ] ]
  where
    apps = foldl HS.App
    rteCon name = HS.Con $ HS.Qual mazRTE $ HS.Ident name
    NameId n m = nameId $ qnameName x
    fx = theFixity $ nameFixity $ qnameName x

    litAssoc NonAssoc   = rteCon "NonAssoc"
    litAssoc LeftAssoc  = rteCon "LeftAssoc"
    litAssoc RightAssoc = rteCon "RightAssoc"

    litPrec Unrelated   = rteCon "Unrelated"
    litPrec (Related l) = rteCon "Related" `HS.App` hsTypedInt l

litqnamepat :: QName -> HS.Pat
litqnamepat x =
  HS.PApp (HS.Qual mazRTE $ HS.Ident "QName")
          [ HS.PLit (HS.Int $ fromIntegral n)
          , HS.PLit (HS.Int $ fromIntegral m)
          , HS.PWildCard, HS.PWildCard ]
  where
    NameId n m = nameId $ qnameName x

erasedArity :: QName -> TCM Nat
erasedArity q = do
  (ar, _) <- conArityAndPars q
  erased  <- length . filter id <$> getErasedConArgs q
  return (ar - erased)

condecl :: QName -> TCM (Nat, HS.ConDecl)
condecl q = do
  (ar, np) <- conArityAndPars q
  erased   <- length . filter id <$> getErasedConArgs q
  let ar' = ar - erased
  return $ (ar' + np, cdecl q ar')

cdecl :: QName -> Nat -> HS.ConDecl
cdecl q n = HS.ConDecl (unqhname "C" q)
            [ HS.TyVar $ ihname "a" i | i <- [0 .. n - 1] ]

tvaldecl :: QName
         -> Induction
            -- ^ Is the type inductive or coinductive?
         -> Nat -> Nat -> [HS.ConDecl] -> Maybe Clause -> [HS.Decl]
tvaldecl q ind ntv npar cds cl =
  HS.FunBind [HS.Match vn pvs (HS.UnGuardedRhs HS.unit_con) emptyBinds] :
  maybe [HS.DataDecl kind tn tvs cds []]
        (const []) cl
  where
  (tn, vn) = (unqhname "T" q, unqhname dPrefix q)
  tvs = [ HS.UnkindedVar $ ihname "a" i | i <- [0 .. ntv  - 1]]
  pvs = [ HS.PVar        $ ihname "a" i | i <- [0 .. npar - 1]]

  -- Inductive data types consisting of a single constructor with a
  -- single argument are translated into newtypes.
  kind = case (ind, cds) of
    (Inductive, [HS.ConDecl _ [_]]) -> HS.NewType
    _                               -> HS.DataType

infodecl :: QName -> [HS.Decl] -> [HS.Decl]
infodecl _ [] = []
infodecl q ds = fakeD (unqhname "name" q) (show $ prettyShow q) : ds

--------------------------------------------------
-- Inserting unsafeCoerce
--------------------------------------------------

hsCast :: HS.Exp -> HS.Exp
{-
hsCast = addcast . go where
  addcast [e@(HS.Var(HS.UnQual(HS.Ident(c:ns))))] | c == 'v' && all isDigit ns = e
  addcast es = foldl HS.App mazCoerce es
  -- this need to be extended if you generate other kinds of exps.
  go (HS.App e1 e2    ) = go e1 ++ [hsCast e2]
  go (HS.Lambda _ ps e) = [ HS.Lambda ps (hsCast e) ]
  go e = [e]
-}

-- TODO: what's the specification for hsCast, hsCast' and hsCoerce???
hsCast e = hsCoerce (hsCast' e)

hsCast' :: HS.Exp -> HS.Exp
hsCast' (HS.InfixApp e1 op e2) = hsCoerce $ HS.InfixApp (hsCast' e1) op (hsCast' e2)
hsCast' (HS.Lambda ps e)       = HS.Lambda ps $ hsCast' e
hsCast' (HS.Let bs e)          = HS.Let bs $ hsCast' e
hsCast' (HS.Case sc alts)      = HS.Case (hsCast' sc) (map (hsMapAlt hsCast') alts)
hsCast' e =
  case hsAppView e of
    f : es -> foldl HS.App (hsCoerce f) (map hsCastApp es)
    _      -> __IMPOSSIBLE__

-- We still have to coerce function applications in arguments to coerced
-- functions.
hsCastApp :: HS.Exp -> HS.Exp
hsCastApp (HS.Lambda ps b) = HS.Lambda ps (hsCastApp b)
hsCastApp (HS.Let bs e) = HS.Let bs $ hsCastApp e
hsCastApp (HS.Case sc bs) = HS.Case (hsCastApp sc) (map (hsMapAlt hsCastApp) bs)
hsCastApp (HS.InfixApp e1 op e2) = HS.InfixApp (hsCastApp e1) op (hsCastApp e2)
hsCastApp e =
  case hsAppView e of
    f : es@(_:_) -> foldl HS.App (hsCoerce f) $ map hsCastApp es
    _ -> e

-- No coercion for literal integers
hsCoerce :: HS.Exp -> HS.Exp
hsCoerce e@(HS.ExpTypeSig (HS.Lit (HS.Int{})) _) = e
hsCoerce (HS.Case sc alts) = HS.Case sc (map (hsMapAlt hsCoerce) alts)
hsCoerce (HS.Let bs e) = HS.Let bs $ hsCoerce e
hsCoerce e =
  case hsAppView e of
    c : _ | c == mazCoerce || c == mazIncompleteMatch -> e
    _ -> mazCoerce `HS.App` e

--------------------------------------------------
-- Writing out a haskell module
--------------------------------------------------

copyRTEModules :: TCM ()
copyRTEModules = do
  dataDir <- lift getDataDir
  let srcDir = dataDir </> "MAlonzo" </> "src"
  (lift . copyDirContent srcDir) =<< compileDir

writeModule :: HS.Module -> TCM ()
writeModule (HS.Module m ps imp ds) = do
  -- Note that GHC assumes that sources use ASCII or UTF-8.
  out <- outFile m
  liftIO $ UTF8.writeFile out $ prettyPrint $
    HS.Module m (p : ps) imp ds
  where
  p = HS.LanguagePragma $ List.map HS.Ident $
        [ "EmptyDataDecls"
        , "ExistentialQuantification"
        , "ScopedTypeVariables"
        , "NoMonomorphismRestriction"
        , "Rank2Types"
        ]


outFile' :: Pretty a => a -> TCM (FilePath, FilePath)
outFile' m = do
  mdir <- compileDir
  let (fdir, fn) = splitFileName $ repldot pathSeparator $
                   prettyPrint m
  let dir = mdir </> fdir
      fp  = dir </> replaceExtension fn "hs"
  liftIO $ createDirectoryIfMissing True dir
  return (mdir, fp)
  where
  repldot c = List.map $ \ c' -> if c' == '.' then c else c'

outFile :: HS.ModuleName -> TCM FilePath
outFile m = snd <$> outFile' m

outFile_ :: TCM FilePath
outFile_ = outFile =<< curHsMod

callGHC :: GHCOptions -> IsMain -> Map ModuleName IsMain -> TCM ()
callGHC opts modIsMain mods = do
  mdir    <- compileDir
  hsmod   <- prettyPrint <$> curHsMod
  agdaMod <- curMName
  let outputName = case mnameToList agdaMod of
        [] -> __IMPOSSIBLE__
        ms -> last ms
  (mdir, fp) <- outFile' =<< curHsMod
  let ghcopts = optGhcFlags opts

  let modIsReallyMain = fromMaybe __IMPOSSIBLE__ $ Map.lookup agdaMod mods
      isMain = mappend modIsMain modIsReallyMain  -- both need to be IsMain

  -- Warn if no main function and not --no-main
  when (modIsMain /= isMain) $
    genericWarning =<< fsep (pwords "No main function defined in" ++ [prettyTCM agdaMod <> text "."] ++
                             pwords "Use --no-main to suppress this warning.")

  let overridableArgs =
        [ "-O"] ++
        (if isMain == IsMain then ["-o", mdir </> show (nameConcrete outputName)] else []) ++
        [ "-Werror"]
      otherArgs       =
        [ "-i" ++ mdir] ++
        (if isMain == IsMain then ["-main-is", hsmod] else []) ++
        [ fp
        , "--make"
        , "-fwarn-incomplete-patterns"
        , "-fno-warn-overlapping-patterns"
        ]
      args     = overridableArgs ++ ghcopts ++ otherArgs
      compiler = "ghc"

  -- Note: Some versions of GHC use stderr for progress reports. For
  -- those versions of GHC we don't print any progress information
  -- unless an error is encountered.
  let doCall = optGhcCallGhc opts
  callCompiler doCall compiler args
