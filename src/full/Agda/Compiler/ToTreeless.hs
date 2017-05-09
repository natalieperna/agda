{-# LANGUAGE CPP #-}

module Agda.Compiler.ToTreeless
  ( toTreeless
  , closedTermToTreeless
  ) where

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Traversable (traverse)
import Data.List

import Agda.Syntax.Common
import Agda.Syntax.Internal (QName)
import qualified Agda.Syntax.Treeless as C
import qualified Agda.Syntax.Internal as I
import Agda.Syntax.Literal
import qualified Agda.TypeChecking.CompiledClause as CC
import Agda.TypeChecking.Records (getRecordConstructor)
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.CompiledClause
import Agda.Interaction.Options

import Agda.Compiler.Treeless.Builtin
import Agda.Compiler.Treeless.Simplify
import Agda.Compiler.Treeless.Erase
import Agda.Compiler.Treeless.Uncase
import Agda.Compiler.Treeless.Pretty
import Agda.Compiler.Treeless.Unused
import Agda.Compiler.Treeless.AsPatterns
import Agda.Compiler.Treeless.Identity
import Agda.Compiler.Treeless.CaseSquash
import Agda.Compiler.Treeless.SplitPLet (extractCrossCallFloat)
import Agda.Compiler.Treeless.FloatPLetNV

import Agda.Syntax.Common
import Agda.TypeChecking.Monad as TCM
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute

import Agda.Utils.Functor
import qualified Agda.Utils.HashMap as HMap
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Lens
import qualified Agda.Utils.Pretty as P

#include "undefined.h"
import Agda.Utils.Impossible

prettyPure :: P.Pretty a => a -> TCM Doc
prettyPure = return . P.pretty

-- | Converts compiled clauses to treeless syntax.
--
-- Note: Do not use any of the concrete names in the returned
-- term for identification purposes! If you wish to do so,
-- first apply the Agda.Compiler.Treeless.NormalizeNames
-- transformation.
toTreeless :: QName -> TCM (Maybe C.TTerm)
toTreeless q = ifM (alwaysInline q) (pure Nothing) $ Just <$> toTreeless' q

toTreeless' :: QName -> TCM C.TTerm
toTreeless' q =
  flip fromMaybeM (getTreeless q) $ verboseBracket "treeless.convert" 20 ("compiling " ++ show q) $ do
    Just cc <- defCompiled <$> getConstInfo q
    unlessM (alwaysInline q) $ setTreeless q (C.TDef C.TDefDefault q)
      -- so recursive inlining doesn't loop, but not for always inlined
      -- functions, since that would risk inlining to fail.
    ccToTreeless q cc

-- | Does not require the name to refer to a function.
cacheTreeless :: QName -> TCM ()
cacheTreeless q = do
  def <- theDef <$> getConstInfo q
  case def of
    Function{} -> () <$ toTreeless' q
    _          -> return ()

ccToTreeless :: QName -> CC.CompiledClauses -> TCM C.TTerm
ccToTreeless q cc = do
  let pbody b = pbody' "" b
      pbody' suf b = sep [ text (show q ++ suf) <+> text "=", nest 2 $ prettyPure b ]
  v <- ifM (alwaysInline q) (return 20) (return 0)
  reportSDoc "treeless.convert" (30 + v) $ text "-- compiled clauses of" <+> prettyTCM q $$ nest 2 (prettyPure cc)
  body <- casetreeTop cc
  reportSDoc "treeless.opt.converted" (30 + v) $ text "-- converted" $$ pbody body
  body <- simplifyTTerm body
  reportSDoc "treeless.opt.simpl" (35 + v) $ text "-- after first simplification"  $$ pbody body
  body <- translateBuiltins body
  reportSDoc "treeless.opt.builtin" (30 + v) $ text "-- after builtin translation" $$ pbody body
  body <- simplifyTTerm body
  reportSDoc "treeless.opt.simpl" (30 + v) $ text "-- after second simplification"  $$ pbody body
  body <- eraseTerms q body
  reportSDoc "treeless.opt.erase" (30 + v) $ text "-- after erasure"  $$ pbody body
  body <- caseToSeq body
  reportSDoc "treeless.opt.uncase" (30 + v) $ text "-- after uncase"  $$ pbody body
  body <- recoverAsPatterns body
  reportSDoc "treeless.opt.aspat" (30 + v) $ text "-- after @-pattern recovery"  $$ pbody body
  body <- detectIdentityFunctions q body
  reportSDoc "treeless.opt.id" (30 + v) $ text "-- after identity function detection"  $$ pbody body
  body <- simplifyTTerm body
  reportSDoc "treeless.opt.simpl" (30 + v) $ text "-- after third simplification"  $$ pbody body
  body <- eraseTerms q body
  reportSDoc "treeless.opt.erase" (30 + v) $ text "-- after second erasure"  $$ pbody body
  doSquashCases <- optSquashCases <$> commandLineOptions
  body <- if doSquashCases
    then do
      body' <- squashCases q body
      reportSDoc "treeless.opt.squash" (30 + v) $ text "-- after case squashing"  $$ pbody body'
      return body'
    else return body
  doFloatPLet <- optFloatPLet <$> commandLineOptions
  body <- if doFloatPLet
    then let body' = floatPLet body
      in do
      reportSDoc "treeless.opt.floatplet" (30 + v) $ text "-- after PLet floating"  $$ pbody body'
      return body'
    else return body
  used <- usedArguments q body
  when (any not used) $
    reportSDoc "treeless.opt.unused" (30 + v) $
      text "-- used args:" <+> hsep [ if u then text [x] else text "_" | (x, u) <- zip ['a'..] used ] $$
      pbody' "[stripped]" (stripUnusedArguments used body)
  reportSDoc "treeless.opt.final" (20 + v) $ pbody body
  setTreeless q body
  setCompiledArgUse q used
  doAbstractPLet <- optAbstractPLet <$> commandLineOptions
  if doAbstractPLet
    then case extractCrossCallFloat body of
      Nothing ->         -- return ()
        reportSDoc "treeless.opt.abstractPLet" (40 + v) $
          text "AbstractPLet: No PLet found:" <+> pbody body
      Just ccf -> do
        setCompiledCrossCallFloat q ccf
        reportSDoc "treeless.opt.abstractPLet" (30 + v) $
          text ("-- ccfLambdaLen = " ++ show (C.ccfLambdaLen ccf))
            <+> text (" length ccfPLets = " ++ show (length $ C.ccfPLets ccf))
            $$ pbody' "[inside plets]" (C.ccfBody ccf)
    else return ()
  return body

closedTermToTreeless :: I.Term -> TCM C.TTerm
closedTermToTreeless t = do
  substTerm [] t `runReaderT` initCCEnv

alwaysInline :: QName -> TCM Bool
alwaysInline q = do
  def <- theDef <$> getConstInfo q
  pure $ case def of  -- always inline with functions and pattern lambdas
    Function{} -> isJust (funExtLam def) || isJust (funWith def)
    _ -> False

-- | Initial environment for expression generation.
initCCEnv :: CCEnv
initCCEnv = CCEnv
  { ccCxt        = []
  , ccCatchAll   = Nothing
  }

-- | Environment for naming of local variables.
data CCEnv = CCEnv
  { ccCxt        :: CCContext  -- ^ Maps case tree de-bruijn indices to TTerm de-bruijn indices
  , ccCatchAll   :: Maybe Int  -- ^ TTerm de-bruijn index of the current catch all
  -- If an inner case has no catch-all clause, we use the one from its parent.
  }

type CCContext = [Int]
type CC = ReaderT CCEnv TCM

shift :: Int -> CCContext -> CCContext
shift n = map (+n)

-- | Term variables are de Bruijn indices.
lookupIndex :: Int -- ^ Case tree de bruijn index.
    -> CCContext
    -> Int -- ^ TTerm de bruijn index.
lookupIndex i xs = fromMaybe __IMPOSSIBLE__ $ xs !!! i

-- | Case variables are de Bruijn levels.
lookupLevel :: Int -- ^ case tree de bruijn level
    -> CCContext
    -> Int -- ^ TTerm de bruijn index
lookupLevel l xs = fromMaybe __IMPOSSIBLE__ $ xs !!! (length xs - 1 - l)

-- | Compile a case tree into nested case and record expressions.
casetreeTop :: CC.CompiledClauses -> TCM C.TTerm
casetreeTop cc = flip runReaderT initCCEnv $ do
  let a = commonArity cc
  lift $ reportSLn "treeless.convert.arity" 40 $ "-- common arity: " ++ show a
  lambdasUpTo a $ casetree cc

casetree :: CC.CompiledClauses -> CC C.TTerm
casetree cc = do
  case cc of
    CC.Fail -> return C.tUnreachable
    CC.Done xs v -> withContextSize (length xs) $ do
      -- Issue 2469: Body context size (`length xs`) may be smaller than current context size
      -- if some arguments are not used in the body.
      v <- lift (putAllowedReductions [ProjectionReductions, CopatternReductions] $ normalise v)
      substTerm [] v
    CC.Case _ (CC.Branches True _ _ Just{}) -> __IMPOSSIBLE__
      -- Andreas, 2016-06-03, issue #1986: Ulf: "no catch-all for copatterns!"
      -- lift $ do
      --   typeError . GenericDocError =<< do
      --     text "Not yet implemented: compilation of copattern matching with catch-all clause"
    CC.Case (Arg _ n) (CC.Branches True conBrs _ Nothing) -> lambdasUpTo n $ do
      mkRecord =<< traverse casetree (CC.content <$> conBrs)
    CC.Case (Arg _ n) (CC.Branches False conBrs litBrs catchAll) -> lambdasUpTo (n + 1) $ do
      if Map.null conBrs && Map.null litBrs then do
        -- there are no branches, just return default
        fromCatchAll
      else do
        caseTy <- case (Map.keys conBrs, Map.keys litBrs) of
              ((c:_), []) -> do
                c' <- lift (canonicalName c)
                dtNm <- conData . theDef <$> lift (getConstInfo c')
                return $ C.CTData dtNm
              ([], (LitChar _ _):_)  -> return C.CTChar
              ([], (LitString _ _):_) -> return C.CTString
              ([], (LitFloat _ _):_) -> return C.CTFloat
              ([], (LitQName _ _):_) -> return C.CTQName
              _ -> __IMPOSSIBLE__
        updateCatchAll catchAll $ do
          x <- lookupLevel n <$> asks ccCxt
          def <- fromCatchAll
          C.TCase x caseTy def <$> do
            br1 <- conAlts n conBrs
            br2 <- litAlts n litBrs
            return (br1 ++ br2)
  where
    -- normally, Agda should make sure that a pattern match is total,
    -- so we set the default to unreachable if no default has been provided.
    fromCatchAll :: CC C.TTerm
    fromCatchAll = maybe C.tUnreachable C.TVar <$> asks ccCatchAll

commonArity :: CC.CompiledClauses -> Int
commonArity cc =
  case arities 0 cc of
    [] -> 0
    as -> minimum as
  where
    arities cxt (Case (Arg _ x) (Branches False cons lits def)) =
      concatMap (wArities cxt') (Map.elems cons) ++
      concatMap (wArities cxt' . WithArity 0) (Map.elems lits) ++
      concat [ arities cxt' c | Just c <- [def] ] -- ??
      where cxt' = max (x + 1) cxt
    arities cxt (Case _ (Branches True _ _ _)) = [cxt]
    arities cxt (Done xs _) = [max cxt (length xs)]
    arities _   Fail        = []


    wArities cxt (WithArity k c) = map (\ x -> x - k + 1) $ arities (cxt - 1 + k) c

updateCatchAll :: Maybe CC.CompiledClauses -> (CC C.TTerm -> CC C.TTerm)
updateCatchAll Nothing cont = cont
updateCatchAll (Just cc) cont = do
  def <- casetree cc
  local (\e -> e { ccCatchAll = Just 0, ccCxt = shift 1 (ccCxt e) }) $ do
    C.mkLet def <$> cont

-- | Shrinks or grows the context to the given size.
-- Does not update the catchAll expression, the catchAll expression
-- MUST NOT be used inside `cont`.
withContextSize :: Int -> CC C.TTerm -> CC C.TTerm
withContextSize n cont = do
  diff <- (n -) . length <$> asks ccCxt

  if diff <= 0
  then do
    local (\e -> e { ccCxt = shift diff $ drop (-diff) (ccCxt e)}) $
      C.mkTApp <$> cont <*> pure [C.TVar i | i <- reverse [0..(-diff - 1)]]
  else do
    local (\e -> e { ccCxt = [0..(diff - 1)] ++ shift diff (ccCxt e)}) $ do
      createLambdas diff <$> do
        cont
  where createLambdas :: Int -> C.TTerm -> C.TTerm
        createLambdas 0 cont' = cont'
        createLambdas i cont' | i > 0 = C.TLam (createLambdas (i - 1) cont')
        createLambdas _ _ = __IMPOSSIBLE__

-- | Adds lambdas until the context has at least the given size.
-- Updates the catchAll expression to take the additional lambdas into account.
lambdasUpTo :: Int -> CC C.TTerm -> CC C.TTerm
lambdasUpTo n cont = do
  diff <- (n -) . length <$> asks ccCxt

  if diff <= 0 then cont -- no new lambdas needed
  else do
    catchAll <- asks ccCatchAll

    withContextSize n $ do
      case catchAll of
        Just catchAll' -> do
          -- the catch all doesn't know about the additional lambdas, so just directly
          -- apply it again to the newly introduced lambda arguments.
          -- we also bind the catch all to a let, to avoid code duplication
          local (\e -> e { ccCatchAll = Just 0
                         , ccCxt = shift 1 (ccCxt e)}) $ do
            let catchAllArgs = map C.TVar $ reverse [0..(diff - 1)]
            C.mkLet (C.mkTApp (C.TVar $ catchAll' + diff) catchAllArgs)
              <$> cont
        Nothing -> cont

conAlts :: Int -> Map QName (CC.WithArity CC.CompiledClauses) -> CC [C.TAlt]
conAlts x br = forM (Map.toList br) $ \ (c, CC.WithArity n cc) -> do
  c' <- lift $ canonicalName c
  replaceVar x n $ do
    branch (C.TACon c' n) cc

litAlts :: Int -> Map Literal CC.CompiledClauses -> CC [C.TAlt]
litAlts x br = forM (Map.toList br) $ \ (l, cc) ->
  -- Issue1624: we need to drop the case scrutinee from the environment here!
  replaceVar x 0 $ do
    branch (C.TALit l ) cc

branch :: (C.TTerm -> C.TAlt) -> CC.CompiledClauses -> CC C.TAlt
branch alt cc = do
  alt <$> casetree cc

-- | Replace de Bruijn Level @x@ by @n@ new variables.
replaceVar :: Int -> Int -> CC a -> CC a
replaceVar x n cont = do
  let upd cxt = shift n ys ++ ixs ++ shift n zs
       where
         -- compute the de Bruijn index
         i = length cxt - 1 - x
         -- discard index i
         (ys, _:zs) = splitAt i cxt
         -- compute the de-bruijn indexes of the newly inserted variables
         ixs = [0..(n - 1)]
  local (\e -> e { ccCxt = upd (ccCxt e) , ccCatchAll = (+n) <$> ccCatchAll e }) $
    cont


-- | Precondition: Map not empty.
mkRecord :: Map QName C.TTerm -> CC C.TTerm
mkRecord fs = lift $ do
  -- Get the name of the first field
  let p1 = fst $ fromMaybe __IMPOSSIBLE__ $ headMaybe $ Map.toList fs
  -- Use the field name to get the record constructor and the field names.
  I.ConHead c _ind xs <- conSrcCon . theDef <$> (getConstInfo =<< canonicalName . I.conName =<< recConFromProj p1)
  -- Convert the constructor
  let (args :: [C.TTerm]) = for xs $ \ x -> fromMaybe __IMPOSSIBLE__ $ Map.lookup x fs
  return $ C.mkTApp (C.TCon c) args


recConFromProj :: QName -> TCM I.ConHead
recConFromProj q = do
  caseMaybeM (isProjection q) __IMPOSSIBLE__ $ \ proj -> do
    let d = unArg $ projFromType proj
    getRecordConstructor d


-- | Translate the actual Agda terms, with an environment of all the bound variables
--   from patternmatching. Agda terms are in de Bruijn indices, but the expected
--   TTerm de Bruijn indexes may differ. This is due to additional let-bindings
--   introduced by the catch-all machinery, so we need to lookup casetree de bruijn
--   indices in the environment as well.
substTerm :: ProjInfo -> I.Term -> CC C.TTerm
substTerm inlinedAncestors term = normaliseStatic term >>= \ term ->
  case I.ignoreSharing $ I.unSpine term of
    I.Var ind es -> do
      ind' <- lookupIndex ind <$> asks ccCxt
      let args = fromMaybe __IMPOSSIBLE__ $ I.allApplyElims es
      C.mkTApp (C.TVar ind') <$> substArgs inlinedAncestors args
    I.Lam _ ab ->
      C.TLam <$>
        local (\e -> e { ccCxt = 0 : (shift 1 $ ccCxt e) })
          (substTerm inlinedAncestors (I.unAbs ab))
    I.Lit l -> return $ C.TLit l
    I.Level _ -> return C.TUnit
    I.Def q es -> do
      let args = fromMaybe __IMPOSSIBLE__ $ I.allApplyElims es
      maybeInlineDef inlinedAncestors q args
    I.Con c ci args -> do
        c' <- lift $ canonicalName $ I.conName c
        C.mkTApp (C.TCon c') <$> substArgs inlinedAncestors args
    I.Shared _ -> __IMPOSSIBLE__ -- the ignoreSharing fun should already take care of this
    I.Pi _ _ -> return C.TUnit
    I.Sort _  -> return C.TSort
    I.MetaV _ _ -> __IMPOSSIBLE__   -- we don't compiled if unsolved metas
    I.DontCare _ -> return C.TErased

normaliseStatic :: I.Term -> CC I.Term
normaliseStatic v@(I.Def f es) = lift $ do
  static <- isStaticFun . theDef <$> getConstInfo f
  if static then normalise v else pure v
normaliseStatic v = pure v

type ProjInfo = [(I.QName, (I.Args, Definition))]

maybeInlineDef :: ProjInfo -> I.QName -> I.Args -> CC C.TTerm
maybeInlineDef inlinedAncestors q vs =
  ifM (lift $ alwaysInline q) (doinline inlinedAncestors) $ do
    lift $ cacheTreeless q
    def <- lift $ getConstInfo q
    doInlineProj <- optInlineProj <$> lift commandLineOptions
    case theDef def of
      fun@Function{}
        | fun ^. funInline -> doinline []
        | isProperProjection fun && doInlineProj -- && q `notElem` inlinedAncestors ->
        -> do
            lift $ reportSDoc "treeless.inline" 20 $ text "-- inlining projection" $$ prettyPure (defName def)
            doinline inlinedAncestors
        | otherwise -> defaultCase
      _ -> C.mkTApp (C.TDef C.TDefDefault q) <$> substArgs inlinedAncestors vs
  where
    updatedAncestors = do
      def <- lift $ getConstInfo q
      return $ (q, (vs, def)) : inlinedAncestors
    doinline inlinedAncestors = do
      ancestors <- updatedAncestors
      case (q `lookup` inlinedAncestors) of
        Nothing -> C.mkTApp <$> inline q <*> substArgs ancestors vs
        Just _ -> defaultCase --trace ("BAD STUFF: " ++ unlines (map show ancestors)) defaultCase
    -- doinline qs = C.mkTApp <$> inline q <*> substArgs ancestors vs
    inline :: QName -> CC C.TTerm
    inline q = lift $ toTreeless' q
    defaultCase = do
            _ <- lift $ toTreeless' q
            used <- lift $ getCompiledArgUse q
            let substUsed False _   = pure C.TErased
                substUsed True  arg = substArg inlinedAncestors arg
            C.mkTApp (C.TDef C.TDefDefault q) <$> sequence [ substUsed u arg | (arg, u) <- zip vs $ used ++ repeat True ]

substArgs :: ProjInfo -> [Arg I.Term] -> CC [C.TTerm]
substArgs = traverse . substArg

substArg :: ProjInfo -> Arg I.Term -> CC C.TTerm
substArg inlinedAncestors x | erasable x     = return C.TErased
                            | otherwise      = substTerm inlinedAncestors (unArg x)
  where
    erasable x =
      case getRelevance x of
        Irrelevant -> True
        NonStrict  -> True
        UnusedArg  -> True
        Forced{}   -> False -- TODO: would like this to be True
        Relevant   -> False
