{-# LANGUAGE CPP #-}
module Agda.Compiler.Treeless.NVTTerm
  ( module Agda.Compiler.Treeless.NVTTerm
  , module Agda.Syntax.NVTTerm
  ) where

-- A variant of |TTerm| using named variables.

import Prelude hiding (Floating)

import Control.Arrow (first)
import Control.Applicative
import Control.Monad.Identity (runIdentity)
import Control.Monad.Reader
import Control.Monad.State
import Data.List (elemIndex)
import Data.Maybe (mapMaybe)
import Data.Monoid
import qualified Data.Map as Map
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

import Agda.Syntax.Common
import Agda.Syntax.Treeless
import Agda.Syntax.Literal
import Agda.Syntax.Position
import Agda.Syntax.Fixity
import Agda.Syntax.Abstract.Name
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.NVTTerm
import Agda.TypeChecking.Substitute
import Agda.Compiler.Treeless.Subst
import Agda.Compiler.Treeless.Compare
import Agda.Compiler.Treeless.Pretty ()
import Agda.Compiler.Treeless.NVTTerm.Pretty ()

-- import Agda.Utils.Permutation
import qualified Agda.Utils.Pretty as P
import Agda.Utils.List ( (!!!) )

import Data.Word (Word64)

import Agda.Utils.Impossible
#include "undefined.h"

import Debug.Trace

mkNVTLet :: Var -> NVTTerm -> NVTTerm -> NVTTerm
mkNVTLet v e b = maybe b id $ mkNVTLetM v e b

mkNVTLetM :: Var -> NVTTerm -> NVTTerm -> Maybe NVTTerm
mkNVTLetM v (NVTVar u) b = Just $ renameNVTTerm (singletonNVRename v u) b
mkNVTLetM v e b = if v `elemVarSet` fvarsNVTTerm b
  then Just $ NVTLet v e b
  else Nothing

splitVars :: [NVTTerm] -> ([Var], [NVTTerm])
splitVars = h id
  where
    h acc [] = (acc [], [])
    h acc (t : ts')
      | NVTVar v <- t  =  h (acc . (v :)) ts'
    h acc ts = (acc [], ts)


emptyVarSet :: VarSet
emptyVarSet = VarSet IntSet.empty
singletonVarSet :: Var -> VarSet
singletonVarSet (V i) = VarSet $ IntSet.singleton i
insertVarSet :: Var -> VarSet -> VarSet
insertVarSet (V i) (VarSet s) = VarSet $ IntSet.insert i s
deleteVarSet :: Var -> VarSet -> VarSet
deleteVarSet (V i) (VarSet s) = VarSet $ IntSet.delete i s
differenceVarSet :: VarSet -> VarSet -> VarSet
differenceVarSet (VarSet s1) (VarSet s2) = VarSet $ IntSet.difference s1 s2
nullVarSet :: VarSet -> Bool
nullVarSet (VarSet s) = IntSet.null s
elemVarSet :: Var -> VarSet -> Bool
elemVarSet (V i) (VarSet s) = IntSet.member i s
listToVarSet :: [Var] -> VarSet
listToVarSet = foldr insertVarSet emptyVarSet
unionVarSet :: VarSet -> VarSet -> VarSet
unionVarSet (VarSet s1) (VarSet s2) = VarSet $ IntSet.union s1 s2
unionsVarSet :: [VarSet] -> VarSet
unionsVarSet = foldr unionVarSet emptyVarSet
intersectionVarSet :: VarSet -> VarSet -> VarSet
intersectionVarSet (VarSet s1) (VarSet s2) = VarSet $ IntSet.intersection s1 s2

fromTTerm' :: TTerm -> NVTTerm
fromTTerm' t = runIdentity $ evalStateT (fromTTerm [] t) 0

type U m = StateT Int m

getVar :: Monad m => U m Var
getVar = do
  i <- get
  put $ succ i
  return $ V i

getVars :: Monad m => Int -> U m [Var]
getVars k = sequence $ replicate k getVar

-- @map fst <$> getRenaming vs = return vs@
getRenaming :: Monad m => [Var] -> U m [(Var, Var)]
getRenaming [] = return []
getRenaming (u : us) = do
  v <- getVar
  ((u,v) :) <$> getRenaming us

fromTTerm :: Monad m => [Var] -> TTerm -> U m NVTTerm
fromTTerm vs t = fst <$> fromTTerm0 True vs t

-- |fromTTerm0| also returns the set of free variables in the generated term,
-- and omits |let|s for variables that do not occur.
-- If |letOpt = True|, trivial |let|s are not generated ---
-- therefore |letOpt| must be false for |PLet| conversion
-- (in |floatingsFromPLets|).
fromTTerm0 :: Monad m => Bool -> [Var] -> TTerm -> U m (NVTTerm, VarSet)
fromTTerm0 letOpt vs0 t0 = fromT vs0 t0 where
  fromT vs t = case t of
    TVar k -> case vs !!! k of
      Just v -> return $ (NVTVar v, singletonVarSet v)
      Nothing -> trace (show (P.text "fromTTerm: variable out of range!"
                  P.$$ P.nest 4 (P.text ("vs = " ++ show vs)
                        P.$$ P.text ("k = " ++ show k)
                        P.$$ P.text ("letOpt = " ++ show letOpt)
                        P.$$ P.text ("vs0 = " ++ show vs0)
                        P.$$ (P.text "t0 = " P.<+> P.nest 4 (P.pretty t0)))))
                 __IMPOSSIBLE__
    TPrim p -> return (NVTPrim p, emptyVarSet)
    TDef TDefDefault name -> return (NVTDef NVTDefDefault name, emptyVarSet)
    TDef (TDefAbstractPLet i) name -> do
      var' <- return NVTDefAbstractPLet -- <$> getVars i -- map (vs !!) is
         -- \edcomm{WK}{Better |__IMPOSSIBLE__|?}
      return (NVTDef var' name, emptyVarSet)
    TApp f as -> do
      (f', vsF) <- fromT vs f
      (as', vssAs) <- unzip <$> mapM (fromT vs) as
      return (NVTApp f' as', unionsVarSet (vsF : vssAs))
    TLam b -> do
      v <- getVar
      (b', vsB) <- fromT (v : vs) b
      return (NVTLam v b', deleteVarSet v vsB)
    TLit lit -> return (NVTLit lit, emptyVarSet)
    TCon c -> return (NVTCon c, emptyVarSet)
    TLet e b -> do
      (e', vsE) <- fromT vs e
      case e' of
        NVTVar u | letOpt -> fromT (u : vs) b
        _ -> do
          v <- getVar
          pB@(b', vsB) <- fromT (v : vs) b
          return $ if letOpt <= v `elemVarSet` vsB
            then (NVTLet v e' b', vsE `unionVarSet` deleteVarSet v vsB)
            else pB
    TCase k caseType dft alts -> case vs !!! k of
      Just v -> do
        (dft', vsDft) <- fromT vs dft
        (alts', vssAlts) <- unzip <$> mapM (fromTAlt vs) alts
        return ( NVTCase v caseType dft' alts'
               , insertVarSet v . unionsVarSet $ vsDft : vssAlts
               )
      Nothing -> trace (show (P.text "fromTTerm: case scrutinee out of range!"
                  P.$$ P.nest 4 (P.text ("vs = " ++ show vs)
                        P.$$ P.text ("k = " ++ show k)
                        P.$$ P.text ("letOpt = " ++ show letOpt)
                        P.$$P.text ("vs0 = " ++ show vs0)
                        P.$$  (P.text "t0 = " P.<+> P.nest 4 (P.pretty t)))))
                  __IMPOSSIBLE__
    TUnit -> return (NVTUnit, emptyVarSet)
    TSort -> return (NVTSort, emptyVarSet)
    TErased -> return (NVTErased, emptyVarSet)
    TError t -> return (NVTError t, emptyVarSet)

  fromTAlt :: Monad m => [Var] -> TAlt -> U m (NVTAlt, VarSet)
  fromTAlt vs (TACon name arity b) = do
    cvars <- getVars arity
    (b', vsB) <- fromT (reverse cvars ++ vs) b
    return (NVTACon name cvars b', foldr deleteVarSet vsB cvars)
  fromTAlt vs (TAGuard g b) = do
    (g', vsG) <- fromT vs g
    (b', vsB) <- fromT vs b
    return (NVTAGuard g' b', unionVarSet vsG vsB)
  fromTAlt vs (TALit lit b) = first (NVTALit lit) <$> fromT vs b

toTTerm' :: NVTTerm -> TTerm
toTTerm' = toTTerm []

fromVar :: Nat -> [Var] -> Var -> Nat -- first argument is __IMPOSSIBLE__
fromVar err vs v = maybe (tr err) id $ elemIndex v vs
  where  tr = trace $ "fromVar " ++ shows vs (' ' : show v)

toTTerm, toTTerm0 :: [Var] -> NVTTerm -> TTerm
toTTerm vs t = trace ("toTTerm " ++ shows vs (' ' : P.prettyShow t)) $
               toTTerm0 vs t
toTTerm0 vs t = case t of
  NVTVar v -> TVar (fromVar __IMPOSSIBLE__ vs v)
  NVTPrim p -> TPrim p
  NVTDef var name -> TDef var' name
    where
      var' = case var of
        NVTDefDefault -> TDefDefault
        NVTDefFloating _us -> TDefDefault -- |__IMPOSSIBLE__|  -- should have been squashed away.
          -- \edcomm{WK}{Currently occurring in |t'| in |mkCCF 2:|}
        NVTDefAbstractPLet -> TDefAbstractPLet 0 -- |TDefAbstractPLet __IMPOSSIBLE__|
  NVTApp f ts -> TApp (toTTerm0 vs f) (map (toTTerm0 vs) ts)
  NVTLam v b -> TLam $ toTTerm0 (v : vs) b
  NVTLit lit -> TLit lit
  NVTCon c -> TCon c
  NVTLet v e b -> TLet (toTTerm0 vs e) (toTTerm0 (v : vs) b)
  NVTCase v caseType dft alts ->
    TCase (fromVar __IMPOSSIBLE__ vs v) caseType (toTTerm0 vs dft)
      $ map (toTAlt vs) alts
  NVTUnit -> TUnit
  NVTSort -> TSort
  NVTErased -> TErased
  NVTError t -> TError t


toTAlt :: [Var] -> NVTAlt -> TAlt
toTAlt vs (NVTACon name cvars b) =
  TACon name (length cvars) $ toTTerm0 (reverse cvars ++ vs) b
toTAlt vs (NVTAGuard g b) = TAGuard (toTTerm0 vs g) (toTTerm0 vs b)
toTAlt vs (NVTALit lit b) = TALit lit (toTTerm0 vs b)

copyVar :: Monad m => Var -> StateT NVRename (U m) Var -- for binders
copyVar v = do
  v' <- lift getVar
  modify $ insertNVRename v v'
  return v'

renameVarS :: Monad m => Var -> StateT NVRename (U m) Var -- only lookup
renameVarS v = do
    r <- get
    return $ renameVar r v

copyNVTTerm :: Monad m => NVTTerm -> StateT NVRename (U m) NVTTerm
copyNVTTerm t = case t of
  NVTVar v -> NVTVar <$> renameVarS v
  NVTPrim p -> return t
  NVTDef variant name -> do
    variant' <- case variant of
      NVTDefFloating us -> NVTDefFloating <$> mapM renameVarS us
      _ -> return variant
    return $ NVTDef variant' name
  NVTApp f ts -> (NVTApp <$> copyNVTTerm f) <*> mapM copyNVTTerm ts
  NVTLam v b -> do
    v' <- copyVar v
    NVTLam v' <$> copyNVTTerm b
  NVTLit lit -> return t
  NVTCon c -> return t
  NVTLet v e b -> do
    e' <- copyNVTTerm e -- conceptually needs to be first!
      -- (actually should not make a difference, due to uniqueness of binders)
    v' <- copyVar v
    NVTLet v' e' <$> copyNVTTerm b
  NVTCase v caseType dft alts -> do
    v' <- renameVarS v
    dft' <- copyNVTTerm dft
    NVTCase v' caseType dft' <$> mapM copyNVTAlt alts
  NVTUnit -> return t
  NVTSort -> return t
  NVTErased -> return t
  NVTError _ -> return t

copyNVTAlt :: Monad m => NVTAlt -> StateT NVRename (U m) NVTAlt
copyNVTAlt (NVTACon name cvars b) = do
  cvars' <- mapM copyVar cvars
  NVTACon name cvars' <$> copyNVTTerm b
copyNVTAlt (NVTAGuard g b) = (NVTAGuard <$> copyNVTTerm g) <*> copyNVTTerm b
copyNVTAlt (NVTALit lit b) = NVTALit lit <$> copyNVTTerm b


fvarsNVTTerm :: NVTTerm -> VarSet
fvarsNVTTerm (NVTVar v) = singletonVarSet v
fvarsNVTTerm (NVTPrim p) = emptyVarSet
fvarsNVTTerm (NVTDef (NVTDefFloating vs) name) = listToVarSet vs
fvarsNVTTerm (NVTDef _ name) = emptyVarSet
fvarsNVTTerm (NVTApp f ts) = unionsVarSet $ fvarsNVTTerm f : map fvarsNVTTerm ts
fvarsNVTTerm (NVTLam v b) = deleteVarSet v $ fvarsNVTTerm b
fvarsNVTTerm (NVTLit lit) = emptyVarSet
fvarsNVTTerm (NVTCon c) = emptyVarSet
fvarsNVTTerm (NVTLet v e b) = fvarsNVTTerm e `unionVarSet` deleteVarSet v (fvarsNVTTerm b)
fvarsNVTTerm (NVTCase v caseType dft alts) = unionsVarSet $ insertVarSet v (fvarsNVTTerm dft) : map fvarsNVTAlt alts
fvarsNVTTerm NVTUnit = emptyVarSet
fvarsNVTTerm NVTSort = emptyVarSet
fvarsNVTTerm NVTErased = emptyVarSet
fvarsNVTTerm (NVTError t) = emptyVarSet

fvarsNVTAlt :: NVTAlt -> VarSet
fvarsNVTAlt (NVTACon c cvars b) = foldr deleteVarSet (fvarsNVTTerm b) cvars
fvarsNVTAlt (NVTAGuard g b) = fvarsNVTTerm g `unionVarSet` fvarsNVTTerm b
fvarsNVTAlt (NVTALit lit b) = fvarsNVTTerm b

{-
bvarsNVTTerm :: NVTTerm -> IntSet
bvarsNVTTerm (NVTVar v) = IntSet.empty
bvarsNVTTerm (NVTPrim p) = IntSet.empty
bvarsNVTTerm (NVTDef _ name) = IntSet.empty
bvarsNVTTerm (NVTApp f ts) = IntSet.unions $ bvarsNVTTerm f : map bvarsNVTTerm ts
bvarsNVTTerm (NVTLam (V i) b) = IntSet.insert i $ bvarsNVTTerm b
bvarsNVTTerm (NVTLit lit) = IntSet.empty
bvarsNVTTerm (NVTCon c) = IntSet.empty
bvarsNVTTerm (NVTLet (V i) e b) = bvarsNVTTerm e `IntSet.union` IntSet.insert i (bvarsNVTTerm b)
bvarsNVTTerm (NVTCase (V i) caseType dft alts) = IntSet.unions $ bvarsNVTTerm dft : map bvarsNVTAlt alts
bvarsNVTTerm NVTUnit = IntSet.empty
bvarsNVTTerm NVTSort = IntSet.empty
bvarsNVTTerm NVTErased = IntSet.empty
bvarsNVTTerm (NVTError t) = IntSet.empty

bvarsNVTAlt :: NVTAlt -> IntSet
bvarsNVTAlt (NVTACon name cvars b) = let bvars = IntSet.fromList (map unV cvars)
  in IntSet.union (bvarsNVTTerm b) bvars
bvarsNVTAlt (NVTAGuard g b) = bvarsNVTTerm g `IntSet.union` bvarsNVTTerm b
bvarsNVTAlt (NVTALit lit b) = bvarsNVTTerm b
-}

singletonNVRename :: Var -> Var -> NVRename
singletonNVRename (V i) v@(V j) = NVRename $
   if i == j then IntMap.empty else IntMap.singleton i v

insertNVRename :: Var -> Var -> NVRename -> NVRename
insertNVRename (V i) v@(V j) r@(NVRename m)
  = if i == j then r else NVRename $ IntMap.insert i v m

lookupNVRename :: Var -> NVRename -> Maybe Var
lookupNVRename (V i) (NVRename m) = IntMap.lookup i m

unionNVRename :: NVRename -> NVRename -> NVRename
unionNVRename (NVRename m1) (NVRename m2) = NVRename $ IntMap.union m1 m2

domRestrNVRename :: [Var] -> NVRename -> NVRename
domRestrNVRename vs0 r = h emptyNVRename vs0
  where
    h :: NVRename -> [Var] -> NVRename
    h r' [] = r'
    h r' (v : vs) = h r'' vs
      where
        r'' = case lookupNVRename v r of
          Nothing -> r'
          Just v' -> insertNVRename v v' r'

zipInsertNVRename :: [Var] -> [Var] -> NVRename -> NVRename
zipInsertNVRename us vs r = foldr ($) r $ zipWith insertNVRename us vs

listInsertNVRename :: [(Var,Var)] -> NVRename -> NVRename
listInsertNVRename ps r = foldr (uncurry insertNVRename) r ps

listToNVRename :: [(Var,Var)] -> NVRename
listToNVRename ps = listInsertNVRename ps emptyNVRename

zipNVRename :: [Var] -> [Var] -> NVRename
zipNVRename us vs = zipInsertNVRename us vs emptyNVRename

renameNVTTerm' :: [Var] -> [Var] -> NVTTerm -> NVTTerm
renameNVTTerm' us vs = renameNVTTerm $ zipNVRename us vs

deleteNVRename :: Var -> NVRename -> NVRename
deleteNVRename (V i) (NVRename m) = NVRename $ IntMap.delete i m

renameVar :: NVRename -> Var -> Var
renameVar (NVRename m) v@(V i) = IntMap.findWithDefault v i m

renameNVTTerm :: NVRename -> NVTTerm -> NVTTerm
renameNVTTerm r0@(NVRename m) t0
  | IntMap.null m  = t0
  | otherwise      = renTTerm r0 t0
  where
    renTTerm :: NVRename -> NVTTerm -> NVTTerm
    renTTerm r (NVTVar v) = NVTVar $ renameVar r v
    renTTerm r t@(NVTPrim _) = t
    renTTerm r t@(NVTDef NVTDefDefault _) = t
    renTTerm r t@(NVTDef NVTDefAbstractPLet _) = t
    renTTerm r t@(NVTDef (NVTDefFloating vs) name) -- = t
       = NVTDef (NVTDefFloating $ map (renameVar r) vs) name
    renTTerm r (NVTApp f ts) = NVTApp (renTTerm r f) (map (renTTerm r) ts)
    renTTerm r t@(NVTLam v b) = let
        r'@(NVRename m') = deleteNVRename v r
        bad (y,x) = v == x && (V y `elemVarSet` fvarsNVTTerm b)
      in case filter bad $ IntMap.toList m' of
        [] -> NVTLam v $ renameNVTTerm r' b
        ps -> trace ("captured variables " ++ show ps
                 ++ "\nin renTTerm " ++ shows r " " ++ P.prettyShow t
                 ++ "\nin renameNVTTerm " ++ shows r0 " " ++ P.prettyShow t0
                    ) __IMPOSSIBLE__ -- unexpected variable capture
    renTTerm r t@(NVTLit _) = t
    renTTerm r t@(NVTCon _) = t
    renTTerm r t@(NVTLet v e b) = let
        r'@(NVRename m') = deleteNVRename v r
        bad (y,x) = v == x && (V y `elemVarSet` fvarsNVTTerm b)
      in case filter bad $ IntMap.toList m' of
        [] -> NVTLet v (renTTerm r e) (renameNVTTerm r' b)
        ps -> trace ("captured variables " ++ show ps
                 ++ "\nin renTTerm " ++ shows r " " ++ P.prettyShow t
                 ++ "\nin renameNVTTerm " ++ shows r0 " " ++ P.prettyShow t0
                    ) __IMPOSSIBLE__ -- unexpected variable capture
    renTTerm r (NVTCase v caseType dft alts) = let
        v' = renameVar r v
      in NVTCase v' caseType (renTTerm r dft) $ map (renameNVTAlt r) alts
    renTTerm r NVTUnit = NVTUnit
    renTTerm r NVTSort = NVTSort
    renTTerm r NVTErased = NVTErased
    renTTerm r t@(NVTError _) = t

    -- The |NVRename| argument has already been confirmed to be non-empty
    renameNVTAlt :: NVRename  -> NVTAlt -> NVTAlt
    renameNVTAlt r a@(NVTACon name cvars b) = let
        r'@(NVRename m') = foldr deleteNVRename r cvars
        bad (y,x) = (x `elem` cvars) && (V y `elemVarSet` fvarsNVTTerm b)
      in case filter bad $ IntMap.toList m' of
        [] -> NVTACon name cvars $ renameNVTTerm r' b
        ps -> trace ("captured variables " ++ show ps
                 ++ "\nin renameNVTAlt " ++ shows r " " ++ P.prettyShow a
                 ++ "\nin renameNVTTerm " ++ shows r0 " " ++ P.prettyShow t0
                    ) __IMPOSSIBLE__ -- unexpected variable capture
    renameNVTAlt r (NVTAGuard g b) = NVTAGuard (renTTerm r g) (renTTerm r b)
    renameNVTAlt r (NVTALit lit b) = NVTALit lit (renTTerm r b)

innerNVPat :: NVPat -> Maybe NVConPat
innerNVPat (NVPVar _) = Nothing
innerNVPat (NVPAsCon _v p) = Just p

withInnerNVPats :: [NVPat] -> [(Var, NVConPat)]
withInnerNVPats [] = []
withInnerNVPats (NVPVar _ : ps) = withInnerNVPats ps
withInnerNVPats (NVPAsCon v conPat : ps) = (v, conPat) : withInnerNVPats ps

getNVPatVar :: NVPat -> Var
getNVPatVar (NVPVar v) = v
getNVPatVar (NVPAsCon v _) = v

-- taking care that |innerNVPatVars| generates the sequence of variables
-- that will be the sequence of bound variables in the result of |caseNVPat|.
innerNVPatVars :: NVPat -> [Var]
innerNVPatVars (NVPVar _v) =[]
innerNVPatVars (NVPAsCon _v cp) = boundNVConPatVars cp

boundNVConPatVars :: NVConPat -> [Var]
boundNVConPatVars (NVConPat _ct _dft _c pats)
  = map getNVPatVar pats ++ concatMap innerNVPatVars pats

patVars :: NVPat -> [Var]
patVars p = getNVPatVar p : innerNVPatVars p


-- @caseNVPat v p b@ is @case v of p -> b@ inside the body of @let a@p = ...@
-- \edcomm{WK}{Used?}
caseNVPat :: Var -> NVPat -> NVTTerm -> NVTTerm
caseNVPat a@(V i) (NVPVar v@(V j)) b
   | i == j     = b
   | otherwise  = renameNVTTerm (singletonNVRename v a) b
caseNVPat a (NVPAsCon _v conPat) b = caseNVConPat a conPat b

-- @caseNVConPat v p b@ is @case v of p -> b@
caseNVConPat :: Var -> NVConPat -> NVTTerm -> NVTTerm
caseNVConPat a (NVConPat ct dft c pats) b = NVTCase a ct dft
   [NVTACon c (map getNVPatVar pats) $ foldr (\ (v, p) -> caseNVConPat v p) b $ withInnerNVPats pats]


-- Monadic versions: These rename the case scrutinees according to the incoming
-- NVRename, and create new bound variables, propagating the renaming of those
-- through inner patterns, but do not touch the body argument |b|.

-- \edcomm{WK}{Used?}
caseNVPatU :: Monad m => NVRename -> Var -> NVPat -> NVTTerm -> U m NVTTerm
caseNVPatU r a@(V i) (NVPVar v@(V j)) b
   | i == j     = return b
   | otherwise  = return $ renameNVTTerm (insertNVRename v (renameVar r a) r) b
caseNVPatU r a (NVPAsCon _v conPat) b = caseNVConPatU r (renameVar r a) conPat b

caseNVConPatU :: Monad m => NVRename -> Var -> NVConPat -> NVTTerm -> U m NVTTerm
caseNVConPatU r a (NVConPat ct dft c pats) b = NVTCase (renameVar r a) ct dft . (: []) <$> do
    vps <- getRenaming $ map getNVPatVar pats
    let  cvars = map snd vps
         r' = listInsertNVRename vps r -- does not need to propagate across siblings.
    b' <- foldM (\ t (v, p) -> caseNVConPatU r' v p t) b $ withInnerNVPats pats
    return $ NVTACon c cvars b'

-- The result of @unifyNVPat@ contains the unified pattern,
-- and the renamings for matching the argument patterns into that.
--(Full substitutions are not necessary,
--  since every pattern node contains a variable.)
--(Full substitutions are also not useful,
--  since these renamings are intended for use on bodies via @renameNVTTerm@.)
unifyNVPat :: NVPat -> NVPat -> Maybe (NVPat, PU)
unifyNVPat p1 p2 = unifyNVPat0 p1 p2 emptyPU

unifyNVPat0 :: NVPat -> NVPat -> PU -> Maybe (NVPat, PU)
unifyNVPat0 p1 p2 pu@(r1@(NVRename m1), r2@(NVRename m2)) = case p2 of
  NVPVar v2@(V i2) -> let v1@(V i1) = getNVPatVar p1
      in case IntMap.lookup i2 m2 of
    Just v1' -> if v1 /= v1' then Nothing
      else case IntMap.lookup i1 m1 of
        Just v2' ->  if v2 /= v2'  then Nothing
          else Just (p1, pu)
        Nothing -> Just (p1, pu)
    Nothing -> let r2' = insertNVRename v2 v1 r2
      in case IntMap.lookup i1 m1 of
        Just v2' ->  if v2 /= v2'  then Nothing
          else Just (p1, (r1, r2'))
        Nothing -> Just (p1, (r1, r2'))
  NVPAsCon v2@(V i2) cp2 -> case p1 of
    NVPVar v1@(V i1) -> case IntMap.lookup i1 m1 of
      Just v2' -> if v2 /= v2' then Nothing
        else case IntMap.lookup i2 m2 of
          Just v1' ->  if v1 /= v1'  then Nothing
            else Just (p2, pu)
          Nothing -> Just (p2, pu)
      Nothing -> let r1' = insertNVRename v1 v2 r1
        in case IntMap.lookup i2 m2 of
          Just v1' ->  if v1 /= v1'  then Nothing
            else Just (p2, (r1', r2))
          Nothing -> Just (p2, (r1', r2))
    NVPAsCon v1@(V i1) cp1 -> case unifyNVConPat0 cp1 cp2 pu of
      Nothing -> Nothing
      Just (cp', (r1', r2')) -> Just (NVPAsCon v2 cp'
                                     , (insertNVRename v1 v2 r1', r2'))

copyNVConPat :: Monad m => NVConPat -> StateT NVRename (U m) NVConPat
copyNVConPat (NVConPat ct dft c pats) = do
  dft' <- copyNVTTerm dft
  NVConPat ct dft' c <$> mapM copyNVPat pats

copyNVPat :: Monad m => NVPat -> StateT NVRename (U m) NVPat
copyNVPat (NVPVar v) = NVPVar <$> copyVar v
copyNVPat (NVPAsCon v cp) = do
  v' <- copyVar v
  NVPAsCon v' <$> copyNVConPat cp

onPU1, onPU2 :: Monad m => StateT NVRename (U m) a -> StateT PU (U m) a
onPU1 m = do
  (r1, r2) <- get
  (a, r1') <- lift $ runStateT m r1
  put (r1', r2)
  return a
onPU2 m = do
  (r1, r2) <- get
  (a, r2') <- lift $ runStateT m r2
  put (r1, r2')
  return a

unifyVarU :: Monad m => Var -> Var -> StateT PU (U m) Var
unifyVarU v1 v2 = do
  (r1, r2) <- get
  v3 <- lift getVar
  let r1' = insertNVRename v1 v3 r1
      r2' = insertNVRename v2 v3 r2
  put (r1', r2')
  return v3

-- All default expressions in |NVConPat|s will be |harmless|,
-- and therefore needno explicit copying.

-- | ``harmless'' in the sense of negligible as default expression in |TCase|:
harmless :: NVTTerm -> Bool
harmless (NVTError _)  = True
harmless NVTUnit       = True
harmless NVTErased     = True
harmless NVTSort       = True
harmless _             = False

-- Creating a pushout with all new binders:
unifyNVPatU :: Monad m => NVPat -> NVPat -> StateT PU (U m) (Maybe NVPat)
unifyNVPatU p1 p2
  = let
   v1 = getNVPatVar p1
   v2 = getNVPatVar p2
  in do
  v3 <- unifyVarU v1 v2
  case p1 of
    NVPVar _v1 -> case p2 of
      NVPVar _v2       -> return . Just $ NVPVar v3
      NVPAsCon _v2 cp2 -> Just . NVPAsCon v3 <$> onPU2 (copyNVConPat cp2)
    NVPAsCon _v1 cp1 -> fmap (NVPAsCon v3) <$> case p2 of
      NVPVar _v2       -> Just <$> onPU1 (copyNVConPat cp1)
      NVPAsCon _v2 cp2 -> unifyNVConPatU cp1 cp2

unifyNVPatsU :: Monad m => [NVPat] -> [NVPat] -> StateT PU (U m) (Maybe [NVPat])
unifyNVPatsU [] [] = return $ Just []
unifyNVPatsU (p1 : ps1) (p2 : ps2) = do
  mp3 <- unifyNVPatU p1 p2
  case mp3 of
    Nothing -> return Nothing
    Just p3 -> fmap (p3 :) <$> unifyNVPatsU ps1 ps2
unifyNVPatsU _ _ = return Nothing

unifyNVConPatU :: Monad m
               => NVConPat -> NVConPat -> StateT PU (U m) (Maybe NVConPat)
unifyNVConPatU (NVConPat ct1 dft1 c1 ps1) (NVConPat ct2 dft2 c2 ps2)
  = if c1 /= c2
    then return Nothing
    else fmap (NVConPat ct1 dft1 c1) <$> unifyNVPatsU ps1 ps2

unifyNVConPat :: NVConPat -> NVConPat -> Maybe (NVConPat, PU)
unifyNVConPat cp1 cp2 = unifyNVConPat0 cp1 cp2 emptyPU

unifyNVConPat' :: (Var, NVConPat) -> (Var, NVConPat) -> Maybe (NVConPat, PU)
unifyNVConPat' (cv1, cp1) (cv2, cp2) = if cv1 /= cv2 then Nothing else unifyNVConPat cp1 cp2

unifyNVConPat0 :: NVConPat -> NVConPat -> PU -> Maybe (NVConPat, PU)
unifyNVConPat0 (NVConPat ct1 dft1 c1 ps1) (NVConPat ct2 dft2 c2 ps2)
               pu@(r1@(NVRename m1), r2@(NVRename m2))
  = if c1 /= c2
    then Nothing
    else case unifyNVPats ps1 ps2 pu of
      Nothing -> Nothing
      Just (ps', pu') ->Just (NVConPat ct1 dft1 c1 ps', pu')

unifyNVPats :: [NVPat] -> [NVPat] -> PU -> Maybe ([NVPat], PU)
unifyNVPats [] [] pu = Just ([], pu)
unifyNVPats (p1 : ps1) (p2 : ps2) pu = do
  (p', pu') <- unifyNVPat0 p1 p2 pu
  (ps', pu'') <- unifyNVPats ps1 ps2 pu'
  Just (p' : ps', pu'')
unifyNVPats _ _ _ = Nothing

deepUnifyNVConPat1in2 :: (Var, NVConPat) -> (Var, NVConPat) -> Maybe (NVConPat, PU)
deepUnifyNVConPat1in2 p1@(cv1, cp1) p2@(cv2, cp2@(NVConPat ct2 dft2 c2 ps2))
  | cv1 == cv2
  , Just p <- unifyNVConPat' p1 p2
  = Just p
  | otherwise
  = first (NVConPat ct2 dft2 c2) <$> h id ps2
    where
      h :: ([NVPat] -> [NVPat]) -> [NVPat] -> Maybe ([NVPat], PU)
      h acc [] = Nothing
      h acc (pat : pats)
        | NVPAsCon vi cpi <- pat
        , Just (cpi', pu) <- deepUnifyNVConPat1in2 p1 (vi, cpi)
        = Just (acc $ NVPAsCon vi cpi' : pats, pu)
        | otherwise
        = h (acc . (pat :)) pats

deepUnifyNVConPat :: (Var, NVConPat) -> (Var, NVConPat) -> Maybe (NVConPat, PU)
deepUnifyNVConPat p1 p2 = deepUnifyNVConPat1in2 p1 p2 `mplus` deepUnifyNVConPat1in2 p2 p1

-- attaching to an inner variable is accepted if the corresponding subpatterns unify.
attachNVConPat :: Var -> NVConPat -> NVPat -> Maybe NVPat
attachNVConPat v cp (NVPVar v') = if v == v' then Just (NVPAsCon v' cp) else Nothing
attachNVConPat v cp (NVPAsCon v' cp')
  | v == v'    = case unifyNVConPat cp cp' of
    Nothing -> Nothing
    Just (cp'', _pu) -> Just $ NVPAsCon v' cp''
  | otherwise  = NVPAsCon v' <$> attachToNVConPat v cp cp'

attachToNVConPat :: Var -> NVConPat -> NVConPat -> Maybe NVConPat
attachToNVConPat v cp (NVConPat ct dft c ps)
  =NVConPat ct dft c <$> h ps
    where
      h :: [NVPat] -> Maybe [NVPat]
      h [] = Just []
      h (p : ps') = case attachNVConPat v cp p of
        Nothing -> (p :) <$> h ps'
        Just p' -> Just $ p' : ps' -- patterns are linear: each variable occurs only once.


matchNVPat :: NVPat -> NVPat -> Maybe NVRename
matchNVPat p1 p2 = matchNVPat0 p1 p2 emptyNVRename

matchNVPat0 :: NVPat -> NVPat -> NVRename -> Maybe NVRename
matchNVPat0 p1 p2 r
   | v1 <- getNVPatVar p1
   , v2 <- getNVPatVar p2
  = case lookupNVRename v1 r of
  Just v2' ->    if v2 == v2'  then Just r
                               else Nothing -- clash
  Nothing -> case p1 of
    NVPVar _v1 -> Just $ insertNVRename v1 v2 r
    NVPAsCon _v1 (NVConPat ct1 dft1 c1 ps1) -> insertNVRename v1 v2 <$> case p2 of
      NVPVar _v2 -> Nothing
      NVPAsCon _v2 (NVConPat ct2 dft2 c2 ps2) -> if c1 /= c2
        then Nothing
        else matchNVPats ps1 ps2 r

matchNVConPat :: NVConPat -> NVConPat -> Maybe NVRename
matchNVConPat  p1 p2 = matchNVConPat0 p1 p2 emptyNVRename

matchNVConPat0 :: NVConPat -> NVConPat -> NVRename -> Maybe NVRename
matchNVConPat0 (NVConPat ct1 dft1 c1 ps1) (NVConPat ct2 dft2 c2 ps2) r@(NVRename m)
  = if c1 /= c2
    then Nothing
    else matchNVPats ps1 ps2 r

-- Spec: @deepMatchNVConPat cp cp' = Just r@
-- iff @r@ is the least renaming such that @renameNVConpat r cp@ occurs in @cp'@.
deepMatchNVConPat :: NVConPat -> NVConPat -> Maybe NVRename
deepMatchNVConPat cp cp'@(NVConPat ct2 dft2 c2 ps2)
  = case matchNVConPat cp cp' of
      Just r ->Just  r
      Nothing -> h $ withInnerNVPats ps2
        where
          h :: [(Var, NVConPat)] -> Maybe NVRename
          h [] = Nothing
          h ((_, cpi) : ps) = case deepMatchNVConPat cp cpi of
            Nothing -> h ps
            x -> x

matchNVPats :: [NVPat] -> [NVPat] -> NVRename -> Maybe NVRename
matchNVPats [] [] r = Just r
matchNVPats (p1 : ps1) (p2 : ps2) r  =    matchNVPat0 p1 p2 r
                                     >>=  matchNVPats ps1 ps2
matchNVPats _ _ _ = Nothing

mkFloatingPLet :: NVPat -> NVTTerm -> Floating
mkFloatingPLet pat rhs = mkFloatingPLet' pat rhs []

mkFloatingPLet' :: NVPat -> NVTTerm -> [Var] -> Floating
mkFloatingPLet' pat rhs vs = FloatingPLet
    { pletPat      = pat
    , pletRHS      = rhs
    , pletFVars    = fvarsNVTTerm rhs
    , flExtraScope = vs
    }

flFreeVars :: Floating -> VarSet
flFreeVars plet@(FloatingPLet {}) = pletFVars plet
flFreeVars fc@(FloatingCase {}) = singletonVarSet $ fcaseScrutinee fc

flBoundVars :: Floating -> [Var]
flBoundVars (FloatingPLet {pletPat = p}) = patVars p
flBoundVars (FloatingCase {fcasePat = cp}) = boundNVConPatVars cp

flRevBoundVars :: Floating -> [Var]
flRevBoundVars = reverse . flBoundVars

-- The functions |renameNVPat|, |renameNVConPat|, and |renameFloating|
-- are to be used with renamings resulting from pushout unification.

renameNVConPat :: NVRename -> NVConPat -> NVConPat
renameNVConPat r (NVConPat ct dft c pats)
  = NVConPat ct (renameNVTTerm r dft) c (map (renameNVPat r) pats)

renameNVPat :: NVRename -> NVPat -> NVPat
renameNVPat r (NVPVar v) = NVPVar $ renameVar r v
renameNVPat r (NVPAsCon v cp) = NVPAsCon (renameVar r v) (renameNVConPat r cp)

renameNVPatTopVar :: NVRename -> NVPat -> NVPat
renameNVPatTopVar r (NVPVar v) = NVPVar $ renameVar r v
renameNVPatTopVar r (NVPAsCon v cp) = NVPAsCon (renameVar r v) cp

renameFloating :: NVRename -> Floating -> Floating
renameFloating r fl@(FloatingPLet {}) = mkFloatingPLet' pat' rhs' vs'
  where
   pat' = renameNVPat r $ pletPat fl
   rhs' =  renameNVTTerm r $ pletRHS fl
   vs' = map (renameVar r) $ flExtraScope fl
renameFloating r fl@(FloatingCase {}) = FloatingCase
  {fcaseScrutinee = renameVar r $ fcaseScrutinee fl
  ,fcasePat = renameNVConPat r $ fcasePat fl
  ,flExtraScope = map (renameVar r) $ flExtraScope fl
  }

-- to rename only the free variables in a |Floating|:
renameFloatingFVars :: NVRename -> Floating -> Floating
renameFloatingFVars r fl@(FloatingPLet {}) = mkFloatingPLet pat rhs'
  where
   pat = pletPat fl
   rhs' = renameNVTTerm r $ pletRHS fl
renameFloatingFVars r fl@(FloatingCase {}) = fl
  {fcaseScrutinee = renameVar r $ fcaseScrutinee fl
  }

addExtraScope :: [Var] -> Floating -> Floating
addExtraScope vs fl = fl { flExtraScope = vs ++ flExtraScope fl }

-- \edcomm{WK}{Use |flExtraScope|?}
matchFloating :: Floating -> Floating -> Maybe NVRename
matchFloating fl1@(FloatingPLet {pletPat = pat1, pletRHS = rhs1})
              fl2@(FloatingPLet {pletPat = pat2, pletRHS = rhs2})
  = if let b = rhs1 == rhs2
       in {- trace (show $ P.text "matchFloating: " P.<+> P.prettyPrec 10 rhs1  P.$$ P.text " |=> " P.<+> P.prettyPrec 10 rhs2  P.<+> P.text " --> " P.$$ P.pretty b) -} b
  then let m = matchNVPat pat1 pat2
       in {- trace (show $ P.text "matchFloating: " P.<+> P.prettyPrec 10 pat1 P.$$ P.text " |=> " P.<+> P.prettyPrec 10 pat2  P.<+> P.text " --> " P.$$ P.pretty m) -} m
  else Nothing
matchFloating fl1@(FloatingCase v1 cp1 extraScope1)
              fl2@(FloatingCase v2 cp2 extraScope2)
  = if v1 == v2
  then matchNVConPat cp1 cp2
  else -- \edcomm{WK}{deepMathching not yet connected here!}
       Nothing
matchFloating _ _ = Nothing
 -- \edcomm{WK}{Matching FloatingCase into FloatingPLet still missing.}

matchFloatings :: Floating -> [Floating] -> Maybe NVRename
matchFloatings fl = msum . map (matchFloating fl)
