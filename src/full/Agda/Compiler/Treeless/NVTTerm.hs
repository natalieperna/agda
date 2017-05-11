{-# LANGUAGE CPP #-}
module Agda.Compiler.Treeless.NVTTerm where

-- A variant of |TTerm| using named variables.

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
import Agda.TypeChecking.Substitute
import Agda.Compiler.Treeless.Subst
import Agda.Compiler.Treeless.Compare

import Agda.Utils.Permutation

import Data.Word (Word64)

import Agda.Utils.Impossible
#include "undefined.h"

newtype Var = V {unV :: Int} deriving (Eq, Ord, Show)

newtype VarSet = VarSet IntSet
instance Show VarSet where showsPrec p (VarSet s) = showsPrec p s

emptyVarSet :: VarSet
emptyVarSet = VarSet IntSet.empty
singletonVarSet :: Var -> VarSet
singletonVarSet (V i) = VarSet $ IntSet.singleton i
insertVarSet :: Var -> VarSet -> VarSet
insertVarSet (V i) (VarSet s) = VarSet $ IntSet.insert i s
deleteVarSet :: Var -> VarSet -> VarSet
deleteVarSet (V i) (VarSet s) = VarSet $ IntSet.delete  i s
elemVarSet :: Var -> VarSet -> Bool
elemVarSet (V i) (VarSet s) = IntSet.member i s
listToVarSet :: [Var] -> VarSet
listToVarSet = foldr insertVarSet emptyVarSet
unionVarSet :: VarSet -> VarSet -> VarSet
unionVarSet (VarSet s1) (VarSet s2) = VarSet $ IntSet.union s1 s2
unionsVarSet :: [VarSet] -> VarSet
unionsVarSet = foldr unionVarSet emptyVarSet

data NVTTerm
  = NVTVar Var
  | NVTPrim TPrim
  | NVTDef NVTDefVariant QName
  | NVTApp NVTTerm [NVTTerm]
  | NVTLam Var NVTTerm
  | NVTLit Literal
  | NVTCon QName
  | NVTLet Var NVTTerm NVTTerm
  | NVTCase Var CaseType NVTTerm [NVTAlt]
  -- ^ Case scrutinee (always variable), case type, default value, alternatives
  | NVTUnit
  | NVTSort
  | NVTErased
  | NVTError TError
  deriving (Show)


data NVTAlt
  = NVTACon QName [Var] NVTTerm
  | NVTAGuard NVTTerm NVTTerm
  | NVTALit Literal NVTTerm
  deriving (Show)

-- ``Flavour'' of @NVTDef@, analogous to @TDefVariant@
data NVTDefVariant
  = NVTDefDefault             -- traditional variants: "du*" or "d*"
  | NVTDefAbstractPLet [Var]  -- additional variable arguments for "dv*" variant.
  deriving (Show)

instance Eq NVTTerm where (==) = eqNVTTerm

eqNVTTerm :: NVTTerm -> NVTTerm -> Bool
eqNVTTerm = eqT IntMap.empty
  where
    eqV :: IntMap Int -> Var -> Var -> Bool
    eqV m (V i) (V j) = case IntMap.lookup i m of
      Nothing -> i == j
      Just j' -> j == j'

    eqVs :: IntMap Int -> [Var] -> [Var] -> Bool
    eqVs m [] [] = True
    eqVs m (u : us) (v : vs) = eqV m u v && eqVs m us vs
    eqVs _ _ _ = False

    eqVariant :: IntMap Int -> NVTDefVariant -> NVTDefVariant -> Bool
    eqVariant _ NVTDefDefault NVTDefDefault = True
    eqVariant m (NVTDefAbstractPLet us) (NVTDefAbstractPLet vs) = eqVs m us vs
    eqVariant _ _ _ = False

    eqT :: IntMap Int -> NVTTerm -> NVTTerm -> Bool
    eqT m (NVTVar v) (NVTVar v') = eqV m v v'
    eqT m (NVTPrim p) (NVTPrim p') = p == p'
    eqT m (NVTDef var n) (NVTDef var' n') = n == n' && eqVariant m var var'
    eqT m (NVTApp f ts) (NVTApp f' ts') = and $ zipWith (eqT m) (f : ts) (f' : ts')
    eqT m (NVTLam (V i) b) (NVTLam (V j) b') = eqT (IntMap.insert i j m) b b'
    eqT m (NVTLit l) (NVTLit l') = l == l'
    eqT m (NVTCon n) (NVTCon n') = n == n'
    eqT m (NVTLet (V i) e b) (NVTLet (V j) e' b') = eqT m e e' && eqT (IntMap.insert i j m) b b'
    eqT m (NVTCase v cty dft alts) (NVTCase v' cty' dft' alts') =
      eqV m v v' && and (zipWith (eqA m) alts alts')
    eqT m NVTUnit NVTUnit = True
    eqT m NVTSort NVTSort = True
    eqT m NVTErased NVTErased = True
    eqT m (NVTError t) (NVTError t') = t == t'
    eqT _ _ _ = False

    eqA :: IntMap Int -> NVTAlt -> NVTAlt -> Bool
    eqA m (NVTACon c vs b) (NVTACon c' vs' b') = let
        m' = IntMap.fromList (zip (map unV vs) (map unV vs')) `IntMap.union` m
      in eqT m' b b'
    eqA m (NVTAGuard g b) (NVTAGuard g' b') = eqT m g g' && eqT m b b'
    eqA m (NVTALit lit b) (NVTALit lit' b') = lit == lit' && eqT m b b'
    eqA _ _ _ = False


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
fromTTerm vs (TVar k) = return $ NVTVar (vs !! k)
fromTTerm vs (TPrim p) = return $ NVTPrim p
fromTTerm vs (TDef var name) = return $ NVTDef var' name
  where
    var' = case var of
      TDefDefault -> NVTDefDefault
      TDefAbstractPLet is -> NVTDefAbstractPLet $ map (vs !!) is
fromTTerm vs (TApp f ts) = NVTApp <$> fromTTerm vs f <*> mapM (fromTTerm vs) ts
fromTTerm vs (TLam b) = do
  v <- getVar
  NVTLam v <$> fromTTerm (v : vs) b
fromTTerm vs (TLit lit) = return $ NVTLit lit
fromTTerm vs (TCon c) = return $ NVTCon c
fromTTerm vs (TLet e b) = do
  e' <- fromTTerm vs e
  v <- getVar
  NVTLet v e' <$> fromTTerm (v : vs) b
fromTTerm vs (TCase k caseType dft alts) = NVTCase (vs !! k) caseType
  <$> fromTTerm vs dft
  <*> mapM (fromTAlt vs) alts
fromTTerm vs TUnit = return NVTUnit
fromTTerm vs TSort = return NVTSort
fromTTerm vs TErased = return NVTErased
fromTTerm vs (TError t) = return $ NVTError t

fromTAlt :: Monad m => [Var] -> TAlt -> U m NVTAlt
fromTAlt vs (TACon name arity b) = do
  cvars <- getVars arity
  b' <- fromTTerm (reverse cvars ++ vs) b
  return $ NVTACon name cvars b'
fromTAlt vs (TAGuard g b) = NVTAGuard <$> fromTTerm vs g <*> fromTTerm vs b
fromTAlt vs (TALit lit b) = NVTALit lit <$> fromTTerm vs b

toTTerm' :: NVTTerm -> TTerm
toTTerm' = toTTerm []

fromVar :: Nat -> [Var] -> Var -> Nat -- first argument is __IMPOSSIBLE__
fromVar err vs v = maybe err id $ elemIndex v vs

toTTerm :: [Var] -> NVTTerm -> TTerm
toTTerm vs (NVTVar v) = TVar (fromVar __IMPOSSIBLE__ vs v)
toTTerm vs (NVTPrim p) = TPrim p
toTTerm vs (NVTDef var name) = TDef var' name
  where
    var' = case var of
      NVTDefDefault -> TDefDefault
      NVTDefAbstractPLet us -> TDefAbstractPLet $ map (fromVar __IMPOSSIBLE__ vs) us
toTTerm vs (NVTApp f ts) = TApp (toTTerm vs f) (map (toTTerm vs) ts)
toTTerm vs (NVTLam v b) = TLam $ toTTerm (v : vs) b
toTTerm vs (NVTLit lit) = TLit lit
toTTerm vs (NVTCon c) = TCon c
toTTerm vs (NVTLet v e b) = TLet (toTTerm vs e) (toTTerm (v : vs) b)
toTTerm vs (NVTCase v caseType dft alts) =
  TCase (maybe __IMPOSSIBLE__ id $ elemIndex v vs) caseType (toTTerm vs dft)
    $ map (toTAlt vs) alts
toTTerm vs NVTUnit = TUnit
toTTerm vs NVTSort = TSort
toTTerm vs NVTErased = TErased
toTTerm vs (NVTError t) = TError t


toTAlt :: [Var] -> NVTAlt -> TAlt
toTAlt vs (NVTACon name cvars b) =
  TACon name (length cvars) $ toTTerm (reverse cvars ++ vs) b
toTAlt vs (NVTAGuard g b) = TAGuard (toTTerm vs g) (toTTerm vs b)
toTAlt vs (NVTALit lit b) = TALit lit (toTTerm vs b)


fvarsNVTTerm :: NVTTerm -> VarSet
fvarsNVTTerm (NVTVar v) = singletonVarSet v
fvarsNVTTerm (NVTPrim p) = emptyVarSet
fvarsNVTTerm (NVTDef NVTDefDefault name) = emptyVarSet
fvarsNVTTerm (NVTDef (NVTDefAbstractPLet vs) name) = listToVarSet vs
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

newtype NVRename = NVRename (IntMap Var)

emptyNVRename :: NVRename
emptyNVRename = NVRename IntMap.empty

singletonNVRename :: Var -> Var -> NVRename
singletonNVRename (V i) v@(V j) = NVRename $
   if i == j then IntMap.empty else IntMap.singleton i v

insertNVRename :: Var -> Var -> NVRename -> NVRename
insertNVRename (V i) v@(V j) r@(NVRename m)
  = if i == j then r else NVRename $ IntMap.insert i v m

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
renameNVTTerm r@(NVRename m) t
  | IntMap.null m  = t
  | otherwise      = renTTerm r t
  where
    renTTerm :: NVRename -> NVTTerm -> NVTTerm
    renTTerm r (NVTVar v) = NVTVar $ renameVar r v
    renTTerm r t@(NVTPrim _) = t
    renTTerm r t@(NVTDef NVTDefDefault _) = t
    renTTerm r (NVTDef (NVTDefAbstractPLet vs) name)
      = NVTDef (NVTDefAbstractPLet $ map (renameVar r) vs) name
    renTTerm r (NVTApp f ts) = NVTApp (renTTerm r f) (map (renTTerm r) ts)
    renTTerm r (NVTLam v b) = let
      r'@(NVRename m') = deleteNVRename v r
      in if v `elem` IntMap.elems m'
      then __IMPOSSIBLE__ -- unexpected variable capture
      else NVTLam v $ renameNVTTerm r' b
    renTTerm r t@(NVTLit _) = t
    renTTerm r t@(NVTCon _) = t
    renTTerm r (NVTLet v e b) = let
      r'@(NVRename m') = deleteNVRename v r
      in if v `elem` IntMap.elems m'
      then __IMPOSSIBLE__ -- unexpected variable capture
      else NVTLet v (renTTerm r e) (renameNVTTerm r' b)
    renTTerm r (NVTCase v caseType dft alts) = let
        v' = renameVar r v
      in NVTCase v' caseType (renTTerm r dft) $ map (renameNVTAlt r) alts
    renTTerm r NVTUnit = NVTUnit
    renTTerm r NVTSort = NVTSort
    renTTerm r NVTErased = NVTErased
    renTTerm r t@(NVTError _) = t

    -- The |NVRename| argument has already been confirmed to be non-empty
    renameNVTAlt :: NVRename  -> NVTAlt -> NVTAlt
    renameNVTAlt m (NVTACon name cvars b) =
      let r'@(NVRename m') = foldr deleteNVRename r cvars
      in if any (`elem` IntMap.elems m') cvars
      then __IMPOSSIBLE__ -- unexpected variable capture
      else  NVTACon name cvars $ renameNVTTerm r' b
    renameNVTAlt r (NVTAGuard g b) = NVTAGuard (renTTerm r g) (renTTerm r b)
    renameNVTAlt r (NVTALit lit b) = NVTALit lit (renTTerm r b)

data NVConPat = NVConPat CaseType NVTTerm QName [NVPat]
  deriving (Show)

data NVPat
  = NVPVar Var
  | NVPAsCon Var NVConPat
  deriving (Show)

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
-- that will be the sequence of bound variabe in the result of |caseNVPat|.
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

-- pattern unifiers:
type PU = (NVRename, NVRename)

emptyPU :: PU
emptyPU = (emptyNVRename, emptyNVRename)


-- The result of @unifyNVPat@ contains the unified pattern,
-- and the renamings for matching the argument patterns into that.
--(Full substitutions are not necessary,
--  since every pattern node contains a variable.)
--(Full substitutions are also not useful,
--  since these renamings are intended for use on bodies via @renameNVTTerm@.)
unifyNVPat :: NVPat -> NVPat -> Maybe (NVPat, PU)
unifyNVPat p1 p2 = unifyNVPat0 p1 p2 emptyPU

unifyNVPat0 :: NVPat -> NVPat -> PU -> Maybe (NVPat, PU)
unifyNVPat0 p1 p2 pu@(r1@(NVRename m1), r2@(NVRename m2))
   | v1@(V i1) <- getNVPatVar p1
   , v2@(V i2) <- getNVPatVar p2
  = case IntMap.lookup i1 m1 of
  Just v2' ->    if v2 == v2'  then Just (p2, pu)
                               else Nothing -- renamings have to be injective
  Nothing -> case IntMap.lookup i2 m2 of
    Just v1' ->  if v1 == v1'  then Just (p1, pu)
                               else Nothing
    Nothing -> case p2 of
      NVPVar _v2 -> Just (p1, (r1, insertNVRename v2 v1 r2))
      NVPAsCon _v2 cp2 -> case p1 of
        NVPVar _v1 -> Just (p2, (insertNVRename v1 v2 r1, r2))
        NVPAsCon _v1 cp1 -> case unifyNVConPat0 cp1 cp2 pu of
          Nothing -> Nothing
          Just (cp', pu') -> Just (NVPAsCon v1 cp', pu')

unifyNVConPat :: NVConPat -> NVConPat -> Maybe (NVConPat, PU)
unifyNVConPat cp1 cp2 = unifyNVConPat0 cp1 cp2 emptyPU

unifyNVConPat' :: (Var, NVConPat) -> (Var, NVConPat) -> Maybe (NVConPat, PU)
unifyNVConPat' (cv1, cp1) (cv2, cp2) = if cv1 /= cv2 then Nothing else unifyNVConPat cp1 cp2

deepUnifyNVConPat1in2 :: (Var, NVConPat) -> (Var, NVConPat) -> Maybe (NVConPat, PU)
deepUnifyNVConPat1in2 p1@(cv1, cp1) p2@(cv2, cp2@(NVConPat ct2 dft2 c2 ps2))
  = case unifyNVConPat' p1 p2 of
  Nothing -> h ps2
      where
        h :: [NVPat] -> Maybe (NVConPat, PU)
        h [] = Nothing
        h (pat : pats)  | NVPAsCon vi cpi <- pat
                        , Just (cp', pu) <- deepUnifyNVConPat1in2 p1 (vi, cpi)
                        = do
                           cp'' <- attachToNVConPat vi cp' cp2 -- inefficient, could attach to |pat|
                           Just (cp'', pu)
                                   -- \edcomm{WK}{And |pu| is now wrong. For the time being, |pu| is unused...}
                        | otherwise
                        = h pats
  x -> x

deepUnifyNVConPat :: (Var, NVConPat) -> (Var, NVConPat) -> Maybe (NVConPat, PU)
deepUnifyNVConPat p1 p2 = deepUnifyNVConPat1in2 p1 p2 `mplus` deepUnifyNVConPat1in2 p2 p1


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
matchNVPat0 p1 p2 r@(NVRename m)
   | v1@(V i1) <- getNVPatVar p1
   , v2@(V i2) <- getNVPatVar p2
  = case IntMap.lookup i1 m of
  Just v2' ->    if v2 == v2'  then Just r
                               else Nothing -- clash
  Nothing -> case p1 of
    NVPVar _v1 -> Just $ insertNVRename v1 v2 r
    NVPAsCon _v1 (NVConPat ct1 dft1 c1 ps1) -> case p2 of
      NVPVar _v2 -> Nothing -- \edcomm{WK}{CHeck this again later!}
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
