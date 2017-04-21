{-# LANGUAGE CPP #-}
module Agda.Compiler.Treeless.NVTTerm where

-- A variant of |TTerm| using named variables.

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State
import Data.Monoid
import qualified Data.Map as Map
import Data.List (elemIndex)
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

data NVTTerm
  = NVTVar Var
  | NVTPrim TPrim
  | NVTDef QName
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

instance Eq NVTTerm where (==) = eqNVTTerm

eqNVTTerm :: NVTTerm -> NVTTerm -> Bool
eqNVTTerm = eqT IntMap.empty
  where
    eqT :: IntMap Int -> NVTTerm -> NVTTerm -> Bool
    eqT m (NVTVar (V i)) (NVTVar (V j)) = case IntMap.lookup i m of
      Nothing -> i == j
      Just j' -> j == j'
    eqT m (NVTPrim p) (NVTPrim p') = p == p'
    eqT m (NVTDef n) (NVTDef n') = n == n'
    eqT m (NVTApp f ts) (NVTApp f' ts') = and $ zipWith (eqT m) (f : ts) (f' : ts')
    eqT m (NVTLam (V i) b) (NVTLam (V j) b') = eqT (IntMap.insert i j m) b b'
    eqT m (NVTLit l) (NVTLit l') = l == l'
    eqT m (NVTCon n) (NVTCon n') = n == n'
    eqT m (NVTLet (V i) e b) (NVTLet (V j) e' b') = eqT m e e' && eqT (IntMap.insert i j m) b b'
    eqT m (NVTCase (V i) cty dft alts) (NVTCase (V j) cty' dft' alts') =
      (case IntMap.lookup i m of Nothing -> i == j; Just j' -> j == j') &&
      and (zipWith (eqA m) alts alts')
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


type U = State Int

getVar :: U Var
getVar = do
  i <- get
  put $ succ i
  return $ V i

getVars :: Int -> U [Var]
getVars k = sequence $ replicate k getVar

fromTTerm :: [Var] -> TTerm -> U NVTTerm
fromTTerm vs (TVar k) = return $ NVTVar (vs !! k)
fromTTerm vs (TPrim p) = return $ NVTPrim p
fromTTerm vs (TDef name) = return $ NVTDef name
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

fromTAlt :: [Var] -> TAlt -> U NVTAlt
fromTAlt vs (TACon name arity b) = do
  cvars <- getVars arity
  b' <- fromTTerm (reverse cvars ++ vs) b
  return $ NVTACon name cvars b'
fromTAlt vs (TAGuard g b) = NVTAGuard <$> fromTTerm vs g <*> fromTTerm vs b
fromTAlt vs (TALit lit b) = NVTALit lit <$> fromTTerm vs b


toTTerm :: [Var] -> NVTTerm -> TTerm
toTTerm vs (NVTVar v) = TVar (maybe __IMPOSSIBLE__ id $ elemIndex v vs)
toTTerm vs (NVTPrim p) = TPrim p
toTTerm vs (NVTDef name) = TDef name
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


fvarsNVTTerm :: NVTTerm -> IntSet
fvarsNVTTerm (NVTVar (V i)) = IntSet.singleton i
fvarsNVTTerm (NVTPrim p) = IntSet.empty
fvarsNVTTerm (NVTDef name) = IntSet.empty
fvarsNVTTerm (NVTApp f ts) = IntSet.unions $ fvarsNVTTerm f : map fvarsNVTTerm ts
fvarsNVTTerm (NVTLam (V i) b) = IntSet.delete i $ fvarsNVTTerm b
fvarsNVTTerm (NVTLit lit) = IntSet.empty
fvarsNVTTerm (NVTCon c) = IntSet.empty
fvarsNVTTerm (NVTLet (V i) e b) = fvarsNVTTerm e `IntSet.union` IntSet.delete i (fvarsNVTTerm b)
fvarsNVTTerm (NVTCase (V i) caseType dft alts) = IntSet.unions $ IntSet.insert i (fvarsNVTTerm dft) : map fvarsNVTAlt alts
fvarsNVTTerm NVTUnit = IntSet.empty
fvarsNVTTerm NVTSort = IntSet.empty
fvarsNVTTerm NVTErased = IntSet.empty
fvarsNVTTerm (NVTError t) = IntSet.empty

fvarsNVTAlt :: NVTAlt -> IntSet
fvarsNVTAlt (NVTACon name cvars b) = let bvars = IntSet.fromList (map unV cvars)
  in IntSet.difference (fvarsNVTTerm b) bvars
fvarsNVTAlt (NVTAGuard g b) = fvarsNVTTerm g `IntSet.union` fvarsNVTTerm b
fvarsNVTAlt (NVTALit lit b) = fvarsNVTTerm b


bvarsNVTTerm :: NVTTerm -> IntSet
bvarsNVTTerm (NVTVar v) = IntSet.empty
bvarsNVTTerm (NVTPrim p) = IntSet.empty
bvarsNVTTerm (NVTDef name) = IntSet.empty
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

