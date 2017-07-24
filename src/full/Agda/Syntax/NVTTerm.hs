{-# LANGUAGE CPP #-}
module Agda.Syntax.NVTTerm where

-- A variant of |TTerm| using named variables.

-- This module, |Agda.Syntax.NVTTerm|, is intended to be imported
-- only via its re-export in |Agda.Compiler.Treeless.NVTTerm|.

import Prelude hiding (Floating)

-- import Control.Arrow (first)
-- import Control.Applicative
-- import Control.Monad.Identity (runIdentity)
-- import Control.Monad.Reader
-- import Control.Monad.State
-- import Data.List (elemIndex)
-- import Data.Maybe (mapMaybe)
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

import Agda.Utils.Impossible
#include "undefined.h"

newtype Var = V {unV :: Int} deriving (Eq, Ord)
instance Show Var where showsPrec _ (V i) = ('v' :) . shows i

newtype VarSet = VarSet IntSet
instance Show VarSet where showsPrec p (VarSet s) = showsPrec p s

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
  = NVTACon QName [Maybe Var] NVTTerm  -- |Nothing| for erased arguments
  | NVTAGuard NVTTerm NVTTerm
  | NVTALit Literal NVTTerm
  deriving (Show)

-- ``Flavour'' of @NVTDef@, originally intended analogous to @TDefVariant@
--
-- Assuming @f@ is known to be @n@-ary, with @m@ used arguments,
-- and that @f@ translated into @dF@, @duF@, @dvF@
-- (that is, @dF@ is @n@-ary, and @duF@ is @m@-ary),
-- and @duF v1 ... vm = let (vSm, ...., vp) = bindRHS in dvF v1 ... vm vSm ... vp@:
--
-- Before floating:
-- @NVTApp (NVTDef NVTDefDefault f) [arg1, ..., argn]@
-- @dF arg1 ... argn@
-- @duF arg1u ... argnu@ where @[arg1u, ..., argnu] = filter used [arg1, ..., argn]@
--
-- During floating:
-- @let v1 = arg1; ...; vm = argm; (vSm, ...., vp) = bindRHS@
--   @in NVTDef (NVTDefFloating [v1U, ... Erased ..., vmU, vSm, ...., vp]) f@
-- @duF arg1 ... argm@
-- @dvF arg1 ... argm vSm ... vp@
--
-- During floating: Not: @NVTApp (NVTDef (NVTDefFloating [vSm, ...., vp]) f) [arg1, ..., argm]@
--
--
-- After floating: Either revert to @NVTDefDefault@, or:
-- @NVTApp (NVTDef NVTDefAbstractPLet f) [arg1, ..., argm, argSm, ...., argp]@
-- @duF arg1 ... argm@
-- @dvF arg1 ... argm argSm, ...., argp@
--
-- Additional complications arise if fewer or more than @n@ arguments are initially supplied.
--
data NVTDefVariant
  = NVTDefDefault         -- traditional variants: "du*" or "d*"
  | NVTDefFloating [Var]  -- additional variable arguments for possible switch to "dv*" variant.
  | NVTDefAbstractPLet    -- with additional arguments for "dv*" variant.
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

    -- Semantically, |NVTDefFloating us| is the same as |NVTDefDefault|.
    -- However, |NVTDefAbstractPLet| is different,
    -- since already applied to additional arguments.
    eqVariant :: NVTDefVariant -> NVTDefVariant -> Bool
    eqVariant NVTDefAbstractPLet NVTDefAbstractPLet = True
    eqVariant NVTDefAbstractPLet _ = False
    eqVariant _ NVTDefAbstractPLet = False
    eqVariant _ _ = True

    eqT :: IntMap Int -> NVTTerm -> NVTTerm -> Bool
    eqT m (NVTVar v) (NVTVar v') = eqV m v v'
    eqT m (NVTPrim p) (NVTPrim p') = p == p'
    eqT m (NVTDef var n) (NVTDef var' n') = n == n' && eqVariant var var'
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
        addVs [] [] m0 = Just m0
        addVs (Nothing : us) (Nothing : vs) m0 = addVs us vs m0
        addVs (Just (V i) : us) (Just (V j) : vs) m0 = IntMap.insert i j <$> addVs us vs m0
        addVs _ _ _ = Nothing
      in case addVs vs vs' m of
        Nothing -> False
        Just m' -> eqT m' b b'
    eqA m (NVTAGuard g b) (NVTAGuard g' b') = eqT m g g' && eqT m b b'
    eqA m (NVTALit lit b) (NVTALit lit' b') = lit == lit' && eqT m b b'
    eqA _ _ _ = False

newtype NVRename = NVRename (IntMap Var)
instance Show NVRename where showsPrec p (NVRename m) = showsPrec p m

emptyNVRename :: NVRename
emptyNVRename = NVRename IntMap.empty

data NVConPat = NVConPat CaseType NVTTerm QName [Bool] [NVPat]
  deriving (Show)

data NVPat
  = NVPVar Var
  | NVPAsCon Var NVConPat
  deriving (Show)

-- pattern unifiers:
type PU = (NVRename, NVRename)

emptyPU :: PU
emptyPU = (emptyNVRename, emptyNVRename)

data Floating
  = FloatingPLet
    { pletPat :: NVPat
    , pletRHS :: NVTTerm
    , pletFVars :: VarSet -- free variables of pletRHS
    , flExtraScope :: [Var]
    }
  | FloatingCase
    { fcaseScrutinee :: Var
    , fcasePat :: NVConPat
    , flExtraScope :: [Var]
    }
   deriving (Show)
