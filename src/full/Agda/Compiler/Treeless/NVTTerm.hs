{-# LANGUAGE CPP #-}
module Agda.Compiler.Treeless.NVTTerm where

-- A variant of |TTerm| using named variables.

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State
import Data.Monoid
import qualified Data.Map as Map
import Data.List (elemIndex)

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

newtype Var = V Int deriving (Eq, Ord, Show)

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
  deriving (Show, Eq, Ord)


data NVTAlt
  = NVTACon QName [Var] NVTTerm
  | NVTAGuard NVTTerm NVTTerm
  | NVTALit Literal NVTTerm
  deriving (Show, Eq, Ord)

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

