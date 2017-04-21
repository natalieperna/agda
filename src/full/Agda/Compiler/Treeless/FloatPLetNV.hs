{-# LANGUAGE CPP #-}
module Agda.Compiler.Treeless.FloatPLetNV where

import Control.Applicative
import Control.Monad.Reader
import Data.Monoid
import qualified Data.Map as Map
import Data.Function (on)
import qualified Data.IntSet as IntSet
import Data.IntSet (IntSet)

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
import Agda.Compiler.Treeless.NVTTerm

import Agda.Utils.Permutation

import Data.Word (Word64)

import Agda.Utils.Impossible
#include "undefined.h"

data PLet = PLet
  { pletFVars :: IntSet
  , pletBVars :: IntSet
  , eTerm :: NVTTerm -- |NVTErased| signals the end of the pattern
  } deriving (Show)

corePLet :: PLet -> (IntSet, NVTTerm) -- let-body only
corePLet (PLet fv1 _ (NVTLet _ t1 _)) = (fv1, t1)
corePLet _ = __IMPOSSIBLE__

instance Eq PLet where
  (==) = (==) `on` corePLet

applyPLet :: NVTTerm -> NVTTerm -> NVTTerm
applyPLet (NVTLet v t1 b) a = h b
  where
    h (NVTCase v' ct def [NVTACon c cvars b'])
      = NVTCase v' ct def [NVTACon c cvars (h b')]
    h NVTErased = a
    h _ = __IMPOSSIBLE__
applyPLet _ _ = __IMPOSSIBLE__

-- If |splitPLet t = Just (pl, t')|, then |applyPLet (eTerm pl) t' = t|.
splitPLet :: NVTTerm -> Maybe (PLet, NVTTerm)
splitPLet (NVTLet v t1 (NVTCase v' ct def [NVTACon c cvars t2])) | v == v' && harmless def
  = Just (PLet fvs bvs t0, t2)
  where
    fvs = fvarsNVTTerm t0
    bvs = bvarsNVTTerm t0
    t0 = NVTLet v t1 (NVTCase v ct def [NVTACon c cvars NVTErased])
    harmless (NVTError _)  = True
    harmless NVTUnit       = True
    harmless NVTErased     = True
    harmless NVTSort       = True
    harmless _             = False
splitPLet _ = Nothing

joinPLets :: ([PLet], NVTTerm) -> ([PLet], NVTTerm) -> ([PLet], (NVTTerm, NVTTerm))
joinPLets (ps1, t1) (ps2, t2) = h 0 id 0 ps1 t1 0 ps2 t2
  where
    -- |d1, d2| are the distances from the top
    --
    h :: Int                 -- |countBindersPLets (acc [])| 
      -> ([PLet] -> [PLet])  -- |acc|, already processed
      -> Int -> [PLet] -> NVTTerm
      -> Int -> [PLet] -> NVTTerm
      -> ([PLet], (NVTTerm, NVTTerm))
    h d0 acc d1 []  t1 d2 ps2 t2 = (acc ps2, (t1, t2))
    h d0 acc d1 ps1 t1 d2 []  t2 = (acc ps2, (t1, t2))
    h d0 acc d1 ps1@(p1 : ps1') t1 d2 ps2@(p2 : ps2') t2 = undefined

floatPLet0 :: NVTTerm -> ([PLet], NVTTerm)
floatPLet0 t = case splitPLet t of
  Just (p, t') -> case floatPLet0 t' of
    (ps, t'') -> (p : ps, t'')
  Nothing -> case t of
    NVTVar _ -> ([], t)
    NVTPrim _ -> ([], t)
    NVTDef _ -> ([], t)
    NVTApp tf tas -> undefined
    NVTLam v tb -> undefined
    NVTLit _ -> ([], t)
    NVTCon _ -> ([], t)
    NVTLet v te tb -> undefined
    NVTCase i ct dft alts -> undefined
    NVTUnit -> ([], t)
    NVTSort -> ([], t)
    NVTErased -> ([], t)
    NVTError _ -> ([], t)


testFloatPLet :: String
testFloatPLet = let r = splitPLet tt1
  in "\n=== FloatPLet: " ++ shows r "\n"

tt1 :: NVTTerm
tt1 = NVTLet (V 0) (NVTLit (LitNat NoRange 15))
   (NVTCase (V 0) (CTData $ name0 1 "Pair") NVTErased [NVTACon (name0 2 "pair") [V 1, V 2]
     (NVTLit (LitNat NoRange 42))])

name0 :: Word64 -> RawName -> QName
name0 i s = QName (MName []) (Name (NameId i 0) (C.Name NoRange [C.Id s]) NoRange noFixity')