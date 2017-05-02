{-# LANGUAGE CPP #-}
module Agda.Compiler.Treeless.FloatPLet where

import Control.Applicative
import Control.Monad.Reader
import Data.Monoid
import qualified Data.Map as Map
import Data.Map (Map)

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

data MinFreeVar = MinFV Nat | NoFV
  deriving (Eq, Ord)

instance Show MinFreeVar where
  showsPrec _ (MinFV i)  = shows i
  showsPrec _ NoFV       = ('⊤' :)

instance Num MinFreeVar where  -- only (+), (-), and fromInteger are relevant
  NoFV + _ = NoFV
  _ + NoFV = NoFV
  MinFV i + MinFV j = MinFV (i + j)
  NoFV - _ = NoFV
  MinFV _ - NoFV = __IMPOSSIBLE__
  MinFV i - MinFV j = MinFV (i - j)
  _ * _   = __IMPOSSIBLE__
  negate  = __IMPOSSIBLE__
  abs     = __IMPOSSIBLE__
  signum  = __IMPOSSIBLE__
  fromInteger i = MinFV (fromInteger i)

data PLet = PLet
  { minFree :: MinFreeVar
  , pletFreeVars :: Map Nat Occurs
  , pletNumBinders :: Nat  -- number of all binders on the spine of |eTerm|
  , eTerm :: TTerm
  } deriving (Eq, Ord, Show)

instance Subst TTerm PLet where
  applySubst su p = p { eTerm = applySubst su $ eTerm p }


applyPLet :: TTerm -> TTerm -> TTerm
applyPLet (TLet t1 b) a = TLet t1 $ h b
  where
    h (TCase v' ct def [TACon c cArity b'])
      = TCase v' ct def [TACon c cArity (h b')]
    h TErased = a
    h _ = __IMPOSSIBLE__
applyPLet _ _ = __IMPOSSIBLE__


-- If |splitPLet t = Just (pl, t')|, then |applyPLet (eTerm pl) t' = t|.
splitPLet :: TTerm -> Maybe (PLet, TTerm)
splitPLet (TLet t1 t2) = case splitBoundedCase 0 t2 of
  Nothing -> Nothing
  Just ((pat, maxv), t') -> Just
    ( PLet
      { minFree = d
      , pletFreeVars = fvs
      , pletNumBinders = maxv
      , eTerm = TLet t1 pat
      }
    , t'
    )
  where
    fvs = freeVars t1
    d = maybe NoFV MinFV $ fst . fst <$> Map.minViewWithKey fvs
splitPLet _ = Nothing

-- |splitBoundedCase maxv t = Just ((t0, maxv'), t1)| means
-- that |t| matched on a variable |<= maxv|,
-- and |applyPLet t0 t1 == t|,
-- and |maxv'| is |maxv| plus the number of binders in |t0|.
splitBoundedCase :: Nat -> TTerm -> Maybe ((TTerm, Nat), TTerm)
splitBoundedCase maxv (TCase v ct dft [TACon c cArity t2]) | v <= maxv && harmlessTT dft
  = let ((b', maxv'), t') = let maxv2 = maxv + cArity in case splitBoundedCase maxv2 t2 of
          Nothing -> ((TErased, maxv2), t2)
          Just r -> r
    in Just ((TCase v ct dft [TACon c cArity b'], maxv'), t')
splitBoundedCase _ _ = Nothing



-- ``harmless'' in the sense of not contributing possible control flow
-- if used as default expression in |TCase|:
harmlessTT :: TTerm -> Bool
harmlessTT (TError _)  = True
harmlessTT TUnit       = True
harmlessTT TErased     = True
harmlessTT TSort       = True
harmlessTT _           = False

countBindersPLet :: PLet -> Nat
countBindersPLet = pletNumBinders

countBindersPLets :: [PLet] -> Nat
countBindersPLets = sum . map countBindersPLet

-- the pattern-let lists of type [PLet] will be sorted in descending order.

swapP :: Int -> Int -> Int -> Permutation
swapP offset m n = Perm (n + m) $  [0 .. offset - 1]
                                ++ [offset + n .. offset + n + m - 1]
                                ++ [offset .. offset + m - 1]

-- |insertPLet| is only intended for the result of |splitPLet|
insertPLet :: PLet -> ([PLet], TTerm) -> ([PLet], TTerm)
insertPLet p ([], t) = ([p], t)
insertPLet p0 (ps, t) = let
    canMoveAbove, shouldMoveAbove :: PLet -> Bool
    canMoveAbove = ((MinFV d0) <=) . minFree
    shouldMoveAbove = ((minFree p0 <) . (flip (-) (MinFV d0)) . minFree)
    (ps1, ps2) = span (\ p -> canMoveAbove p && shouldMoveAbove p) ps
    d0 = countBindersPLet p0
    d1 = countBindersPLets ps1
    d2 = countBindersPLets ps2
    raise :: PLet -> PLet
    raise p = p { minFree = minFree p - MinFV d0
                , eTerm = applySubst (strengthenS __IMPOSSIBLE__ d0) (eTerm p)
                }
    p0' = p0 { minFree = minFree p0 + MinFV d1
             , eTerm = applySubst (wkS d1 idS) (eTerm p0)
             }
    
    lower offset p = p { minFree = minFree p + MinFV d0
                       , eTerm = renameP __IMPOSSIBLE__ (swapP offset d0 d1) (eTerm p)
                       }
    lowers :: Int -> [PLet] -> [PLet]
    lowers _ [] = []
    lowers offset (p : ps) = lower offset p : lowers (offset + pletNumBinders p) ps
  in ( map raise ps1 ++ p0' : lowers 0 ps2
     , renameP __IMPOSSIBLE__ (swapP d2 d0 d1) t
     )

joinPLets :: ([PLet], TTerm) -> ([PLet], TTerm) -> ([PLet], (TTerm, TTerm))
joinPLets (ps1, t1) (ps2, t2) = h 0 id 0 ps1 t1 0 ps2 t2
  where
    -- |d1, d2| are the distances from the top
    --
    h :: Int                 -- |countBindersPLets (acc [])| 
      -> ([PLet] -> [PLet])  -- |acc|, already processed
      -> Int -> [PLet] -> TTerm
      -> Int -> [PLet] -> TTerm
      -> ([PLet], (TTerm, TTerm))
    h d0 acc d1 []  t1 d2 ps2 t2 = (acc ps2, (t1, t2))
    h d0 acc d1 ps1 t1 d2 []  t2 = (acc ps2, (t1, t2))
    h d0 acc d1 ps1@(p1 : ps1') t1 d2 ps2@(p2 : ps2') t2 = undefined

floatPLet0 :: TTerm -> ([PLet], TTerm)
floatPLet0 t = case splitPLet t of
  Just (p, t') -> case floatPLet0 t' of
    r -> insertPLet p r
  Nothing -> case t of
    TVar _ -> ([], t)
    TPrim _ -> ([], t)
    TDef _ -> ([], t)
    TApp tf tas -> undefined
    TLam tb -> undefined
    TLit _ -> ([], t)
    TCon _ -> ([], t)
    TLet te tb -> undefined
    TCase i ct dft alts -> undefined
    TUnit -> ([], t)
    TSort -> ([], t)
    TErased -> ([], t)
    TError _ -> ([], t)


testFloatPLet :: String
testFloatPLet = let r = splitPLet tt1
  in "\n=== FloatPLet: " ++ shows r "\n"

tt1 :: TTerm
tt1 = TLet (TLit (LitNat NoRange 15))
   (TCase 0 (CTData $ name0 1 "Pair") TErased [TACon (name0 2 "pair") 2
     (TLit (LitNat NoRange 42))])

name0 :: Word64 -> RawName -> QName
name0 i s = QName (MName []) (Name (NameId i 0) (C.Name NoRange [C.Id s]) NoRange noFixity')