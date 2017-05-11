{-# LANGUAGE CPP #-}
module Agda.Compiler.Treeless.SplitPLet where

-- import Control.Applicative
-- import Control.Monad.Reader
-- import Data.Monoid

import qualified Data.IntSet as IntSet
import qualified Data.Map as Map

import Agda.Syntax.Common
import Agda.Syntax.Treeless
import Agda.Syntax.Literal
-- import Agda.Syntax.Position
-- import Agda.Syntax.Fixity
-- import Agda.Syntax.Abstract.Name
-- import qualified Agda.Syntax.Concrete.Name as C
-- import Agda.TypeChecking.Substitute
import Agda.Compiler.Treeless.Subst (freeVars)
-- import Agda.Compiler.Treeless.Compare

import Agda.Utils.Impossible
#include "undefined.h"



-- The first argument to @applyPLet@ is a pattern-let prefix,
-- that is, a TTerm prefix that can be translated into a pattern let binding,
-- encoded as a TTerm delimited by TErase, see @data PLet@ in @Syntax.Treeless@.
--
-- The call @applyPLet pl t@  substitutes @t@ for the @TErased@ in @pl@..
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
      { pletFreeVars = fvs -- throw away Occurs to avoid import cycle
      , pletNumBinders = maxv
      , eTerm = TLet t1 pat
      }
    , t'
    )
  where
    fvs = Map.foldWithKey (\ k _ -> IntSet.insert k) IntSet.empty $ freeVars t1
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

tPLetView :: TTerm -> ([PLet], TTerm)
tPLetView = h id
  where
    h acc t = case splitPLet t of
      Nothing -> (acc [], t)
      Just (plet, t') -> h (acc . (plet :)) t'

splitPLets :: TTerm -> Maybe ([PLet], TTerm)
splitPLets t = do
  (plet, t')  <- splitPLet t
  let (plets, t'') = tPLetView t'
  Just (plet : plets, t'')


-- WK: |extractCrossCallFloat| will be replaced by generation by floatPatterns!
extractCrossCallFloat :: TTerm -> Maybe CrossCallFloat
extractCrossCallFloat t = case tLamView t of
   (varNum, t') -> do
     (plets, b) <- splitPLets t'
     Just $ CrossCallFloat
       { ccfLambdaLen = varNum
       , ccfPLets = plets
       , ccfBody = b
       }
