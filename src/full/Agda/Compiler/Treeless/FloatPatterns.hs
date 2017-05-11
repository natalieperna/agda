{-# LANGUAGE CPP #-}
module Agda.Compiler.Treeless.FloatPatterns where

import Prelude hiding (Floating)

import Control.Applicative
import Control.Arrow (second)
import Control.Monad.Reader
import Control.Monad.State
import Data.Monoid
import qualified Data.Map as Map
import Data.Function (on)
import Data.Maybe (isJust)
import Data.List (nub, partition)
import qualified Data.IntSet as IntSet
import Data.IntSet (IntSet)
import qualified Data.IntMap as IntMap
import Data.IntMap (IntMap)

import Agda.Syntax.Common
import Agda.Syntax.Treeless hiding (PLet(..))
import qualified Agda.Syntax.Treeless as T
import Agda.Syntax.Literal
import Agda.Syntax.Position
import Agda.Syntax.Fixity
import Agda.Syntax.Abstract.Name
import qualified Agda.Syntax.Concrete.Name as C
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.Compiler.Treeless.Subst
import Agda.Compiler.Treeless.Compare
import Agda.Compiler.Treeless.NVTTerm

import Agda.Utils.Permutation

import Data.Word (Word64)

import Agda.Utils.Impossible
#include "undefined.h"

data Floating
  = FloatingPLet
    { pletPat :: NVPat
    , pletRHS :: NVTTerm
    , pletFVars :: VarSet -- free variables of pletRHS \edcomm{WK}{still used?}
    }
  | FloatingCase
    { fcaseScrutinee :: Var
    , fcasePat :: NVConPat
    }
   deriving (Show)

flFreeVars :: Floating -> VarSet
flFreeVars plet@(FloatingPLet {}) = pletFVars plet
flFreeVars (FloatingCase v _) = singletonVarSet v

flBoundVars :: Floating -> [Var]
flBoundVars (FloatingPLet {pletPat = p}) = patVars p
flBoundVars (FloatingCase {fcasePat = cp}) = boundNVConPatVars cp


attachConPatToFloating :: Var -> NVConPat -> Floating -> Maybe Floating
attachConPatToFloating v conPat plet@(FloatingPLet {})
  = case attachNVConPat v conPat (pletPat plet) of
      Nothing -> Nothing
      Just pat' -> Just plet { pletPat = pat' }
attachConPatToFloating v conPat fcase@(FloatingCase {})
  = case attachToNVConPat v conPat (fcasePat fcase) of
      Nothing -> Nothing
      Just pat' -> Just fcase { fcasePat = pat' }

applyFloating :: Floating -> NVTTerm -> NVTTerm
applyFloating plet@(FloatingPLet {pletPat = p}) b {- NVTLet v t1 b) a = -}
    = NVTLet v (pletRHS plet)
    $ maybe b (caseNVConPat v `flip` b) (innerNVPat p)
  where
    v = getNVPatVar p
applyFloating fcase@(FloatingCase v p) b = caseNVConPat v p b


-- If |splitPLet t = Just (fl, t')|, then |applyFloating fl t' = t|.
splitFloating :: NVTTerm -> Maybe (Floating, NVTTerm)
splitFloating (NVTLet v t1 t2) = case h (NVPVar v) t2 of
   (pat, t')  -> Just
      (FloatingPLet
       { pletPat = pat
        , pletRHS = t1
        , pletFVars = fvarsNVTTerm t1
        }
      , t'
      )
   where
     h :: NVPat -> NVTTerm -> (NVPat, NVTTerm)
     h p t = case splitSingleAltCase t of
       Just (cv, conPat, b)
         | Just p' <-  attachNVConPat cv conPat p
                       -- this fails if cv is not in p
         -> h p' b
       _ -> (p, t)
splitFloating t = case splitSingleAltCase t of
       Nothing -> Nothing
       Just (cv, conPat, b) -> Just
         (FloatingCase
           { fcaseScrutinee = cv
           , fcasePat = conPat
           }
         , b
         )
-- WK: Deeper |FloatingCase|s are not yet generated here.
--     Merging into deeper |FloatingCase|s is currently
--     also not done below (e.g. in joinFloatings)

-- |splitSingleAltCase t = Just (v, conPat, t1)| means
-- that |caseNVConPat v conPat t1 == t|.
splitSingleAltCase :: NVTTerm -> Maybe (Var, NVConPat, NVTTerm)
splitSingleAltCase (NVTCase v ct dft [NVTACon c cvars t2]) | harmless dft
  = Just (v, NVConPat ct dft c $ map NVPVar cvars, t2)
splitSingleAltCase _ = Nothing

-- | ``harmless'' in the sense of negligible as default expression in |TCase|:
harmless :: NVTTerm -> Bool
harmless (NVTError _)  = True
harmless NVTUnit       = True
harmless NVTErased     = True
harmless NVTSort       = True
harmless _             = False

-- |  @floatPLet@ floats pattern lets occuring in multiple branches
--    to the least join point of those branches.
floatPatterns :: Bool -> TTerm -> TCM TTerm
floatPatterns doCrossCallFloat t = toTTerm' <$>
  floatNVPatterns doCrossCallFloat (fromTTerm' t)
-- -- For all the details:
--  floatPatterns t = let
--    nvt = fromTTerm' t
--    nvt' = floatNVPatterns nvt
--    t' = toTTerm' nvt'
--    in trace (unlines
--     ["floatPatterns", "    " ++ show nvt, "\n    " ++ show nvt']) t'

floatNVPatterns :: Bool -> NVTTerm -> TCM NVTTerm
floatNVPatterns doCrossCallFloat t
  = evalStateT (snd <$> floatPatterns0 doCrossCallFloat t) 0
  -- squashPLet [] . snd . floatPatterns0

-- [Floating] only contains maximal elements after unification of patterns

-- | @joinFloatings@ returns the (maximal) common elements first, and then a nubbed concatenation (of the maximal elements).
joinFloatings :: [Floating] -> [Floating] -> ([Floating], [Floating])
joinFloatings = h id
  where
    h acc [] ps2 = (acc [], ps2)
    h acc (p1 : ps1) ps2 = let (mc, ps2') = insertFloating p1 ps2
      in h (acc . maybe id (:) mc) ps1 ps2'

-- If @findFloating fl fls = Just (fl', fls')@
-- then @fls' = Data.List.delete fl0 fls@ for some @fl0@,
-- which, unified with @fl@, yields @fl'@.
findFloating :: Floating -> [Floating] -> Maybe (Floating, [Floating])
findFloating fl [] = Just (fl, [])
findFloating plet@(FloatingPLet {pletPat = pat, pletRHS = t}) (fl : fls)
   | FloatingPLet {pletPat = pat', pletRHS = t'} <- fl
   , t == t'
   , Just (pat'', _pu) <- unifyNVPat pat pat'
   = Just (fl { pletPat = pat''}, fls)
   | otherwise
   = second (fl :) <$> findFloating plet fls
findFloating fcase@(FloatingCase cv cpat) (fl : fls)
  | FloatingCase cv' cpat' <- fl
  , Just (cpat'', _pu) <- deepUnifyNVConPat (cv, cpat) (cv', cpat')
  = Just (FloatingCase cv' cpat'', fls)
  | otherwise
  = second (fl :) <$> findFloating fcase fls

-- If @insertFloating fl fls = (mfl, fls')@,
-- then @fls'@ is the result either of adding @fl@ to @fls@,
--               or of unifying @fl@ with onle of the elements of @fls@,
-- and @mfl@ is @Just fl'@ if @fl'@ is the result of that unification.
insertFloating :: Floating -> [Floating] -> (Maybe Floating, [Floating])
insertFloating fl fls = case findFloating fl fls of
  Just (fl', fls') -> (Just fl', fl' : fls')
  Nothing -> (Nothing, fl : fls)

-- | @joinFloatingss@ returns the elements that are ``common'' to
-- at least two constituent lists first,
-- and then a nubbed concatenation of all (maximal) elements.
joinFloatingss :: [[Floating]] -> ([Floating], [Floating])
joinFloatingss [] = ([], [])
joinFloatingss [ps] = ([], ps)
joinFloatingss (ps : pss) = case joinFloatingss pss of
  (psC, psR) -> case joinFloatings ps psR of
    (psC', psR') -> (snd (joinFloatings psC' psC), psR')

floatingsFromPLets :: [Var] -> [T.PLet] -> U TCM [Floating]
floatingsFromPLets vs [] = return []
floatingsFromPLets vs (plet : plets) = do
  p' <- fromTTerm vs $ T.eTerm plet
  let Just (fl, NVTErased) = splitFloating p'
  let vs' = reverse (flBoundVars fl) ++ vs
  fls <- floatingsFromPLets vs' plets
  return $ fl : fls

-- | @floatPatterns0@ duplicates PLet occurrences at join points.
floatPatterns0 :: Bool -> NVTTerm -> U TCM ([Floating], NVTTerm)
floatPatterns0 doCrossCallFloat t = case splitFloating t of
  Just (fl, t') -> do
    (fls, t'') <- floatPatterns0 doCrossCallFloat t'
    case insertFloating fl fls of
      (_, fls') -> return (fls', applyFloating fl t'')
  Nothing -> case t of
    NVTVar _ -> return ([], t)
    NVTPrim _ -> return ([], t)
    NVTDef NVTDefDefault name -> if not doCrossCallFloat
      then return ([], t)
      else do
      mccf <- lift $ getCrossCallFloat name
      case mccf of
        Nothing -> return ([], t)
        Just ccf -> do
          vVars <- reverse <$> getVars (ccfLambdaLen ccf)
          fls <- floatingsFromPLets vVars $ ccfPLets ccf
          let dvcall = NVTDef (NVTDefAbstractPLet vVars) name
          return (fls, dvcall) -- \unfinished
            -- WK: because |fls| are not arising from real duplication,
            --     the |vVars| may get lost in |joinFloatings| etc.!
            -- WK: The reversing of the list, if kept,
            --     needs to be documented in Syntax,Treeless!
            -- \unfinished

    NVTDef (NVTDefAbstractPLet _) _ -> return ([], t) -- unlikely to be encountered
    NVTApp tf tas -> do
      (psf, tf') <- floatPatterns0 doCrossCallFloat tf
      (psas, tas') <- unzip <$> mapM (floatPatterns0 doCrossCallFloat) tas
      let (psC, psR) = joinFloatingss $ psf : psas
      return (psR, foldr applyFloating (NVTApp tf' tas') psC)
    NVTLam v tb -> do
      (ps, tb') <- floatPatterns0 doCrossCallFloat tb
      return (filter (not . (v `elemVarSet`) . flFreeVars) ps, NVTLam v tb')
    NVTLit _ -> return ([], t)
    NVTCon _ -> return ([], t)
    NVTLet v te tb -> do
      (psb, tb') <- floatPatterns0 doCrossCallFloat tb
      let psb' = filter (not . (v `elemVarSet`) . flFreeVars) psb
      (pse, te') <- floatPatterns0 doCrossCallFloat te
      case joinFloatings pse psb' of
          (ps, ps') -> return (ps', foldr applyFloating (NVTLet v te' tb') ps)
    NVTCase i ct dft alts -> do
      (psdft, dft') <- floatPatterns0 doCrossCallFloat dft
      (pairs, alts') <- unzip <$> mapM h alts
      case unzip pairs of
        (flsCs, flsRs) -> case joinFloatingss flsRs of
          (flsC, flsR) -> case joinFloatingss (flsC : flsCs) of
            (_, flsC') -> let tcore = NVTCase i ct dft' alts'
              in return (flsR, foldr applyFloating tcore flsC')
    NVTUnit -> return ([], t)
    NVTSort -> return ([], t)
    NVTErased -> return ([], t)
    NVTError _ -> return ([], t)
  where
    -- |h| returns a pair like |joinFloatings|
    h :: NVTAlt -> U TCM (([Floating],[Floating]), NVTAlt)
    h (NVTACon name cvars b) = do
      (psb, b') <- floatPatterns0 doCrossCallFloat b
      return (([], filter (\ p -> all (not . (`elemVarSet` flFreeVars p)) cvars) psb), NVTACon name cvars b')
    h (NVTAGuard g b) = do
      (psg, g') <- floatPatterns0 doCrossCallFloat g
      (psb, b') <- floatPatterns0 doCrossCallFloat b
      return (joinFloatings psg psb, NVTAGuard g' b')
    h (NVTALit lit b) = do
      (psb, b') <- floatPatterns0 doCrossCallFloat b
      return (([], psb), NVTALit lit b')

-- |squashPatterns| is to be called after |floatPatterns0|
-- \edcomm{WK}{With the improved simplifier, this may not be necessary anymore.}
{-
squashPLet :: [PLet] -> NVTTerm -> NVTTerm
squashPLet ps t = case splitPLet t of
  Just (p, t') -> case msum $ map (matchPLet p) ps of
    Just r -> squashPLet ps $ renameNVTTerm r t'
    Nothing -> applyPLet (pletNVTT p) $ squashPLet (p : ps) t'
  Nothing -> case t of
    NVTVar _ -> t
    NVTPrim _ -> t
    NVTDef NVTDefDefault name
      | False -- \edcomm{WK}{Criteria for choosing |dv| and supplying variables!}
      -> NVTDef (NVTDefAbstractPLet undefined) name
    NVTDef _ _ -> t
    NVTApp tf tas -> NVTApp (squashPLet ps tf) (map (squashPLet ps) tas)
    NVTLam v tb -> NVTLam v $ squashPLet ps tb
    NVTLit _ -> t
    NVTCon _ -> t
    NVTLet v te tb -> NVTLet v (squashPLet ps te) (squashPLet ps tb)
    NVTCase i ct dft alts -> NVTCase i ct (squashPLet ps dft) (map h alts)
    NVTUnit -> t
    NVTSort -> t
    NVTErased -> t
    NVTError _ -> t
  where
    h :: NVTAlt -> NVTAlt
    h (NVTACon name cvars b) = NVTACon name cvars $ squashPLet ps b
    h (NVTAGuard g b) = NVTAGuard (squashPLet ps g) (squashPLet ps b)
    h (NVTALit lit b) = NVTALit lit $ squashPLet ps b
-}
