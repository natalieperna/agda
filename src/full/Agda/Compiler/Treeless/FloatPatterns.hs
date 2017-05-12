{-# LANGUAGE CPP #-}
module Agda.Compiler.Treeless.FloatPatterns where

import Prelude hiding (Floating)

import Control.Applicative
import Control.Arrow (first, second)
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
-- import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Pretty
import Agda.Compiler.Treeless.Subst
import Agda.Compiler.Treeless.Compare
import Agda.Compiler.Treeless.NVTTerm
import Agda.Compiler.Treeless.NVTTerm.Pretty
import Agda.Compiler.Treeless.Pretty

-- import Agda.Utils.Permutation
import qualified Agda.Utils.Pretty as P

import Data.Word (Word64)

import Agda.Utils.Impossible
#include "undefined.h"

import Debug.Trace


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
splitFloating t = case Nothing {- splitSingleAltCase t -} of
       Nothing -> Nothing
       Just (cv, conPat, b) -> Just
         -- \edcomm{WK}{Disabled for now.}
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
-- The |QName| of the function this is called for
-- is passed in only for debug printing.
floatPatterns :: Bool -> QName -> TTerm -> TCM TTerm
floatPatterns doCrossCallFloat q t = do
  (nvt, u) <- runStateT (fromTTerm [] t) 0
  reportSDoc "treeless.opt.float" 20 $ text ("========== { floatPatterns " ++ show q ++ " starting")
  reportSDoc "treeless.opt.float" 40 $ nest 2 $ return (P.pretty nvt)
  let spuriousTopVariablesFloat
        = map ((\ v -> trace (show v) v) . V) [899990000..899990888]
  nvt' <- -- floatNVPatterns doCrossCallFloat nvt
          evalStateT (snd <$> floatPatterns0 doCrossCallFloat spuriousTopVariablesFloat nvt) u
  reportSDoc "treeless.opt.float" 20 $ text ("========== floatPatterns " ++ show q ++ " done")
  reportSDoc "treeless.opt.float" 40 $ nest 2 $ return (P.pretty nvt')
  reportSDoc "treeless.opt.float" 20 $ text "=========== }"
  let spuriousTopVariablesDone
        = map ((\ v -> trace (show v) v) . V) [999990000..999990888]
  let t' = toTTerm spuriousTopVariablesDone nvt'
  return t'

{-
floatNVPatterns :: Bool -> NVTTerm -> TCM NVTTerm
floatNVPatterns doCrossCallFloat t
  = evalStateT (snd <$> floatPatterns0 doCrossCallFloat [] t) 0
  -- squashPLet [] . snd . floatPatterns0
-}

-- [Floating] only contains maximal elements after unification of patterns

-- | @joinFloatings@ returns the (maximal) common elements first, and then a nubbed concatenation (of the maximal elements).
-- \edcomm{WK}{Propagate |PU|?}
joinFloatings :: [Floating] -> [Floating] -> ([Floating], [Floating])
joinFloatings = h id
  where
    h acc [] ps2 = (acc [], ps2)
    h acc (p1 : ps1) ps2 = let (mc, ps2') = insertFloating p1 ps2
      in h (acc . maybe id ((:) . fst) mc) ps1 ps2'

-- If @findFloating fl fls = Just ((fl', pu), fls')@
-- then @fls' = Data.List.delete fl0 fls@ for some @fl0@,
-- which, unified with @fl@, yields @fl'@.
findFloating :: Floating -> [Floating] -> Maybe ((Floating, PU), ([Floating], [Floating]))
findFloating fl [] = Nothing -- Just ((fl, emptyPU), ([], []))
findFloating plet@(FloatingPLet {pletPat = pat, pletRHS = t}) (fl : fls)
   | FloatingPLet {pletPat = pat', pletRHS = t'} <- fl
   , t == t'
   , Just (pat'', pu) <- unifyNVPat pat pat'
   = Just ((fl { pletPat = pat''}, pu), ([], fls))
   | otherwise
   = second (first (fl :)) <$> findFloating plet fls
findFloating fcase@(FloatingCase cv cpat) (fl : fls)
  | FloatingCase cv' cpat' <- fl
  , Just (cpat'', pu) <- deepUnifyNVConPat (cv, cpat) (cv', cpat')
  = Just ((FloatingCase cv' cpat'', pu), ([], fls))
  | otherwise
  = second (first (fl :)) <$> findFloating fcase fls

-- If @insertFloating fl fls = (mfl, fls')@,
-- then @fls'@ is the result either of adding @fl@ to @fls@,
--               or of unifying @fl@ with onle of the elements of @fls@,
-- and @mfl@ is @Just (fl', pu)@ if @fl'@ is the result of that unification.
insertFloating :: Floating -> [Floating] -> (Maybe (Floating, PU), [Floating])
insertFloating fl fls = case findFloating fl fls of
  Just (p@(fl', pu), (fls1, fls2)) -> (Just p, fls1 ++ fl' : fls2)
  Nothing ->
    case partition (any (`elemVarSet` flFreeVars fl) . flBoundVars) fls of
      (binding, nonbinding) -> (Nothing, binding ++ fl : nonbinding)

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
-- The @vs@ argument is an inside-out list of the binders in scope
-- from the call stack, ignoring unmanifested duplication of |Floating|s.
-- \edcomm{WK}{Should the |Floating|s be accompanied by the copy of |vs| used when generating them?}
floatPatterns0 :: Bool -> [Var] -> NVTTerm -> U TCM ([Floating], NVTTerm)
floatPatterns0 doCrossCallFloat vs t = do
  r@(fls, t') <- floatPatterns1 doCrossCallFloat vs t
  lift $ reportSDoc "treeless.opt.float.fp" 50 $
    text ("====== floatPatterns0 " ++ show (take 7 vs))
    $$ (nest 2 . return $ P.pretty t)
  lift $ reportSDoc "treeless.opt.float.fp" 50 $
    text "=== result:"
    $$ (P.vcat <$> sequence (map (nest 4 . return . P.pretty) fls ++ [nest 2 . return . P.pretty $ t']))
  return r

floatPatterns1 :: Bool -> [Var] -> NVTTerm -> U TCM ([Floating], NVTTerm)
floatPatterns1 doCrossCallFloat vs t = case splitFloating t of
  Just (fl, t') -> let vs' = flRevBoundVars fl ++ vs in do
    (fls, t'') <- floatPatterns0 doCrossCallFloat vs' t'
    case insertFloating fl fls of
      (mcflpu, fls') -> return (fls', applyFloating fl t'')
  {- should not make a difference, and apparently does not make a difference:
        where
          t''' = case mcflpu of
            Nothing -> t''
            Just (cfl, (r1, r2)) -> renameNVTTerm r2 t''
  -}
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
          lift $ reportSDoc "treeless.opt.float.ccf" 30 $ text ("-- Found CCF for " ++ show name) $$ text (show ccf)
          lift $ reportSDoc "treeless.opt.float.ccf" 40 $ text (show ccf)
          vVars <- reverse <$> getVars (ccfLambdaLen ccf)
          fls <- floatingsFromPLets vVars $ ccfPLets ccf
          let dvref = NVTDef (NVTDefAbstractPLet vVars) name
              dvcall = NVTApp dvref
                     . map NVTVar . concat $ vVars : map flBoundVars fls
              dubodyInlined -- (equivalent)
                = foldr applyFloating dvcall fls
              result = foldr NVTLam dubodyInlined vVars
          lift $ reportSDoc "treeless.opt.float.ccf" 30 $ text ("-- Instantiated CCF for " ++ show name) $$ text (P.prettyShow result)
          lift $ reportSDoc "treeless.opt.float.ccf" 40 $ text (show result)
          return (fls, result)
            -- This actual duplication of |fls| makes sure that their variables are not lost.
            -- Previously: WK: because |fls| are not arising from real duplication,
            --     the |vVars| may get lost in |joinFloatings| etc.!
            -- WK: This actual duplication will not be reversed
            --     if non of |fls| are squashed by the simplifier;
            --     probably we will have to reactivate and expand
            --     our own squashing for that.
            -- WK: The reversing of the list, if kept,
            --     needs to be documented in Syntax,Treeless!
            -- \unfinished

    NVTDef (NVTDefAbstractPLet _) _ -> return ([], t) -- unlikely to be encountered
    NVTApp tf tas -> do
      (psf, tf') <- floatPatterns0 doCrossCallFloat vs tf
      (psas, tas') <- unzip <$> mapM (floatPatterns0 doCrossCallFloat vs) tas
      let (psC, psR) = joinFloatingss $ psf : psas
      return (psR, foldr applyFloating (NVTApp tf' tas') psC)
    NVTLam v tb -> do
      (fls, tb') <- floatPatterns0 doCrossCallFloat (v : vs) tb
      return (filter (not . (v `elemVarSet`) . flFreeVars) fls, NVTLam v tb')
    NVTLit _ -> return ([], t)
    NVTCon _ -> return ([], t)
    NVTLet v te tb -> do
      (flsb, tb') <- floatPatterns0 doCrossCallFloat (v : vs) tb
      let flsb' = filter (not . (v `elemVarSet`) . flFreeVars) flsb
      (flse, te') <- floatPatterns0 doCrossCallFloat vs te
      case joinFloatings flse flsb' of
          (fls, fls') -> return (fls', foldr applyFloating (NVTLet v te' tb') fls)
    NVTCase i ct dft alts -> do
      (flsdft, dft') <- floatPatterns0 doCrossCallFloat vs dft
      (pairs, alts') <- unzip <$> mapM (h vs) alts
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
    h :: [Var] -> NVTAlt -> U TCM (([Floating],[Floating]), NVTAlt)
    h vs (NVTACon name cvars b) = do
      (flsb, b') <- floatPatterns0 doCrossCallFloat (reverse cvars ++ vs) b
      return (([], filter (\ fl -> all (not . (`elemVarSet` flFreeVars fl)) cvars) flsb), NVTACon name cvars b')
    h vs (NVTAGuard g b) = do
      (psg, g') <- floatPatterns0 doCrossCallFloat vs g
      (psb, b') <- floatPatterns0 doCrossCallFloat vs b
      return (joinFloatings psg psb, NVTAGuard g' b')
    h vs (NVTALit lit b) = do
      (psb, b') <- floatPatterns0 doCrossCallFloat vs b
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
