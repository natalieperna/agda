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
floatPatterns doCrossCallFloat q t = flip evalStateT 0 $ do
  nvt <- fromTTerm [] t
  lift $ reportSDoc "treeless.opt.float" 20 $ text ("========== { floatPatterns " ++ show q ++ " starting")
  lift $ reportSDoc "treeless.opt.float" 40 $ nest 2 $ return (P.pretty nvt)
  let spuriousTopVariablesFloat
        = [] -- map ((\ v -> trace (show v) v) . V) [899990000..899990888]
  nvt' <- -- floatNVPatterns doCrossCallFloat nvt
          snd <$> floatPatterns0 doCrossCallFloat spuriousTopVariablesFloat nvt
  nvt'' <- squashFloatings doCrossCallFloat [] nvt'
  lift $ reportSDoc "treeless.opt.float" 50 $ text ("========== floatPatterns " ++ show q ++ " afterfloating:")
  lift $ reportSDoc "treeless.opt.float" 50 $ nest 2 $ return (P.pretty nvt')
  lift $ reportSDoc "treeless.opt.float" 20 $ text ("========== floatPatterns " ++ show q ++ " done")
  lift $ reportSDoc "treeless.opt.float" 40 $ nest 2 $ return (P.pretty nvt'')
  lift $ reportSDoc "treeless.opt.float" 20 $ text "=========== }"
  let spuriousTopVariablesDone
        = [] -- map ((\ v -> trace (show v) v) . V) [999990000..999990888]
  let t' = toTTerm spuriousTopVariablesDone nvt''
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
joinFloatings :: [Floating] -> [Floating] -> (([Floating], [Floating]))
joinFloatings [] fls2 = ([], fls2)
joinFloatings fls1 [] = ([], fls1)
joinFloatings x y = h id x y
  where
    h acc [] fls2 = (acc [], fls2)
    h acc (fl1 : fls1) fls2 = let (mc, fls2') = insertFloating fl1 fls2
      in case mc of
        Nothing -> h acc fls1 fls2'
        Just (fl, (r1, r2)) -> h (acc . (fl :)) (map (renameFloating r1) fls1) fls2'
          -- \edcomm{WK}{Do things in |acc| need to be renamed? Is |acc| in the right place?}

-- If @findFloating fl fls = Just ((fl', pu), (fls1, fls2))@
-- then @fls = fls1 ++ fl0 : fls2@ for some @fl0@,
-- which, unified with @fl@, yields @fl'@.
findFloating :: Floating -> [Floating] -> Maybe ((Floating, PU), ([Floating], [Floating]))
findFloating fl [] = Nothing -- Just ((fl, emptyPU), ([], []))
findFloating plet@(FloatingPLet {pletPat = pat, pletRHS = t}) (fl : fls)
   | FloatingPLet {pletPat = pat', pletRHS = t'} <- fl
   , t == t'
   , Just (pat'', pu) <- unifyNVPat pat pat'
   = Just ((mkFloatingPLet pat'' t', pu), ([], fls))
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
  Just (p@(fl', (r1, r2)), (fls1, fls2))
    -> (Just p
       , fl' : map (renameFloating r1) (fls1 ++ map (renameFloating r2) fls2))
  Nothing -> let
      flHasToGoBelow = any (`elemVarSet` flFreeVars fl) . flBoundVars
      (below, above) = span flHasToGoBelow $ reverse fls
    in (Nothing, reverse above ++ fl : reverse below)

-- | @joinFloatingss@ returns the elements that are ``common'' to
-- at least two constituent lists first,
-- and then a nubbed concatenation of all (maximal) elements.
joinFloatingss :: [[Floating]] -> ([Floating], [Floating])
joinFloatingss [] = ([], [])
joinFloatingss [fls] = ([], fls)
joinFloatingss (fls : flss) = case joinFloatingss flss of
  (flsC, flsR) -> case joinFloatings fls flsR of
    (flsC', flsR') -> let
        (flsCC, flsC'') = joinFloatings flsC' flsC
        prt i = show . (P.text ("XXX" ++ shows i " ") P.<+>) . P.nest 5
      in -- trace
         --  (unlines $ zipWith prt [1..]
         --   [P.pretty flsC'
         --   ,P.pretty flsC
         --   ,P.pretty flsC''
         --   ,P.pretty flsCC
         --   ])
         (flsC'', flsR')

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
    return $ case insertFloating fl fls of
      (Nothing, fls')             -> (fls', applyFloating fl t'')
      (Just (cfl, (r1, _)), fls') -> (fls', applyFloating cfl $ renameNVTTerm r1 t'')
      -- the renaming may not make a difference.
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
          lift $ reportSDoc "treeless.opt.float.ccf" 30 $ text ("-- floatPatterns: Found CCF for " ++ show name) $$ text (show ccf)
          lift $ reportSDoc "treeless.opt.float.ccf" 40 $ text (show ccf)
          vVars <- reverse <$> getVars (ccfLambdaLen ccf)
          fls <- floatingsFromPLets vVars $ ccfPLets ccf
          let dvref = NVTDef (NVTDefAbstractPLet vVars) name
          lift $ reportSDoc "treeless.opt.float.ccf" 30 $ text ("-- Using CCF for " ++ shows name " switching to") $$ text (P.prettyShow dvref)
          return (fls, dvref)
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
      (flsf, tf') <- floatPatterns0 doCrossCallFloat vs tf
      (flsas, tas') <- unzip <$> mapM (floatPatterns0 doCrossCallFloat vs) tas
      let (flsC, flsR) = joinFloatingss $ flsf : flsas
      return (flsR, foldr applyFloating (NVTApp tf' tas') flsC)
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
      (flsg, g') <- floatPatterns0 doCrossCallFloat vs g
      (flsb, b') <- floatPatterns0 doCrossCallFloat vs b
      return (joinFloatings flsg flsb, NVTAGuard g' b')
    h vs (NVTALit lit b) = do
      (flsb, b') <- floatPatterns0 doCrossCallFloat vs b
      return (([], flsb), NVTALit lit b')

-- If |fls| are considered to move into binders of |vs|,
-- then only |pruneFloatings vs fls| are allowed to move in.
pruneFloatings :: VarSet -> [Floating] -> [Floating]
pruneFloatings vs [] = []
pruneFloatings vs (fl : fls) = let flBs = flBoundVars fl
  in if nullVarSet (vs `intersectionVarSet` flFreeVars fl)
  then (fl :) $ pruneFloatings vs fls
  else pruneFloatings (foldr insertVarSet vs $ flBoundVars fl) fls

-- |squashPatterns| is to be called after |floatPatterns0|
-- With the improved simplifier, this is necessary only to make sure
-- that "du" bodies are not inlined without actually giving rise to sharing.
squashFloatings :: Bool -> [Floating] -> NVTTerm -> U TCM NVTTerm
squashFloatings doCrossCallFloat fls t = case splitFloating t of
  Just (fl, t') -> case msum $ map (matchFloating fl) fls of
    Just r -> squashFloatings doCrossCallFloat fls $ renameNVTTerm r t'
      -- \edcomm{WK}{This renaming could be put into an environment.}
    Nothing -> applyFloating fl
            <$> squashFloatings doCrossCallFloat (fl : fls) t'
  Nothing -> case t of
    NVTVar _ -> return t
    NVTPrim _ -> return t
    NVTDef NVTDefDefault _name -> return t
    NVTDef (NVTDefAbstractPLet vVars) name -> if not doCrossCallFloat
      then return t
      else do
      mccf <- lift $ getCrossCallFloat name
      case mccf of
        Nothing -> return t
        Just ccf -> do
          lift $ reportSDoc "treeless.opt.float.ccf" 30 $ text ("-- squashFloatings: Found CCF for " ++ show name)
          lift $ reportSDoc "treeless.opt.float.ccf" 60 $ text (show ccf)
          fls <- floatingsFromPLets vVars $ ccfPLets ccf
          let dvref = NVTDef (NVTDefAbstractPLet vVars) name
              dvcall = NVTApp dvref
                     . map NVTVar . concat $ vVars : map flBoundVars fls
              -- |wrap fls t0 = (b, t1)|
              -- iff |b| indicates whether one of the |fls| matches,
              -- and |t1| is |t0| wrapped into all those elements of |fls|
              -- that do not match.
              wrap [] t0 = (False, t0)
              wrap (fl : fls') t0 = case matchFloatings fl fls' of
                Nothing -> second (applyFloating fl) $ wrap fls' t0
                Just r  -> first (const True) . wrap fls'
                        $  renameNVTTerm r t0
              (dv, dubodyInlined {- (equivalent) -} )
                = wrap fls dvcall
              result = if dv then foldr NVTLam dubodyInlined vVars
                       else NVTDef NVTDefDefault name
          lift $ if dv
            then do
              reportSDoc "treeless.opt.float.ccf" 30
                $ text ("-- Instantiated CCF for " ++ show name)
              reportSDoc "treeless.opt.float.ccf" 50 $ nest 4
                $ text (P.prettyShow result)
            else do
              reportSDoc "treeless.opt.float.ccf" 40 $ text ("-- Nothing matched in  CCF for " ++ show name) $$ text (P.prettyShow result)
          return result
    NVTApp tf tas -> do
      tf' <- squashFloatings doCrossCallFloat fls tf
      tas' <- mapM (squashFloatings doCrossCallFloat fls) tas
      return $ NVTApp tf' tas'
    NVTLam v tb -> NVTLam v <$> squashFloatings doCrossCallFloat fls' tb
      where fls' = pruneFloatings (singletonVarSet v) fls
    NVTLit _ -> return t
    NVTCon _ -> return t
    NVTLet v te tb -> do
        te' <- squashFloatings doCrossCallFloat fls te
        tb' <- squashFloatings doCrossCallFloat fls' tb
        return $ NVTLet v te' tb'
      where fls' = pruneFloatings (singletonVarSet v) fls
    NVTCase i ct dft alts -> do
      dft' <- squashFloatings doCrossCallFloat fls dft
      alts' <- mapM h alts
      return $ NVTCase i ct dft' alts'
    NVTUnit -> return t
    NVTSort -> return t
    NVTErased -> return t
    NVTError _ -> return t
  where
    h :: NVTAlt -> U TCM NVTAlt
    h (NVTACon name cvars b) = NVTACon name cvars
        <$> squashFloatings doCrossCallFloat fls b
      where fls' = pruneFloatings (listToVarSet cvars) fls
    h (NVTAGuard g b) = do
      g' <- squashFloatings doCrossCallFloat fls g
      b' <- squashFloatings doCrossCallFloat fls b
      return $ NVTAGuard g' b'
    h (NVTALit lit b) = NVTALit lit <$> squashFloatings doCrossCallFloat fls b
