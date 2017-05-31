{-# LANGUAGE CPP #-}
module Agda.Compiler.Treeless.FloatPatterns where

-- {{{ imports
import Prelude hiding (Floating)

import Control.Applicative
import Control.Arrow (first, second)
import Control.Monad.Reader
import Control.Monad.State
import Data.Monoid
import qualified Data.Map as Map
import Data.Function (on)
import Data.Maybe (catMaybes)
import Data.List (nub, partition)
import qualified Data.IntSet as IntSet
import Data.IntSet (IntSet)
import qualified Data.IntMap as IntMap
import Data.IntMap (IntMap)

import System.IO (hFlush, stdout, stderr)

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
import Agda.Compiler.Treeless.SplitPLet (splitCCF)

-- import Agda.Utils.Permutation
import qualified Agda.Utils.Pretty as P

import Data.Word (Word64)

import Agda.Utils.Impossible
#include "undefined.h"

import Debug.Trace
-- }}}

-- {{{ attachConPatToFloating :: Var -> NVConPat -> Floating -> Maybe Floating
attachConPatToFloating :: Var -> NVConPat -> Floating -> Maybe Floating
attachConPatToFloating v conPat plet@(FloatingPLet {})
  = case attachNVConPat v conPat (pletPat plet) of
      Nothing -> Nothing
      Just pat' -> Just $ mkFloatingPLet pat' (pletRHS plet)
attachConPatToFloating v conPat fcase@(FloatingCase {})
  = case attachToNVConPat v conPat (fcasePat fcase) of
      Nothing -> Nothing
      Just pat' -> Just fcase { fcasePat = pat' }
-- }}}

-- {{{ applyFloating :: Floating -> NVTTerm -> NVTTerm
-- \edcomm{WK}{Use |flExtraScope|?}
applyFloating :: Floating -> NVTTerm -> NVTTerm
applyFloating plet@(FloatingPLet {pletPat = p}) b {- NVTLet v t1 b) a = -}
    = mkNVTLet v (pletRHS plet)
    $ maybe b (caseNVConPat v `flip` b) (innerNVPat p)
  where
    v = getNVPatVar p
applyFloating fcase@(FloatingCase v p extraScope) b = caseNVConPat v p b
-- }}}

-- {{{ splitFloating :: NVTTerm -> Maybe (Floating, NVTTerm)
-- If |splitPLet t = Just (fl, t')|, then |applyFloating fl t' = t|.
splitFloating :: NVTTerm -> Maybe (Floating, NVTTerm)
splitFloating (NVTLet v t1 t2) = case h (NVPVar v) t2 of
   (pat, t')  -> Just (mkFloatingPLet pat t1, t')
   where
     h :: NVPat -> NVTTerm -> (NVPat, NVTTerm)
     h p t = case splitSingleAltCase t of
       Just (cv, conPat, b)
         | Just p' <-  attachNVConPat cv conPat p
                       -- this fails if cv is not in p
         -> h p' b
       _ -> (p, t)
-- \edcomm{WK}{Disabling |FloatingCase| for now.}
splitFloating t = case Nothing {- splitSingleAltCase t -} of
       Nothing -> Nothing
       Just (cv, conPat, b) -> Just
         (FloatingCase
           { fcaseScrutinee = cv
           , fcasePat = conPat
           , flExtraScope = []
           }
         , b
         )
-- WK: Deeper |FloatingCase|s are not yet generated here.
--     Merging into deeper |FloatingCase|s is currently
--     also not done below (e.g. in joinFloatings)
-- }}}

-- {{{ splitSingleAltCase :: NVTTerm -> Maybe (Var, NVConPat, NVTTerm)
-- |splitSingleAltCase t = Just (v, conPat, t1)| means
-- that |caseNVConPat v conPat t1 == t|.
splitSingleAltCase :: NVTTerm -> Maybe (Var, NVConPat, NVTTerm)
splitSingleAltCase (NVTCase v ct dft [NVTACon c cvars t2]) | harmless dft
  = Just (v, NVConPat ct dft c $ map NVPVar cvars, t2)
splitSingleAltCase _ = Nothing
-- }}}

-- {{{ floatPatterns :: Bool -> QName -> TTerm -> TCM ((TTerm -> Maybe CrossCallFloat), TTerm)
-- |  @floatPLet@ floats pattern lets occuring in multiple branches
--    to the least join point of those branches.
-- The |QName| of the function this is called for
-- is passed in only for debug printing.
-- @floatPLet@ returns a pair |(mkCCF, t')|, where
-- |mkCCF :: TTerm -> Maybe CrossCallFloat| will be used in |toTreeless|
-- to wrap the final simplified version of |t'| into a |CrossCallFloat|,
-- if applicable.
floatPatterns :: Bool -> QName -> TTerm -> TCM ((TTerm -> Maybe CrossCallFloat), TTerm)
floatPatterns doCrossCallFloat q t = flip evalStateT 0 $ do
  nvt <- fromTTerm [] t
  lift $ reportSDoc "treeless.opt.float" 20 $ text ("========== { floatPatterns " ++ show q ++ ": starting")
  lift $ reportSDoc "treeless.opt.float" 40 $ nest 2 $ return (P.pretty nvt)
  tr@(lambdaVars, floats, nvt') <- floatPatternsTop doCrossCallFloat q nvt
  -- |floats|A version of |tr|, with squashed (and simplified term)
  -- should be cached in |Compiled|
  lift $ reportSDoc "treeless.opt.float" 20 $ text ("========== floatPatterns " ++ show q ++ ": squashing")
  nvt'' <- squashFloatings doCrossCallFloat [] nvt'
  lift $ reportSDoc "treeless.opt.float" 50 $ text ("========== floatPatterns " ++ show q ++ " after floating:")
  lift $ reportSDoc "treeless.opt.float" 50 $ nest 2 $ return (P.pretty nvt')
  lift $ reportSDoc "treeless.opt.float" 20 $ text ("========== floatPatterns " ++ show q ++ " done")
  lift $ reportSDoc "treeless.opt.float" 40 $ nest 2 $ return (P.pretty nvt'')
  lift $ reportSDoc "treeless.opt.float" 20 $ text "=========== }"
  let spuriousTopVariablesDone
        = [] -- map ((\ v -> trace (show v) v) . V) [999990000..999990888]
  let k = length lambdaVars
      unTLam 0 t = t
      unTLam n (T.TLam b) = unTLam (pred n) b
      unTLam _ _ = __IMPOSSIBLE__
  lift . reportSDoc "treeless.opt.float.ccf" 60
     $ text ("========== floatPatterns " ++ show q ++ ": mkCCF:")
     $$ nest 4 (vcat
       [ text "t = " <+> nest 6 (pretty t)
       , text "lambdaVars = " <+> pretty lambdaVars
       , text ("lambdaLen = " ++ show k)
       , text "body = " <+> nest 6 (pretty $ unTLam k t)
       , text "nvt'' = " <+> nest 6 (pretty nvt'')
       , text "floats = " <+> nest 9 (vcat $ map pretty floats)
       ])
  let t' = toTTerm spuriousTopVariablesDone nvt''
  lift . reportSDoc "treeless.opt.float.ccf" 60
     $ text ("========== floatPatterns " ++ show q ++ ": mkCCF 2:")
     $$ nest 4 (text "t' = " <+> nest 6 (pretty t'))
  -- let plets = floatingsToPLets (reverse lambdaVars) floats
  --         -- \edcomm{WK}{More variables needed?}
  --
  -- lift . reportSDoc "treeless.opt.float.ccf" 60
  --    $ text ("========== floatPatterns " ++ show q ++ ": mkCCF 3:")
  --    $$ nest 4 (text "plets = " <+> nest 9 (vcat $ map pretty plets))
  -- let mkCCF = if null plets then const Nothing
  --             else splitCCF
  return (splitCCF, t')
-- }}}

-- {{{ floatingsToPLets :: [Var] -> [Floating] -> [T.PLet]
floatingsToPLets :: [Var] -> [Floating] -> [T.PLet]
floatingsToPLets vs [] = []
floatingsToPLets vs (fl : fls) = let
    (plet, vs') = floatingToPLet vs fl
  in plet : floatingsToPLets vs' fls
-- }}}

-- {{{ floatingToPLet :: [Var] -> Floating -> (T.PLet, [Var])
floatingToPLet :: [Var] -> Floating -> (T.PLet, [Var])
floatingToPLet vs fl@(FloatingPLet {pletPat = pat, pletRHS = rhs}) = let
    tt = NVTLet v rhs
      $ maybe NVTErased (caseNVConPat v `flip` NVTErased) (innerNVPat pat)
      where v = getNVPatVar pat
    t = toTTerm vs tt
    -- t = toTTerm vs $ applyFloating fl NVTErased -- no: uses mkNVTLet!
    fvs = Map.foldWithKey (\ k _ -> IntSet.insert k) IntSet.empty $ freeVars t
    tBinders = flRevBoundVars fl
  in (T.PLet
       { T.pletFreeVars = fvs
       , T.pletNumBinders = length tBinders
       , T.eTerm = t
       }
     , tBinders ++ vs
     )
floatingToPLet vs _ = __IMPOSSIBLE__ -- \edcomm{WK}{As long as |FloatingCase| is disabled.}
-- }}}

{-
floatNVPatterns :: Bool -> NVTTerm -> TCM NVTTerm
floatNVPatterns doCrossCallFloat t
  = evalStateT (snd <$> floatPatterns0 doCrossCallFloat [] t) 0
  -- squashPLet [] . snd . floatPatterns0
-}

-- [Floating] only contains maximal elements after unification of patterns

-- {{{  -- Attempt: |closeFloatings|
-- Important: Common |Floating|s need to be closed under binders at the time of insertion!
-- |closeFloatings| takes common floating |flsC| extracted from
-- joined floatings |fls| (both top-down)
-- and returns |flsC| closed under binders in |fls|.
   {-
closeFloatings :: Monad m => [Floating] -> [Floating] -> U m [Floating]
closeFloatings flsC fls = let
  flsC' :: [((Floating, [Var]), ([Var], VarSet))]
    -- binders in scope from above,
    -- binders and free variables here and below
  flsC' = fst $ h id []
    where
      h :: [Var]  -- binders in scope from above
        -> [Floating]
        -> ( [((Floating, [Var]), ([Var], VarSet))]
           , ([Var], VarSet)
           )
      h vs [] = ([], ([], emptyVarSet))
      h vs (flC : flsC') = let
          bvs = flBoundVars flC
          ((r, (belowB, belowF)) = h (bvs ++ vs) flsC'
          below' = (bvs ++ belowB, flFreeVars `unionVarSet` belowF)
        in (((flC, vs), below')) : r, below')
  fls' :: [(Floating, VarSet)] -- variables bound (indirectly) here
  fls' = fst $ h fls
    where
      h :: [Floating] -> ([(Floating, VarSet)], IntMap VarSet)
      h [] = ([], IntMap.empty)
      h (fl : fls') = ((fl, fromHere), below') : fls''
        where
          (fls'', below) = h fls'
          reachableB b@(V i) m = case IntMap.lookup i m of
              Nothing -> singletonVarSet b
              Just s -> insertVarSet b s
          closeB b@(V i) m = IntMap.insert i (reachableB b m) m
          bvars = flBoundVars fl
          below' = foldr closeB below bvars
          fromHere = unionsVarSet $ map (flip reachableB below) bvars
  close :: [((Floating, [Var]), ([Var], VarSet))]
        -> [(Floating, VarSet)]
        -> U m [Floating]
    -- taking |flsC'| and |fls'|; returning closed |flsC|
  close [] _ = []
  close (flC : flsC') [] = __IMPOSSIBLE__
  close (((flC, above), (belowB, belowF)) : flsC') ((fl, binding) : fls')
    = if any (\ (V i) -> IntMap.lookup ) (flBoundVars fl)
    = if any (\ (V i) -> not . nullVarSet . intersectionVarSet belowF
                      $ IntMap.findWithDefault emptyVarSet i binding)
             (flBoundVars fl)
      then fl : close flsC0 fls'
-}
-- }}}

-- {{{ joinFloatings :: [Floating] [Floating] -> U m (([Floating], [Floating]))
-- | @joinFloatings@ returns the (maximal) common elements first, and then a nubbed concatenation (of the maximal elements).
-- \edcomm{WK}{Propagate |PU|?}
joinFloatings :: Monad m => [Floating] -> [Floating] -> U m (([Floating], [Floating]))
joinFloatings [] fls2 = return ([], fls2)
joinFloatings fls1 [] = return ([], fls1)
joinFloatings x y = h id x y
  where
    h acc [] fls2 = return (acc [], fls2)
    h acc (fl1 : fls1) fls2 = do
      (mc, fls2') <- insertFloating fl1 fls2
      case mc of
        Nothing -> h acc fls1 fls2'
        Just (fl, (r1, r2))
          -> h (acc . (fl :)) (map (renameFloating r1) fls1) fls2'
          -- \edcomm{WK}{Do things in |acc| need to be renamed? Is |acc| in the right place?}
-- }}}

-- {{{ findFloating :: Fl -> [Fl] -> U m (Maybe ((Fl, PU), ([Fl], [Fl])))
-- If @findFloating fl fls = Just ((fl', pu), (fls1, fls2))@
-- then @fls = fls1 ++ fl0 : fls2@ for some @fl0@,
-- which, unified with @fl@, yields @fl'@.
findFloating :: Monad m => Floating -> [Floating] -> U m (Maybe ((Floating, PU), ([Floating], [Floating])))
findFloating fl [] = return Nothing
findFloating plet1@(FloatingPLet {pletPat = pat1, pletRHS = t1}) (fl : fls)
   | FloatingPLet {pletPat = pat2, pletRHS = t2} <- fl
   , t1 == t2
   = do
     avoidU t1
     avoidU t2
     (m, pu) <- runStateT (unifyNVPatU pat1 pat2) emptyPU
     case m of
       Just pat3 -> do
         t3 <- evalStateT (copyNVTTerm t1) emptyNVRename
         return $ Just ((mkFloatingPLet pat3 t3, pu), ([], fls))
       _ -> fmap (second (first (fl :))) <$> findFloating plet1 fls
   | otherwise
   = fmap (second (first (fl :))) <$> findFloating plet1 fls
{-
findFloating fcase@(FloatingCase cv cpat) (fl : fls)
  | FloatingCase cv' cpat' <- fl
  , Just (cpat'', pu) <- deepUnifyNVConPat (cv, cpat) (cv', cpat')
  = Just ((FloatingCase cv' cpat'', pu), ([], fls))
  | otherwise
  = second (first (fl :)) <$> findFloating fcase fls
-}
findFloating _ _ = return Nothing -- as long as |FloatingCase| is deactivated
-- }}}

-- {{{ insertFloating :: Fl -> [Fl] -> U m (Maybe (Fl, PU), [Fl])
-- If @insertFloating fl fls = (mfl, fls')@,
-- then @fls'@ is the result either of adding @fl@ to @fls@,
--               or of unifying @fl@ with one of the elements of @fls@,
-- and @mfl@ is @Just (fl', pu)@ if @fl'@ is the result of that unification.
insertFloating :: Monad m => Floating -> [Floating] -> U m (Maybe (Floating, PU), [Floating])
insertFloating fl fls = do
  m <- findFloating fl fls
  return $ case m of
    Just (p@(fl', (r1, r2)), (fls1, fls2))
      -> (Just p
         , fl' : map (renameFloating r1 . renameFloating r2) (fls1 ++ fls2))
    Nothing -> let
        flHasToGoBelow = any (`elemVarSet` flFreeVars fl) . flBoundVars
        (below, above) = span flHasToGoBelow $ reverse fls
      in (Nothing, reverse above ++ fl : reverse below)
-- }}}

-- {{{ joinFloatingss :: [[Floating]] -> U m ([Floating], [Floating])
-- | @joinFloatingss@ returns the elements that are ``common'' to
-- at least two constituent lists first,
-- and then a nubbed concatenation of all (maximal) elements.
joinFloatingss :: Monad m => [[Floating]] -> U m ([Floating], [Floating])
joinFloatingss [] = return ([], [])
joinFloatingss [fls] = return ([], fls)
joinFloatingss (fls : flss) = do
  (flsC, flsR) <- joinFloatingss flss
  (flsC', flsR') <- joinFloatings fls flsR
  (flsCC, flsC'') <- joinFloatings flsC' flsC
  -- let prt i = show . (P.text ("XXX" ++ shows i " ") P.<+>) . P.nest 5
  -- trace
  --        (unlines $ zipWith prt [1..]
  --         [P.pretty flsC'
  --         ,P.pretty flsC
  --         ,P.pretty flsC''
  --         ,P.pretty flsCC
  --         ])
  return (flsC'', flsR')
-- }}}

-- |NVTDefFloating vVars| contains the locally-free occurrences of |vVars|,
-- the binders of which are the |Floating|s floated out of this call.
-- They therefore need to be renamed together with these |Floatings|!

-- {{{ floatingsFromPLets :: [Var] [Var] NVRename [T.PLet] -> U TCM [Fl]
-- |floatingsFromPLets| is called twice:
-- In |floatPatterns0| with |ws = []|;
--   for every generated |Floating|,
--   the |flRevBoundVars| in scope for its body
--   are inserted into |flExtraScope|.
-- In |squashFloatings| with |ws = vVarsExtra| to apply the resulting renamings.
-- \edcomm{WK}{It is possible that too much is going on here at the same time.}
-- \edcomm{WK}{Assumption about |[T.PLet]| and |ws|: Outside-in!}
floatingsFromPLets :: [Var] -> [Var] -> NVRename
                   -> [T.PLet] -> U TCM [Floating]
floatingsFromPLets vs ws r [] = return []
floatingsFromPLets vs ws r (T.PLet {T.eTerm = TErased} : plets)
                   = floatingsFromPLets vs ws r plets
floatingsFromPLets vs ws r (T.PLet {T.eTerm = TVar _} : plets)
                   = floatingsFromPLets vs ws r plets
floatingsFromPLets vs ws r (plet : plets) = do
  p' <- fst <$> fromTTerm0 False vs (T.eTerm plet)
  case splitFloating p' of
    Just (fl, NVTErased) -> do
      let flBvs = flRevBoundVars fl
          (ws0, ws') = splitAt (length flBvs) ws
          r' = zipInsertNVRename ws0 flBvs r
          fl' = renameFloatingFVars r fl {flExtraScope = flBvs}
      let vs' = flBvs ++ vs -- \edcomm{WK}{\unfinished}
      lift $ do
          reportSDoc "treeless.opt.float.ccf" 50
            $ text "-- floatingsFromPLets: " <+> pretty vs
            $$ nest 4 (vcat
               [text "r = " <+> nest 8 (pretty r)
               ,text "plet = " <+> nest 8 (pretty plet)
               ,text "fl = " <+> nest 8 (pretty fl)
               ,text "r' = " <+> nest 8 (pretty r')
               ,text "fl' = " <+> nest 8 (pretty fl')
               ,text "flBvs = " <+> nest 8 (pretty flBvs)
               ])
      fls <- floatingsFromPLets vs' ws' r' plets
      return $ fl' : map (addExtraScope flBvs) fls
    _ -> do
       doc <- lift $ text "floatingsFromPLets: empty splitFloating:"
                $$ text "  plet = " <+> nest 12 (pretty plet)
                $$ text "  p'   = " <+> nest 12 (pretty p')
       trace (show doc) __IMPOSSIBLE__
-- }}}

-- {{{ floatPatterns0 :: Bool -> QName -> [Var] -> NVTTerm -> U TCM ([Fl], NVTTerm)
-- | @floatPatterns0@ duplicates PLet occurrences at join points.
-- The @vs@ argument is an inside-out list of the binders in scope
-- from the call stack, ignoring unmanifested duplication of |Floating|s.
-- \edcomm{WK}{Should the |Floating|s be accompanied by the copy of |vs| used when generating them?}
-- For the purpose of debug output generation,
-- the work of @floatPatterns0@ happens in @floatPatterns1@.
floatPatterns0 :: Bool -> QName -> [Var] -> NVTTerm -> U TCM ([Floating], NVTTerm)
floatPatterns0 doCrossCallFloat q vs t = do
  r@(fls, t') <- floatPatterns1 doCrossCallFloat q vs t
  lift $ reportSDoc "treeless.opt.float.fp" 50 $
    text ("====== floatPatterns0 " ++ shows q (' ' : show (take 17 vs)))
    $$ (nest 2 . return $ P.pretty t)
  lift $ reportSDoc "treeless.opt.float.fp" 50 $
    text "=== result:"
    $$ (P.vcat <$> sequence (map (nest 4 . return . P.pretty) fls ++ [nest 2 . return . P.pretty $ t']))
  return r
-- }}}

-- {{{ floatPatternsTop :: Bool -> QName -> NVTTerm -> U TCM ([Var], [Fl], NVTTerm)
-- |floatPatternsTop| is intended to prepare for caching in |Compiled|
floatPatternsTop :: Bool -> QName -> NVTTerm -> U TCM ([Var], [Floating], NVTTerm)
floatPatternsTop doCrossCallFloat q = h []
  where
    h :: [Var] -> NVTTerm -> U TCM ([Var], [Floating], NVTTerm)
    h vs (NVTLam v tb) = do
      (vs', fls, tb') <- h (v : vs) tb
      return (vs', fls, NVTLam v tb') -- Adding the lambdas back in for |floatPatterns|
    h vs t = do
      (fls, t') <- floatPatterns0 doCrossCallFloat q vs t
      return (reverse vs, fls, t')
-- }}}


-- {{{ floatFloatings :: Bool -> QName -> [Var] -> [Floating] -> U TCM [Floating]
-- \edcomm{WK}{Possibly big hammer!}
floatFloatings :: Bool -> QName -> [Var] -> [Floating] -> U TCM [Floating]
floatFloatings False _ _ fls = return fls
floatFloatings doCrossCallFloat q vs fls = snd <$>
  (joinFloatingss =<< mapM (floatFloating doCrossCallFloat q vs) fls)  -- \edcomm{WK}{|vs|?}
  where
    floatFloating :: Bool -> QName -> [Var] -> Floating -> U TCM [Floating]
    floatFloating doCrossCallFloat q vs fl@(FloatingPLet {}) = do
      (fls', rhs') <- floatPatterns1 doCrossCallFloat q vs $ pletRHS fl
      (m, fls'') <- insertFloating (mkFloatingPLet (pletPat fl) rhs') fls'
      return fls'' -- fls' ++ [mkFloatingPLet (pletPat fl) rhs']  -- \edcomm{WK}{?}
    floatFloating doCrossCallFloat q vs fl = return [fl]
-- }}}


-- |NVTTLet| needs to be treated separately,
-- since currently evey occurrence would be taken over by |splitFloating|.
-- \edcomm{WK}{The same will hold for |NVTCase| once |FloatingCase| is reactivated.}
floatPatterns1 :: Bool -> QName -> [Var] -> NVTTerm -> U TCM ([Floating], NVTTerm)
floatPatterns1 doCrossCallFloat q vs t = case t of
  NVTLet v te tb -> do
      (flsb, tb') <- floatPatterns0 doCrossCallFloat q (v : vs) tb
      floatNVTLet vs v te flsb tb'
{-
          (_, fls'') <- joinFloatings fls' [fl]
          return (fls'', t') -- no renaming...
-}
{-
          m <- insertFloating fl fls'
          case m of
            (Nothing, fls'')  -> return (fls'', applyFloating fl t'')
            (Just (cfl, (r1, _)), fls'')
              -> return (fls'', applyFloating cfl $ renameNVTTerm r1 t'')
-}
  _ | Just (fl, t') <- splitFloating t
    -> let vs' = flRevBoundVars fl ++ vs in do
        (fls, t'') <- floatPatterns0 doCrossCallFloat q vs' t'
        m <- insertFloating fl fls
        return $ case m of
          (Nothing, fls')             -> (fls', applyFloating fl t'')
          (Just (cfl, (r1, r2)), fls') -> let
              r1' = domRestrNVRename (flExtraScope fl) r1
              r2' = domRestrNVRename (flExtraScope =<< fls) r2
              r = unionNVRename r1' r2'
            in (fls', applyFloating cfl $ renameNVTTerm r t'')
             -- the renamings are only needed to propagate to |NVTDefFloating|s,
             -- and therefore restricted to |flExtraScope|s.
             -- \edcomm{WK}{The necessity to rename here is still unfortunate.}
  NVTVar _ -> return ([], t)
  NVTPrim _ -> return ([], t)
  NVTApp d@(NVTDef NVTDefDefault name) tas -> if not doCrossCallFloat
    then floatNVTApp vs [] d tas
    else do
    mccf <- lift $ getCrossCallFloat name
    case mccf of
      Nothing -> return ([], t)
      Just ccf -> do
        floatNVTDefApp vs (ccfLambdaLen ccf) name (ccfPLets ccf) tas
  {-
          let dvref = NVTDef (NVTDefFloating vVars) name
          lift $ do
            reportSDoc "treeless.opt.float.ccf" 30
              $ text ("-- floatPatterns: Found CCF for " ++ show name)
            reportSDoc "treeless.opt.float.ccf" 40
              $ pretty ccf
            -- reportSDoc "treeless.opt.float.ccf" 60
            --   $ text ("-- floatPatterns: Expanded CCF floats for " ++ show name)
            --   $$ nest 4 (vcat $ map pretty fls')
            reportSDoc "treeless.opt.float.ccf" 30
              $ text ("-- Using CCF for " ++ shows name " switching to")
              $$ pretty dvref
          -- return (fls', dvref)
          return (fls, dvref)
            -- WK: The reversing of the variable list, if kept,
            --     needs to be documented in Syntax,Treeless!
            -- \unfinished
-}

  NVTDef NVTDefDefault name -> floatPatterns1 doCrossCallFloat q vs (NVTApp t [])
  NVTDef NVTDefAbstractPLet name -> __IMPOSSIBLE__-- only creating these here.
  NVTDef (NVTDefFloating _) name -> __IMPOSSIBLE__ -- only creating these here.
    {-
    return ([], NVTDef NVTDefDefault name')
    where
      name' = case name of
        QName mName (Name nId n rng' fix)
          -> QName mName (Name nId n' rng' fix)
          where
            n' = case n of
              C.Name rng cid -> C.Name rng $ w cid
              C.NoName rng (NameId w i) -> C.NoName rng (NameId w 9999999)
      w [] = [C.Id "?????"]
      w [C.Id s] = [C.Id $ s ++ "?????"]
      w (c : cs) = c : w cs
     -}
  NVTApp tf tas -> do
    (flsf, tf') <- floatPatterns0 doCrossCallFloat q vs tf
    floatNVTApp vs flsf tf tas
  NVTLam v tb -> do
    (flsb, tb') <- floatPatterns0 doCrossCallFloat q (v : vs) tb
    floatNVTLam v flsb tb
  NVTLit _ -> return ([], t)
  NVTCon _ -> return ([], t)
  {-
  NVTLet v te tb -> do -- taken care of above.
    do
    (flse, te') <- floatPatterns0 doCrossCallFloat q vs te
    (flsb, tb') <- floatPatterns0 doCrossCallFloat q (v : vs) tb
    let flsb' = filter (not . (v `elemVarSet`) . flFreeVars) flsb
    (fls, fls') <- joinFloatings flse flsb'
    return (fls', foldr applyFloating (NVTLet v te' tb') fls)
  -}
  NVTCase i ct dft alts -> do
    (flsdft, dft') <- floatPatterns0 doCrossCallFloat q vs dft
    (pairs, alts') <- unzip <$> mapM (floatNVTAlt vs) alts
    let (flsCs, flsRs) = unzip pairs
    (flsC, flsR) <- joinFloatingss flsRs
    (_, flsC') <- joinFloatingss (flsC : flsCs)
    let tcore = NVTCase i ct dft' alts'
    return (flsR, foldr applyFloating tcore flsC')
  NVTUnit -> return ([], t)
  NVTSort -> return ([], t)
  NVTErased -> return ([], t)
  NVTError _ -> return ([], t)

  where
-- {{{     floatNVTAlt :: [Var] -> NVTAlt -> U TCM (([Fl],[Fl]), NVTAlt)
    -- |floatNVTAlt| returns a pair like |joinFloatings|
    floatNVTAlt :: [Var] -> NVTAlt -> U TCM (([Floating],[Floating]), NVTAlt)
    floatNVTAlt vs (NVTACon name cvars b) = do
      (flsb, b') <- floatPatterns0 doCrossCallFloat q (reverse cvars ++ vs) b
      return (([], filter (\ fl -> all (not . (`elemVarSet` flFreeVars fl)) cvars) flsb), NVTACon name cvars b')
    floatNVTAlt vs (NVTAGuard g b) = do
      (flsg, g') <- floatPatterns0 doCrossCallFloat q vs g
      (flsb, b') <- floatPatterns0 doCrossCallFloat q vs b
      flsPair <- joinFloatings flsg flsb
      return (flsPair, NVTAGuard g' b')
    floatNVTAlt vs (NVTALit lit b) = do
      (flsb, b') <- floatPatterns0 doCrossCallFloat q vs b
      return (([], flsb), NVTALit lit b')
-- }}}

-- {{{     floatNVTApp :: [Var] [Fl] NVTTerm [NVTTerm] -> U TCM ([Fl], NVTTerm)
    -- Parts of the main |case| in |floatPatterns1| are factored out for
    -- separate use:
    floatNVTApp :: [Var] -> [Floating] -> NVTTerm -> [NVTTerm]
                -> U TCM ([Floating], NVTTerm)
    floatNVTApp vs flsf tf [] = return (flsf, tf)
    floatNVTApp vs flsf tf tas = do
      lift $ do
            reportSDoc "treeless.opt.float.ccf" 50
              $ text ("-- floatNVTApp: " ++ show vs) <+> nest 8
                 (vcat [text "tf = " <+> pretty tf
                       ,text "flsf = " <+> vcat (map pretty flsf)
                       ,text "tas = " <+> vcat (map pretty tas)
                       ,text "control."
                       ])
      (flsas, tas') <- unzip <$> mapM (floatPatterns0 doCrossCallFloat q vs) tas
      (flsC, flsR) <- joinFloatingss $ flsf : flsas
      return (flsR, foldr applyFloating (NVTApp tf tas') flsC)
-- }}}

-- {{{     floatNVTLams :: [Var] -> [Fl] -> NVTTerm -> U TCM ([Fl], NVTTerm)
    floatNVTLams :: [Var] -> [Floating] -> NVTTerm
                 -> U TCM ([Floating], NVTTerm)
    floatNVTLams [] flsb b = return (flsb, b)
    floatNVTLams (u : us) flsb b = do
      (flsb', b') <- floatNVTLams us flsb b
      floatNVTLam u flsb b
-- }}}

-- {{{     floatNVTLam :: Var -> [Fl] -> NVTTerm -> U TCM ([Fl], NVTTerm)
    floatNVTLam :: Var -> [Floating] -> NVTTerm -> U TCM ([Floating], NVTTerm)
    floatNVTLam v flsb tb = do
      return (filter (not . (v `elemVarSet`) . flFreeVars) flsb, NVTLam v tb)
-- }}}

-- {{{     floatNVTLets :: [Var] [(Var, NVTTerm)] [Fl] NVTTerm -> U TCM ([Fl], NVTTerm)
    -- The pairs need to be outside-in!
    floatNVTLets :: [Var] -> [(Var, NVTTerm)] -> [Floating] -> NVTTerm
                 -> U TCM ([Floating], NVTTerm)
    floatNVTLets vs [] flsb tb = return (flsb, tb)
    floatNVTLets vs ((v, te) : ps) flsb tb = do
       (flsb', tb') <- floatNVTLets (v : vs) ps flsb tb
       floatNVTLet vs v te flsb' tb'
-- }}}

-- {{{     floatNVTLet :: [Var] Var NVTTerm [Fl] NVTTerm -> UTCM ([Fl], NVTTerm)
    floatNVTLet :: [Var] -> Var -> NVTTerm -> [Floating] -> NVTTerm
                 -> U TCM ([Floating], NVTTerm)
    floatNVTLet vs v te flsb tb' = do
      lift $ do
            reportSDoc "treeless.opt.float.ccf" 60
              $ text ("-- floatNVTLet 1 " ++ unwords [show vs, show v])
              $$ nest 8
                 (vcat [text "te = " <+> nest 5 (pretty te)
                       ,text "tb = " <+> nest 5 (pretty tb')
                       ,text "flsb = " <+> nest 6 (vcat $ map pretty flsb)
                       ])
      (flse, te') <- floatPatterns0 doCrossCallFloat q vs te
      lift $ do
            reportSDoc "treeless.opt.float.ccf" 60
              $ text ("-- floatNVTLet 2 " ++ unwords [show vs, show v])
              $$ nest 8
                 (vcat [text "te = " <+> nest 5 (pretty te)
                       ,text "tb = " <+> nest 5 (pretty tb')
                       ,text "flsb = " <+> nest 6 (vcat $ map pretty flsb)
                       ,text "te' = " <+> nest 5 (pretty te')
                       ,text "flse = " <+> nest 6 (vcat $ map pretty flse)
                       ])
      let flsb' = filter (not . (v `elemVarSet`) . flFreeVars) flsb
      (fls, fls') <- joinFloatings flse flsb'
      let t' = mkNVTLet v te' tb'

          mSplit = splitFloating t'
      lift $ do
            reportSDoc "treeless.opt.float.ccf" 60
              $ text ("-- floatNVTLet 3 " ++ unwords [show vs, show v])
              $$ nest 8
                 (vcat [text "te = " <+> nest 5 (pretty te)
                       ,text "tb = " <+> nest 5 (pretty tb')
                       ,text "flsb = " <+> nest 6 (vcat $ map pretty flsb)
                       ,text "te' = " <+> nest 5 (pretty te')
                       ,text "flse = " <+> nest 6 (vcat $ map pretty flse)
                       ,text "t' = " <+> nest 5 (pretty t')
                       ,text "fls' = " <+> nest 6 (vcat $ map pretty fls')
                       ,text "mSplit = " <+> nest 9 (pretty mSplit)
                       ])
      case mSplit of
        Nothing -> let -- possible if generated |let|s would be trivial
            t'' = foldr applyFloating t' fls
          in return (fls', t'')
        Just (fl, t'') -> do
          m <- insertFloating fl fls'
          case m of
            (Nothing, fls'') -> do
              lift $ reportSDoc "treeless.opt.float.ccf" 60
                  $ text ("-- floatNVTLet 4 " ++ unwords [show vs, show v])
                  $$ nest 4
                   (vcat [text "fst m = Nothing"
                         ,text "fls'' = " <+> nest 8 (vcat $ map pretty fls'')
                         ])
              return (fl : fls', foldr applyFloating t' fls)
                -- |applyFloating fl| already done in |t'|
                -- \edcomm{WK}{Using |(:)| means assuming outside-in sequence --- check!}
            (Just (cfl, (r1, r2)), fls'')
              -> let
                r1' = domRestrNVRename (flExtraScope fl) r1
                r2' = domRestrNVRename (flExtraScope =<< fls') r2
                -- r = unionNVRename r1' r2'
              -- \edcomm{WK}{Same unfortunate renaming as above in |floatPatterns1 (NVTLet ...)|.}
                r = unionNVRename r1 r2 -- \edcomm{WK}{Worse...}
                t''' = renameNVTTerm r $ foldr applyFloating t'' fls
              in do
                lift $ reportSDoc "treeless.opt.float.ccf" 60
                  $ text ("-- floatNVTLet 4 " ++ unwords [show vs, show v])
                  $$ nest 4
                   (vcat [text "fst m = Just ..."
                         ,text "cfl = " <+> nest 6 (pretty cfl)
                         ,text "r1 = " <+> nest 6 (pretty r1)
                         ,text "r2 = " <+> nest 6 (pretty r2)
                         ,text "r1' = " <+> nest 6 (pretty r1')
                         ,text "r2' = " <+> nest 6 (pretty r2')
                         ,text "fls'' = " <+> nest 8 (vcat $ map pretty fls'')
                         ])
                return (fls', applyFloating cfl t''')
              -- \edcomm{WK}{Same unfortunate renaming as above in |floatPatterns1 (NVTLet ...)|.}
-- }}}

-- {{{     floatNVTDefApp :: [Var] Nat QName [PLet] [NVTT] -> U TCM ([Fl], NVTT)
    -- The plan is to apply this at floating time with |ducall|,
    -- and then extract the |dvArgVars| from that call at squashing time.
    floatNVTDefApp :: [Var] -> Nat -> QName -> [T.PLet] -> [NVTTerm]
                 -> U TCM ([Floating], NVTTerm)
    floatNVTDefApp vs lambdaLen nameF plets ts = do
        used <- lift $ getCompiledArgUse nameF
        let given   = length ts
            needed  = length used
            givenUsed, missingUsed :: [Bool]
            (givenUsed, missingUsed) = splitAt given used

        ((dvArgVars, lets), (ts', newVars)) <- mkArgs used ts lambdaLen
        lift $ do
            reportSDoc "treeless.opt.float.ccf" 50
              $ text "-- floatNVTDefApp 1: " <+> nest 8
                 (vcat [text ("vs = " ++ show vs)
                       ,text ("nameF = " ++ show nameF)
                       ,text ("lambdaLen = " ++ show lambdaLen)
                       ,text ("dvArgVars = " ++ show dvArgVars)
                       ,text ("newVars = " ++ show newVars)
                       ,text ("used = " ++ shows used (' ' : show needed))
                       ,text ("given = " ++ shows given ";") $$ nest 2 (vcat $ map pretty ts)
                       ,text "plets:" $$ nest 2 (vcat $ map pretty plets)
                       ])
        flsF <- pruneFloatings (floatingHasName nameF) emptyVarSet -- \edcomm{WK}{as long as we don't prune at/before CCF registration time}
             <$> floatingsFromPLets (reverse dvArgVars) [] emptyNVRename plets
        let dvArgs = zipWith h givenUsed dvArgVars
              where h False _ = NVTErased
                    h True v = NVTVar v
        flsF <- if nameF == q -- \edcomm{WK}{for now, just cut recursive calls.}
          then return flsF
          else floatFloatings doCrossCallFloat q dvArgVars flsF
        let dvref = NVTDef (NVTDefFloating (dvArgVars ++ concatMap flBoundVars flsF)) nameF
            dvcall = NVTApp dvref dvArgs
        let vs2 = reverse newVars ++ vs
            vs1 = (map fst lets) ++ vs2
        lift $ do
            reportSDoc "treeless.opt.float.ccf" 50
              $ text "-- floatNVTDefApp 2: " <+> nest 8
                 (vcat [text ("nameF = " ++ show nameF)
                       ,text "dvArgs = " <+> pretty dvArgs
                       ,text "dvref  = " <+> pretty dvref
                       ,text "dvcall = " <+> pretty dvcall
                       ,text "flsF = " <+> nest 6 (vcat $ map pretty flsF)
                       ,text "lets = " <+> nest 6 (vcat $ map pretty lets)
                       ,text "vs = " <+> pretty vs
                       ,text "vs1 = " <+> pretty vs1
                       ,text "vs2 = " <+> pretty vs2
                       ,text "control."
                       ])
        (fls1, r1) <- floatNVTLets vs1 (reverse lets) flsF dvcall
        lift $ do
            reportSDoc "treeless.opt.float.ccf" 50
              $ text ("-- floatNVTDefApp result 1 for " ++ show nameF)
              $$ nest 8
                 (vcat [text "vs = " <+> pretty vs
                       ,text "r1 = " <+> nest 5 (pretty r1)
                       ,text "fls1 = " <+> nest 6 (vcat $ map pretty fls1)
                       ])
        liftIO $ hFlush stdout
        liftIO $ hFlush stderr
        (appFloats, r2) <- floatNVTApp vs2 fls1 r1 ts'
        lift $ do
            reportSDoc "treeless.opt.float.ccf" 50
              $ text ("-- floatNVTDefApp p2 for " ++ show nameF)
              $$ nest 8
                 (vcat [text "vs = " <+> pretty vs
                       ,text "r2 = " <+> nest 5 (pretty r2)
                       ,text "appFloats = " <+> nest 6 (vcat $ map pretty appFloats)
                       ])
        liftIO $ hFlush stdout

        p3@(fls3, r3) <- floatNVTLams newVars appFloats r2
        lift $ do
            reportSDoc "treeless.opt.float.ccf" 50
              $ text ("-- floatNVTDefApp result for " ++ show nameF)
              $$ nest 8
                 (vcat [text "vs = " <+> pretty vs
                       ,text "r3 = " <+> nest 5 (pretty r3)
                       ,text "fls3 = " <+> nest 5 (vcat $ map pretty fls3)
                       ])
        liftIO $ hFlush stdout
        return p3
      where
        -- If |mkArgs used ts k = ((dvArgVars, lets), (ts', newVars))|, then
        --  * |dvArgVars| is the list of |k| initial argument variables for |dv|
        --    to be used for |floatingsFromPLets| and for recording in |NVTDefFloating|.
        --    |length dvArgVars = k|
        --  * |lets|: the data needed for creating lets (inside-out)
        --       for non-variable non-erased |ts|
        --  * |ts'|: remaining |ts|
        --  * |newVars|: new variables for eta-expansion;
        --    none if there are remaining |ts|
        -- If |length ts >= k|, then |k + length ts' = length ts|.
        -- If |length ts <= k|, then |length ts + length newVars = k|.
        mkArgs :: [Bool] -> [NVTTerm] -> Nat
               -> U TCM ( ([Var], [(Var, NVTTerm)])
                        , ([NVTTerm],[Var]))
        mkArgs used [] k = do
          vs <- getVars k
          return ((vs, []), ([], vs))
        mkArgs used as 0 = return (([], []), (as, []))
        mkArgs (_ : used') (NVTVar v : as) k
          = first (first (v :)) <$> mkArgs used' as (pred k)
        mkArgs (False : used') (NVTErased : as) k = do
          v <- getVar
          ((avs, lets), q) <- mkArgs used' as (pred k)
          return ((v : avs, lets), q) -- no let for erased arguments
        mkArgs (_ : used') (a : as) k = do
          v <- getVar
          ((avs, lets), q) <- mkArgs used' as (pred k)
          return ((v : avs, (v, a) : lets), q)
        mkArgs [] (_ : _) _ = __IMPOSSIBLE__
-- }}}

-- If |fls| are considered to move into binders of |vs|,
-- then only |pruneFloatings vs fls| are allowed to move in.
-- |fls| are inside-out.
pruneFloatings :: (Floating -> Bool) -> VarSet -> [Floating] -> [Floating]
pruneFloatings mustPrune vs = reverse . pruneRevFloatings mustPrune vs . reverse

pruneRevFloatings :: (Floating -> Bool) -> VarSet -> [Floating] -> [Floating]
pruneRevFloatings _ _ [] = []
pruneRevFloatings mustPrune vs (fl : fls) = let flBs = flBoundVars fl
  in if nullVarSet (vs `intersectionVarSet` flFreeVars fl) && not (mustPrune fl)
  then (fl :) $ pruneRevFloatings mustPrune vs fls
  else pruneRevFloatings mustPrune (foldr insertVarSet vs $ flBoundVars fl) fls


-- |squashFloatings| is to be called after |floatPatterns0|
-- With the improved simplifier, this is necessary only to make sure
-- that "du" bodies are not inlined without actually giving rise to sharing.
-- The |Floating|s in |flsC| are inside-out.
squashFloatings :: Bool -> [Floating] -> NVTTerm -> U TCM NVTTerm
squashFloatings doCrossCallFloat flsC t = do
 lift $ do
            reportSDoc "treeless.opt.float.ccf" 60
              $ text "-- squashFloatings call:"
              $$ nest 8
                 (vcat [text "flsC = " <+> nest 6 (vcat $ map pretty flsC)
                       ,text "t = " <+> nest 5 (pretty t)
                       ])
 case splitFloating t of
  Just (fl, t') -> case matchFloatings fl flsC of
    Just r -> squashFloatings doCrossCallFloat flsC $ renameNVTTerm r t'
      -- \edcomm{WK}{This renaming could perhaps be put into an environment.}
    Nothing -> squashApplyFloating flsC fl
            =<< squashFloatings doCrossCallFloat (fl : flsC) t'
  Nothing -> squashTerm t
    where
    squashTerm :: NVTTerm -> U TCM NVTTerm
    squashTerm t = case t of
      NVTVar _ -> return t
      NVTPrim _ -> return t
      NVTDef NVTDefDefault _name -> return t
      NVTDef NVTDefAbstractPLet _name -> return t -- possible from CCF?
      NVTDef (NVTDefFloating vVars) name
        -> squashTerm $ NVTApp t []
      NVTApp d@(NVTDef (NVTDefFloating vVars) name) ts -> let
          d' = NVTDef NVTDefDefault name
        in if not doCrossCallFloat
        then squashTApp d' ts
        else do
        lift $ do
              reportSDoc "treeless.opt.float.ccf" 30
                $ text ("-- squashFloatings: Checking CCF for " ++ show name)
        mccf <- lift $ getCrossCallFloat name
        case mccf of
          Nothing -> squashTApp d' ts
          Just ccf -> let lambdaLen = ccfLambdaLen ccf in do
            used <- lift $ getCompiledArgUse name
            let given   = length ts
                needed  = length used
                givenUsed, missingUsed :: [Bool]
                (givenUsed, missingUsed) = splitAt given used
            lift $ do
              reportSDoc "treeless.opt.float.ccf" 30
                $ text ("-- squashFloatings: Found CCF for " ++ show name)
              reportSDoc "treeless.opt.float.ccf" 60
                $ nest 4 (pretty ccf)
            lift $ do
                reportSDoc "treeless.opt.float.ccf" 50
                  $ text "-- vVars = " <+> pretty vVars
                reportSDoc "treeless.opt.float.ccf" 50
                  $ text "-- flsC: " <+> nest 8 (pretty flsC)
            -- let (duArgs, ts') = splitAt lambdaLen ts

            {- let (vts, tas) = splitVars ts
              in if length vas < lambdaLen
              then __IMPOSSIBLE__
                -- If other optimisations are added between
                -- floatPatterns0 and squashFloatings,
                -- then the eta expansion etc. in floatNVTDefApp
                -- may need to be duplicated here.
                {-
                do
                reportSDoc "treeless.opt.float.ccf" 20
                  $ text "XXXX squashFloatings.NVTApp-NVTDef " <+> text (show name) <+> pretty tas
                  $$ nest 8 (text "split into" <+> pretty vas <+> pretty tas)
                  $$ nest 8 (pretty ccf)
                squashTApp d' ts
                -}
              else -}
            let
                  (vts, tas') = splitAt lambdaLen ts
                  (vVarsGiven, vVarsExtra) = splitAt given vVars
                  (vVarsLambdaLen, vVarsCCF) = splitAt lambdaLen vVars
                  -- some of the |vts| may be erased;
                  -- we use |vVars| instead for generating the floatings.
  {-
                  (dvVars, tas') = second ((++ tas) . map NVTVar)
                     $ splitAt lambdaLen vas
 -}
                in do
                  lift $ let ps = zipWith (\ v t -> pretty v <+> nest 8 (pretty t)) vVars vts
                     in reportSDoc "treeless.opt.float.ccf" 50
                       $ text "-- AppTDef args: " <+> nest 8 (vcat ps)
                  flsCCF <- floatingsFromPLets (reverse vVarsLambdaLen) vVarsCCF emptyNVRename
                                             $ ccfPLets ccf
                  let flsCCFboundVarss = map flBoundVars flsCCF
                      flsCCFboundVars = concat flsCCFboundVarss
                      renameBvFls [] [] _extraVars r = []
                      renameBvFls (fl : fls) (bvs : bvss) extraVars r
                        = case splitAt (length bvs) extraVars of
                        (extraHere, extraVars') -> let
                            r' = zipInsertNVRename extraHere bvs r
                          in renameFloatingFVars r fl
                          :  renameBvFls fls bvss extraVars' r'
                      renameBvFls _fls _bvss _extraVars _r = __IMPOSSIBLE__
                      -- flsCCF' = renameBvFls flsCCF flsCCFboundVarss vVarsExtra
                                            emptyNVRename
                      {-
                      flsCCFboundVarRename
                         = zipInsertNVRename vVarsExtra
                                             flsCCFboundVars emptyNVRename
                      flsCCF' = map (renameFloating flsCCFboundVarRename) flsCCF
                      flsC' = map (renameFloating flsCCFboundVarRename) flsC
                      -}
                  lift $ do
                      reportSDoc "treeless.opt.float.ccf" 50
                        $ text "-- flsCCFboundVars: " <+> nest 8 (vcat $ map pretty flsCCFboundVarss)
                        $$ text "-- flsCCF: " <+> nest 8 (vcat $ map pretty flsCCF)
                        -- $$ text "-- flsCCF': " <+> nest 8 (vcat $ map pretty flsCCF')
                        -- $$ text "-- flsC': " <+> nest 8 (vcat $ map pretty flsC')
                  let dvArgs0 = zipWith h used vVars
                        where h False _ = Nothing
                              h True v = Just v
                      dvArgs = map (maybe NVTErased NVTVar) dvArgs0
                        -- \edcomm{where are the binders for |missingUsed|?}
                      missingVars = catMaybes $ drop given dvArgs0
                  let dvref = NVTDef NVTDefAbstractPLet name
                      dvcall = NVTApp dvref (dvArgs ++ map NVTVar flsCCFboundVars)
                      -- |wrap flsD fls t0 = (vss, t1)|
                      -- iff |vss| is the list of bound variable lists
                      --                          of the |fls| that match,
                      --     and |t1| is |t0| wrapped into all those elements of |fls|
                      --     that do not match.
                      -- |flsD| start as |flsC|
                      --     and grow by |fls| as the latter are traversed.
                      -- |flsD| are inside-out, like |flsC|.
                      -- |fls| must be outside-in
                      --       --- they are coming from |flsCCF|, should be OK.
                      wrap flsD [] t0 = return ([], t0)
                      wrap flsD (fl : fls) t0 = do
                        let m = matchFloatings fl flsD
                        lift $ do
                          reportSDoc "treeless.opt.float.ccf" 50
                            $ text "-- squashFloatings: Matching " <+> nest 4 (pretty fl)
                          reportSDoc "treeless.opt.float.ccf" 50
                            $ text "-- squashFloatings: against " <+> nest 4 (pretty flsD)
                          reportSDoc "treeless.opt.float.ccf" 50
                            $ text "-- squashFloatings: match result: " <+> nest 4 (pretty m)
                        case m of
                          Nothing -> -- second (applyFloating fl) <$> wrap fls t0
                            do -- expanded for debug output
                            (bvs1, t1) <- wrap (fl : flsD) fls t0
                            t2 <- squashApplyFloating flsD fl t1
                            lift $ reportSDoc "treeless.opt.float.ccf" 50
                              $ text "-- squashFloatings: NO MATCH: "
                              $$ nest 4 (vcat
                                [ text ("length fls = " ++ show (length fls))
                                , text "flsD = " <+> nest 6 (vcat $ map pretty flsD)
                                , text "fl = " <+> nest 6 (pretty fl)
                                , text "t0 = " <+> nest 5 (pretty t0)
                                , text "bvs1 = " <+> pretty bvs1
                                , text "t1 = " <+> nest 5 (pretty t1)
                                , text "t2 = " <+> nest 5 (pretty t2)
                                ])
                            return (bvs1, t2)
                          Just r  -> --  first (flBoundVars fl :)
                                  -- <$> wrap fls (renameNVTTerm r t0)
                            do -- expanded for debug output
                            lift $ reportSDoc "treeless.opt.float.ccf" 50
                              $ text "-- squashFloatings: MATCHED: "
                              $$ nest 4 (vcat
                                [ text ("length fls = " ++ show (length fls))
                                , text "fl = " <+> nest 5 (pretty fl)
                                , text "t0 = " <+> nest 5 (pretty t0)
                                , text "r = " <+> pretty r
                                ])
                            (bvs1, t1) <- wrap flsD (map (renameFloating r) fls)
                                                    (renameNVTTerm r t0)
                            let flBVs = flBoundVars fl
                            lift $ reportSDoc "treeless.opt.float.ccf" 50
                              $ text "-- squashFloatings: MATCHED after recursive wrap call: "
                              $$ nest 4 (vcat
                                [ text ("length fls = " ++ show (length fls))
                                , text "t0 = " <+> nest 5 (pretty t0)
                                , text "bvs1 = " <+> pretty bvs1
                                , text ("flBVs = " ++ show flBVs)
                                ])
                            return (flBVs : bvs1, t1)
                  (matchBVarss, dubodyInlined0 {- (equivalent) -} )
                        <- wrap flsC flsCCF dvcall
                  let dubodyInlined = foldr NVTLam dubodyInlined0 missingVars
                      dv = not $ null matchBVarss
                  result <- if dv
                        then squashTApp dubodyInlined tas'
                        else squashTApp (NVTDef NVTDefDefault name) ts
                  lift $ do
                      reportSDoc "treeless.opt.float.ccf" 50
                        $ text "-- matchBVarss: " <+> nest 8 (vcat $ map pretty matchBVarss)
                      reportSDoc "treeless.opt.float.ccf" 50
                        $ text "-- dubodyInlined: " <+> nest 8 (pretty dubodyInlined)
                      reportSDoc "treeless.opt.float.ccf" 50
                        $ text "-- dv: " <+> pretty dv
                  lift $ if dv
                    then do
                      reportSDoc "treeless.opt.float.ccf" 30
                        $ text ("-- squashFloatings: Instantiated CCF for " ++ show name)
                      reportSDoc "treeless.opt.float.ccf" 50
                        $ text "-- squashFloatings.RESULT: " <+> nest 8 (pretty result)
                    else do
                      reportSDoc "treeless.opt.float.ccf" 40
                        $ text ("-- squashFloatings: Nothing matched in  CCF for " ++ show name)
                        $$ pretty result
                  return result
      NVTApp tf tas -> do
        tf' <- squashFloatings doCrossCallFloat flsC tf
        squashTApp tf' tas
      NVTLam v tb -> NVTLam v <$> squashFloatings doCrossCallFloat flsC' tb
        where flsC' = pruneFloatings (const False) (singletonVarSet v) flsC
      NVTLit _ -> return t
      NVTCon _ -> return t
      NVTLet v te tb -> let flsC' = pruneFloatings (const False) (singletonVarSet v) flsC
        in do
          tb' <- squashFloatings doCrossCallFloat flsC' tb
          squashTLet v te tb'
      NVTCase i ct dft alts -> do
        dft' <- squashFloatings doCrossCallFloat flsC dft
        alts' <- mapM squashTAlt alts
        return $ NVTCase i ct dft' alts'
      NVTUnit -> return t
      NVTSort -> return t
      NVTErased -> return t
      NVTError _ -> return t

    squashTApp tf' [] = return tf'
    squashTApp tf' tas = do
      tas' <- mapM (squashFloatings doCrossCallFloat flsC) tas
      return $ NVTApp tf' tas'

    squashTLet v te tb' = do
      te' <- squashFloatings doCrossCallFloat flsC te
      return $ mkNVTLet v te' tb'

    squashTAlt :: NVTAlt -> U TCM NVTAlt
    squashTAlt (NVTACon name cvars b) = NVTACon name cvars
        <$> squashFloatings doCrossCallFloat flsC' b
      where flsC' = pruneFloatings (const False) (listToVarSet cvars) flsC
    squashTAlt (NVTAGuard g b) = do
      g' <- squashFloatings doCrossCallFloat flsC g
      b' <- squashFloatings doCrossCallFloat flsC b
      return $ NVTAGuard g' b'
    squashTAlt (NVTALit lit b) = NVTALit lit
      <$> squashFloatings doCrossCallFloat flsC b
  where
    -- In |squashFloatings|, the above |applyFloating| cannot be used
    -- since the floating itself needs to be squashed, in particular
    -- for getting rid of |NVTDefFloating|.
    squashApplyFloating :: [Floating] -> Floating -> NVTTerm -> U TCM NVTTerm
    squashApplyFloating flsD plet@(FloatingPLet {pletPat = p}) b {- NVTLet v t1 b) a = -}
      = let
          v = getNVPatVar p
          b' = maybe b (caseNVConPat v `flip` b) (innerNVPat p)
        in do
          e <- squashFloatings doCrossCallFloat flsD $ pletRHS plet
          return $ mkNVTLet v e b'
    squashApplyFloating flsD fcase@(FloatingCase v p extraScope) b
      = return $ caseNVConPat v p b


-- {{{ EMACS lv
--  Local Variables:
--  folded-file: t
--  eval: (fold-set-marks "-- {{{ " "-- }}}")
--  eval: (fold-whole-buffer)
--  fold-internal-margins: 0
--  end:
-- }}}
