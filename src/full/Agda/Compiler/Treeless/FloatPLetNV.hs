{-# LANGUAGE CPP #-}
module Agda.Compiler.Treeless.FloatPLetNV where

import Control.Applicative
import Control.Monad.Reader
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
  , pletBinders :: [Var]
  , pletNVTT :: NVTTerm -- |NVTErased| signals the end of the pattern
  } deriving (Show)

corePLet :: PLet -> (IntSet, NVTTerm) -- let-body only
corePLet (PLet fv1 _ (NVTLet _ t1 _)) = (fv1, t1)
corePLet _ = __IMPOSSIBLE__

eqPLet :: PLet -> PLet -> Bool
eqPLet = (==) `on` corePLet

instance Eq PLet where (==) = eqPLet

applyPLet :: NVTTerm -> NVTTerm -> NVTTerm
applyPLet (NVTLet v t1 b) a = NVTLet v t1 $ h b
  where
    h (NVTCase v' ct def [NVTACon c cvars b'])
      = NVTCase v' ct def [NVTACon c cvars (h b')]
    h NVTErased = a
    h _ = __IMPOSSIBLE__
applyPLet _ _ = __IMPOSSIBLE__

-- If |splitPLet t = Just (pl, t')|, then |applyPLet (pletNVTT pl) t' = t|.
splitPLet :: NVTTerm -> Maybe (PLet, NVTTerm)
splitPLet (NVTLet v t1 t2) = case splitBoundedCase [v] t2 of
  Just ((pat, vs), t') -> Just (PLet (fvarsNVTTerm t1) vs (NVTLet v t1 pat), t')
  Nothing -> Nothing
splitPLet _ = Nothing

-- |splitBoundedCase vs t = Just ((t0, vs'), t1)| means
-- that |applyPLet t0 t1 == t|
-- and |vs'| contains |vs| and the additional pattern variables of |t0|
splitBoundedCase :: [Var] -> NVTTerm -> Maybe ((NVTTerm, [Var]), NVTTerm)
splitBoundedCase vs (NVTCase v ct dft [NVTACon c cvars t2]) | v `elem` vs && harmless dft
  = let ((b', vs'), t') = let vs2 = vs ++ cvars in case splitBoundedCase vs2 t2 of
          Nothing -> ((NVTErased, vs2), t2)
          Just r -> r
    in Just ((NVTCase v ct dft [NVTACon c cvars b'], vs'), t')
splitBoundedCase _ _ = Nothing

-- | ``harmless'' in the sense of negligible as default expression in |TCase|:
harmless :: NVTTerm -> Bool
harmless (NVTError _)  = True
harmless NVTUnit       = True
harmless NVTErased     = True
harmless NVTSort       = True
harmless _             = False

-- |  @floatPLet@ floats pattern lets occuring in multiple branches
--    to the least join point of those branches.
floatPLet :: TTerm -> TTerm
floatPLet = toTTerm' . floatPLetNV . fromTTerm'
-- -- For all the details:
--  floatPLet t = let
--    nvt = fromTTerm' t
--    nvt' = floatPLetNV nvt
--    t' = toTTerm' nvt'
--    in trace (unlines
--     ["floatPLet", "    " ++ show nvt, "\n    " ++ show nvt']) t'

floatPLetNV :: NVTTerm -> NVTTerm
floatPLetNV = squashPLet [] . snd . floatPLet0

-- [PLet] invariant: elements unique up to |eqPLet|.

-- | @joinPLets@ returns the (maximal) common elements first, and then a nubbed concatenation (of the maximal elements).
joinPLets :: [PLet] -> [PLet] -> ([PLet], [PLet])
joinPLets = h id
  where
    h acc [] ps2 = (acc [], ps2)
    h acc (p1 : ps1) ps2 = let (mc, ps2') = insertPLet p1 ps2
      in h (acc . maybe id (:) mc) ps1 ps2'


insertPLet :: PLet -> [PLet] -> (Maybe PLet, [PLet])
insertPLet p ps = case partition (p `matchesPLet`) ps of
  ([p'], ps') -> (Just p', ps)
  ([], _) -> case partition (`matchesPLet` p) ps of
    ([], _) -> (Nothing, p : ps)
    (_, ps') -> (Just p, p : ps')
  _ -> __IMPOSSIBLE__ -- due to absence of duplicates in |ps|

joinPLetss :: [[PLet]] -> ([PLet], [PLet])
joinPLetss [] = ([], [])
joinPLetss [ps] = ([], ps)
joinPLetss (ps : pss) = case joinPLetss pss of
  (psC, psR) -> case joinPLets ps psR of
    (psC', psR') -> (filter (`notElem` psC) psC' ++ psC, psR')

mkRename :: [Var] -> [Var] -> Maybe (IntMap Var)
mkRename vs1 vs2 = case filter (uncurry (/=)) $ zip vs1 vs2 of
  [] -> Nothing
  ps -> Just $ foldr (uncurry (IntMap.insert . unV)) IntMap.empty ps

renameNVTTerm' :: [Var] -> [Var] -> NVTTerm -> NVTTerm
renameNVTTerm' vs1 vs2 t = case mkRename vs1 vs2 of
  Nothing -> t
  Just m -> renameNVTTerm m t

-- | @floatPLet0@ duplicates PLet occurrences at join points.
floatPLet0 :: NVTTerm -> ([PLet], NVTTerm)
floatPLet0 t = case splitPLet t of
  Just (p, t') -> case floatPLet0 t' of
    (ps, t'') -> case insertPLet p ps of
      (Nothing, ps') -> (ps', applyPLet (pletNVTT p) t'')
      (Just c, ps') -> (ps', applyPLet (pletNVTT c) $ renameNVTTerm' (pletBinders p) (pletBinders c) t'')
  Nothing -> case t of
    NVTVar _ -> ([], t)
    NVTPrim _ -> ([], t)
    NVTDef _ -> ([], t)
    NVTApp tf tas -> let
      (psf, tf') = floatPLet0 tf
      (psas, tas') = unzip $ map floatPLet0 tas
      (psC, psR) = joinPLetss $ psf : psas
      in (psR, foldr (applyPLet . pletNVTT) (NVTApp tf' tas') psC)
    NVTLam v tb -> case floatPLet0 tb of
      (ps, tb') -> (filter ((unV v `IntSet.notMember`) . pletFVars) ps, NVTLam v tb')
    NVTLit _ -> ([], t)
    NVTCon _ -> ([], t)
    NVTLet v te tb -> case floatPLet0 tb of
      (psb, tb') -> let psb' = filter ((unV v `IntSet.notMember`) . pletFVars) psb
        in case floatPLet0 te of
        (pse, te') -> case joinPLets pse psb' of
          (ps, ps') -> (ps', foldr (applyPLet . pletNVTT) (NVTLet v te' tb') ps)
    NVTCase i ct dft alts -> case floatPLet0 dft of
      (psdft, dft') -> case unzip $ map h alts of
        (pairs, alts') -> case unzip pairs of
          (psCs, psRs) -> case joinPLetss psRs of
            (psC, psR) -> let psC' = nub $ concat (psCs ++ [psC]) -- \unfinished
              in (psR, foldr (applyPLet . pletNVTT) (NVTCase i ct dft' alts') psC')
    NVTUnit -> ([], t)
    NVTSort -> ([], t)
    NVTErased -> ([], t)
    NVTError _ -> ([], t)
  where
    -- |h| returns a pair like |joinPLets|
    h :: NVTAlt -> (([PLet],[PLet]), NVTAlt)
    h (NVTACon name cvars b) = case floatPLet0 b of
      (psb, b') -> (([], filter (\ p -> all ((`IntSet.notMember` pletFVars p) . unV) cvars) psb), NVTACon name cvars b')
    h (NVTAGuard g b) = case floatPLet0 g of
      (psg, g') -> case floatPLet0 b of
        (psb, b') -> (joinPLets psg psb, NVTAGuard g' b')
    h (NVTALit lit b) = case floatPLet0 b of
      (psb, b') -> (([], psb), NVTALit lit b')

-- |matchPLet p1 p2 = Just m| means that |p1| is a prefix of |p2|,
-- and |m| rnames |p1|-variables to |p2|variables.
matchPLet :: PLet -> PLet -> Maybe (IntMap Var)
matchPLet p1 p2 = case pletNVTT p1 of
  NVTLet v1 e1 b1 -> case pletNVTT p2 of
    NVTLet v2 e2 b2 | e1 == e2 -> IntMap.insert (unV v1) v2 <$> matchCase b1 b2
    _ -> Nothing
  _ -> Nothing

matchesPLet :: PLet -> PLet -> Bool
matchesPLet p1 p2 = isJust $ matchPLet p1 p2


matchCase :: NVTTerm -> NVTTerm -> Maybe (IntMap Var)
matchCase  (NVTCase v1 ct1 dft1 [NVTACon c1 cvars1 b1])
           (NVTCase v2 ct2 dft2 [NVTACon c2 cvars2 b2])
  | c1 == c2 && harmless dft1 && harmless dft2
  = case matchCase b1 b2 of
    Nothing -> Nothing 
    Just m -> Just . foldr (uncurry (IntMap.insert . unV)) m $ zip cvars1 cvars2
matchCase NVTErased _ = Just IntMap.empty
matchCase _ _ = Nothing

-- |squashPLet| is to be called after |floatPLet0|
squashPLet :: [PLet] -> NVTTerm -> NVTTerm
squashPLet ps t = case splitPLet t of
  Just (p, t') -> case msum $ map (matchPLet p) ps of
    Just m -> squashPLet ps $ renameNVTTerm m t'
    Nothing -> applyPLet (pletNVTT p) $ squashPLet (p : ps) t'
  Nothing -> case t of
    NVTVar _ -> t
    NVTPrim _ -> t
    NVTDef _ -> t
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


testFloatPLet :: String
testFloatPLet = let r = splitPLet tt1
  in "\n=== FloatPLet: " ++ shows r "\n"

tt1 :: NVTTerm
tt1 = NVTLet (V 0) (NVTLit (LitNat NoRange 15))
   (NVTCase (V 0) (CTData $ name0 1 "Pair") NVTErased [NVTACon (name0 2 "pair") [V 1, V 2]
     (NVTLit (LitNat NoRange 42))])

name0 :: Word64 -> RawName -> QName
name0 i s = QName (MName []) (Name (NameId i 0) (C.Name NoRange [C.Id s]) NoRange noFixity')