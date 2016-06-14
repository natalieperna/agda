{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Pattern matcher used in the reducer for clauses that
--   have not been compiled to case trees yet.

module Agda.TypeChecking.Patterns.Match where

import Prelude hiding (null)

import Data.Monoid
import Data.Traversable (traverse)

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Reduce.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Monad hiding (reportSDoc)
import Agda.TypeChecking.Pretty

import Agda.Utils.Functor (for, ($>))
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Size
import Agda.Utils.Tuple

#include "undefined.h"
import Agda.Utils.Impossible

-- | If matching is inconclusive (@DontKnow@) we want to know whether
--   it is due to a particular meta variable.
data Match a = Yes Simplification [a]
             | No
             | DontKnow (Blocked ())
  deriving Functor

instance Null (Match a) where
  empty = Yes empty empty
  null (Yes simpl as) = null simpl && null as
  null _              = False

-- 'mappend' is UNUSED.
--
-- instance Monoid (Match a) where
--     mempty = Yes mempty []

--     Yes s us   `mappend` Yes s' vs        = Yes (s `mappend` s') (us ++ vs)
--     Yes _ _    `mappend` No               = No
--     Yes _ _    `mappend` DontKnow m       = DontKnow m
--     No         `mappend` _                = No

--     -- @NotBlocked (StuckOn e)@ means blocked by a variable.
--     -- In this case, no instantiation of
--     -- meta-variables will make progress.
--     DontKnow b `mappend` DontKnow b'      = DontKnow $ b `mappend` b'

--     -- One could imagine DontKnow _ `mappend` No = No, but would break the
--     -- equivalence to case-trees.
--     DontKnow m `mappend` _                = DontKnow m

-- | Instead of 'zipWithM', we need to use this lazy version
--   of combining pattern matching computations.

-- Andreas, 2014-05-08, see Issue 1124:
--
-- Due to a bug in TypeChecking.Patterns.Match
-- a failed match of (C n b) against (C O unit)
-- turned into (C n unit).
-- This was because all patterns were matched in
-- parallel, and evaluations of successfull matches
-- (and a record constructor like unit can always
-- be successfully matched) were returned, leading
-- to a reassembly of (C n b) as (C n unit) which is
-- illtyped.

-- Now patterns are matched left to right and
-- upon failure, no further matching is performed.

foldMatch
  :: forall p v . (p -> v -> ReduceM (Match Term, v))
  -> [p] -> [v] -> ReduceM (Match Term, [v])
foldMatch match = loop where
  loop :: [p] -> [v] -> ReduceM (Match Term, [v])
  loop ps0 vs0 = do
    case (ps0, vs0) of
      ([], []) -> return (empty, [])
      (p : ps, v : vs) -> do
        (r, v') <- match p v
        case r of
          No         -> return (No        , v' : vs)
          DontKnow m -> return (DontKnow m, v' : vs)
          Yes s us   -> do
            (r', vs') <- loop ps vs
            let vs1 = v' : vs'
            case r' of
              Yes s' us' -> return (Yes (s `mappend` s') (us ++ us'), vs1)
              No         -> return (No                              , vs1)
              DontKnow m -> return (DontKnow m                      , vs1)
      _ -> __IMPOSSIBLE__

-- | @matchCopatterns ps es@ matches spine @es@ against copattern spine @ps@.
--
--   Returns 'Yes' and a substitution for the pattern variables
--   (in form of [Term]) if matching was successful.
--
--   Returns 'No' if there was a constructor or projection mismatch.
--
--   Returns 'DontKnow' if an argument could not be evaluated to
--   constructor form because of a blocking meta variable.
--
--   In any case, also returns spine @es@ in reduced form
--   (with all the weak head reductions performed that were necessary
--   to come to a decision).
matchCopatterns :: [NamedArg Pattern] -> [Elim] -> ReduceM (Match Term, [Elim])
matchCopatterns ps vs = do
  traceSDoc "tc.match" 50
    (vcat [ text "matchCopatterns"
          , nest 2 $ text "ps =" <+> fsep (punctuate comma $ map (prettyTCM . namedArg) ps)
          , nest 2 $ text "vs =" <+> fsep (punctuate comma $ map prettyTCM vs)
          ]) $ do
     -- Buggy, see issue 1124:
     -- mapFst mconcat . unzip <$> zipWithM' (matchCopattern . namedArg) ps vs
     foldMatch (matchCopattern . namedArg) ps vs

-- | Match a single copattern.
matchCopattern :: Pattern -> Elim -> ReduceM (Match Term, Elim)
matchCopattern (ProjP _ p) elim@(Proj _ q)
  | p == q    = return (Yes YesSimplification [], elim)
  | otherwise = return (No                      , elim)
matchCopattern ProjP{} Apply{}   = __IMPOSSIBLE__
matchCopattern _       Proj{}    = __IMPOSSIBLE__
matchCopattern p       (Apply v) = mapSnd Apply <$> matchPattern p v

matchPatterns :: [NamedArg Pattern] -> [Arg Term] -> ReduceM (Match Term, [Arg Term])
matchPatterns ps vs = do
  traceSDoc "tc.match" 50
    (vcat [ text "matchPatterns"
          , nest 2 $ text "ps =" <+> fsep (punctuate comma $ map (text . show) ps)
          , nest 2 $ text "vs =" <+> fsep (punctuate comma $ map prettyTCM vs)
          ]) $ do
     -- Buggy, see issue 1124:
     -- (ms,vs) <- unzip <$> zipWithM' (matchPattern . namedArg) ps vs
     -- return (mconcat ms, vs)
     foldMatch (matchPattern . namedArg) ps vs

-- | Match a single pattern.
matchPattern :: Pattern -> Arg Term -> ReduceM (Match Term, Arg Term)
matchPattern p u = case (p, u) of
  (ProjP{}, _            ) -> __IMPOSSIBLE__
  (VarP _ , arg@(Arg _ v)) -> return (Yes NoSimplification [v], arg)
  (DotP _ , arg@(Arg _ v)) -> return (Yes NoSimplification [v], arg)
  (LitP l , arg@(Arg _ v)) -> do
    w <- reduceB' v
    let arg' = arg $> ignoreBlocking w
    case ignoreSharing <$> w of
      NotBlocked _ (Lit l')
          | l == l'            -> return (Yes YesSimplification []    , arg')
          | otherwise          -> return (No                          , arg')
      NotBlocked _ (MetaV x _) -> return (DontKnow $ Blocked x ()     , arg')
      Blocked x _              -> return (DontKnow $ Blocked x ()     , arg')
      NotBlocked r t           -> return (DontKnow $ NotBlocked r' () , arg')
        where r' = stuckOn (Apply arg') r

  -- Case record pattern: always succeed!
  -- This case is necessary if we want to use the clauses before
  -- record pattern translation (e.g., in type-checking definitions by copatterns).
  (ConP con@(ConHead c _ ds) ConPatternInfo{conPRecord = Just{}} ps, arg@(Arg info v))
     -- precondition: con actually comes with the record fields
     | size ds == size ps -> mapSnd (Arg info . Con con) <$> do
         matchPatterns ps $ for ds $ \ d -> Arg info $ v `applyE` [Proj ProjSystem d]
           -- TODO: correct info for projected terms
     | otherwise -> __IMPOSSIBLE__

  -- Case data constructor pattern.
  (ConP c _ ps, Arg info v) ->
    do  w <- traverse constructorForm =<< reduceB' v
        -- Unfold delayed (corecursive) definitions one step. This is
        -- only necessary if c is a coinductive constructor, but
        -- 1) it does not hurt to do it all the time, and
        -- 2) whatInduction c sometimes crashes because c may point to
        --    an axiom at this stage (if we are checking the
        --    projection functions for a record type).
{-
        w <- case ignoreSharing <$> w of
               NotBlocked r (Def f es) ->   -- Andreas, 2014-06-12 TODO: r == ReallyNotBlocked sufficient?
                 unfoldDefinitionE True reduceB' (Def f []) f es
                   -- reduceB is used here because some constructors
                   -- are actually definitions which need to be
                   -- unfolded (due to open public).
               _ -> return w
-}
        w <- case w of
               NotBlocked r u -> unfoldCorecursion u  -- Andreas, 2014-06-12 TODO: r == ReallyNotBlocked sufficient?
               _ -> return w
        let v = ignoreBlocking w
            arg = Arg info v  -- the reduced argument
        case ignoreSharing <$> w of
          NotBlocked _ (Con c' vs)
            | c == c'               -> do
                (m, vs) <- yesSimplification <$> matchPatterns ps vs
                return (m, Arg info $ Con c' vs)
            | otherwise             -> return (No                          , arg)
          NotBlocked _ (MetaV x vs) -> return (DontKnow $ Blocked x ()     , arg)
          Blocked x _               -> return (DontKnow $ Blocked x ()     , arg)
          NotBlocked r _            -> return (DontKnow $ NotBlocked r' () , arg)
            where r' = stuckOn (Apply arg) r
-- ASR (08 November 2014). The type of the function could be
--
-- @(Match Term, [Arg Term]) -> (Match Term, [Arg Term])@.
yesSimplification :: (Match a, b) -> (Match a, b)
yesSimplification (Yes _ vs, us) = (Yes YesSimplification vs, us)
yesSimplification r              = r
