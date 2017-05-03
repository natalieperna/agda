{-# LANGUAGE CPP #-}

module Agda.Compiler.Treeless.CaseSquash (squashCases) where

import Agda.Syntax.Abstract.Name (QName)
import Agda.Syntax.Treeless

import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Monad as TCM

import Agda.Compiler.Treeless.Subst

#include "undefined.h"

-- | Eliminates case expressions where the scrutinee has already
-- been matched on by an enclosing parent case expression.
squashCases :: QName -> TTerm -> TCM TTerm
squashCases q body = return $ dedupTerm (0, []) body

-- | Qualified name of constructor with a list of its arguments
type ConWithArgs = (QName, [Int])

-- | Case scrutinee (de Bruijn index) with alternative match
--   for that expression.
type CaseMatch = (Int, ConWithArgs)

-- | Environment containing next de Bruijn index to be introduced
--   and 'CaseMatch'es in scope.
type Env = (Int, [CaseMatch])

-- | Recurse through 'TTerm's, accumulting environment of case alternatives
--   matched and replacing repeated cases.
--   De Bruijn indices in environment should be appropriatedly shifted as
--   terms are traversed.
dedupTerm :: Env -> TTerm -> TTerm
-- Increment indices in scope to account for newly bound variable
dedupTerm env (TLam tt) = TLam (dedupTerm (shiftIndices (+1) env) tt)
dedupTerm env (TLet tt1 tt2) = TLet (dedupTerm env tt1) (dedupTerm (shiftIndices (+1) env) tt2)

-- Check if scrutinee is already in scope
dedupTerm env@(n, cs) body@(TCase sc t def alts) = case lookup sc cs of
  -- If in scope with match then substitute body
  Just match -> caseReplacement match body

  -- Otherwise add to scope in alt branches
  Nothing -> TCase sc t
    (dedupTerm env def)
    (map (dedupTermHelper sc env) alts)

-- Continue traversing nested terms in applications
dedupTerm env (TApp tt args) = TApp (dedupTerm env tt) (map (dedupTerm env) args)
dedupTerm env body = body

-- | Find the alternative with matching name and replace case term with its body
--   (after necessary substitutions), if it exists.
caseReplacement :: ConWithArgs -> TTerm -> TTerm
caseReplacement (name, args) tt@(TCase _ _ _ alts) =
  case lookupTACon name alts of
    Just (TACon name ar body) -> varReplace [0..ar-1] (reverse args) body
    _ -> tt
caseReplacement _ tt = tt

lookupTACon :: QName -> [TAlt] -> Maybe TAlt
lookupTACon _ [] = Nothing
lookupTACon match ((alt@(TACon name ar body)):alts) = if (match == name)
                                                      then Just alt
                                                      else lookupTACon match alts
lookupTACon match (_:alts) = lookupTACon match alts

-- TODO Better name
dedupTermHelper :: Int -> Env -> TAlt -> TAlt
dedupTermHelper sc env alt =
  case alt of
    TACon name ar body -> TACon name ar (dedupTerm env' body)
      where
        env' = addToEnv (sc + ar, (name, [ar-1,ar-2..0])) (shiftIndices (+ar) env)
    TAGuard guard body -> TAGuard guard (dedupTerm env body)
    TALit lit body -> TALit lit (dedupTerm env body)

addToEnv :: CaseMatch -> Env -> Env
addToEnv c (n, cs) = (n, c:cs)

dedupAlt :: Env -> TAlt -> TAlt
dedupAlt env alt =
  case alt of
    TACon name ar body -> TACon name ar (dedupTerm (shiftIndices (+ar) env) body)
    TAGuard guard body -> TAGuard guard (dedupTerm env body)
    TALit lit body -> TALit lit (dedupTerm env body)

-- TODO make this function less ugly and repetitive
shiftIndices :: (Int -> Int) -> Env -> Env
shiftIndices f (n, cs) = (f n, map (shiftIndices' f) cs)
  where
    shiftIndices' :: (Int -> Int) -> CaseMatch -> CaseMatch
    shiftIndices' f (sc, (name, vars)) = (f sc, (name, map f vars))

varReplace :: [Int] -> [Int] -> TTerm -> TTerm
varReplace (from:froms) (to:tos) = subst from (TVar to) . varReplace froms tos
varReplace [] [] = id
-- TODO handle these
varReplace _ _ = error "Mismatched arguments"
