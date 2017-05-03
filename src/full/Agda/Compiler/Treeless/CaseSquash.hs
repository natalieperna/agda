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

dedupTerm :: Env -> TTerm -> TTerm
dedupTerm env@(n, cs) body =
  case body of
    -- increment vars in scope to account for newly bound
    TLam tt -> TLam (dedupTerm (shiftIndices (+1) env) tt)
    TCase sc t def alts ->
      -- Check if scrutinee is already in scope
      case lookup sc cs of
        -- If in scope with match then substitute
          -- Previous match was a constructor alt
          -- Find the TACon with matching name and replace body with args substituted term, otherwise replace body with default term
        Just match -> caseReplacement n match alts def

        -- Otherwise add to scope in alts
        Nothing -> TCase sc t
          (dedupTerm env def)
          (map (dedupTermHelper sc env) alts)

    -- Continue traversing nested terms
    TApp tt args -> TApp (dedupTerm' tt) (map dedupTerm' args)
    TLet tt1 tt2 -> TLet (dedupTerm' tt1) (dedupTerm (shiftIndices (+1) env) tt2)
    _ -> body
    where
          dedupTerm' = dedupTerm env
          dedupAlt' = dedupAlt env

caseReplacement :: Int -> ConWithArgs -> [TAlt] -> TTerm -> TTerm
caseReplacement n (name, args) alts def =
  case lookupTACon name alts of
    Just (TACon name ar body) -> varReplace [0..ar-1] (reverse args) body
    Just _ -> def -- TODO does this make sense?
    Nothing -> def

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
