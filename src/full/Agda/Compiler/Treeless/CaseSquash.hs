{-# LANGUAGE CPP #-}
-- | Eliminates case expressions where the scrutinee has already
-- been matched on by an enclosing parent case expression.
module Agda.Compiler.Treeless.CaseSquash (squashCases) where

import Agda.Syntax.Abstract.Name (QName)
import Agda.Syntax.Treeless

import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Monad as TCM

import Agda.Compiler.Treeless.Subst

#include "undefined.h"

-- TODO Find the actual technical term for this type of compiler optimization
squashCases :: QName -> TTerm -> TCM TTerm
squashCases q body = return $ dedupTerm (0, []) body
-- (constructor name, constructor arguments)
type ConWithArgs = (QName, [Int])
-- CaseMatch: (case scrutinee, Maybe ConWithArgs)
-- (sc, Nothing) indicates the default case
type CaseMatch = (Int, Maybe ConWithArgs)
-- (next variable index, cases in scope)
type Env = (Int, [CaseMatch])

dedupTerm :: Env -> TTerm -> TTerm
dedupTerm (n, env) body =
  case body of
    -- increment vars in scope to account for newly bound
    TLam tt -> TLam (dedupTerm (n + 1, modifyCaseScope (+1) env) tt)
    TCase sc t def alts ->
      -- Check if scrutinee is already in scope
      case lookup sc env of
        -- If in scope with match then substitute
        Just existingCase -> case existingCase of
          -- Previous match was a constructor alt
          -- Find the TACon with matching name and replace body with args substituted term, otherwise replace body with default term
          Just match -> caseReplacement n match alts def
          -- Previous match was a default case
          -- TODO Add more info to environment to handle this. If the default case was followed before, then maybe the default case should be followed again, but we should first check that the other TAlts are the same as they were in the "match".
          Nothing ->
            TCase sc t
            (dedupTerm' def)
            (map dedupAlt' alts)

        -- Otherwise add to scope
        Nothing -> TCase sc t
          (dedupTerm defEnv def)
          (map (dedupTermHelper sc (n, env)) alts)
          where
            defEnv = (n, (sc,Nothing):env)

    -- Continue traversing nested terms
    TApp tt args -> TApp (dedupTerm' tt) (map dedupTerm' args)
    TLet tt1 tt2 -> TLet (dedupTerm' tt1) (dedupTerm (n + 1, modifyCaseScope (+1) env) tt2)
    _ -> body
    where
          dedupTerm' = dedupTerm (n, env)
          dedupAlt' = dedupAlt (n, env)

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
dedupTermHelper sc (n, env) alt =
  case alt of
    TACon name ar body -> TACon name ar (dedupTerm (n + ar, bindVars name ar sc env) body)
    TAGuard guard body -> TAGuard guard (dedupTerm' body)
    TALit lit body -> TALit lit (dedupTerm' body)
    where
      dedupTerm' = dedupTerm (n, env)
      bindVars name ar sc env = (sc+ar,Just (name, [ar-1,ar-2..0])):modifyCaseScope (+ar) env

dedupAlt :: Env -> TAlt -> TAlt
dedupAlt (n, env) alt =
  case alt of
    TACon name ar body -> TACon name ar (dedupTerm (n + ar, modifyCaseScope (+ar) env) body)
    TAGuard guard body -> TAGuard guard (dedupTerm' body)
    TALit lit body -> TALit lit (dedupTerm' body)
    where
      dedupTerm' = dedupTerm (n, env)

-- TODO make this function less ugly and repetitive
modifyCaseScope :: (Int -> Int) -> [CaseMatch] -> [CaseMatch]
modifyCaseScope f = map (modifyCaseScope' f)
  where
    modifyCaseScope' :: (Int -> Int) -> CaseMatch -> CaseMatch
    modifyCaseScope' f (sc, Nothing) = (f sc, Nothing)
    modifyCaseScope' f (sc, Just (name, vars)) = (f sc, Just (name, map f vars))

varReplace :: [Int] -> [Int] -> TTerm -> TTerm
varReplace (from:froms) (to:tos) = subst from (TVar to) . varReplace froms tos
varReplace [] [] = id
-- TODO handle these
varReplace _ _ = error "Mismatched arguments"
