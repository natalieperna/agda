module Agda.Compiler.Treeless.InlineProjections (inlineProjections) where

import Agda.Syntax.Treeless
import Agda.TypeChecking.Monad

inlineProjections :: TTerm -> TCM TTerm
inlineProjections body =
  case body of
    TCase sc t def alts -> return body
    -- | TCase Int CaseType TTerm [TAlt]
    -- ^ Case scrutinee (always variable), case type, default value, alternatives
    otherwise -> return body
