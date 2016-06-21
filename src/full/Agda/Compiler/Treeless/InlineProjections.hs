module Agda.Compiler.Treeless.InlineProjections (inlineProjections) where

import Agda.Syntax.Treeless
import Agda.TypeChecking.Monad

inlineProjections :: TTerm -> TCM TTerm
inlineProjections body = return body
