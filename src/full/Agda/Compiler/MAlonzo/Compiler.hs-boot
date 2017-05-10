module Agda.Compiler.MAlonzo.Compiler where

import qualified Agda.Utils.Haskell.Syntax as HS

import Agda.Syntax.Treeless (TTerm)
import Agda.TypeChecking.Monad (TCM)

data GHCOptions

defaultGHCOptions :: GHCOptions

closedTerm :: GHCOptions -> TTerm -> TCM HS.Exp

-- WK: Should we only have a declaration for
--        |closedTerm' = closedTerm defaultGHCOptions| here?
