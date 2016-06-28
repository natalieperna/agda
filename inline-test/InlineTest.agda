module InlineTest where

open import Data.Bool
open import Data.String
open import Data.Unit.Base
open import IO
open import RATH.Data.Product

prod : Σ s ∶ String • ⊤
prod = "one" , tt

main = run (
     if (proj₁ prod == proj₁ prod)
     then (if (proj₁ prod == "one")
       then putStrLn (proj₁ prod)
       else putStrLn "uh oh")
     else putStrLn "uh oh"
  )

