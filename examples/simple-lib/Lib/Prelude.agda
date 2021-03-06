
module Lib.Prelude where

infixr 90 _∘_
infixr 1 _,_

id : {A : Set} -> A -> A
id x = x

_∘_ : {A : Set}{B : A -> Set}{C : {x : A} -> B x -> Set}
      (f : {x : A}(y : B x) -> C y)(g : (x : A) -> B x)(x : A) ->
      C (g x)
(f ∘ g) x = f (g x)

data Unit : Set where
  unit : Unit

{-# COMPILE GHC Unit = data () (()) #-}

postulate String : Set

{-# BUILTIN STRING String #-}

data _×_ (A B : Set) : Set where
  _,_ : A -> B -> A × B

{-# COMPILE GHC _×_ = data (,) ((,)) #-}

fst : {A B : Set} -> A × B -> A
fst (x , y) = x

snd : {A B : Set} -> A × B -> B
snd (x , y) = y

