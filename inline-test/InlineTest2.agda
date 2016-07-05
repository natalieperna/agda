module InlineTest2 where

open import Level
open import Relation.Binary using (Poset)
open import Relation.Binary.Poset.Meet using (module PosetMeet)

module HasMeetProps  {j k₁ k₂ : Level} (𝒫 : Poset j k₁ k₂)
                     (meet : (R S : Poset.Carrier 𝒫) → PosetMeet.Meet 𝒫 R S) where
  open Poset 𝒫
  open PosetMeet 𝒫
  infixr 7 _∧_

  _∧_ : Carrier → Carrier → Carrier
  R ∧ S = Meet.value (meet R S)

  ≤-from-∧₂ : {R S : Carrier} → R ∧ S ≈ S → S ≤ R
  ≤-from-∧₂ {R} {S} = ≤-from-Meet₂ (meet R S)
