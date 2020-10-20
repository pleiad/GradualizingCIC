{-# OPTIONS --without-K --prop #-}
module GroundTypes where

open import prelude

private
  variable
    i : Nat


-- "ground types"

data ℂ : Nat → Set where
  ℂnat : ℂ i
  ℂbool : ℂ i
  ℂπ : ℂ i
  ℂ𝕦 : ∀ {j} {j<i : Squash (j < i)} → ℂ i

open import Data.Nat using (_≟_)

abstract
  _≟ℂ_ : DecidableEquality (ℂ i)
  ℂnat ≟ℂ ℂnat = yes erefl
  ℂnat ≟ℂ ℂbool = no λ()
  ℂnat ≟ℂ ℂπ = no λ()
  ℂnat ≟ℂ ℂ𝕦 = no λ()
  ℂbool ≟ℂ ℂnat = no λ()
  ℂbool ≟ℂ ℂbool = yes erefl
  ℂbool ≟ℂ ℂπ = no λ()
  ℂbool ≟ℂ ℂ𝕦 = no λ()
  ℂπ ≟ℂ ℂnat = no λ()
  ℂπ ≟ℂ ℂbool = no λ()
  ℂπ ≟ℂ ℂπ = yes erefl
  ℂπ ≟ℂ ℂ𝕦 = no λ()
  ℂ𝕦 ≟ℂ ℂnat = no λ()
  ℂ𝕦 ≟ℂ ℂbool = no λ()
  ℂ𝕦 ≟ℂ ℂπ = no λ()
  ℂ𝕦 {j = j₁} {x₁} ≟ℂ ℂ𝕦 {j = j₂} {x₂} with j₁ ≟ j₂
  ... | yes erefl = yes erefl
  ... | no h = no (h ∘ aux)
    where
      aux : ℂ𝕦 {j = j₁} {x₁} ≡ ℂ𝕦 {j = j₂} {x₂} → j₁ ≡ j₂
      aux erefl = erefl

ℂε : ℂ i → ℂ i → Set
ℂε = _≡_
