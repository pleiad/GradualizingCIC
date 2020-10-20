{-# OPTIONS --without-K --prop #-}
module bool where

open import prelude

open import Relation.Binary.Core
open import Relation.Binary.Structures
import Relation.Binary.Bundles as RBB using (Poset)

open import Poset

-- Booleans

data 𝔹 : Set where
  true𝔹 : 𝔹
  false𝔹 : 𝔹
  ?𝔹 : 𝔹
  ✠𝔹 : 𝔹

-- instance
--   exc𝔹 : excType 𝔹
--   raise {{exc𝔹}} true = ?𝔹
--   raise {{exc𝔹}} false = ✠𝔹

data 𝔹ε : 𝔹 → 𝔹 → Set where
  true𝔹ε : 𝔹ε true𝔹 true𝔹
  false𝔹ε : 𝔹ε false𝔹 false𝔹
  true?𝔹ε : 𝔹ε true𝔹 ?𝔹
  false?𝔹ε : 𝔹ε false𝔹 ?𝔹
  ?𝔹𝔹ε : 𝔹ε ?𝔹 ?𝔹
  ✠𝔹ε : {b : 𝔹} → 𝔹ε ✠𝔹 b

𝔹ε-hprop : Irrelevant 𝔹ε
𝔹ε-hprop true𝔹ε true𝔹ε = erefl
𝔹ε-hprop false𝔹ε false𝔹ε = erefl
𝔹ε-hprop true?𝔹ε true?𝔹ε = erefl
𝔹ε-hprop false?𝔹ε false?𝔹ε = erefl
𝔹ε-hprop ?𝔹𝔹ε ?𝔹𝔹ε = erefl
𝔹ε-hprop ✠𝔹ε ✠𝔹ε = erefl


?𝔹ε : (b : 𝔹) → 𝔹ε b ?𝔹
?𝔹ε true𝔹 = true?𝔹ε
?𝔹ε false𝔹 = false?𝔹ε
?𝔹ε ?𝔹 = ?𝔹𝔹ε
?𝔹ε ✠𝔹 = ✠𝔹ε

refl𝔹ε : (b : 𝔹) → 𝔹ε b b
refl𝔹ε true𝔹 = true𝔹ε
refl𝔹ε false𝔹 = false𝔹ε
refl𝔹ε ?𝔹 = ?𝔹𝔹ε
refl𝔹ε ✠𝔹 = ✠𝔹ε

trans𝔹ε : Transitive 𝔹ε
trans𝔹ε true𝔹ε true𝔹ε = true𝔹ε
trans𝔹ε true𝔹ε true?𝔹ε = true?𝔹ε
trans𝔹ε false𝔹ε false𝔹ε = false𝔹ε
trans𝔹ε false𝔹ε false?𝔹ε = false?𝔹ε
trans𝔹ε true?𝔹ε ?𝔹𝔹ε = true?𝔹ε
trans𝔹ε false?𝔹ε ?𝔹𝔹ε = false?𝔹ε
trans𝔹ε ?𝔹𝔹ε ?𝔹𝔹ε = ?𝔹𝔹ε
trans𝔹ε ✠𝔹ε bc = ✠𝔹ε

antisym𝔹ε : Antisymmetric _≡_ 𝔹ε
antisym𝔹ε true𝔹ε ba = erefl
antisym𝔹ε false𝔹ε ba = erefl
antisym𝔹ε ?𝔹𝔹ε ba = erefl
antisym𝔹ε ✠𝔹ε ✠𝔹ε = erefl

dec𝔹 : DecidableEquality 𝔹
dec𝔹 true𝔹 true𝔹 = yes erefl
dec𝔹 true𝔹 false𝔹 = no λ()
dec𝔹 true𝔹 ?𝔹 = no λ()
dec𝔹 true𝔹 ✠𝔹 = no λ()
dec𝔹 false𝔹 true𝔹 = no λ()
dec𝔹 false𝔹 false𝔹 = yes erefl
dec𝔹 false𝔹 ?𝔹 = no λ()
dec𝔹 false𝔹 ✠𝔹 = no λ()
dec𝔹 ?𝔹 true𝔹 = no λ()
dec𝔹 ?𝔹 false𝔹 = no λ()
dec𝔹 ?𝔹 ?𝔹 = yes erefl
dec𝔹 ?𝔹 ✠𝔹 = no λ()
dec𝔹 ✠𝔹 true𝔹 = no λ()
dec𝔹 ✠𝔹 false𝔹 = no λ()
dec𝔹 ✠𝔹 ?𝔹 = no λ()
dec𝔹 ✠𝔹 ✠𝔹 = yes erefl

instance
  𝔹ᵖ : Poset 𝔹
  _⊑_ {{𝔹ᵖ}} = 𝔹ε
  isPoset {{𝔹ᵖ}} = record
    { isPreorder = record
      { isEquivalence = PE.isEquivalence
      ; reflexive = Reflexive-respects-≡ 𝔹ε (refl𝔹ε $-)
      ; trans = trans𝔹ε }
    ; antisym = antisym𝔹ε }
  ⊑-hProp {{𝔹ᵖ}} = 𝔹ε-hprop
  carrier-hSet {{𝔹ᵖ}} = hedberg dec𝔹

✠𝔹' : Initial 𝔹 {{𝔹ᵖ}}
✠𝔹' = record
  { bot = ✠𝔹
  ; is-bot = is✠
  ; is-bot-spec = λ {n} → bot-spec n
  ; bot-is-bot = ⟨⟩
  ; bot-min = min
  ; bot-smallest = max'
  }
  where
    is✠ : 𝔹 → Prop
    is✠ = λ {✠𝔹 → 𝟙 ; _ → 𝟘}
    bot-spec : (n : 𝔹) (h : is✠ n) → n ≡ ✠𝔹
    bot-spec ✠𝔹 h = erefl
    min : {b b' : 𝔹} → is✠ b → 𝔹ε b b'
    min {✠𝔹} h = ✠𝔹ε
    max' : {b b' : 𝔹} → 𝔹ε b b' → is✠ b' → is✠ b
    max' {.✠𝔹} {b'} ✠𝔹ε h = ⟨⟩


?𝔹' : Final 𝔹 {{𝔹ᵖ}}
?𝔹' = record
  { top = ?𝔹
  ; is-top = λ { ?𝔹 → 𝟙 ; _ → 𝟘 }
  ; is-top-spec = λ { {?𝔹} h → erefl }
  ; top-is-top = ⟨⟩
  ; top-max = λ { {b} {?𝔹} h → ?𝔹ε b}
  ; top-greatest = λ { {?𝔹} {.?𝔹} ?𝔹𝔹ε h → ⟨⟩ }
  }
