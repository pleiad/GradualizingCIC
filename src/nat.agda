{-# OPTIONS --without-K --prop #-}
module nat where

open import prelude

open import Relation.Binary.Core
open import Relation.Binary.Structures
import Relation.Binary.Bundles as RBB using (Poset)

open import Poset

-- Natural numbers

data ℕ : Set where
  Zℕ : ℕ
  Sℕ : ℕ → ℕ
  ?ℕ : ℕ
  ✠ℕ : ℕ

-- instance
--   excℕ : excType ℕ
--   raise {{excℕ}} true = ?ℕ
--   raise {{excℕ}} false = ✠ℕ

data ℕε : ℕ → ℕ → Set where
  Zℕε : ℕε Zℕ Zℕ
  Sℕε : {n n' : ℕ} → ℕε n n' → ℕε (Sℕ n) (Sℕ n')
  Z?ℕε : ℕε Zℕ ?ℕ
  S?ℕε : ∀ {n} → ℕε n ?ℕ → ℕε (Sℕ n) ?ℕ
  ?ℕℕε : ℕε ?ℕ ?ℕ
  ✠ℕε : {n : ℕ} → ℕε ✠ℕ n

ℕε-hprop : Irrelevant ℕε
ℕε-hprop Zℕε Zℕε = erefl
ℕε-hprop (Sℕε h) (Sℕε h') = PE.cong Sℕε (ℕε-hprop h h')
ℕε-hprop Z?ℕε Z?ℕε = erefl
ℕε-hprop (S?ℕε h) (S?ℕε h') = PE.cong S?ℕε (ℕε-hprop h h')
ℕε-hprop ?ℕℕε ?ℕℕε = erefl
ℕε-hprop ✠ℕε ✠ℕε = erefl

?ℕε : ∀ n → ℕε n ?ℕ
?ℕε Zℕ = Z?ℕε
?ℕε (Sℕ n) = S?ℕε (?ℕε n)
?ℕε ?ℕ = ?ℕℕε
?ℕε ✠ℕ = ✠ℕε


reflℕε : ∀ n → ℕε n n
reflℕε Zℕ = Zℕε
reflℕε (Sℕ n) = Sℕε (reflℕε n)
reflℕε ?ℕ = ?ℕℕε
reflℕε ✠ℕ = ✠ℕε


transℕε : Transitive ℕε
transℕε Zℕε Zℕε = Zℕε
transℕε Zℕε Z?ℕε = Z?ℕε
transℕε (Sℕε mn) (Sℕε np) = Sℕε (transℕε mn np)
transℕε (Sℕε mn) (S?ℕε np) = S?ℕε (transℕε mn np)
transℕε Z?ℕε ?ℕℕε = Z?ℕε
transℕε (S?ℕε mn) ?ℕℕε = S?ℕε mn
transℕε ?ℕℕε ?ℕℕε = ?ℕℕε
transℕε ✠ℕε np = ✠ℕε

antisymℕε : Antisymmetric _≡_ ℕε
antisymℕε Zℕε ba = erefl
antisymℕε (Sℕε ab) (Sℕε ba) = PE.cong Sℕ (antisymℕε ab ba)
antisymℕε ?ℕℕε ba = erefl
antisymℕε ✠ℕε ✠ℕε = erefl

decℕ : DecidableEquality ℕ
decℕ Zℕ Zℕ = yes erefl
decℕ Zℕ (Sℕ y) = no λ()
decℕ Zℕ ?ℕ = no λ()
decℕ Zℕ ✠ℕ = no λ()
decℕ (Sℕ x) Zℕ = no λ()
decℕ (Sℕ x) (Sℕ y) with decℕ x y
... | yes erefl = yes erefl
... | no h = no (h ∘ aux)
  where
    aux : Sℕ x ≡ Sℕ y → x ≡ y
    aux erefl = erefl
decℕ (Sℕ x) ?ℕ = no λ()
decℕ (Sℕ x) ✠ℕ = no λ()
decℕ ?ℕ Zℕ = no λ()
decℕ ?ℕ (Sℕ y) = no λ()
decℕ ?ℕ ?ℕ = yes erefl
decℕ ?ℕ ✠ℕ = no λ()
decℕ ✠ℕ Zℕ = no λ()
decℕ ✠ℕ (Sℕ y) = no λ()
decℕ ✠ℕ ?ℕ = no λ()
decℕ ✠ℕ ✠ℕ = yes erefl


instance
  ℕᵖ : Poset ℕ
  _⊑_ {{ℕᵖ}} = ℕε
  isPoset {{ℕᵖ}} = record
    { isPreorder = record
      { isEquivalence = PE.isEquivalence
      ; reflexive = Reflexive-respects-≡ ℕε (reflℕε $-)
      ; trans = transℕε }
    ; antisym = antisymℕε }
  ⊑-hProp {{ℕᵖ}} = ℕε-hprop
  carrier-hSet {{ℕᵖ}} = hedberg decℕ

✠ℕ' : Initial ℕ {{ℕᵖ}}
✠ℕ' = record
  { bot = ✠ℕ
  ; is-bot = is✠
  ; is-bot-spec = λ {n} → bot-spec n
  ; bot-is-bot = ⟨⟩
  ; bot-min = min
  ; bot-smallest = max'
  }
  where
    is✠ : ℕ → Prop
    is✠ = λ {✠ℕ → 𝟙 ; _ → 𝟘}
    bot-spec : (n : ℕ) (h : is✠ n) → n ≡ ✠ℕ
    bot-spec ✠ℕ h = erefl
    min : {b b' : ℕ} → is✠ b → ℕε b b'
    min {✠ℕ} h = ✠ℕε
    max' : {b b' : ℕ} → ℕε b b' → is✠ b' → is✠ b
    max' {.✠ℕ} {b'} ✠ℕε h = ⟨⟩

?ℕ' : Final ℕ {{ℕᵖ}}
?ℕ' = record
  { top = ?ℕ
  ; is-top = λ { ?ℕ → 𝟙 ; _ → 𝟘 }
  ; is-top-spec = λ { {?ℕ} h → erefl }
  ; top-is-top = ⟨⟩
  ; top-max = λ { {b} {?ℕ} h → ?ℕε b}
  ; top-greatest = λ { {?ℕ} {.?ℕ} ?ℕℕε h → ⟨⟩ }
  }
