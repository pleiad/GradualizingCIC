{-# OPTIONS --without-K --prop #-}
module top where

open import prelude

import Relation.Unary as RU

open import Relation.Binary.Core
open import Relation.Binary.Structures

open import Poset

-- Negative ⊤

module _ where
  private
    variable
      A : Set

  ⊤ε : ⊤ → A → Set
  ⊤ε _ _ = ⊤

  ⊤ε-hprop : Irrelevant (⊤ε {A})
  ⊤ε-hprop _ _ = erefl

  ?⊤ε : {a : A} (x : ⊤) → ⊤ε {A} x a
  ?⊤ε _ = tt

  ✠⊤ε : (a : A) → ⊤ε tt a
  ✠⊤ε _ = tt

  ⊤ᵖ : Poset₀ ⊤
  ⊤ᵖ = record
    { _⊑_ = ⊤ε
    ; isPoset = record
    { isPreorder = record
      { isEquivalence = PE.isEquivalence
      ; reflexive = λ x → tt
      ; trans = λ x x₁ → tt }
      ; antisym = λ _ _ → erefl }
    ; ⊑-hProp = λ a b → erefl
    ; carrier-hSet = hedberg λ { tt tt → yes erefl } }


  private
    instance
      P⊤ = ⊤ᵖ

  ✠⊤ : Initial ⊤
  ✠⊤ = record
         { bot = tt
         ; is-bot = λ _ → 𝟙
         ; is-bot-spec = λ hbot → erefl
         ; bot-is-bot = ⟨⟩
         ; bot-min = λ hbot → tt
         ; bot-smallest = λ bb' x → ⟨⟩
         }

  ?⊤ : Final ⊤
  ?⊤ = record
    { top = tt
    ; is-top = λ _ → 𝟙
    ; is-top-spec = λ htop → erefl
    ; top-is-top = ⟨⟩
    ; top-max = λ htop → tt
    ; top-greatest = λ bb' x → ⟨⟩
    }

  module ⊤ε-Distr {{PA : Poset₀ A}} (botA : A) (botA-min : (a : A) → botA ⊑ a) where

    pf : PosetDistr.IsRepresentablePosetDistr ⊤ A ⊤ε
    pf = record
      { isPosetDistr = record {
        act-left = λ x x₁ → tt ;
        act-right = λ x x₁ → tt ;
        distr-hProp = λ a b → erefl }
      ; isLeftRepresentable = record {
        up = record { fun = λ x → botA ; monotone = λ x → refl } ;
        up-repr-from = λ {_} {a} x → botA-min a ;
        up-repr-to = λ x → tt }
      ; isRightRepresentable = record {
        down = record { fun = λ x → tt ; monotone = λ x → tt } ;
        down-repr-from = λ x → tt ;
        down-repr-to = λ x → tt }
      }

    ⊤-distr : Distr ⊤ A
    ⊤-distr = record { distr = ⊤ε ; isDistr = pf ; up-down-inverseˡ = λ { tt → erefl } }

