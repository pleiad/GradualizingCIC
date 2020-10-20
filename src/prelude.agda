{-# OPTIONS  --without-K --prop #-}
module prelude where

open import Agda.Primitive public
open import Agda.Builtin.Unit public
open import Agda.Builtin.Bool public
open import Data.Nat.Base renaming (ℕ to Nat; _⊔_ to max) hiding (_≤_) public
open import Data.Product renaming (proj₁ to fst ; proj₂ to snd) public


open import Function.Base public

open import Relation.Binary.Core public
open import Relation.Binary.Definitions public
module RB = Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to erefl) public
module PE = Relation.Binary.PropositionalEquality

open import Relation.Nullary renaming (Irrelevant to ishProp) public

import Relation.Unary
module RU = Relation.Unary

open import Axiom.Extensionality.Propositional
FunextStatement : Set₁
FunextStatement = Extensionality lzero lzero
postulate funext : {l l' : Level} → Extensionality l l'
postulate funext-impl : {l l' : Level} → ExtensionalityImplicit l l'

∀-ext : ∀ {a b} → {A : Set a} (B₁ B₂ : A → Set b) →
                   (∀ x → B₁ x ≡ B₂ x) →
                   (∀ x → B₁ x) ≡ (∀ x → B₂ x)
∀-ext = ∀-extensionality funext

postulate ∀impl-ext : ∀ {a b} →
                   {A : Set a} (B₁ B₂ : A → Set b) →
                   (∀ {x} → B₁ x ≡ B₂ x) →
                   (∀ {x} → B₁ x) ≡ (∀ {x} → B₂ x)

hSet : ∀ {l} (A : Set l) → Set l
hSet A = Irrelevant(_≡_ {_} {A})

postulate irrelevant-is-hProp : ∀ {lA lB l} {A : Set lA} {B : Set lB} (R : REL A B l) → ishProp (Irrelevant R)
postulate hSet-is-hProp : ∀ {l} {A : Set l} → ishProp (hSet A)

postulate hProp-to-hSet : ∀ {l} {A : Set l} → ishProp A → hSet A

postulate hpropext : ∀ {l} {P Q : Set l} → ishProp P → ishProp Q → (P → Q) → (Q → P) → P ≡ Q

postulate hProp-hSet : ∀ {l} {P Q : Set l} → ishProp P → ishProp Q → ishProp (P ≡ Q)

open import Data.Empty renaming (⊥ to Empty) public

module Hedberg where
  _·_ : ∀ {l} {A : Set l} {x y z : A} (p : x ≡ y) (q : y ≡ z) → x ≡ z
  erefl · q = q

  !_ : {A : Set} {x y : A} (p : x ≡ y) → y ≡ x
  ! erefl = erefl

  comp-left-inverse : {A : Set} {x y : A} (p : x ≡ y) → (! p) · p ≡ erefl
  comp-left-inverse erefl = erefl

  private
    normalize-eq-type : {A : Set} {a : A} (deca : RU.Decidable (_≡_ a)) {x : A} (p : a ≡ x) → Set
    normalize-eq-type {a = a} deca {x} p with deca a with deca x
    ... | yes aa | yes ax = p ≡ (! aa) · ax
    ... | _ | _ = Empty

    normalize-eq : {A : Set} {a : A} (deca : RU.Decidable (_≡_ a)) {x : A} (p : a ≡ x) → normalize-eq-type deca p
    normalize-eq {a = a} deca {x} erefl with deca a
    ... | yes aa = PE.sym (comp-left-inverse aa)
    ... | no h = ⊥-elim (h erefl)

  local-hedberg : {A : Set} (a : A) → RU.Decidable (_≡_ a) → RU.Irrelevant (_≡_ a)
  local-hedberg a deca {x} p q with deca a with deca x with normalize-eq deca p with normalize-eq deca q
  ... | yes _ | yes _ | p' | q' = p' · (! q')
  ... | no _ | _ | () | q'
  ... | yes _ | no _ | () | q'

  hedberg : {A : Set} → DecidableEquality A → hSet A
  hedberg decA {a} = local-hedberg a (decA $-)

open Hedberg public

subst-· : ∀ {l l'} {A : Set l} (P : A → Set l') {ax ay az : A} (h : ax ≡ ay) (h' : ay ≡ az) (x : P ax)→
          PE.subst P (h · h') x ≡ PE.subst P h' (PE.subst P h x)
subst-· P erefl _ _ = erefl

postulate ∀-hSet : {A : Set} {B : A → Set} (hSetB : ∀ a → hSet (B a)) → hSet (∀ a → B a)
postulate ∀impl-hSet : {A : Set} {B : A → Set} (hSetB : ∀ {a} → hSet (B a)) → hSet (∀ {a} → B a)
postulate Σ-hset : {A : Set} {B : A → Set} (hSetA : hSet A) (hSetB : ∀ a → hSet (B a)) → hSet (Σ A B)

J : {A : Set} {a : A} (P : (a' : A) (eq : a ≡ a') → Set) {a' : A} (eq : a ≡ a') (x : P a erefl) → P a' eq
J P erefl x = x

substProp : {A : Set} {a : A} (P : A → Prop) {a' : A} (eq : a ≡ a') (x : P a) → P a'
substProp P erefl x = x


data 𝟘 : Prop where

absurd : ∀ {l} {A : Set l} → 𝟘 → A
absurd ()

data 𝟙 : Prop where
  ⟨⟩ : 𝟙

data Box (P : Prop) : Set where
  ⟦_⟧ : (p : P) → Box P

data Squash {l} (A : Set l) : Prop l where
  ⟦_⟧' : (a : A) → Squash A

data _⊗_ (P Q : Prop) : Prop where
  ⟨_,_⟩ : P → Q → P ⊗ Q

⊗fst : {P Q : Prop} → P ⊗ Q → P
⊗fst ⟨ x , _ ⟩ = x

⊗snd : {P Q : Prop} → P ⊗ Q → Q
⊗snd ⟨ _ , y ⟩ = y

data ⊗dep (P : Prop) (Q : P → Prop) : Prop where
  ⟪_,_⟫ : ∀ (h : P) → Q h → ⊗dep P Q

infix 2 ⊗dep-syntax
⊗dep-syntax : ∀ (P : Prop) → (P → Prop) → Prop
⊗dep-syntax = ⊗dep
syntax ⊗dep-syntax P (λ h → Q) = ⊗[ h ∈ P ] Q

⊗dfst : ∀ {P : Prop} {Q : P → Prop} → ⊗[ h ∈ P ] Q h → P
⊗dfst ⟪ h , _ ⟫ = h

⊗dsnd : ∀ {P : Prop} {Q : P → Prop} (wit : ⊗[ h ∈ P ] Q h) → Q (⊗dfst wit)
⊗dsnd ⟪ h , x ⟫ = x

-- data _⊕_ (p q : Prop) : Prop where
--   inl₁ : p → p ⊕ q
--   inl₂ : q → p ⊕ q

-- data existsp (A : Set) (p : A → Prop) : Prop where
--   ⟪_,_⟫ : ∀ a → p a → existsp A p

-- infix 2 ∃'-syntax
-- ∃'-syntax : ∀ (A : Set) → (A → Prop) → Prop
-- ∃'-syntax = existsp
-- syntax ∃'-syntax A (λ x → B) = ∃'[ x ∈ A ] B

Bool2Prop : Bool → Prop
Bool2Prop true = 𝟙
Bool2Prop false = 𝟘


neg-Prop : {X : Set} → ¬ X → (X → 𝟘)
neg-Prop {X} h x with h x
... | ()

⊤-hprop : ishProp ⊤
⊤-hprop = λ p₁ p₂ → erefl

mapSquash : ∀ {l} {A B : Set l} (f : A → B) → Squash A → Squash B
mapSquash f ⟦ a ⟧' = ⟦ f a ⟧'

SquashBox : ∀ {P} → Squash (Box P) → P
SquashBox ⟦ ⟦ p ⟧ ⟧' = p

toSquashBox : ∀ {P : Prop} → P → Squash (Box P)
toSquashBox p = ⟦ ⟦ p ⟧ ⟧'

unbox : ∀ {P} → Box P → P
unbox ⟦ p ⟧ = p

absurdProp : ∀ {l} {P : Prop l} → 𝟘 → P
absurdProp ()

⊥-elimProp : ∀ {l} {P : Prop l} → Empty → P
⊥-elimProp ()

Empty-hprop : ishProp Empty
Empty-hprop ()

subst-const : ∀ {l} {X : Set} {A : Set l} {x y : X} (h : x ≡ y) {a : A} → PE.subst (λ _ → A) h a ≡ a
subst-const erefl = erefl

Box-hprop : {P : Prop} → ishProp (Box P)
Box-hprop ⟦ p ⟧ ⟦ p₁ ⟧ = erefl

hProp-inhabited : {X : Set} (X-hProp : ishProp X) (x : X) → X ≡ ⊤
hProp-inhabited X-hProp x = hpropext X-hProp ⊤-hprop (λ _ → tt) (λ _ → x)


decEq-refl : {A : Set} (decA : DecidableEquality A) {a a' : A} (eq : a ≡ a') →
  decA a a' ≡ yes eq
decEq-refl decA {a} {a'} eq with decA a a'
decEq-refl decA eq | yes eq' rewrite hedberg decA eq eq' = erefl
decEq-refl decA eq | no h = ⊥-elim (h eq)

decEq-neq : {A : Set} (decA : DecidableEquality A) (c c' : A) (h : ¬ c ≡ c') → decA c' c ≡ no (h ∘ PE.sym)
decEq-neq decA c c' h with decA c' c
... | yes eq = ⊥-elim (h (PE.sym eq))
... | no h' = PE.cong no (funext {f = h'} {h ∘ PE.sym} (λ _ → Empty-hprop _ _))

Squash-absurd : ∀ {l} {P : Set l} → Squash P -> ¬ P → 𝟘
Squash-absurd ⟦ p ⟧' h with h p
... | ()

Squash-dec : ∀ {l l'} {A : Set l} {P : A → Set l'} → RU.Decidable P → {a : A} → Squash (P a) → P a
Squash-dec decP {a} pf with decP a
... | yes p = p
... | no h = absurd (Squash-absurd pf h)

Squash-decidable : ∀ {l l'} {A : Set l} {R : Rel A l'} (decR : RB.Decidable R) {a a' : A} → Squash (R a a') → R a a'
Squash-decidable decR {a} h = Squash-dec (decR a) h

record Subset {l l'} (A : Set l) (P : A → Prop l') : Set (l ⊔ l') where
  constructor ⟪_,_⟫
  field
    sfst : A
    ssnd : P sfst

open Subset public

Subset-type : ∀ {l l'} (A : Set l) (P : A → Prop l') → Set (l ⊔ l')
Subset-type A P = Subset A P

syntax Subset-type A (λ a → P) = Sub[ a ∈ A ] P

subset-ext : ∀ {l l'} {A : Set l} {P : A → Prop l'} (p q : Subset A P) → p .sfst ≡ q .sfst → p ≡ q
subset-ext ⟪ p , _ ⟫ ⟪ q , _ ⟫ erefl = erefl

≺_ : Nat → Set
≺ i = Sub[ j ∈ Nat ] Squash (j < i)

from-< : {i j : Nat} (pf : i < j) → ≺ j
from-< {i} pf = ⟪ i , ⟦ pf ⟧' ⟫

open import Data.Nat using (_≟_;_<?_;_≤?_;_≤_)
open import Data.Nat.Properties using (<-transˡ)

coe-≺ : {i j : Nat} (x : ≺ i) (hij : i Data.Nat.Base.≤ j) → ≺ j
coe-≺ {i} {j} x hij with x .sfst <? j
... | yes pf = from-< pf
... | no h = absurd (Squash-absurd (x .ssnd) (λ xi → h (<-transˡ xi hij)))



-- A positive sum type
data Sum (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (a : A) (b : B a) → Sum A B
