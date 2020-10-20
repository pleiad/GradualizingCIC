{-# OPTIONS --without-K --prop --rewriting #-}

open import prelude

open import nat
open import bool
open import top
open import Unknown.Core

open import GroundTypes


module DiscreteModelPartial where

private
  variable
    i : Nat

data U : Nat → Set
El : U i → Set


ℂtoU : ℂ i → U i

Elℂ : ℂ i → Set
Elℂ c = El (ℂtoU c)

U-hSet : hSet (U i)
El-hSet : (A : U i) → hSet (El A)

is✠U : U i → Prop
is✠U-eq : {A B : U i} → is✠U A → is✠U B → A ≡ B

is✠El : (A : U i) → El A → Prop
is✠El-eq : (A : U i) (x y : El A) (hx : is✠El A x) (hy : is✠El A y) → x ≡ y


pfpℂ : Nat → pointedFamilyPack
pfpℂ i = record
  { fp = record
    { A = ℂ i
    ; B = Elℂ
    ; decA = _≟ℂ_
    ; hSetB = El-hSet ∘ ℂtoU }
  ; is✠ = λ c → is✠El (ℂtoU c)
  ; is✠-eq = λ c → is✠El-eq (ℂtoU c) }

module Unk i = UnknownType (pfpℂ i)


{-# NO_POSITIVITY_CHECK #-}
data U where
  nat : U i
  bool : U i
  ?U : U i
  ✠U : U i
  π : (A : U i) → (B : El A → U i) → U i
  u : (j : ≺ i) → U i

{-# TERMINATING #-}
El nat = ℕ
El bool = 𝔹
El {i = i} ?U = Unk.unknown i
El ✠U = ⊤
El (π A B) = (a : El A) → El (B a)
El (u j) = U (j .sfst)

ℂtoU ℂnat = nat
ℂtoU ℂbool = bool
ℂtoU ℂπ = π ?U (λ _ → ?U)
ℂtoU (ℂ𝕦 {j = j} {j<i}) = u ⟪ j , j<i ⟫

is✠U ✠U = 𝟙
is✠U _ = 𝟘

is✠U-eq {A = ✠U} {✠U} hA hB = erefl

import Poset
open Poset.Initial

is✠El nat =  ✠ℕ' .is-bot
is✠El bool = ✠𝔹' .is-bot
is✠El {i = i} ?U = Unk.is✠u i
is✠El ✠U x = 𝟙
is✠El (π A B) f = (a : El A) → is✠El (B a) (f a)
is✠El (u j) = is✠U

private
  h : {A : Set} {x y z : A} → x ≡ y → z ≡ y → x ≡ z
  h xy zy = PE.trans xy (PE.sym zy)

is✠El-eq nat x y hx hy = h (✠ℕ' .is-bot-spec hx) (✠ℕ' .is-bot-spec hy)
is✠El-eq bool x y hx hy = h (✠𝔹' .is-bot-spec hx) (✠𝔹' .is-bot-spec hy)
is✠El-eq {i = i} ?U x y hx hy = h (Unk.is✠u-eq i x hx) (Unk.is✠u-eq i y hy)
is✠El-eq ✠U tt tt hx hy = erefl
is✠El-eq (π A B) x y hx hy =
  funext (λ a → is✠El-eq (B a) (x a) (y a) (hx a) (hy a))
is✠El-eq (u j) x y hx hy = is✠U-eq hx hy



-- Proving That U is an hSet...



-- TODO : these definitions should be reworked to be private
isπ : U i → Set
isπ (π _ _) = ⊤
isπ _ = Empty

eqΣ : ∀ (A A' : U i) (B : El A → U i) (B' : El A' → U i) → Set
eqΣ {i} A A' B B' = Σ[ h ∈ A ≡ A' ] PE.subst (λ X → El X → U i) h B ≡ B'

πeqΣ : ∀ {A A' B B'} → π {i} A B ≡ π A' B' → eqΣ A A' B B'
πeqΣ erefl = erefl , erefl

πeqΣinv : ∀ {A A' B B'} → eqΣ {i} A A' B B' → π A B ≡ π A' B'
πeqΣinv ( erefl , erefl ) = erefl

πeqΣ-id : ∀ {A A' B B'} (h : π {i} A B ≡ π A' B') → h ≡ πeqΣinv (πeqΣ h)
πeqΣ-id erefl = erefl

πeqΣ-inj : ∀ {A A' B B'} (h h' : π {i} A B ≡ π A' B') → πeqΣ h ≡ πeqΣ h' → h ≡ h'
πeqΣ-inj h h' hh' = PE.trans (πeqΣ-id h) (PE.trans (PE.cong πeqΣinv hh') (PE.sym (πeqΣ-id h')))

A→U-hSet : (A : U i) → hSet (El A → U i)
A→U-hSet {i} A =  ∀-hSet (λ _ → U-hSet)

open import Data.Nat using (_≟_)

U-hSet {_} {nat} {B} = local-hedberg nat aux
  where
    aux : RU.Decidable (_≡_ (nat {i}))
    aux nat = yes erefl
    aux bool = no λ()
    aux ?U = no λ()
    aux ✠U = no λ()
    aux (π c B) = no λ()
    aux (u _) = no λ()
U-hSet {_} {bool} {B} = local-hedberg bool aux
  where
    aux : RU.Decidable (_≡_ (bool {i}))
    aux bool = yes erefl
    aux nat = no λ()
    aux ?U = no λ()
    aux ✠U = no λ()
    aux (π c B) = no λ()
    aux (u _) = no λ()
U-hSet {_} {?U} {B} = local-hedberg ?U aux
  where
    aux : RU.Decidable (_≡_ (?U {i}))
    aux ?U = yes erefl
    aux nat = no λ()
    aux bool = no λ()
    aux ✠U = no λ()
    aux (π c B) = no λ()
    aux (u _) = no λ()
U-hSet {_} {✠U} {B} = local-hedberg ✠U aux
  where
    aux : RU.Decidable (_≡_ (✠U {i}))
    aux ✠U = yes erefl
    aux nat = no λ()
    aux bool = no λ()
    aux ?U = no λ()
    aux (π c B) = no λ()
    aux (u _) = no λ()
U-hSet {i} {π A B} {π A' B'} h h' with πeqΣ h with PE.inspect πeqΣ h with πeqΣ h' with PE.inspect πeqΣ h'
... | (h₁ , h₂) | PE.[ eqh ] | (h'₁ , h'₂) | PE.[ eqh' ] rewrite U-hSet h₁ h'₁ rewrite A→U-hSet A' h₂ h'₂ =
  πeqΣ-inj h h' (PE.trans eqh (PE.sym eqh'))
U-hSet {_} {π A B₁} {nat} eq = ⊥-elim (PE.subst isπ eq tt)
U-hSet {_} {π A B₁} {bool} eq = ⊥-elim (PE.subst isπ eq tt)
U-hSet {_} {π A B₁} {?U} eq = ⊥-elim (PE.subst isπ eq tt)
U-hSet {_} {π A B₁} {✠U} eq = ⊥-elim (PE.subst isπ eq tt)
U-hSet {_} {π A B₁} {u _} eq = ⊥-elim (PE.subst isπ eq tt)
U-hSet {_} {X@(u j)} {B} = local-hedberg X aux
  where
    aux : RU.Decidable (_≡_ X)
    aux Y@(u j') with j .sfst ≟ j' .sfst
    ... | yes erefl = yes erefl
    ... | no h = no (h ∘ aux')
      where
        aux' : X ≡ Y → j .sfst ≡ j' .sfst
        aux' erefl = erefl
    aux nat = no λ()
    aux bool = no λ()
    aux ✠U = no λ()
    aux (π c B) = no λ()
    aux ?U = no λ()



El-hSet nat = hedberg (decℕ)
El-hSet bool = hedberg (dec𝔹)
El-hSet {i} ?U = Unk.unknown-hSet i
El-hSet ✠U = hedberg dec⊤
  where
    dec⊤ : DecidableEquality ⊤
    dec⊤ tt tt = yes erefl
El-hSet {i} (π A B) = ∀-hSet (λ a → El-hSet (B a))
El-hSet (u _) = U-hSet






fail : (A : U i) → El A
fail nat = ✠ℕ
fail bool = ✠𝔹
fail {i = i} ?U = Unk.✠u i
fail ✠U = tt
fail (π A B) = λ a → fail (B a)
fail (u j) = ✠U

fail-is✠ : (A : U i) → is✠El A (fail A)
fail-is✠ nat = ⟨⟩
fail-is✠ bool = ⟨⟩
fail-is✠ {i} ?U = Unk.is✠✠u i
fail-is✠ ✠U = ⟨⟩
fail-is✠ (π A B) = λ a → fail-is✠ (B a)
fail-is✠ (u j) = ⟨⟩

?El : (A : U i) → El A
?El nat = ?ℕ
?El bool = ?𝔹
?El ?U = Unk.?u _
?El ✠U = tt
?El (π A B) = λ a → ?El (B a)
?El (u j) = ?U

ℂu : (j : ≺ i) → ℂ i
ℂu {i} j = ℂ𝕦 {i} {j .sfst} {j .ssnd}

-- suprising failure of termination on the 2nd case...
-- anyway not supposed to be terminating
{-# TERMINATING #-}
cast : (A B : U i) → El A → El B
cast-fail : (A B : U i) (a : El A) (ha : is✠El A a) → is✠El B (cast A B a)



cast nat nat Zℕ = Zℕ
cast {i} nat nat (Sℕ n) = Sℕ (cast {i} nat nat n)
cast nat nat ?ℕ = ?ℕ
cast nat nat ✠ℕ = ✠ℕ
cast {i} nat ?U n = Unk.uinj i ℂnat n
cast nat B n = fail B

cast bool bool true𝔹 = true𝔹
cast bool bool false𝔹 = false𝔹
cast bool bool ?𝔹 = ?𝔹
cast bool bool ✠𝔹 = ✠𝔹
cast {i} bool ?U b = Unk.uinj i ℂbool b
cast bool B b = fail B

cast ✠U B _ = fail B


-- Many debatable things here:
-- 1] we only consider same universe level cast
--    (but this mimics the monotone model)
-- 2] we do not destruct/reconstruct the types by induction
--    (contrarily to inductive types)
cast (u j) (u j') X with j .sfst ≟ j' .sfst
... | yes erefl = X
... | no _ = fail (u j')
cast {i} (u j) ?U X = Unk.uinj i (ℂu j) X
cast (u j) B X = fail B

cast (π Adom Acod) (π Bdom Bcod) f =
  λ b → let a = cast Bdom Adom b in cast (Acod a) (Bcod b) (f a)
cast {i} A@(π Adom Acod) ?U f = Unk.uinj i ℂπ (cast A (ℂtoU ℂπ) f)
cast (π Adom Acod) B f = fail B

cast {i} ?U B = Unk./rec i (El B) (λ where
  (inj c x) → cast (ℂtoU c) B x
  ?Σ → ?El B
  ✠Σ → fail B)
  λ c x hx → is✠El-eq B (cast (ℂtoU c) B x)
                        (fail B)
                        (cast-fail (ℂtoU c) B x hx)
                        (fail-is✠ B)


import Unknown.Quotient

cast-fail nat nat ✠ℕ ha = ha
cast-fail {i} nat ?U a ha = Unk.is✠u-uinj i ℂnat a ha
cast-fail nat B@bool a ha = fail-is✠ B
cast-fail nat B@✠U a ha = fail-is✠ B
cast-fail nat B@(π _ _) a ha = fail-is✠ B
cast-fail nat B@(u j) a ha = fail-is✠ B

cast-fail bool bool ✠𝔹 ha = ha
cast-fail {i} bool ?U a ha = Unk.is✠u-uinj i ℂbool a ha
cast-fail bool B@nat a ha = fail-is✠ B
cast-fail bool B@✠U a ha = fail-is✠ B
cast-fail bool B@(π _ _) a ha = fail-is✠ B
cast-fail bool B@(u j) a ha = fail-is✠ B

cast-fail {i} ?U B a ha = unbox (Unk./elim _ P aux aux-quot a ⟦ ha ⟧)
  where
    open Unk i
    P = λ a → Box (Unk.is✠u _ a) → Box (is✠El B (cast ?U B a))
    aux : ∀ a → P ⦅ a ⦆
    aux (inj a x) hx = ⟦ cast-fail (ℂtoU a) B x (SquashBox (unbox hx)) ⟧
    aux ?Σ ha = absurd (SquashBox (unbox ha))
    aux ✠Σ ha = ⟦ fail-is✠ B ⟧

    aux-quot : quot-elim P aux
    aux-quot a₁ x hx = funext (λ x₁ → Box-hprop _ _)

cast-fail ✠U B a ha = fail-is✠ B

cast-fail A@(π Adom Acod) B@(π Bdom Bcod) f hf =
  λ b → let a = cast Bdom Adom b in
    cast-fail (Acod a) (Bcod b) (f a) (hf a)
cast-fail {i} A@(π Adom Acod) B@?U f hf =
  Unk.is✠u-uinj i ℂπ (cast A (ℂtoU ℂπ) f) (cast-fail A (ℂtoU ℂπ) f hf)
cast-fail A@(π Adom Acod) B@nat a ha = fail-is✠ B
cast-fail A@(π Adom Acod) B@bool a ha = fail-is✠ B
cast-fail A@(π Adom Acod) B@✠U a ha = fail-is✠ B
cast-fail A@(π Adom Acod) B@(u j) a ha = fail-is✠ B

cast-fail (u j) B@(u j') a ha with j .sfst ≟ j' .sfst
... | yes erefl = ha
... | no _ = fail-is✠ B
cast-fail (u j) ?U a ha = Unk.is✠u-uinj _ (ℂu j) a ha
cast-fail (u j) B@nat a ha = fail-is✠ B
cast-fail (u j) B@bool a ha = fail-is✠ B
cast-fail (u j) B@✠U a ha = fail-is✠ B
cast-fail (u j) B@(π _ _) a ha = fail-is✠ B
