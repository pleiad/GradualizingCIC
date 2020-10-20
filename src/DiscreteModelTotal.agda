{-# OPTIONS --without-K --prop #-}

open import prelude

open import FiniteOrdinal

open import nat
open import top

open import Data.Nat using (_≟_;_<?_;_≤?_;_≤_)
open import Data.Nat.Properties using (<-transˡ)

module DiscreteModelTotal where



-- Inductive part of the definition of the universe
-- Proceeds by strong induction on natural numbers
module Univ (n : Nat)
            (U : (k : ≺ n) → Set)
            (El : {k : ≺ n} (A : U k) → Set)
            (Unk : (k : ≺ n) → U k)
            where

  data ℍ : Set where
    𝕙σ : ℍ
    𝕙π : (i j : ≺ n) → ℍ
    𝕙u : ≺ n → ℍ
    𝕙nat : ℍ

  Elℍ : ℍ → Set

  -- sadly the modular version does not work...
  -- open import Unknown.Core using (Σ⁺ ; inj ; ✠Σ ; ?Σ)
  -- Unkₛ : Set
  -- Unkₛ = Σ⁺ ℍ Elℍ

  -- but at least it goes through after inlining
  data Unkₛ : Set where
    inj-unk : (h : ℍ) (x : Elℍ h) → Unkₛ
    ?unk : Unkₛ
    ✠unk : Unkₛ

  Elℍ 𝕙σ = Sum Unkₛ λ _ → Unkₛ
  Elℍ (𝕙π i j) = El (Unk i) → El (Unk j)
  Elℍ (𝕙u j) = U j
  Elℍ 𝕙nat = ℕ

  data Uₛ : Set
  Elₛ : Uₛ → Set

  data Uₛ where
    Uₛσ : (A : Uₛ) (B : Elₛ A → Uₛ) → Uₛ
    Uₛπ : {i j : ≺ n} (A : U i) (B : El A → U j) → Uₛ
    Uₛ? : Uₛ
    Uₛu : (j : ≺ n) → Uₛ
    Uₛ✠ : Uₛ
    Uₛnat : Uₛ

  Elₛ (Uₛσ A B) = Sum (Elₛ A) (λ a → Elₛ (B a))
  Elₛ Uₛ? = Unkₛ
  Elₛ Uₛnat = ℕ
  Elₛ (Uₛπ A B) = (a : El A) → El (B a)
  Elₛ (Uₛu j) = U j
  Elₛ Uₛ✠ = ⊤

  -- experiments to prove termination of cast
  -- term : Set
  -- term = Σ[ A ∈ Uₛ ] Elₛ A

  -- data subterm : Rel term lzero where
  --   subt-σ₁ : {A : Uₛ} (B : Elₛ A → Uₛ) (a : Elₛ A) (b : Elₛ (B a)) → subterm (A , a) (Uₛσ A B , ⟨ a , b ⟩)
  --   subt-σ₂ : {A : Uₛ} (B : Elₛ A → Uₛ) (a : Elₛ A) (b : Elₛ (B a)) → subterm (B a , b) (Uₛσ A B , ⟨ a , b ⟩)
  --   subt-nat : (n : ℕ) → subterm (Uₛnat , n) (Uₛnat , Sℕ n)
  --   subt-?-σ : (x : Sum Unkₛ (λ _ → Unkₛ)) → subterm (Uₛσ Uₛ? (λ _ → Uₛ?) , x) (Uₛ? , 𝕙σ x)
  --   subt-?-π : {j : ≺ n} (f : (El (Unk j) → El (Unk j))) → subterm (Uₛπ {j} (Unk j) (λ _ → Unk j) , f) (Uₛ? , 𝕙π f)
  --   subt-?-U : {j : ≺ n} (A : U j) → subterm (Uₛu j , A) (Uₛ? , 𝕙U j A)
  --   subt-?-nat : (n : ℕ) → subterm (Uₛnat , n) (Uₛ? , 𝕙nat n)

  -- data ut : Set where
  --   ut-const : ut
  --   ut-un : ut → ut
  --   ut-bin : ut → ut → ut

  -- encode : (A : Uₛ) (t : Elₛ A) → ut
  -- encode-? : Unkₛ → ut
  -- encode-nat : ℕ → ut

  -- encode (Uₛσ A B) ⟨ a , b ⟩ = ut-bin (encode A a) (encode (B a) b)
  -- encode (Uₛπ A B) t = ut-const
  -- encode Uₛ? x = encode-? x
  -- encode (Uₛu j) t = ut-const
  -- encode Uₛ✠ t = ut-const
  -- encode Uₛnat t = encode-nat t

  -- encode-? (𝕙σ ⟨ a , b ⟩) = ut-bin (encode-? a) (encode-? b)
  -- encode-? (𝕙π x) = ut-un ut-const
  -- encode-? (𝕙U j x) = ut-un ut-const
  -- encode-? ?unk = ut-const
  -- encode-? ✠unk = ut-const
  -- encode-? (𝕙nat x) = encode-nat x

  -- encode-nat (Sℕ t) = ut-un (encode-nat t)
  -- encode-nat c = ut-const

  -- data ut : Set where
  --   ut-σ-pair : ut → ut → ut
  --   ut-?-σ : ut → ut
  --   ut-?-π : {j : ≺ n} (f : El (Unk j) → El (Unk j)) → ut
  --   ut-?-U : {j : ≺ n} (A : U j) → ut
  --   ut-?-nat : ut → ut
  --   ut-nat-suc : ut → ut
  --   ut-nat-const : ut


--   module subterm-wf where
--     open import Induction.WellFounded

--     subterm-wf-aux : (A : Uₛ) (a : Elₛ A) → Acc subterm (A , a)
--     subterm-wf-aux (Uₛσ A B) a = acc (λ { .(A , a) (subt-σ₁ .B a b) → subterm-wf-aux A a ; .(B a , b) (subt-σ₂ .B a b) → subterm-wf-aux (B a) b })
--     subterm-wf-aux (Uₛπ A B) a = acc (λ { y ()})
--     subterm-wf-aux Uₛ? a = acc (λ {
--       .(Uₛσ Uₛ? (λ _ → Uₛ?) , x) (subt-?-σ x) → acc (λ {
--             .(Uₛ? , a) (subt-σ₁ .(λ _ → Uₛ?) a b) → {!subterm-wf-aux Uₛ? a!} ;
--             .(Uₛ? , b) (subt-σ₂ .(λ _ → Uₛ?) a b) → {!subterm-wf-aux Uₛ? b!} }) ;
--       .(Uₛπ (Unk _) (λ _ → Unk _) , f) (subt-?-π f) → acc (λ { y ()}) ;
--       .(Uₛu _ , A) (subt-?-U A) → subterm-wf-aux (Uₛu _) A ;
--       .(Uₛnat , n) (subt-?-nat n) → subterm-wf-aux Uₛnat n})
--     subterm-wf-aux (Uₛu j) a = {!!}
--     subterm-wf-aux Uₛ✠ a = {!!}
--     subterm-wf-aux Uₛnat a = {!!}

--     subterm-wf : WellFounded subterm
--     subterm-wf (A , a) = subterm-wf-aux A a

U : PNat → Set
El : {n : PNat} (A : U n) → Set
Unk : (n : PNat) → U n

U (P n lower) = Univ.Uₛ n (λ i → U (lower i)) (\ {k} → El {lower k}) (λ i → Unk (lower i))
El {P n lower} = Univ.Elₛ n (λ i → U (lower i)) (\ {k} → El {lower k}) (λ i -> Unk (lower i))
Unk (P n lower) = Univ.Uₛ?

ℍ : PNat → Set
ℍ (P n lower) = Univ.ℍ n (U ∘ lower) (\ {k} → El {lower k}) (Unk ∘ lower)

open Univ hiding (ℍ)

fail : {i : Nat} {lower : ≺ i → PNat} (A : U (P i lower)) → El A
fail (Uₛσ A B) = let a = fail A in ⟨ a , fail (B a) ⟩
fail {i} {lower} (Uₛπ {_} {j} A B) with lower j
... | P k ≺k  = λ a → fail (B a)
fail Uₛ? = ✠unk
fail {i} {lower} (Uₛu j) with lower j
... | P k ≺k = Uₛ✠
fail Uₛ✠ = tt
fail Uₛnat = ✠ℕ

?U : (i : Nat) (≺i : ≺ i → PNat) (A : U (P i ≺i)) → El A
?U i ≺i (Uₛσ A B) = let a = ?U i ≺i A in ⟨ a , ?U i ≺i (B a) ⟩
?U i ≺i (Uₛπ {_} {j} A B) with ≺i j
... | P k ≺k = λ a → ?U k ≺k (B a)
?U i ≺i Uₛ? = ?unk
?U i ≺i (Uₛu j) with ≺i j
... | P k ≺k = Uₛ?
?U i ≺i Uₛ✠ = tt
?U i ≺i Uₛnat = ?ℕ


germ : (i : PNat) → ℍ i → U i
germ k@(P n lower) 𝕙σ = Uₛσ (Unk k) (λ _ → Unk k)
germ k@(P n lower) (𝕙π i j) =
  Uₛπ {i = i} {j = j} (Unk (lower i)) (λ _ → Unk (lower j))
germ k@(P n lower) (𝕙u i) = Uₛu i
germ k@(P n lower) 𝕙nat = Uₛnat

coe-ℍ : (i j : PNat) (hij : toNat i ≤ toNat j) → ℍ i → ℍ j
coe-ℍ (P i ≺i) (P j ≺j) hij 𝕙σ = 𝕙σ
coe-ℍ (P i ≺i) (P j ≺j) hij (𝕙π k l) = 𝕙π (coe-≺ k hij) (coe-≺ l hij)
coe-ℍ (P i ≺i) (P j ≺j) hij (𝕙u k) = 𝕙u (coe-≺ k hij)
coe-ℍ (P i ≺i) (P j ≺j) hij 𝕙nat = 𝕙nat


cast : (i j : Nat) (≺i : ≺ i → PNat) (≺j : ≺ j → PNat)
       (hi : Wf (P i ≺i) i) (hj : Wf (P j ≺j) j)
       (A : U (P i ≺i)) (B : U (P j ≺j)) → El A → El B

cast-from-univ : (i j : Nat) (≺i : ≺ i → PNat) (≺j : ≺ j → PNat)
                 (hi : Wf (P i ≺i) i) (hj : Wf (P j ≺j) j)
                 (k : ≺ i) (B : U (P j ≺j)) → U (≺i k) → El B

cast-from-pi : (i j : Nat) (≺i : ≺ i → PNat) (≺j : ≺ j → PNat)
               (hi : Wf (P i ≺i) i) (hj : Wf (P j ≺j) j)
               (k : ≺ i) (l : ≺ i)
               (Adom : U (≺i k)) (Acod : El Adom → U (≺i l))
               (B : U (P j ≺j)) →
               ((a : El Adom) → El (Acod a)) → El B

cast-from-σ : (i j : Nat) (≺i : ≺ i → PNat) (≺j : ≺ j → PNat)
              (hi : Wf (P i ≺i) i) (hj : Wf (P j ≺j) j)
              (Adom : U (P i ≺i)) (Acod : El Adom → U (P i ≺i)) (B : U (P j ≺j)) →
              Sum (El Adom) (λ a → El (Acod a)) → El B

cast-from-nat : (i j : Nat) (≺i : ≺ i → PNat) (≺j : ≺ j → PNat)
                (hi : Wf (P i ≺i) i) (hj : Wf (P j ≺j) j)
                (B : U (P j ≺j)) → ℕ → El B

cast i j ≺i ≺j hi hj Uₛnat B a =
  cast-from-nat i j ≺i ≺j hi hj B a
cast i j ≺i ≺j hi hj (Uₛσ Adom Acod) B a =
  cast-from-σ i j ≺i ≺j hi hj Adom Acod B a
cast i j ≺i ≺j hi hj (Uₛu p) B a =
  cast-from-univ i j ≺i ≺j hi hj p B a
cast i j ≺i ≺j hi hj (Uₛπ {p} {q} Adom Acod) B f =
  cast-from-pi i j ≺i ≺j hi hj p q Adom Acod B f

cast i j ≺i ≺j hi hj Uₛ✠ B a = fail B

-- morally cast ... Uₛ? B (inj-unk h x) = cast ... (germ h) B x
-- split apart for termination
cast i j ≺i ≺j hi hj Uₛ? B (inj-unk 𝕙σ x) =
  cast-from-σ i j ≺i ≺j hi hj Uₛ? (λ _ → Uₛ?) B x
cast i j ≺i ≺j hi hj Uₛ? B (inj-unk (𝕙π k l) f) =
  cast-from-pi i j ≺i ≺j hi hj k l (Unk (≺i k)) (λ _ → Unk (≺i l)) B f
cast i j ≺i ≺j hi hj Uₛ? B (inj-unk (𝕙u k) a) =
  cast-from-univ i j ≺i ≺j hi hj k B a
cast i j ≺i ≺j hi hj Uₛ? B (inj-unk 𝕙nat n) =
  cast-from-nat i j ≺i ≺j hi hj B n
cast i j ≺i ≺j hi hj Uₛ? B ?unk = ?U j ≺j B
cast i j ≺i ≺j hi hj Uₛ? B ✠unk = fail B


cast-from-univ i j ≺i ≺j hi hj p (Uₛu q) a with p .sfst ≟ q .sfst
... | yes epq = PE.subst U (to-lower-ext (P i ≺i) (P j ≺j) hi hj p q epq) a
... | no _ = fail {j} {≺j} (Uₛu q)
cast-from-univ i j ≺i ≺j hi hj p Uₛ? a with p .sfst <? j
... | no _ = fail {j} {≺j} Uₛ?
... | yes pf =
  let 𝕚 = P i ≺i
      𝕛 = P j ≺j
      eq-on-p = to-lower-ext (P i ≺i) (P j ≺j) hi hj p (from-< pf) erefl
  in inj-unk (𝕙u (from-< pf)) (PE.subst U eq-on-p a)
cast-from-univ i j ≺i ≺j hi hj p B a = fail B


cast-from-pi i j ≺i ≺j hi hj pdom pcod Adom Acod
  (Uₛπ {qdom} {qcod} Bdom Bcod) f
  with ≺i pdom with PE.inspect ≺i pdom
  with ≺j qdom with PE.inspect ≺j qdom
  with ≺i pcod with PE.inspect ≺i pcod
  with ≺j qcod with PE.inspect ≺j qcod
... | P kdom ≺kdom | PE.[ ekdom ] | P ldom ≺ldom | PE.[ eldom ]
    | P kcod ≺kcod | PE.[ ekcod ] | P lcod ≺lcod | PE.[ elcod ] =
  λ b →
    let hkdom = PE.subst WfPNat ekdom (to-lower-wf (P i ≺i) hi pdom)
        hldom = PE.subst WfPNat eldom (to-lower-wf (P j ≺j) hj qdom)
        a = cast ldom kdom ≺ldom ≺kdom hldom hkdom Bdom Adom b
        hkcod = PE.subst WfPNat ekcod (to-lower-wf (P i ≺i) hi pcod)
        hlcod = PE.subst WfPNat elcod (to-lower-wf (P j ≺j) hj qcod)
    in  cast kcod lcod ≺kcod ≺lcod hkcod hlcod (Acod a) (Bcod b) (f a)
cast-from-pi i j ≺i ≺j hi hj k l Adom Acod Uₛ? f with i ≤? j
... | no _ = fail {j} {≺j} Uₛ?
... | yes pf =
  let A = Uₛπ Adom Acod
      h = coe-ℍ (P i ≺i) (P j ≺j) pf (𝕙π k l)
      tgt = germ (P j ≺j) h
  in inj-unk h (cast i j ≺i ≺j hi hj A tgt f)
cast-from-pi i j ≺i ≺j hi hj _ _ Adom Acod B a = fail B


cast-from-σ i j ≺i ≺j hi hj Adom Acod (Uₛσ Bdom Bcod) ⟨ a₁ , a₂ ⟩ =
  let bdom = cast i j ≺i ≺j hi hj Adom Bdom a₁
      bcod = cast i j ≺i ≺j hi hj (Acod a₁) (Bcod bdom) a₂
  in
  ⟨ bdom ,  bcod ⟩
-- interestingly the universe level check is not strictly needed
cast-from-σ i j ≺i ≺j hi hj Adom Acod B@Uₛ? a with i ≤? j
... | no _ = fail B
... | yes _ =
  inj-unk 𝕙σ (cast i j ≺i ≺j hi hj (Uₛσ Adom Acod) (germ (P j ≺j) 𝕙σ) a)
cast-from-σ i j ≺i ≺j hi hj Adom Acod B a = fail B


cast-from-nat i j ≺i ≺j hi hj Uₛnat Zℕ = Zℕ
cast-from-nat i j ≺i ≺j hi hj Uₛnat (Sℕ a) = Sℕ (cast-from-nat i j ≺i ≺j hi hj Uₛnat a)
cast-from-nat i j ≺i ≺j hi hj Uₛnat ?ℕ = ?ℕ
cast-from-nat i j ≺i ≺j hi hj Uₛnat ✠ℕ = ✠ℕ
-- interestingly the universe level check is not strictly needed
cast-from-nat i j ≺i ≺j hi hj B@Uₛ? a with i ≤? j
... | no _ = fail B
... | yes _ = inj-unk 𝕙nat a
cast-from-nat i j ≺i ≺j hi hj B a = fail B
