{-# OPTIONS --without-K --prop #-}

open import prelude
open import Data.Nat using (_<?_)

module FiniteOrdinal where

-- W types specialized to A = Nat, B = n ↦ { k < n }
data PNat : Set where
  P : (n : Nat) (lower : ≺ n → PNat) → PNat

toNat : PNat → Nat
toNat (P i _) = i

to-lower : (n : PNat) → ≺ toNat n → PNat
to-lower (P i ≺i) = ≺i


-- Carving out those trees corresponding to natural numbers
-- (a.k.a finite ordinals)
data Wf : PNat → Nat → Set where
  PWf : (n : Nat)
        (lower : ≺ n → PNat)
        (wf-lower : (k : ≺ n) → Wf (lower k) (k .sfst)) →
        Wf (P n lower) n

WfPNat : PNat → Set
WfPNat n = Wf n (toNat n)

wf-toNat : (i : Nat) (𝕚 : PNat) (wfi : Wf 𝕚 i) → toNat 𝕚 ≡ i
wf-toNat i .(P i lower) (PWf .i lower wf-lower) = erefl

to-lower-wf-aux : (i : Nat) (𝕚 : PNat) (wfi : Wf 𝕚 i) (k : ≺ toNat 𝕚) → WfPNat (to-lower 𝕚 k)
to-lower-wf-aux i .(P i lower) (PWf .i lower wf-lower) k rewrite wf-toNat (k .sfst) (lower k) (wf-lower k) = wf-lower k

to-lower-wf : (i : PNat) (wf : WfPNat i) (k : ≺ toNat i) → WfPNat (to-lower i k)
to-lower-wf i wf = to-lower-wf-aux (toNat i) i wf

wf-toNat-to-lower-aux : (i : Nat) (𝕚 : PNat) (wfi : Wf 𝕚 i) (p : ≺ toNat 𝕚) → toNat (to-lower 𝕚 p) ≡ p .sfst
wf-toNat-to-lower-aux i .(P i lower) (PWf .i lower wf-lower) p = wf-toNat (p .sfst) (lower p) (wf-lower p)

wf-toNat-to-lower : (𝕚 : PNat) (wfi : WfPNat 𝕚) (p : ≺ toNat 𝕚) → toNat (to-lower 𝕚 p) ≡ p .sfst
wf-toNat-to-lower i wfi p = wf-toNat-to-lower-aux (toNat i) i wfi p


-- The only part of the bijection between natural numbers and finite ordinals that we actually need
Wf-ext : (i j : Nat) (𝕚 𝕛 : PNat) (hi : Wf 𝕚 i) (hj : Wf 𝕛 j) → i ≡ j → 𝕚 ≡ 𝕛
Wf-ext i .i .(P i ≺i) .(P i ≺j) (PWf .i ≺i wfi) (PWf .i ≺j wfj) erefl = PE.cong (P i) helper
  where
    helper : ≺i ≡ ≺j
    helper = funext λ x → Wf-ext (x .sfst) (x .sfst) (≺i x) (≺j x) (wfi x) (wfj x) erefl

to-lower-ext : (i j : PNat) (wfi : WfPNat i) (wfj : WfPNat j)
               (p : ≺ toNat i) (q : ≺ toNat j) (epq : p .sfst ≡ q .sfst)
               → to-lower i p ≡ to-lower j q
to-lower-ext i j wfi wfj p q epq with to-lower-wf i wfi p with to-lower-wf j wfj q
... | wfp | wfq
    rewrite wf-toNat-to-lower i wfi p
    rewrite wf-toNat-to-lower j wfj q =
      Wf-ext (p .sfst) (q .sfst) (to-lower i p) (to-lower j q) wfp wfq epq


sucP : PNat → PNat
sucP (P i ≺i) = P (suc i) aux
  where
    aux : ≺ suc i → PNat
    aux k with k .sfst <? i
    ... | yes pf = ≺i (from-< pf)
    ... | no _ = P i ≺i

fromNat : (n : Nat) → PNat
fromNat 0 = P 0 (λ k → absurd (Squash-absurd (k .ssnd) λ()))
fromNat (suc n) = sucP (fromNat n)

precPNat : (n : Nat) (hn : Squash (0 < n)) → PNat
precPNat 0 hn = absurd (Squash-absurd hn λ())
precPNat (suc n) hn = fromNat n
