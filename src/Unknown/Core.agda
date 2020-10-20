{-# OPTIONS --without-K --prop --rewriting #-}
module Unknown.Core where

open import prelude
open PE hiding (_≡_)
import Unknown.Quotient
open import Unknown.Interface


data Σ⁺ {l l' : Level} (A : Set l) (B : A → Set l') : Set (l ⊔ l') where
  inj : ∀ a → B a → Σ⁺ A B
  ?Σ : Σ⁺ A B
  ✠Σ : Σ⁺ A B

module Σ⁺-hSet (fp : familyPack) where

  open familyPack fp

  private
    eqinj : (c c' : A) (x : B c) (x' : B c') → Set
    eqinj c c' x x' = Σ[ h ∈ c ≡ c' ] subst B h x ≡ x'

    inj-eqinj : {c c' : A} {x : B c} {x' : B c'} → inj c x ≡ inj c' x' → eqinj c c' x x'
    inj-eqinj refl = refl , refl

    eqinj-inj : {c c' : A} {x : B c} {x' : B c'} → eqinj c c' x x' → inj c x ≡ inj c' x'
    eqinj-inj (refl , refl) = refl

    inj-eqinj-id : {c c' : A} {x : B c} {x' : B c'} (h : inj c x ≡ inj c' x') → h ≡ eqinj-inj (inj-eqinj h)
    inj-eqinj-id refl = refl

    eqinj-injective : {c c' : A} {x : B c} {x' : B c'} (h h' : inj c x ≡ inj c' x') → inj-eqinj h ≡ inj-eqinj h' → h ≡ h'
    eqinj-injective h h' hh' = trans (inj-eqinj-id h) (trans (cong eqinj-inj hh') (sym (inj-eqinj-id h')))

  Σ⁺-hSet : hSet (Σ⁺ A B)
  Σ⁺-hSet {inj c x} {inj c' x'} eq eq' with inj-eqinj eq with inspect inj-eqinj eq with inj-eqinj eq' with inspect inj-eqinj eq'
  ... | (h₁ , h₂) | [ eqh ] | (h'₁ , h'₂) | [ eqh' ] rewrite hedberg decA h₁ h'₁ rewrite hSetB c' h₂ h'₂ =
    eqinj-injective eq eq' (trans eqh (sym eqh'))
  Σ⁺-hSet {?Σ} {y} = local-hedberg ?Σ dec
    where
      dec : RU.Decidable (_≡_ (?Σ {A = A} {B = B}))
      dec (inj a x) = no λ()
      dec ?Σ = yes refl
      dec ✠Σ = no λ()
  Σ⁺-hSet {✠Σ} {y} = local-hedberg ✠Σ dec
    where
      dec : RU.Decidable (_≡_ (✠Σ {A = A} {B = B}))
      dec (inj a x) = no λ()
      dec ?Σ = no λ()
      dec ✠Σ = yes refl


record pointedFamilyPack : Set₁ where
  field
    fp : familyPack {lzero} {lzero}
  open familyPack fp public

  field
    is✠  : (a : A) → B a → Prop
    is✠-eq : (a : A) (b b' : B a) (hb : is✠ a b) (hb' : is✠ a b') → b ≡ b'


module UnknownType (pfp : pointedFamilyPack) where

  open pointedFamilyPack pfp

  private
    ✠Σ⁺ : Σ⁺ A B → Prop
    ✠Σ⁺ (inj a x) = is✠ a x
    ✠Σ⁺ ?Σ = 𝟘
    ✠Σ⁺ ✠Σ = 𝟙


    data ✠rel₀ : Σ⁺ A B → Σ⁺ A B → Set where
      ✠rel-refl : {x : Σ⁺ A B} → ✠rel₀ x x
      ✠rel-✠ : {x y : Σ⁺ A B} (xyneq : x ≡ y → 𝟘) (hx : ✠Σ⁺ x) (hy : ✠Σ⁺ y) → ✠rel₀ x y

    ΣhSet = Σ⁺-hSet.Σ⁺-hSet fp

    ✠rel₀-eq-elim : {x y : Σ⁺ A B} (h : x ≡ y) (xy : ✠rel₀ x y) → xy ≡ PE.subst (✠rel₀ x) h ✠rel-refl
    ✠rel₀-eq-elim h ✠rel-refl rewrite ΣhSet h refl = refl
    ✠rel₀-eq-elim h (✠rel-✠ xyneq hx hy) = absurd (xyneq h)

    ✠rel₀-irr : Irrelevant ✠rel₀
    ✠rel₀-irr ✠rel-refl h' = PE.sym (✠rel₀-eq-elim refl h')
    ✠rel₀-irr (✠rel-✠ xyneq hx hy) ✠rel-refl = absurd (xyneq refl)
    ✠rel₀-irr (✠rel-✠ xyneq hx hy) (✠rel-✠ xyneq₁ hx₁ hy₁) = refl

    open import Relation.Binary.Structures using (IsEquivalence)

    ✠rel₀-refl : Reflexive ✠rel₀
    ✠rel₀-refl = ✠rel-refl

    ✠rel₀-sym : Symmetric ✠rel₀
    ✠rel₀-sym xx@✠rel-refl = xx
    ✠rel₀-sym (✠rel-✠ xyneq hx hy) = ✠rel-✠ (λ h → xyneq (sym h)) hy hx

    dec-eq-✠Σ⁺ : (x y : Σ⁺ A B) (hx : ✠Σ⁺ x) (hy : ✠Σ⁺ y) → Dec (x ≡ y)
    dec-eq-✠Σ⁺ (inj a x) (inj a' x') hx hy with decA a a'
    ... | yes refl = yes (PE.cong (inj a) (is✠-eq a x x' hx hy))
    ... | no h = no λ { refl → h refl }
    dec-eq-✠Σ⁺ (inj a x) ✠Σ hx hy = no (λ())
    dec-eq-✠Σ⁺ ✠Σ (inj a x) hx hy = no (λ())
    dec-eq-✠Σ⁺ ✠Σ ✠Σ hx hy = yes refl

    ✠rel₀-trans : Transitive ✠rel₀
    ✠rel₀-trans ✠rel-refl yz = yz
    ✠rel₀-trans xy@(✠rel-✠ xyneq hx hy) ✠rel-refl = xy
    ✠rel₀-trans (✠rel-✠ {x} _ hx _) (✠rel-✠ {y = z} _ _ hz) with dec-eq-✠Σ⁺ x z hx hz
    ... | yes refl = ✠rel-refl
    ... | no h = ✠rel-✠ (neg-Prop h) hx hz

    ✠rel₀-equiv : IsEquivalence ✠rel₀
    ✠rel₀-equiv = record { refl = ✠rel₀-refl ; sym = ✠rel₀-sym ; trans = ✠rel₀-trans }


  ✠rel-helper : Rel (Σ⁺ A B) lzero
  ✠rel-helper (inj a x) ✠Σ = Box (is✠ a x)
  ✠rel-helper _ _ = Empty

  private
    to✠rel₀ : ✠rel-helper ⇒ ✠rel₀
    to✠rel₀ {inj a x} {✠Σ} hx = ✠rel-✠ (λ()) (unbox hx) ⟨⟩

    open import Relation.Binary.Construct.Closure.Equivalence as CCEq
    open import Relation.Binary.Construct.Closure.Symmetric as CCSym
    open import Relation.Binary.Construct.Closure.ReflexiveTransitive as CCRT

    ret : ∀ {l l'} {A : Set l} {R : Rel A l'} → R ⇒ EqClosure R
    ret xy = return (fwd xy)

    from✠rel₀ : ✠rel₀ ⇒ EqClosure ✠rel-helper
    from✠rel₀ ✠rel-refl = reflexive _
    from✠rel₀ {inj a x} {inj a₁ x₁} (✠rel-✠ xyneq hx hy) =
      transitive _ (ret ⟦ hx ⟧) (CCEq.symmetric _ (ret ⟦ hy ⟧))
    from✠rel₀ {inj a x} {✠Σ} (✠rel-✠ xyneq hx hy) = ret ⟦ hx ⟧
    from✠rel₀ {✠Σ} {inj a x} (✠rel-✠ xyneq hx hy) =
      CCEq.symmetric _ (ret ⟦ hy ⟧)
    from✠rel₀ {✠Σ} {✠Σ} (✠rel-✠ xyneq hx hy) = reflexive _

    module Q = Unknown.Quotient (Σ⁺ A B) ✠rel₀

  unknown : Set
  unknown = Q._/_

  ⦅_⦆ : Σ⁺ A B → unknown
  ⦅_⦆ = Q.⦅_⦆

  uinj : (a : A) → B a → unknown
  uinj a b = Q.⦅ inj a b ⦆

  ?u : unknown
  ?u = ⦅ ?Σ ⦆

  ✠u : unknown
  ✠u = ⦅ ✠Σ ⦆

  uinj✠ : (c : A) (x : B c) (h✠ : is✠ c x) → uinj c x ≡ ✠u
  uinj✠ c x h✠ = Q.quot (✠rel-✠ (λ()) h✠ ⟨⟩)

  unknown-hSet : hSet unknown
  unknown-hSet = Q.quot-hSet ΣhSet ✠rel₀-irr ✠rel₀-equiv

  quot-elim : ∀ {l} (P : unknown → Set l) (hΣ : ∀ a → P ⦅ a ⦆) → Set l
  quot-elim P hΣ = (a : A) (x : B a) (hx : is✠ a x) →
                    subst P (uinj✠ a x hx) (hΣ (inj a x)) ≡ hΣ ✠Σ

  module _ {l} (P : unknown → Set l)
                (hΣ : ∀ a → P ⦅ a ⦆)
                (hquot : quot-elim P hΣ)
                where
    private
      open Q.QuotSimpl unknown-hSet ✠rel₀-equiv ✠rel-helper to✠rel₀ from✠rel₀ P hΣ

      aux : ∀ {x x'} (h : ✠rel-helper x x') → Q./elim-eq-hyp P hΣ {x} {x'} (to✠rel₀ h)
      aux {inj a x} {✠Σ} h = hquot a x (unbox h)


    /elim : (u : unknown) → P u
    /elim = Q./elim P hΣ (qsimpl aux)

  module _ {l} (P : Set l) (hΣ : Σ⁺ A B → P) where

    quot-rec : Set l
    quot-rec = (a : A) (x : B a) (hx : is✠ a x) → hΣ (inj a x) ≡ hΣ ✠Σ

    /rec : (hquot : quot-rec) → unknown → P
    /rec hquot = /elim (λ _ → P) hΣ
      λ a x hx → trans (subst-const (uinj✠ a x hx)) (hquot a x hx)

  is✠u : (u : unknown) → Prop
  is✠u u = Squash (/rec Set (λ {
    (inj a x) → Box (is✠ a x) ;
    ?Σ → Box 𝟘 ;
    ✠Σ → Box 𝟙})
    (λ a x hx → hpropext Box-hprop Box-hprop (λ _ → ⟦ ⟨⟩ ⟧) (λ _ → ⟦ hx ⟧)) u)

  is✠✠u : is✠u ✠u
  is✠✠u = toSquashBox ⟨⟩

  is✠u-uinj : (a : A) (x : B a) (hx : is✠ a x) → is✠u (uinj a x)
  is✠u-uinj a x hx = toSquashBox hx

  private
    flip-subst-≡ : {A : Set} (P : A → Set) {a b : A} (x : P a) (y : P b) (eq : a ≡ b) → x ≡ subst P (sym eq) y → subst P eq x ≡ y
    flip-subst-≡ P x y refl = id


  is✠u-eq : (u : unknown) (h✠ : is✠u u) → u ≡ ✠u
  is✠u-eq u h✠ = /elim Ptop auxtop
    (λ a x h' → flip-subst-≡ Ptop _ _ (uinj✠ a x h')
         (funext ((λ {⟦ _ ⟧ →  simpl-eq _ _ _})))) u ⟦ h✠ ⟧
    where
      Ptop = λ (u : unknown) → Box (is✠u u) → u ≡ ✠u
      auxtop : ( u : Σ⁺ A B) → Ptop ⦅ u ⦆
      auxtop (inj a x) ⟦ h ⟧ = uinj✠ a x (SquashBox h)
      auxtop ?Σ ⟦ h ⟧ = absurd (SquashBox h)
      auxtop ✠Σ _ = refl

      simpl-eq : {A : Set} {x y : A} (eq : x ≡ y) (P : A → Set) (p : P x) →
               eq ≡ subst (λ a → P a → a ≡ y) (sym eq) (λ _ → refl) p
      simpl-eq refl P r = refl
