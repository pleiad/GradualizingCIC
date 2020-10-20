{-# OPTIONS --without-K --prop --rewriting #-}

open import Agda.Builtin.Equality

open import prelude
open import Unknown.Core
open PE hiding (_≡_)

module Unknown.Into (pfp : pointedFamilyPack) where

open pointedFamilyPack pfp
open UnknownType pfp


record intoDomData : Set₁ where
  field
    X : Set
    cx : A
    Xε : REL X (B cx) lzero
    is✠X : X → Prop
    ✠X-min : ∀ {x x'} → is✠X x → Xε x x'
    ✠X-smallest : ∀ {x x'} → Xε x x' → is✠ cx x' → is✠X x
    Xε-hprop : Irrelevant Xε


module IntoUnknown (iDD : intoDomData) where
  open intoDomData iDD

  intoUnkε : REL X unknown lzero
  intoUnkε x = /rec Set
    (λ { (inj c' x') → auxInj x' (decA c' cx)
        ; ?Σ → ⊤
        ; ✠Σ → Box (is✠X x) })
    λ { c' x' h✠ → auxInjEq x' (decA c' cx) h✠}
    where
      auxInj : {c' : A} (x' : B c') (h : Dec (c' ≡ cx)) → Set
      auxInj x' (yes eq) = Xε x (subst B eq x')
      auxInj x' (no h) = Box (is✠X x)

      auxInjEq : {c' : A} (x' : B c') (h : Dec (c' ≡ cx)) (h✠ : is✠ c' x') →
                  auxInj x' h ≡ Box (is✠X x)
      auxInjEq x' (yes erefl) h✠ =
        hpropext Xε-hprop Box-hprop
                  (λ xε → ⟦ ✠X-smallest xε h✠ ⟧)
                  λ h✠X → ✠X-min (unbox h✠X)
      auxInjEq x' (no h) h✠ = erefl

  intoUnkε-hprop : Irrelevant intoUnkε
  intoUnkε-hprop {x} {y} = /elim Ptop auxtop
    (λ {c' x' h✠ →
        funext (λ _ → funext (λ _ → hProp-to-hSet Box-hprop _ _))}) y
    where
      Ptop = λ (y : unknown) → (a b : intoUnkε x y) → a ≡ b
      auxtop : (y : Σ⁺ A B) → Ptop ⦅ y ⦆
      auxtop (inj c' x') with decA c' cx
      ... | yes erefl = Xε-hprop
      ... | no h = Box-hprop
      auxtop ?Σ = ⊤-hprop
      auxtop ✠Σ = Box-hprop

  ??max-intoUnkε : {x : X} → intoUnkε x ?u
  ??max-intoUnkε = tt

  ✠min-intoUnkε : {x : X} (u : unknown) → is✠X x → intoUnkε x u
  ✠min-intoUnkε {x} u h✠ = /elim (intoUnkε x) aux
    (λ _ _ _ →  intoUnkε-hprop {x = x} {y = ✠u} _ _ ) u
    where
      aux : (u : Σ⁺ A B) → intoUnkε x ⦅ u ⦆
      aux (inj c' x') with decA c' cx
      ... | yes erefl = ✠X-min h✠
      ... | no h = ⟦ h✠ ⟧
      aux ?Σ = tt
      aux ✠Σ = ⟦ h✠ ⟧

  ✠smallest-intoUnkε : {x : X} {u : unknown} → intoUnkε x u → is✠u u → is✠X x
  ✠smallest-intoUnkε {x} {u} xu hu =
    unbox (/elim P aux aux-quot u xu ⟦ hu ⟧)
    where
      P = λ (u : unknown) → intoUnkε x u → Box (is✠u u) → Box (is✠X x)
      aux : (u : Σ⁺ A B) → P ⦅ u ⦆
      aux (inj c' x') xu ⟦ hu ⟧ with decA c' cx
      ... | yes erefl = ⟦ ✠X-smallest xu (SquashBox hu) ⟧
      ... | no h = xu
      aux ?Σ _ ⟦ h ⟧ = absurd (SquashBox h)
      aux ✠Σ xu _ = xu

      aux-quot : quot-elim P aux
      aux-quot _ _ _ = funext (λ _ → funext (λ _ → Box-hprop _ _))


record intoDomDataCompat (iX iY : intoDomData) : Set₁ where
  open intoDomData
  field
    ceq : iY .cx ≡ iX .cx
    XY : REL (iX .X) (iY .X) lzero
    ✠XY-smallest : ∀ {x y} → XY x y → iY .is✠X y → iX .is✠X x
    XYcompat : ∀ {x y z} (xy : XY x y) (yz : iY .Xε y z) → iX .Xε x (subst B ceq z)

module IntoUnknownDown (iDDX iDDY : intoDomData)
                       (iDDC : intoDomDataCompat iDDX iDDY) where

  open intoDomData iDDX
  open intoDomData iDDY renaming (X to Y; cx to cy ; Xε to Yε ; is✠X to is✠Y ;
                ✠X-min to ✠Y-min; ✠X-smallest to ✠Y-smallest)

  open intoDomDataCompat iDDC

  module IUX = IntoUnknown iDDX
  module IUY = IntoUnknown iDDY

  compatDown : ∀ {x y u} (xy : XY x y)(yu : IUY.intoUnkε y u) →  IUX.intoUnkε x u
  compatDown {x} {y} {u} xy = /elim P aux aux-quot u
    where
      P = λ (u : unknown) → (yu : IUY.intoUnkε y u) →  IUX.intoUnkε x u
      aux : (u : Σ⁺ A B) → P ⦅ u ⦆
      aux (inj c' z) yu with decA c' cy
      ... | yes erefl rewrite decEq-refl decA ceq =   XYcompat xy yu
      aux (inj c' z) yu | no h rewrite ceq rewrite decEq-neq decA cx c' (h ∘ sym) =
         ⟦ ✠XY-smallest xy (unbox yu) ⟧
      aux ?Σ _ = tt
      aux ✠Σ yu =
        let h✠y = IUY.✠smallest-intoUnkε {x = y} {✠u} yu (is✠✠u) in
        IUX.✠min-intoUnkε ✠u (✠XY-smallest xy h✠y)

      aux-quot : quot-elim P aux
      aux-quot a x' h = funext (λ _ → IUX.intoUnkε-hprop {x = x} { ✠u } _ _)
