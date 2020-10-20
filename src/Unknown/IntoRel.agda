{-# OPTIONS --without-K --prop --rewriting #-}

open import prelude
open PE hiding (_≡_)
open import Unknown.Core
import Poset as P
open P.Initial
open P.Final
import Unknown.Interface as I

module Unknown.IntoRel (fp : I.familyPack)
                       {{PB : ∀ {c} → P.Poset₀ (I.familyPack.B fp c)}}
                       (✠B : ∀ {c} → P.Initial (I.familyPack.B fp c))
                       where

open import Unknown.Rel fp ✠B

iDDB : (c : A) → intoDomData
iDDB c = record {
    X = B c;
    cx = c;
    Xε = P._⊑_ {{PB {c}}};
    is✠X = P.is-bot ✠B;
    ✠X-min = P.bot-min ✠B;
    ✠X-smallest = P.bot-smallest ✠B;
    Xε-hprop = P.⊑-hProp {{PB {c}}}
  }

private
  decA-refl : (a : A) → decA a a ≡ yes erefl
  decA-refl a = decEq-refl decA {a} erefl

  decA-neq = decEq-neq decA

  instance
    PUnkown = unknownᵖ

module IntoUnknownCompat (iDD : intoDomData) where

  open intoDomData iDD
  open IntoUnknown iDD

  module IU (c : A) = IntoUnknown (iDDB c)


  open P.Initial

  uinj-uε-inv : (c : A) (x : B c) (u : unknown) → uε (uinj c x) u → IU.intoUnkε c x u
  uinj-uε-inv c x = /elim P aux aux-quot
    where
      P = λ (u : unknown) → uε (uinj c x) u → IU.intoUnkε c x u
      aux : (u : Σ⁺ A B) → P ⦅ u ⦆
      aux (inj c' x') cxu with decA c' c
      ... | yes refl rewrite decA-refl c' = cxu
      ... | no h rewrite decA-neq _ _ h = cxu
      aux ?Σ cxu = IU.??max-intoUnkε c {x}
      aux ✠Σ cxu = IU.✠min-intoUnkε c {x} ✠u (SquashBox (✠unk .bot-smallest {uinj c x} {✠u} cxu is✠✠u))

      aux-quot : quot-elim P aux
      aux-quot a _ x₁ = funext (λ _ → IU.intoUnkε-hprop c {x} {✠u} _ _)

  private
    Bε = λ {c} → P._⊑_ {{PB {c}}}
    -- reflB = λ c {x} → P.refl {{PB {c}}} {x}
    -- Bε-hprop = λ {c} {x} {y} → P.⊑-hProp  {{PB {c}}} {x} {y}
    -- ✠min = λ {c} {b} {b'} → P.bot-min (✠B {c}) {b} {b'}
    -- ✠smallest = λ {c} {b} {b'} → P.bot-smallest (✠B {c}) {b} {b'}

  compat : (transXε : ∀ {x b b'}(xb : Xε x b)(bb' : Bε b b') → Xε x b')
            {x : X} {u u' : unknown} → intoUnkε x u → uε u u' → intoUnkε x u'
  compat transXε {x} {u} {u'} = /elim Ptop auxtop auxtop-quot u u'
    where
      P = λ (x' : B cx)(u' : unknown)→
          (xu : Xε x x')(uu' : uε (uinj cx x') u') → intoUnkε x u'
      aux : (x' : B cx)(u' : Σ⁺ A B) → P x' ⦅ u' ⦆
      aux x' (inj c' x'') xu uu' with decA c' cx
      ... | yes refl rewrite decA-refl c' = transXε xu uu'
      ... | no h rewrite decA-neq _ _ h =
        let h✠u = SquashBox (✠unk .bot-smallest {uinj cx x'} {✠u} uu' (is✠✠u)) in
        ⟦ ✠X-smallest xu h✠u ⟧
      aux x' ?Σ _ _ = tt
      aux x' ✠Σ xu uu' =
        let h✠u = SquashBox (✠unk .bot-smallest {uinj cx x'} {✠u} uu' (is✠✠u)) in
        ✠min-intoUnkε ✠u (✠X-smallest xu h✠u)

      aux-quot : (x' : B cx) → quot-elim (P x') (aux x')
      aux-quot x' _ _ _ =
        funext (λ _ → funext (λ _ → intoUnkε-hprop {x} {✠u} _ _))

      Ptop = λ (u : unknown) →
        (u' : unknown)(xu : intoUnkε x u)(uu' : uε u u') → intoUnkε x u'
      auxtop : (u : Σ⁺ A B) → Ptop ⦅ u ⦆
      auxtop (inj c' x') u' xu uu' with decA c' cx
      ... | yes refl = /elim (P x') (aux x') (aux-quot x') u' xu uu'
      ... | no h = ✠min-intoUnkε u' (unbox xu)
      auxtop ?Σ u' _ uu' rewrite (u?ε-inv u' uu') = tt
      auxtop ✠Σ u' xu _ =
        ✠min-intoUnkε u' (✠smallest-intoUnkε {u = ✠u} xu (is✠✠u))

      auxtop-quot : quot-elim Ptop auxtop
      auxtop-quot _ _ _ =
        funext (λ u' → funext (λ _ → funext (λ _ → intoUnkε-hprop {x} {u'} _ _)))


intoDistrData = I.intoDistrData fp ✠B


module _ (c : A) (d : intoDistrData c) where
  open P.Distr
--  open P.IsRepresentablePosetDistr
  open P._⇒-Poset_
  open P.Initial
  open P.Final

  open I.intoDistrData d

  intoDistrDom : intoDomData
  intoDistrDom = record
    { X = X
    ; cx = c
    ; Xε = distr XB
    ; is✠X = is-bot ✠X
    ; ✠X-min = P.bot-min-over' {X} {B c} {{PX}} {{PB {c}}} ✠X XB
    ; ✠X-smallest = P.distr-smallest ✠X (✠B {c}) XB down✠
    ; Xε-hprop = distr-hProp XB}

  intoDomDistrSelfCompat : intoDomDataCompat intoDistrDom intoDistrDom
  intoDomDistrSelfCompat = record
    { ceq = refl
    ; XY = P._⊑_
    ; ✠XY-smallest = bot-smallest ✠X
    ; XYcompat = act-left XB }


module IntoDistr (cx : A) (iDiDX : intoDistrData cx) where

  open P.Distr
--  open P.IsRepresentablePosetDistr
  open P._⇒-Poset_
  open P.Initial
  open P.Final

  open I.intoDistrData iDiDX

  private
    -- isXB = isDistr XB

    iDDX : intoDomData
    iDDX = intoDistrDom cx iDiDX

    iDDXSelfCompat : intoDomDataCompat iDDX iDDX
    iDDXSelfCompat = intoDomDistrSelfCompat cx iDiDX

  open intoDomData iDDX using (Xε)

  private
    iDDXBcompat : intoDomDataCompat iDDX (iDDB cx)
    iDDXBcompat = record
      { ceq = refl
      ; XY = Xε
      ; ✠XY-smallest = P.distr-smallest ✠X (✠B {cx}) XB down✠
      ; XYcompat = act-right XB }


  open IntoUnknown iDDX


  𝕦inj : B cx P.⇒-Poset unknown
  𝕦inj = record { fun = uinj cx ; monotone = uinj-mon cx }

  from-unknown : unknown → X
  from-unknown = /rec X aux aux-quot
    where
      aux-inj : (c : A) (x : B c) → X
      aux-inj c x with decA c cx
      ... | yes refl = down XB .fun x
      ... | no _ = bot ✠X

      aux : Σ⁺ A B → X
      aux (inj c x) = aux-inj c x
      aux ?Σ = top ?X
      aux ✠Σ = bot ✠X

      aux-quot : quot-rec X aux
      aux-quot c x h✠ with decA c cx
      ... | yes refl = is-bot-spec ✠X (down✠ h✠)
      ... | no _ = refl

  from-unknown-mon : ∀ {u u' : unknown} (uu' : u P.⊑ u') → from-unknown u P.⊑ from-unknown u'
  from-unknown-mon {u} {u'} uu' = /elim Ptop auxtop auxtop-quot u u' uu'
    where
      P = λ (x : B cx)(u' : unknown) → (uu' : uε (uinj cx x) u') → down XB .fun x P.⊑ from-unknown u'
      aux : (x : B cx)(u' : Σ⁺ A B) → P x ⦅ u' ⦆
      aux x (inj c' x') with decA c' cx
      ... | yes refl rewrite decA-refl c' = down XB .monotone
      ... | no h rewrite decA-neq _ _ h = λ h✠ → bot-min ✠X (down✠ (unbox h✠))
      aux x ?Σ = λ _ → top-max ?X (top-is-top ?X)
      aux x ✠Σ uu' = bot-min ✠X (down✠ (SquashBox (✠unk .bot-smallest {uinj cx x} {✠u} uu' is✠✠u)))

      aux-quot : (x : B cx) → quot-elim (P x) (aux x)
      aux-quot x c x' h = funext (λ _ → P.⊑-hProp {{PX}} {down XB .fun x} {from-unknown ✠u} _ _)

      Ptop = λ (u : unknown) → (u' : unknown) (uu' : uε u u') → from-unknown u P.⊑ from-unknown u'
      auxtop : (u : Σ⁺ A B) → Ptop ⦅ u ⦆
      auxtop (inj c x) with decA c cx
      ... | yes refl = /elim (P x) (aux x) (aux-quot x)
      ... | no _ = λ u' uu' → bot-min ✠X (bot-is-bot ✠X)
      auxtop ?Σ u' uu' rewrite u?ε-inv u' uu' = top-max ?X (top-is-top ?X)
      auxtop ✠Σ u' uu' = bot-min ✠X (bot-is-bot ✠X)

      auxtop-quot : quot-elim Ptop auxtop
      auxtop-quot c x' h = funext (λ u' → funext (λ _ → P.⊑-hProp {{PX}} {from-unknown ✠u} {from-unknown u'} _ _))


  from-unknown-✠u : (u : unknown) → is✠u u → is-bot ✠X (from-unknown u)
  from-unknown-✠u u h rewrite is✠u-eq u h = bot-is-bot ✠X

  module IUDsame = IntoUnknownDown iDDX iDDX iDDXSelfCompat

  module IUD = IntoUnknownDown iDDX (iDDB cx) iDDXBcompat

  module IUC = IntoUnknownCompat iDDX

  open P.PosetDistr X unknown intoUnkε

  intoUnkε-PosetDistr : PosetDistr
  intoUnkε-PosetDistr = record
    { act-left = λ {x} {x'} {u} → IUDsame.compatDown {x} {x'} {u}
    ; act-right = λ {x} {u} {u'} → IUC.compat (act-right XB) {x} {u} {u'}
    ; distr-hProp = λ {u} {u'} → intoUnkε-hprop {u} {u'} }

  intoUnkε-LeftRepresentable : LeftRepresentable
  intoUnkε-LeftRepresentable = record
    { up = updef
    ; up-repr-from = λ {x} {u} → /elim (Pupfrom x) (auxupfrom x) (quotupfrom x) u
    ; up-repr-to = λ {x} {u} → let ux = up XB .fun x in
      IUD.compatDown {x} {ux} {u} (P.⊑-up XB x) ∘ IUC.uinj-uε-inv cx ux u }
    where
      updef = P.mon-∘ 𝕦inj (up XB)
      Pupfrom = λ (x : X) (u : unknown) → intoUnkε x u → uε (uinj cx (up XB .fun x)) u
      auxupfrom : (x : X) (u : Σ⁺ A B) → Pupfrom x ⦅ u ⦆
      auxupfrom x (inj c' x') cxu with decA cx c'
      ... | yes refl rewrite decA-refl c' = up-repr-from XB cxu
      ... | no h rewrite decA-neq _ _ h = ⟦ (P.up-bot ✠X ✠B XB (unbox cxu)) ⟧
      auxupfrom x ?Σ _ = u?ε (uinj cx (up XB .fun x))
      auxupfrom x ✠Σ cxu =
        ✠unk .bot-min {uinj cx (up XB .fun x)} {✠u}
                      (toSquashBox (P.up-bot ✠X ✠B XB (unbox cxu)))
      quotupfrom : (x : X) → quot-elim (Pupfrom x) (auxupfrom x)
      quotupfrom x c x' h =
        funext (λ _ → uε-hprop {uinj cx (up XB .fun x)} {✠u} _ _)

  intoUnkε-RightRepresentable : RightRepresentable
  intoUnkε-RightRepresentable = record
    { down = downdef
    ; down-repr-from = λ {x} {u} → /elim (Pdownfrom x) (auxdownfrom x) (quotdownfrom x) u
    ; down-repr-to = λ {x} {u} → /elim (Pdownto x) (auxdownto x) (quotdownto x) u }
    where
      downdef = record { fun = from-unknown ; monotone = λ {u} {u'} → from-unknown-mon {u} {u'} }
      Pdownfrom = λ (x : X) (u : unknown) → intoUnkε x u → x P.⊑ downdef .fun u
      auxdownfrom : (x : X) (u : Σ⁺ A B) → Pdownfrom x ⦅ u ⦆
      auxdownfrom x (inj c' x') with decA cx c'
      ... | yes refl rewrite decA-refl c' = down-repr-from XB
      ... | no h rewrite decA-neq _ _ h = λ cxu → bot-min ✠X (unbox cxu)
      auxdownfrom x ?Σ _ = top-max ?X (top-is-top ?X)
      auxdownfrom x ✠Σ cxu = bot-min ✠X (unbox cxu)
      quotdownfrom : (x : X) → quot-elim (Pdownfrom x) (auxdownfrom x)
      quotdownfrom x _ _ _ = funext (λ _ → P.⊑-hProp {x = x} {downdef .fun ✠u} _ _)


      Pdownto = λ (x : X) (u : unknown) → x P.⊑ downdef .fun u → intoUnkε x u
      auxdownto : (x : X) (u : Σ⁺ A B) → Pdownto x ⦅ u ⦆
      auxdownto x (inj c' x') with decA cx c'
      ... | yes refl rewrite decA-refl c' = down-repr-to XB
      ... | no h rewrite decA-neq _ _ h = λ h → ⟦ (bot-smallest ✠X h (bot-is-bot ✠X)) ⟧
      auxdownto x ?Σ _ = ??max-intoUnkε {x}
      auxdownto x ✠Σ xu = ✠min-intoUnkε {x} ✠u (bot-smallest ✠X xu (bot-is-bot ✠X))
      quotdownto : (x : X) → quot-elim (Pdownto x) (auxdownto x)
      quotdownto x _ _ _ = funext (λ _ → intoUnkε-hprop {x} {✠u} _ _)


  intoUnkε-isDistr : IsRepresentablePosetDistr
  intoUnkε-isDistr = record
    { isPosetDistr = intoUnkε-PosetDistr
    ; isLeftRepresentable = intoUnkε-LeftRepresentable
    ; isRightRepresentable = intoUnkε-RightRepresentable }

  open import Function

  intoUnkε-Distr : P.𝔻istr (X , PX) 𝕦nknown
  intoUnkε-Distr = record
    { distr = intoUnkε
    ; isDistr = intoUnkε-isDistr
    ; up-down-inverseˡ = pf }
    where
       pf : Inverseˡ {a = lzero} {A = X} _≡_ _≡_
            (P.PosetDistr.IsRepresentablePosetDistr.down intoUnkε-isDistr .fun)
            (P.PosetDistr.IsRepresentablePosetDistr.up intoUnkε-isDistr .fun)
       pf rewrite decA-refl cx = λ x → up-down-inverseˡ XB x

module IntoDistrDownCompat (cx : A) (iDiDX iDiDY : intoDistrData cx) where

  module IDX = IntoDistr cx iDiDX
  module IDY = IntoDistr cx iDiDY

  open I.intoDistrData iDiDX
  open I.intoDistrData iDiDY renaming (X to Y; PX to PY; ✠X to ✠Y; ?X to ?Y ; XB to YB)

  open P

  dX = IDX.intoUnkε-Distr
  dY = IDY.intoUnkε-Distr

  compat : (XY : Distr X Y) (down✠XY : {y : Y} → P.is-bot ✠Y y → P.is-bot ✠X (XY P.↡ y))
            (H : XB ≡ ∘-Distr XY YB) → dX ≡ ∘-Distr XY dY
  compat XY down✠XY H = 𝔻istr-ext _ _ (λ x → /elim (P x) (aux x) (quot-helper x))
    where
      box-helper : (x : X) → Box (is-bot ✠X x) ≡ Box (is-bot ✠Y (XY ↟ x))
      box-helper x = hpropext Box-hprop Box-hprop (λ hx → ⟦ up-bot ✠X ✠Y XY (unbox hx) ⟧)
                      λ hy → ⟦ bot-smallest ✠X (down-up-greater XY x) (down✠XY (unbox hy)) ⟧
      P = λ (x : X) (u : unknown) → 𝕕istr dX x u ≡ 𝕕istr (∘-Distr XY dY) x u
      aux : (x : X) (u : Σ⁺ A B) → P x ⦅ u ⦆
      aux x (inj c b) with decA c cx
      ... | yes refl = PE.cong-app (PE.cong-app (cong 𝕕istr H) x) b
      ... | no h = box-helper x
      aux x ?Σ = PE.refl
      aux x ✠Σ = box-helper x

      quot-helper : (x : X) → quot-elim (P x) (aux x)
      quot-helper x _ _ _ = hProp-hSet (𝕕istr-hProp dX {x} {✠u}) (𝕕istr-hProp (∘-Distr XY dY) {x} {✠u}) _ _

module IntoDistrDownCompatEq (cx cy : A)  (iDiDX : intoDistrData cx) (iDiDY : intoDistrData cy) where

  module IDX = IntoDistr cx iDiDX
  module IDY = IntoDistr cy iDiDY

  open I.intoDistrData iDiDX using (X ; PX ; XB; ✠X)
  open I.intoDistrData iDiDY renaming (X to Y; PX to PY; ✠X to ✠Y; XB to YB)

  open P

  dX = IDX.intoUnkε-Distr
  dY = IDY.intoUnkε-Distr

  compat : (cxy : cx ≡ cy) (XY : Distr X Y)
            (down✠XY : {y : Y} → P.is-bot ✠Y y → P.is-bot ✠X (XY P.↡ y))
            (H : subst (λ c → Distr X (B c)) cxy XB ≡ ∘-Distr XY YB) →
             dX ≡ ∘-Distr XY dY
  compat PE.refl = IntoDistrDownCompat.compat cx iDiDX iDiDY
