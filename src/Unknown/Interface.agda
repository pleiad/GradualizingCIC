{-# OPTIONS --without-K --prop --rewriting #-}
module Unknown.Interface where

open import prelude
import Poset as P

record familyPack {l l' : Level} : Set (lsuc (l ⊔ l')) where
  field
    A : Set l
    B : A → Set l'
    decA : DecidableEquality A
    hSetB : ∀ a → hSet (B a)

module _ (fp : familyPack {lzero} {lzero})
         {{PB : ∀ {c} → P.Poset₀ (familyPack.B fp c)}}
         (✠B : ∀ {c} → P.Initial (familyPack.B fp c))
         where

  open familyPack fp

  private
    𝔹 : (c : A) → P.ℙoset
    𝔹 c = B c , PB {c}

  record intoDistrData (cx : A) : Set₁ where
    field
      X : Set
      {{PX}} : P.Poset₀ X
      ✠X : P.Initial X
      ?X : P.Final X
      XB : P.Distr X (B cx)
      down✠ : P.preserves-bot {X} {B cx} ✠X (✠B {cx}) XB

    poset : P.ℙoset
    poset = X , PX

  open intoDistrData

  record intoDistrCompat {cx cy : A}
                         (dX : intoDistrData cx)
                         (dY : intoDistrData cy)
                         : Set₁ where
    field
      cxy : cx ≡ cy
      distr : P.𝔻istr (poset dX) (poset dY)
      down✠ : P.preserves-bot (dX .✠X) (dY .✠X) distr

    XB' = PE.subst (λ c → P.𝔻istr (poset dX) (𝔹 c)) cxy (dX .XB)
    field
      distr-eq : XB' ≡ P.∘-𝔻istr distr (dY .XB)

  selfDistrCompat : {cx : A} (dX : intoDistrData cx) → intoDistrCompat dX dX
  selfDistrCompat {cx} dX = record
    { cxy = erefl
    ; distr = P.id-𝔻istr (poset dX)
    ; down✠ = λ x → x
    ; distr-eq = PE.sym (P.id-∘-𝔻istr (dX .XB)) }

  record BuildUnknown : Set₁ where
    open P
    open intoDistrCompat
    field
      unknownType : ℙoset

    private
      unk = unknownType .fst
      instance
        Punk : Poset unk
        Punk = unknownType .snd

    field
      unknown-hSet : hSet unk
      ✠unk : P.Initial unk
      ?unk : P.Final unk
      intoDistr : {cx : A}(d : intoDistrData cx) → 𝔻istr (poset d) unknownType
      intoDistr-down✠ : {cx : A}(d : intoDistrData cx) →
                        P.preserves-bot {{d .PX}} (d .✠X) ✠unk (intoDistr d)
      intoCompat : {cx cy : A}
                   (dX : intoDistrData cx)
                   (dY : intoDistrData cy)
                   (dXY : intoDistrCompat dX dY) →
                   intoDistr dX ≡ ∘-𝔻istr (distr dXY) (intoDistr dY)

UnknownBuilder : Set₁
UnknownBuilder = (fp : familyPack)
                 {{PB : ∀ {c} → P.Poset₀ (fp .familyPack.B c)}}
                 (✠B : ∀ {c} → P.Initial (fp .familyPack.B c)) →
                 BuildUnknown fp {{PB}} ✠B
