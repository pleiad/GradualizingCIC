{-# OPTIONS --without-K --prop #-}
module Poset where

open import prelude

open import Relation.Binary.Structures
import Relation.Binary.Bundles as RBB -- using (Poset)


record Poset {c} {l} (A : Set c) : Set (lsuc (c ⊔ l)) where
  infix 5 _⊑_
  field
    _⊑_ : Rel A l
    isPoset : IsPartialOrder _≡_ _⊑_
    ⊑-hProp : Irrelevant _⊑_
    carrier-hSet  : hSet A

  open IsPartialOrder isPoset public
    hiding (module Eq)

  preorder : RBB.Preorder c c l
  preorder = record
    { isPreorder = isPreorder
    }

  open RBB.Preorder preorder public
    using (module Eq)


open Poset {{...}} public

Poset₀ : Set → Set₁
Poset₀ = Poset {lzero} {lzero}

abstract
  trans-left-id : {X : Set} {{PX : Poset₀ X}} {x x' : X}
                  (xx' : x ⊑ x') (x'x' : x' ⊑ x' ) →
                  trans xx' x'x' ≡ xx'
  trans-left-id {{PX}} xx' x'x' = ⊑-hProp _ _



record Initial (B : Set) {{PB : Poset₀ B}} : Set₁ where
  field
    bot : B
    is-bot : B → Prop
    is-bot-spec : {b : B} (hbot : is-bot b) → b ≡ bot
    bot-is-bot : is-bot bot
    bot-min : {b b' : B} (hbot : is-bot b) → b ⊑ b'
    bot-smallest : {b b' : B} (bb' : b ⊑ b') → is-bot b' → is-bot b

open Initial public

record Final (B : Set) {{PB : Poset₀ B}} : Set₁ where
  field
    top : B
    is-top : B → Prop
    is-top-spec : {b : B} (htop : is-top b) → b ≡ top
    top-is-top : is-top top
    top-max : {b b' : B} (htop : is-top b') → b ⊑ b'
    top-greatest : {b b' : B} (bb' : b ⊑ b') → is-top b → is-top b'

open Final public

record PointedPoset : Set₂ where
  field
    carrier : Set
    {{poset}} : Poset₀ carrier
    initial : Initial carrier
    final : Final carrier

  open Poset poset public
  open Initial initial public
  open Final final public


Reflexive-respects-≡ : ∀ {c} {l} {A : Set c} (R : Rel A l) (reflR : Reflexive R) → _≡_ ⇒ R
Reflexive-respects-≡ R reflR erefl = reflR

record _⇒-Poset_ {cA cB lA lB} (A : Set cA) (B : Set cB) {{PA : Poset {cA} {lA} A}} {{PB : Poset {cB} {lB} B}} : Set (lsuc (cA ⊔ cB ⊔ lA ⊔ lB))  where
  field
    fun      : A → B
    monotone : _⊑_ {{PA}} =[ fun ]⇒ _⊑_ {{PB}}

open _⇒-Poset_

abstract
  ⇒-Poset-ext : {cA cB lA lB : Level} {A : Set cA} {B : Set cB} {{PA : Poset {cA} {lA} A}} {{PB : Poset {cB} {lB} B}} {f g : A ⇒-Poset B} → f .fun ≡ g .fun → f ≡ g
  ⇒-Poset-ext {{PA}} {{PB}} {g = g} erefl =
    PE.cong (λ pf → record { fun = g .fun ; monotone = λ {x} {y} → pf {x} {y} })
        (funext-impl (funext-impl (funext (λ _ → ⊑-hProp _ _))))

mon-id : ∀ {c l} {A : Set c} {{PA : Poset {c} {l} A}} → A ⇒-Poset A
mon-id {A} {{PA}} = record { fun = id ; monotone = id }

mon-∘ : ∀ {A B C} {{PA : Poset₀ A}} {{PB : Poset₀ B}} {{PC : Poset₀ C}} (g : B ⇒-Poset C) (f : A ⇒-Poset B) → A ⇒-Poset C
mon-∘ g f = record { fun = fun g ∘ fun f ; monotone = monotone g ∘ monotone f }


ℙoset : Set₁
ℙoset = Σ[ A ∈ Set ] Poset A

ℙosetˡ : ∀ {l} {l'} → Set (lsuc (l ⊔ l'))
ℙosetˡ {l} {l'} = Σ[ A ∈ Set l ] Poset {l} {l'} A


module PosetDistr {cA cB lA lB}
                  (A : Set cA) (B : Set cB)
                  {{PA : Poset {cA} {lA} A}}
                  {{PB : Poset {cB} {lB} B}}
                  (R : REL A B lzero)
                  where

  record PosetDistr : Set (cA ⊔ cB ⊔ lA ⊔ lB) where
    field
      act-left : {a a' : A} {b : B} → a ⊑ a' → R a' b → R a b
      act-right : {a : A} {b b' : B} → R a b → b ⊑ b' → R a b'
      distr-hProp : Irrelevant R

  l : Level
  l = lsuc (cA ⊔ cB ⊔ lA ⊔ lB)

  record LeftRepresentable : Set l where
    field
      up : A ⇒-Poset B
      up-repr-from : ∀ {a b} → R a b → (fun up a) ⊑ b
      up-repr-to : ∀ {a b} → (fun up a) ⊑ b → R a b

  record RightRepresentable : Set l where
    field
      down : B ⇒-Poset A
      down-repr-from : ∀ {a b} → R a b → a ⊑ fun down b
      down-repr-to : ∀ {a b} → a ⊑ fun down b → R a b

  record IsRepresentablePosetDistr : Set l where
    field
      isPosetDistr : PosetDistr
      isLeftRepresentable : LeftRepresentable
      isRightRepresentable : RightRepresentable

    open PosetDistr isPosetDistr public
    open LeftRepresentable isLeftRepresentable public
    open RightRepresentable isRightRepresentable public

  module Extensionality where

    PosetDistr-hProp : ishProp PosetDistr
    PosetDistr-hProp D D' = pf
      where
        open PosetDistr
        al-ext : (λ {a} {a'} {b} → D .act-left {a} {a'} {b}) ≡ D' .act-left
        al-ext = (funext-impl (funext-impl (funext-impl (funext (λ _ → funext (λ _ → distr-hProp D _ _))))))
        ar-ext : (λ {a} {b} {b'} → D .act-right {a} {b} {b'}) ≡ D' .act-right
        ar-ext = (funext-impl (funext-impl (funext-impl (funext (λ _ → funext (λ _ → distr-hProp D _ _))))))
        dh-ext : (λ {x} {y} → D .distr-hProp {x} {y}) ≡ D' .distr-hProp
        dh-ext = (irrelevant-is-hProp R _ _)
        pf : D ≡ D'
        pf with al-ext with ar-ext with dh-ext
        ... | erefl | erefl | erefl = erefl


    up-unique : (L L' : LeftRepresentable) → L .LeftRepresentable.up ≡ L' .LeftRepresentable.up
    up-unique L L' = ⇒-Poset-ext (funext (λ a → antisym (helper a L L') (helper a L' L)))
      where
        open LeftRepresentable
        helper : (a : A) (L L' : LeftRepresentable) → L . up .fun a ⊑ L' .up .fun a
        helper a L L' = up-repr-from L (up-repr-to L' refl)

    LeftRepresentable-hProp : (D : PosetDistr) → ishProp LeftRepresentable
    LeftRepresentable-hProp D L L' with up-unique L L'
    ... | erefl = pf
      where
        open PosetDistr
        open LeftRepresentable
        urf-ext : (λ {a} {b} → L .up-repr-from {a} {b}) ≡ L' .up-repr-from
        urf-ext = (funext-impl (funext-impl (funext (λ _ → ⊑-hProp _ _))))
        urt-ext : (λ {a} {b} → L .up-repr-to {a} {b}) ≡ L' .up-repr-to
        urt-ext = (funext-impl (funext-impl (funext (λ _ → distr-hProp D _ _))))
        pf : L ≡ L'
        pf with urf-ext with urt-ext
        ... | erefl | erefl = erefl

    down-unique : (R R' : RightRepresentable) → R .RightRepresentable.down ≡ R' .RightRepresentable.down
    down-unique R R' = ⇒-Poset-ext (funext (λ a → antisym (helper a R R') (helper a R' R)))
      where
        open RightRepresentable
        helper : (b : B) (R R' : RightRepresentable) → R . down .fun b ⊑ R' .down .fun b
        helper b R R' = down-repr-from R' (down-repr-to R refl)

    RightRepresentable-hProp : (D : PosetDistr) → ishProp RightRepresentable
    RightRepresentable-hProp D R R' with down-unique R R'
    ... | erefl = pf
      where
        open PosetDistr
        open RightRepresentable
        drf-ext : (λ {a} {b} → R .down-repr-from {a} {b}) ≡ R' .down-repr-from
        drf-ext = (funext-impl (funext-impl (funext (λ _ → ⊑-hProp _ _))))
        drt-ext : (λ {a} {b} → R .down-repr-to {a} {b}) ≡ R' .down-repr-to
        drt-ext = (funext-impl (funext-impl (funext (λ _ → distr-hProp D _ _))))
        pf : R ≡ R'
        pf with drf-ext with drt-ext
        ... | erefl | erefl = erefl

    open IsRepresentablePosetDistr

    IsRepresentablePosetDistr-hProp : ishProp IsRepresentablePosetDistr
    IsRepresentablePosetDistr-hProp RPD RPD'
      with PosetDistr-hProp (RPD .isPosetDistr) (RPD' .isPosetDistr)
      with LeftRepresentable-hProp (RPD. isPosetDistr) (RPD .isLeftRepresentable) (RPD' .isLeftRepresentable)
      with RightRepresentable-hProp (RPD. isPosetDistr) (RPD .isRightRepresentable) (RPD' .isRightRepresentable)
    ... | erefl | erefl | erefl = erefl


open PosetDistr using (IsRepresentablePosetDistr)

-- record IsRepresentablePosetDistr {cA cB lA lB} (A : Set cA) (B : Set cB)
--                                     {{PA : Poset {cA} {lA} A}} {{PB : Poset {cB} {lB} B}}
--                                     (R : REL A B lzero)
--                                       : Set (lsuc (cA ⊔ cB ⊔ lA ⊔ lB)) where
--   field
--     up : A ⇒-Poset B
--     down : B ⇒-Poset A
--     up-repr-from : ∀ {a b} → R a b → (fun up a) ⊑ b
--     up-repr-to : ∀ {a b} → (fun up a) ⊑ b → R a b
--     down-repr-from : ∀ {a b} → R a b → a ⊑ fun down b
--     down-repr-to : ∀ {a b} → a ⊑ fun down b → R a b
--     act-left : {a a' : A} {b : B} → a ⊑ a' → R a' b → R a b
--     act-right : {a : A} {b b' : B} → R a b → b ⊑ b' → R a b'
--     distr-hProp : Irrelevant R


-- module _ where
--   open IsRepresentablePosetDistr
--   abstract
--     isDistr-unique-up : {A B : Set} {{PA : Poset₀ A}} {{PB : Poset₀ B}} (R : REL A B lzero)
--                         (id id' : IsRepresentablePosetDistr A B R) → id .up ≡ up id'
--     isDistr-unique-up {A} {B} {{PA}} {{PB}} R id id' = ⇒-Poset-ext (funext (λ a → antisym (helper a id id') (helper a id' id)))
--       where
--         helper : (a : A) (id id' : IsRepresentablePosetDistr A B R) → id .up .fun a ⊑ id' .up .fun a
--         helper a id id' = up-repr-from id (up-repr-to id' refl)

--     isDistr-unique-down : {A B : Set} {{PA : Poset₀ A}} {{PB : Poset₀ B}} (R : REL A B lzero)
--                         (id id' : IsRepresentablePosetDistr A B R) → id .down ≡ down id'
--     isDistr-unique-down {A} {B} {{PA}} {{PB}} R id id' = ⇒-Poset-ext (funext (λ b → antisym (helper b id id') (helper b id' id)))
--       where
--         helper : (b : B) (id id' : IsRepresentablePosetDistr A B R) → id .down .fun b ⊑ id' .down .fun b
--         helper b id id' = down-repr-from id' (down-repr-to id refl)

--     isDistr-ext₀ : {A B : Set} {{PA : Poset₀ A}} {{PB : Poset₀ B}} (R : REL A B lzero)
--                     {up : A ⇒-Poset B}
--                     {down : B ⇒-Poset A}
--                     { urf : ∀ {a b} → R a b → (up .fun a) ⊑ b}
--                     { urt : ∀ {a b} → (up .fun a) ⊑ b → R a b}
--                     { drf : ∀ {a b} → R a b → a ⊑ down .fun b}
--                     { drt : ∀ {a b} → a ⊑ down .fun b → R a b}
--                     { al : {a a' : A} {b : B} → a ⊑ a' → R a' b → R a b}
--                     { ar : {a : A} {b b' : B} → R a b → b ⊑ b' → R a b'}
--                     { dh : Irrelevant R}
--                     { urf' : ∀ {a b} → R a b → (up .fun a) ⊑ b}
--                     { urt' : ∀ {a b} → (up .fun a) ⊑ b → R a b}
--                     { drf' : ∀ {a b} → R a b → a ⊑ down .fun b}
--                     { drt' : ∀ {a b} → a ⊑ down .fun b → R a b}
--                     { al' : {a a' : A} {b : B} → a ⊑ a' → R a' b → R a b}
--                     { ar' : {a : A} {b b' : B} → R a b → b ⊑ b' → R a b'}
--                     { dh' : Irrelevant R} →
--                     (λ {a} {b} → urf {a} {b}) ≡ urf' →
--                     (λ {a} {b} → urt {a} {b}) ≡ urt' →
--                     (λ {a} {b} → drf {a} {b}) ≡ drf' →
--                     (λ {a} {b} → drt {a} {b}) ≡ drt' →
--                     (λ {x} {y} {z} → al {x} {y} {z}) ≡ al' →
--                     (λ {x} {y} {z} → ar {x} {y} {z}) ≡ ar' →
--                     (λ {a} {b} → dh {a} {b}) ≡ dh' →
--                     record {
--                       up = up ;
--                       down = down ;
--                       up-repr-from = urf ;
--                       up-repr-to = urt ;
--                       down-repr-from = drf ;
--                       down-repr-to = drt ;
--                       act-left = al ;
--                       act-right = ar ;
--                       distr-hProp = dh } ≡
--                     record {
--                       up = up ;
--                       down = down ;
--                       up-repr-from = urf' ;
--                       up-repr-to = urt' ;
--                       down-repr-from = drf' ;
--                       down-repr-to = drt' ;
--                       act-left = al' ;
--                       act-right = ar' ;
--                       distr-hProp = dh' }
--     isDistr-ext₀ _ erefl erefl erefl erefl erefl erefl erefl = erefl

-- abstract
--   isDistr-hProp : {A B : Set} {{PA : Poset₀ A}} {{PB : Poset₀ B}} (R : REL A B lzero) → ishProp (IsRepresentablePosetDistr A B R)
--   isDistr-hProp {A} {B} {{PA}} {{PB}} R id@(record { up = up₁ ; down = down₁ ; up-repr-from = up-repr-from₁ ; up-repr-to = up-repr-to₁ ; down-repr-from = down-repr-from₁ ; down-repr-to = down-repr-to₁ ; act-left = act-left₁ ; act-right = act-right₁ ; distr-hProp = distr-hProp₁ }) id'@(record { up = up ; down = down ; up-repr-from = up-repr-from ; up-repr-to = up-repr-to ; down-repr-from = down-repr-from ; down-repr-to = down-repr-to ; act-left = act-left ; act-right = act-right ; distr-hProp = distr-hProp }) with isDistr-unique-down R id id' with isDistr-unique-up R id id'
--   ... | erefl | erefl =
--     isDistr-ext₀ R
--       (funext-impl (funext-impl (funext (λ _ → ⊑-hProp _ _))))
--       (funext-impl (funext-impl (funext (λ _ → distr-hProp _ _))))
--       (funext-impl (funext-impl (funext (λ _ → ⊑-hProp _ _))))
--       (funext-impl (funext-impl (funext (λ _ → distr-hProp _ _))))

abstract
  isDistr-hProp : {A B : Set} {{PA : Poset₀ A}} {{PB : Poset₀ B}} (R : REL A B lzero) → ishProp (IsRepresentablePosetDistr A B R)
  isDistr-hProp {A} {B} {{PA}} {{PB}} R =  PosetDistr.Extensionality.IsRepresentablePosetDistr-hProp A B R

open import Function

record Distr {cA cB lA lB} (A : Set cA) (B : Set cB) {{PA : Poset {cA} {lA} A}} {{PB : Poset {cB} {lB} B}} : Set (lsuc (cA ⊔ cB ⊔ lA ⊔ lB)) where
  field
    distr : REL A B lzero
    isDistr : IsRepresentablePosetDistr A B distr
  open IsRepresentablePosetDistr isDistr public
  field
    up-down-inverseˡ : Inverseˡ {a = cB} {A = B} _≡_ _≡_ (down .fun) (up . fun)


open Distr


id-Distr : (A : Set) {{PA : Poset {_} {lzero} A}} → Distr A A
id-Distr A {{PA}} = record
  { distr = _⊑_ {{PA}}
  ; isDistr = record
    { isPosetDistr = record {
      act-left = trans ;
      act-right = trans ;
      distr-hProp = ⊑-hProp }
    ; isLeftRepresentable = record {
      up = mon-id ;
      up-repr-from = id ;
      up-repr-to = id }
    ; isRightRepresentable = record {
      down = mon-id ;
      down-repr-from = id ;
      down-repr-to = id } }
    ; up-down-inverseˡ = λ a → erefl
  }

-- right biaised definition of composition
-- we use a canonical candidate given by representability rather than the coend formula
∘-Distr : {A B C : Set} {{PA : Poset₀ A}} {{PB : Poset₀ B}} {{PC : Poset₀ C}}
                  (AB : Distr A B) (BC : Distr B C) → Distr A C
∘-Distr {A} {B} {C} {{PA}} {{PB}} {{PC}} AB BC = record
  { distr = λ a c → distr BC (fun (up AB) a) c -- alt : distr AB a (fun (down BC) c)
  ; isDistr = record
    { isPosetDistr = record {
      act-left = λ aa' → act-left BC (monotone (up AB) aa') ;
      act-right = act-right BC ;
      distr-hProp = distr-hProp BC }
    ; isLeftRepresentable = record {
      up = mon-∘ (up BC) (up AB) ;
      up-repr-from = up-repr-from BC ;
      up-repr-to = up-repr-to BC }
    ; isRightRepresentable = record {
      down = mon-∘ (down AB) (down BC) ;
      down-repr-from = down-repr-from AB ∘ up-repr-to AB ∘ down-repr-from BC ;
      down-repr-to = down-repr-to BC ∘ up-repr-from AB ∘ down-repr-to AB
    } }
  ; up-down-inverseˡ = λ a → PE.trans ((PE.cong (AB .down .fun) (BC .up-down-inverseˡ (AB .up .fun a)))) (AB .up-down-inverseˡ a)
  }

_⇒-ℙoset_ : ∀ {c c' l l'} (A : ℙosetˡ {c} {l}) (B : ℙosetˡ {c'} {l'}) → Set (lsuc (c ⊔ c' ⊔ l ⊔ l'))
_⇒-ℙoset_ (A , PA) (B , PB) = _⇒-Poset_ A B {{PA}} {{PB}}

-- The "category" of posets and galois connections (Distr) between them
-- With the current definition it does not satisfy unitality/associativity
-- but this can be corrected, for instance by requiring that the underlying relations are hProp
-- ℙosetPack : ℙosetˡ {lsuc lzero} {lsuc lzero}
-- ℙosetPack = (ℙoset , ℙosetᵖ)

𝔻istr : (A B : ℙoset) → Set₁
𝔻istr (A , PA) (B , PB) = Distr A B {{PA}} {{PB}}

id-𝔻istr : (A : ℙoset) → 𝔻istr A A
id-𝔻istr (A , PA) = id-Distr A {{PA}}

∘-𝔻istr : {A B C : ℙoset} (AB : 𝔻istr A B) (BC : 𝔻istr B C) → 𝔻istr A C
∘-𝔻istr {A , PA} {B , PB} {C , PC} AB BC = ∘-Distr {A} {B} {C} {{PA}} {{PB}} {{PC}} AB BC

PREL : ℙoset → ℙoset → Set₁
PREL A B = REL (A .fst) (B .fst) lzero

𝕕istr : {A B : ℙoset} → 𝔻istr A B → PREL A B
𝕕istr {A , PA} {B , PB} d = distr ⦃ PA ⦄ ⦃ PB ⦄ d

infix 10 _↟_
infix 10 _↡_

_↟_ : {A A' : ℙoset} (d : 𝔻istr A A') (a : A .fst) → A' .fst
_↟_ {A , PA} {A' , PA'} d = fun {{PA}} {{PA'}} (up {{PA}} {{PA'}} d)

_↡_ : {A A' : ℙoset} (d : 𝔻istr A A') (a' : A' .fst) → A .fst
_↡_ {A , PA} {A' , PA'} d = fun {{PA'}} {{PA}} (down {{PA}} {{PA'}} d)


Inverseˡ-hProp : {a b : Level} {A : Set a} {B : Set b} (hSetB : hSet B) (f : A → B) (g : B → A) →
                 ishProp (Inverseˡ {a = a} {A = A} _≡_ _≡_ f g)
Inverseˡ-hProp hSetB f g p₁ p₂ = funext (λ x → hSetB (p₁ x) (p₂ x))

𝔻istr-ext : {A B : ℙoset} (d d' : 𝔻istr A B) → (∀ a b → 𝕕istr d a b ≡ 𝕕istr d' a b) → d ≡ d'
𝔻istr-ext {A , PA} {B , PB} d d' ext with funext (funext ∘ ext)
𝔻istr-ext {A , PA} {B , PB} d d' ext | erefl with isDistr-hProp {{PA}} {{PB}} (distr {{PA = PA}} {{PB = PB}} d)
                                                                              (isDistr {{PA = PA}} {{PB = PB}} d)
                                                                              (isDistr {{PA = PA}} {{PB = PB}} d')
𝔻istr-ext {A , PA} {B , PB} d d' ext | erefl | erefl with Inverseˡ-hProp (carrier-hSet {{PA}}) (_↡_ d) (_↟_ d)
                                                                         (up-down-inverseˡ {{PA = PA}} {{PB = PB}} d)
                                                                         (up-down-inverseˡ {{PA = PA}} {{PB = PB}} d')
𝔻istr-ext {A , PA} {B , PB} d d' ext | erefl | erefl | erefl = erefl


trans-∘-𝔻istr : {A B C : ℙoset} (AB : 𝔻istr A B) (BC : 𝔻istr B C) → ∀ {a b c} → 𝕕istr AB a b → 𝕕istr BC b c → 𝕕istr (∘-𝔻istr AB BC) a c
trans-∘-𝔻istr {A} {B} {C} AB BC ab bc = act-left BC (up-repr-from AB ab) bc
  where
    instance
      PA : Poset (A .fst)
      PA = A .snd
      PB : Poset (B .fst)
      PB = B .snd
      PC : Poset (C .fst)
      PC = C .snd




-- Lemmas on 𝔻istr
abstract
  ⊑-up : {A A' : ℙoset} (d : 𝔻istr A A') (a : A .fst) → 𝕕istr d a (d ↟ a)
  ⊑-up {_ , PA} {A' , PA'} d a = up-repr-to {{PA}} {{PA'}} d (refl {{PA'}} {d ↟ a})

  ⊑-down : {A A' : ℙoset} (d : 𝔻istr A A') (a' : A' .fst) → 𝕕istr d (d ↡ a') a'
  ⊑-down {_ , PA} {A' , PA'} d a' = down-repr-to {{PA}} {{PA'}} d (refl {{PA}} {d ↡ a'})

  id-∘-𝔻istr : ∀ {A B : ℙoset} (AB : 𝔻istr A B) → ∘-𝔻istr (id-𝔻istr A) AB ≡ AB
  id-∘-𝔻istr AB = 𝔻istr-ext _ AB λ a b → erefl

  Distr-up-eq : ∀ {A B : Set} {{PA : Poset A}} {{PB : Poset B}} (d : 𝔻istr (A , PA) (B , PB)) → ∀ {a b} → 𝕕istr d a b ≡ (d ↟ a) ⊑ b
  Distr-up-eq {A} {B} {{PA}} {{PB}} d {a} {b} = hpropext (distr-hProp d) ⊑-hProp (up-repr-from d) (up-repr-to d)


  ∘-id-𝔻istr : ∀ {A B : ℙoset} (AB : 𝔻istr A B) → ∘-𝔻istr AB (id-𝔻istr B) ≡ AB
  ∘-id-𝔻istr {A , PA} {B , PB} AB = 𝔻istr-ext _ AB λ a b → PE.sym (Distr-up-eq {{PA}} {{PB}} AB {a} {b})

  ∘-∘-𝔻istr : ∀ {A B C D : ℙoset} (AB : 𝔻istr A B) (BC : 𝔻istr B C) (CD : 𝔻istr C D) → ∘-𝔻istr AB (∘-𝔻istr BC CD) ≡ ∘-𝔻istr (∘-𝔻istr AB BC) CD
  ∘-∘-𝔻istr AB BC CD = 𝔻istr-ext _ _ λ a d → erefl


  trans-∘-𝔻istr-up : {Ax Ay Az : ℙoset} (Axy : 𝔻istr Ax Ay) (Ayz : 𝔻istr Ay Az)
                    {ax : Ax .fst} {az : Az .fst} (axz : 𝕕istr Ayz (Axy ↟ ax) az) → trans-∘-𝔻istr Axy Ayz (⊑-up Axy ax) axz ≡ axz
  trans-∘-𝔻istr-up {Ax} {Ay} {Az} Axy Ayz axz = distr-hProp (∘-𝔻istr Axy Ayz) _ _
    where
      instance
        PAx = Ax .snd
        PAz = Az .snd



-- A functor from a poset seen as a category to the category of posets and galois connections
record IndexedPoset (A : ℙoset) : Set₂ where
  private
    instance
      PA : Poset (A .fst)
      PA = A .snd
  infix 15 _at_
  infix 15 _onRel_
  field
    _at_ : A .fst → ℙoset
    _onRel_ : _⊑_ =[ _at_ ]⇒ 𝔻istr
    indexedPoset-refl : ∀ (a : A .fst) → _onRel_ refl ≡ id-𝔻istr (_at_ a)
    indexedPoset-trans : ∀ {a b c : A .fst} (ab : a ⊑ b) (bc : b ⊑ c) → _onRel_ (trans ab bc) ≡ ∘-𝔻istr (_onRel_ ab) (_onRel_ bc)


𝕀nitial : ℙoset → Set₁
𝕀nitial (A , PA) = Initial A {{PA}}

𝔽inal : ℙoset → Set₁
𝔽inal (A , PA) = Final A {{PA}}

record IndexedPointedPoset (A : PointedPoset) : Set₃ where
  open PointedPoset A
  open IndexedPoset

  field
    index : IndexedPoset (carrier , poset)
    index-initial : (a : carrier) → 𝕀nitial (index at a)
    index-final : (a : carrier) → 𝔽inal (index at a)

  open IndexedPoset index public

open IndexedPoset

trivialIndexedPoset : (A B : ℙoset) → IndexedPoset A
trivialIndexedPoset A B =
 record
   { _at_ = λ _ → B
   ; _onRel_ = λ _ → id-𝔻istr B
   ; indexedPoset-refl = λ a → PE.refl
   ; indexedPoset-trans = λ ab bc → id-∘-𝔻istr _
   }

IndexedPREL : {A A' : ℙoset} (B : IndexedPoset A) (B' : IndexedPoset A') (Aε : PREL A A') → Set₁
IndexedPREL B B' Aε = ∀ {a a'} (aa' : Aε a a') → PREL (B at a) (B' at a')

record IndexedDistr {A A' : ℙoset} (d : 𝔻istr A A') (B : IndexedPoset A) (B' : IndexedPoset A')  : Set₂ where
  private
    instance
      PA : Poset (A .fst)
      PA = A .snd
      PB : Poset (A' .fst)
      PB = A' .snd
  infix 15 _over_
  field
    _over_ : ∀ {a : A .fst} {a' : A' .fst} (aε : 𝕕istr d a a') → 𝔻istr (B at a) (B' at a')
    indexedDistr-naturality : ∀ {a₁ a₂ a'₁ a'₂} (a₁₂ : a₁ ⊑ a₂) (a₂ε : 𝕕istr d a₂ a'₂) (a₁ε : 𝕕istr d a₁ a'₁) (a'₁₂ : a'₁ ⊑ a'₂) →
      ∘-𝔻istr (B onRel a₁₂) (_over_ a₂ε) ≡ ∘-𝔻istr (_over_ a₁ε) (B' onRel a'₁₂)

open IndexedDistr

toIndexedPREL : {A A' : ℙoset} (Aε : 𝔻istr A A')
                (B : IndexedPoset A) (B' : IndexedPoset A') (Bε : IndexedDistr Aε B B') → IndexedPREL B B' (𝕕istr Aε)
toIndexedPREL {A} {A'} Aε B B' Bε {a} {a'} aε = 𝕕istr (Bε over aε)


id-IndexedDistr : {A : ℙoset} (B : IndexedPoset A) → IndexedDistr (id-𝔻istr A) B B
id-IndexedDistr {A} B = record {
  _over_ = λ aε → B onRel aε ;
  indexedDistr-naturality =
    λ a₁₂ a₂ε a₁ε a'₁₂ →
      PE.trans (PE.sym (indexedPoset-trans B a₁₂ a₂ε))
      (PE.subst (λ aε → B onRel aε ≡ _) (⊑-hProp ⦃ A .snd ⦄ _ _) (indexedPoset-trans B a₁ε a'₁₂)) }

id-toIndexedPREL : {A : ℙoset} (B : IndexedPoset A) → IndexedPREL B B (_⊑_ {{A .snd}})
id-toIndexedPREL {A} B = toIndexedPREL (id-𝔻istr A) B B (id-IndexedDistr B)


∘-IndexedDistr : {Ax Ay Az : ℙoset} (Bx : IndexedPoset Ax) (By : IndexedPoset Ay) (Bz : IndexedPoset Az)
                 (Axy : 𝔻istr Ax Ay) (Ayz : 𝔻istr Ay Az) (Bxy : IndexedDistr Axy Bx By) (Byz : IndexedDistr Ayz By Bz) →
                 IndexedDistr (∘-𝔻istr Axy Ayz) Bx Bz
∘-IndexedDistr {Ax} {Ay} {Az} Bx By Bz Axy Ayz Bxy Byz = record
  { _over_ = λ {ax} {az} axz → ∘-𝔻istr (Bxy over (⊑-up Axy ax)) (Byz over axz)
  ; indexedDistr-naturality =
    λ {ax₁} {ax₂} {az₁} {az₂} ax₁₂ a₂ε a₁ε az₁₂ →
    let Bx-ax₁₂ = (Bx onRel ax₁₂)
        Bxy-ax₂ = (Bxy over ⊑-up Axy ax₂)
        Byz-a₂ε = (Byz over a₂ε)
        Bxy-ax₁ = (Bxy over ⊑-up Axy ax₁)
        By-ax₁₂ = (By onRel  Axy .up .monotone ax₁₂)
    in
    begin
      ∘-𝔻istr Bx-ax₁₂ (∘-𝔻istr Bxy-ax₂ Byz-a₂ε)
      ≡⟨  ∘-∘-𝔻istr Bx-ax₁₂ Bxy-ax₂ Byz-a₂ε  ⟩
      ∘-𝔻istr (∘-𝔻istr Bx-ax₁₂ Bxy-ax₂) Byz-a₂ε
      ≡⟨ PE.cong (λ Bxy → ∘-𝔻istr Bxy Byz-a₂ε) (indexedDistr-naturality Bxy _ _ _ _) ⟩
      ∘-𝔻istr (∘-𝔻istr Bxy-ax₁ By-ax₁₂) Byz-a₂ε
      ≡˘⟨  ∘-∘-𝔻istr Bxy-ax₁ By-ax₁₂ Byz-a₂ε  ⟩
      ∘-𝔻istr Bxy-ax₁ (∘-𝔻istr By-ax₁₂ Byz-a₂ε)
      ≡⟨ PE.cong (λ Byz → ∘-𝔻istr (Bxy over ⊑-up Axy ax₁) Byz) (indexedDistr-naturality Byz _ _ _ _) ⟩
      ∘-𝔻istr (Bxy over ⊑-up Axy ax₁) (∘-𝔻istr (Byz over a₁ε) (Bz onRel az₁₂) )
      ≡⟨ ∘-∘-𝔻istr (Bxy over ⊑-up Axy ax₁) (Byz over a₁ε) (Bz onRel az₁₂) ⟩
      ∘-𝔻istr (∘-𝔻istr (Bxy over ⊑-up Axy ax₁) (Byz over a₁ε)) (Bz onRel az₁₂)
      ∎ }
  where
    open PE.≡-Reasoning
    instance
      PAx = Ax .snd
      PAy = Ay .snd
      PAz = Az .snd

open IsRepresentablePosetDistr

abstract

  ∘-id-𝔻istr-helper : {A : Set} {{PA : Poset A}} {X : ℙoset} (B : IndexedPoset (A , PA)) {a : A} (XBa : 𝔻istr X (B at a)) →
                      ∘-𝔻istr XBa (B onRel refl) ≡ XBa
  ∘-id-𝔻istr-helper {A} {{PA}} B {a} XBa rewrite indexedPoset-refl B a = ∘-id-𝔻istr XBa

  id-∘-𝔻istr-helper : {A : Set} {{PA : Poset A}} {X : ℙoset} (B : IndexedPoset (A , PA)) {a : A} (BaX : 𝔻istr (B at a) X) →
                      ∘-𝔻istr (B onRel refl) BaX ≡ BaX
  id-∘-𝔻istr-helper {A} {{PA}} B {a} BaX rewrite indexedPoset-refl B a = id-∘-𝔻istr BaX

  trans-∘-IndexedDistr : {Ax Ay Az : ℙoset} (Bx : IndexedPoset Ax) (By : IndexedPoset Ay) (Bz : IndexedPoset Az)
                        (Axy : 𝔻istr Ax Ay) (Ayz : 𝔻istr Ay Az) (Bxy : IndexedDistr Axy Bx By) (Byz : IndexedDistr Ayz By Bz) →
                        ∀ {ax ay az} (axy : 𝕕istr Axy ax ay) (ayz : 𝕕istr Ayz ay az)
                          {bx : (Bx at ax) .fst} {by : (By at ay) .fst} {bz : (Bz at az) .fst}
                          (bxy : 𝕕istr (Bxy over axy) bx by) (byz : 𝕕istr (Byz over ayz) by bz) →
                          𝕕istr ((∘-IndexedDistr Bx By Bz Axy Ayz Bxy Byz) over (trans-∘-𝔻istr Axy Ayz axy ayz)) bx bz
  trans-∘-IndexedDistr {Ax} {Ay} {Az} Bx By Bz Axy Ayz Bxy Byz {ax} {ay} {az} axy ayz {bx} {by} {bz} bxy byz = h
    where
      instance
        PAx = Ax .snd
        PAy = Ay .snd
        PAz = Az .snd
        PBx = (Bx at ax) .snd
        PBy = (By at ay) .snd
        PBz = (Bz at az) .snd
        PBux = (By at (Axy ↟ ax)) .snd
      auxy = (up-repr-from Axy axy)
      Hxy' = PE.trans (PE.sym (id-∘-𝔻istr-helper Bx (Bxy over axy)))
                      (indexedDistr-naturality Bxy {ax} {ax} {Axy ↟ ax} {ay} refl axy (⊑-up Axy ax) auxy)
      Hyz' = PE.trans (indexedDistr-naturality Byz {Axy ↟ ax} {ay} {az} {az} auxy ayz (act-left Ayz auxy ayz) refl)
                      (∘-id-𝔻istr-helper Bz (Byz over trans-∘-𝔻istr Axy Ayz axy ayz))
      Hxy = PE.cong (λ dxy → ∘-𝔻istr dxy (Byz over ayz)) Hxy'
      Hyz = PE.cong (λ dyz → ∘-𝔻istr (Bxy over ⊑-up Axy ax) dyz) Hyz'
      H = PE.trans Hxy (PE.trans (PE.sym (∘-∘-𝔻istr (Bxy over ⊑-up Axy ax) (By onRel auxy) (Byz over ayz))) Hyz)
      h = PE.subst id (PE.cong-app (PE.cong-app (PE.cong 𝕕istr H) bx) bz) (trans-∘-𝔻istr (Bxy over axy) (Byz over ayz) bxy byz)


abstract
  up-bot : {A B : Set} {{PA : Poset A}} {{PB : Poset B}}
          (botA : Initial A) (botB : Initial B)
          (AB : Distr A B) {a : A} (ha : is-bot botA a) →
          is-bot botB (up AB .fun a)
  up-bot {{PA}} {{PB}} botA botB AB {a} ha =
    let a-downbot = bot-min botA {b' = down AB .fun (bot botB)} ha
        upa-bot = up-repr-from AB (down-repr-to AB a-downbot)
    in bot-smallest botB upa-bot (bot-is-bot botB)

s𝕕istr : {A B : ℙoset} {AB AB' : 𝔻istr A B} (h : AB ≡ AB') {a : A .fst} {b : B .fst} (ab : 𝕕istr AB a b) → 𝕕istr AB' a b
s𝕕istr h {a} {b} = PE.subst (λ AB → 𝕕istr AB a b) h

abstract
  up-down-lower : {A B : ℙoset} (AB : 𝔻istr A B) (b : B .fst) → _⊑_ {{B .snd}} (AB ↟ (AB ↡ b)) b
  up-down-lower AB b = up-repr-from AB (⊑-down AB b)

  down-up-greater : {A B : ℙoset} (AB : 𝔻istr A B) (a : A .fst) → _⊑_ {{A .snd}} a (AB ↡ (AB ↟ a))
  down-up-greater AB a = down-repr-from AB (⊑-up AB a)


module IndexedDistrHelper {A A' : ℙoset} (Aε : 𝔻istr A A')
                          (B : IndexedPoset A) (B' : IndexedPoset A')
                          (Bε : IndexedDistr Aε B B') where
  private
    instance
      PA = A .snd
      PA' = A' .snd
      PB = λ {a} → (B at a) .snd
      PB' = λ {a'} → (B at a') .snd

    variable
      a₁ a₂ a₃ : A .fst
      a'₁ a'₂ a'₃ : A' .fst
      aε₁ : 𝕕istr Aε a₁ a'₁
      aε₁₂ : 𝕕istr Aε a₁ a'₂
      aε₂ : 𝕕istr Aε a₂ a'₂
      aε₃ : 𝕕istr Aε a₃ a'₃

  abstract
    act-right-compat : {a'₁₂ : _⊑_ {{PA'}} a'₁ a'₂} → ∘-𝔻istr (Bε over aε₁) (B' onRel a'₁₂) ≡ Bε over aε₁₂
    act-right-compat {aε₁₂ = aε₁₂} =
      PE.trans (PE.sym (indexedDistr-naturality Bε refl aε₁₂ _ _))
              (PE.trans (indexedDistr-naturality Bε _ _ _ _)
                        (∘-id-𝔻istr-helper B' _))

    act-left-compat : {a₁₂ : _⊑_ {{PA}} a₁ a₂} → ∘-𝔻istr (B onRel a₁₂) (Bε over aε₂) ≡ Bε over aε₁₂
    act-left-compat {aε₁₂ = aε₁₂} =
      PE.trans (indexedDistr-naturality Bε _ _ aε₁₂ refl)
              (PE.trans (PE.sym (indexedDistr-naturality Bε _ _ _ _))
                        (id-∘-𝔻istr-helper B _))


module DistrHelper {A B C : ℙoset} (AB : 𝔻istr A B) (BC : 𝔻istr B C) where
  private
    instance
      PA : Poset (A .fst)
      PA = A .snd
      PB : Poset (B .fst)
      PB = B .snd
      PC : Poset (C .fst)
      PC = C .snd

    variable
      a : A .fst
      b : B .fst
      c : C .fst

  abstract
    up-left : 𝕕istr (∘-𝔻istr AB BC) a c → 𝕕istr BC (AB ↟ a) c
    up-left = id
    up-right : 𝕕istr AB a b → 𝕕istr (∘-𝔻istr AB BC) a (BC ↟ b)
    up-right {_} {b} ab = act-left BC (up-repr-from AB ab) (⊑-up BC b)

    down-left : 𝕕istr BC b c → 𝕕istr (∘-𝔻istr AB BC) (AB ↡ b) c
    down-left {b} bc = act-left BC (up-down-lower AB b) bc

    down-right : 𝕕istr (∘-𝔻istr AB BC) a c → 𝕕istr AB a (BC ↡ c)
    down-right {a} {c} ac = act-right AB (⊑-up AB a) (down-repr-from BC ac)

abstract
  up-mon : {A B C D : ℙoset}
          (AB : 𝔻istr A B)(BD : 𝔻istr B D)
          (AC : 𝔻istr A C)(CD : 𝔻istr C D)
          {a : A .fst} {c : C .fst}
          (h : ∘-𝔻istr AB BD ≡ ∘-𝔻istr AC CD) (ac : 𝕕istr AC a c) →
            𝕕istr BD (AB ↟ a) (CD ↟ c)
  up-mon AB BD AC CD h ac =
    DistrHelper.up-left AB BD (s𝕕istr (PE.sym h) (DistrHelper.up-right AC CD ac))

  down-mon : {A B C D : ℙoset}
            (AB : 𝔻istr A B)(BD : 𝔻istr B D)
            (AC : 𝔻istr A C)(CD : 𝔻istr C D)
            {b : B .fst} {d : D .fst}
            (h : ∘-𝔻istr AB BD ≡ ∘-𝔻istr AC CD) (bd : 𝕕istr BD b d) →
              𝕕istr AC (AB ↡ b) (CD ↡ d)
  down-mon AB BD AC CD h bd =
    DistrHelper.down-right AC CD (s𝕕istr h (DistrHelper.down-left AB BD bd))


  𝕕istr-hProp : {A B : ℙoset} (d : 𝔻istr A B) → Irrelevant (𝕕istr d)
  𝕕istr-hProp {_ , PA} {_ , PB} d = distr-hProp {{PA}} {{PB}} d

  bot-min-over : {A B : Set} {{PA : Poset A}} {{PB : Poset₀ B}} (✠A : Initial A) (d : Distr A B){b : B} → distr d (bot ✠A) b
  bot-min-over {{PA}} {{PB}} ✠A d {b} = down-repr-to d (bot-min ✠A (bot-is-bot ✠A))

  bot-min-over' : {A B : Set} {{PA : Poset A}} {{PB : Poset₀ B}} (✠A : Initial A) (d : Distr A B){a : A} {b : B} (ha : is-bot ✠A a)  → distr d a b
  bot-min-over' {{PA}} {{PB}} ✠A d {a} {b} ha = down-repr-to d (bot-min ✠A ha)

  top-max-over : {A B : Set} {{PA : Poset₀ A}} {{PB : Poset₀ B}} (?B : Final B) (d : Distr A B){a : A} → distr d a (top ?B)
  top-max-over {{PA}} {{PB}} ?B d = up-repr-to d (top-max ?B (top-is-top ?B))

module _ {A B : Set} {{PA : Poset A}} {{PB : Poset₀ B}}
         (✠A : Initial A) (✠B : Initial B) (d : Distr A B)
         where

  preserves-bot : Prop
  preserves-bot = {b : B} → is-bot ✠B b → is-bot ✠A (d .down .fun b)

  abstract
    distr-smallest : (hpbot : preserves-bot)
                    {a : A}{b : B}(ab : d .distr a b)
                    (hb : ✠B .is-bot b) →
                    ✠A .is-bot a
    distr-smallest hpbot {a} {b} ab hb =
      ✠A .bot-smallest (d .down-repr-from ab) (hpbot hb)
