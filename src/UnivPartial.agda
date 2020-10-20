{-# OPTIONS --without-K --prop #-}

open import prelude

open import Relation.Binary.Core
open import Relation.Binary.Structures
import Relation.Binary.Bundles as RBB using (Poset)

open import Poset

open import nat
open import bool
open import top
open import pi
open import Unknown.Interface
open import GroundTypes

open import Data.Nat using (_≟_)

module UnivPartial (build-unknown : UnknownBuilder) where


private
  variable
    i : Nat



-- Declaration of the universe of codes U

data U : Nat → Set
data Uε : Rel (U i) lzero
reflUε : Reflexive (Uε {i})
transUε : Transitive (Uε {i})
{-# TERMINATING #-}
Uε-hprop : Irrelevant (Uε {i})
antisymUε : Antisymmetric _≡_ (Uε {i})

{-# TERMINATING #-}
U-hSet : hSet (U i)

Uᵖ : Poset (U i)
Uᵖ {i} = record
  { _⊑_ = Uε {i}
  ; isPoset = record
    { isPreorder = record
      { isEquivalence = PE.isEquivalence
      ; reflexive = Reflexive-respects-≡ Uε reflUε
      ; trans = transUε }
    ; antisym = antisymUε }
  ; ⊑-hProp = Uε-hprop
  ; carrier-hSet = U-hSet }

𝕌 : Nat → ℙoset
𝕌 i = U i , Uᵖ

✠𝕌 : Initial (U i) {{Uᵖ}}
?𝕌 : Final (U i) {{Uᵖ}}

-- Declaration of the decoding function El

{-# TERMINATING #-}
𝕖l : U i → ℙoset
𝔼lε : {A B : U i} (AB : Uε A B) → 𝔻istr (𝕖l A) (𝕖l B)
𝔼lε-refl : (A : U i) → 𝔼lε (reflUε {_} {A}) ≡ id-𝔻istr (𝕖l A)
𝔼lε-trans : {A B C : U i} (AB : Uε A B) (BC : Uε B C) →
  𝔼lε (transUε AB BC) ≡ ∘-𝔻istr (𝔼lε AB) (𝔼lε BC)

𝔼l : IndexedPoset (𝕌 i)
𝔼l = record
  { _at_ = 𝕖l
  ; _onRel_ = 𝔼lε
  ; indexedPoset-refl = 𝔼lε-refl
  ; indexedPoset-trans = 𝔼lε-trans
  }

open IndexedPoset

El : U i → Set
El A = 𝕖l A .fst

Elᵖ : (A : U i) → Poset (El A)
Elᵖ A = 𝕖l A .snd

Elε : {A B : U i} (AB : Uε A B) → REL (El A) (El B) lzero
Elε AB = 𝕕istr (𝔼l onRel AB)

Rel-transp : {A B : Set} {R R' : REL A B lzero} (H : R ≡ R') {a : A} {b : B} → R a b → R' a b
Rel-transp H {a} {b} = PE.subst (λ R → R a b) H

Elε-reflUε : {A : U i} {a a' : El A} →  Elε reflUε a a' → _⊑_ {{Elᵖ A}} a a'
Elε-reflUε {A = A} = Rel-transp (PE.cong 𝕕istr (𝔼lε-refl A))

Elε-reflUε-inv : {A : U i} {a a' : El A} → _⊑_ {{Elᵖ A}} a a' →  Elε reflUε a a'
Elε-reflUε-inv {A = A} {a} {a'} = Rel-transp (PE.sym (PE.cong 𝕕istr (𝔼lε-refl A)))


El-hSet : {A : U i} → hSet (El A)


-- Declaration of decoding of "ground types"

hasℂ : (U i) → Prop
𝕔[_] : {A : U i} → hasℂ {i} A → ℂ i
ℂtoU : ℂ i → U i

U[_] : {A : U i} → hasℂ {i} A → U i
U[ hasc ] = ℂtoU 𝕔[ hasc ]

Elℂ : ℂ i → Set
Elℂ = El ∘ ℂtoU

Elℂ-hSet : (c : ℂ i) → hSet (Elℂ c)
Elℂ-hSet c = El-hSet

ℂtoUε : (c : ℂ i) → Uε (ℂtoU c) (ℂtoU c)
ℂtoUε c = reflUε {x = ℂtoU c}

Elℂε : (c : ℂ i) → Rel (Elℂ c) lzero
Elℂε = Elε ∘ ℂtoUε

Elℂᵖ : {c : ℂ i} → Poset₀ (Elℂ c)
Elℂᵖ {c = c} = Elᵖ (ℂtoU c)

𝔼lℂ : (c : ℂ i) → ℙoset
𝔼lℂ c = 𝔼l at (ℂtoU c)

-- Smallest and greatest elements

private
  variable
    A B C : U i
    a : El A
    b : El B
    c : El C


✠El : (A : U i) → Initial (El A) {{Elᵖ A}}

✠' : (A : U i) → El A
✠' A = bot {{Elᵖ A}} (✠El A)

is✠ : (A : U i) → El A → Prop
is✠ A = is-bot {{Elᵖ A}} (✠El A)

down✠ : (AB : Uε {i} A B) {b : El B} → is✠ B b → is✠ A (𝔼lε AB ↡ b)

is✠✠ : (A : U i) → is✠ A (✠' A)
is✠✠ A = bot-is-bot {{Elᵖ A}} (✠El A)


✠ℂ : {c : ℂ i} → Initial (Elℂ c) {{Elℂᵖ}}
✠ℂ {c = c} = ✠El (ℂtoU c)

is✠ℂ : (c : ℂ i) → Elℂ c → Prop
is✠ℂ c x = is✠ (ℂtoU c) x

?El : (A : U i) → Final (El A) {{𝕖l A .snd}}

??' : (A : U i) → El A
??' A = top {{Elᵖ A}} (?El A)


-- constructing the dynamic type associated to the family (ℂ ; 𝔼lℂ)

ℂfp : (i : Nat) → familyPack
ℂfp i = record { A = ℂ i ; B = Elℂ ; decA = _≟ℂ_ ; hSetB = Elℂ-hSet }

unk : BuildUnknown (ℂfp i) {{Elℂᵖ}} ✠ℂ
unk {i} = build-unknown (ℂfp i) {{Elℂᵖ}} ✠ℂ

open module B {i : Nat} = BuildUnknown {ℂfp i} {{Elℂᵖ}} {✠ℂ} (unk {i})


iDiD : ∀ {i} (A : U i) (c : ℂ i) (AB : Uε A (ℂtoU c)) → intoDistrData (ℂfp i) {{Elℂᵖ}} ✠ℂ c
iDiD {i = i} A c AB = record
  { X = El A
  ; PX = Elᵖ A
  ; ✠X = ✠El A
  ; ?X = ?El A
  ; XB = 𝔼lε AB
  ; down✠ = down✠ AB }

--

open IndexedPoset

open Distr
open PosetDistr.IsRepresentablePosetDistr



-- Implementation of the universe of codes


{-# NO_POSITIVITY_CHECK #-}
data U where
  nat : U i
  bool : U i
  ?U : U i
  ✠U : U i
  π : (A : U i) → (B : (𝔼l at A) ⟶ 𝕌 i) → U i
  𝕦 : ∀ {j} {j<i : Squash (j < i)} → U i


𝔻𝕌 : 𝔻istr (𝕌 i) (𝕌 i)
𝔻𝕌 {i} = id-𝔻istr (𝕌 i)

{-# NO_POSITIVITY_CHECK #-}
data Uε where
  natε : Uε {i} nat nat
  boolε : Uε {i} bool bool
  ??ε : Uε {i} ?U ?U
  ℂ?ε : {A : U i} {hasc : hasℂ A} → Uε A U[ hasc ] → Uε A ?U
  ✠Uε : {A : U i} → Uε {i} ✠U A
  𝕦ε : ∀ {j} {j<i : Squash (j < i)} → Uε (𝕦 {i} {j} {j<i}) (𝕦 {i} {j} {j<i})
  πε : ∀ {i} {A A' : U i} {B B'} → (Aε : Uε A A') →
             (Bε : (𝔼lε Aε ⟶ε 𝔻𝕌) B B') →
             Uε (π A B) (π A' B')

-- implementation of the correspondance between ground types and types

ℂtoU ℂnat = nat
ℂtoU ℂbool = bool
ℂtoU ℂπ = π ?U ((λ x → ?U) , λ aa' → ??ε)
ℂtoU (ℂ𝕦 {i} {j} {j<i}) = 𝕦 {i} {j} {j<i}

open import Data.Maybe
open import MaybeProp

Utoℂ : (A : U i) → Maybe (ℂ i)
Utoℂ nat = just ℂnat
Utoℂ bool = just ℂbool
Utoℂ ?U = nothing
Utoℂ ✠U = nothing
Utoℂ (π A B) = just ℂπ
Utoℂ (𝕦 {i} {j} {j<i}) = just (ℂ𝕦 {i} {j} {j<i})

hasℂ = just? ∘ Utoℂ


𝕔[ hasc ] = just?v _ hasc


-- Poset structure on the universe U

reflUε {_} {nat} = natε
reflUε {_} {bool} = boolε
reflUε {_} {?U} = ??ε
reflUε {_} {✠U} = ✠Uε
reflUε {_} {π A B} = πε reflUε (B .snd ∘ Elε-reflUε)
reflUε {_} {𝕦} = 𝕦ε

transUε natε natε = natε
transUε natε (ℂ?ε BC) = ℂ?ε {hasc = ⟨⟩} (transUε natε BC)
transUε boolε boolε = boolε
transUε boolε (ℂ?ε BC) = ℂ?ε {hasc = ⟨⟩} (transUε boolε BC)
transUε ??ε ??ε = ??ε
transUε AB@(ℂ?ε _) ??ε = AB
transUε ✠Uε BC = ✠Uε
transUε 𝕦ε (ℂ?ε BC) = ℂ?ε {hasc = ⟨⟩} (transUε 𝕦ε BC)
transUε 𝕦ε 𝕦ε = 𝕦ε
transUε AB@(πε ABdom ABcod) (ℂ?ε BC) = ℂ?ε {hasc = ⟨⟩} (transUε AB BC)
transUε (πε {A = A} {B = B} ABdom ABcod) (πε {A' = A''} {B' = B''} BCdom BCcod) =
  πε ACdom ACcod
  where
    ACdom = transUε ABdom BCdom
    open Distr
    instance
      PA : Poset (El A)
      PA = Elᵖ A
      PA'' : Poset (El A'')
      PA'' = Elᵖ A''
    ACcod : {a : El A} {a'' : El A''} (aε : Elε ACdom a a'') → Uε (B .fst a) (B'' .fst a'')
    ACcod {a} {a''} aε = transUε (ABcod (⊑-up (𝔼lε ABdom) a))
      (BCcod (Rel-transp (PE.cong 𝕕istr (𝔼lε-trans ABdom BCdom)) aε ))

𝕦𝕦ε-elim : {i : Nat} {j j' : Nat} {j<i : Squash (j < i)} {j'<i : Squash (j' < i)} (AB : Uε (𝕦 {i} {j} {j<i}) (𝕦 {i} {j'} {j'<i})) →
  Σ[ h ∈ j ≡ j' ] AB ≡ J (λ (j' : Nat) (eq : j ≡ j') → Uε (𝕦 {i} {j} {j<i}) (𝕦 {i} {j'} {substProp (λ j' → Squash (j' < i)) eq j<i})) h 𝕦ε
𝕦𝕦ε-elim 𝕦ε = erefl , erefl

Uε-hprop {x = .nat} {y = .nat} natε natε = erefl
Uε-hprop {x = .bool} {y = .bool} boolε boolε = erefl
Uε-hprop {x = .?U} {y = .?U} ??ε ??ε = erefl
Uε-hprop {x = A} {y = .?U} (ℂ?ε AB) (ℂ?ε AB') = PE.cong ℂ?ε (Uε-hprop AB AB')
Uε-hprop {x = .✠U} {y = B} ✠Uε ✠Uε = erefl
Uε-hprop {x = .𝕦} {y = .𝕦} (𝕦ε {j = j}) AB' with 𝕦𝕦ε-elim AB'
... | (h , h') rewrite hedberg _≟_ h erefl rewrite h' = erefl
Uε-hprop {x = .(π _ _)} {y = .(π _ _)} (πε ABdom ABcod) (πε ABdom' ABcod') rewrite (Uε-hprop ABdom ABdom') =
  PE.cong (πε ABdom') (funext-impl (funext-impl (funext (λ ab → Uε-hprop (ABcod ab) (ABcod' ab)))))

antisymUε natε natε = erefl
antisymUε boolε boolε = erefl
antisymUε ??ε ??ε = erefl
antisymUε (ℂ?ε {hasc = ()} AB) ??ε
antisymUε (ℂ?ε {hasc = ()} AB) (ℂ?ε BA)
antisymUε ✠Uε ✠Uε = erefl
antisymUε 𝕦ε BA with 𝕦𝕦ε-elim BA
... | (h , h') rewrite hedberg _≟_ h erefl rewrite h' = erefl
antisymUε (πε {A' = Bdom} {Acod} {Bcod} ABdom ABcod) (πε BAdom BAcod) with antisymUε ABdom BAdom
... | erefl = PE.cong (π _) (⟶-ext {A = 𝕖l Bdom} {𝕌 _} Acod Bcod
  λ (a : El Bdom) → antisymUε (ABcod (aε ABdom a)) (BAcod (aε BAdom a)))
  where
    aε = λ AB a → PE.subst (λ AB → Elε AB a a) (Uε-hprop (refl {{Uᵖ}}) AB)
                     (Elε-reflUε-inv (refl {{𝕖l Bdom .snd}}))

✠𝕌 = record
  { bot = ✠U
  ; is-bot = λ { ✠U → 𝟙 ; _ → 𝟘 }
  ; is-bot-spec = λ { {✠U} h → erefl }
  ; bot-is-bot = ⟨⟩
  ; bot-min = λ { {✠U} hbot → ✠Uε}
  ; bot-smallest = λ { {.✠U} {✠U} ✠Uε hbot → ⟨⟩}
  }

U?ε : Uε A ?U
U?ε {A = nat} = ℂ?ε {hasc = ⟨⟩} natε
U?ε {A = bool} = ℂ?ε {hasc = ⟨⟩} boolε
U?ε {A = ?U} = ??ε
U?ε {A = ✠U} = ✠Uε
U?ε {A = π A B} = ℂ?ε {hasc = ⟨⟩} (πε U?ε (λ aε → U?ε))
U?ε {A = 𝕦} = ℂ?ε {hasc = ⟨⟩} 𝕦ε

?𝕌 = record
  { top = ?U
  ; is-top = λ { ?U → 𝟙 ; _ → 𝟘 }
  ; is-top-spec = λ { {?U} h → erefl }
  ; top-is-top = ⟨⟩
  ; top-max = λ { {b} {?U} h → U?ε}
  ; top-greatest = λ { {?U} {.?U} ??ε h → ⟨⟩ }
  }

--------------------------------------------------------------------------------
-- Implementation of the interpretation of codes as posets                 --
--------------------------------------------------------------------------------

𝕖l nat = ℕ , ℕᵖ
𝕖l bool = 𝔹 , 𝔹ᵖ
𝕖l {i} ?U = unknownType {i}
𝕖l ✠U = ⊤ , ⊤ᵖ
𝕖l (π A B) = Π' (𝕖l A) (pullback B 𝔼l)
𝕖l (𝕦 {j = j}) = 𝕌 j


✠El nat = ✠ℕ'
✠El bool = ✠𝔹'
✠El ?U = ✠unk
✠El ✠U = ✠⊤
✠El (π A B) = Limits.✠Π (𝕖l A) (pullback B 𝔼l) (✠El ∘ (B .fst))
✠El 𝕦 = ✠𝕌

?El nat = ?ℕ'
?El bool = ?𝔹'
?El ?U = ?unk
?El ✠U = ?⊤
?El (π A B) = Limits.?Π (𝕖l A) (pullback B 𝔼l) (?El ∘ (B .fst))
?El 𝕦 = ?𝕌


𝔼lε {A = A} natε = id-𝔻istr (𝕖l A)
𝔼lε {A = A} boolε = id-𝔻istr (𝕖l A)
𝔼lε {A = A} ??ε = id-𝔻istr (𝕖l A)
𝔼lε {A = A} (ℂ?ε {hasc = hasc} AB) = intoDistr (iDiD A 𝕔[ hasc ] AB)
𝔼lε {B = A} ✠Uε = ⊤ε-Distr.⊤-distr {El A} {{Elᵖ A}} (✠' A) λ a → bot-min {{Elᵖ A}} (✠El A) {b' = a} (bot-is-bot {{Elᵖ A}} (✠El A))
𝔼lε {A = A} 𝕦ε = id-𝔻istr (𝕖l A)
𝔼lε {A = A} (πε {A = Adom} {Bdom} {Acod} {Bcod} ABdom ABcod) =
  let
    Bx = pullback Acod 𝔼l
    By = pullback Bcod 𝔼l
    Axy = 𝔼lε ABdom
    Bxy = indexed-pullback Axy 𝔻𝕌 Acod Bcod ABcod 𝔼l 𝔼l (id-IndexedDistr 𝔼l)
  in Π𝔻istr Bx By Axy Bxy

down✠ natε {b} h = h
down✠ boolε {b} h = h
down✠ ??ε {b} h = h
down✠ {A = A} (ℂ?ε {hasc = hasc} AB) {b} h = intoDistr-down✠ (iDiD A 𝕔[ hasc ] AB) {b} h
down✠ ✠Uε {b} h = ⟨⟩
down✠ 𝕦ε {b} h = h
down✠ (πε ABdom ABcod) {f} h = λ a → let b = (𝔼lε ABdom) ↟ a in down✠ (ABcod (⊑-up (𝔼lε ABdom) a)) {f .fst b} (h b)




𝔼lε-refl nat = erefl
𝔼lε-refl bool = erefl
𝔼lε-refl ?U = erefl
𝔼lε-refl ✠U = 𝔻istr-ext _ _ (λ a b → erefl)
𝔼lε-refl (π A B) = 𝔻istr-ext _ _
  (λ f g → PE.cong-app (PE.cong-app (Πε-ext {𝕒} {𝕒} 𝕓 𝕓 Aε Aε' Bε Bε' IHAε IHBε) f) g)
  where
    𝕒 = 𝕖l A
    𝕓 = pullback B 𝔼l
    𝔸ε = 𝔼lε (reflUε {x = A})
    Aε = 𝕕istr 𝔸ε
    Aε' = 𝕕istr (id-𝔻istr 𝕒)
    IHAε = PE.cong 𝕕istr (𝔼lε-refl A)

    Bε = toIndexedPREL 𝔸ε 𝕓 𝕓 (indexed-pullback 𝔸ε 𝔻𝕌 B B (B .snd ∘ (Rel-transp IHAε)) 𝔼l 𝔼l (id-IndexedDistr 𝔼l))
    Bε' = id-toIndexedPREL 𝕓

    IHBε : {a a' : 𝕒 .fst} (aε : Aε' a a') → Bε (Rel-transp (PE.sym IHAε) aε) ≡ Bε' aε
    IHBε {a} {a'} aε =
      PE.subst (λ aε₀ → 𝕕istr (𝔼lε (B .snd aε₀)) ≡ 𝕕istr (𝔼lε (B .snd aε))) (PE.sym (PE.subst-subst-sym (PE.cong 𝕕istr (𝔼lε-refl A)) {p = aε})) erefl
𝔼lε-refl 𝕦 = erefl


module helper-𝔼lε-ℂ?ε where

  Uε-hasℂ : (AB : Uε {i} A B) (hascA : hasℂ A) (hascB : hasℂ B) → 𝕔[ hascA ] ≡ 𝕔[ hascB ]
  Uε-hasℂ natε hascA hascB = erefl
  Uε-hasℂ boolε hascA hascB = erefl
  Uε-hasℂ 𝕦ε hascA hascB = erefl
  Uε-hasℂ (πε AB Bε) hascA hascB = erefl

  tr-ℂtoU : {cx cy : ℂ i} (cxy : cx ≡ cy) (Ax : Uε {i} A (ℂtoU cx)) → Uε A (ℂtoU cy)
  tr-ℂtoU {A = A} = PE.subst (λ c → Uε A (ℂtoU c))

  transUε-tr-ℂtoU : {cx cy : ℂ i} (cxy : cx ≡ cy)
                    (AB : Uε {i} A B) (BC : Uε B (ℂtoU cx)) →
                    transUε AB (tr-ℂtoU cxy BC) ≡ tr-ℂtoU cxy (transUε AB BC)
  transUε-tr-ℂtoU erefl AB BC = erefl

  Uε-changeℂ : (AB : Uε {i} A B) (hascA : hasℂ A) (hascB : hasℂ B) (B? : Uε {i} B U[ hascB ]) → Uε B U[ hascA ]
  Uε-changeℂ {B = B} AB hascA hascB = tr-ℂtoU (PE.sym (Uε-hasℂ AB hascA hascB))

  transUε-ℂ?ε : (AB : Uε {i} A B) (hascA : hasℂ A) (hascB : hasℂ B) (B? : Uε {i} B U[ hascB ]) →
    transUε AB (ℂ?ε {hasc = hascB} B?) ≡ ℂ?ε {hasc = hascA} (transUε AB (Uε-changeℂ AB hascA hascB B?))
  transUε-ℂ?ε natε hascA hascB B? = erefl
  transUε-ℂ?ε boolε hascA hascB B? = erefl
  transUε-ℂ?ε 𝕦ε hascA hascB B? = erefl
  transUε-ℂ?ε (πε AB Bε) hascA hascB B? = erefl

  module _ where
    open module iDD {i} = intoDistrData {ℂfp i} {{λ {c} → Elℂᵖ {c = c}}} {λ {c} → ✠ℂ {c = c}}
    subst-iDiD-helper : {cx cy : ℂ i} (cxy : cx ≡ cy) (Ax : Uε A (ℂtoU cx)) →
                        PE.subst (λ c → 𝔻istr (𝔼l at A) (𝔼lℂ c)) cxy (iDiD A cx Ax .XB) ≡ iDiD A cy (PE.subst (λ c → Uε A (ℂtoU c)) cxy Ax) .XB
    subst-iDiD-helper erefl Ax = erefl

𝔼lε-trans-ℂ?ε : (AB : Uε {i} A B) (hascA : hasℂ A) (hascB : hasℂ B)
                (B? : Uε {i} B U[ hascB ])
                (IH : 𝔼lε (transUε AB B?) ≡ ∘-𝔻istr (𝔼lε AB) (𝔼lε B?)) →
  𝔼lε (transUε AB (ℂ?ε {hasc = hascB} B?)) ≡ ∘-𝔻istr (𝔼lε AB) (𝔼lε (ℂ?ε {hasc = hascB} B?))
𝔼lε-trans-ℂ?ε {i = i} {A = A} {B = B} AB hascA hascB BC IH
  rewrite helper-𝔼lε-ℂ?ε.transUε-ℂ?ε AB hascA hascB BC =
  PE.trans (PE.cong (λ AC → intoDistr (iDiD A 𝕔[ hascA ] AC)) (transUε-tr-ℂtoU (PE.sym ceq) AB BC))
           (intoCompat iDA iDB iDAB)
  where
    open helper-𝔼lε-ℂ?ε
    ceq = Uε-hasℂ AB hascA hascB
    AC' : Uε A U[ hascA ]
    AC' = tr-ℂtoU (PE.sym ceq) (transUε AB BC)
    iDA = iDiD A 𝕔[ hascA ] AC'
    iDB = iDiD B 𝕔[ hascB ] BC
    iDAB : intoDistrCompat (ℂfp i) {{λ {c} → Elℂᵖ {c = c}}} _ iDA iDB
    iDAB = record
      { cxy = ceq
      ; distr = 𝔼lε AB
      ; down✠ = down✠ AB
      ; distr-eq = PE.trans (PE.trans (subst-iDiD-helper ceq AC')
                                      (PE.cong 𝔼lε (PE.subst-subst-sym ceq)))
                            IH }


𝔼lε-trans natε natε = PE.sym (id-∘-𝔻istr _)
𝔼lε-trans {A = A@(.nat)} natε (ℂ?ε {hasc = hasc} AB@natε) = 𝔼lε-trans-ℂ?ε natε ⟨⟩ hasc natε (PE.sym (id-∘-𝔻istr _))
𝔼lε-trans boolε boolε = PE.sym (id-∘-𝔻istr _)
𝔼lε-trans {A = A} boolε (ℂ?ε {hasc = hasc} AB@boolε) = 𝔼lε-trans-ℂ?ε boolε ⟨⟩ hasc boolε (PE.sym (id-∘-𝔻istr _))
𝔼lε-trans ??ε ??ε = PE.sym (id-∘-𝔻istr (𝔼lε ??ε))
𝔼lε-trans (ℂ?ε AB) ??ε = PE.sym (∘-id-𝔻istr _)
𝔼lε-trans {B = B} {C} ✠Uε BC =
  𝔻istr-ext _ _ (λ _ _ → hpropext ⊤-hprop (𝕕istr-hProp (𝔼lε BC))
    (λ _ → bot-min-over {{Elᵖ B}} {{Elᵖ C}} (✠El B) (𝔼lε BC))
     λ _ → tt)
𝔼lε-trans AB@𝕦ε (ℂ?ε {hasc = hasc} BC) = 𝔼lε-trans-ℂ?ε AB ⟨⟩ hasc BC (𝔼lε-trans AB BC)
𝔼lε-trans 𝕦ε 𝕦ε = PE.sym (id-∘-𝔻istr _)
𝔼lε-trans {A = A} {B} AB@(πε ABdom ABcod) (ℂ?ε {hasc = hasc} BC) = 𝔼lε-trans-ℂ?ε AB ⟨⟩ hasc BC (𝔼lε-trans AB BC)
𝔼lε-trans AB@(πε {A = Adom} {Bdom} {Acod} {Bcod} ABdom ABcod) BC@(πε {A' = Cdom} {B' = Ccod} BCdom BCcod) =
  𝔻istr-ext _ _ (λ f h →
    hpropext (𝕕istr-hProp (𝔼lε AC) {f} {h})
             (𝕕istr-hProp (∘-𝔻istr (𝔼lε AB) (𝔼lε BC)) {f} {h})
             (part1 f h) (part2 f h))
  where
    AC = transUε AB BC
    part1 : ∀ f h → Elε (transUε AB BC) f h → 𝕕istr (∘-𝔻istr (𝔼lε AB) (𝔼lε BC)) f h
    part1 f h fh {b} {c} bc =
      let a = 𝔼lε ABdom ↡ b
          b' = 𝔼lε ABdom ↟ a
          b'c = act-left {{Elᵖ Bdom}} {{Elᵖ Cdom}} (𝔼lε BCdom) (up-down-lower (𝔼lε ABdom) b) bc
          ab'c = trans-∘-𝔻istr (𝔼lε ABdom) (𝔼lε BCdom) (⊑-up (𝔼lε ABdom) a) b'c
          ac' = Rel-transp (PE.sym (PE.cong 𝕕istr (𝔼lε-trans ABdom BCdom))) ab'c

          ABcod' = ABcod (⊑-up (𝔼lε ABdom) a)
          BCcod' = BCcod (Rel-transp (PE.cong 𝕕istr (𝔼lε-trans ABdom BCdom)) ac')
          ABcod = ABcod (⊑-down (𝔼lε ABdom) b)
          BCcod = BCcod bc
          xε = PE.subst (λ AC → Elε AC (f .fst a) (h .fst c))
                        (Uε-hprop (transUε ABcod' BCcod')
                                  (transUε ABcod BCcod))
                        (fh ac')
      in  Rel-transp (PE.cong 𝕕istr (𝔼lε-trans ABcod BCcod)) xε

    part2 : ∀ f h  → 𝕕istr (∘-𝔻istr (𝔼lε AB) (𝔼lε BC)) f h → Elε (transUε AB BC) f h
    part2 f h fh {a} {c} ac =
      let ac' = Rel-transp (PE.cong 𝕕istr (𝔼lε-trans ABdom BCdom)) ac
          ABcod' = ABcod (⊑-up (𝔼lε ABdom) a)
          BCcod' = BCcod ac'
          xε = trans-∘-𝔻istr (𝔼lε ABcod') (𝔼lε BCcod')
                             (⊑-up (𝔼lε AB) f (⊑-up (𝔼lε ABdom) a)) (fh ac')
      in
       Rel-transp (PE.sym (PE.cong 𝕕istr (𝔼lε-trans ABcod' BCcod'))) xε

-----------------------------------------------------------------------
-- properties of ?? and ✠                                            --
-----------------------------------------------------------------------


-- TODO : these definitions should be reworked to be private
isπ : U i → Set
isπ (π _ _) = ⊤
isπ _ = Empty

eqΣ : ∀ (A A' : U i) (B : (𝔼l at A) ⟶  𝕌 i) (B' : (𝔼l at A') ⟶ 𝕌 i) → Set
eqΣ {i} A A' B B' = Σ[ h ∈ A ≡ A' ] PE.subst (λ X → (𝔼l at X) ⟶ 𝕌 i) h B ≡ B'

πeqΣ : ∀ {A A' B B'} → π {i} A B ≡ π A' B' → eqΣ A A' B B'
πeqΣ erefl = erefl , erefl

πeqΣinv : ∀ {A A' B B'} → eqΣ {i} A A' B B' → π A B ≡ π A' B'
πeqΣinv ( erefl , erefl ) = erefl

πeqΣ-id : ∀ {A A' B B'} (h : π {i} A B ≡ π A' B') → h ≡ πeqΣinv (πeqΣ h)
πeqΣ-id erefl = erefl

πeqΣ-inj : ∀ {A A' B B'} (h h' : π {i} A B ≡ π A' B') → πeqΣ h ≡ πeqΣ h' → h ≡ h'
πeqΣ-inj h h' hh' = PE.trans (πeqΣ-id h) (PE.trans (PE.cong πeqΣinv hh') (PE.sym (πeqΣ-id h')))

A⟶U-hSet : (A : U i) → hSet (𝕖l A ⟶ 𝕌 i)
A⟶U-hSet {i} _ = Σ-hset (∀-hSet (λ a → U-hSet {i})) ((λ f → ∀impl-hSet (∀impl-hSet (∀-hSet (λ _ → hProp-to-hSet (Uε-hprop))))))

Elε-hprop : {A B : U i} (AB : Uε A B) → Irrelevant (Elε AB)
Elε-hprop {A = A} {B} AB = distr-hProp (isDistr {{Elᵖ A}} {{Elᵖ B}} (𝔼lε AB))


U-hSet {_} {nat} {B} = local-hedberg nat aux
  where
    aux : RU.Decidable (_≡_ (nat {i}))
    aux nat = yes erefl
    aux bool = no λ()
    aux ?U = no λ()
    aux ✠U = no λ()
    aux (π c B) = no λ()
    aux 𝕦 = no λ()
U-hSet {_} {bool} {B} = local-hedberg bool aux
  where
    aux : RU.Decidable (_≡_ (bool {i}))
    aux bool = yes erefl
    aux nat = no λ()
    aux ?U = no λ()
    aux ✠U = no λ()
    aux (π c B) = no λ()
    aux 𝕦 = no λ()
U-hSet {_} {?U} {B} = local-hedberg ?U aux
  where
    aux : RU.Decidable (_≡_ (?U {i}))
    aux ?U = yes erefl
    aux nat = no λ()
    aux bool = no λ()
    aux ✠U = no λ()
    aux (π c B) = no λ()
    aux 𝕦 = no λ()
U-hSet {_} {✠U} {B} = local-hedberg ✠U aux
  where
    aux : RU.Decidable (_≡_ (✠U {i}))
    aux ✠U = yes erefl
    aux nat = no λ()
    aux bool = no λ()
    aux ?U = no λ()
    aux (π c B) = no λ()
    aux 𝕦 = no λ()
U-hSet {i} {π A B} {π A' B'} h h' with πeqΣ h with PE.inspect πeqΣ h with πeqΣ h' with PE.inspect πeqΣ h'
... | (h₁ , h₂) | PE.[ eqh ] | (h'₁ , h'₂) | PE.[ eqh' ] rewrite U-hSet h₁ h'₁ rewrite A⟶U-hSet A' h₂ h'₂ =
  πeqΣ-inj h h' (PE.trans eqh (PE.sym eqh'))
U-hSet {_} {π A B₁} {nat} eq = ⊥-elim (PE.subst isπ eq tt)
U-hSet {_} {π A B₁} {bool} eq = ⊥-elim (PE.subst isπ eq tt)
U-hSet {_} {π A B₁} {?U} eq = ⊥-elim (PE.subst isπ eq tt)
U-hSet {_} {π A B₁} {✠U} eq = ⊥-elim (PE.subst isπ eq tt)
U-hSet {_} {π A B₁} {𝕦} eq = ⊥-elim (PE.subst isπ eq tt)
U-hSet {_} {X@(𝕦 {j = j})} {B} = local-hedberg X aux
  where
    aux : RU.Decidable (_≡_ X)
    aux Y@(𝕦 {j = j'}) with j ≟ j'
    ... | yes erefl = yes erefl
    ... | no h = no (h ∘ aux')
      where
        aux' : X ≡ Y → j ≡ j'
        aux' erefl = erefl
    aux nat = no λ()
    aux bool = no λ()
    aux ✠U = no λ()
    aux (π c B) = no λ()
    aux ?U = no λ()

El-hSet {A = nat} = hedberg (decℕ)
El-hSet {A = bool} = hedberg (dec𝔹)
El-hSet {i} {A = ?U} = unknown-hSet
El-hSet {A = ✠U} = hedberg dec⊤
  where
    dec⊤ : DecidableEquality ⊤
    dec⊤ tt tt = yes erefl
El-hSet {i} {A = π A B} =
  Σ-hset (∀-hSet (λ a → El-hSet {A = B .fst a})) ((λ f → ∀impl-hSet (∀impl-hSet (∀-hSet (λ aε → hProp-to-hSet (Elε-hprop (B .snd aε)))))))
El-hSet {A = 𝕦} = U-hSet

