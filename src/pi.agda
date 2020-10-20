{-# OPTIONS --without-K --prop #-}
module pi where

open import prelude

import Relation.Unary as RU

open import Relation.Binary.Core
open import Relation.Binary.Structures
import Relation.Binary.Bundles as RBB using (Poset)

open import Poset

-- Negative Π

open Distr
open IndexedPoset


Π₀ : {l l' : Level} → (A : Set l) → (B : A → Set l') → Set (l ⊔ l')
Π₀ A B = ∀ a → B a

module RelΠ₀ {A A' : Set} {B : A → Set} {B' : A' → Set}
            (Aε : A → A' → Set)
            (Bε : ∀ {a a'} (aε : Aε a a') → B a → B' a' → Set) where

  Πε₀ : Π₀ A B → Π₀ A' B' → Set
  Πε₀ f f' = ∀ {a a'} (aε : Aε a a') → Bε aε (f a) (f' a')

  Πε₀-hprop : (∀ {a a'} (aε : Aε a a') → Irrelevant (Bε aε)) → Irrelevant Πε₀
  Πε₀-hprop BIrr f f' = funext-impl λ {a} → funext-impl (λ {a'} → funext (λ aε → BIrr aε (f aε) (f' aε)))


Π : (A : ℙoset) (B : IndexedPoset A) → Set
Π (A , PA) B =
  let B' a = (B at a) .fst in
  let instance
        PA : Poset A
        PA = PA
        PB : ∀ {a} → Poset (B' a)
        PB {a} = (B at a) .snd
  in Σ[ f ∈ (∀ (a : A) → B' a) ] ∀ {a a'} (aa' : a ⊑ a') → distr (B onRel aa') (f a) (f a')


Π-ext : (A : ℙoset) (B : IndexedPoset A) (f g : Π A B) (Heq : (a : A .fst) → f .fst a ≡ g .fst a) → f ≡ g
Π-ext A B (f , monf) (g , mong) Heq rewrite (funext Heq) =
  PE.cong (_,_ g) (funext-impl (funext-impl (funext (λ aa' → distr-hProp {{(B at _) .snd}} {{(B at _) .snd}} (B onRel aa') (monf aa') (mong aa')))))

infix 8 _⟶_

_⟶_ : (A B : ℙoset) → Set
A ⟶ B = Π A (trivialIndexedPoset A B)

⟶-ext : {A B : ℙoset} (f g : A ⟶ B) (Heq : (a : A .fst) → f .fst a ≡ g .fst a) → f ≡ g
⟶-ext {A} {B} = Π-ext A (trivialIndexedPoset A B)


Πε : {A A' : ℙoset} (B : IndexedPoset A) (B' : IndexedPoset A')
     (Aε : PREL A A') (Bε : IndexedPREL B B' Aε) →
     REL (Π A B) (Π A' B') lzero
Πε _ _ Aε Bε f g = RelΠ₀.Πε₀ Aε Bε (f .fst) (g .fst)

_⟶ε_ : {A A' B B' : ℙoset} (Aε : 𝔻istr A A') (Bε : 𝔻istr B B') → REL (A ⟶ B) (A' ⟶ B') lzero
_⟶ε_ {A} {A'} {B} {B'} Aε Bε = Πε (trivialIndexedPoset A B) (trivialIndexedPoset A' B') (𝕕istr Aε) λ aa' → 𝕕istr Bε


Πε-ext : {A A' : ℙoset} (B : IndexedPoset A) (B' : IndexedPoset A')
        (Aε Aε' : PREL A A') (Bε : IndexedPREL B B' Aε) (Bε' : IndexedPREL B B' Aε')
        (HA : Aε ≡ Aε') (HB : ∀ {a} {a'} (aε : Aε' a a') → Bε (PE.subst (λ R → R a a') (PE.sym HA) aε) ≡ Bε' aε) →
        Πε B B' Aε Bε ≡ Πε B B' Aε' Bε'
Πε-ext B B' Aε Aε' Bε Bε' erefl HB = PE.cong (Πε B B' Aε) {Bε} {Bε'} (funext-impl (funext-impl (funext HB)))

Πε-hprop : {A A' : ℙoset} (B : IndexedPoset A) (B' : IndexedPoset A')
           (Aε : PREL A A') (Bε : IndexedPREL B B' Aε) →
           (∀ {a a'} (aε : Aε a a') → Irrelevant (Bε aε)) →
           Irrelevant (Πε B B' Aε Bε)
Πε-hprop _ _ Aε Bε BIrr = RelΠ₀.Πε₀-hprop Aε Bε BIrr


reflΠε : {A : ℙoset} (B : IndexedPoset A) →
         Reflexive (Πε B B (_⊑_ {{A .snd}}) (id-toIndexedPREL B))
reflΠε _ {f} = f .snd

id-transΠε : {A : ℙoset} (B : IndexedPoset A) →
          Transitive (Πε B B (_⊑_ {{A .snd}}) (id-toIndexedPREL B))
id-transΠε {A} B {f} {g} {h} fg gh {a} {a'} aa'  = act-right ⦃ (B at a) .snd ⦄ ⦃ (B at a') .snd ⦄
                                     (B onRel aa') (fg aa') gha'
        where
          instance
            PBa' : Poset ((B at a') .fst)
            PBa' = (B at a') .snd
          gha' : g .fst a' ⊑ h .fst a'
          gha' = PE.subst (λ d → distr d (g .fst a') (h .fst a')) (indexedPoset-refl B a') (gh (refl {{A .snd}} {a'}))

antisymΠε : (A : ℙoset) (B : IndexedPoset A) → Antisymmetric _≡_ (Πε B B (𝕕istr (id-𝔻istr A)) (id-toIndexedPREL B))
antisymΠε A B {f} {g} fg gf = Π-ext A B f g ext
  where
    helper = λ a x y → PE.subst (λ R → 𝕕istr R x y) (indexedPoset-refl B a)
    ext : (a : A .fst) → f .fst a ≡ g .fst a
    ext a = let ra = refl {{A .snd}} in antisym {{(B at a) .snd}} (helper a (f .fst a) (g .fst a) (fg ra)) (helper a (g .fst a) (f .fst a) (gf ra))

Πᵖ : (A : ℙoset) (B : IndexedPoset A) → Poset₀ (Π A B)
Πᵖ A B = record
  { _⊑_ = Πε B B Aε Bε
  ; isPoset = record
    { isPreorder = record
      { isEquivalence = PE.isEquivalence
      ; reflexive = Reflexive-respects-≡ (Πε B B Aε Bε) (λ {f} → reflΠε B {f})
      ; trans = λ {f} {g} {h} → id-transΠε B {f} {g} {h} }
    ; antisym = antisymΠε A B }
  ; ⊑-hProp = λ {f} {g} →
    Πε-hprop B B Aε Bε
             (λ aε a b → distr-hProp {{(B at _) .snd}} {{(B at _) .snd}} (id-IndexedDistr B IndexedDistr.over aε) a b)
             {f} {g}
  ; carrier-hSet =
      Σ-hset (∀-hSet (λ a → carrier-hSet {{(B at a) .snd}}))
            λ f → hProp-to-hSet
              λ p₁ p₂ → funext-impl (funext-impl (funext (λ aε →
                  distr-hProp {{(B at _) .snd}}
                              {{(B at _) .snd}}
                              (B onRel aε) _ _)))}
  where
    Aε = 𝕕istr (id-𝔻istr A)
    Bε = id-toIndexedPREL B

infix 8 _⟶ᵖ_

_⟶ᵖ_ : (A B : ℙoset) → Poset₀ (A ⟶ B)
A ⟶ᵖ B = Πᵖ A (trivialIndexedPoset A B)


module Limits (A : ℙoset) (B : IndexedPoset A) where
  private
    instance
      PΠ : Poset (Π A B)
      PΠ = Πᵖ A B
      PA : Poset (A .fst)
      PA = A .snd
      PB : ∀ {a} → Poset ((B at a) .fst)
      PB {a} = (B at a) .snd


  ✠Π : (✠B : (a : A .fst) → Initial ((B at a) .fst)) → Initial (Π A B)
  ✠Π ✠B = record
    { bot = ✠π
    ; is-bot = is✠π
    ; is-bot-spec = λ {f} h → Π-ext A B f ✠π (λ a → is-bot-spec (✠B a) {f .fst a} (h a))
    ; bot-is-bot = λ a → bot-is-bot (✠B a)
    ; bot-min = λ hbot aε → down-repr-to (B onRel aε) (bot-min (✠B _) (hbot _))
    ; bot-smallest = λ {b} {b'} bb' hbot a →
      bot-smallest (✠B a)
         (PE.subst (λ d → 𝕕istr d (b .fst a) (b' .fst a)) (indexedPoset-refl B a) (bb' refl))
         (hbot a)
    }
    where
    ✠π : Π A B
    ✠π = (λ a → bot (✠B a)), λ {a} aε → bot-min-over (✠B a) (B onRel aε)
    is✠π : Π A B → Prop
    is✠π f = (a : A .fst) → is-bot (✠B a) (f .fst a)

  ?Π : ((a : A .fst) → Final ((B at a) .fst)) → Final (Π A B)
  ?Π ?B = record
    { top = top ∘ ?B , λ {_} {a} aε → top-max-over (?B a) (B onRel aε)
    ; is-top = λ f → (a : A .fst) → is-top (?B a) (f .fst a)
    ; is-top-spec = λ {f} h → Π-ext A B f _ (λ a → is-top-spec (?B a) {f .fst a} (h a))
    ; top-is-top = λ a → top-is-top (?B a)
    ; top-max = λ htop aε → up-repr-to (B onRel aε) (top-max (?B _) (htop _))
    ; top-greatest = λ {f} {g} fg htop a → top-greatest (?B a)
                   (PE.subst (λ d → 𝕕istr d (f .fst a) (g .fst a)) (indexedPoset-refl B a) (fg refl)) (htop a)
    }


✠⟶ : (A B : ℙoset) (✠B : 𝕀nitial B) → Initial (A ⟶ B) {{A ⟶ᵖ B}}
✠⟶ A B ✠B = Limits.✠Π A (trivialIndexedPoset A B) (λ _ → ✠B)


Π' : (A : ℙoset) (B : IndexedPoset A) → ℙoset
Π' A B = Π A B , Πᵖ A B


transΠε : {Ax Ay Az : ℙoset} (Bx : IndexedPoset Ax) (By : IndexedPoset Ay) (Bz : IndexedPoset Az)
          (Axy : 𝔻istr Ax Ay) (Ayz : 𝔻istr Ay Az) (Bxy : IndexedDistr Axy Bx By) (Byz : IndexedDistr Ayz By Bz) →
          ∀ {f g h} → Πε Bx By (𝕕istr Axy) (toIndexedPREL Axy Bx By Bxy) f g → Πε By Bz (𝕕istr Ayz) (toIndexedPREL Ayz By Bz Byz) g h →
          Πε Bx Bz (𝕕istr (∘-𝔻istr Axy Ayz)) (toIndexedPREL _ _ _ (∘-IndexedDistr Bx By Bz Axy Ayz Bxy Byz)) f h
transΠε Bx By Bz Axy Ayz Bxy Byz {f} {g} {h} fg gh {ax} {az} auxz =
  let axux = (⊑-up Axy ax)
      fgax = fg axux
      ghaxz = gh auxz
  in PE.subst (λ axz → toIndexedPREL (∘-𝔻istr Axy Ayz) Bx Bz (∘-IndexedDistr Bx By Bz Axy Ayz Bxy Byz) axz (f .fst ax) (h .fst az))
              (trans-∘-𝔻istr-up Axy Ayz auxz)
              (trans-∘-IndexedDistr Bx By Bz Axy Ayz Bxy Byz axux auxz fgax ghaxz)

⟶-on-refl : {A B : ℙoset} (f : A ⟶ B) (a : A .fst) →
               f .snd (refl {{A .snd}})  ≡ refl {{B .snd}} {f .fst a}
⟶-on-refl {A} {B , PB} f a = ⊑-hProp {{PB}} _ _

⟶-on-trans : {A : Set} {{PA : Poset A}} {B : ℙoset} (f : (A , PA) ⟶ B) {a b c : A} (ab : a ⊑ b) (bc : b ⊑ c) →
               f .snd (trans ab bc)  ≡ trans {{B .snd}} (f .snd ab) (f .snd bc)
⟶-on-trans {A} {B , PB} f ab bc = ⊑-hProp {{PB}} _ _


-- composition of a monotone function f : A → B (seen as a functor) and a functor X : B → Distr
pullback : {A B : ℙoset} (f : A ⟶ B) (X : IndexedPoset B) → IndexedPoset A
pullback {A} {B} f X = record
  { _at_ = λ a → X at (f .fst a)
  ; _onRel_ = λ aε → X onRel (f .snd aε)
  ; indexedPoset-refl = aux-refl
  ; indexedPoset-trans = aux-trans
  }
  where
    instance
      PA = A .snd
      PB = B .snd
    aux-refl : (a : A .fst) → (X onRel f .snd refl) ≡ id-𝔻istr (X at f .fst a)
    aux-refl a rewrite ⟶-on-refl {A} {B} f a = indexedPoset-refl X _
    aux-trans : {a b c : A .fst} (ab : a ⊑ b) (bc : b ⊑ c) →
                (X onRel f .snd (trans ab bc)) ≡
                ∘-𝔻istr (X onRel f .snd ab) (X onRel f .snd bc)
    aux-trans ab bc rewrite ⟶-on-trans {A .fst} {B} f ab bc =
      indexedPoset-trans X _ _

⇒-Poset-to-⟶ : {A B : Set} {{PA : Poset A}} {{PB : Poset B}}
                   (f : A ⇒-Poset B) → ((A , PA) ⟶ (B , PB))
⇒-Poset-to-⟶ f = fun f , monotone f
  where
    open _⇒-Poset_

indexed-pullback : {A A' B B' : ℙoset} (Aε : 𝔻istr A A') (Bε : 𝔻istr B B')
                   (f : A ⟶ B) (f' : A' ⟶ B') (fε : (Aε ⟶ε Bε) f f')
                   (X : IndexedPoset B) (X' : IndexedPoset B') (Xε : IndexedDistr Bε X X') →
                   IndexedDistr  Aε (pullback f X) (pullback f' X')
indexed-pullback {A} {A'} {B} {B'} Aε Bε f f' fε X X' Xε = record
  { _over_ = λ aε → Xε over (fε aε)
  ; indexedDistr-naturality = λ a₁₂ a₂ε a₁ε a'₁₂ → indexedDistr-naturality Xε (f .snd a₁₂) (fε a₂ε) (fε a₁ε) (f' .snd a'₁₂) }
  where
    open IndexedDistr

-- (f : Π A B) (f' : Π A' B') (Aε 𝔻istr A A') (X : IndexedPoset B) → IndexedPoset A {a a'} (aε : a ⊑ a') IndexedDistr (B a)


module Π-Distr {Adom Bdom : ℙoset}
               (Acod : IndexedPoset Adom) (Bcod : IndexedPoset Bdom)
               (ABdom : 𝔻istr Adom Bdom) (ABcod : IndexedDistr ABdom Acod Bcod)
               where

  Πdistr = Πε Acod Bcod (𝕕istr ABdom) (toIndexedPREL ABdom Acod Bcod ABcod)

  private
    instance
      PiA : Poset (Π Adom Acod)
      PiA = (Π' Adom Acod) .snd
      PiB : Poset (Π Bdom Bcod)
      PiB = (Π' Bdom Bcod) .snd
      PAdom : Poset (Adom .fst)
      PAdom = Adom .snd
      PBdom : Poset (Bdom .fst)
      PBdom = Bdom .snd
      PAcod : {a : Adom .fst} → Poset ((Acod at a) .fst)
      PAcod {a} = (Acod at a) .snd
      PBcod : ∀ {a} → Poset ((Bcod at a) .fst)
      PBcod {b} = (Bcod at b) .snd

  open PosetDistr (Π Adom Acod) (Π Bdom Bcod) Πdistr
  open IndexedDistr

  ΠPosetDistr : PosetDistr
  ΠPosetDistr = record
    { act-left =  λ {f} {g} {h} fg gh {a} {b} ab →
      let aε = down-repr-from ABdom ab
          a'b = ⊑-down ABdom b
          hA = IndexedDistrHelper.act-left-compat ABdom Acod Bcod ABcod
      in s𝕕istr hA (trans-∘-𝔻istr (Acod onRel aε) (ABcod over a'b) (fg aε) (gh a'b))
      -- so long for loosy abstract arguments...
      -- transΠε Acod Acod Bcod (id-𝔻istr Adom) ABdom
      --         (id-IndexedDistr Acod) ABcod
      --         {f} {g} {h}
      --         (λ {a} {a'} aε → fg aε) (λ {a'} {b} a'b → gh a'b)
    ; act-right = λ {f} {g} {h} fg gh {a} {b} ab →
      let bε = up-repr-from ABdom ab
          ab' = ⊑-up ABdom a
          hB = IndexedDistrHelper.act-right-compat ABdom Acod Bcod ABcod
      in s𝕕istr hB (trans-∘-𝔻istr (ABcod over ab') (Bcod onRel bε)
                                    (fg ab') (gh bε))
    ; distr-hProp = λ {f} {g} →
      Πε-hprop Acod Bcod (𝕕istr ABdom)
               (toIndexedPREL ABdom Acod Bcod ABcod)
               (λ aε a b → distr-hProp (ABcod over aε) a b)
               {f} {g} }

  open _⇒-Poset_
  up₀ : Π Adom Acod → Π Bdom Bcod
  up₀ f = (λ b → (ABcod over (⊑-down ABdom b)) ↟ (f .fst (ABdom ↡ b))) ,
          λ {b} {b'} bε → up-mon (ABcod over ⊑-down ABdom b)
                                  (Bcod onRel bε)
                                  (Acod onRel (down ABdom .monotone bε))
                                  (ABcod over ⊑-down ABdom b')
                                  (PE.sym (indexedDistr-naturality ABcod _ _ _ _))
                                  (f .snd (down ABdom .monotone bε))

  up₀-mon : _⊑_ =[ up₀ ]⇒ _⊑_
  up₀-mon fg {b} {b'} bε =
    up-mon (ABcod over ⊑-down ABdom b)
            (Bcod onRel bε)
            (Acod onRel (down ABdom .monotone bε))
            (ABcod over ⊑-down ABdom b')
            (PE.sym (indexedDistr-naturality ABcod _ _ _ _))
            (fg (down ABdom .monotone bε))

  updef : (Π' Adom Acod) ⇒-ℙoset (Π' Bdom Bcod)
  updef = record { fun = up₀ ; monotone = λ {f} {g} → up₀-mon {f} {g} }

  down₀ : Π Bdom Bcod → Π Adom Acod
  down₀ f =
    (λ a → (ABcod over ⊑-up ABdom a) ↡ (f .fst (ABdom ↟ a))),
    λ {a} {a'} aε → down-mon (ABcod over ⊑-up ABdom a)
                              (Bcod onRel (up ABdom .monotone aε))
                              (Acod onRel aε)
                              (ABcod over ⊑-up ABdom a')
                              (PE.sym (indexedDistr-naturality ABcod _ _ _ _))
                              (f .snd (up ABdom .monotone aε))

  down₀-mon :  _⊑_ =[ down₀ ]⇒ _⊑_
  down₀-mon fg {a} {a'} aε =
    down-mon (ABcod over ⊑-up ABdom a)
              (Bcod onRel (up ABdom .monotone aε))
              (Acod onRel aε)
              (ABcod over ⊑-up ABdom a')
              (PE.sym (indexedDistr-naturality ABcod _ _ _ _))
              (fg (up ABdom .monotone aε))

  downdef : (Π' Bdom Bcod) ⇒-ℙoset (Π' Adom Acod)
  downdef = record { fun = down₀ ; monotone = λ {f} {g} → down₀-mon {f} {g} }

  ΠLeftRepresentable : LeftRepresentable
  ΠLeftRepresentable = record
    { up = updef
    ; up-repr-from = λ {f} {g} fg {b} bε →
      let ab = act-right ABdom (⊑-down ABdom b) bε
          h = PE.sym (IndexedDistrHelper.act-right-compat ABdom Acod Bcod ABcod)
      in
      DistrHelper.up-left (ABcod over (⊑-down ABdom b)) (Bcod onRel bε)
                          (s𝕕istr h (fg ab))
    ; up-repr-to = λ {f} {g} fg {a} {b} ab →
      let bε = up-repr-from ABdom ab
          aε = down-up-greater ABdom a
          xε = act-right ABdom (⊑-down ABdom (ABdom ↟ a)) bε
          hB = IndexedDistrHelper.act-right-compat ABdom Acod Bcod ABcod
          hA = IndexedDistrHelper.act-left-compat ABdom Acod Bcod ABcod
          AB = ABcod over (⊑-down ABdom (ABdom ↟ a))
          part1 = f .snd aε
          part2 = ⊑-up AB (f .fst (ABdom ↡ (ABdom ↟ a)))
          part3 = fg bε
      in s𝕕istr hA (trans-∘-𝔻istr (Acod onRel aε) (ABcod over xε)
                                  part1
                                  (s𝕕istr hB (trans-∘-𝔻istr AB (Bcod onRel bε)
                                                            part2 part3))) }

  ΠRightRepresentable : RightRepresentable
  ΠRightRepresentable = record
    { down = downdef
    ; down-repr-from = λ {f} {g} fg {a} {a'} aε →
      let ab = act-left ABdom aε (⊑-up ABdom a')
          h = PE.sym (IndexedDistrHelper.act-left-compat ABdom Acod Bcod ABcod)
      in DistrHelper.down-right (Acod onRel aε) (ABcod over (⊑-up ABdom a'))
                                  (s𝕕istr h (fg ab))
    ; down-repr-to = λ {f} {g} fg {a} {b} ab →
      let aε = down-repr-from ABdom ab
          bε = up-down-lower ABdom b
          xε = act-left ABdom aε (⊑-up ABdom (ABdom ↡ b))
          hB = IndexedDistrHelper.act-right-compat ABdom Acod Bcod ABcod
          hA = IndexedDistrHelper.act-left-compat ABdom Acod Bcod ABcod
          AB = ABcod over (⊑-up ABdom (ABdom ↡ b))
          part1 = fg aε
          part2 = ⊑-down AB (g .fst (ABdom ↟ (ABdom ↡ b)))
          part3 = g .snd bε
      in s𝕕istr hB (trans-∘-𝔻istr (ABcod over xε) (Bcod onRel bε)
                                  (s𝕕istr hA (trans-∘-𝔻istr (Acod onRel aε) AB
                                                            part1 part2))
                                  part3)}

  -- this postulate hold up to troubles with dependent rewrite
  -- downdef (updef f) a ≡ ↡↟ (f (↡↟ a)) by definition of updef/downdef
  --                     ≡ ↡↟ (f a)      by section-retraction property of ABdom
  --                     ≡ f a          by section-retraction property of ABcod (this only holds up to the previous equation)
  postulate sect-retr-Π : (f : (Π' Adom Acod) .fst) (a : Adom .fst) → (downdef .fun (updef .fun f)) .fst a ≡ f .fst a

  Π𝔻istr : 𝔻istr (Π' Adom Acod) (Π' Bdom Bcod)
  Π𝔻istr = record
    { distr = Πdistr
    ; isDistr = record
      { isPosetDistr = ΠPosetDistr
      ; isLeftRepresentable = ΠLeftRepresentable
      ; isRightRepresentable = ΠRightRepresentable
      }
    ; up-down-inverseˡ =
      λ f → Π-ext Adom Acod _ _
        (λ a → sect-retr-Π f a) }


open Π-Distr public using (Π𝔻istr)
