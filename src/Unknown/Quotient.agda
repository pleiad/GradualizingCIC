{-# OPTIONS --without-K --prop --rewriting #-}

module Unknown.Quotient (A : Set) (R : A → A → Set) where

open import Agda.Builtin.Equality.Rewrite public
open import prelude
open PE hiding (_≡_)
open import Relation.Binary.Structures using (IsEquivalence)

postulate _/_ : Set
postulate ⦅_⦆ : A → _/_
postulate quot : ∀ {a a'} → R a a' → ⦅ a ⦆ ≡ ⦅ a' ⦆

/elim-eq-hyp : ∀ {l} (P : _/_ → Set l) (hA : ∀ a → P ⦅ a ⦆) → {a a' : A} → (h : R a a') → Set l
/elim-eq-hyp P hA {a} {a'} h = subst P (quot h) (hA a) ≡ hA a'

postulate /elim : ∀ {l} (P : _/_ → Set l) (hA : ∀ a → P ⦅ a ⦆) (hquot : {a a' : A} (h : R a a') → /elim-eq-hyp P hA h) → (x : _/_) → P x
postulate /elim-⦅⦆ : ∀ {l} (P : _/_ → Set l) hA (hquot : {a a' : A} (h : R a a') → /elim-eq-hyp P hA h) a → /elim P hA hquot ⦅ a ⦆ ≡ hA a

-- can be proved with an univalent universe (see E.Rijke, The join construction)
postulate quot-hSet : hSet A → Irrelevant R → IsEquivalence R → hSet _/_

{-# REWRITE /elim-⦅⦆ #-}

open import Relation.Binary.Construct.Closure.Equivalence as CCEq

module QuotSimpl (qhSet : hSet _/_) (EquivR : IsEquivalence R)
                 (R' : A → A → Set) (toR : R' ⇒ R)  (fromR : R ⇒ EqClosure R')
                 {l : Level} (P : _/_ → Set l) (hA : ∀ a → P ⦅ a ⦆)
                 where

  open import Relation.Binary.Construct.Closure.Symmetric
  open import Relation.Binary.Construct.Closure.ReflexiveTransitive as CCRT

  private
    ER = /elim-eq-hyp P hA

    sym-alg : ∀ {l l'} {A : Set l} {S : Rel A l'} → Symmetric S → SymClosure S ⇒ S
    sym-alg sym (fwd x) = x
    sym-alg sym (bwd y) = sym y

    star-alg : ∀ {l l'} {A : Set l} {RT : Rel A l'} → Reflexive RT → Transitive RT → Star RT ⇒ RT
    star-alg reflRT transRT ε = reflRT
    star-alg reflRT transRT (x ◅ hRT) = transRT x (star-alg reflRT transRT hRT)

    eqcl-alg : ∀ {l l'} {A : Set l} {R : Rel A l'} → IsEquivalence R → EqClosure R ⇒ R
    eqcl-alg record { refl = reflR ; sym = symR ; trans = transR } hR =
      star-alg reflR transR (CCRT.map (sym-alg (λ {x} {y} → symR {x} {y})) hR)

    toR* : EqClosure R' ⇒ R
    toR* = eqcl-alg EquivR ∘ CCEq.map toR

    ERrefl : {a : A} (h : R a a) → ER h
    ERrefl h rewrite (qhSet (quot h) refl) = refl

    ERsym : {a a' : A} (h : R a a') (h' : R a' a) → ER h → ER h'
    ERsym {a} {a'} h h' ih rewrite (qhSet (quot h') (sym (quot h))) =
      sym (begin
        hA a
        ≡˘⟨ subst-sym-subst {P = P} (quot h) ⟩
        subst P (sym (quot h)) (subst P (quot h) (hA a))
        ≡⟨ cong (subst P (sym (quot h))) ih ⟩
        subst P (sym (quot h)) (hA a')
        ∎)
      where
        open ≡-Reasoning

    ERTrans : {a a' a'' : A} (h : R a a') (h' : R a' a'') (h'' : R a a'') → ER h → ER h' → ER h''
    ERTrans {a} {a'} {a''} h h' h'' ih ih' rewrite (qhSet (quot h'') (quot h · quot h')) =
      begin
        subst P (quot h · quot h') (hA a)
        ≡⟨ subst-· P (quot h) (quot h') (hA a) ⟩
        subst P (quot h') (subst P (quot h) (hA a))
        ≡⟨ cong (subst P (quot h')) ih ⟩
        subst P (quot h') (hA a')
        ≡⟨ ih' ⟩
        hA a''
      ∎
      where
        open ≡-Reasoning


    liftER : ({a a' : A} (h : R' a a') → ER (toR h)) → {a a' : A} (h* : EqClosure R' a a') → ER (toR* h*)
    liftER f ε = ERrefl _
    liftER f (fwd x ◅ h*) = ERTrans _ _ _ (f x) (liftER f h*)
    liftER f (bwd y ◅ h*) = ERTrans (IsEquivalence.sym EquivR (toR y)) _ _ (ERsym _ _ (f y)) (liftER f h*)


    liftER-toER : {a a' : A} (h : R a a') → ER (toR* (fromR h)) → ER h
    liftER-toER h rewrite (qhSet (quot (toR* (fromR h))) (quot h)) = id

  qsimpl : ({a a' : A} (h : R' a a') → ER (toR h)) → {a a' : A} (h : R a a') → ER h
  qsimpl f h = liftER-toER h (liftER f (fromR h))


postulate /elimProp : ∀ {l} (P : _/_ → Prop l) (hA : ∀ (a : A) → P ⦅ a ⦆) → (x : _/_) → P x


J₂ : ∀ {l l'} {A B : Set l} {a : A} {b : B} (P : {a' : A} {b' : B} (eqA : a ≡ a') (eqB : b ≡ b') → Set l')
     (hP : P refl refl) {a' : A} {b' : B} (eqA : a ≡ a') (eqB : b ≡ b') → P eqA eqB
J₂ P hP refl refl = hP

transp₂ : ∀ {l l'} {A B : Set l} (P : A → B → Set l') {a a' : A} {b b' : B} (eqA : a ≡ a') (eqB : b ≡ b') → P a b → P a' b'
transp₂ P refl refl = id



/rec : ∀ {l} (P : Set l) (hA : A → P) (hquot : ∀ {a a'} (h : R a a') → hA a ≡ hA a') → _/_ → P
/rec P hA hquot = /elim (λ _ → P) hA λ h → trans (subst-const (quot h)) (hquot h)

