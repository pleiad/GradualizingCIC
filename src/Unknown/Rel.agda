{-# OPTIONS --without-K --prop --rewriting #-}

open import prelude
open PE hiding (_≡_)
open import Unknown.Core
import Poset as P
import Unknown.Interface as I

module Unknown.Rel (fp : I.familyPack)
                   {{PB : ∀ {c} → P.Poset₀ (I.familyPack.B fp c)}}
                   (✠B : ∀ {c} → P.Initial (I.familyPack.B fp c))
                   where

open I.familyPack fp public

private
  Bε = λ {c} → P._⊑_ {{PB {c}}}
  reflB = λ c {x} → P.refl {{PB {c}}} {x}
  Bε-hprop = λ {c} {x} {y} → P.⊑-hProp  {{PB {c}}} {x} {y}
  is✠ = λ c → P.is-bot (✠B {c})
  ✠min = λ {c} {b} {b'} → P.bot-min (✠B {c}) {b} {b'}
  ✠smallest = λ {c} {b} {b'} → P.bot-smallest (✠B {c}) {b} {b'}

pfp : pointedFamilyPack
pfp = record { fp = fp ; is✠ = is✠ ; is✠-eq = helper }
  where
    helper : (a : A) (b b' : B a) (hb : is✠ a b) (hb' : is✠ a b') → b ≡ b'
    helper c x x' hx hx' = PE.trans (P.is-bot-spec (✠B {c}) hx)
                                    (PE.sym (P.is-bot-spec (✠B {c}) hx'))

open import Unknown.Into pfp public

open UnknownType pfp public

private
  decA-refl : (a : A) → decA a a ≡ yes erefl
  decA-refl a = decEq-refl decA {a} erefl

  decA-neq = decEq-neq decA


uε : unknown → unknown → Set
uε = /rec _ (λ {
  (inj c x) → /rec _ (λ { (inj c' x') → aux c c' x x' ; ?Σ → ⊤ ; ✠Σ → Box (is✠ c x)})
                      λ { a x h✠ → aux-✠ _ _ h✠};
  ?Σ → /rec _ (λ { ?Σ → ⊤ ; _ → Empty}) λ { a x x₁ → erefl };
  ✠Σ → λ _ → ⊤ })
  λ { a x h✠ →
      funext (/elim _ (λ {
        (inj a x) → aux-⊤ _ _ h✠ ;
        ?Σ → erefl ;
        ✠Σ → hpropext Box-hprop ⊤-hprop (λ _ → tt) (λ _ → ⟦ h✠ ⟧)})
        λ { a x h✠ → hProp-hSet Box-hprop ⊤-hprop _ _})}
  where
    aux : (c c' : A) (x : B c) (x' : B c') → Set
    aux c c' x x' with decA c c'
    ... | yes refl = Bε x x'
    ... | no h = Box (is✠ c x)
    aux-✠ : (c c' : A) {x : B c} {x' : B c'} (h✠ : is✠ c' x') → aux c c' x x' ≡ Box (is✠ c x)
    aux-✠ c c' h✠ with decA c c'
    ... | yes refl = hpropext Bε-hprop Box-hprop (λ xε → ⟦ ✠smallest xε h✠ ⟧) λ { ⟦ h✠ ⟧ → ✠min h✠ }
    ... | no h = erefl
    aux-⊤ : (c  c' : A) {x : B c} {x' : B c'} (h✠ : is✠ c x) → aux c c' x x' ≡ ⊤
    aux-⊤ c c' h✠ with decA c c'
    ... | yes refl =  hProp-inhabited Bε-hprop (✠min h✠)
    ... | no h = hProp-inhabited Box-hprop ⟦ h✠ ⟧



u?ε : (u : unknown) → uε u ?u
u?ε = /elim _ (λ { (inj a x) → tt ; ?Σ → tt ; ✠Σ → tt})
            λ { a x x₁ → erefl}

abstract
  private
    refluε : (u : unknown) → uε u u
    refluε = /elim _ aux λ { a x x₁ → erefl }
      where
        aux : (x : Σ⁺ A B) → uε ⦅ x ⦆ ⦅ x ⦆
        aux (inj a x) rewrite decA-refl a = reflB a
        aux ?Σ = tt
        aux ✠Σ = tt

  u?ε-inv : (u : unknown) → uε ?u u → u ≡ ?u
  u?ε-inv = /elim _ (λ { (inj a x) → ⊥-elim ; ?Σ _ → erefl ; ✠Σ → ⊥-elim})
                  λ { a x x₁ → funext (λ())}

  uε-hprop : Irrelevant uε
  uε-hprop {x} {y} = /elim Ptop auxtop
    (λ { _ _ _ → funext (λ _ → funext (λ _ → funext (λ _ → hProp-to-hSet ⊤-hprop _ _)))}) x y
    where
      P = λ (c : A) (x : B c) (y : unknown) → (a b : uε (uinj c x) y) → a ≡ b
      aux : (c : A) (x : B c) (y : Σ⁺ A B) → P c x ⦅ y ⦆
      aux c x (inj c' x') with decA c c'
      ... | yes refl = Bε-hprop
      ... | no h = Box-hprop
      aux c x ?Σ  _ _ = erefl
      aux c x ✠Σ = Box-hprop

      Ptop = (λ x → ∀ (y : unknown) (a b : uε x y) → a ≡ b)
      auxtop : (x : Σ⁺ A B) → Ptop ⦅ x ⦆
      auxtop (inj c x) = /elim (P c x) (aux c x) (λ { _ _ _ → funext (λ _ → funext (λ _ → hProp-to-hSet Box-hprop _ _))})
      auxtop ?Σ y h h' with (u?ε-inv y h)
      auxtop ?Σ y h h' | refl = erefl
      auxtop ✠Σ _ _ _ = erefl

  private
    u✠ε : (u u' : unknown) → is✠u u → uε u u'
    u✠ε u u' h✠ = /elim (λ u → (u' : unknown) → Box (is✠u u) → uε u u')
      (λ { z@(inj c x) u' ⟦ h✠ ⟧ → /elim (λ u' → uε ⦅ z ⦆ u') (λ { (inj c' x') → aux (SquashBox h✠) ; ?Σ → tt ; ✠Σ → ⟦ SquashBox h✠ ⟧})
                      (λ _ _ _ → uε-hprop {⦅ z ⦆} {✠u} _ _) u' ;
            ?Σ _ ⟦ h✠ ⟧ → absurd (SquashBox h✠) ;
            ✠Σ _ _ → tt})
      (λ _ _ _ → funext (λ u' → funext (λ h✠ → uε-hprop {✠u} {u'} _ _))) u u' ⟦ h✠ ⟧
      where
        aux : {c c' : A} {x : B c} {x'  : B c'} (h✠ : is✠ c x) → uε (uinj c x) (uinj c' x')
        aux {c} {c'} h✠ with decA c c'
        ... | yes refl = ✠min h✠
        ... | no h = ⟦ h✠ ⟧


  ?u-dec : RU.Decidable (_≡_ ?u)
  ?u-dec = aux'
    where
      auxBool : unknown → Bool
      auxBool = /rec Bool (λ {?Σ → true ; _ → false}) λ { _ _ _ → erefl }

      sep?u : unknown → Set
      sep?u = /rec _ (λ {?Σ → ⊤ ; _ → Empty}) λ { _ _ _ → erefl }

      Pfalse = (λ u → auxBool u ≡ false → ¬ ?u ≡ u)
      auxfalse : (u : Σ⁺ A B) → Pfalse ⦅ u ⦆
      auxfalse (inj a x) _ eq = subst sep?u eq tt
      auxfalse ?Σ  ()
      auxfalse ✠Σ _ eq = subst sep?u eq tt

      Ptrue = (λ u → auxBool u ≡ true → ?u ≡ u)
      auxtrue : (u : Σ⁺ A B) → Ptrue ⦅ u ⦆
      auxtrue (inj a x) ()
      auxtrue ?Σ _ = erefl
      auxtrue ✠Σ ()

      aux' : RU.Decidable (_≡_ ?u)
      aux' u with auxBool u with inspect auxBool u
      ... | false | [ eq ] = no (/elim Pfalse auxfalse (λ _ _ _ → funext (λ x → funext (λ x₁ → Empty-hprop _ _))) u eq)
      ... | true | [ eq ] = yes ((/elim Ptrue auxtrue (λ { a x x₁ → funext (λ())}) u eq))


  private
    u✠-smallest : (u u' : unknown) → uε u u' → is✠u u' → is✠u u
    u✠-smallest u = unbox (/elim P₀ aux₀ (λ c x h → Box-hprop _ _) u)
      where
        aux : (c c' : A) (x : B c) (x' : B c') (uu' : uε (uinj c x) (uinj c' x')) (h✠ : is✠u (uinj c' x')) → is✠u (uinj c x)
        aux c c' x x' uu' h✠ with decA c c'
        ... | yes refl = toSquashBox (✠smallest uu' (SquashBox h✠))
        ... | no h = ⟦ uu' ⟧'

        aux₁ : (c : A) (x : B c) (u' : Σ⁺ A B) → Box (uε (uinj c x) ⦅ u' ⦆ → is✠u ⦅ u' ⦆ → is✠u (uinj c x))
        aux₁ c x (inj c' x') = ⟦ aux c c' x x' ⟧
        aux₁ _ _ ?Σ = ⟦ (λ _ h✠ → absurdProp (SquashBox h✠)) ⟧
        aux₁ _ _ ✠Σ = ⟦ (λ h✠ _ → ⟦ h✠ ⟧') ⟧

        P₀ = (λ u → Box ((u' : unknown) → uε u u' → is✠u u' → is✠u u))

        aux₀ : (u : Σ⁺ A B) → P₀ ⦅ u ⦆
        aux₀ z@(inj c x) = ⟦ (λ u' → let P = (λ u' → Box (uε ⦅ z ⦆ u' → is✠u u' → is✠u ⦅ z ⦆)) in
                              unbox (/elim P (aux₁ c x) (λ c' x' h' → Box-hprop _ _ ) u')) ⟧
        aux₀ ?Σ = ⟦ (λ u' uu' h✠ → unbox (subst (λ u → Box (is✠u u)) (u?ε-inv u' uu') ⟦ h✠ ⟧))⟧
        aux₀ ✠Σ = ⟦ (λ _ _ _ → is✠✠u) ⟧


  uε-down : {c : A} {x x' : B c} (xx' : Bε x x') (u : unknown) (uu' : uε (uinj c x') u) → uε (uinj c x) u
  uε-down {c} {x} {x'} xx' = /elim P aux λ _ _ _ → funext (λ _ → uε-hprop {uinj c x} {✠u} _ _)
    where
      P = λ (u : unknown) → (uu' : uε (uinj c x') u) → uε (uinj c x) u
      aux : (u : Σ⁺ A B) → P ⦅ u ⦆
      aux (inj c'' x'') with decA c c''
      ... | yes refl = P.trans xx'
      ... | no h = λ uu' → ⟦ (✠smallest xx' (unbox uu')) ⟧
      aux ?Σ _ = u?ε (uinj c x)
      aux ✠Σ uu' = u✠ε (uinj c x) ✠u (toSquashBox (✠smallest xx' (SquashBox (u✠-smallest (uinj c x') ✠u uu' (is✠✠u)))))

  private
    transuε : Transitive uε
    transuε {ux} {uy} {uz} uxy uyz = /elim Ptop auxtop quottop ux uy uz uxy uyz
      where
        Pmid = λ (c : A) (x : B c) (uy : unknown) → (uz : unknown) (uxy : uε (uinj c x) uy) (uyz : uε uy uz) → uε (uinj c x) uz
        auxmid : (c : A) (x : B c) (uy : Σ⁺ A B) → Pmid c x ⦅ uy ⦆
        auxmid c x (inj c' x') with decA c c'
        ... | yes refl = λ uz uxy → uε-down uxy uz
        ... | no h = λ uz h✠ _ → u✠ε (uinj c x) uz ⟦ h✠ ⟧'
        auxmid c x ?Σ uz _ uyz rewrite (u?ε-inv uz uyz) = tt
        auxmid c x ✠Σ uz uxy _ = u✠ε (uinj c x) uz (u✠-smallest (uinj c x) ✠u uxy (is✠✠u))
        quotmid : (c : A) (x : B c) → quot-elim (Pmid c x) (auxmid c x)
        quotmid c x _ _ _ = funext (λ uz → funext (λ _ → funext (λ _ → uε-hprop {uinj c x} {uz} _ _)))

        Ptop = λ (ux : unknown) → (uy uz : unknown) (uxy : uε ux uy) (uyz : uε uy uz) → uε ux uz
        auxtop : (ux : Σ⁺ A B) → Ptop ⦅ ux ⦆
        auxtop (inj c x) = /elim (Pmid c x) (auxmid c x) (quotmid c x)
        auxtop ?Σ uy uz uxy uyz rewrite (u?ε-inv uy uxy) rewrite (u?ε-inv uz uyz) = tt
        auxtop ✠Σ _ uz _ _ = u✠ε ✠u uz (is✠✠u)

        quottop : quot-elim Ptop auxtop
        quottop _ _ _ = funext (λ _ → funext (λ uz → funext (λ _ → funext (λ _ → uε-hprop {✠u} {uz} _ _))))



    uε-antisym : (u u' : unknown) → uε u u' → uε u' u → u ≡ u'
    uε-antisym = /elim Ptop auxtop λ _ _ _ → funext (λ _ → funext (λ _ → funext (λ _ → unknown-hSet _ _)))
      where
        P = λ (c : A) (x : B c) (u' : unknown) → uε (uinj c x) u' → uε u' (uinj c x) → uinj c x ≡ u'
        aux : (c : A) (x : B c) (u' : Σ⁺ A B) → P c x ⦅ u' ⦆
        aux c x (inj c' x') uu' u'u with decA c c'
        ... | yes refl rewrite decA-refl c = cong (uinj c) (P.antisym uu' u'u)
        ... | no h rewrite decA-neq c c' h = trans
            (is✠u-eq (uinj c x) (u✠-smallest (uinj c x) ✠u uu' (is✠✠u)))
            (sym (is✠u-eq (uinj c' x') (u✠-smallest (uinj c' x') ✠u u'u (is✠✠u))))
        aux c x ?Σ _ ()
        aux c x ✠Σ uu' _ = is✠u-eq (uinj c x) (u✠-smallest (uinj c x) ✠u uu' (is✠✠u))

        Ptop = λ (u : unknown) → (u' : unknown) → uε u u' → uε u' u → u ≡ u'
        auxtop : (u : Σ⁺ A B) → Ptop ⦅ u ⦆
        auxtop (inj c x) = /elim (P c x) (aux c x)
                                  λ _ _ _ → funext (λ _ → funext (λ _ → unknown-hSet _ _))
        auxtop ?Σ u' uu' _ rewrite (u?ε-inv u' uu') = erefl
        auxtop ✠Σ u' _ u'u = sym (is✠u-eq u' (u✠-smallest u' ✠u u'u (is✠✠u)))


unknownᵖ : P.Poset₀ unknown
unknownᵖ = record
  { _⊑_ = uε
  ; isPoset = record
  {isPreorder = record
    { isEquivalence = PE.isEquivalence
    ; reflexive = P.Reflexive-respects-≡ uε (λ {x} → refluε x)
    ; trans = λ {i} {j} {k}  → transuε {i} {j} {k} }
    ; antisym = λ {u} {u'} → uε-antisym u u' }
  ; ⊑-hProp = λ {x} {y} → uε-hprop {x} {y}
  ; carrier-hSet = unknown-hSet }

𝕦nknown : P.ℙoset
𝕦nknown = unknown , unknownᵖ

private
  instance
    PUnkown = unknownᵖ

open P using (_⊑_)

uinj-mon : (c : A) {x x' : B c} (xx' : x ⊑ x') → uinj c x ⊑ uinj c x'
uinj-mon c xx' rewrite decA-refl c = xx'

✠unk : P.Initial unknown
✠unk = record
  { bot = ✠u
  ; is-bot = is✠u
  ; is-bot-spec = λ {u} → is✠u-eq u
  ; bot-is-bot = is✠✠u
  ; bot-min = λ {u} {u'} → u✠ε u u'
  ; bot-smallest = λ {u} {u'} → u✠-smallest u u'
  }

?unk : P.Final unknown
?unk = record
  { top = ?u
  ; is-top = λ u → Squash (?u ≡ u)
  ; is-top-spec = λ {u} → spec u
  ; top-is-top = ⟦ erefl ⟧'
  ; top-max = λ {u} {u'} → max-helper {u} {u'}
  ; top-greatest = λ {u} {u'} → greatest-helper u u'
  }
  where
    spec : (u : unknown) → Squash (?u ≡ u) → u ≡ ?u
    spec u pf = sym (Squash-dec ?u-dec {u} pf)
    max-helper : {b b' : unknown} → Squash (?u ≡ b') → uε b b'
    max-helper {u} {u'} pf rewrite spec u' pf = u?ε u
    greatest-helper : (u u' : unknown) → uε u u' → Squash (?u ≡ u) → Squash (?u ≡ u')
    greatest-helper u u' uu' pf rewrite spec u pf = ⟦ sym (u?ε-inv u' uu') ⟧'
