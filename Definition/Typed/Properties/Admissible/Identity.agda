------------------------------------------------------------------------
-- Admissible rules related to identity types
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Admissible.Identity
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Modality 𝕄
open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties.Admissible.Equality R
import Definition.Typed.Properties.Admissible.Identity.Primitive
open import Definition.Typed.Properties.Admissible.Pi R
open import Definition.Typed.Properties.Admissible.Var R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Reasoning.Term R
open import Definition.Typed.Stability R
open import Definition.Typed.Substitution.Primitive R
open import Definition.Typed.Weakening R
open import Definition.Typed.Well-formed R

open import Definition.Untyped M as U
open import Definition.Untyped.Identity 𝕄
open import Definition.Untyped.Properties M

open import Tools.Fin
open import Tools.Function
open import Tools.Level
open import Tools.Nat as N using (Nat; 1+; 2+; 3+)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

open Definition.Typed.Properties.Admissible.Identity.Primitive R public

private variable
  m n                           : Nat
  Η                             : Cons _ _
  A₁ A₂ B₁ B₂ t t₁ t₂ u u₁ u₂ v : Term _
  p p′ p″ q q′ q″               : M
  b                             : BinderMode
  l l₁ l₂                       : Universe-level

------------------------------------------------------------------------
-- Some preservation lemmas

private opaque

  -- A variant of the J rule.

  J′ :
    ∀ {a p} {A : Set a} {x y : A}
    (P : ∀ y → x PE.≡ y → Set p) →
    P x PE.refl →
    (x≡y : x PE.≡ y) →
    P y x≡y
  J′ _ p PE.refl = p

  -- The following code illustrates roughly how ΠΣ-cong-Idˡ below is
  -- defined.

  Π-cong-Idˡ′ :
    ∀ {a b} →
    Function-extensionality a (lsuc b) →
    {A₁ A₂ : Set a} {B₁ : A₁ → Set b} {B₂ : A₂ → Set b} →
    (A₁≡A₂ : A₁ PE.≡ A₂) →
    ((x : A₁) → B₁ x PE.≡ B₂ (PE.subst (λ A → A) A₁≡A₂ x)) →
    ((x : A₁) → B₁ x) PE.≡ ((x : A₂) → B₂ x)
  Π-cong-Idˡ′ {b} fe {A₁} {A₂} {B₁} {B₂} A₁≡A₂ B₁≡B₂ =
    J′ (λ A₂ A₁≡A₂ →
          {B₂ : A₂ → Set b} →
          ((x : A₁) → B₁ x PE.≡ B₂ (PE.subst (λ A → A) A₁≡A₂ x)) →
          ((x : A₁) → B₁ x) PE.≡ ((x : A₂) → B₂ x))
       (λ {B₂} B₁≡B₂ →
          PE.cong (λ B → (x : A₁) → B x) {x = B₁} {y = B₂}
            (ext {A = A₁} {P = λ _ → Set b} {f = B₁} {g = B₂} fe B₁≡B₂))
       A₁≡A₂ B₁≡B₂

opaque
  unfolding Has-function-extensionality Funext

  -- Allowed Π- and Σ-types preserve propositional equality in a
  -- certain sense, assuming that a certain form of function
  -- extensionality can be proved (and that certain Π-types are
  -- allowed).

  ΠΣ-cong-Idˡ :
    {Γ : Cons m n} →
    ΠΣ-allowed b p q →
    Π-allowed p′ q′ →
    Π-allowed p″ q″ →
    Has-function-extensionality p′ q′ p″ q″ l₁ (1+ l₂) Γ →
    Γ »∙ A₂ ⊢ B₂ ∷ U l₂ →
    Γ ⊢ t ∷ Id (U l₁) A₁ A₂ →
    Γ »∙ A₁ ⊢ u ∷
      Id (U l₂) B₁
        (B₂ [ cast l₁ (wk1 A₁) (wk1 A₂) (wk1 t) (var x0) ]↑) →
    ∃ λ v →
      Γ ⊢ v ∷
        Id (U (l₁ ⊔ᵘ l₂)) (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁)
          (ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂)
  ΠΣ-cong-Idˡ
    {n} {b} {p} {q} {p′} {q′} {p″} {q″} {l₁} {l₂}
    {A₂} {B₂} {t} {A₁} {u} {B₁} {Γ}
    ok ok′ ok″ (ext , ⊢ext) ⊢B₂ ⊢t ⊢u =
    J-app ∘⟨ p″ ⟩ lam p′ B₂ ∘⟨ p″ ⟩ lam p′ u , ⊢J∘∘
    where
    opaque
      ⊢A₁ : Γ ⊢ A₁ ∷ U l₁
      ⊢A₁ = inversion-Id (wf-⊢∷ ⊢t) .proj₂ .proj₁

    opaque
      ⊢A₂ : Γ ⊢ A₂ ∷ U l₁
      ⊢A₂ = inversion-Id (wf-⊢∷ ⊢t) .proj₂ .proj₂

    opaque
      ⊢B₁ : Γ »∙ A₁ ⊢ B₁ ∷ U l₂
      ⊢B₁ = inversion-Id (wf-⊢∷ ⊢u) .proj₂ .proj₁

    opaque
      ∙⊢Id : Γ »∙ U l₁ ⊢ Id (U l₁) (wk1 A₁) (var x0)
      ∙⊢Id = Idⱼ′ (wkTerm₁ (wf-⊢∷ ⊢A₁) ⊢A₁) (var₀ (wf-⊢∷ ⊢A₁))

    opaque
      ∙²⊢ΠU :
        Γ »∙ U l₁ »∙ Id (U l₁) (wk1 A₁) (var x0) ⊢
        Π p′ , q′ ▷ var x1 ▹ U l₂
      ∙²⊢ΠU = ΠΣⱼ (Uⱼ (∙ univ (var₁ ∙⊢Id))) ok′

    opaque
      ∙³⊢A₁ :
        Γ »∙ U l₁ »∙ Id (U l₁) (wk1 A₁) (var x0) »∙
        Π p′ , q′ ▷ var x1 ▹ U l₂ ⊢
        wk[ 3 ] A₁
      ∙³⊢A₁ =
        PE.subst (_⊢_ _) (PE.sym wk[]≡wk[]′) $
        _⊢_.univ $ wkTerm (ʷ⊇-drop (∙ ∙²⊢ΠU)) ⊢A₁

    ΠId : ∀ k → (_ _ _ : Term (1+ (k N.+ n))) → Term (k N.+ n)
    ΠId k C D t =
      Π p′ , q′ ▷ wk[ k ] A₁ ▹
      Id (U l₂) (B₁ [ 1+ k ][ var x0 ]↑)
        (C ∘⟨ p′ ⟩ cast l₁ (wk[ 1+ k ]′ A₁) D t (var x0))

    opaque
      ⊢ΠId :
        {k : Nat} {Δ : Con Term (k N.+ n)}
        {C D t : Term (1+ (k N.+ n))} →
        drop k Δ PE.≡ Γ .vars →
        Γ .defs » Δ ∙ wk[ k ] A₁ ⊢ C ∷ Π p′ , q′ ▷ D ▹ U l₂ →
        Γ .defs » Δ ∙ wk[ k ] A₁ ⊢ t ∷ Id (U l₁) (wk[ 1+ k ]′ A₁) D →
        Γ .defs » Δ ⊢ ΠId k C D t
      ⊢ΠId {k} {Δ} PE.refl ⊢C ⊢t =
        flip _⊢_.ΠΣⱼ ok′ $
        Idⱼ′ (subst-⊢∷ ⊢B₁ (⊢ˢʷ∷-[][]↑ (var₀ (univ ⊢wk[k]A₁∷))))
          (⊢C ∘ⱼ
           ⊢cast ⊢t
             (PE.subst (_⊢_∷_ _ _) wk[]≡wk[]′ $
              var₀ (univ ⊢wk[k]A₁∷)))
        where
        ⊢wk[k]A₁∷ : Γ .defs » Δ ⊢ wk[ k ] A₁ ∷ U l₁
        ⊢wk[k]A₁∷ =
          PE.subst₂ (_⊢_∷_ _) (PE.sym wk[]≡wk[]′) PE.refl $
          wkTerm (ʷ⊇-drop (wf (⊢∙→⊢ (wf (wf-⊢∷ ⊢C))))) ⊢A₁

    ΠId-lam : Term n
    ΠId-lam = ΠId 0 (wk1 (lam p′ B₂)) (wk1 A₂) (wk1 t)

    opaque
      ⊢ΠId-lam : Γ ⊢ ΠId-lam
      ⊢ΠId-lam =
        ⊢ΠId PE.refl (wkTerm₁ (univ ⊢A₁) (lamⱼ′ ok′ ⊢B₂))
          (wkTerm₁ (univ ⊢A₁) ⊢t)

    opaque
      ΠId-lam⊢A₂ : Γ »∙ ΠId-lam ⊢ wk1 A₂ ∷ U l₁
      ΠId-lam⊢A₂ = wkTerm₁ ⊢ΠId-lam ⊢A₂

    ΠId-1 : Term (3+ n)
    ΠId-1 = ΠId 3 (var x1) (var x3) (var x2)

    opaque
      ⊢ΠId-1 :
        Γ »∙ U l₁ »∙ Id (U l₁) (wk1 A₁) (var x0) »∙
        Π p′ , q′ ▷ var x1 ▹ U l₂ ⊢
        ΠId-1
      ⊢ΠId-1 =
        ⊢ΠId PE.refl (var₁ ∙³⊢A₁)
          (PE.subst (_⊢_∷_ _ _)
             (PE.cong₂ (Id _) wk[]≡wk[]′ PE.refl) $
           var₂ ∙³⊢A₁)

    opaque
      ⊢ΠId-1[] :
        Γ »∙ Π p′ , q′ ▷ A₁ ▹ U l₂ ⊢
        ΠId-1 [ consSubst (sgSubst A₁) rfl ⇑ ]
      ⊢ΠId-1[] =
        subst-⊢ ⊢ΠId-1 $
        ⊢ˢʷ∷-⇑′ ∙²⊢ΠU $
        →⊢ˢʷ∷∙ (⊢ˢʷ∷-sgSubst ⊢A₁) $
        PE.subst (_⊢_∷_ _ _)
          (PE.cong₂ (Id _) (PE.sym $ wk1-sgSubst _ _) PE.refl) $
        rflⱼ ⊢A₁

    opaque
      ∙⊢A₁ : Γ »∙ Π p′ , q′ ▷ A₁ ▹ U l₂ ⊢ wk1 A₁ ∷ U l₁
      ∙⊢A₁ = wkTerm₁ (ΠΣⱼ (Uⱼ (∙ univ ⊢A₁)) ok′) ⊢A₁

    opaque
      ∙²⊢A₁ :
        Γ »∙ ΠΣ⟨ BMΠ ⟩ p′ , q′ ▷ A₁ ▹ U l₂ »∙
        ΠId-1 [ consSubst (sgSubst A₁) rfl ⇑ ] ⊢
        wk[ 2 ]′ A₁ ∷ U l₁
      ∙²⊢A₁ = wkTerm (stepʷ ⊇-drop ⊢ΠId-1[]) ⊢A₁

    opaque
      ∙³⊢U₂ :
        Γ »∙ ΠΣ⟨ BMΠ ⟩ p′ , q′ ▷ A₁ ▹ U l₂ »∙
        ΠId-1 [ consSubst (sgSubst A₁) rfl ⇑ ] »∙ wk[ 2 ]′ A₁ ⊢
        U l₂ ∷ U (1+ l₂)
      ∙³⊢U₂ = Uⱼ (∙ univ ∙²⊢A₁)

    opaque
      ∙³⊢A₁′ :
        Γ »∙ ΠΣ⟨ BMΠ ⟩ p′ , q′ ▷ A₁ ▹ U l₂ »∙
        ΠId-1 [ consSubst (sgSubst A₁) rfl ⇑ ] »∙ wk[ 2 ]′ A₁ ⊢
        wk[ 3 ]′ A₁ ∷ U l₁
      ∙³⊢A₁′ = wkTerm (stepʷ ⊇-drop (univ ∙²⊢A₁)) ⊢A₁

    opaque
      ∙³⊢A₁″ :
        Γ »∙ ΠΣ⟨ BMΠ ⟩ p′ , q′ ▷ A₁ ▹ U l₂ »∙
        ΠId-1 [ consSubst (sgSubst A₁) rfl ⇑ ] »∙
        ΠΣ⟨ BMΠ ⟩ p′ , q′ ▷ wk[ 2 ]′ A₁ ▹ U l₂ ⊢
        wk[ 3 ]′ A₁ ∷ U l₁
      ∙³⊢A₁″ = wkTerm (stepʷ ⊇-drop (univ (ΠΣⱼ ∙²⊢A₁ ∙³⊢U₂ ok′))) ⊢A₁

    Motive : Term (2+ n)
    Motive =
      Π p″ , q″ ▷ (Π p′ , q′ ▷ var x1 ▹ U l₂) ▹
      Π p″ , q″ ▷ ΠId-1 ▹
      Id (U (l₁ ⊔ᵘ l₂)) (wk[ 4 ]′ (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁))
        (ΠΣ⟨ b ⟩ p , q ▷ var x3 ▹ (var x2 ∘⟨ p′ ⟩ var x0))

    opaque
      ⊢Π20 :
        Γ »∙ U l₁ »∙ Id (U l₁) (wk1 A₁) (var x0) »∙
        Π p′ , q′ ▷ var x1 ▹ U l₂ »∙ ΠId-1 ⊢
        ΠΣ⟨ b ⟩ p , q ▷ var x3 ▹ (var x2 ∘⟨ p′ ⟩ var x0) ∷
        wk[ 4 ]′ (U (l₁ ⊔ᵘ l₂))
      ⊢Π20 =
        ΠΣⱼ (var₃ ⊢ΠId-1)
          (var₂ (univ (var₃ ⊢ΠId-1)) ∘ⱼ var₀ (univ (var₃ ⊢ΠId-1))) ok

    opaque
      ⊢Π20′ :
        Γ »∙ Π p′ , q′ ▷ A₁ ▹ U l₂ »∙
        ΠId-1 [ consSubst (sgSubst A₁) rfl ⇑ ] ⊢
        ΠΣ⟨ b ⟩ p , q ▷ wk[ 2 ]′ A₁ ▹ (var x2 ∘⟨ p′ ⟩ var x0) ∷
        U (l₁ ⊔ᵘ l₂)
      ⊢Π20′ =
        ΠΣⱼ ∙²⊢A₁
          (var₂ (univ ∙²⊢A₁) ∘ⱼ
           PE.subst (_⊢_∷_ _ _) (PE.sym $ PE.cong wk1 wk[]≡wk[]′)
             (var₀ (univ ∙²⊢A₁)))
          ok

    opaque
      ⊢Π10 :
        Γ »∙ Π p′ , q′ ▷ A₁ ▹ U l₂ »∙
        ΠId-1 [ consSubst (sgSubst A₁) rfl ⇑ ] »∙
        wk[ 2 ]′ (Π p′ , q′ ▷ A₁ ▹ U l₂) ⊢
        ΠΣ⟨ b ⟩ p , q ▷ wk[ 3 ]′ A₁ ▹ (var x1 ∘⟨ p′ ⟩ var x0) ∷
        U (l₁ ⊔ᵘ l₂)
      ⊢Π10 =
        ΠΣⱼ ∙³⊢A₁″
          (var₁ (univ ∙³⊢A₁″) ∘ⱼ
           PE.subst (_⊢_∷_ _ _) (PE.sym $ PE.cong wk1 $ wk-comp _ _ _)
             (var₀ (univ ∙³⊢A₁″)))
          ok

    opaque
      ⊢Motive : Γ »∙ U l₁ »∙ Id (U l₁) (wk1 A₁) (var x0) ⊢ Motive
      ⊢Motive =
        flip _⊢_.ΠΣⱼ ok″ $
        flip _⊢_.ΠΣⱼ ok″ $
        Idⱼ′ (wkTerm (ʷ⊇-drop (∙ ⊢ΠId-1)) (ΠΣⱼ ⊢A₁ ⊢B₁ ok)) ⊢Π20

    opaque
      ⊢U≡λU0 : Γ »∙ A₁ ⊢ U l₂ ≡ lam p′ (U l₂) ∘⟨ p′ ⟩ var x0 ∷ U (1+ l₂)
      ⊢U≡λU0 =
        sym′ $
        β-red-≡ (Uⱼ (∙ wk₁ (univ ⊢A₁) (univ ⊢A₁))) (var₀ (univ ⊢A₁)) ok′

    opaque
      ⊢10 :
        Γ »∙ Π p′ , q′ ▷ A₁ ▹ U l₂ »∙ wk1 A₁ ⊢
        var x1 ∘⟨ p′ ⟩ var x0 ∷ U l₂
      ⊢10 = var₁ (univ ∙⊢A₁) ∘ⱼ var₀ (univ ∙⊢A₁)

    opaque
      ⊢ΠId′ :
        Γ »∙ Π p′ , q′ ▷ A₁ ▹ U l₂ ⊢
        Π p′ , q′ ▷ wk1 A₁ ▹
        Id (U l₂) (B₁ [ 2 ][ var x0 ]↑) (var x1 ∘⟨ p′ ⟩ var x0)
      ⊢ΠId′ =
        flip ΠΣⱼ ok′ $
        Idⱼ′ (subst-⊢∷ ⊢B₁ (⊢ˢʷ∷-[][]↑ (var₀ (univ ∙⊢A₁)))) ⊢10

    opaque
      ∙²⊢A₁′ :
        Γ »∙ Π p′ , q′ ▷ A₁ ▹ U l₂ »∙
        Π p′ , q′ ▷ wk1 A₁ ▹
          Id (U l₂) (B₁ [ 2 ][ var x0 ]↑) (var x1 ∘⟨ p′ ⟩ var x0) ⊢
        wk[ 2 ]′ A₁ ∷ U l₁
      ∙²⊢A₁′ = wkTerm (stepʷ ⊇-drop ⊢ΠId′) ⊢A₁

    ext∘³ : Term n
    ext∘³ =
      ext ∘⟨ p′ ⟩ A₁ ∘⟨ p″ ⟩ lam p′ (U l₂) ∘⟨ p″ ⟩ lam p′ B₁

    opaque
      ⊢ext∘³ :
        Γ ⊢
        ext∘³ ∷
        Π p″ , q″ ▷ (Π p′ , q′ ▷ A₁ ▹ U l₂) ▹
        Π p″ , q″ ▷
          (Π p′ , q′ ▷ wk1 A₁ ▹
           Id (U l₂) (B₁ [ 2 ][ var x0 ]↑)
             (var x1 ∘⟨ p′ ⟩ var x0)) ▹
        Id (wk[ 2 ]′ (Π p′ , q′ ▷ A₁ ▹ U l₂))
          (wk[ 2 ]′ (lam p′ B₁)) (var x1)
      ⊢ext∘³ =
        conv
          (((⊢ext ∘ⱼ ⊢A₁) ∘ⱼ
            lamⱼ′ ok′ (Uⱼ (∙ univ ⊢A₁))) ∘ⱼ
           (_⊢_∷_.conv (lamⱼ′ ok′ ⊢B₁) $ univ
              (Π p′ , q′ ▷ A₁ ▹ U l₂                    ≡⟨ ΠΣ-cong
                                                             (PE.subst₂ (_⊢_≡_∷_ _ _) (PE.sym $ wk1-sgSubst _ _) PE.refl $
                                                              refl ⊢A₁)
                                                             ⊢U≡λU0 ok′ ⟩⊢∎
               Π p′ , q′ ▷ wk1 A₁ [ lam p′ (U l₂) ]₀ ▹
               (lam p′ (U l₂) ∘⟨ p′ ⟩ var x0)           ∎)))
          (_⊢_≡_.univ $ sym′
             (Π p″ , q″ ▷ (Π p′ , q′ ▷ A₁ ▹ U l₂) ▹
              Π p″ , q″ ▷
                (Π p′ , q′ ▷ wk1 A₁ ▹
                 Id (U l₂) (B₁ [ 2 ][ var x0 ]↑)
                   (var x1 ∘⟨ p′ ⟩ var x0)) ▹
              Id (wk[ 2 ]′ (Π p′ , q′ ▷ A₁ ▹ U l₂))
                (wk[ 2 ]′ (lam p′ B₁)) (var x1)                        ≡⟨ ΠΣ-cong
                                                                            (ΠΣ-cong (refl ⊢A₁) ⊢U≡λU0 ok′)
                                                                            (ΠΣ-cong
                                                                               (ΠΣ-cong
                                                                                  (refl ∙⊢A₁)
                                                                                  (Id-cong
                                                                                     (wkEqTerm (liftʷ ⊇-drop (univ ∙⊢A₁)) ⊢U≡λU0)
                                                                                     (PE.subst₃ (_⊢_≡_∷_ _) (PE.sym $ [][]↑≡ B₁) PE.refl PE.refl $
                                                                                      sym′ $
                                                                                      β-red-≡
                                                                                        (PE.subst₃ _⊢_∷_
                                                                                           (PE.cong (_»_ _) (PE.cong (_∙_ _) (PE.sym wk[]≡wk[]′)))
                                                                                           PE.refl PE.refl $
                                                                                         wkTerm
                                                                                           (liftʷ ⊇-drop $
                                                                                            univ (wkTerm (stepʷ ⊇-drop (univ ∙⊢A₁)) ⊢A₁))
                                                                                           ⊢B₁)
                                                                                        (var₀ (univ ∙⊢A₁)) ok′)
                                                                                     (refl ⊢10))
                                                                                  ok′)
                                                                               (Id-cong
                                                                                  (ΠΣ-cong
                                                                                     (refl ∙²⊢A₁′)
                                                                                     (wkEqTerm (liftʷ ⊇-drop (univ ∙²⊢A₁′)) ⊢U≡λU0)
                                                                                     ok′)
                                                                                  (_⊢_≡_∷_.refl $
                                                                                   wkTerm (stepʷ ⊇-drop ⊢ΠId′) (lamⱼ′ ok′ ⊢B₁))
                                                                                  (_⊢_≡_∷_.refl $
                                                                                   PE.subst (_⊢_∷_ _ _) wk[]≡wk[]′ $
                                                                                   var₁ ⊢ΠId′))
                                                                               ok″)
                                                                            ok″ ⟩⊢∎≡
              Π p″ , q″ ▷
                (Π p′ , q′ ▷ A₁ ▹
                 (lam p′ (U l₂) ∘⟨ p′ ⟩ var x0)) ▹
              Π p″ , q″ ▷
                (Π p′ , q′ ▷ wk1 A₁ ▹
                 Id (lam p′ (U l₂) ∘⟨ p′ ⟩ var x0)
                   (wk[ 2 ]′ (lam p′ B₁) ∘⟨ p′ ⟩ var x0)
                   (var x1 ∘⟨ p′ ⟩ var x0)) ▹
              Id
                (wk[ 2 ]′
                   (Π p′ , q′ ▷ A₁ ▹ (lam p′ (U l₂) ∘⟨ p′ ⟩ var x0)))
                (wk[ 2 ]′ (lam p′ B₁)) (var x1)                        ≡˘⟨ PE.cong₂ (Π p″ , q″ ▷_▹_)
                                                                             (PE.cong₂ (Π p′ , q′ ▷_▹_) wk2-[,] PE.refl)
                                                                             (PE.cong₂ (Π p″ , q″ ▷_▹_)
                                                                                (PE.cong₂ (Π p′ , q′ ▷_▹_)
                                                                                   (PE.trans (PE.cong _[ _ ] $ wk[]≡wk[]′ {t = A₁})
                                                                                    wk[2+]′[,⇑]≡)
                                                                                   (PE.cong₂ (Id _)
                                                                                      (PE.cong₃ _∘⟨_⟩_ (wk-comp _ _ _) PE.refl PE.refl)
                                                                                      PE.refl))
                                                                                (PE.cong₃ Id
                                                                                   (PE.cong₂ (Π p′ , q′ ▷_▹_)
                                                                                      (PE.trans (PE.cong _[ _ ] $ wk[]≡wk[]′ {t = A₁})
                                                                                       wk[2+]′[,⇑]≡)
                                                                                      PE.refl)
                                                                                   (wk-comp _ _ _)
                                                                                   PE.refl)) ⟩
              Π p″ , q″ ▷
                (Π p′ , q′ ▷ wk[ 2 ] A₁ ▹
                 (lam p′ (U l₂) ∘⟨ p′ ⟩ var x0)) ▹
              Π p″ , q″ ▷
                (Π p′ , q′ ▷ wk[ 3 ] A₁ ▹
                 Id (lam p′ (U l₂) ∘⟨ p′ ⟩ var x0)
                   (var x2 ∘⟨ p′ ⟩ var x0) (var x1 ∘⟨ p′ ⟩ var x0)) ▹
              Id
                (Π p′ , q′ ▷ wk[ 4 ] A₁ ▹
                 (lam p′ (U l₂) ∘⟨ p′ ⟩ var x0))
                (var x2) (var x1)
              [ lam p′ (U l₂) , lam p′ B₁ ]₁₀                          ≡˘⟨ singleSubstComp _ _
                                                                             (Π _ , _ ▷ (Π _ , _ ▷ wk[ _ ] A₁ ▹ (lam _ (U _) ∘⟨ _ ⟩ var x0)) ▹
                                                                              Π _ , _ ▷
                                                                                (Π _ , _ ▷ wk[ _ ] A₁ ▹
                                                                                 Id (lam _ (U _) ∘⟨ _ ⟩ var x0) (var x2 ∘⟨ _ ⟩ var x0)
                                                                                   (var x1 ∘⟨ _ ⟩ var x0)) ▹
                                                                              Id (Π _ , _ ▷ wk[ 4 ] A₁ ▹ (lam _ (U _) ∘⟨ _ ⟩ var x0)) (var x2)
                                                                                (var x1)) ⟩
              Π p″ , q″ ▷
                (Π p′ , q′ ▷ wk[ 2 ] A₁ ▹
                 (lam p′ (U l₂) ∘⟨ p′ ⟩ var x0)) ▹
              Π p″ , q″ ▷
                (Π p′ , q′ ▷ wk[ 3 ] A₁ ▹
                 Id (lam p′ (U l₂) ∘⟨ p′ ⟩ var x0)
                   (var x2 ∘⟨ p′ ⟩ var x0) (var x1 ∘⟨ p′ ⟩ var x0)) ▹
              Id
                (Π p′ , q′ ▷ wk[ 4 ] A₁ ▹
                 (lam p′ (U l₂) ∘⟨ p′ ⟩ var x0))
                (var x2) (var x1)
              [ sgSubst (lam p′ (U l₂)) ⇑ ] [ lam p′ B₁ ]₀             ∎))

    opaque
      ⊢ext∘⁴ :
        Γ »∙ ΠΣ⟨ BMΠ ⟩ p′ , q′ ▷ A₁ ▹ U l₂ »∙
        ΠId-1 [ consSubst (sgSubst A₁) rfl ⇑ ] ⊢
        wk[ 2 ]′ ext∘³ ∘⟨ p″ ⟩ var x1 ∷
        Π p″ , q″ ▷
          (Π p′ , q′ ▷ wk[ 2 ]′ A₁ ▹
           Id (U l₂) (B₁ [ 3 ][ var x0 ]↑)
             (var x2 ∘⟨ p′ ⟩ var x0)) ▹
        Id (wk[ 3 ]′ (ΠΣ⟨ BMΠ ⟩ p′ , q′ ▷ A₁ ▹ U l₂))
          (wk[ 3 ]′ (lam p′ B₁)) (var x2)
      ⊢ext∘⁴ =
        PE.subst (_⊢_∷_ _ _)
          (Π p″ , q″ ▷
             (U.wk (lift (stepn id 2)) $
              Π p′ , q′ ▷ wk1 A₁ ▹
              Id (U l₂) (B₁ [ 2 ][ var x0 ]↑) (var x1 ∘⟨ p′ ⟩ var x0)) ▹
           Id
             (U.wk (liftn (stepn id 2) 2)
                (wk[ 2 ]′ (Π p′ , q′ ▷ A₁ ▹ U l₂)))
             (U.wk (liftn (stepn id 2) 2) (wk[ 2 ]′ (lam p′ B₁)))
             (var x1)
           [ var x1 ]₀                                                    ≡⟨ PE.cong₂ (Π p″ , q″ ▷_▹_)
                                                                               (PE.cong₂ (Π p′ , q′ ▷_▹_)
                                                                                  (PE.trans (PE.sym $ [][]↑≡ (wk1 A₁))
                                                                                   wk1-[][]↑′)
                                                                                  (PE.cong₂ (Id _)
                                                                                     (PE.trans (subst-wk (B₁ [ 2 ][ _ ]↑)) $
                                                                                      PE.trans (substCompEq B₁) $
                                                                                      flip substVar-to-subst B₁ λ where
                                                                                        x0     → PE.refl
                                                                                        (_ +1) → PE.refl)
                                                                                     PE.refl))
                                                                               (PE.cong₃ Id
                                                                                  (PE.trans (subst-wk (wk[ 2 ]′ (Π _ , _ ▷ A₁ ▹ U _))) $
                                                                                   PE.trans (subst-wk (Π _ , _ ▷ A₁ ▹ U _)) $
                                                                                   PE.sym $ wk≡subst _ _)
                                                                                  (PE.trans (subst-wk (wk[ 2 ]′ (lam _ B₁))) $
                                                                                   PE.trans (subst-wk (lam _ B₁)) $
                                                                                   PE.sym $ wk≡subst _ _)
                                                                                  PE.refl) ⟩
          Π p″ , q″ ▷
            (Π p′ , q′ ▷ wk[ 2 ]′ A₁ ▹
             Id (U l₂) (B₁ [ 3 ][ var x0 ]↑) (var x2 ∘⟨ p′ ⟩ var x0)) ▹
          Id (wk[ 3 ]′ (Π p′ , q′ ▷ A₁ ▹ U l₂)) (wk[ 3 ]′ (lam p′ B₁))
            (var x2)                                                      ∎) $
        PE.subst (_⊢_∷_ _ _)
          (PE.cong₂ (Π p″ , q″ ▷_▹_) (PE.sym wk[]≡wk[]′) PE.refl)
          (wkTerm (stepʷ ⊇-drop ⊢ΠId-1[]) ⊢ext∘³) ∘ⱼ
        var₁ ⊢ΠId-1[]

    opaque
      ⊢ext∘⁵ :
        Γ »∙ ΠΣ⟨ BMΠ ⟩ p′ , q′ ▷ A₁ ▹ U l₂ »∙
        ΠId-1 [ consSubst (sgSubst A₁) rfl ⇑ ] ⊢
        wk[ 2 ]′ ext∘³ ∘⟨ p″ ⟩ var x1 ∘⟨ p″ ⟩ var x0 ∷
        Id (wk[ 2 ]′ (ΠΣ⟨ BMΠ ⟩ p′ , q′ ▷ A₁ ▹ U l₂))
          (wk[ 2 ]′ (lam p′ B₁)) (var x1)
      ⊢ext∘⁵ =
        PE.subst (_⊢_∷_ _ _)
          (PE.cong₃ Id (step-sgSubst _ _) (step-sgSubst _ _) PE.refl) $
        ⊢ext∘⁴ ∘ⱼ
        (_⊢_∷_.conv (var₀ ⊢ΠId-1[]) $ univ
           (wk1 (ΠId-1 [ consSubst (sgSubst A₁) rfl ⇑ ])             ≡⟨ PE.trans
                                                                          (PE.cong wk1 $
                                                                           PE.cong₂ (Π p′ , q′ ▷_▹_)
                                                                             (PE.trans
                                                                                (PE.cong _[ consSubst (sgSubst _) _ ⇑ ] $
                                                                                 wk[]≡wk[]′ {t = A₁})
                                                                              wk[2+]′[,⇑]≡)
                                                                             (PE.cong₂ (Id _)
                                                                                (PE.trans ([][]↑-[,⇑] 2 B₁) $
                                                                                 [1+][0]↑ {t = B₁})
                                                                                (PE.cong (var x1 ∘⟨ _ ⟩_) $
                                                                                 PE.trans cast-[] $
                                                                                 PE.cong₄ (cast _)
                                                                                   wk[2+]′[,⇑]≡ wk[]≡wk[]′ PE.refl PE.refl))) $
                                                                        PE.cong₂ (Π p′ , q′ ▷_▹_)
                                                                          wk[]≡wk[]′
                                                                          (PE.cong₂ (Id _)
                                                                             (PE.trans (wk-comp _ _ _) $
                                                                              PE.sym [1+][0]↑)
                                                                             (PE.cong (_ ∘⟨ _ ⟩_) $
                                                                              PE.trans wk-cast $
                                                                              PE.cong₄ (cast _)
                                                                                (wk-comp _ _ _) (wk-comp _ _ _) PE.refl PE.refl)) ⟩⊢≡
            Π p′ , q′ ▷ wk[ 2 ]′ A₁ ▹
            Id (U l₂) (B₁ [ 3 ][ var x0 ]↑)
              (var x2 ∘⟨ p′ ⟩
               cast l₁ (wk[ 3 ]′ A₁) (wk[ 3 ]′ A₁) rfl (var x0))     ≡⟨ ΠΣ-cong
                                                                          (refl ∙²⊢A₁)
                                                                          (Id-cong
                                                                             (refl ∙³⊢U₂)
                                                                             (_⊢_≡_∷_.refl $ subst-⊢∷ ⊢B₁ $ ⊢ˢʷ∷-[][]↑ $
                                                                              PE.subst₃ _⊢_∷_
                                                                                (PE.cong (_»_ _) (PE.cong (_∙_ _) wk[]≡wk[]′)) PE.refl PE.refl $
                                                                              var₀ (PE.subst (_⊢_ _) (PE.sym wk[]≡wk[]′) (univ ∙²⊢A₁)))
                                                                             (app-cong
                                                                                (refl (var₂ (univ ∙²⊢A₁)))
                                                                                (PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym wk[]≡wk[]′) $
                                                                                 cast-≡ ∙³⊢A₁′ $
                                                                                 PE.subst (_⊢_∷_ _ _) (wk-comp _ _ _) $
                                                                                 var₀ (univ ∙²⊢A₁))))
                                                                          ok′ ⟩⊢∎≡
            Π p′ , q′ ▷ wk[ 2 ]′ A₁ ▹
            Id (U l₂) (B₁ [ 3 ][ var x0 ]↑) (var x2 ∘⟨ p′ ⟩ var x0)  ∎))

    rfl-case : Term n
    rfl-case =
      lam p″ $ lam p″ $
      cong ω (wk[ 2 ]′ (Π p′ , q′ ▷ A₁ ▹ U l₂))
        (wk[ 2 ]′ (lam p′ B₁)) (var x1) (U (l₁ ⊔ᵘ l₂))
        (ΠΣ⟨ b ⟩ p , q ▷ wk[ 3 ]′ A₁ ▹ (var x1 ∘⟨ p′ ⟩ var x0))
        (wk[ 2 ]′ ext∘³ ∘⟨ p″ ⟩ var x1 ∘⟨ p″ ⟩ var x0)

    opaque
      ⊢rfl-case : Γ ⊢ rfl-case ∷ Motive [ A₁ , rfl ]₁₀
      ⊢rfl-case =
        lamⱼ′ ok″ $ lamⱼ′ ok″ $
        _⊢_∷_.conv (⊢cong ⊢Π10 ⊢ext∘⁵) $ univ
          (Id (U (l₁ ⊔ᵘ l₂))
             (ΠΣ⟨ b ⟩ p , q ▷ wk[ 3 ]′ A₁ ▹ (var x1 ∘⟨ p′ ⟩ var x0)
              [ wk[ 2 ]′ (lam p′ B₁) ]₀)
             (ΠΣ⟨ b ⟩ p , q ▷ wk[ 3 ]′ A₁ ▹ (var x1 ∘⟨ p′ ⟩ var x0)
              [ var x1 ]₀)                                            ≡⟨ PE.cong₂ (Id _)
                                                                           (PE.cong₂ (ΠΣ⟨_⟩_,_▷_▹_ _ _ _)
                                                                              wk[1+]′-[]₀≡
                                                                              (PE.cong₃ _∘⟨_⟩_ (wk-comp _ _ _) PE.refl PE.refl))
                                                                           (PE.cong₂ (ΠΣ⟨_⟩_,_▷_▹_ _ _ _) wk[1+]′-[]₀≡ PE.refl) ⟩⊢≡
           Id (U (l₁ ⊔ᵘ l₂))
             (ΠΣ⟨ b ⟩ p , q ▷ wk[ 2 ]′ A₁ ▹
              (wk[ 3 ]′ (lam p′ B₁) ∘⟨ p′ ⟩ var x0))
             (ΠΣ⟨ b ⟩ p , q ▷ wk[ 2 ]′ A₁ ▹ (var x2 ∘⟨ p′ ⟩ var x0))  ≡⟨ Id-cong (refl (Uⱼ (∙ ⊢ΠId-1[])))
                                                                           (ΠΣ-cong (refl ∙²⊢A₁)
                                                                              (PE.subst₂ (_⊢_≡_∷_ _ _)
                                                                                 (PE.trans (PE.sym $ [][]↑≡ B₁) [1+][0]↑)
                                                                                 PE.refl $
                                                                               β-red-≡
                                                                                 (PE.subst₃ _⊢_∷_
                                                                                    (PE.cong (_»_ _) (PE.cong (_∙_ _) $ PE.sym $ wk-comp _ _ _))
                                                                                    PE.refl PE.refl $
                                                                                  wkTerm (liftʷ ⊇-drop (univ ∙³⊢A₁′)) ⊢B₁)
                                                                                 (var₀ (univ ∙²⊢A₁)) ok′)
                                                                              ok)
                                                                           (refl ⊢Π20′) ⟩⊢∎≡
           Id (U (l₁ ⊔ᵘ l₂)) (wk[ 2 ]′ (ΠΣ⟨ b ⟩ p , q ▷  A₁ ▹ B₁))
             (ΠΣ⟨ b ⟩ p , q ▷ wk[ 2 ]′ A₁ ▹ (var x2 ∘⟨ p′ ⟩ var x0))  ≡˘⟨ PE.cong₂ (Id _)
                                                                            wk[2+]′[,⇑]≡
                                                                            (PE.cong₂ (ΠΣ⟨_⟩_,_▷_▹_ _ _ _) wk[]≡wk[]′ PE.refl) ⟩
           (Id (U (l₁ ⊔ᵘ l₂)) (wk[ 4 ]′ (ΠΣ⟨ b ⟩ p , q ▷  A₁ ▹ B₁))
              (ΠΣ⟨ b ⟩ p , q ▷ var x3 ▹ (var x2 ∘⟨ p′ ⟩ var x0))
            [ consSubst (sgSubst A₁) rfl ⇑[ 2 ] ])                    ∎)

    J-app : Term n
    J-app = J ω ω (U l₁) A₁ Motive rfl-case A₂ t

    opaque
      ⊢J :
        Γ ⊢ J-app ∷
        Π p″ , q″ ▷ (Π p′ , q′ ▷ A₂ ▹ U l₂) ▹
        Π p″ , q″ ▷ ΠId 1 (var x1) (wk[ 2 ]′ A₂) (wk[ 2 ]′ t) ▹
        Id (U (l₁ ⊔ᵘ l₂)) (wk[ 2 ]′ (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁))
          (ΠΣ⟨ b ⟩ p , q ▷ wk[ 2 ]′ A₂ ▹ (var x2 ∘⟨ p′ ⟩ var x0))
      ⊢J =
        PE.subst (_⊢_∷_ _ _)
          (Π p″ , q″ ▷ (Π p′ , q′ ▷ var x1 ▹ U l₂) ▹
           Π p″ , q″ ▷
             (Π p′ , q′ ▷ wk[ 3 ] A₁ ▹
              Id (U l₂) (B₁ [ 4 ][ var x0 ]↑)
                (var x1 ∘⟨ p′ ⟩
                 cast l₁ (wk[ 4 ]′ A₁) (var x3) (var x2) (var x0))) ▹
           Id (U (l₁ ⊔ᵘ l₂)) (wk[ 4 ]′ (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁))
             (ΠΣ⟨ b ⟩ p , q ▷ var x3 ▹ (var x2 ∘⟨ p′ ⟩ var x0))
           [ A₂ , t ]₁₀                                                ≡⟨ PE.cong₂ (Π p″ , q″ ▷_▹_) PE.refl $
                                                                          PE.cong₂ (Π p″ , q″ ▷_▹_)
                                                                            (PE.cong₂ (Π p′ , q′ ▷_▹_)
                                                                               (PE.trans
                                                                                  (PE.cong _[ _ ] $
                                                                                   wk[]≡wk[]′ {t = A₁}) $
                                                                                wk[2+]′[,⇑]≡)
                                                                               (PE.cong₂ (Id _)
                                                                                  ([][]↑-[,⇑] 2 B₁)
                                                                                  (PE.cong (_∘⟨_⟩_ _ _) $
                                                                                   PE.trans cast-[] $
                                                                                   PE.cong₄ (cast _)
                                                                                     wk[2+]′[,⇑]≡ wk[]≡wk[]′ wk[]≡wk[]′ PE.refl)))
                                                                            (PE.cong₂ (Id _)
                                                                               wk[2+]′[,⇑]≡
                                                                               (PE.cong₂ (ΠΣ⟨_⟩_,_▷_▹_ _ _ _) wk[]≡wk[]′ PE.refl)) ⟩
        Π p″ , q″ ▷ (Π p′ , q′ ▷ A₂ ▹ U l₂) ▹
        Π p″ , q″ ▷
          (Π p′ , q′ ▷ wk1 A₁ ▹
           Id (U l₂) (B₁ [ 2 ][ var x0 ]↑)
             (var x1 ∘⟨ p′ ⟩
              cast l₁ (wk[ 2 ]′ A₁) (wk[ 2 ]′ A₂) (wk[ 2 ]′ t)
                (var x0))) ▹
        Id (U (l₁ ⊔ᵘ l₂)) (wk[ 2 ]′ (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁))
          (ΠΣ⟨ b ⟩ p , q ▷ wk[ 2 ]′ A₂ ▹ (var x2 ∘⟨ p′ ⟩ var x0))      ∎) $
        Jⱼ′ ⊢Motive ⊢rfl-case ⊢t

    opaque
      ⊢J∘ :
        Γ ⊢ J-app ∘⟨ p″ ⟩ lam p′ B₂ ∷
        Π p″ , q″ ▷
          (Π p′ , q′ ▷ A₁ ▹
           Id (U l₂) (B₁ [ 1 ][ var x0 ]↑)
             (B₂ [ 1 ][ cast l₁ (wk1 A₁) (wk1 A₂) (wk1 t)
                          (var x0) ]↑)) ▹
        Id (U (l₁ ⊔ᵘ l₂)) (wk1 (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁))
          (ΠΣ⟨ b ⟩ p , q ▷ wk1 A₂ ▹ (B₂ [ 2 ][ var x0 ]↑))
      ⊢J∘ =
        _⊢_∷_.conv (⊢J ∘ⱼ lamⱼ′ ok′ ⊢B₂) $ univ
          (Π p″ , q″ ▷
             (Π p′ , q′ ▷ wk1 A₁ ▹
              Id (U l₂) (B₁ [ 2 ][ var x0 ]↑)
                (var x1 ∘⟨ p′ ⟩
                 cast l₁ (wk[ 2 ]′ A₁) (wk[ 2 ]′ A₂) (wk[ 2 ]′ t)
                   (var x0))) ▹
           Id (U (l₁ ⊔ᵘ l₂)) (wk[ 2 ]′ (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁))
             (ΠΣ⟨ b ⟩ p , q ▷ wk[ 2 ]′ A₂ ▹ (var x2 ∘⟨ p′ ⟩ var x0))
           [ lam p′ B₂ ]₀                                             ≡⟨ PE.cong₂ (Π p″ , q″ ▷_▹_)
                                                                           (PE.cong₂ (Π p′ , q′ ▷_▹_)
                                                                              (wk1-sgSubst _ _)
                                                                              (PE.cong₂ (Id _)
                                                                                 ([][]↑-[₀⇑] 1 B₁)
                                                                                 (PE.cong (_∘⟨_⟩_ _ _) $
                                                                                  PE.trans cast-[] $
                                                                                  PE.cong₄ (cast _)
                                                                                    wk[+1]′-[₀⇑]≡ wk[+1]′-[₀⇑]≡ wk[+1]′-[₀⇑]≡ PE.refl)))
                                                                           (PE.cong₂ (Id _)
                                                                              wk[+1]′-[₀⇑]≡
                                                                              (PE.cong₂ (ΠΣ⟨_⟩_,_▷_▹_ _ _ _)
                                                                                 wk[+1]′-[₀⇑]≡
                                                                                 (PE.cong₃ _∘⟨_⟩_ wk[]≡wk[]′ PE.refl PE.refl))) ⟩⊢≡
          (Π p″ , q″ ▷
             (Π p′ , q′ ▷ A₁ ▹
              Id (U l₂) (B₁ [ 1 ][ var x0 ]↑)
                (wk1 (lam p′ B₂) ∘⟨ p′ ⟩
                 cast l₁ (wk1 A₁) (wk1 A₂) (wk1 t) (var x0))) ▹
           Id (U (l₁ ⊔ᵘ l₂)) (wk1 (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁))
             (ΠΣ⟨ b ⟩ p , q ▷ wk1 A₂ ▹
              (wk[ 2 ]′ (lam p′ B₂) ∘⟨ p′ ⟩ var x0)))                 ≡⟨ ΠΣ-cong
                                                                           (ΠΣ-cong
                                                                              (refl ⊢A₁)
                                                                              (Id-cong (refl (Uⱼ (∙ univ ⊢A₁)))
                                                                                 (refl (subst-⊢∷ ⊢B₁ (⊢ˢʷ∷-[][]↑ (var₀ (univ ⊢A₁)))))
                                                                                 (PE.subst₂ (_⊢_≡_∷_ _ _) (PE.sym $ [][]↑≡ B₂) PE.refl $
                                                                                  β-red-≡
                                                                                    (wkTerm (liftʷ ⊇-drop (wk₁ (univ ⊢A₁) (univ ⊢A₂))) ⊢B₂)
                                                                                    (⊢cast (wkTerm₁ (univ ⊢A₁) ⊢t) (var₀ (univ ⊢A₁))) ok′))
                                                                              ok′)
                                                                           (Id-cong (refl (Uⱼ (∙ ⊢ΠId-lam)))
                                                                              (refl (wkTerm₁ ⊢ΠId-lam (ΠΣⱼ ⊢A₁ ⊢B₁ ok)))
                                                                              (ΠΣ-cong (refl ΠId-lam⊢A₂)
                                                                                 (PE.subst₂ (_⊢_≡_∷_ _ _) (PE.sym $ [][]↑≡ B₂) PE.refl $
                                                                                  β-red-≡
                                                                                    (wkTerm
                                                                                       (liftʷ ⊇-drop $ _⊢_.univ $
                                                                                        wkTerm (ʷ⊇-drop (∙ univ ΠId-lam⊢A₂)) ⊢A₂)
                                                                                       ⊢B₂)
                                                                                    (PE.subst (_⊢_∷_ _ _) wk[]≡wk[]′ $
                                                                                     var₀ (univ ΠId-lam⊢A₂)) ok′)
                                                                                 ok))
                                                                           ok″ ⟩⊢∎
           Π p″ , q″ ▷
             (Π p′ , q′ ▷ A₁ ▹
              Id (U l₂) (B₁ [ 1 ][ var x0 ]↑)
                (B₂ [ 1 ][ cast l₁ (wk1 A₁) (wk1 A₂) (wk1 t)
                             (var x0) ]↑)) ▹
           Id (U (l₁ ⊔ᵘ l₂)) (wk1 (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁))
             (ΠΣ⟨ b ⟩ p , q ▷ wk1 A₂ ▹ (B₂ [ 2 ][ var x0 ]↑))         ∎)

    opaque
      ⊢J∘∘ :
        Γ ⊢ J-app ∘⟨ p″ ⟩ lam p′ B₂ ∘⟨ p″ ⟩ lam p′ u ∷
        Id (U (l₁ ⊔ᵘ l₂)) (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁)
          (ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂)
      ⊢J∘∘ =
        PE.subst (_⊢_∷_ _ _)
          (Id (U (l₁ ⊔ᵘ l₂)) (wk1 (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁))
             (ΠΣ⟨ b ⟩ p , q ▷ wk1 A₂ ▹ (B₂ [ 2 ][ var x0 ]↑))
           [ lam p′ u ]₀                                       ≡⟨ PE.cong₂ (Id _) (wk1-sgSubst _ _) $
                                                                  PE.cong₂ (ΠΣ⟨_⟩_,_▷_▹_ _ _ _)
                                                                    (wk1-sgSubst _ _)
                                                                    ([][]↑-[₀⇑] 1 B₂) ⟩
           Id (U (l₁ ⊔ᵘ l₂)) (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁)
             (ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ (B₂ [ var x0 ]↑))           ≡⟨ PE.cong (Id _ _ ∘→ ΠΣ⟨_⟩_,_▷_▹_ _ _ _ _) [0]↑ ⟩

           Id (U (l₁ ⊔ᵘ l₂)) (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁)
             (ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂)                         ∎)
          (⊢J∘ ∘ⱼ
           PE.subst (_⊢_∷_ _ _)
             (PE.cong (Π p′ , q′ ▷ A₁ ▹_) $
              PE.cong₂ (Id _) (PE.sym [0]↑) PE.refl)
             (lamⱼ′ ok′ ⊢u))

opaque

  -- A variant of ΠΣ-cong-Idˡ.

  ΠΣ-cong-Idʳ :
    ΠΣ-allowed b p q →
    Π-allowed p′ q′ →
    Π-allowed p″ q″ →
    Has-function-extensionality p′ q′ p″ q″ l₁ (1+ l₂) Η →
    Η »∙ A₁ ⊢ B₁ ∷ U l₂ →
    Η ⊢ t ∷ Id (U l₁) A₂ A₁ →
    Η »∙ A₂ ⊢ u ∷
      Id (U l₂) (B₁ [ cast l₁ (wk1 A₂) (wk1 A₁) (wk1 t) (var x0) ]↑)
        B₂ →
    ∃ λ v →
      Η ⊢ v ∷
        Id (U (l₁ ⊔ᵘ l₂)) (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁)
          (ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂)
  ΠΣ-cong-Idʳ ok ok′ ok″ ext ⊢B₁ ⊢t ⊢u =
    _ ,
    ⊢symmetry (ΠΣ-cong-Idˡ ok ok′ ok″ ext ⊢B₁ ⊢t (⊢symmetry ⊢u) .proj₂)

private opaque

  -- The following code illustrates roughly how Id-cong-Idˡ below is
  -- defined.

  Id-cong-Idˡ′ :
    ∀ {a} {A₁ A₂ : Set a} {t₁ u₁ : A₁} {t₂ u₂ : A₂}
    (A₁≡A₂ : A₁ PE.≡ A₂) →
    PE.subst (λ A → A) A₁≡A₂ t₁ PE.≡ t₂ →
    PE.subst (λ A → A) A₁≡A₂ u₁ PE.≡ u₂ →
    (t₁ PE.≡ u₁) PE.≡ (t₂ PE.≡ u₂)
  Id-cong-Idˡ′ {A₁} {t₁} {u₁} {t₂} {u₂} A₁≡A₂ t₁≡t₂ u₁≡u₂ =
    J′ (λ A₂ A₁≡A₂ →
           (t₂ u₂ : A₂) →
           PE.subst (λ A → A) A₁≡A₂ t₁ PE.≡ t₂ →
           PE.subst (λ A → A) A₁≡A₂ u₁ PE.≡ u₂ →
           (t₁ PE.≡ u₁) PE.≡ (t₂ PE.≡ u₂))
      (λ t₂ u₂ t₁≡t₂ u₁≡u₂ →
         PE.cong₂ (PE._≡_ {A = A₁}) t₁≡t₂ u₁≡u₂)
      A₁≡A₂ t₂ u₂ t₁≡t₂ u₁≡u₂

opaque

  -- Id preserves propositional equality in a certain sense (assuming
  -- that some Π-type is allowed).

  Id-cong-Idˡ :
    {Γ : Cons m n} →
    Π-allowed p q →
    Γ ⊢ t ∷ Id (U l) A₁ A₂ →
    Γ ⊢ u ∷ Id A₂ (cast l A₁ A₂ t t₁) t₂ →
    Γ ⊢ v ∷ Id A₂ (cast l A₁ A₂ t u₁) u₂ →
    ∃ λ w → Γ ⊢ w ∷ Id (U l) (Id A₁ t₁ u₁) (Id A₂ t₂ u₂)
  Id-cong-Idˡ
    {n} {p} {q} {t} {l} {A₁} {A₂} {u} {t₁} {t₂} {v} {u₁} {u₂} {Γ}
    ok ⊢t ⊢u ⊢v =
    J-app ∘⟨ p ⟩ t₂ ∘⟨ p ⟩ u₂ ∘⟨ p ⟩ u ∘⟨ p ⟩ v , ⊢J∘⁴
    where
    opaque
      ⊢A₁ : Γ ⊢ A₁ ∷ U l
      ⊢A₁ = inversion-Id (wf-⊢∷ ⊢t) .proj₂ .proj₁

    opaque
      ⊢t₁ : Γ ⊢ t₁ ∷ A₁
      ⊢t₁ =
        inversion-cast (inversion-Id (wf-⊢∷ ⊢u) .proj₂ .proj₁)
          .proj₂ .proj₂ .proj₂ .proj₁

    opaque
      ⊢t₂ : Γ ⊢ t₂ ∷ A₂
      ⊢t₂ = inversion-Id (wf-⊢∷ ⊢u) .proj₂ .proj₂

    opaque
      ⊢u₁ : Γ ⊢ u₁ ∷ A₁
      ⊢u₁ =
        inversion-cast (inversion-Id (wf-⊢∷ ⊢v) .proj₂ .proj₁)
          .proj₂ .proj₂ .proj₂ .proj₁

    opaque
      ⊢u₂ : Γ ⊢ u₂ ∷ A₂
      ⊢u₂ = inversion-Id (wf-⊢∷ ⊢v) .proj₂ .proj₂

    opaque
      ⊢U : Γ ⊢ U l
      ⊢U = wf-⊢∷ ⊢A₁

    opaque
      ⊢Id-U-0 : Γ »∙ U l ⊢ Id (U l) (wk1 A₁) (var x0)
      ⊢Id-U-0 = Idⱼ′ (wkTerm₁ ⊢U ⊢A₁) (var₀ ⊢U)

    opaque
      ⊢1 : Γ »∙ U l »∙ Id (U l) (wk1 A₁) (var x0) ⊢ var x1
      ⊢1 = univ (var₁ ⊢Id-U-0)

    opaque
      ⊢2 : Γ »∙ U l »∙ Id (U l) (wk1 A₁) (var x0) »∙ var x1 ⊢ var x2
      ⊢2 = univ (var₂ ⊢1)

    opaque
      ⊢Id-3-cast-1 :
        Γ »∙ U l »∙ Id (U l) (wk1 A₁) (var x0) »∙ var x1 »∙ var x2 ⊢
        Id (var x3)
          (cast l (wk[ 4 ]′ A₁) (var x3) (var x2) (wk[ 4 ]′ t₁))
          (var x1)
      ⊢Id-3-cast-1 =
        Idⱼ′
          (⊢cast
             (PE.subst (_⊢_∷_ _ _)
                (PE.cong₂ (Id _) wk[]≡wk[]′ PE.refl) $
              var₂ ⊢2)
             (wkTerm (ʷ⊇-drop (∙ ⊢2)) ⊢t₁))
          (var₁ ⊢2)

    opaque
      ⊢Id-4-cast-1 :
        Γ »∙ U l »∙ Id (U l) (wk1 A₁) (var x0) »∙ var x1 »∙ var x2 »∙
        Id (var x3)
          (cast l (wk[ 4 ]′ A₁) (var x3) (var x2) (wk[ 4 ]′ t₁))
          (var x1) ⊢
        Id (var x4)
          (cast l (wk[ 5 ]′ A₁) (var x4) (var x3) (wk[ 5 ]′ u₁))
          (var x1)
      ⊢Id-4-cast-1 =
        Idⱼ′
          (⊢cast
             (PE.subst (_⊢_∷_ _ _)
                (PE.cong₂ (Id _) wk[]≡wk[]′ PE.refl) $
              var₃ ⊢Id-3-cast-1)
             (wkTerm (ʷ⊇-drop (∙ ⊢Id-3-cast-1)) ⊢u₁))
          (var₁ ⊢Id-3-cast-1)

    Motive : Term (2+ n)
    Motive =
      Π p , q ▷ var x1 ▹
      Π p , q ▷ var x2 ▹
      Π p , q ▷
        Id (var x3)
          (cast l (wk[ 4 ]′ A₁) (var x3) (var x2) (wk[ 4 ]′ t₁))
          (var x1) ▹
      Π p , q ▷
        Id (var x4)
          (cast l (wk[ 5 ]′ A₁) (var x4) (var x3) (wk[ 5 ]′ u₁))
          (var x1) ▹
      Id (U l) (wk[ 6 ]′ (Id A₁ t₁ u₁)) (Id (var x5) (var x3) (var x2))

    opaque
      ⊢Motive : Γ »∙ U l »∙ Id (U l) (wk1 A₁) (var x0) ⊢ Motive
      ⊢Motive =
        flip _⊢_.ΠΣⱼ ok $ flip _⊢_.ΠΣⱼ ok $
        flip _⊢_.ΠΣⱼ ok $ flip _⊢_.ΠΣⱼ ok $
        Idⱼ′
          (wkTerm (ʷ⊇-drop (∙ ⊢Id-4-cast-1)) (Idⱼ ⊢A₁ ⊢t₁ ⊢u₁))
          (Idⱼ (var₅ ⊢Id-4-cast-1) (var₃ ⊢Id-4-cast-1)
             (var₂ ⊢Id-4-cast-1))

    opaque
      ⊢A₁′ : Γ »∙ A₁ ⊢ wk1 A₁
      ⊢A₁′ = wk₁ (univ ⊢A₁) (univ ⊢A₁)

    opaque
      ⊢Id-1 :
        Γ »∙ A₁ »∙ wk1 A₁ ⊢ Id (wk[ 2 ]′ A₁) (wk[ 2 ]′ t₁) (var x1)
      ⊢Id-1 =
        Idⱼ′
          (wkTerm (ʷ⊇-drop (∙ ⊢A₁′)) ⊢t₁)
          (PE.subst (_⊢_∷_ _ _) wk[]≡wk[]′ $
           var₁ ⊢A₁′)

    opaque
      ⊢Id-1′ :
        Γ »∙ A₁ »∙ wk1 A₁ »∙ Id (wk[ 2 ]′ A₁) (wk[ 2 ]′ t₁) (var x1) ⊢
        Id (wk[ 3 ]′ A₁) (wk[ 3 ]′ u₁) (var x1)
      ⊢Id-1′ =
        Idⱼ′
          (wkTerm (ʷ⊇-drop (∙ ⊢Id-1)) ⊢u₁)
          (PE.subst (_⊢_∷_ _ _) wk[]≡wk[]′ $
           var₁ ⊢Id-1)

    opaque
      ⊢A₁″ :
        Γ »∙ A₁ »∙ wk1 A₁ »∙ Id (wk[ 2 ]′ A₁) (wk[ 2 ]′ t₁) (var x1) »∙
        Id (wk[ 3 ]′ A₁) (wk[ 3 ]′ u₁) (var x1) ⊢
        wk[ 4 ]′ A₁
      ⊢A₁″ =
        univ $ wkTerm (ʷ⊇-drop (∙ ⊢Id-1′)) ⊢A₁

    opaque
      ⊢A₁‴ :
        Γ »∙ A₁ »∙ wk1 A₁ »∙ Id (wk[ 2 ]′ A₁) (wk[ 2 ]′ t₁) (var x1) »∙
        Id (wk[ 3 ]′ A₁) (wk[ 3 ]′ u₁) (var x1) »∙ wk[ 4 ]′ A₁ ⊢
        wk[ 5 ]′ A₁
      ⊢A₁‴ =
        univ $ wkTerm (ʷ⊇-drop (∙ ⊢A₁″)) ⊢A₁

    opaque
      ⊢Id-1-0 :
        Γ »∙ A₁ »∙ wk1 A₁ »∙
        Id (wk[ 2 ]′ A₁) (wk[ 2 ]′ t₁) (var x1) »∙
        Id (wk[ 3 ]′ A₁) (wk[ 3 ]′ u₁) (var x1) »∙
        wk[ 4 ]′ A₁ »∙ wk1 (wk[ 4 ]′ A₁) ⊢
        Id (wk[ 6 ]′ A₁) (var x1) (var x0) ∷ U l
      ⊢Id-1-0 =
        PE.subst₃ _⊢_∷_
          (PE.cong (_»_ _) (PE.cong (_∙_ _) $ wk[]-wk[]′-comp 1))
          PE.refl PE.refl $
        Idⱼ
          (wkTerm (ʷ⊇-drop (∙ ⊢A₁‴)) ⊢A₁)
          (PE.subst (_⊢_∷_ _ _) (PE.sym $ wk[]-wk[]′-comp 2) $
           var₁ ⊢A₁‴)
          (PE.subst (_⊢_∷_ _ _) (PE.sym $ wk[]-wk[]′-comp 1) $
           var₀ ⊢A₁‴)

    opaque
      ⊢1′ :
        Γ »∙ A₁ »∙ wk1 A₁ »∙
        Id (wk[ 2 ]′ A₁) (wk[ 2 ]′ t₁) (var x1) »∙
        Id (wk[ 3 ]′ A₁) (wk[ 3 ]′ u₁) (var x1) ⊢
        var x1 ∷ Id (wk[ 4 ]′ A₁) (wk[ 4 ]′ t₁) (var x3)
      ⊢1′ =
        PE.subst (_⊢_∷_ _ _)
          (PE.sym $
           PE.cong₃ Id
             (wk[]-wk[]′-comp 2) (wk[]-wk[]′-comp 2) PE.refl) $
        var₁ ⊢Id-1′

    opaque
      ⊢0 :
        Γ »∙ A₁ »∙ wk1 A₁ »∙
        Id (wk[ 2 ]′ A₁) (wk[ 2 ]′ t₁) (var x1) »∙
        Id (wk[ 3 ]′ A₁) (wk[ 3 ]′ u₁) (var x1) ⊢
        var x0 ∷ Id (wk[ 4 ]′ A₁) (wk[ 4 ]′ u₁) (var x2)
      ⊢0 =
        PE.subst (_⊢_∷_ _ _)
          (PE.cong₃ Id (wk-comp _ _ _) (wk-comp _ _ _) PE.refl) $
        var₀ ⊢Id-1′

    rfl-case : Term n
    rfl-case =
      lam p $ lam p $ lam p $ lam p $
      cong₂ ω (wk[ 4 ]′ A₁) (wk[ 4 ]′ t₁) (var x3) (wk[ 4 ]′ A₁)
        (wk[ 4 ]′ u₁) (var x2) (U l)
        (Id (wk[ 6 ]′ A₁) (var x1) (var x0)) (var x1) (var x0)

    opaque
      ⊢rfl-case : Γ ⊢ rfl-case ∷ Motive [ A₁ , rfl ]₁₀
      ⊢rfl-case =
        lamⱼ′ ok $ lamⱼ′ ok $ lamⱼ′ ok $ lamⱼ′ ok $
        PE.subst (_⊢_∷_ _ _)
          (Id (U l)
             (Id (wk[ 6 ]′ A₁ [ wk[ 4 ]′ t₁ , wk[ 4 ]′ u₁ ]₁₀)
                (wk[ 4 ]′ t₁) (wk[ 4 ]′ u₁))
             (Id (wk[ 6 ]′ A₁ [ var x3 , var x2 ]₁₀) (var x3) (var x2))  ≡⟨ PE.cong₂ (Id _)
                                                                              (PE.trans (PE.cong₃ Id (wk[2+]′-[,]≡ {t = A₁}) PE.refl PE.refl) $
                                                                               PE.sym wk[2+]′[,⇑]≡)
                                                                              (PE.cong₃ Id
                                                                                 (PE.trans wk[2+]′-[,]≡ $
                                                                                  PE.sym $ wk[]≡wk[]′ {k = 4})
                                                                                 PE.refl PE.refl) ⟩
           Id (U l)
             (wk[ 6 ]′ (Id A₁ t₁ u₁)
                [ consSubst (sgSubst A₁) rfl ⇑[ 4 ] ])
             (Id (wk[ 4 ] A₁) (var x3) (var x2))                         ∎) $
        stabilityTerm
          (refl-∙
             (univ
                (Id (wk[ 2 ]′ A₁) (wk[ 2 ]′ t₁) (var x1)                 ≡˘⟨ Id-cong (refl (wkTerm (ʷ⊇-drop (∙ ⊢A₁′)) ⊢A₁))
                                                                               (wkEqTerm (ʷ⊇-drop (∙ ⊢A₁′)) (cast-≡ ⊢A₁ ⊢t₁))
                                                                               (_⊢_≡_∷_.refl $
                                                                                PE.subst (_⊢_∷_ _ _) wk[]≡wk[]′ $
                                                                                var₁ ⊢A₁′) ⟩⊢∎≡
                 Id (wk[ 2 ]′ A₁) (wk[ 2 ]′ (cast l A₁ A₁ rfl t₁))
                   (var x1)                                              ≡˘⟨ PE.cong₃ Id
                                                                               (wk[]≡wk[]′ {k = 2})
                                                                               (PE.trans cast-[] $
                                                                                PE.trans
                                                                                  (PE.cong₄ (cast _)
                                                                                     wk[2+]′[,⇑]≡ wk[]≡wk[]′ PE.refl wk[2+]′[,⇑]≡) $
                                                                                PE.sym wk-cast)
                                                                               PE.refl ⟩
                Id (wk[ 2 ] A₁)
                  (cast l (wk[ 4 ]′ A₁) (var x3) (var x2) (wk[ 4 ]′ t₁)
                     [ consSubst (sgSubst A₁) rfl ⇑[ 2 ] ])
                  (var x1)                                               ∎)) ∙
           univ
              (Id (wk[ 3 ]′ A₁) (wk[ 3 ]′ u₁) (var x1)                  ≡˘⟨ Id-cong (refl (wkTerm (ʷ⊇-drop (∙ ⊢Id-1)) ⊢A₁))
                                                                              (wkEqTerm (ʷ⊇-drop (∙ ⊢Id-1)) (cast-≡ ⊢A₁ ⊢u₁))
                                                                              (_⊢_≡_∷_.refl $
                                                                               PE.subst (_⊢_∷_ _ _) wk[]≡wk[]′ $
                                                                               var₁ ⊢Id-1) ⟩⊢∎≡
               Id (wk[ 3 ]′ A₁) (wk[ 3 ]′ (cast l A₁ A₁ rfl u₁))
                 (var x1)                                               ≡˘⟨ PE.cong₃ Id
                                                                              wk[]≡wk[]′
                                                                              (PE.trans cast-[] $
                                                                               PE.trans
                                                                                 (PE.cong₄ (cast _)
                                                                                    wk[2+]′[,⇑]≡ wk[]≡wk[]′ PE.refl wk[2+]′[,⇑]≡) $
                                                                               PE.sym wk-cast)
                                                                              PE.refl ⟩
               Id (wk[ 3 ] A₁)
                 (cast l (wk[ 5 ]′ A₁) (var x4) (var x3) (wk[ 5 ]′ u₁)
                    [ consSubst (sgSubst A₁) rfl ⇑[ 3 ] ])
                 (var x1)                                               ∎)) $
        ⊢cong₂ ⊢Id-1-0 ⊢1′ ⊢0

    J-app : Term n
    J-app = J ω ω (U l) A₁ Motive rfl-case A₂ t

    opaque
      ⊢J :
        Γ ⊢ J-app ∷
        Π p , q ▷ A₂ ▹
        Π p , q ▷ wk1 A₂ ▹
        Π p , q ▷
          Id (wk[ 2 ]′ A₂) (wk[ 2 ]′ (cast l A₁ A₂ t t₁)) (var x1) ▹
        Π p , q ▷
          Id (wk[ 3 ]′ A₂) (wk[ 3 ]′ (cast l A₁ A₂ t u₁)) (var x1) ▹
        Id (U l) (wk[ 4 ]′ (Id A₁ t₁ u₁))
          (Id (wk[ 4 ]′ A₂) (var x3) (var x2))
      ⊢J =
        PE.subst (_⊢_∷_ _ _)
          (Motive [ A₂ , t ]₁₀                                           ≡⟨ PE.cong (Π p , q ▷ A₂ ▹_) $
                                                                            PE.cong (Π p , q ▷ wk1 A₂ ▹_) $
                                                                            PE.cong₂ (Π p , q ▷_▹_)
                                                                              (PE.cong₃ Id
                                                                                 wk[]≡wk[]′
                                                                                 (PE.trans cast-[] $
                                                                                  PE.trans
                                                                                    (PE.cong₄ (cast _)
                                                                                       wk[2+]′[,⇑]≡ wk[]≡wk[]′ wk[]≡wk[]′ wk[2+]′[,⇑]≡) $
                                                                                  PE.sym wk-cast)
                                                                                 PE.refl)
                                                                              (PE.cong₂ (Π p , q ▷_▹_)
                                                                                 (PE.cong₃ Id
                                                                                    wk[]≡wk[]′
                                                                                    (PE.trans cast-[] $
                                                                                     PE.trans
                                                                                       (PE.cong₄ (cast _)
                                                                                          wk[2+]′[,⇑]≡ wk[]≡wk[]′ wk[]≡wk[]′ wk[2+]′[,⇑]≡) $
                                                                                     PE.sym wk-cast)
                                                                                    PE.refl)
                                                                                 (PE.cong₂ (Id _)
                                                                                    wk[2+]′[,⇑]≡
                                                                                    (PE.cong₃ Id wk[]≡wk[]′ PE.refl PE.refl))) ⟩
           Π p , q ▷ A₂ ▹
           Π p , q ▷ wk1 A₂ ▹
           Π p , q ▷
             Id (wk[ 2 ]′ A₂) (wk[ 2 ]′ (cast l A₁ A₂ t t₁)) (var x1) ▹
           Π p , q ▷
             Id (wk[ 3 ]′ A₂) (wk[ 3 ]′ (cast l A₁ A₂ t u₁)) (var x1) ▹
           Id (U l) (wk[ 4 ]′ (Id A₁ t₁ u₁))
            (Id (wk[ 4 ]′ A₂) (var x3) (var x2))                         ∎) $
        Jⱼ′ ⊢Motive ⊢rfl-case ⊢t

    opaque
      ⊢J∘ :
        Γ ⊢ J-app ∘⟨ p ⟩ t₂ ∷
        Π p , q ▷ A₂ ▹
        Π p , q ▷ wk1 (Id A₂ (cast l A₁ A₂ t t₁) t₂) ▹
        Π p , q ▷
          Id (wk[ 2 ]′ A₂) (wk[ 2 ]′ (cast l A₁ A₂ t u₁)) (var x1) ▹
        Id (U l) (wk[ 3 ]′ (Id A₁ t₁ u₁))
          (Id (wk[ 3 ]′ A₂) (wk[ 3 ]′ t₂) (var x2))
      ⊢J∘ =
        PE.subst (_⊢_∷_ _ _)
          (Π p , q ▷ wk1 A₂ ▹
           Π p , q ▷
             Id (wk[ 2 ]′ A₂) (wk[ 2 ]′ (cast l A₁ A₂ t t₁)) (var x1) ▹
           Π p , q ▷
             Id (wk[ 3 ]′ A₂) (wk[ 3 ]′ (cast l A₁ A₂ t u₁)) (var x1) ▹
           Id (U l) (wk[ 4 ]′ (Id A₁ t₁ u₁))
             (Id (wk[ 4 ]′ A₂) (var x3) (var x2))
           [ t₂ ]₀                                                       ≡⟨ PE.cong₂ (Π p , q ▷_▹_)
                                                                              (wk1-sgSubst _ _)
                                                                              (PE.cong₂ (Π p , q ▷_▹_)
                                                                                 (PE.cong₃ Id wk[+1]′-[₀⇑]≡ wk[+1]′-[₀⇑]≡ PE.refl)
                                                                                 (PE.cong₂ (Π p , q ▷_▹_)
                                                                                    (PE.cong₃ Id wk[+1]′-[₀⇑]≡ wk[+1]′-[₀⇑]≡ PE.refl)
                                                                                    (PE.cong₂ (Id _)
                                                                                       wk[+1]′-[₀⇑]≡
                                                                                       (PE.cong₃ Id wk[+1]′-[₀⇑]≡ wk[]≡wk[]′ PE.refl) ))) ⟩
           Π p , q ▷ A₂ ▹
           Π p , q ▷ wk1 (Id A₂ (cast l A₁ A₂ t t₁) t₂) ▹
           Π p , q ▷
             Id (wk[ 2 ]′ A₂) (wk[ 2 ]′ (cast l A₁ A₂ t u₁)) (var x1) ▹
           Id (U l) (wk[ 3 ]′ (Id A₁ t₁ u₁))
             (Id (wk[ 3 ]′ A₂) (wk[ 3 ]′ t₂) (var x2))                   ∎) $
        ⊢J ∘ⱼ ⊢t₂

    opaque
      ⊢J∘² :
        Γ ⊢ J-app ∘⟨ p ⟩ t₂ ∘⟨ p ⟩ u₂ ∷
        Π p , q ▷ Id A₂ (cast l A₁ A₂ t t₁) t₂ ▹
        wk1
          (Π p , q ▷ Id A₂ (cast l A₁ A₂ t u₁) u₂ ▹
           wk1 (Id (U l) (Id A₁ t₁ u₁) (Id A₂ t₂ u₂)))
      ⊢J∘² =
        PE.subst (_⊢_∷_ _ _)
          (Π p , q ▷ wk1 (Id A₂ (cast l A₁ A₂ t t₁) t₂) ▹
           Π p , q ▷
             Id (wk[ 2 ]′ A₂) (wk[ 2 ]′ (cast l A₁ A₂ t u₁)) (var x1) ▹
           Id (U l) (wk[ 3 ]′ (Id A₁ t₁ u₁))
            (Id (wk[ 3 ]′ A₂) (wk[ 3 ]′ t₂) (var x2))
           [ u₂ ]₀                                                       ≡⟨ PE.cong₂ (Π p , q ▷_▹_)
                                                                              (wk1-sgSubst _ _)
                                                                              (PE.cong₂ (Π p , q ▷_▹_)
                                                                                 (PE.cong₃ Id wk[+1]′-[₀⇑]≡ wk[+1]′-[₀⇑]≡ PE.refl)
                                                                                 (PE.trans
                                                                                    (PE.cong₂ (Id _)
                                                                                       wk[+1]′-[₀⇑]≡
                                                                                       (PE.cong₃ Id wk[+1]′-[₀⇑]≡ wk[+1]′-[₀⇑]≡ wk[]≡wk[]′)) $
                                                                                  PE.sym $ wk-comp _ _ _)) ⟩
           Π p , q ▷ Id A₂ (cast l A₁ A₂ t t₁) t₂ ▹
           wk1
             (Π p , q ▷ Id A₂ (cast l A₁ A₂ t u₁) u₂ ▹
              wk1 (Id (U l) (Id A₁ t₁ u₁) (Id A₂ t₂ u₂)))                ∎) $
        ⊢J∘ ∘ⱼ ⊢u₂

    opaque
      ⊢J∘³ :
        Γ ⊢ J-app ∘⟨ p ⟩ t₂ ∘⟨ p ⟩ u₂ ∘⟨ p ⟩ u ∷
        Π p , q ▷ Id A₂ (cast l A₁ A₂ t u₁) u₂ ▹
        wk1 (Id (U l) (Id A₁ t₁ u₁) (Id A₂ t₂ u₂))
      ⊢J∘³ =
        PE.subst (_⊢_∷_ _ _) (wk1-sgSubst _ _) $
        ⊢J∘² ∘ⱼ ⊢u

    opaque
      ⊢J∘⁴ :
        Γ ⊢ J-app ∘⟨ p ⟩ t₂ ∘⟨ p ⟩ u₂ ∘⟨ p ⟩ u ∘⟨ p ⟩ v ∷
        Id (U l) (Id A₁ t₁ u₁) (Id A₂ t₂ u₂)
      ⊢J∘⁴ =
        PE.subst (_⊢_∷_ _ _) (wk1-sgSubst _ _) $
        ⊢J∘³ ∘ⱼ ⊢v

opaque

  -- A variant of Id-cong-Idˡ.

  Id-cong-Idʳ :
    Π-allowed p q →
    Η ⊢ t ∷ Id (U l) A₂ A₁ →
    Η ⊢ u ∷ Id A₁ t₁ (cast l A₂ A₁ t t₂) →
    Η ⊢ v ∷ Id A₁ u₁ (cast l A₂ A₁ t u₂) →
    ∃ λ w → Η ⊢ w ∷ Id (U l) (Id A₁ t₁ u₁) (Id A₂ t₂ u₂)
  Id-cong-Idʳ ok ⊢t ⊢u ⊢v =
    Id-cong-Idˡ ok (⊢symmetry ⊢t) (cast-right-left ⊢t ⊢u .proj₂)
      (cast-right-left ⊢t ⊢v .proj₂)
