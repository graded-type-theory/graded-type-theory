------------------------------------------------------------------------
-- Derived rules related to Σ-types
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.DerivedRules.Sigma
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Consequences.DerivedRules.Pi-Sigma R
open import Definition.Typed.Consequences.Inequality R
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Reduction R
open import Definition.Typed.Consequences.Substitution R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Properties R
open import Definition.Typed.Weakening R as W

open import Definition.Untyped M as U
  hiding (_∷_) renaming (_[_,_] to _[_∣_])
open import Definition.Untyped.Properties M
open import Definition.Untyped.Sigma M as Sigma using (prodrecₚ)

open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation

private variable
  n                                           : Nat
  Γ                                           : Con _ _
  A A₁ A₂ B B₁ B₂ C C₁ C₂ t t₁ t₂ u u₁ u₂ v w : Term _
  p q q′ r                                    : M
  s s′                                        : SigmaMode

------------------------------------------------------------------------
-- Some derived rules

-- A variant of the typing rule for prod.

⊢prod :
  Γ ∙ A ⊢ B →
  Γ ⊢ t ∷ A →
  Γ ⊢ u ∷ B [ t ]₀ →
  Σ-allowed s p q →
  Γ ⊢ prod s p t u ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B
⊢prod ⊢B ⊢t = prodⱼ (syntacticTerm ⊢t) ⊢B ⊢t

opaque

  -- A variant of the typing rule for fst.

  fstⱼ′ :
    Γ ⊢ t ∷ Σₚ p , q ▷ A ▹ B →
    Γ ⊢ fst p t ∷ A
  fstⱼ′ ⊢t =
    case inversion-ΠΣ (syntacticTerm ⊢t) of λ {
      (⊢A , ⊢B , _) →
    fstⱼ ⊢A ⊢B ⊢t }

opaque

  -- A variant of the typing rule for snd.

  sndⱼ′ :
    Γ ⊢ t ∷ Σₚ p , q ▷ A ▹ B →
    Γ ⊢ snd p t ∷ B [ fst p t ]₀
  sndⱼ′ ⊢t =
    case inversion-ΠΣ (syntacticTerm ⊢t) of λ {
      (⊢A , ⊢B , _) →
    sndⱼ ⊢A ⊢B ⊢t }

opaque

  -- A variant of the typing rule for prodrec.

  prodrecⱼ′ :
    Γ ∙ Σᵣ p , q′ ▷ A ▹ B ⊢ C →
    Γ ⊢ t ∷ Σᵣ p , q′ ▷ A ▹ B →
    Γ ∙ A ∙ B ⊢ u ∷ C [ prodᵣ p (var x1) (var x0) ]↑² →
    Γ ⊢ prodrec r p q C t u ∷ C [ t ]₀
  prodrecⱼ′ ⊢C ⊢t ⊢u =
    case inversion-ΠΣ (syntacticTerm ⊢t) of λ {
      (⊢A , ⊢B , ok) →
    prodrecⱼ ⊢A ⊢B ⊢C ⊢t ⊢u ok }

opaque

  -- A variant of prod-cong.

  prod-cong′ :
    Γ ∙ A ⊢ B →
    Γ ⊢ t₁ ≡ t₂ ∷ A →
    Γ ⊢ u₁ ≡ u₂ ∷ B [ t₁ ]₀ →
    Σ-allowed s p q →
    Γ ⊢ prod s p t₁ u₁ ≡ prod s p t₂ u₂ ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B
  prod-cong′ ⊢B t₁≡t₂ =
    prod-cong (syntacticEqTerm t₁≡t₂ .proj₁) ⊢B t₁≡t₂

opaque

  -- A variant of fst-subst.

  fst-subst′ :
    Γ ⊢ t ⇒ u ∷ Σₚ p , q ▷ A ▹ B →
    Γ ⊢ fst p t ⇒ fst p u ∷ A
  fst-subst′ t⇒u =
    case inversion-ΠΣ (syntacticTerm (redFirstTerm t⇒u)) of λ {
      (⊢A , ⊢B , _) →
    fst-subst ⊢A ⊢B t⇒u }

opaque

  -- A variant of fst-cong.

  fst-cong′ :
    Γ ⊢ t ≡ u ∷ Σₚ p , q ▷ A ▹ B →
    Γ ⊢ fst p t ≡ fst p u ∷ A
  fst-cong′ t≡u =
    case inversion-ΠΣ (syntacticEqTerm t≡u .proj₁) of λ {
      (⊢A , ⊢B , _) →
    fst-cong ⊢A ⊢B t≡u }

opaque

  -- A variant of snd-subst.

  snd-subst′ :
    Γ ⊢ t ⇒ u ∷ Σₚ p , q ▷ A ▹ B →
    Γ ⊢ snd p t ⇒ snd p u ∷ B [ fst p t ]₀
  snd-subst′ t⇒u =
    case inversion-ΠΣ (syntacticTerm (redFirstTerm t⇒u)) of λ {
      (⊢A , ⊢B , _) →
    snd-subst ⊢A ⊢B t⇒u }

opaque

  -- A variant of snd-cong.

  snd-cong′ :
    Γ ⊢ t ≡ u ∷ Σₚ p , q ▷ A ▹ B →
    Γ ⊢ snd p t ≡ snd p u ∷ B [ fst p t ]₀
  snd-cong′ t≡u =
    case inversion-ΠΣ (syntacticEqTerm t≡u .proj₁) of λ {
      (⊢A , ⊢B , _) →
    snd-cong ⊢A ⊢B t≡u }

opaque

  -- A variant of prodrec-subst.

  prodrec-subst′ :
    Γ ∙ (Σᵣ p , q′ ▷ A ▹ B) ⊢ C →
    Γ ∙ A ∙ B ⊢ u ∷ C [ prodᵣ p (var x1) (var x0) ]↑² →
    Γ ⊢ t₁ ⇒ t₂ ∷ Σᵣ p , q′ ▷ A ▹ B →
    Σᵣ-allowed p q′ →
    Γ ⊢ prodrec r p q C t₁ u ⇒ prodrec r p q C t₂ u ∷ C [ t₁ ]₀
  prodrec-subst′ ⊢C ⊢u t₁⇒t₂ =
    case inversion-ΠΣ (syntacticTerm (redFirstTerm t₁⇒t₂)) of λ {
      (⊢A , ⊢B , _) →
    prodrec-subst ⊢A ⊢B ⊢C ⊢u t₁⇒t₂ }

opaque

  -- A variant of prodrec-cong.

  prodrec-cong′ :
    Γ ∙ (Σᵣ p , q′ ▷ A ▹ B) ⊢ C₁ ≡ C₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ Σᵣ p , q′ ▷ A ▹ B →
    Γ ∙ A ∙ B ⊢ u₁ ≡ u₂ ∷ C₁ [ prodᵣ p (var x1) (var x0) ]↑² →
    Γ ⊢ prodrec r p q C₁ t₁ u₁ ≡ prodrec r p q C₂ t₂ u₂ ∷ C₁ [ t₁ ]₀
  prodrec-cong′ C₁≡C₂ t₁≡t₂ u₁≡u₂ =
    case inversion-ΠΣ (syntacticEqTerm t₁≡t₂ .proj₁) of λ {
      (⊢A , ⊢B , ok) →
    prodrec-cong ⊢A ⊢B C₁≡C₂ t₁≡t₂ u₁≡u₂ ok }

opaque

  -- A variant of the reduction rule Σ-β₁.

  Σ-β₁-⇒ :
    Γ ∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Σₚ-allowed p q →
    Γ ⊢ fst p (prodₚ p t u) ⇒ t ∷ A
  Σ-β₁-⇒ ⊢B ⊢t ⊢u =
    Σ-β₁ (syntacticTerm ⊢t) ⊢B ⊢t ⊢u PE.refl

opaque

  -- A variant of the equality rule Σ-β₁.

  Σ-β₁-≡ :
    Γ ∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Σₚ-allowed p q →
    Γ ⊢ fst p (prodₚ p t u) ≡ t ∷ A
  Σ-β₁-≡ ⊢B ⊢t ⊢u ok =
    subsetTerm (Σ-β₁-⇒ ⊢B ⊢t ⊢u ok)

opaque

  -- A variant of the reduction rule Σ-β₂.

  Σ-β₂-⇒ :
    Γ ∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Σₚ-allowed p q →
    Γ ⊢ snd p (prodₚ p t u) ⇒ u ∷ B [ fst p (prodₚ p t u) ]₀
  Σ-β₂-⇒ ⊢B ⊢t ⊢u =
    Σ-β₂ (syntacticTerm ⊢t) ⊢B ⊢t ⊢u PE.refl

opaque

  -- A variant of the equality rule Σ-β₂.

  Σ-β₂-≡ :
    Γ ∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Σₚ-allowed p q →
    Γ ⊢ snd p (prodₚ p t u) ≡ u ∷ B [ fst p (prodₚ p t u) ]₀
  Σ-β₂-≡ ⊢B ⊢t ⊢u ok =
    subsetTerm (Σ-β₂-⇒ ⊢B ⊢t ⊢u ok)

opaque

  -- A variant of the reduction rule prodrec-β.

  prodrec-β-⇒ :
    Γ ∙ (Σᵣ p , q′ ▷ A ▹ B) ⊢ C →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Γ ∙ A ∙ B ⊢ v ∷ C [ prodᵣ p (var x1) (var x0) ]↑² →
    Σᵣ-allowed p q′ →
    Γ ⊢ prodrec r p q C (prodᵣ p t u) v ⇒ v [ t ∣ u ] ∷
      C [ prodᵣ p t u ]₀
  prodrec-β-⇒ ⊢C ⊢t ⊢u ⊢v ok =
    case wf ⊢C of λ {
      (_ ∙ ⊢ΣAB) →
    case inversion-ΠΣ ⊢ΣAB of λ {
      (⊢A , ⊢B , _) →
    prodrec-β ⊢A ⊢B ⊢C ⊢t ⊢u ⊢v PE.refl ok }}

opaque

  -- A variant of the equality rule prodrec-β.

  prodrec-β-≡ :
    Γ ∙ (Σᵣ p , q′ ▷ A ▹ B) ⊢ C →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Γ ∙ A ∙ B ⊢ v ∷ C [ prodᵣ p (var x1) (var x0) ]↑² →
    Σᵣ-allowed p q′ →
    Γ ⊢ prodrec r p q C (prodᵣ p t u) v ≡ v [ t ∣ u ] ∷
      C [ prodᵣ p t u ]₀
  prodrec-β-≡ ⊢C ⊢t ⊢u ⊢v ok =
    subsetTerm (prodrec-β-⇒ ⊢C ⊢t ⊢u ⊢v ok)

opaque

  -- A variant of Σ-η.

  Σ-η′ :
    Γ ⊢ t ∷ Σₚ p , q ▷ A ▹ B →
    Γ ⊢ u ∷ Σₚ p , q ▷ A ▹ B →
    Γ ⊢ fst p t ≡ fst p u ∷ A →
    Γ ⊢ snd p t ≡ snd p u ∷ B [ fst p t ]₀ →
    Γ ⊢ t ≡ u ∷ Σₚ p , q ▷ A ▹ B
  Σ-η′ ⊢t =
    case inversion-ΠΣ (syntacticTerm ⊢t) of λ {
      (⊢A , ⊢B , _) →
    Σ-η ⊢A ⊢B ⊢t }

-- An η-rule for strong Σ-types.

Σ-η-prod-fst-snd :
  Γ ⊢ t ∷ Σₚ p , q ▷ A ▹ B →
  Γ ⊢ prodₚ p (fst p t) (snd p t) ≡ t ∷ Σₚ p , q ▷ A ▹ B
Σ-η-prod-fst-snd ⊢t = Σ-η′
  (⊢prod ⊢B ⊢fst ⊢snd ok)
  ⊢t
  (Σ-β₁-≡ ⊢B ⊢fst ⊢snd ok)
  (Σ-β₂-≡ ⊢B ⊢fst ⊢snd ok)
  where
  ⊢B,ok = inversion-ΠΣ (syntacticTerm ⊢t) .proj₂
  ⊢B    = ⊢B,ok .proj₁
  ok    = ⊢B,ok .proj₂
  ⊢fst  = fstⱼ′ ⊢t
  ⊢snd  = sndⱼ′ ⊢t

-- An "inverse" of prod-cong for Σₚ.

prod-cong⁻¹-Σₚ :
  Γ ⊢ prodₚ p t u ≡ prodₚ p v w ∷ Σₚ p , q ▷ A ▹ B →
  (Γ ∙ A ⊢ B) × Γ ⊢ t ≡ v ∷ A × Γ ⊢ u ≡ w ∷ B [ t ]₀ ×
  Σₚ-allowed p q
prod-cong⁻¹-Σₚ
  {Γ = Γ} {p = p} {t = t} {u = u} {v = v} {w = w}
  {q = q} {A = A} {B = B} prod≡prod =
  ⊢B , t≡v , u≡w , ok
  where
  ⊢ΣAB = syntacticEqTerm prod≡prod .proj₁
  ⊢B   = inversion-ΠΣ ⊢ΣAB .proj₂ .proj₁
  ok   = inversion-ΠΣ ⊢ΣAB .proj₂ .proj₂
  ⊢t,u = syntacticEqTerm prod≡prod .proj₂ .proj₁
  ⊢t   = inversion-prod-Σ ⊢t,u .proj₁
  ⊢u   = inversion-prod-Σ ⊢t,u .proj₂ .proj₁
  ⊢v,w = syntacticEqTerm prod≡prod .proj₂ .proj₂
  ⊢v   = inversion-prod-Σ ⊢v,w .proj₁
  ⊢w   = inversion-prod-Σ ⊢v,w .proj₂ .proj₁

  fst-t,u≡t = Σ-β₁-≡ ⊢B ⊢t ⊢u ok

  t≡v =                                                $⟨ prod≡prod ⟩
    Γ ⊢ prodₚ p t u ≡ prodₚ p v w ∷ Σₚ p , q ▷ A ▹ B   →⟨ fst-cong′ ⟩
    Γ ⊢ fst p (prodₚ p t u) ≡ fst p (prodₚ p v w) ∷ A  →⟨ (λ hyp → trans (sym fst-t,u≡t) (trans hyp (Σ-β₁-≡ ⊢B ⊢v ⊢w ok))) ⟩
    Γ ⊢ t ≡ v ∷ A                                      □

  u≡w =                                               $⟨ prod≡prod ⟩
    Γ ⊢ prodₚ p t u ≡ prodₚ p v w ∷ Σₚ p , q ▷ A ▹ B  →⟨ snd-cong′ ⟩

    Γ ⊢ snd p (prodₚ p t u) ≡ snd p (prodₚ p v w) ∷
      B [ fst p (prodₚ p t u) ]₀                       →⟨ (λ hyp → trans
                                                            (sym (Σ-β₂-≡ ⊢B ⊢t ⊢u ok))
                                                               (trans hyp
                                                                  (conv (Σ-β₂-≡ ⊢B ⊢v ⊢w ok)
                                                                     (substTypeEq (refl ⊢B)
                                                                        (fst-cong′ (sym prod≡prod)))))) ⟩

    Γ ⊢ u ≡ w ∷ B [ fst p (prodₚ p t u) ]₀             →⟨ flip _⊢_≡_∷_.conv (substTypeEq (refl ⊢B) fst-t,u≡t) ⟩

    Γ ⊢ u ≡ w ∷ B [ t ]₀                               □

------------------------------------------------------------------------
-- An investigation of to what degree weak Σ-types can emulate strong
-- Σ-types, and vice versa

-- The rest of this module, down to "More derived rules", consists of
-- (parts of) an investigation of to what degree weak Σ-types can
-- emulate strong Σ-types, and vice versa. This investigation was
-- prompted by a question asked by an anonymous reviewer. See also
-- Definition.Untyped.Sigma, which contains some basic definitions,
-- and Graded.Derived.Sigma, which contains properties related to
-- usage. This module contains properties related to typing.

------------------------------------------------------------------------
-- Typing and equality rules for prodrecₚ

private

  -- A lemma used below.

  ⊢[1,0]↑²[fst,snd]≡ :
    Γ ∙ (Σₚ p , q ▷ A ▹ B) ⊢ C →
    Γ ⊢ t ∷ Σₚ p , q ▷ A ▹ B →
    Γ ⊢
      C [ prodₚ p (var x1) (var x0) ]↑² [ fst p t ∣ snd p t ] ≡
      C [ t ]₀
  ⊢[1,0]↑²[fst,snd]≡
    {Γ = Γ} {p = p} {q = q} {A = A} {B = B} {C = C} {t = t} ⊢C =
    Γ ⊢ t ∷ Σₚ p , q ▷ A ▹ B                                     →⟨ Σ-η-prod-fst-snd ⟩

    Γ ⊢ prodₚ p (fst p t) (snd p t) ≡ t ∷ Σₚ p , q ▷ A ▹ B       →⟨ substTypeEq (refl ⊢C) ⟩

    Γ ⊢ C [ prodₚ p (fst p t) (snd p t) ]₀ ≡ C [ t ]₀              →⟨ PE.subst (_ ⊢_≡ _) (PE.sym $ [1,0]↑²[,] C) ⟩

    Γ ⊢
      C [ prodₚ p (var x1) (var x0) ]↑² [ fst p t ∣ snd p t ] ≡
      C [ t ]₀                                                    □

-- A typing rule for prodrecₚ.

prodrecₚⱼ :
  Γ ∙ (Σₚ p , q ▷ A ▹ B) ⊢ C →
  Γ ⊢ t ∷ Σₚ p , q ▷ A ▹ B →
  Γ ∙ A ∙ B ⊢ u ∷ C [ prodₚ p (var x1) (var x0) ]↑² →
  Γ ⊢ prodrecₚ p t u ∷ C [ t ]₀
prodrecₚⱼ
  {Γ = Γ} {p = p} {q = q} {A = A} {B = B} {C = C} {t = t} {u = u}
  ⊢C ⊢t ⊢u =                                                 $⟨ fstⱼ′ ⊢t , sndⱼ′ ⊢t ⟩
  Γ ⊢ fst p t ∷ A ×
  Γ ⊢ snd p t ∷ B [ fst p t ]₀                                →⟨ (λ (hyp₁ , hyp₂) →
                                                                   PE.subst (_ ⊢ _ ∷_) (PE.sym (subst-id _)) hyp₁ , hyp₂) ⟩
  Γ ⊢ fst p t ∷ A [ idSubst ] ×
  Γ ⊢ snd p t ∷ B [ fst p t ]₀                                →⟨ (λ (hyp₁ , hyp₂) → (idSubst′ ⊢Γ , hyp₁) , hyp₂) ⟩

  Γ ⊢ˢ
    consSubst (consSubst idSubst (fst p t)) (snd p t) ∷
    Γ ∙ A ∙ B                                                →⟨ flip (substitutionTerm ⊢u) ⊢Γ ⟩

  Γ ⊢
    prodrecₚ p t u ∷
    C [ prodₚ p (var x1) (var x0) ]↑² [ fst p t ∣ snd p t ]  →⟨ flip conv (⊢[1,0]↑²[fst,snd]≡ ⊢C ⊢t) ⟩

  Γ ⊢ prodrecₚ p t u ∷ C [ t ]₀                               □
  where
  ⊢Γ = wfTerm ⊢t

-- An equality rule for prodrecₚ.

prodrecₚ-β :
  Γ ⊢ t ∷ A →
  Γ ⊢ u ∷ B [ t ]₀ →
  Γ ∙ A ∙ B ⊢ v ∷ C [ prodₚ p (var x1) (var x0) ]↑² →
  Σₚ-allowed p q →
  Γ ⊢ prodrecₚ p (prodₚ p t u) v ≡ v [ t ∣ u ] ∷ C [ prodₚ p t u ]₀
prodrecₚ-β
  {Γ = Γ} {t = t} {A = A} {u = u} {B = B} {v = v} {C = C} {p = p}
  ⊢t ⊢u ⊢v ok =                                                     $⟨ Σ-β₁-≡ ⊢B ⊢t ⊢u ok
                                                                     , Σ-β₂-≡ ⊢B ⊢t ⊢u ok
                                                                     ⟩
  Γ ⊢ fst p (prodₚ p t u) ≡ t ∷ A ×
  Γ ⊢ snd p (prodₚ p t u) ≡ u ∷ B [ fst p (prodₚ p t u) ]₀           →⟨ (λ (hyp₁ , hyp₂) →
                                                                            PE.subst (_ ⊢ _ ≡ _ ∷_) (PE.sym $ subst-id _) hyp₁
                                                                          , conv hyp₂ (substTypeEq (refl ⊢B) hyp₁)) ⟩
  Γ ⊢ fst p (prodₚ p t u) ≡ t ∷ A [ idSubst ] ×
  Γ ⊢ snd p (prodₚ p t u) ≡ u ∷ B [ t ]₀                             →⟨ (λ (hyp₁ , hyp₂) →
                                                                          (substRefl (idSubst′ ⊢Γ) , sym hyp₁) , sym hyp₂) ⟩
  Γ ⊢ˢ
    consSubst (consSubst idSubst t) u ≡
    consSubst (consSubst idSubst (fst p (prodₚ p t u)))
      (snd p (prodₚ p t u)) ∷
    Γ ∙ A ∙ B                                                       →⟨ flip (substitutionEqTerm (refl ⊢v)) ⊢Γ ⟩

  Γ ⊢
    v [ t ∣ u ] ≡
    prodrecₚ p (prodₚ p t u) v ∷
    C [ prodₚ p (var x1) (var x0) ]↑² [ t ∣ u ]                     →⟨ PE.subst (_⊢_≡_∷_ _ _ _) ([1,0]↑²[,] C) ∘→ sym ⟩

  Γ ⊢ prodrecₚ p (prodₚ p t u) v ≡ v [ t ∣ u ] ∷ C [ prodₚ p t u ]₀  □
  where
  ⊢Γ = wfTerm ⊢t
  ⊢B = case wfTerm ⊢v of λ where
         (_ ∙ _ ∙ ⊢B) → ⊢B

-- Another equality rule for prodrecₚ.

prodrecₚ-cong :
  Γ ∙ (Σₚ p , q ▷ A ▹ B) ⊢ C →
  Γ ⊢ t₁ ≡ t₂ ∷ Σₚ p , q ▷ A ▹ B →
  Γ ∙ A ∙ B ⊢ u₁ ≡ u₂ ∷ C [ prodₚ p (var x1) (var x0) ]↑² →
  Γ ⊢ prodrecₚ p t₁ u₁ ≡ prodrecₚ p t₂ u₂ ∷ C [ t₁ ]₀
prodrecₚ-cong
  {Γ = Γ} {p = p} {q = q} {A = A} {B = B} {C = C} {t₁ = t₁} {t₂ = t₂}
  {u₁ = u₁} {u₂ = u₂} ⊢C t₁≡t₂ u₁≡u₂ =                         $⟨ fst-cong′ t₁≡t₂ , snd-cong′ t₁≡t₂ ⟩
  Γ ⊢ fst p t₁ ≡ fst p t₂ ∷ A ×
  Γ ⊢ snd p t₁ ≡ snd p t₂ ∷ B [ fst p t₁ ]₀                     →⟨ (λ (hyp₁ , hyp₂) →
                                                                     PE.subst (_ ⊢ _ ≡ _ ∷_) (PE.sym (subst-id _)) hyp₁ , hyp₂) ⟩
  Γ ⊢ fst p t₁ ≡ fst p t₂ ∷ A [ idSubst ] ×
  Γ ⊢ snd p t₁ ≡ snd p t₂ ∷ B [ fst p t₁ ]₀                     →⟨ (λ (hyp₁ , hyp₂) → (substRefl (idSubst′ ⊢Γ) , hyp₁) , hyp₂) ⟩

  Γ ⊢ˢ
    consSubst (consSubst idSubst (fst p t₁)) (snd p t₁) ≡
    consSubst (consSubst idSubst (fst p t₂)) (snd p t₂) ∷
    Γ ∙ A ∙ B                                                   →⟨ flip (substitutionEqTerm u₁≡u₂) ⊢Γ ⟩

  Γ ⊢
    prodrecₚ p t₁ u₁ ≡
    prodrecₚ p t₂ u₂ ∷
    C [ prodₚ p (var x1) (var x0) ]↑² [ fst p t₁ ∣ snd p t₁ ]   →⟨ flip conv (⊢[1,0]↑²[fst,snd]≡ ⊢C ⊢t₁) ⟩

  Γ ⊢ prodrecₚ p t₁ u₁ ≡ prodrecₚ p t₂ u₂ ∷ C [ t₁ ]₀           □
  where
  ⊢Γ  = wfEqTerm t₁≡t₂
  ⊢t₁ = syntacticEqTerm t₁≡t₂ .proj₂ .proj₁

-- This module does not contain proofs of any reduction rules for
-- prodrecₚ. One might have hoped that the following rules should
-- hold:
--
--   Γ ∙ (Σₚ p , q ▷ A ▹ B) ⊢ C →
--   Γ ⊢ t ∷ A →
--   Γ ⊢ u ∷ B [ t ]₀ →
--   Γ ∙ A ∙ B ⊢ v ∷ C [ prodₚ p (var x1) (var x0) ]↑² →
--   Γ ⊢ prodrecₚ p (prodₚ p t u) v ⇒ v [ t ∣ u ] ∷ C [ prodₚ p t u ]₀
--
--   Γ ∙ (Σₚ p , q ▷ A ▹ B) ⊢ C →
--   Γ ∙ A ∙ B ⊢ u ∷ C [ prodᵣ p (var x1) (var x0) ]↑² →
--   Γ ⊢ t₁ ⇒ t₂ ∷ Σᵣ p , q ▷ A ▹ B →
--   Γ ⊢ prodrecₚ p t₁ u ⇒ prodrecₚ p t₂ u ∷ C [ t₁ ]₀
--
-- However, the reduction relation only allows reduction in certain
-- places in terms. For instance, it does not include reduction under
-- lambdas. Thus it seems unlikely that the rules above can be proved
-- (but there is no formal proof of this in this module).

------------------------------------------------------------------------
-- The first and second projections for weak Σ-types

-- The projections are defined using some extra quantities r′ and q′.

module Fstᵣ-sndᵣ (r′ q′ : M) where

  open Sigma.Fstᵣ-sndᵣ r′ q′ public

  ----------------------------------------------------------------------
  -- Some private lemmas related to wk1 and wk1Subst

  private

    -- Some lemmas used below.

    ⊢wk1 :
      Γ ⊢ A →
      Γ ⊢ B →
      Γ ∙ A ⊢ wk1 B
    ⊢wk1 ⊢A = W.wk (step id) (wf ⊢A ∙ ⊢A)

    Σ⊢wk1 :
      Γ ∙ A ⊢ B →
      Σᵣ-allowed p q →
      Γ ∙ (Σᵣ p , q ▷ A ▹ B) ⊢ wk1 A
    Σ⊢wk1 ⊢B ok = ⊢wk1 (ΠΣⱼ′ ⊢B ok) ⊢A
      where
      ⊢A = case wf ⊢B of λ where
             (_ ∙ ⊢A) → ⊢A

    ⊢wk1-wk1 :
      Γ ∙ A ⊢ B →
      Γ ∙ A ∙ B ⊢ wk1 (wk1 A)
    ⊢wk1-wk1 ⊢B = W.wk (step id) ⊢ΓAB (W.wk (step id) ⊢ΓA ⊢A)
      where
      ⊢ΓA  = wf ⊢B
      ⊢A   = case ⊢ΓA of λ where
               (_ ∙ ⊢A) → ⊢A
      ⊢ΓAB = ⊢ΓA ∙ ⊢B

    ⊢wk1[]≡ :
      Γ ⊢ A →
      Γ ⊢ wk1 A [ t ]₀ ≡ A
    ⊢wk1[]≡ {Γ = Γ} {A = A} {t = t} =
      Γ ⊢ A                  →⟨ refl ⟩
      (Γ ⊢ A ≡ A)            →⟨ PE.subst (_ ⊢_≡ _) (PE.sym (wk1-sgSubst _ _)) ⟩
      (Γ ⊢ wk1 A [ t ]₀ ≡ A)  □

    ⊢wk1≡ :
      Γ ⊢ A →
      Γ ⊢ B →
      Γ ∙ A ⊢ wk1 B ≡ B [ wk1Subst idSubst ]
    ⊢wk1≡ {Γ = Γ} {A = A} {B = B} ⊢A =
      Γ ⊢ B                                         →⟨ ⊢wk1 ⊢A ⟩
      Γ ∙ A ⊢ wk1 B                                 →⟨ refl ⟩
      (Γ ∙ A ⊢ wk1 B ≡ wk1 B)                       →⟨ PE.subst₂ (_ ⊢_≡_) PE.refl lemma ⟩
      (Γ ∙ A ⊢ wk1 B ≡ B [ wk1Subst idSubst ])  □
      where
      open Tools.Reasoning.PropositionalEquality

      lemma =
        wk1 B                    ≡⟨ wk≡subst _ _ ⟩
        B [ toSubst (step id) ]  ≡⟨⟩
        B [ wk1Subst idSubst ]   ∎

    ⊢wk1-wk1≡ :
      Γ ∙ A ⊢ B →
      Γ ∙ A ∙ B ⊢ wk1 (wk1 A) ≡ A [ wk1Subst (wk1Subst idSubst) ]
    ⊢wk1-wk1≡ {Γ = Γ} {A = A} {B = B} =
      Γ ∙ A ⊢ B                                                      →⟨ ⊢wk1-wk1 ⟩
      Γ ∙ A ∙ B ⊢ wk1 (wk1 A)                                        →⟨ refl ⟩
      (Γ ∙ A ∙ B ⊢ wk1 (wk1 A) ≡ wk1 (wk1 A))                        →⟨ PE.subst₂ (_ ⊢_≡_) PE.refl lemma ⟩
      (Γ ∙ A ∙ B ⊢ wk1 (wk1 A) ≡ A [ wk1Subst (wk1Subst idSubst) ])  □
      where
      open Tools.Reasoning.PropositionalEquality

      lemma =
        wk1 (wk1 A)                        ≡⟨ wk1-wk _ _ ⟩
        U.wk (step (step id)) A            ≡⟨ wk≡subst _ _ ⟩
        A [ toSubst (step (step id)) ]     ≡⟨⟩
        A [ wk1Subst (wk1Subst idSubst) ]  ∎

    ⊢ˢwk1Subst-idSubst :
      Γ ⊢ A →
      Γ ∙ A ⊢ˢ wk1Subst idSubst ∷ Γ
    ⊢ˢwk1Subst-idSubst {Γ = Γ} {A = A} ⊢A =
                                     $⟨ idSubst′ ⊢Γ ⟩
      Γ ⊢ˢ idSubst ∷ Γ               →⟨ wk1Subst′ ⊢Γ ⊢Γ ⊢A ⟩
      Γ ∙ A ⊢ˢ wk1Subst idSubst ∷ Γ  □
      where
      ⊢Γ = wf ⊢A

    ⊢ˢwk1Subst-wk1Subst-idSubst :
      Γ ∙ A ⊢ B →
      Γ ∙ A ∙ B ⊢ˢ wk1Subst (wk1Subst idSubst) ∷ Γ
    ⊢ˢwk1Subst-wk1Subst-idSubst {Γ = Γ} {A = A} {B = B} ⊢B =
      case ⊢ΓA of λ { (⊢Γ ∙ ⊢A) →
                                                    $⟨ ⊢ˢwk1Subst-idSubst ⊢A ⟩
      Γ ∙ A ⊢ˢ wk1Subst idSubst ∷ Γ                 →⟨ wk1Subst′ ⊢Γ ⊢ΓA ⊢B ⟩
      Γ ∙ A ∙ B ⊢ˢ wk1Subst (wk1Subst idSubst) ∷ Γ  □ }
      where
      ⊢ΓA = wf ⊢B

  ----------------------------------------------------------------------
  -- Typing rules for fstᵣ

  private

    -- A lemma used below.

    1∷wk1[1,0] :
      Γ ∙ A ⊢ B →
      Γ ∙ A ∙ B ⊢ var x1 ∷ wk1 A [ prodᵣ p (var x1) (var x0) ]↑²
    1∷wk1[1,0] {Γ = Γ} {A = A} {B = B} {p = p} ⊢B =                      $⟨ ⊢B ⟩
      Γ ∙ A ⊢ B                                                          →⟨ ⊢wk1-wk1 ⟩
      Γ ∙ A ∙ B ⊢ wk1 (wk1 A)                                            →⟨ refl ⟩
      (Γ ∙ A ∙ B ⊢ wk1 (wk1 A) ≡ wk1 (wk1 A))                            →⟨ PE.subst (_⊢_≡_ _ _) (PE.sym wk1-[]↑²) ⟩
      (Γ ∙ A ∙ B ⊢ wk1 (wk1 A) ≡ wk1 A [ prodᵣ p (var x1) (var x0) ]↑²)  →⟨ conv (var (wf ⊢B ∙ ⊢B) (there here)) ⟩
      (Γ ∙ A ∙ B ⊢ var x1 ∷ wk1 A [ prodᵣ p (var x1) (var x0) ]↑²)       □

  -- A typing rule for fstᵣ.

  fstᵣⱼ :
    Γ ⊢ t ∷ Σᵣ p , q ▷ A ▹ B →
    Γ ⊢ fstᵣ p A t ∷ A
  fstᵣⱼ {Γ = Γ} {t = t} {p = p} {q = q} {A = A} {B = B} ⊢t =    $⟨ Σ⊢wk1 ⊢B ok , 1∷wk1[1,0] ⊢B ⟩
    (Γ ∙ (Σᵣ p , q ▷ A ▹ B) ⊢ wk1 A) ×
    Γ ∙ A ∙ B ⊢ var x1 ∷ wk1 A [ prodᵣ p (var x1) (var x0) ]↑²  →⟨ (λ (hyp₁ , hyp₂) → prodrecⱼ′ hyp₁ ⊢t hyp₂) ⟩

    Γ ⊢ fstᵣ p A t ∷ wk1 A [ t ]₀                                →⟨ flip conv (⊢wk1[]≡ ⊢A) ⟩

    Γ ⊢ fstᵣ p A t ∷ A                                          □
    where
    ⊢A,⊢B,ok = inversion-ΠΣ (syntacticTerm ⊢t)
    ⊢A       = ⊢A,⊢B,ok .proj₁
    ⊢B       = ⊢A,⊢B,ok .proj₂ .proj₁
    ok       = ⊢A,⊢B,ok .proj₂ .proj₂

  -- A reduction rule for fstᵣ.

  fstᵣ-β-⇒ :
    Γ ∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Σᵣ-allowed p q →
    Γ ⊢ fstᵣ p A (prodᵣ p t u) ⇒ t ∷ A
  fstᵣ-β-⇒
    {Γ = Γ} {A = A} {B = B} {t = t} {u = u} {p = p} {q = q}
    ⊢B ⊢t ⊢u ok =                                                $⟨ Σ⊢wk1 ⊢B ok , 1∷wk1[1,0] ⊢B ⟩
    (Γ ∙ (Σᵣ p , q ▷ A ▹ B) ⊢ wk1 A) ×
    Γ ∙ A ∙ B ⊢ var x1 ∷ wk1 A [ prodᵣ p (var x1) (var x0) ]↑²   →⟨ (λ (hyp₁ , hyp₂) → prodrec-β-⇒ hyp₁ ⊢t ⊢u hyp₂ ok) ⟩

    Γ ⊢ fstᵣ p A (prodᵣ p t u) ⇒ t ∷ wk1 A [ prodᵣ p t u ]₀      →⟨ flip conv (⊢wk1[]≡ ⊢A) ⟩

    Γ ⊢ fstᵣ p A (prodᵣ p t u) ⇒ t ∷ A                           □
    where
    ⊢A = syntacticTerm ⊢t

  -- Another reduction rule for fstᵣ.

  fstᵣ-subst :
    Γ ∙ A ⊢ B →
    Γ ⊢ t₁ ⇒ t₂ ∷ Σᵣ p , q ▷ A ▹ B →
    Γ ⊢ fstᵣ p A t₁ ⇒ fstᵣ p A t₂ ∷ A
  fstᵣ-subst
    {Γ = Γ} {A = A} {B = B} {t₁ = t₁} {t₂ = t₂} {p = p} {q = q}
    ⊢B t₁⇒t₂ =                                                   $⟨ Σ⊢wk1 ⊢B ok , 1∷wk1[1,0] ⊢B ⟩
    (Γ ∙ (Σᵣ p , q ▷ A ▹ B) ⊢ wk1 A) ×
    Γ ∙ A ∙ B ⊢ var x1 ∷ wk1 A [ prodᵣ p (var x1) (var x0) ]↑²   →⟨ (λ (hyp₁ , hyp₂) → prodrec-subst′ hyp₁ hyp₂ t₁⇒t₂ ok) ⟩

    Γ ⊢ fstᵣ p A t₁ ⇒ fstᵣ p A t₂ ∷ wk1 A [ t₁ ]₀                →⟨ flip conv (⊢wk1[]≡ ⊢A) ⟩

    Γ ⊢ fstᵣ p A t₁ ⇒ fstᵣ p A t₂ ∷ A                            □
    where
    ⊢A = case wf ⊢B of λ where
           (_ ∙ ⊢A) → ⊢A
    ok = ⊢∷ΠΣ→ΠΣ-allowed $
         syntacticRedTerm (redMany t₁⇒t₂) .proj₂ .proj₁

  -- An equality rule for fstᵣ.

  fstᵣ-β-≡ :
    Γ ∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Σᵣ-allowed p q →
    Γ ⊢ fstᵣ p A (prodᵣ p t u) ≡ t ∷ A
  fstᵣ-β-≡ ⊢B ⊢t ⊢u ok = subsetTerm (fstᵣ-β-⇒ ⊢B ⊢t ⊢u ok)

  -- Another equality rule for fstᵣ.

  fstᵣ-cong :
    Γ ⊢ A₁ ≡ A₂ →
    Γ ∙ A₁ ⊢ B₁ →
    Γ ⊢ t₁ ≡ t₂ ∷ Σᵣ p , q ▷ A₁ ▹ B₁ →
    Γ ⊢ fstᵣ p A₁ t₁ ≡ fstᵣ p A₂ t₂ ∷ A₁
  fstᵣ-cong
    {Γ = Γ} {A₁ = A₁} {A₂ = A₂} {B₁ = B₁} {t₁ = t₁} {t₂ = t₂}
    {p = p} {q = q} A₁≡A₂ ⊢B₁ t₁≡t₂ =                              $⟨ W.wkEq (step id) (wfEq A₁≡A₂ ∙ ΠΣⱼ′ ⊢B₁ ok) A₁≡A₂
                                                                    , 1∷wk1[1,0] ⊢B₁
                                                                    ⟩
    (Γ ∙ (Σᵣ p , q ▷ A₁ ▹ B₁) ⊢ wk1 A₁ ≡ wk1 A₂) ×
    Γ ∙ A₁ ∙ B₁ ⊢ var x1 ∷ wk1 A₁ [ prodᵣ p (var x1) (var x0) ]↑²  →⟨ (λ (hyp₁ , hyp₂) → prodrec-cong′ hyp₁ t₁≡t₂ (refl hyp₂)) ⟩

    Γ ⊢ fstᵣ p A₁ t₁ ≡ fstᵣ p A₂ t₂ ∷ wk1 A₁ [ t₁ ]₀               →⟨ flip conv (⊢wk1[]≡ ⊢A₁) ⟩

    Γ ⊢ fstᵣ p A₁ t₁ ≡ fstᵣ p A₂ t₂ ∷ A₁                           □
    where
    ⊢A₁ = syntacticEq A₁≡A₂ .proj₁
    ok  = ⊢∷ΠΣ→ΠΣ-allowed $
          syntacticEqTerm t₁≡t₂ .proj₂ .proj₁

  ----------------------------------------------------------------------
  -- Some private lemmas related to fstᵣ

  private

    -- Some lemmas used below.

    fstᵣ-0[] : fstᵣ p (wk1 A) (var x0) [ t ]₀ PE.≡ fstᵣ p A t
    fstᵣ-0[] {A = A} {t = t} = PE.cong (λ A → prodrec _ _ _ A _ _) $
      wk1 (wk1 A) [ liftSubst (sgSubst t) ]  ≡⟨ subst-wk (wk1 A) ⟩
      wk1 A [ wk1 ∘→ sgSubst t ]             ≡⟨ wk1-tail A ⟩
      A [ wk1Subst idSubst ]                 ≡˘⟨ wk≡subst _ _ ⟩
      wk1 A                                  ∎
      where
      open Tools.Reasoning.PropositionalEquality

    [fstᵣ] :
      ∀ B → B [ fstᵣ p A t ]₀ PE.≡ B [ fstᵣ p (wk1 A) (var x0) ]↑ [ t ]₀
    [fstᵣ] {p = p} {A = A} {t = t} B =
      B [ fstᵣ p A t ]₀                                            ≡˘⟨ (flip substVar-to-subst B λ where
                                                                          x0     → fstᵣ-0[]
                                                                          (_ +1) → PE.refl) ⟩
      B [ sgSubst t ₛ•ₛ
          consSubst (wk1Subst idSubst) (fstᵣ p (wk1 A) (var x0)) ] ≡˘⟨ substCompEq B ⟩

      B [ fstᵣ p (wk1 A) (var x0) ]↑ [ t ]₀                        ∎
      where
      open Tools.Reasoning.PropositionalEquality

    ⊢≡[fstᵣ] :
      Γ ⊢ t ∷ Σᵣ p , q ▷ A ▹ B →
      Γ ⊢ B [ fstᵣ p (wk1 A) (var x0) ]↑ [ t ]₀ ≡ B [ fstᵣ p A t ]₀
    ⊢≡[fstᵣ] {Γ = Γ} {t = t} {p = p} {A = A} {B = B} ⊢t =              $⟨ substitution ⊢B (singleSubst (fstᵣⱼ ⊢t)) ⊢Γ ⟩
      Γ ⊢ B [ fstᵣ p A t ]₀                                            →⟨ refl ⟩
      (Γ ⊢ B [ fstᵣ p A t ]₀ ≡ B [ fstᵣ p A t ]₀)                      →⟨ PE.subst₂ (_ ⊢_≡_) ([fstᵣ] B) PE.refl ⟩
      (Γ ⊢ B [ fstᵣ p (wk1 A) (var x0) ]↑ [ t ]₀ ≡ B [ fstᵣ p A t ]₀)  □
      where
      ⊢Γ = wfTerm ⊢t
      ⊢B = inversion-ΠΣ (syntacticTerm ⊢t) .proj₂ .proj₁

    [fstᵣ-0]↑[1,0]↑² :
      ∀ B →
      B [ fstᵣ p (wk1 A) (var x0) ]↑ [ prodᵣ p (var x1) (var x0) ]↑²
        PE.≡
      B [ fstᵣ p (wk1 (wk1 A)) (prodᵣ p (var x1) (var x0)) ]↑²
    [fstᵣ-0]↑[1,0]↑² {p = p} {A = A} B =
      B [ fstᵣ p (wk1 A) (var x0) ]↑ [ prodᵣ p (var x1) (var x0) ]↑²  ≡⟨ substCompEq B ⟩

      B [ consSubst (wk1Subst (wk1Subst idSubst))
           (prodᵣ p (var x1) (var x0)) ₛ•ₛ
         consSubst (wk1Subst idSubst) (fstᵣ p (wk1 A) (var x0)) ]     ≡⟨ (flip substVar-to-subst B λ where
                                                                            x0     → PE.refl
                                                                            (_ +1) → PE.refl) ⟩
      B [ prodrec r′ p q′
            (wk1 (wk1 A) [ liftSubst $
              consSubst (wk1Subst (wk1Subst idSubst)) $
              prodᵣ p (var x1) (var x0) ])
            (prodᵣ p (var x1) (var x0))
            (var x1) ]↑²                                              ≡⟨ PE.cong (λ A → B [ prodrec _ _ _ A _ _ ]↑²) $
                                                                         PE.trans (wk1-tail (wk1 A)) $
                                                                         wk1-tail A ⟩
      B [ prodrec r′ p q′
            (A [ wk1Subst (wk1Subst (wk1Subst idSubst)) ])
            (prodᵣ p (var x1) (var x0))
            (var x1) ]↑²                                              ≡˘⟨ PE.cong (λ A → B [ prodrec _ _ _ A _ _ ]↑²) $
                                                                          PE.trans (PE.cong (_[ _ ]) $ substCompEq A) $
                                                                          substCompEq A ⟩
      B [ prodrec r′ p q′
            (_[ wk1Subst idSubst ] $
             _[ wk1Subst idSubst ] $
             A [ wk1Subst idSubst ])
            (prodᵣ p (var x1) (var x0))
            (var x1) ]↑²                                              ≡˘⟨ PE.cong (λ A → B [ prodrec _ _ _ A _ _ ]↑²) $
                                                                          PE.trans (wk≡subst _ _) $
                                                                          PE.trans (PE.cong (_[ _ ]) $ wk≡subst _ (wk1 A)) $
                                                                          PE.cong (_[ _ ]) $ PE.cong (_[ _ ]) $ wk≡subst _ A ⟩
      B [ fstᵣ p (wk1 (wk1 A)) (prodᵣ p (var x1) (var x0)) ]↑²        ∎
      where
      open Tools.Reasoning.PropositionalEquality

    ⊢≡[fstᵣ-0]↑[1,0]↑² :
      Γ ∙ A ⊢ B →
      Σᵣ-allowed p q →
      Γ ∙ A ∙ B ⊢
        wk1 B ≡
        B [ fstᵣ p (wk1 A) (var x0) ]↑ [ prodᵣ p (var x1) (var x0) ]↑²
    ⊢≡[fstᵣ-0]↑[1,0]↑² {Γ = Γ} {A = A} {B = B} {p = p} ⊢B ok =          $⟨ substRefl (⊢ˢwk1Subst-wk1Subst-idSubst ⊢B) , lemma ⟩
      Γ ∙ A ∙ B ⊢ˢ
        consSubst (wk1Subst (wk1Subst idSubst)) (var x1) ≡
        consSubst (wk1Subst (wk1Subst idSubst))
          (fstᵣ p (wk1 (wk1 A)) (prodᵣ p (var x1) (var x0))) ∷
        Γ ∙ A                                                           →⟨ flip (substitutionEq (refl ⊢B)) ⊢ΓAB ⟩

      Γ ∙ A ∙ B ⊢
        B [ var x1 ]↑² ≡
        B [ fstᵣ p (wk1 (wk1 A)) (prodᵣ p (var x1) (var x0)) ]↑²        →⟨ PE.subst₂ (_ ⊢_≡_) [1]↑² (PE.sym $ [fstᵣ-0]↑[1,0]↑² B) ⟩

      Γ ∙ A ∙ B ⊢
        wk1 B ≡
        B [ fstᵣ p (wk1 A) (var x0) ]↑ [ prodᵣ p (var x1) (var x0) ]↑²  □
      where
      ⊢ΓAB = wf ⊢B ∙ ⊢B

      lemma =                                                  $⟨ ⊢wk1 ⊢B ⊢B ⟩

        (Γ ∙ A ∙ B ⊢ wk1 B)                                    →⟨ refl ⟩

        Γ ∙ A ∙ B ⊢ wk1 B ≡ wk1 B                              →⟨ PE.subst₂ (_ ⊢_≡_) PE.refl (PE.sym (wk1-sgSubst (wk1 B) _)) ⟩

        Γ ∙ A ∙ B ⊢ wk1 B ≡ wk1 (wk1 B) [ var x1 ]₀            →⟨ conv (var ⊢ΓAB here) ⟩

        (Γ ∙ A ∙ B ⊢ var x0 ∷ wk1 (wk1 B) [ var x1 ]₀)         →⟨ (λ ⊢0 → ⊢wk1-wk1 (⊢wk1-wk1 ⊢B) , var ⊢ΓAB (there here) , ⊢0) ⟩

        (Γ ∙ A ∙ B ∙ wk1 (wk1 A) ⊢ wk1 (wk1 B)) ×
        (Γ ∙ A ∙ B ⊢ var x1 ∷ wk1 (wk1 A)) ×
        (Γ ∙ A ∙ B ⊢ var x0 ∷ wk1 (wk1 B) [ var x1 ]₀)         →⟨ (λ (⊢B , ⊢1 , ⊢0) → fstᵣ-β-≡ ⊢B ⊢1 ⊢0 ok) ⟩

        (Γ ∙ A ∙ B ⊢
           fstᵣ p (wk1 (wk1 A)) (prodᵣ p (var x1) (var x0)) ≡
           var x1 ∷
           wk1 (wk1 A))                                        →⟨ flip _⊢_≡_∷_.conv (⊢wk1-wk1≡ ⊢B) ∘→ _⊢_≡_∷_.sym ⟩

        (Γ ∙ A ∙ B ⊢
           var x1 ≡
           fstᵣ p (wk1 (wk1 A)) (prodᵣ p (var x1) (var x0)) ∷
           A [ wk1Subst (wk1Subst idSubst) ])                  □

    ⊢[fstᵣ-0]↑≡[fstᵣ-0]↑ :
      Γ ⊢ A₁ ≡ A₂ →
      Γ ∙ A₁ ⊢ B₁ ≡ B₂ →
      Σᵣ-allowed p q →
      Γ ∙ (Σᵣ p , q ▷ A₁ ▹ B₁) ⊢
        B₁ [ fstᵣ p (wk1 A₁) (var x0) ]↑ ≡
        B₂ [ fstᵣ p (wk1 A₂) (var x0) ]↑
    ⊢[fstᵣ-0]↑≡[fstᵣ-0]↑
      {Γ = Γ} {A₁ = A₁} {A₂ = A₂} {B₁ = B₁} {B₂ = B₂} {p = p} {q = q}
      A₁≡A₂ B₁≡B₂ ok =                                             $⟨ refl (var ⊢ΓΣA₁B₁ here) ⟩
      Γ ∙ (Σᵣ p , q ▷ A₁ ▹ B₁) ⊢
        var x0 ≡
        var x0 ∷
        wk1 (Σᵣ p , q ▷ A₁ ▹ B₁)                                   →⟨ fstᵣ-cong
                                                                        (wkEq (step id) ⊢ΓΣA₁B₁ A₁≡A₂)
                                                                        (W.wk (lift (step id)) (⊢ΓΣA₁B₁ ∙ ⊢wk1 ⊢ΣA₁B₁ ⊢A₁) ⊢B₁) ⟩
      Γ ∙ (Σᵣ p , q ▷ A₁ ▹ B₁) ⊢
        fstᵣ p (wk1 A₁) (var x0) ≡
        fstᵣ p (wk1 A₂) (var x0) ∷
        wk1 A₁                                                     →⟨ flip conv (⊢wk1≡ ⊢ΣA₁B₁ ⊢A₁) ⟩

      Γ ∙ (Σᵣ p , q ▷ A₁ ▹ B₁) ⊢
        fstᵣ p (wk1 A₁) (var x0) ≡
        fstᵣ p (wk1 A₂) (var x0) ∷
        A₁ [ wk1Subst idSubst ]                                    →⟨ substRefl (⊢ˢwk1Subst-idSubst ⊢ΣA₁B₁) ,_ ⟩

      Γ ∙ (Σᵣ p , q ▷ A₁ ▹ B₁) ⊢ˢ
        consSubst (wk1Subst idSubst) (fstᵣ p (wk1 A₁) (var x0)) ≡
        consSubst (wk1Subst idSubst) (fstᵣ p (wk1 A₂) (var x0)) ∷
        Γ ∙ A₁                                                     →⟨ flip (substitutionEq B₁≡B₂) ⊢ΓΣA₁B₁ ⟩

      Γ ∙ (Σᵣ p , q ▷ A₁ ▹ B₁) ⊢
        B₁ [ fstᵣ p (wk1 A₁) (var x0) ]↑ ≡
        B₂ [ fstᵣ p (wk1 A₂) (var x0) ]↑                           □
      where
      ⊢A₁     = syntacticEq A₁≡A₂ .proj₁
      ⊢B₁     = syntacticEq B₁≡B₂ .proj₁
      ⊢ΣA₁B₁  = ΠΣⱼ′ ⊢B₁ ok
      ⊢ΓΣA₁B₁ = wf ⊢A₁ ∙ ⊢ΣA₁B₁

    ⊢[fstᵣ-0]↑ :
      Γ ∙ A ⊢ B →
      Σᵣ-allowed p q →
      Γ ∙ (Σᵣ p , q ▷ A ▹ B) ⊢ B [ fstᵣ p (wk1 A) (var x0) ]↑
    ⊢[fstᵣ-0]↑ ⊢B ok =
      syntacticEq (⊢[fstᵣ-0]↑≡[fstᵣ-0]↑ (refl ⊢A) (refl ⊢B) ok) .proj₁
      where
      ⊢A = case wf ⊢B of λ where
             (_ ∙ ⊢A) → ⊢A

    ⊢0∷[fstᵣ-0]↑[1,0]↑² :
      Γ ∙ A ⊢ B →
      Σᵣ-allowed p q →
      Γ ∙ A ∙ B ⊢
        var x0 ∷
        B [ fstᵣ p (wk1 A) (var x0) ]↑ [ prodᵣ p (var x1) (var x0) ]↑²
    ⊢0∷[fstᵣ-0]↑[1,0]↑² {Γ = Γ} {A = A} {B = B} {p = p} ⊢B ok =
                                                                        $⟨ var (wf ⊢B ∙ ⊢B) here ⟩

      Γ ∙ A ∙ B ⊢ var x0 ∷ wk1 B                                        →⟨ flip conv (⊢≡[fstᵣ-0]↑[1,0]↑² ⊢B ok) ⟩

      Γ ∙ A ∙ B ⊢
        var x0 ∷
        B [ fstᵣ p (wk1 A) (var x0) ]↑ [ prodᵣ p (var x1) (var x0) ]↑²  □

  ----------------------------------------------------------------------
  -- Typing rules for sndᵣ

  -- A typing rule for sndᵣ.

  sndᵣⱼ :
    Γ ⊢ t ∷ Σᵣ p , q ▷ A ▹ B →
    Γ ⊢ sndᵣ p q A B t ∷ B [ fstᵣ p A t ]₀
  sndᵣⱼ {Γ = Γ} {t = t} {p = p} {q = q} {A = A} {B = B} ⊢t =    $⟨ prodrecⱼ ⊢A ⊢B (⊢[fstᵣ-0]↑ ⊢B ok) ⊢t
                                                                     (⊢0∷[fstᵣ-0]↑[1,0]↑² ⊢B ok) ok ⟩
    Γ ⊢ sndᵣ p q A B t ∷ B [ fstᵣ p (wk1 A) (var x0) ]↑ [ t ]₀  →⟨ flip conv (⊢≡[fstᵣ] ⊢t) ⟩
    Γ ⊢ sndᵣ p q A B t ∷ B [ fstᵣ p A t ]₀                      □
    where
    ⊢A,⊢B,ok = inversion-ΠΣ (syntacticTerm ⊢t)
    ⊢A       = ⊢A,⊢B,ok .proj₁
    ⊢B       = ⊢A,⊢B,ok .proj₂ .proj₁
    ok       = ⊢A,⊢B,ok .proj₂ .proj₂

  -- A reduction rule for sndᵣ.

  sndᵣ-β-⇒ :
    Γ ∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Σᵣ-allowed p q →
    Γ ⊢ sndᵣ p q A B (prodᵣ p t u) ⇒ u ∷ B [ fstᵣ p A (prodᵣ p t u) ]₀
  sndᵣ-β-⇒
    {Γ = Γ} {A = A} {B = B} {t = t} {u = u} {p = p} {q = q}
    ⊢B ⊢t ⊢u ok =                                      $⟨ prodrec-β (syntacticTerm ⊢t) ⊢B (⊢[fstᵣ-0]↑ {q = q} ⊢B ok)
                                                            ⊢t ⊢u (⊢0∷[fstᵣ-0]↑[1,0]↑² ⊢B ok) PE.refl ok ⟩
    Γ ⊢ sndᵣ p q A B (prodᵣ p t u) ⇒ u ∷
      B [ fstᵣ p (wk1 A) (var x0) ]↑ [ prodᵣ p t u ]₀  →⟨ flip conv (⊢≡[fstᵣ] (⊢prod ⊢B ⊢t ⊢u ok)) ⟩

    Γ ⊢ sndᵣ p q A B (prodᵣ p t u) ⇒ u ∷
      B [ fstᵣ p A (prodᵣ p t u) ]₀                    □

  -- Another reduction rule for sndᵣ.

  sndᵣ-subst :
    Γ ⊢ t₁ ⇒ t₂ ∷ Σᵣ p , q ▷ A ▹ B →
    Γ ⊢ sndᵣ p q A B t₁ ⇒ sndᵣ p q A B t₂ ∷ B [ fstᵣ p A t₁ ]₀
  sndᵣ-subst
    {Γ = Γ} {t₁ = t₁} {t₂ = t₂} {p = p} {q = q} {A = A} {B = B} t₁⇒t₂ =
                                              $⟨ prodrec-subst′ (⊢[fstᵣ-0]↑ ⊢B ok) (⊢0∷[fstᵣ-0]↑[1,0]↑² ⊢B ok) t₁⇒t₂ ok ⟩
    Γ ⊢ sndᵣ p q A B t₁ ⇒ sndᵣ p q A B t₂ ∷
      B [ fstᵣ p (wk1 A) (var x0) ]↑ [ t₁ ]₀  →⟨ flip conv (⊢≡[fstᵣ] ⊢t₁) ⟩

    Γ ⊢ sndᵣ p q A B t₁ ⇒ sndᵣ p q A B t₂ ∷
      B [ fstᵣ p A t₁ ]₀                      □
    where
    ⊢t₁   = syntacticEqTerm (subsetTerm t₁⇒t₂) .proj₂ .proj₁
    ⊢B,ok = inversion-ΠΣ (syntacticTerm ⊢t₁) .proj₂
    ⊢B    = ⊢B,ok .proj₁
    ok    = ⊢B,ok .proj₂

  -- An equality rule for sndᵣ.

  sndᵣ-β-≡ :
    Γ ∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Σᵣ-allowed p q →
    Γ ⊢ sndᵣ p q A B (prodᵣ p t u) ≡ u ∷ B [ fstᵣ p A (prodᵣ p t u) ]₀
  sndᵣ-β-≡ ⊢B ⊢t ⊢u ok = subsetTerm (sndᵣ-β-⇒ ⊢B ⊢t ⊢u ok)

  -- Another equality rule for sndᵣ.

  sndᵣ-cong :
    Γ ⊢ A₁ ≡ A₂ →
    Γ ∙ A₁ ⊢ B₁ ≡ B₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ Σᵣ p , q ▷ A₁ ▹ B₁ →
    Γ ⊢ sndᵣ p q A₁ B₁ t₁ ≡ sndᵣ p q A₂ B₂ t₂ ∷ B₁ [ fstᵣ p A₁ t₁ ]₀
  sndᵣ-cong
    {Γ = Γ} {A₁ = A₁} {A₂ = A₂} {B₁ = B₁} {B₂ = B₂} {t₁ = t₁} {t₂ = t₂}
    {p = p} {q = q} A₁≡A₂ B₁≡B₂ t₁≡t₂ =           $⟨ prodrec-cong′ (⊢[fstᵣ-0]↑≡[fstᵣ-0]↑ A₁≡A₂ B₁≡B₂ ok)
                                                       t₁≡t₂ (refl (⊢0∷[fstᵣ-0]↑[1,0]↑² ⊢B ok)) ⟩
    Γ ⊢ sndᵣ p q A₁ B₁ t₁ ≡ sndᵣ p q A₂ B₂ t₂ ∷
      B₁ [ fstᵣ p (wk1 A₁) (var x0) ]↑ [ t₁ ]₀    →⟨ flip conv (⊢≡[fstᵣ] ⊢t₁) ⟩

    Γ ⊢ sndᵣ p q A₁ B₁ t₁ ≡ sndᵣ p q A₂ B₂ t₂ ∷
      B₁ [ fstᵣ p A₁ t₁ ]₀                        □
    where
    ⊢t₁   = syntacticEqTerm t₁≡t₂ .proj₂ .proj₁
    ⊢B,ok = inversion-ΠΣ (syntacticTerm ⊢t₁) .proj₂
    ⊢B    = ⊢B,ok .proj₁
    ok    = ⊢B,ok .proj₂

  -- If Σᵣ-allowed p q holds for some p and q, then a certain η-rule
  -- for Σᵣ, fstᵣ and sndᵣ does not hold in general.

  ¬-Σᵣ-η-prodᵣ-fstᵣ-sndᵣ :
    ∀ {p q} →
    Σᵣ-allowed p q →
    ¬ (∀ {n} {Γ : Con Term n} {t A B} →
       Γ ⊢ t ∷ Σᵣ p , q ▷ A ▹ B →
       Γ ⊢ prodᵣ p (fstᵣ p A t) (sndᵣ p q A B t) ≡ t ∷ Σᵣ p , q ▷ A ▹ B)
  ¬-Σᵣ-η-prodᵣ-fstᵣ-sndᵣ {p = p} {q = q} Σ-ok hyp = ¬fst,snd≡ fst,snd≡
    where
    A′ = ℕ
    B′ = ℕ

    Γ′ = ε ∙ Σᵣ p , q ▷ ℕ ▹ ℕ

    t′ : Term 1
    t′ = var x0

    ⊢Γ : ⊢ Γ′
    ⊢Γ = ε ∙ ΠΣⱼ′ (ℕⱼ (ε ∙ ℕⱼ ε)) Σ-ok

    ⊢B : Γ′ ∙ A′ ⊢ B′
    ⊢B = ℕⱼ (⊢Γ ∙ ℕⱼ ⊢Γ)

    ⊢t : Γ′ ⊢ t′ ∷ Σᵣ p , q ▷ A′ ▹ B′
    ⊢t = var ⊢Γ here

    fst,snd≡ :
      Γ′ ⊢ prodᵣ p (fstᵣ p A′ t′) (sndᵣ p q A′ B′ t′) ≡ t′ ∷
        Σᵣ p , q ▷ A′ ▹ B′
    fst,snd≡ = hyp ⊢t

    ¬fst,snd≡ :
      ¬ Γ′ ⊢ prodᵣ p (fstᵣ p A′ t′) (sndᵣ p q A′ B′ t′) ≡ t′ ∷
          Σᵣ p , q ▷ A′ ▹ B′
    ¬fst,snd≡ = prodᵣ≢ne (var _)

  -- If Σᵣ-allowed p q holds for some p and q, then a certain η-rule
  -- for Σᵣ, fstᵣ and sndᵣ does not hold in general.

  ¬-Σᵣ-η :
    ∀ {p q} →
    Σᵣ-allowed p q →
    ¬ (∀ {n} {Γ : Con Term n} {t A B u} →
       Γ ⊢ t ∷ Σᵣ p , q ▷ A ▹ B →
       Γ ⊢ u ∷ Σᵣ p , q ▷ A ▹ B →
       Γ ⊢ fstᵣ p A t ≡ fstᵣ p A u ∷ A →
       Γ ⊢ sndᵣ p q A B t ≡ sndᵣ p q A B u ∷ B [ fstᵣ p A t ]₀ →
       Γ ⊢ t ≡ u ∷ Σᵣ p , q ▷ A ▹ B)
  ¬-Σᵣ-η Σ-ok hyp =
    ¬-Σᵣ-η-prodᵣ-fstᵣ-sndᵣ Σ-ok λ ⊢t →
      case inversion-ΠΣ (syntacticTerm ⊢t) of λ {
        (_ , ⊢B , ok) →
      hyp (⊢prod ⊢B (fstᵣⱼ ⊢t) (sndᵣⱼ ⊢t) ok) ⊢t
        (fstᵣ-β-≡ ⊢B (fstᵣⱼ ⊢t) (sndᵣⱼ ⊢t) ok)
        (sndᵣ-β-≡ ⊢B (fstᵣⱼ ⊢t) (sndᵣⱼ ⊢t) ok) }

------------------------------------------------------------------------
-- More derived rules

-- An "inverse" of prod-cong for Σᵣ.

prod-cong⁻¹-Σᵣ :
  Γ ⊢ prodᵣ p t u ≡ prodᵣ p v w ∷ Σᵣ p , q ▷ A ▹ B →
  (Γ ∙ A ⊢ B) × Γ ⊢ t ≡ v ∷ A × Γ ⊢ u ≡ w ∷ B [ t ]₀ ×
  Σᵣ-allowed p q
prod-cong⁻¹-Σᵣ
  {Γ = Γ} {p = p} {t = t} {u = u} {v = v} {w = w}
  {q = q} {A = A} {B = B} prod≡prod =
  ⊢B , t≡v , u≡w , ok
  where
  ⊢ΣAB = syntacticEqTerm prod≡prod .proj₁
  ⊢A   = inversion-ΠΣ ⊢ΣAB .proj₁
  ⊢B   = inversion-ΠΣ ⊢ΣAB .proj₂ .proj₁
  ok   = inversion-ΠΣ ⊢ΣAB .proj₂ .proj₂
  ⊢t,u = syntacticEqTerm prod≡prod .proj₂ .proj₁
  ⊢t   = inversion-prod-Σ ⊢t,u .proj₁
  ⊢u   = inversion-prod-Σ ⊢t,u .proj₂ .proj₁
  ⊢v,w = syntacticEqTerm prod≡prod .proj₂ .proj₂
  ⊢v   = inversion-prod-Σ ⊢v,w .proj₁
  ⊢w   = inversion-prod-Σ ⊢v,w .proj₂ .proj₁

  open Fstᵣ-sndᵣ p p

  fst-t,u≡t = fstᵣ-β-≡ ⊢B ⊢t ⊢u ok

  t≡v =                                                      $⟨ prod≡prod ⟩
    Γ ⊢ prodᵣ p t u ≡ prodᵣ p v w ∷ Σᵣ p , q ▷ A ▹ B         →⟨ fstᵣ-cong (refl ⊢A) ⊢B ⟩
    Γ ⊢ fstᵣ p A (prodᵣ p t u) ≡ fstᵣ p A (prodᵣ p v w) ∷ A  →⟨ (λ hyp → trans (sym fst-t,u≡t)
                                                                   (trans hyp (fstᵣ-β-≡ ⊢B ⊢v ⊢w ok))) ⟩
    Γ ⊢ t ≡ v ∷ A                                            □

  u≡w =                                                            $⟨ prod≡prod ⟩
    Γ ⊢ prodᵣ p t u ≡ prodᵣ p v w ∷ Σᵣ p , q ▷ A ▹ B               →⟨ sndᵣ-cong (refl ⊢A) (refl ⊢B) ⟩

    Γ ⊢ sndᵣ p q A B (prodᵣ p t u) ≡ sndᵣ p q A B (prodᵣ p v w) ∷
      B [ fstᵣ p A (prodᵣ p t u) ]₀                                →⟨ (λ hyp → trans
                                                                         (sym (sndᵣ-β-≡ ⊢B ⊢t ⊢u ok))
                                                                            (trans hyp
                                                                               (conv (sndᵣ-β-≡ ⊢B ⊢v ⊢w ok)
                                                                                  (substTypeEq (refl ⊢B)
                                                                                     (fstᵣ-cong (refl ⊢A) ⊢B (sym prod≡prod)))))) ⟩

    Γ ⊢ u ≡ w ∷ B [ fstᵣ p A (prodᵣ p t u) ]₀                      →⟨ flip _⊢_≡_∷_.conv (substTypeEq (refl ⊢B) fst-t,u≡t) ⟩

    Γ ⊢ u ≡ w ∷ B [ t ]₀                                           □

-- An "inverse" of prod-cong.

prod-cong⁻¹ :
  Γ ⊢ prod s p t u ≡ prod s p v w ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B →
  (Γ ∙ A ⊢ B) × Γ ⊢ t ≡ v ∷ A × Γ ⊢ u ≡ w ∷ B [ t ]₀ ×
  Σ-allowed s p q
prod-cong⁻¹ {s = Σₚ} = prod-cong⁻¹-Σₚ
prod-cong⁻¹ {s = Σᵣ} = prod-cong⁻¹-Σᵣ
