------------------------------------------------------------------------
-- Admissible rules related to Σ-types
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.Admissible.Sigma
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Consequences.Inequality R
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Substitution R
open import Definition.Typed.Syntactic R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Sigma 𝕄

open import Tools.Fin
open import Tools.Function
open import Tools.Product
open import Tools.Relation

private variable
  Γ             : Cons _ _
  A B C t u v w : Term _
  p q q′ r      : M
  s             : Strength

------------------------------------------------------------------------
-- Some admissible rules

opaque

  -- A variant of the reduction rule prodrec-β.

  prodrec-β-⇒₁ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    Γ »∙ (Σʷ p , q′ ▷ A ▹ B) ⊢ C →
    Γ ⊢ prodʷ p t u ∷ Σʷ p , q′ ▷ A ▹ B →
    Γ »∙ A »∙ B ⊢ v ∷ C [ prodʷ p (var x1) (var x0) ]↑² →
    Γ ⊢ prodrec r p q C (prodʷ p t u) v ⇒ v [ t , u ]₁₀ ∷
      C [ prodʷ p t u ]₀
  prodrec-β-⇒₁ ⊢C ⊢p ⊢v =
    case inversion-prod ⊢p of λ
      (F , G , q , _ , _ , ⊢t , ⊢u , Σ≡Σ′ , _) →
    case ΠΣ-injectivity Σ≡Σ′ of λ
      (A≡F , B≡G , _) →
    case conv ⊢t (sym A≡F) of λ
      ⊢t′ →
    prodrec-β-⇒ ⊢C ⊢t′ (conv ⊢u (sym (B≡G (refl ⊢t′)))) ⊢v

opaque

  -- A variant of the equality rule prodrec-β.

  prodrec-β-≡₁ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    Γ »∙ (Σʷ p , q′ ▷ A ▹ B) ⊢ C →
    Γ ⊢ prodʷ p t u ∷ Σʷ p , q′ ▷ A ▹ B →
    Γ »∙ A »∙ B ⊢ v ∷ C [ prodʷ p (var x1) (var x0) ]↑² →
    Γ ⊢ prodrec r p q C (prodʷ p t u) v ≡ v [ t , u ]₁₀ ∷
      C [ prodʷ p t u ]₀
  prodrec-β-≡₁ ⊢C ⊢p ⊢v =
    subsetTerm (prodrec-β-⇒₁ ⊢C ⊢p ⊢v)

-- An "inverse" of prod-cong for Σˢ.

prod-cong⁻¹-Σˢ :
  ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
  Γ ⊢ prodˢ p t u ≡ prodˢ p v w ∷ Σˢ p , q ▷ A ▹ B →
  (Γ »∙ A ⊢ B) × Γ ⊢ t ≡ v ∷ A × Γ ⊢ u ≡ w ∷ B [ t ]₀ ×
  Σˢ-allowed p q
prod-cong⁻¹-Σˢ {Γ} {p} {t} {u} {v} {w} {q} {A} {B} prod≡prod =
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
    Γ ⊢ prodˢ p t u ≡ prodˢ p v w ∷ Σˢ p , q ▷ A ▹ B   →⟨ fst-cong′ ⟩
    Γ ⊢ fst p (prodˢ p t u) ≡ fst p (prodˢ p v w) ∷ A  →⟨ (λ hyp → trans (sym′ fst-t,u≡t) (trans hyp (Σ-β₁-≡ ⊢B ⊢v ⊢w ok))) ⟩
    Γ ⊢ t ≡ v ∷ A                                      □

  u≡w =                                               $⟨ prod≡prod ⟩
    Γ ⊢ prodˢ p t u ≡ prodˢ p v w ∷ Σˢ p , q ▷ A ▹ B  →⟨ snd-cong′ ⟩

    Γ ⊢ snd p (prodˢ p t u) ≡ snd p (prodˢ p v w) ∷
      B [ fst p (prodˢ p t u) ]₀                      →⟨ (λ hyp → trans
                                                            (sym′ (Σ-β₂-≡ ⊢B ⊢t ⊢u ok))
                                                            (trans (conv hyp (subst-⊢≡₀ ⊢B (Σ-β₁-≡ ⊢B ⊢t ⊢u ok)))
                                                               (conv (Σ-β₂-≡ ⊢B ⊢v ⊢w ok) (subst-⊢≡₀ ⊢B (sym′ t≡v))))) ⟩

    Γ ⊢ u ≡ w ∷ B [ t ]₀                              □

-- An "inverse" of prod-cong for Σʷ.

prod-cong⁻¹-Σʷ :
  ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
  Γ ⊢ prodʷ p t u ≡ prodʷ p v w ∷ Σʷ p , q ▷ A ▹ B →
  (Γ »∙ A ⊢ B) × Γ ⊢ t ≡ v ∷ A × Γ ⊢ u ≡ w ∷ B [ t ]₀ ×
  Σʷ-allowed p q
prod-cong⁻¹-Σʷ {Γ} {p} {t} {u} {v} {w} {q} {A} {B} prod≡prod =
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

  fst-t,u≡t = fstʷ-β-≡ ⊢B ⊢t ⊢u ok

  t≡v =                                                      $⟨ prod≡prod ⟩
    Γ ⊢ prodʷ p t u ≡ prodʷ p v w ∷ Σʷ p , q ▷ A ▹ B         →⟨ fstʷ-cong (refl ⊢A) ⟩
    Γ ⊢ fstʷ p A (prodʷ p t u) ≡ fstʷ p A (prodʷ p v w) ∷ A  →⟨ (λ hyp → trans (sym′ fst-t,u≡t)
                                                                   (trans hyp (fstʷ-β-≡ ⊢B ⊢v ⊢w ok))) ⟩
    Γ ⊢ t ≡ v ∷ A                                            □

  u≡w =                                                            $⟨ prod≡prod ⟩
    Γ ⊢ prodʷ p t u ≡ prodʷ p v w ∷ Σʷ p , q ▷ A ▹ B               →⟨ sndʷ-cong (refl ⊢A) (refl ⊢B) ⟩

    Γ ⊢ sndʷ p q A B (prodʷ p t u) ≡ sndʷ p q A B (prodʷ p v w) ∷
      B [ fstʷ p A (prodʷ p t u) ]₀                                →⟨ (λ hyp → trans
                                                                         (sym′ (sndʷ-β-≡ ⊢B ⊢t ⊢u ok))
                                                                         (trans (conv hyp (subst-⊢≡₀ ⊢B (fstʷ-β-≡ ⊢B ⊢t ⊢u ok)))
                                                                            (conv (sndʷ-β-≡ ⊢B ⊢v ⊢w ok) (subst-⊢≡₀ ⊢B (sym′ t≡v))))) ⟩

    Γ ⊢ u ≡ w ∷ B [ t ]₀                                           □

-- An "inverse" of prod-cong.

prod-cong⁻¹ :
  ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
  Γ ⊢ prod s p t u ≡ prod s p v w ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B →
  (Γ »∙ A ⊢ B) × Γ ⊢ t ≡ v ∷ A × Γ ⊢ u ≡ w ∷ B [ t ]₀ ×
  Σ-allowed s p q
prod-cong⁻¹ {s = 𝕤} = prod-cong⁻¹-Σˢ
prod-cong⁻¹ {s = 𝕨} = prod-cong⁻¹-Σʷ

------------------------------------------------------------------------
-- Negative results related to η-rules for Σʷ

-- If Σʷ-allowed p q holds for some p and q, and equality reflection
-- is not allowed, then a certain definitional η-rule for Σʷ, fstʷ and
-- sndʷ does not hold in general.
--
-- See also
-- Definition.Typed.Properties.Admissible.Sigma.⊢Σʷ-η-prodʷ-fstʷ-sndʷ.

¬-Σʷ-η-prodʷ-fstʷ-sndʷ :
  ⦃ not-ok : No-equality-reflection ⦄ →
  Σʷ-allowed p q →
  ¬ (∀ {m n} {Γ : Cons m n} {t A B} →
     Γ ⊢ t ∷ Σʷ p , q ▷ A ▹ B →
     Γ ⊢ prodʷ p (fstʷ p A t) (sndʷ p q A B t) ≡ t ∷ Σʷ p , q ▷ A ▹ B)
¬-Σʷ-η-prodʷ-fstʷ-sndʷ {p = p} {q = q} Σ-ok hyp = ¬fst,snd≡ fst,snd≡
  where
  A′ = ℕ
  B′ = ℕ

  Γ′ = ε ∙ Σʷ p , q ▷ ℕ ▹ ℕ

  t′ : Term 1
  t′ = var x0

  ⊢Γ : ε »⊢ Γ′
  ⊢Γ = ∙ ΠΣⱼ (⊢ℕ (∙ ⊢ℕ εε)) Σ-ok

  ⊢B : ε » Γ′ ∙ A′ ⊢ B′
  ⊢B = ⊢ℕ (∙ ⊢ℕ ⊢Γ)

  ⊢t : ε » Γ′ ⊢ t′ ∷ Σʷ p , q ▷ A′ ▹ B′
  ⊢t = var ⊢Γ here

  fst,snd≡ :
    ε » Γ′ ⊢ prodʷ p (fstʷ p A′ t′) (sndʷ p q A′ B′ t′) ≡ t′ ∷
      Σʷ p , q ▷ A′ ▹ B′
  fst,snd≡ = hyp ⊢t

  ¬fst,snd≡ :
    ¬ ε » Γ′ ⊢ prodʷ p (fstʷ p A′ t′) (sndʷ p q A′ B′ t′) ≡ t′ ∷
        Σʷ p , q ▷ A′ ▹ B′
  ¬fst,snd≡ = prodʷ≢ne ⦃ ok = included ⦄ _ (var⁺ _)

-- If Σʷ-allowed p q holds for some p and q, and equality reflection
-- is not allowed, then a certain definitional η-rule for Σʷ, fstʷ and
-- sndʷ does not hold in general.

¬-Σʷ-η :
  ⦃ not-ok : No-equality-reflection ⦄ →
  Σʷ-allowed p q →
  ¬ (∀ {m n} {Γ : Cons m n} {t A B u} →
     Γ ⊢ t ∷ Σʷ p , q ▷ A ▹ B →
     Γ ⊢ u ∷ Σʷ p , q ▷ A ▹ B →
     Γ ⊢ fstʷ p A t ≡ fstʷ p A u ∷ A →
     Γ ⊢ sndʷ p q A B t ≡ sndʷ p q A B u ∷ B [ fstʷ p A t ]₀ →
     Γ ⊢ t ≡ u ∷ Σʷ p , q ▷ A ▹ B)
¬-Σʷ-η Σ-ok hyp =
  ¬-Σʷ-η-prodʷ-fstʷ-sndʷ Σ-ok λ ⊢t →
    let _ , ⊢B , ok = inversion-ΠΣ (syntacticTerm ⊢t)
        lemma       = fstʷ-β-≡ ⊢B (fstʷⱼ ⊢t) (sndʷⱼ ⊢t) ok
    in
    hyp (prodⱼ ⊢B (fstʷⱼ ⊢t) (sndʷⱼ ⊢t) ok) ⊢t lemma
      (conv (sndʷ-β-≡ ⊢B (fstʷⱼ ⊢t) (sndʷⱼ ⊢t) ok)
         (subst-⊢≡₀ ⊢B (sym′ lemma)))
