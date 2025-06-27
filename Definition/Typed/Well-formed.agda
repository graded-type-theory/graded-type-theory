------------------------------------------------------------------------
-- Well-formedness lemmas
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Well-formed
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Inversion.Primitive R
import Definition.Typed.Properties.Admissible.Erased.Primitive R
  as Erased
open import Definition.Typed.Properties.Admissible.Var R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Stability.Primitive R
open import Definition.Typed.Substitution.Primitive.Primitive R
open import Definition.Typed.Weakening R

open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Tools.Fin
open import Tools.Function
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Sum using (inj₂)

private variable
  x             : Fin _
  Γ Δ           : Con Term _
  A B t t₁ t₂ u : Term _
  σ₁ σ₂         : Subst _ _

------------------------------------------------------------------------
-- Well-formedness lemmas

opaque

  -- A well-formedness lemma for _∷_∈_.

  wf-∷∈ : x ∷ A ∈ Γ → ⊢ Γ → Γ ⊢ A
  wf-∷∈ here       (∙ ⊢A) = wk₁ ⊢A ⊢A
  wf-∷∈ (there x∈) (∙ ⊢B) = wk₁ ⊢B (wf-∷∈ x∈ (wf ⊢B))

opaque mutual

  -- A well-formedness lemma for _⊢_∷_.

  wf-⊢∷ : Γ ⊢ t ∷ A → Γ ⊢ A
  wf-⊢∷ = λ where
    (conv _ B≡A) →
      let _ , ⊢A = wf-⊢≡ B≡A in
      ⊢A
    (var ⊢Γ x∈) →
      wf-∷∈ x∈ ⊢Γ
    (Levelⱼ ⊢Γ) →
      Uⱼ (zeroᵘⱼ ⊢Γ)
    (zeroᵘⱼ ⊢Γ) →
      Levelⱼ ⊢Γ
    (sucᵘⱼ ⊢l) →
      wf-⊢∷ ⊢l
    (maxᵘⱼ ⊢l ⊢u) →
      wf-⊢∷ ⊢l
    (Uⱼ ⊢l) →
      Uⱼ (sucᵘⱼ ⊢l)
    (Liftⱼ x x₁ x₂) →
      Uⱼ (maxᵘⱼ x x₁)
    (liftⱼ x x₁ x₂) →
      Liftⱼ x x₁
    (lowerⱼ x) →
      let ⊢l₂ , ⊢A = inversion-Lift (wf-⊢∷ x)
      in ⊢A
    (ΠΣⱼ ⊢l ⊢A _ _) →
      Uⱼ ⊢l
    (lamⱼ ⊢B _ ok) →
      ΠΣⱼ ⊢B ok
    (⊢t ∘ⱼ ⊢u) →
      let _ , ⊢B , _ = inversion-ΠΣ (wf-⊢∷ ⊢t) in
      subst-⊢ ⊢B (⊢ˢʷ∷-sgSubst ⊢u)
    (prodⱼ ⊢B _ _ ok) →
      ΠΣⱼ ⊢B ok
    (fstⱼ ⊢B _) →
      ⊢∙→⊢ (wf ⊢B)
    (sndⱼ ⊢B ⊢t) →
      subst-⊢ ⊢B (⊢ˢʷ∷-sgSubst (fstⱼ ⊢B ⊢t))
    (prodrecⱼ ⊢C ⊢t _ _) →
      subst-⊢ ⊢C (⊢ˢʷ∷-sgSubst ⊢t)
    (Emptyⱼ ⊢Γ) →
      Uⱼ (zeroᵘⱼ ⊢Γ)
    (emptyrecⱼ ⊢A _) →
      ⊢A
    (starⱼ ⊢Γ ok) →
      Unitⱼ ⊢Γ ok
    (unitrecⱼ ⊢l ⊢A ⊢t _ _) →
      subst-⊢ ⊢A (⊢ˢʷ∷-sgSubst ⊢t)
    (Unitⱼ ⊢Γ _) →
      Uⱼ ⊢Γ
    (ℕⱼ ⊢Γ) →
      Uⱼ (zeroᵘⱼ ⊢Γ)
    (zeroⱼ ⊢Γ) →
      ℕⱼ ⊢Γ
    (sucⱼ ⊢t) →
      ℕⱼ (wfTerm ⊢t)
    (natrecⱼ _ ⊢u ⊢v) →
      subst-⊢ (⊢∙→⊢ (wfTerm ⊢u)) (⊢ˢʷ∷-sgSubst ⊢v)
    (Idⱼ ⊢A _ _) →
      Uⱼ (inversion-U-Level (wf-⊢∷ ⊢A))
    (rflⱼ ⊢t) →
      Idⱼ (wf-⊢∷ ⊢t) ⊢t ⊢t
    (Jⱼ _ ⊢B _ ⊢v ⊢w) →
      subst-⊢ ⊢B $
      →⊢ˢʷ∷∙ (⊢ˢʷ∷-sgSubst ⊢v) $
      PE.subst (_⊢_∷_ _ _)
        (PE.sym $
         PE.cong₃ Id (wk1-sgSubst _ _) (wk1-sgSubst _ _) PE.refl)
        ⊢w
    (Kⱼ ⊢B _ ⊢v _) →
      subst-⊢ ⊢B (⊢ˢʷ∷-sgSubst ⊢v)
    ([]-congⱼ ⊢A ⊢t ⊢u _ ok) →
      let open Erased ([]-cong→Erased ok) in
      Idⱼ (Erasedⱼ ⊢A) ([]ⱼ ⊢A ⊢t) ([]ⱼ ⊢A ⊢u)

  -- A well-formedness lemma for _⊢_≡_.

  wf-⊢≡ : Γ ⊢ A ≡ B → Γ ⊢ A × Γ ⊢ B
  wf-⊢≡ = λ where
    (refl ⊢A) →
      ⊢A , ⊢A
    (sym B≡A) →
      let ⊢B , ⊢A = wf-⊢≡ B≡A in
      ⊢A , ⊢B
    (trans A≡B B≡C) →
      let ⊢A , _  = wf-⊢≡ A≡B
          _  , ⊢C = wf-⊢≡ B≡C
      in
      ⊢A , ⊢C
    (univ A≡B) →
      let _ , ⊢A , ⊢B = wf-⊢≡∷ A≡B in
      univ ⊢A , univ ⊢B
    (U-cong l₁≡l₂) →
      let _ , ⊢l₁ , ⊢l₂ = wf-⊢≡∷ l₁≡l₂ in
      Uⱼ ⊢l₁ , Uⱼ ⊢l₂
    (Lift-cong l₁≡l₂ A≡B) →
      let _ , ⊢l₁ , ⊢l₂ = wf-⊢≡∷ l₁≡l₂
          ⊢A , ⊢B = wf-⊢≡ A≡B
      in Liftⱼ ⊢l₁ ⊢A , Liftⱼ ⊢l₂ ⊢B
    (ΠΣ-cong A₁≡B₁ A₂≡B₂ ok) →
      let _ , ⊢B₁   = wf-⊢≡ A₁≡B₁
          ⊢A₂ , ⊢B₂ = wf-⊢≡ A₂≡B₂
      in
      ΠΣⱼ ⊢A₂ ok ,
      ΠΣⱼ (stability-⊢ refl-∙⟨ ⊢B₁ ∣ A₁≡B₁ ⟩ ⊢B₂) ok
    (Unit-cong l₁≡l₂ ok) →
      let _ , ⊢l₁ , ⊢l₂ = wf-⊢≡∷ l₁≡l₂ in
      Unitⱼ ⊢l₁ ok , Unitⱼ ⊢l₂ ok
    (Id-cong A≡B t₁≡u₁ t₂≡u₂) →
      let ⊢A , ⊢B       = wf-⊢≡ A≡B
          _ , ⊢t₁ , ⊢u₁ = wf-⊢≡∷ t₁≡u₁
          _ , ⊢t₂ , ⊢u₂ = wf-⊢≡∷ t₂≡u₂
      in
      Idⱼ ⊢A ⊢t₁ ⊢t₂ , Idⱼ ⊢B (conv ⊢u₁ A≡B) (conv ⊢u₂ A≡B)

  -- A well-formedness lemma for _⊢_≡_∷_.

  wf-⊢≡∷ : Γ ⊢ t ≡ u ∷ A → (Γ ⊢ A) × Γ ⊢ t ∷ A × Γ ⊢ u ∷ A
  wf-⊢≡∷ = λ where
    (refl ⊢t) →
      wf-⊢∷ ⊢t , ⊢t , ⊢t
    (sym _ t₂≡t₁) →
      let ⊢A , ⊢t₂ , ⊢t₁ = wf-⊢≡∷ t₂≡t₁ in
      ⊢A , ⊢t₁ , ⊢t₂
    (trans t₁≡t₂ t₂≡t₃) →
      let ⊢A , ⊢t₁ , _ = wf-⊢≡∷ t₁≡t₂
          _ , _ , ⊢t₃  = wf-⊢≡∷ t₂≡t₃
      in
      ⊢A , ⊢t₁ , ⊢t₃
    (conv t₁≡t₂ B≡A) →
      let _ , ⊢t₁ , ⊢t₂ = wf-⊢≡∷ t₁≡t₂
          _ , ⊢A        = wf-⊢≡ B≡A
      in
      ⊢A , conv ⊢t₁ B≡A , conv ⊢t₂ B≡A
    (sucᵘ-cong l₁≡l₂) →
      let ⊢Level , ⊢l₁ , ⊢l₂ = wf-⊢≡∷ l₁≡l₂ in
      ⊢Level , sucᵘⱼ ⊢l₁ , sucᵘⱼ ⊢l₂
    (maxᵘ-cong t₁≡t₂ u₁≡u₂) →
      let ⊢Level , ⊢t₁ , ⊢t₂ = wf-⊢≡∷ t₁≡t₂
          _ , ⊢u₁ , ⊢u₂ = wf-⊢≡∷ u₁≡u₂
      in
      ⊢Level , maxᵘⱼ ⊢t₁ ⊢u₁ , maxᵘⱼ ⊢t₂ ⊢u₂
    (maxᵘ-zeroˡ ⊢l) →
      wf-⊢∷ ⊢l , maxᵘⱼ (zeroᵘⱼ (wfTerm ⊢l)) ⊢l , ⊢l
    (maxᵘ-zeroʳ ⊢l) →
      wf-⊢∷ ⊢l , maxᵘⱼ ⊢l (zeroᵘⱼ (wfTerm ⊢l)) , ⊢l
    (maxᵘ-sucᵘ ⊢l₁ ⊢l₂) →
      wf-⊢∷ ⊢l₁ , maxᵘⱼ (sucᵘⱼ ⊢l₁) (sucᵘⱼ ⊢l₂) , sucᵘⱼ (maxᵘⱼ ⊢l₁ ⊢l₂)
    (maxᵘ-assoc ⊢l₁ ⊢l₂ ⊢l₃) →
      wf-⊢∷ ⊢l₁ , maxᵘⱼ (maxᵘⱼ ⊢l₁ ⊢l₂) ⊢l₃ , maxᵘⱼ ⊢l₁ (maxᵘⱼ ⊢l₂ ⊢l₃)
    (maxᵘ-comm ⊢l₁ ⊢l₂) →
      wf-⊢∷ ⊢l₁ , maxᵘⱼ ⊢l₁ ⊢l₂ , maxᵘⱼ ⊢l₂ ⊢l₁
    (maxᵘ-idem ⊢l) →
      wf-⊢∷ ⊢l , maxᵘⱼ ⊢l ⊢l , ⊢l
    (maxᵘ-sub ⊢l) →
      wf-⊢∷ ⊢l , maxᵘⱼ ⊢l (sucᵘⱼ ⊢l) , (sucᵘⱼ ⊢l)
    (U-cong l₁≡l₂) →
      let ⊢Level , ⊢l₁ , ⊢l₂ = wf-⊢≡∷ l₁≡l₂ in
      Uⱼ (sucᵘⱼ ⊢l₁) , Uⱼ ⊢l₁ , conv (Uⱼ ⊢l₂) (sym (U-cong (sucᵘ-cong l₁≡l₂)))
    (Lift-cong x x₁ x₂) →
      let ⊢Level , ⊢l₂ , ⊢l₂′ = wf-⊢≡∷ x₁
          _ , ⊢A , ⊢B = wf-⊢≡∷ x₂
      in
      Uⱼ (maxᵘⱼ x ⊢l₂) ,
      Liftⱼ x ⊢l₂ ⊢A ,
      conv (Liftⱼ x ⊢l₂′ ⊢B) (U-cong (maxᵘ-cong (refl x) (sym ⊢Level x₁)))
    (lower-cong x) →
      let ⊢Lift , ⊢t , ⊢u = wf-⊢≡∷ x
          ⊢l₂ , ⊢A = inversion-Lift ⊢Lift
      in ⊢A , lowerⱼ ⊢t , lowerⱼ ⊢u
    (Lift-β x₁ x₂) →
      wf-⊢∷ x₂ , lowerⱼ (liftⱼ (zeroᵘⱼ (wf x₁)) x₁ x₂) , x₂
    (Lift-η x x₁ ⊢t ⊢u x₂) →
      Liftⱼ x x₁ , ⊢t , ⊢u
    (ΠΣ-cong ⊢l A₁≡A₂ B₁≡B₂ ok) →
      let _ , ⊢A₁ , ⊢A₂ = wf-⊢≡∷ A₁≡A₂
          _ , ⊢B₁ , ⊢B₂ = wf-⊢≡∷ B₁≡B₂
      in
      Uⱼ ⊢l ,
      ΠΣⱼ ⊢l ⊢A₁ ⊢B₁ ok ,
      ΠΣⱼ ⊢l ⊢A₂ (stability-⊢∷ refl-∙⟨ univ ⊢A₂ ∣ univ A₁≡A₂ ⟩ ⊢B₂) ok
    (app-cong t₁≡t₂ u₁≡u₂) →
      let ⊢Π , ⊢t₁ , ⊢t₂ = wf-⊢≡∷ t₁≡t₂
          _ , ⊢u₁ , ⊢u₂  = wf-⊢≡∷ u₁≡u₂
          _ , ⊢B , _     = inversion-ΠΣ ⊢Π
      in
      subst-⊢ ⊢B (⊢ˢʷ∷-sgSubst ⊢u₁) ,
      ⊢t₁ ∘ⱼ ⊢u₁ ,
      conv (⊢t₂ ∘ⱼ ⊢u₂)
        (sym (subst-⊢≡ (refl ⊢B) (⊢ˢʷ≡∷-sgSubst ⊢u₁ ⊢u₂ u₁≡u₂)))
    (β-red ⊢B ⊢t ⊢u PE.refl ok) →
      let ⊢[u]₀ = ⊢ˢʷ∷-sgSubst ⊢u in
      subst-⊢ ⊢B ⊢[u]₀ ,
      lamⱼ ⊢B ⊢t ok ∘ⱼ ⊢u ,
      subst-⊢∷ ⊢t ⊢[u]₀
    (η-eq ⊢B ⊢t₁ ⊢t₂ _ ok) →
      ΠΣⱼ ⊢B ok , ⊢t₁ , ⊢t₂
    (fst-cong ⊢B t₁≡t₂) →
      let _ , ⊢t₁ , ⊢t₂ = wf-⊢≡∷ t₁≡t₂ in
      ⊢∙→⊢ (wf ⊢B) , fstⱼ ⊢B ⊢t₁ , fstⱼ ⊢B ⊢t₂
    (snd-cong ⊢B t₁≡t₂) →
      let _ , ⊢t₁ , ⊢t₂   = wf-⊢≡∷ t₁≡t₂
          [fst]₀≡[fst]₀   = ⊢ˢʷ≡∷-sgSubst (fstⱼ ⊢B ⊢t₁) (fstⱼ ⊢B ⊢t₂)
                              (fst-cong ⊢B t₁≡t₂)
          _ , ⊢[fst]₀ , _ = wf-⊢ˢʷ≡∷ [fst]₀≡[fst]₀
      in
      subst-⊢ ⊢B ⊢[fst]₀ ,
      sndⱼ ⊢B ⊢t₁ ,
      conv (sndⱼ ⊢B ⊢t₂) (sym (subst-⊢≡ (refl ⊢B) [fst]₀≡[fst]₀))
    (Σ-β₁ ⊢B ⊢t₁ ⊢t₂ PE.refl ok) →
      wf-⊢∷ ⊢t₁ , fstⱼ ⊢B (prodⱼ ⊢B ⊢t₁ ⊢t₂ ok) , ⊢t₁
    (Σ-β₂ ⊢B ⊢t₁ ⊢t₂ PE.refl ok) →
      let ⊢prod                = prodⱼ ⊢B ⊢t₁ ⊢t₂ ok
          [t]₀≡[fst[t,u]]₀     = ⊢ˢʷ≡∷-sgSubst ⊢t₁ (fstⱼ ⊢B ⊢prod)
                                   (_⊢_≡_∷_.sym (⊢∙→⊢ (wf ⊢B)) $
                                    Σ-β₁ ⊢B ⊢t₁ ⊢t₂ PE.refl ok)
          _ , _ , ⊢[fst[t,u]]₀ = wf-⊢ˢʷ≡∷ [t]₀≡[fst[t,u]]₀
      in
      subst-⊢ ⊢B ⊢[fst[t,u]]₀ ,
      sndⱼ ⊢B ⊢prod ,
      conv ⊢t₂ (subst-⊢≡ (refl ⊢B) [t]₀≡[fst[t,u]]₀)
    (Σ-η ⊢B ⊢t₁ ⊢t₂ _ _ ok) →
      ΠΣⱼ ⊢B ok , ⊢t₁ , ⊢t₂
    (prod-cong ⊢B t₁≡t₂ u₁≡u₂ ok) →
      let _ , ⊢t₁ , ⊢t₂ = wf-⊢≡∷ t₁≡t₂
          _ , ⊢u₁ , ⊢u₂ = wf-⊢≡∷ u₁≡u₂
      in
      ΠΣⱼ ⊢B ok ,
      prodⱼ ⊢B ⊢t₁ ⊢u₁ ok ,
      prodⱼ ⊢B ⊢t₂
        (conv ⊢u₂ (subst-⊢≡ (refl ⊢B) (⊢ˢʷ≡∷-sgSubst ⊢t₁ ⊢t₂ t₁≡t₂)))
        ok
    (prodrec-cong {G = B} C₁≡C₂ t₁≡t₂ u₁≡u₂ ok) →
      let ⊢C₁ , ⊢C₂     = wf-⊢≡ C₁≡C₂
          _ , ⊢t₁ , ⊢t₂ = wf-⊢≡∷ t₁≡t₂
          _ , ⊢u₁ , ⊢u₂ = wf-⊢≡∷ u₁≡u₂
          ⊢B            = ⊢∙→⊢ (wfEqTerm u₁≡u₂)
          ⊢A            = ⊢∙→⊢ (wf ⊢B)
          ⊢wk2-id       = ⊢ˢʷ∷-wk1Subst ⊢B $
                          ⊢ˢʷ∷-wk1Subst ⊢A $
                          ⊢ˢʷ∷-idSubst (wf ⊢A)
      in
      subst-⊢ ⊢C₁ (⊢ˢʷ∷-sgSubst ⊢t₁) ,
      prodrecⱼ ⊢C₁ ⊢t₁ ⊢u₁ ok ,
      conv
        (prodrecⱼ ⊢C₂ ⊢t₂
           (conv ⊢u₂ $
            subst-⊢≡ C₁≡C₂ $
            refl-⊢ˢʷ≡∷ $
            →⊢ˢʷ∷∙ ⊢wk2-id $
            prodⱼ
              (subst-⊢ ⊢B (⊢ˢʷ∷-⇑ (subst-⊢ ⊢A ⊢wk2-id) ⊢wk2-id))
              (PE.subst (_⊢_∷_ _ _) (wk[]≡[] 2) (var₁ ⊢B))
              (PE.subst (_⊢_∷_ _ _)
                 (PE.trans (PE.sym [1]↑²) $
                  PE.sym $ singleSubstComp _ _ B) $
               var₀ ⊢B)
              ok)
           ok)
        (sym (subst-⊢≡ C₁≡C₂ (⊢ˢʷ≡∷-sgSubst ⊢t₁ ⊢t₂ t₁≡t₂)))
    (prodrec-β {A = C} ⊢C ⊢t ⊢u ⊢v PE.refl ok) →
      subst-⊢ ⊢C (⊢ˢʷ∷-sgSubst (prodⱼ (⊢∙→⊢ (wfTerm ⊢v)) ⊢t ⊢u ok)) ,
      prodrecⱼ ⊢C (prodⱼ (⊢∙→⊢ (wfTerm ⊢v)) ⊢t ⊢u ok) ⊢v ok ,
      PE.subst (_⊢_∷_ _ _) ([1,0]↑²[,] C)
        (subst-⊢∷ ⊢v (→⊢ˢʷ∷∙ (⊢ˢʷ∷-sgSubst ⊢t) ⊢u))
    (emptyrec-cong A₁≡A₂ t₁≡t₂) →
      let ⊢A₁ , ⊢A₂     = wf-⊢≡ A₁≡A₂
          _ , ⊢t₁ , ⊢t₂ = wf-⊢≡∷ t₁≡t₂
      in
      ⊢A₁ , emptyrecⱼ ⊢A₁ ⊢t₁ , conv (emptyrecⱼ ⊢A₂ ⊢t₂) (sym A₁≡A₂)
    (Unit-cong l₁≡l₂ ok) →
      let ⊢Level , ⊢l₁ , ⊢l₂ = wf-⊢≡∷ l₁≡l₂ in
      Uⱼ ⊢l₁ , Unitⱼ ⊢l₁ ok , conv (Unitⱼ ⊢l₂ ok) (sym (U-cong l₁≡l₂))
    (star-cong l₁≡l₂ ok) →
      let ⊢Level , ⊢l₁ , ⊢l₂ = wf-⊢≡∷ l₁≡l₂ in
      Unitⱼ ⊢l₁ ok , starⱼ ⊢l₁ ok , conv (starⱼ ⊢l₂ ok) (sym (Unit-cong l₁≡l₂ ok))
    (unitrec-cong ⊢l₁ ⊢l₂ l₁≡l₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ ok _) →
      let ⊢A₁ , ⊢A₂     = wf-⊢≡ A₁≡A₂
          _ , ⊢t₁ , ⊢t₂ = wf-⊢≡∷ t₁≡t₂
          _ , ⊢u₁ , ⊢u₂ = wf-⊢≡∷ u₁≡u₂
          ⊢Γ            = wfTerm ⊢l₁
          Unit≡         = Unit-cong l₁≡l₂ ok
      in
      subst-⊢ ⊢A₁ (⊢ˢʷ∷-sgSubst ⊢t₁) ,
      unitrecⱼ ⊢l₁ ⊢A₁ ⊢t₁ ⊢u₁ ok ,
      conv
        (unitrecⱼ ⊢l₂
          (stability-⊢ (reflConEq ⊢Γ ∙⟨ Unitⱼ ⊢l₂ ok ∣ Unit≡ ⟩) ⊢A₂)
          (conv ⊢t₂ Unit≡)
          (conv ⊢u₂ $ subst-⊢≡ A₁≡A₂ $ ⊢ˢʷ≡∷-sgSubst
            (starⱼ ⊢l₁ ok)
            (conv (starⱼ ⊢l₂ ok) (sym Unit≡))
            (star-cong l₁≡l₂ ok))
          ok)
        (sym (subst-⊢≡ A₁≡A₂ (⊢ˢʷ≡∷-sgSubst ⊢t₁ ⊢t₂ t₁≡t₂)))
    (unitrec-β ⊢l ⊢A ⊢t ok _) →
      wf-⊢∷ ⊢t , unitrecⱼ ⊢l ⊢A (starⱼ ⊢l ok) ⊢t ok , ⊢t
    (unitrec-β-η ⊢l ⊢A ⊢t ⊢u ok η) →
      let ⊢star = starⱼ ⊢l ok in
      subst-⊢ ⊢A (⊢ˢʷ∷-sgSubst ⊢t) ,
      unitrecⱼ ⊢l ⊢A ⊢t ⊢u ok ,
      conv ⊢u
        (subst-⊢≡ (refl ⊢A) $
         ⊢ˢʷ≡∷-sgSubst ⊢star ⊢t (η-unit ⊢l ⊢star ⊢t ok (inj₂ η)))
    (η-unit ⊢l ⊢t₁ ⊢t₂ ok _) →
      wf-⊢∷ ⊢t₁ , ⊢t₁ , ⊢t₂
    (suc-cong t₁≡t₂) →
      let ⊢ℕ , ⊢t₁ , ⊢t₂ = wf-⊢≡∷ t₁≡t₂ in
      ⊢ℕ , sucⱼ ⊢t₁ , sucⱼ ⊢t₂
    (natrec-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂) →
      let ⊢A₁ , ⊢A₂     = wf-⊢≡ A₁≡A₂
          _ , ⊢t₁ , ⊢t₂ = wf-⊢≡∷ t₁≡t₂
          _ , ⊢u₁ , ⊢u₂ = wf-⊢≡∷ u₁≡u₂
          _ , ⊢v₁ , ⊢v₂ = wf-⊢≡∷ v₁≡v₂
          ⊢Γ            = wfTerm ⊢t₁
      in
      subst-⊢ ⊢A₁ (⊢ˢʷ∷-sgSubst ⊢v₁) ,
      natrecⱼ ⊢t₁ ⊢u₁ ⊢v₁ ,
      conv
        (natrecⱼ
           (conv ⊢t₂ $
            subst-⊢≡ A₁≡A₂ (refl-⊢ˢʷ≡∷ (⊢ˢʷ∷-sgSubst (zeroⱼ ⊢Γ))))
           (stability-⊢∷ refl-∙⟨ ⊢A₂ ∣ A₁≡A₂ ⟩ $
            conv ⊢u₂ $ subst-⊢≡ A₁≡A₂ $ refl-⊢ˢʷ≡∷ $
            →⊢ˢʷ∷∙
              (⊢ˢʷ∷-wk1Subst ⊢A₁ $
               ⊢ˢʷ∷-wk1Subst (ℕⱼ ⊢Γ) (⊢ˢʷ∷-idSubst ⊢Γ))
              (sucⱼ (var₁ ⊢A₁)))
           ⊢v₂)
        (sym $ subst-⊢≡ A₁≡A₂ (⊢ˢʷ≡∷-sgSubst ⊢v₁ ⊢v₂ v₁≡v₂))
    (natrec-zero ⊢t ⊢u) →
      wf-⊢∷ ⊢t , natrecⱼ ⊢t ⊢u (zeroⱼ (wfTerm ⊢t)) , ⊢t
    (natrec-suc {A} ⊢t ⊢u ⊢v) →
      subst-⊢ (⊢∙→⊢ (wfTerm ⊢u)) (⊢ˢʷ∷-sgSubst (sucⱼ ⊢v)) ,
      natrecⱼ ⊢t ⊢u (sucⱼ ⊢v) ,
      PE.subst (_⊢_∷_ _ _) (PE.sym $ substComp↑² A _)
        (subst-⊢∷ ⊢u (→⊢ˢʷ∷∙ (⊢ˢʷ∷-sgSubst ⊢v) (natrecⱼ ⊢t ⊢u ⊢v)))
    (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) →
      let ⊢U , ⊢A₁ , ⊢A₂ = wf-⊢≡∷ A₁≡A₂
          _ , ⊢t₁ , ⊢t₂  = wf-⊢≡∷ t₁≡t₂
          _ , ⊢u₁ , ⊢u₂  = wf-⊢≡∷ u₁≡u₂
          A₁≡A₂          = univ A₁≡A₂
      in
      ⊢U ,
      Idⱼ ⊢A₁ ⊢t₁ ⊢u₁ ,
      Idⱼ ⊢A₂ (conv ⊢t₂ A₁≡A₂) (conv ⊢u₂ A₁≡A₂)
    (J-cong A₁≡A₂ ⊢t₁ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁≡w₂) →
      let ⊢A₁ , ⊢A₂        = wf-⊢≡ A₁≡A₂
          _ , _ , ⊢t₂      = wf-⊢≡∷ t₁≡t₂
          ⊢t₂′             = conv ⊢t₂ A₁≡A₂
          ⊢B₁ , ⊢B₂        = wf-⊢≡ B₁≡B₂
          _ , ⊢u₁ , ⊢u₂    = wf-⊢≡∷ u₁≡u₂
          _ , ⊢v₁ , ⊢v₂    = wf-⊢≡∷ v₁≡v₂
          _ , ⊢w₁ , ⊢w₂    = wf-⊢≡∷ w₁≡w₂
          A₁≡A₂′           = wkEq₁ ⊢A₂ A₁≡A₂
          ⊢rfl             = PE.subst (_⊢_∷_ _ _)
                               (PE.sym $
                                PE.cong₃ Id (wk1-sgSubst _ _)
                                  (wk1-sgSubst _ _) PE.refl) $
                             rflⱼ ⊢t₁
          [v₁,w₁]≡[v₂,w₂]  = ⊢ˢʷ≡∷∙⇔ .proj₂
                               ( ⊢ˢʷ≡∷-sgSubst ⊢v₁ ⊢v₂ v₁≡v₂
                               , PE.subst (_⊢_∷_ _ _)
                                   (PE.sym $
                                    PE.cong₃ Id (wk1-sgSubst _ _)
                                      (wk1-sgSubst _ _) PE.refl)
                                   ⊢w₁
                               , PE.subst (_⊢_∷_ _ _)
                                   (PE.sym $
                                    PE.cong₃ Id (wk1-sgSubst _ _)
                                      (wk1-sgSubst _ _) PE.refl)
                                   (conv ⊢w₂ $
                                    Id-cong (refl ⊢A₁) (refl ⊢t₁) v₁≡v₂)
                               , PE.subst (_⊢_≡_∷_ _ _ _)
                                   (PE.sym $
                                    PE.cong₃ Id (wk1-sgSubst _ _)
                                      (wk1-sgSubst _ _) PE.refl)
                                   w₁≡w₂
                               )
          _ , ⊢[v₁,w₁] , _ = wf-⊢ˢʷ≡∷ [v₁,w₁]≡[v₂,w₂]
      in
      subst-⊢ ⊢B₁ ⊢[v₁,w₁] ,
      Jⱼ ⊢t₁ ⊢B₁ ⊢u₁ ⊢v₁ ⊢w₁ ,
      conv
        (Jⱼ ⊢t₂′
           (stability-⊢
              (refl-∙⟨ ⊢A₂ ∣ A₁≡A₂ ⟩
                 ∙⟨ Idⱼ (wk₁ ⊢A₂ ⊢A₂) (wkTerm₁ ⊢A₂ ⊢t₂′) (var₀ ⊢A₂)
                  ∣ Id-cong A₁≡A₂′ (wkEqTerm₁ ⊢A₂ t₁≡t₂)
                      (refl (conv (var₀ ⊢A₂) (sym A₁≡A₂′)))
                  ⟩)
              ⊢B₂)
           (conv ⊢u₂ $
            subst-⊢≡ B₁≡B₂ $
            ⊢ˢʷ≡∷∙⇔ .proj₂
              ( ⊢ˢʷ≡∷-sgSubst ⊢t₁ ⊢t₂ t₁≡t₂
              , ⊢rfl
              , conv ⊢rfl
                  (PE.subst₂ (_⊢_≡_ _)
                     (PE.sym $
                      PE.cong₃ Id
                        (wk1-sgSubst _ _) (wk1-sgSubst _ _) PE.refl)
                     (PE.sym $
                      PE.cong₃ Id
                        (wk1-sgSubst _ _) (wk1-sgSubst _ _) PE.refl) $
                   Id-cong (refl ⊢A₁) (refl ⊢t₁) t₁≡t₂)
              , refl ⊢rfl
              ))
           (conv ⊢v₂ A₁≡A₂) (conv ⊢w₂ (Id-cong A₁≡A₂ t₁≡t₂ v₁≡v₂)))
        (sym (subst-⊢≡ B₁≡B₂ [v₁,w₁]≡[v₂,w₂]))
    (J-β ⊢t ⊢B ⊢u PE.refl) →
      wf-⊢∷ ⊢u , Jⱼ ⊢t ⊢B ⊢u ⊢t (rflⱼ ⊢t) , ⊢u
    (K-cong A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ ok) →
      let ⊢A₁ , ⊢A₂     = wf-⊢≡ A₁≡A₂
          _ , ⊢t₁ , ⊢t₂ = wf-⊢≡∷ t₁≡t₂
          ⊢B₁ , ⊢B₂     = wf-⊢≡ B₁≡B₂
          _ , ⊢u₁ , ⊢u₂ = wf-⊢≡∷ u₁≡u₂
          _ , ⊢v₁ , ⊢v₂ = wf-⊢≡∷ v₁≡v₂
          Id≡Id         = Id-cong A₁≡A₂ t₁≡t₂ t₁≡t₂
          ⊢t₂′          = conv ⊢t₂ A₁≡A₂
      in
      subst-⊢ ⊢B₁ (⊢ˢʷ∷-sgSubst ⊢v₁) ,
      Kⱼ ⊢B₁ ⊢u₁ ⊢v₁ ok ,
      conv
        (Kⱼ (stability-⊢ (refl-∙⟨ Idⱼ ⊢A₂ ⊢t₂′ ⊢t₂′ ∣ Id≡Id ⟩) ⊢B₂)
           (conv ⊢u₂ $
            subst-⊢≡ B₁≡B₂ (refl-⊢ˢʷ≡∷ (⊢ˢʷ∷-sgSubst (rflⱼ ⊢t₁))))
           (conv ⊢v₂ Id≡Id) ok)
        (sym (subst-⊢≡ B₁≡B₂ (⊢ˢʷ≡∷-sgSubst ⊢v₁ ⊢v₂ v₁≡v₂)))
    (K-β ⊢B ⊢u ok) →
      let _ , (⊢t , _) , _ = inversion-Id-⊢ (⊢∙→⊢ (wf ⊢B)) in
      wf-⊢∷ ⊢u , Kⱼ ⊢B ⊢u (rflⱼ ⊢t) ok , ⊢u
    ([]-cong-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ ok) →
      let open Erased ([]-cong→Erased ok)
          ⊢A₁ , ⊢A₂     = wf-⊢≡ A₁≡A₂
          _ , ⊢t₁ , ⊢t₂ = wf-⊢≡∷ t₁≡t₂
          _ , ⊢u₁ , ⊢u₂ = wf-⊢≡∷ u₁≡u₂
          _ , ⊢v₁ , ⊢v₂ = wf-⊢≡∷ v₁≡v₂
      in
      Idⱼ (Erasedⱼ ⊢A₁) ([]ⱼ ⊢A₁ ⊢t₁) ([]ⱼ ⊢A₁ ⊢u₁) ,
      []-congⱼ ⊢A₁ ⊢t₁ ⊢u₁ ⊢v₁ ok ,
      conv
        ([]-congⱼ ⊢A₂ (conv ⊢t₂ A₁≡A₂) (conv ⊢u₂ A₁≡A₂)
           (conv ⊢v₂ (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂)) ok)
        (_⊢_≡_.sym $
         Id-cong (Erased-cong ⊢A₁ A₁≡A₂) ([]-cong′ ⊢A₁ t₁≡t₂)
           ([]-cong′ ⊢A₁ u₁≡u₂))
    ([]-cong-β ⊢t PE.refl ok) →
      let open Erased ([]-cong→Erased ok)
          ⊢A   = wf-⊢∷ ⊢t
          ⊢[t] = []ⱼ ⊢A ⊢t
      in
      Idⱼ (Erasedⱼ ⊢A) ⊢[t] ⊢[t] ,
      []-congⱼ ⊢A ⊢t ⊢t (rflⱼ ⊢t) ok ,
      rflⱼ ⊢[t]
    (equality-reflection _ ⊢Id _) →
      inversion-Id ⊢Id

  ⊢≡→⊢ : Γ ⊢ t ≡ t ∷ A → Γ ⊢ t ∷ A
  ⊢≡→⊢ t≡t = wf-⊢≡∷ t≡t .proj₂ .proj₁

opaque

  -- A well-formedness lemma for _⊢ˢ_≡_∷_.

  wf-⊢ˢ≡∷ : ⊢ Γ → Δ ⊢ˢ σ₁ ≡ σ₂ ∷ Γ → Δ ⊢ˢ σ₁ ∷ Γ × Δ ⊢ˢ σ₂ ∷ Γ
  wf-⊢ˢ≡∷ _      id              = id , id
  wf-⊢ˢ≡∷ (∙ ⊢A) (σ₁≡σ₂ , t₁≡t₂) =
    let ⊢σ₁ , ⊢σ₂     = wf-⊢ˢ≡∷ (wf ⊢A) σ₁≡σ₂
        _ , ⊢t₁ , ⊢t₂ = wf-⊢≡∷ t₁≡t₂
        σ₁≡σ₂         = ⊢ˢʷ≡∷⇔ .proj₂ (wfTerm ⊢t₁ , ⊢σ₁ , ⊢σ₂ , σ₁≡σ₂)
    in
    (⊢σ₁ , ⊢t₁) , (⊢σ₂ , conv ⊢t₂ (subst-⊢≡ (refl ⊢A) σ₁≡σ₂))
