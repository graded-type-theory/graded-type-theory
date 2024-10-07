------------------------------------------------------------------------
-- Type conversion lemmata for the logical relation
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Properties.Conversion
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped M hiding (Wk; K)
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.RedSteps R
open import Definition.Typed.Properties R
import Definition.Typed.Weakening R as Wk
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Properties.Escape R
open import Definition.LogicalRelation.Properties.Kit R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Irrelevance R

open import Tools.Function
open import Tools.Nat hiding (_<_)
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    p q : M
    Γ : Con Term n

mutual
  -- Helper function for conversion of terms converting from left to right.
  convTermT₁ : ∀ {l l′ A B t} {[A] : Γ ⊩⟨ l ⟩ A} {[B] : Γ ⊩⟨ l′ ⟩ B}
             → ShapeView Γ l l′ A B [A] [B]
             → Γ ⊩⟨ l ⟩  A ≡ B / [A]
             → Γ ⊩⟨ l ⟩  t ∷ A / [A]
             → Γ ⊩⟨ l′ ⟩ t ∷ B / [B]
  convTermT₁ (ℕᵥ D D′) A≡B t = t
  convTermT₁ (Emptyᵥ D D′) A≡B t = t
  convTermT₁ (Unitᵥ _ (Unitₜ B⇒*Unit₁ _)) B⇒*Unit₂ ⊩t =
    case Unit-PE-injectivity $
         whrDet* (red B⇒*Unit₁ , Unitₙ) (B⇒*Unit₂ , Unitₙ) of λ {
      (_ , PE.refl) →
    ⊩t }
  convTermT₁ (ne (ne _ D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D′ neM K≡M)
             (neₜ k d (neNfₜ neK₂ ⊢k k≡k)) =
    let K≡K₁ = PE.subst (λ x → _ ⊢ _ ≡ x)
                        (whrDet* (red D′ , ne neM) (red D₁ , ne neK₁))
                        (≅-eq K≡M)
    in  neₜ k (convRed:*: d K≡K₁)
            (neNfₜ neK₂ (conv ⊢k K≡K₁) (~-conv k≡k K≡K₁))
  convTermT₁
    {Γ = Γ}
    (Bᵥ (BΠ p q) (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _)
       (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁ _))
    (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
    (Πₜ f d funcF f≡f [f] [f]₁) =
    let ΠF₁G₁≡ΠF′G′       = whrDet* (red D₁ , ΠΣₙ) (red D′ , ΠΣₙ)
        F₁≡F′ , G₁≡G′ , Π₁≡Π′ = B-PE-injectivity BΠ! BΠ! ΠF₁G₁≡ΠF′G′
        ΠFG≡ΠF₁G₁ = PE.subst (λ x → Γ ⊢ Π p , q ▷ F ▹ G ≡ x) (PE.sym ΠF₁G₁≡ΠF′G′)
                             (≅-eq A≡B)
    in  Πₜ f (convRed:*: d ΠFG≡ΠF₁G₁) funcF (≅-conv f≡f ΠFG≡ΠF₁G₁)
           (λ {_} {ρ} [ρ] ⊢Δ [a] [b] [a≡b] →
              let [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                           ([F] [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ)
                  [a]₁ = convTerm₂ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a]
                  [b]₁ = convTerm₂ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [b]
                  [a≡b]₁ = convEqTerm₂ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a≡b]
                  [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ]₀)
                                                    (PE.sym G₁≡G′))
                                           ([G] [ρ] ⊢Δ [a]₁)
                                           ([G≡G′] [ρ] ⊢Δ [a]₁)
              in  convEqTerm₁ ([G] [ρ] ⊢Δ [a]₁) ([G]₁ [ρ] ⊢Δ [a]) [G≡G₁]
                              ([f] [ρ] ⊢Δ [a]₁ [b]₁ [a≡b]₁))
          (λ {_} {ρ} [ρ] ⊢Δ [a] →
             let [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                          ([F] [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ)
                 [a]₁ = convTerm₂ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a]
                 [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ]₀)
                                                   (PE.sym G₁≡G′))
                                          ([G] [ρ] ⊢Δ [a]₁)
                                          ([G≡G′] [ρ] ⊢Δ [a]₁)
             in  convTerm₁ ([G] [ρ] ⊢Δ [a]₁) ([G]₁ [ρ] ⊢Δ [a]) [G≡G₁]
                   ([f]₁ [ρ] ⊢Δ [a]₁))
  convTermT₁
    {Γ = Γ} {l = l} {l′ = l′}
    (Bᵥ (BΣ 𝕤 p q) (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _)
       (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁ _))
    (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
    (Σₜ f d f≡f pProd ([f₁] , [f₂])) =
    let ΣF₁G₁≡ΣF′G′       = whrDet* (red D₁ , ΠΣₙ) (red D′ , ΠΣₙ)
        F₁≡F′ , G₁≡G′ , _ = B-PE-injectivity BΣ! BΣ! ΣF₁G₁≡ΣF′G′
        ΣFG≡ΣF₁G₁ =
          PE.subst (λ x → Γ ⊢ Σˢ p , q ▷ F ▹ G ≡ x) (PE.sym ΣF₁G₁≡ΣF′G′)
            (≅-eq A≡B)
        ⊢Γ = wf ⊢F
        F≡F₁ = PE.subst (λ x → Γ ⊩⟨ l ⟩ wk id F ≡ wk id x / [F] Wk.id ⊢Γ)
                        (PE.sym F₁≡F′)
                        ([F≡F′] Wk.id ⊢Γ)
        [f₁]₁ = convTerm₁ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id (wf ⊢F₁)) F≡F₁ [f₁]
        G≡G₁ = PE.subst (λ x → Γ ⊩⟨ l ⟩ wk (lift id) G [ _ ]₀ ≡ wk (lift id) x [ _ ]₀ / [G] Wk.id ⊢Γ [f₁])
                        (PE.sym G₁≡G′)
                        ([G≡G′] Wk.id ⊢Γ [f₁])
        [f₂]₁ = convTerm₁ ([G] Wk.id ⊢Γ [f₁]) ([G]₁ Wk.id (wf ⊢F₁) [f₁]₁) G≡G₁ [f₂]
    in  Σₜ f (convRed:*: d ΣFG≡ΣF₁G₁) (≅-conv f≡f ΣFG≡ΣF₁G₁) pProd ([f₁]₁ , [f₂]₁)
  convTermT₁
    {Γ = Γ} {l = l} {l′ = l′}
    (Bᵥ (BΣ 𝕨 p q) (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _)
       (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁ _))
    (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
    (Σₜ f d f≡f prodₙ (PE.refl , [f₁] , [f₂] , PE.refl)) =
    let ΣF₁G₁≡ΣF′G′       = whrDet* (red D₁ , ΠΣₙ) (red D′ , ΠΣₙ)
        F₁≡F′ , G₁≡G′ , _ = B-PE-injectivity BΣ! BΣ! ΣF₁G₁≡ΣF′G′
        ΣFG≡ΣF₁G₁ =
          PE.subst (λ x → Γ ⊢ Σʷ p , q ▷ F ▹ G ≡ x) (PE.sym ΣF₁G₁≡ΣF′G′)
            (≅-eq A≡B)
        ⊢Γ = wf ⊢F
        F≡F₁ = PE.subst (λ x → Γ ⊩⟨ l ⟩ wk id F ≡ wk id x / [F] Wk.id ⊢Γ)
                        (PE.sym F₁≡F′)
                        ([F≡F′] Wk.id ⊢Γ)
        [f₁]₁ = convTerm₁ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id (wf ⊢F₁)) F≡F₁ [f₁]
        G≡G₁ = PE.subst (λ x → Γ ⊩⟨ l ⟩ wk (lift id) G [ _ ]₀ ≡ wk (lift id) x [ _ ]₀ / [G] Wk.id ⊢Γ [f₁])
                        (PE.sym G₁≡G′)
                        ([G≡G′] Wk.id ⊢Γ [f₁])
        [f₂]₁ = convTerm₁ ([G] Wk.id ⊢Γ [f₁]) ([G]₁ Wk.id (wf ⊢F₁) [f₁]₁) G≡G₁ [f₂]
    in  Σₜ f (convRed:*: d ΣFG≡ΣF₁G₁) (≅-conv f≡f ΣFG≡ΣF₁G₁) prodₙ
          (PE.refl , [f₁]₁ , [f₂]₁ , PE.refl)
  convTermT₁
    {Γ = Γ} {l = l} {l′ = l′}
    (Bᵥ (BΣ 𝕨 p q) (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _)
       (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁ _))
    (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
    (Σₜ f d f≡f (ne x) f~f) =
    let ΣF₁G₁≡ΣF′G′       = whrDet* (red D₁ , ΠΣₙ) (red D′ , ΠΣₙ)
        ΣFG≡ΣF₁G₁ =
          PE.subst (λ x → Γ ⊢ Σʷ p , q ▷ F ▹ G ≡ x) (PE.sym ΣF₁G₁≡ΣF′G′)
            (≅-eq A≡B)
    in  Σₜ f (convRed:*: d ΣFG≡ΣF₁G₁) (≅-conv f≡f ΣFG≡ΣF₁G₁)
           (ne x) (~-conv f~f ΣFG≡ΣF₁G₁)
  convTermT₁ (Uᵥ (Uᵣ l1 l<1 D1) (Uᵣ l2 l<2 D2)) D (Uₜ A d typeA A≡A [t]) with whrDet* (red D2 , Uₙ) (red D , Uₙ)
  convTermT₁ (Uᵥ (Uᵣ l1 l<1 D1) (Uᵣ l2 l<2 D2)) D (Uₜ A d typeA A≡A [t])
        | PE.refl =
    Uₜ A (convRed:*: d (refl (_⊢_:⇒*:_.⊢B D))) typeA A≡A
      (irrelevance-⊩< l<1 l<2 [t])
  convTermT₁ (Idᵥ ⊩A ⊩B) A≡B ⊩t@(_ , t⇒*u , _) =
    case whrDet* (red (_⊩ₗId_.⇒*Id ⊩B) , Idₙ) (red ⇒*Id′ , Idₙ) of λ {
      PE.refl →
    case Id≅Id A≡B of λ {
      Id≅Id′ →
      _
    , convRed:*: t⇒*u (≅-eq Id≅Id′)
    , (case ⊩Id∷-view-inhabited ⊩t of λ where
         (ne u-n u~u)   → ne u-n , ~-conv u~u (≅-eq Id≅Id′)
         (rflᵣ lhs≡rhs) →
             rflₙ
           , convEqTerm₁ (_⊩ₗId_.⊩Ty ⊩A) (_⊩ₗId_.⊩Ty ⊩B) Ty≡Ty′
               (lhs≡rhs→lhs′≡rhs′ lhs≡rhs)) }}
    where
    open _⊩ₗId_≡_/_ A≡B
  convTermT₁ (embᵥ₁ ≤ᵘ-refl     A≡B) = convTermT₁          A≡B
  convTermT₁ (embᵥ₁ (≤ᵘ-step p) A≡B) = convTermT₁ (embᵥ₁ p A≡B)
  convTermT₁ (embᵥ₂ ≤ᵘ-refl     A≡B) = convTermT₁          A≡B
  convTermT₁ (embᵥ₂ (≤ᵘ-step p) A≡B) = convTermT₁ (embᵥ₂ p A≡B)

  -- Helper function for conversion of terms converting from right to left.
  convTermT₂ : ∀ {l l′ A B t} {[A] : Γ ⊩⟨ l ⟩ A} {[B] : Γ ⊩⟨ l′ ⟩ B}
           → ShapeView Γ l l′ A B [A] [B]
           → Γ ⊩⟨ l ⟩  A ≡ B / [A]
           → Γ ⊩⟨ l′ ⟩ t ∷ B / [B]
           → Γ ⊩⟨ l ⟩  t ∷ A / [A]
  convTermT₂ (ℕᵥ D D′) A≡B t = t
  convTermT₂ (Emptyᵥ D D′) A≡B t = t
  convTermT₂ (Unitᵥ _ (Unitₜ B⇒*Unit₁ _)) B⇒*Unit₂ ⊩t =
    case Unit-PE-injectivity $
         whrDet* (red B⇒*Unit₁ , Unitₙ) (B⇒*Unit₂ , Unitₙ) of λ {
      (_ , PE.refl) →
    ⊩t }
  convTermT₂ (ne (ne _ D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D′ neM K≡M)
             (neₜ k d (neNfₜ neK₂ ⊢k k≡k)) =
    let K₁≡K = PE.subst (λ x → _ ⊢ x ≡ _)
                        (whrDet* (red D′ , ne neM) (red D₁ , ne neK₁))
                        (sym (≅-eq K≡M))
    in  neₜ k (convRed:*: d K₁≡K)
            (neNfₜ neK₂ (conv ⊢k K₁≡K) (~-conv k≡k K₁≡K))
  convTermT₂
    {Γ = Γ}
    (Bᵥ (BΠ p q) (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _)
       (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁ _))
    (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
    (Πₜ f d funcF f≡f [f] [f]₁) =
    let ΠF₁G₁≡ΠF′G′       = whrDet* (red D₁ , ΠΣₙ) (red D′ , ΠΣₙ)
        F₁≡F′ , G₁≡G′ , _ = B-PE-injectivity BΠ! BΠ! ΠF₁G₁≡ΠF′G′
        ΠFG≡ΠF₁G₁ = PE.subst (λ x → Γ ⊢ Π p , q ▷ F ▹ G ≡ x)
                             (PE.sym ΠF₁G₁≡ΠF′G′) (≅-eq A≡B)
    in  Πₜ f (convRed:*: d (sym ΠFG≡ΠF₁G₁)) funcF (≅-conv f≡f (sym ΠFG≡ΠF₁G₁))
           (λ {_} {ρ} [ρ] ⊢Δ [a] [b] [a≡b] →
              let [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                           ([F] [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ)
                  [a]₁ = convTerm₁ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a]
                  [b]₁ = convTerm₁ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [b]
                  [a≡b]₁ = convEqTerm₁ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a≡b]
                  [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ]₀)
                                                    (PE.sym G₁≡G′))
                                           ([G] [ρ] ⊢Δ [a])
                                           ([G≡G′] [ρ] ⊢Δ [a])
              in  convEqTerm₂ ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁)
                              [G≡G₁] ([f] [ρ] ⊢Δ [a]₁ [b]₁ [a≡b]₁))
           (λ {_} {ρ} [ρ] ⊢Δ [a] →
              let [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                           ([F] [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ)
                  [a]₁ = convTerm₁ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a]
                  [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ]₀)
                                                    (PE.sym G₁≡G′))
                                           ([G] [ρ] ⊢Δ [a])
                                           ([G≡G′] [ρ] ⊢Δ [a])
              in  convTerm₂ ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁)
                            [G≡G₁] ([f]₁ [ρ] ⊢Δ [a]₁))
  convTermT₂
    {Γ = Γ} {l = l} {l′ = l′}
    (Bᵥ (BΣ 𝕤 p q) (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _)
       (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁ _))
    (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
    (Σₜ f d f≡f pProd ([f₁]₁ , [f₂]₁)) =
    let ΣF₁G₁≡ΣF′G′       = whrDet* (red D₁ , ΠΣₙ) (red D′ , ΠΣₙ)
        F₁≡F′ , G₁≡G′ , _ = B-PE-injectivity BΣ! BΣ! ΣF₁G₁≡ΣF′G′
        ΣFG≡ΣF₁G₁ =
          PE.subst (λ x → Γ ⊢ Σˢ p , q ▷ F ▹ G ≡ x)
            (PE.sym ΣF₁G₁≡ΣF′G′) (≅-eq A≡B)
        ⊢Γ = wf ⊢F
        F≡F₁ = PE.subst (λ x → Γ ⊩⟨ l ⟩ wk id F ≡ wk id x / [F] Wk.id ⊢Γ)
                        (PE.sym F₁≡F′)
                        ([F≡F′] Wk.id ⊢Γ)
        [f₁] = convTerm₂ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id (wf ⊢F₁)) F≡F₁ [f₁]₁
        G≡G₁ = PE.subst (λ x → Γ ⊩⟨ l ⟩ wk (lift id) G [ _ ]₀ ≡ wk (lift id) x [ _ ]₀ / [G] Wk.id ⊢Γ [f₁])
                        (PE.sym G₁≡G′)
                        ([G≡G′] Wk.id ⊢Γ [f₁])
        [f₂] = convTerm₂ ([G] Wk.id ⊢Γ [f₁]) ([G]₁ Wk.id (wf ⊢F₁) [f₁]₁) G≡G₁ [f₂]₁
    in  Σₜ f (convRed:*: d (sym ΣFG≡ΣF₁G₁)) (≅-conv f≡f (sym ΣFG≡ΣF₁G₁)) pProd ([f₁] , [f₂])
  convTermT₂
    {Γ = Γ} {l = l} {l′ = l′}
    (Bᵥ (BΣ 𝕨 p q) (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _)
       (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁ _))
    (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
    (Σₜ f d f≡f (prodₙ {t = f₁} {u = f₂})
       (PE.refl , [f₁]₁ , [f₂]₁ , PE.refl)) =
    let ΣF₁G₁≡ΣF′G′       = whrDet* (red D₁ , ΠΣₙ) (red D′ , ΠΣₙ)
        F₁≡F′ , G₁≡G′ , _ = B-PE-injectivity BΣ! BΣ! ΣF₁G₁≡ΣF′G′
        ΣFG≡ΣF₁G₁ =
          PE.subst (λ x → Γ ⊢ Σʷ p , q ▷ F ▹ G ≡ x) (PE.sym ΣF₁G₁≡ΣF′G′)
            (≅-eq A≡B)
        ⊢Γ = wf ⊢F
        F≡F₁ = PE.subst (λ x → Γ ⊩⟨ l ⟩ wk id F ≡ wk id x / [F] Wk.id ⊢Γ)
                        (PE.sym F₁≡F′)
                        ([F≡F′] Wk.id ⊢Γ)
        [f₁] = convTerm₂ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id (wf ⊢F₁)) F≡F₁ [f₁]₁
        G≡G₁ = PE.subst (λ x → Γ ⊩⟨ l ⟩ wk (lift id) G [ f₁ ]₀ ≡ wk (lift id) x [ f₁ ]₀ / [G] Wk.id ⊢Γ [f₁])
                        (PE.sym G₁≡G′)
                        ([G≡G′] Wk.id ⊢Γ [f₁])
        [f₂] = convTerm₂ ([G] Wk.id ⊢Γ [f₁]) ([G]₁ Wk.id (wf ⊢F₁) [f₁]₁) G≡G₁ [f₂]₁
    in  Σₜ f (convRed:*: d (sym ΣFG≡ΣF₁G₁)) (≅-conv f≡f (sym ΣFG≡ΣF₁G₁)) prodₙ
          (PE.refl , [f₁] , [f₂] , PE.refl)
  convTermT₂
    {Γ = Γ} {l = l} {l′ = l′}
    (Bᵥ (BΣ 𝕨 p q) (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _)
       (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁ _))
    (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
    (Σₜ f d f≡f (ne x) f~f) =
    let ΣF₁G₁≡ΣF′G′       = whrDet* (red D₁ , ΠΣₙ) (red D′ , ΠΣₙ)
        ΣFG≡ΣF₁G₁ =
          PE.subst (λ x → Γ ⊢ Σʷ p , q ▷ F ▹ G ≡ x) (PE.sym ΣF₁G₁≡ΣF′G′)
            (≅-eq A≡B)
    in  Σₜ f (convRed:*: d (sym ΣFG≡ΣF₁G₁)) (≅-conv f≡f (sym ΣFG≡ΣF₁G₁))
           (ne x) (~-conv f~f (sym ΣFG≡ΣF₁G₁))
  convTermT₂ (Uᵥ (Uᵣ l1 l<1 D1) (Uᵣ l2 l<2 D2)) D (Uₜ A d typeA A≡A [t]) with whrDet* (red D2 , Uₙ) (red D , Uₙ)
  convTermT₂ (Uᵥ (Uᵣ l1 l<1 D1) (Uᵣ l2 l<2 D2)) D (Uₜ A d typeA A≡A [t])
        | PE.refl =
    Uₜ A (convRed:*: d (refl (_⊢_:⇒*:_.⊢B D))) typeA A≡A
      (irrelevance-⊩< l<2 l<1 [t])
  convTermT₂ (Idᵥ ⊩A ⊩B) A≡B ⊩t@(_ , t⇒*u , _) =
    case whrDet* (red (_⊩ₗId_.⇒*Id ⊩B) , Idₙ) (red ⇒*Id′ , Idₙ) of λ {
      PE.refl →
    case Id≅Id A≡B of λ {
      Id≅Id′ →
      _
    , convRed:*: t⇒*u (≅-eq (≅-sym Id≅Id′))
    , (case ⊩Id∷-view-inhabited ⊩t of λ where
         (ne u-n u~u)   → ne u-n , ~-conv u~u (sym (≅-eq Id≅Id′))
         (rflᵣ lhs≡rhs) →
             rflₙ
           , lhs′≡rhs′→lhs≡rhs
               (convEqTerm₂ (_⊩ₗId_.⊩Ty ⊩A) (_⊩ₗId_.⊩Ty ⊩B) Ty≡Ty′
                  lhs≡rhs)) }}
    where
    open _⊩ₗId_≡_/_ A≡B
  convTermT₂ (embᵥ₁ ≤ᵘ-refl     A≡B) = convTermT₂          A≡B
  convTermT₂ (embᵥ₁ (≤ᵘ-step p) A≡B) = convTermT₂ (embᵥ₁ p A≡B)
  convTermT₂ (embᵥ₂ ≤ᵘ-refl     A≡B) = convTermT₂          A≡B
  convTermT₂ (embᵥ₂ (≤ᵘ-step p) A≡B) = convTermT₂ (embᵥ₂ p A≡B)

  -- Conversion of terms converting from left to right.
  convTerm₁ : ∀ {A B t l l′} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l′ ⟩ B)
            → Γ ⊩⟨ l ⟩  A ≡ B / [A]
            → Γ ⊩⟨ l ⟩  t ∷ A / [A]
            → Γ ⊩⟨ l′ ⟩ t ∷ B / [B]
  convTerm₁ [A] [B] A≡B t = convTermT₁ (goodCases [A] [B] A≡B) A≡B t

  -- Conversion of terms converting from right to left.
  convTerm₂ : ∀ {A B t l l′} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l′ ⟩ B)
          → Γ ⊩⟨ l ⟩  A ≡ B / [A]
          → Γ ⊩⟨ l′ ⟩ t ∷ B / [B]
          → Γ ⊩⟨ l ⟩  t ∷ A / [A]
  -- NOTE: this would be easier to define by mutual induction with symEq (which needs conversion),
  -- rather than by defining everything from scratch for both left-to-right and right-to-left,
  -- but with the mutual definition termination checking fails in Agda.
  convTerm₂ [A] [B] A≡B t = convTermT₂ (goodCases [A] [B] A≡B) A≡B t

  -- Conversion of terms converting from right to left
  -- with some propositionally equal types.
  convTerm₂′ : ∀ {A B B′ t l l′} → B PE.≡ B′
          → ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l′ ⟩ B)
          → Γ ⊩⟨ l ⟩  A ≡ B′ / [A]
          → Γ ⊩⟨ l′ ⟩ t ∷ B / [B]
          → Γ ⊩⟨ l ⟩  t ∷ A / [A]
  convTerm₂′ PE.refl [A] [B] A≡B t = convTerm₂ [A] [B] A≡B t


  -- Helper function for conversion of term equality converting from left to right.
  convEqTermT₁ : ∀ {l l′ A B t u} {[A] : Γ ⊩⟨ l ⟩ A} {[B] : Γ ⊩⟨ l′ ⟩ B}
               → ShapeView Γ l l′ A B [A] [B]
               → Γ ⊩⟨ l ⟩  A ≡ B / [A]
               → Γ ⊩⟨ l ⟩  t ≡ u ∷ A / [A]
               → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ B / [B]
  convEqTermT₁ (ℕᵥ D D′) A≡B t≡u = t≡u
  convEqTermT₁ (Emptyᵥ D D′) A≡B t≡u = t≡u
  convEqTermT₁ (Unitᵥ _ (Unitₜ B⇒*Unit₁ _)) B⇒*Unit₂ t≡u =
    case Unit-PE-injectivity $
         whrDet* (red B⇒*Unit₁ , Unitₙ) (B⇒*Unit₂ , Unitₙ) of λ {
      (_ , PE.refl) →
    t≡u }
  convEqTermT₁ (ne (ne _ D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D′ neM K≡M)
               (neₜ₌ k m d d′ (neNfₜ₌ neK₂ neM₁ k≡m)) =
    let K≡K₁ = PE.subst (λ x → _ ⊢ _ ≡ x)
                        (whrDet* (red D′ , ne neM) (red D₁ , ne neK₁))
                        (≅-eq K≡M)
    in  neₜ₌ k m (convRed:*: d K≡K₁)
                 (convRed:*: d′ K≡K₁)
                 (neNfₜ₌ neK₂ neM₁ (~-conv k≡m K≡K₁))
  convEqTermT₁
    {Γ = Γ}
    (Bᵥ (BΠ p q) (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext ok)
       (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁))
    (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
    (Πₜ₌ f g d d′ funcF funcG t≡u [t] [u] [t≡u]) =
    let [A] = Bᵣ′ BΠ! F G D ⊢F ⊢G A≡A [F] [G] G-ext ok
        [B] = Bᵣ′ BΠ! F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁
        [A≡B] = B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]
        ΠF₁G₁≡ΠF′G′ = whrDet* (red D₁ , ΠΣₙ) (red D′ , ΠΣₙ)
        ΠFG≡ΠF₁G₁ = PE.subst (λ x → Γ ⊢ Π p , q ▷ F ▹ G ≡ x)
                             (PE.sym ΠF₁G₁≡ΠF′G′) (≅-eq A≡B)
    in  Πₜ₌ f g (convRed:*: d ΠFG≡ΠF₁G₁) (convRed:*: d′ ΠFG≡ΠF₁G₁)
            funcF funcG (≅-conv t≡u ΠFG≡ΠF₁G₁)
            (convTerm₁ [A] [B] [A≡B] [t]) (convTerm₁ [A] [B] [A≡B] [u])
            (λ {_} {ρ} [ρ] ⊢Δ [a] →
               let F₁≡F′ , G₁≡G′ , _ =
                     B-PE-injectivity BΠ! BΠ!
                       (whrDet* (red D₁ , ΠΣₙ) (red D′ , ΠΣₙ))
                   [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                            ([F] [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ)
                   [a]₁ = convTerm₂ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a]
                   [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ]₀)
                                                     (PE.sym G₁≡G′))
                                            ([G] [ρ] ⊢Δ [a]₁)
                                            ([G≡G′] [ρ] ⊢Δ [a]₁)
               in  convEqTerm₁ ([G] [ρ] ⊢Δ [a]₁) ([G]₁ [ρ] ⊢Δ [a])
                               [G≡G₁] ([t≡u] [ρ] ⊢Δ [a]₁))
  convEqTermT₁
    {Γ = Γ}
    (Bᵥ (BΣ 𝕤 p′ q) (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext ok)
       (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁))
    (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
    (Σₜ₌ p r d d′ pProd rProd p≅r [t] [u]
       ([p₁] , [r₁] , [fst≡] , [snd≡])) =
    let [A] = Bᵣ′ BΣ! F G D ⊢F ⊢G A≡A [F] [G] G-ext ok
        [B] = Bᵣ′ BΣ! F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁
        [A≡B] = B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]
        ΣF₁G₁≡ΣF′G′       = whrDet* (red D₁ , ΠΣₙ) (red D′ , ΠΣₙ)
        F₁≡F′ , G₁≡G′ , _ = B-PE-injectivity BΣ! BΣ! ΣF₁G₁≡ΣF′G′
        ΣFG≡ΣF₁G₁ = PE.subst (λ x → Γ ⊢ Σˢ p′ , q ▷ F ▹ G ≡ x)
                             (PE.sym ΣF₁G₁≡ΣF′G′) (≅-eq A≡B)
        ⊢Γ = wf ⊢F
        ⊢Γ₁ = wf ⊢F₁
        F≡F₁ = PE.subst (λ x → Γ ⊩⟨ _ ⟩ wk id F ≡ wk id x / [F] Wk.id ⊢Γ)
                        (PE.sym F₁≡F′)
                        ([F≡F′] Wk.id ⊢Γ)
        [p₁]₁ = convTerm₁ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id ⊢Γ₁) F≡F₁ [p₁]
        [r₁]₁ = convTerm₁ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id ⊢Γ₁) F≡F₁ [r₁]
        [fst≡]₁ = convEqTerm₁ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id ⊢Γ₁) F≡F₁ [fst≡]
        G≡G₁ = PE.subst (λ x → Γ ⊩⟨ _ ⟩ wk (lift id) G [ _ ]₀ ≡ wk (lift id) x [ _ ]₀ / [G] Wk.id ⊢Γ [p₁])
                        (PE.sym G₁≡G′)
                        ([G≡G′] Wk.id ⊢Γ [p₁])
        [snd≡]₁ = convEqTerm₁ ([G] Wk.id ⊢Γ [p₁]) ([G]₁ Wk.id ⊢Γ₁ [p₁]₁) G≡G₁ [snd≡]
    in  Σₜ₌ p r (convRed:*: d ΣFG≡ΣF₁G₁) (convRed:*: d′ ΣFG≡ΣF₁G₁)
            pProd rProd (≅-conv p≅r ΣFG≡ΣF₁G₁)
            (convTerm₁ [A] [B] [A≡B] [t]) (convTerm₁ [A] [B] [A≡B] [u])
            ([p₁]₁ , [r₁]₁ , [fst≡]₁ , [snd≡]₁)
  convEqTermT₁
    {Γ = Γ}
    (Bᵥ (BΣ 𝕨 p′ q) (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext ok)
       (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁))
    (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
    (Σₜ₌ p r d d′ (prodₙ {t = p₁}) prodₙ p≅r [t] [u]
       (PE.refl , PE.refl ,
        [p₁] , [r₁] , [p₂] , [r₂] , [fst≡] , [snd≡])) =
    let [A] = Bᵣ′ BΣ! F G D ⊢F ⊢G A≡A [F] [G] G-ext ok
        [B] = Bᵣ′ BΣ! F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁
        [A≡B] = B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]
        ΣF₁G₁≡ΣF′G′       = whrDet* (red D₁ , ΠΣₙ) (red D′ , ΠΣₙ)
        F₁≡F′ , G₁≡G′ , _ = B-PE-injectivity BΣ! BΣ! ΣF₁G₁≡ΣF′G′
        ΣFG≡ΣF₁G₁ = PE.subst (λ x → Γ ⊢ Σʷ p′ , q ▷ F ▹ G ≡ x)
                             (PE.sym ΣF₁G₁≡ΣF′G′) (≅-eq A≡B)
        ⊢Γ = wf ⊢F
        ⊢Γ₁ = wf ⊢F₁
        F≡F₁ = PE.subst (λ x → Γ ⊩⟨ _ ⟩ wk id F ≡ wk id x / [F] Wk.id ⊢Γ)
                        (PE.sym F₁≡F′)
                        ([F≡F′] Wk.id ⊢Γ)
        Gp≡G₁p = PE.subst (λ x → Γ ⊩⟨ _ ⟩ wk (lift id) G [ _ ]₀ ≡ wk (lift id) x [ _ ]₀ / [G] Wk.id ⊢Γ [p₁])
                          (PE.sym G₁≡G′) ([G≡G′] Wk.id ⊢Γ [p₁])
        Gr≡G₁r = PE.subst (λ x → Γ ⊩⟨ _ ⟩ wk (lift id) G [ _ ]₀ ≡ wk (lift id) x [ _ ]₀ / [G] Wk.id ⊢Γ [r₁])
                          (PE.sym G₁≡G′) ([G≡G′] Wk.id ⊢Γ [r₁])
        [p₁]₁ = convTerm₁ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id ⊢Γ₁) F≡F₁ [p₁]
        [r₁]₁ = convTerm₁ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id ⊢Γ₁) F≡F₁ [r₁]
        [p₂]₁ = convTerm₁ ([G] Wk.id ⊢Γ [p₁]) ([G]₁ Wk.id ⊢Γ₁ [p₁]₁) Gp≡G₁p [p₂]
        [r₂]₁ = convTerm₁ ([G] Wk.id ⊢Γ [r₁]) ([G]₁ Wk.id ⊢Γ₁ [r₁]₁) Gr≡G₁r [r₂]
        [fst≡]₁ = convEqTerm₁ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id ⊢Γ₁) F≡F₁ [fst≡]
        G≡G₁ = PE.subst (λ x → Γ ⊩⟨ _ ⟩ wk (lift id) G [ p₁ ]₀ ≡ wk (lift id) x [ p₁ ]₀ / [G] Wk.id ⊢Γ [p₁])
                        (PE.sym G₁≡G′)
                        ([G≡G′] Wk.id ⊢Γ [p₁])
        [snd≡]₁ = convEqTerm₁ ([G] Wk.id ⊢Γ [p₁]) ([G]₁ Wk.id ⊢Γ₁ [p₁]₁) G≡G₁ [snd≡]
    in  Σₜ₌ p r (convRed:*: d ΣFG≡ΣF₁G₁) (convRed:*: d′ ΣFG≡ΣF₁G₁)
            prodₙ prodₙ (≅-conv p≅r ΣFG≡ΣF₁G₁)
            (convTerm₁ [A] [B] [A≡B] [t]) (convTerm₁ [A] [B] [A≡B] [u])
            (PE.refl , PE.refl ,
             [p₁]₁ , [r₁]₁ , [p₂]₁ , [r₂]₁ , [fst≡]₁ , [snd≡]₁)
  convEqTermT₁
    {Γ = Γ}
    (Bᵥ (BΣ 𝕨 p′ q) (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext ok)
       (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁))
    (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
    (Σₜ₌ p r d d′ (ne x) (ne y) p≅r [t] [u] p~r) =
    let [A] = Bᵣ′ BΣ! F G D ⊢F ⊢G A≡A [F] [G] G-ext ok
        [B] = Bᵣ′ BΣ! F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁
        [A≡B] = B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]
        ΣF₁G₁≡ΣF′G′       = whrDet* (red D₁ , ΠΣₙ) (red D′ , ΠΣₙ)
        F₁≡F′ , G₁≡G′ , _ = B-PE-injectivity BΣ! BΣ! ΣF₁G₁≡ΣF′G′
        ΣFG≡ΣF₁G₁ = PE.subst (λ x → Γ ⊢ Σʷ p′ , q ▷ F ▹ G ≡ x)
                             (PE.sym ΣF₁G₁≡ΣF′G′) (≅-eq A≡B)
        p~r₁ = ~-conv p~r ΣFG≡ΣF₁G₁
    in  Σₜ₌ p r (convRed:*: d ΣFG≡ΣF₁G₁) (convRed:*: d′ ΣFG≡ΣF₁G₁)
            (ne x) (ne y) (≅-conv p≅r ΣFG≡ΣF₁G₁)
            (convTerm₁ [A] [B] [A≡B] [t]) (convTerm₁ [A] [B] [A≡B] [u])
            p~r₁
  convEqTermT₁ (Uᵥ (Uᵣ l1 l<1 D1) (Uᵣ l2 l<2 D2)) D eq with whrDet* (red D2 , Uₙ) (red D , Uₙ)
  convEqTermT₁
    (Uᵥ (Uᵣ _ l<1 _) (Uᵣ _ l<2 _)) _
    (Uₜ₌ A B d d′ typeA typeB A≡B _ [u] [t≡u])
    | PE.refl =
    Uₜ₌ A B d d′ typeA typeB A≡B _ (irrelevance-⊩< l<1 l<2 [u])
      (irrelevance-⊩<≡ l<1 l<2 [t≡u])
  convEqTermT₁ (Idᵥ ⊩A ⊩B) A≡B t≡u@(_ , _ , t⇒*t′ , u⇒*u′ , _) =
    case whrDet* (red (_⊩ₗId_.⇒*Id ⊩B) , Idₙ) (red ⇒*Id′ , Idₙ) of λ {
      PE.refl →
    case ≅-eq (Id≅Id A≡B) of λ {
      Id≡Id′ →
      _ , _
    , convRed:*: t⇒*t′ Id≡Id′
    , convRed:*: u⇒*u′ Id≡Id′
    , (case ⊩Id≡∷-view-inhabited ⊩A t≡u of λ where
         (ne t′-n u′-n t′~u′) →
           ne t′-n , ne u′-n , ~-conv t′~u′ Id≡Id′
         (rfl₌ lhs≡rhs) →
             rflₙ , rflₙ
           , convEqTerm₁ (_⊩ₗId_.⊩Ty ⊩A) (_⊩ₗId_.⊩Ty ⊩B) Ty≡Ty′
               (lhs≡rhs→lhs′≡rhs′ lhs≡rhs)) }}
    where
    open _⊩ₗId_≡_/_ A≡B
  convEqTermT₁ (embᵥ₁ ≤ᵘ-refl     A≡B) = convEqTermT₁          A≡B
  convEqTermT₁ (embᵥ₁ (≤ᵘ-step p) A≡B) = convEqTermT₁ (embᵥ₁ p A≡B)
  convEqTermT₁ (embᵥ₂ ≤ᵘ-refl     A≡B) = convEqTermT₁          A≡B
  convEqTermT₁ (embᵥ₂ (≤ᵘ-step p) A≡B) = convEqTermT₁ (embᵥ₂ p A≡B)

  -- Helper function for conversion of term equality converting from right to left.
  convEqTermT₂ : ∀ {l l′ A B t u} {[A] : Γ ⊩⟨ l ⟩ A} {[B] : Γ ⊩⟨ l′ ⟩ B}
             → ShapeView Γ l l′ A B [A] [B]
             → Γ ⊩⟨ l ⟩  A ≡ B / [A]
             → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ B / [B]
             → Γ ⊩⟨ l ⟩  t ≡ u ∷ A / [A]
  convEqTermT₂ (ℕᵥ D D′) A≡B t≡u = t≡u
  convEqTermT₂ (Emptyᵥ D D′) A≡B t≡u = t≡u
  convEqTermT₂ (Unitᵥ _ (Unitₜ B⇒*Unit₁ _)) B⇒*Unit₂ t≡u =
    case Unit-PE-injectivity $
         whrDet* (red B⇒*Unit₁ , Unitₙ) (B⇒*Unit₂ , Unitₙ) of λ {
      (_ , PE.refl) →
    t≡u }
  convEqTermT₂ (ne (ne _ D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D′ neM K≡M)
               (neₜ₌ k m d d′ (neNfₜ₌ neK₂ neM₁ k≡m)) =
    let K₁≡K = PE.subst (λ x → _ ⊢ x ≡ _)
                        (whrDet* (red D′ , ne neM) (red D₁ , ne neK₁))
                        (sym (≅-eq K≡M))
    in  neₜ₌ k m (convRed:*: d K₁≡K) (convRed:*: d′ K₁≡K)
                 (neNfₜ₌ neK₂ neM₁ (~-conv k≡m K₁≡K))
  convEqTermT₂
    {Γ = Γ}
    (Bᵥ (BΠ p q) (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext ok)
       (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁))
    (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
    (Πₜ₌ f g d d′ funcF funcG t≡u [t] [u] [t≡u]) =
    let [A] = Bᵣ′ BΠ! F G D ⊢F ⊢G A≡A [F] [G] G-ext ok
        [B] = Bᵣ′ BΠ! F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁
        [A≡B] = B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]
        ΠF₁G₁≡ΠF′G′ = whrDet* (red D₁ , ΠΣₙ) (red D′ , ΠΣₙ)
        ΠFG≡ΠF₁G₁ = PE.subst (λ x → Γ ⊢ Π p , q ▷ F ▹ G ≡ x)
                             (PE.sym ΠF₁G₁≡ΠF′G′) (≅-eq A≡B)
    in  Πₜ₌ f g (convRed:*: d (sym ΠFG≡ΠF₁G₁)) (convRed:*: d′ (sym ΠFG≡ΠF₁G₁))
            funcF funcG (≅-conv t≡u (sym ΠFG≡ΠF₁G₁))
            (convTerm₂ [A] [B] [A≡B] [t]) (convTerm₂ [A] [B] [A≡B] [u])
            (λ {_} {ρ} [ρ] ⊢Δ [a] →
               let F₁≡F′ , G₁≡G′ , _ =
                     B-PE-injectivity BΠ! BΠ!
                       (whrDet* (red D₁ , ΠΣₙ) (red D′ , ΠΣₙ))
                   [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                            ([F] [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ)
                   [a]₁ = convTerm₁ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a]
                   [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ]₀)
                                                     (PE.sym G₁≡G′))
                                            ([G] [ρ] ⊢Δ [a])
                                            ([G≡G′] [ρ] ⊢Δ [a])
               in  convEqTerm₂ ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁)
                               [G≡G₁] ([t≡u] [ρ] ⊢Δ [a]₁))
  convEqTermT₂
    {Γ = Γ}
    (Bᵥ (BΣ 𝕤 p′ q) (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext ok)
       (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁))
    (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
    (Σₜ₌ p r d d′ pProd rProd t≡u [t] [u]
       ([p₁]₁ , [r₁]₁ , [fst≡]₁ , [snd≡]₁)) =
    let [A] = Bᵣ′ BΣ! F G D ⊢F ⊢G A≡A [F] [G] G-ext ok
        [B] = Bᵣ′ BΣ! F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁
        [A≡B] = B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]
        ΣF₁G₁≡ΣF′G′       = whrDet* (red D₁ , ΠΣₙ) (red D′ , ΠΣₙ)
        F₁≡F′ , G₁≡G′ , _ = B-PE-injectivity BΣ! BΣ! ΣF₁G₁≡ΣF′G′
        ΣFG≡ΣF₁G₁ = PE.subst (λ x → Γ ⊢ Σˢ p′ , q ▷ F ▹ G ≡ x)
                             (PE.sym ΣF₁G₁≡ΣF′G′) (≅-eq A≡B)
        ⊢Γ = wf ⊢F
        ⊢Γ₁ = wf ⊢F₁
        F≡F₁ = PE.subst (λ x → Γ ⊩⟨ _ ⟩ wk id F ≡ wk id x / [F] Wk.id ⊢Γ)
                        (PE.sym F₁≡F′)
                        ([F≡F′] Wk.id ⊢Γ)
        [p₁] = convTerm₂ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id ⊢Γ₁) F≡F₁ [p₁]₁
        [r₁] = convTerm₂ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id ⊢Γ₁) F≡F₁ [r₁]₁
        [fst≡] = convEqTerm₂ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id ⊢Γ₁) F≡F₁ [fst≡]₁
        G≡G₁ = PE.subst (λ x → Γ ⊩⟨ _ ⟩ wk (lift id) G [ _ ]₀ ≡ wk (lift id) x [ _ ]₀ / [G] Wk.id ⊢Γ [p₁])
                        (PE.sym G₁≡G′)
                        ([G≡G′] Wk.id ⊢Γ [p₁])
        [snd≡] = convEqTerm₂ ([G] Wk.id ⊢Γ [p₁]) ([G]₁ Wk.id ⊢Γ₁ [p₁]₁) G≡G₁ [snd≡]₁
    in  Σₜ₌ p r (convRed:*: d (sym ΣFG≡ΣF₁G₁)) (convRed:*: d′ (sym ΣFG≡ΣF₁G₁))
            pProd rProd (≅-conv t≡u (sym ΣFG≡ΣF₁G₁))
            (convTerm₂ [A] [B] [A≡B] [t]) (convTerm₂ [A] [B] [A≡B] [u])
            ([p₁] , [r₁] , [fst≡] , [snd≡])
  convEqTermT₂
    {Γ = Γ}
    (Bᵥ (BΣ 𝕨 p′ q) (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext ok)
       (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁))
    (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
    (Σₜ₌ p r d d′ (prodₙ {t = p₁}) prodₙ t≡u [t] [u]
       (PE.refl , PE.refl ,
        [p₁]₁ , [r₁]₁ , [p₂]₁ , [r₂]₁ , [fst≡]₁ , [snd≡]₁)) =
    let [A] = Bᵣ′ BΣ! F G D ⊢F ⊢G A≡A [F] [G] G-ext ok
        [B] = Bᵣ′ BΣ! F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁
        [A≡B] = B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]
        ΣF₁G₁≡ΣF′G′       = whrDet* (red D₁ , ΠΣₙ) (red D′ , ΠΣₙ)
        F₁≡F′ , G₁≡G′ , _ = B-PE-injectivity BΣ! BΣ! ΣF₁G₁≡ΣF′G′
        ΣFG≡ΣF₁G₁ = PE.subst (λ x → Γ ⊢ Σʷ p′ , q ▷ F ▹ G ≡ x)
                             (PE.sym ΣF₁G₁≡ΣF′G′) (≅-eq A≡B)
        ⊢Γ = wf ⊢F
        ⊢Γ₁ = wf ⊢F₁
        F≡F₁ = PE.subst (λ x → Γ ⊩⟨ _ ⟩ wk id F ≡ wk id x / [F] Wk.id ⊢Γ)
                        (PE.sym F₁≡F′)
                        ([F≡F′] Wk.id ⊢Γ)
        [p₁] = convTerm₂ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id ⊢Γ₁) F≡F₁ [p₁]₁
        [r₁] = convTerm₂ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id ⊢Γ₁) F≡F₁ [r₁]₁
        Gp≡G₁p = PE.subst (λ x → Γ ⊩⟨ _ ⟩ wk (lift id) G [ _ ]₀ ≡ wk (lift id) x [ _ ]₀ / [G] Wk.id ⊢Γ [p₁])
                          (PE.sym G₁≡G′) ([G≡G′] Wk.id ⊢Γ [p₁])
        Gr≡G₁r = PE.subst (λ x → Γ ⊩⟨ _ ⟩ wk (lift id) G [ _ ]₀ ≡ wk (lift id) x [ _ ]₀ / [G] Wk.id ⊢Γ [r₁])
                          (PE.sym G₁≡G′) ([G≡G′] Wk.id ⊢Γ [r₁])
        [p₂] = convTerm₂ ([G] Wk.id ⊢Γ [p₁]) ([G]₁ Wk.id ⊢Γ₁ [p₁]₁) Gp≡G₁p [p₂]₁
        [r₂] = convTerm₂ ([G] Wk.id ⊢Γ [r₁]) ([G]₁ Wk.id ⊢Γ₁ [r₁]₁) Gr≡G₁r [r₂]₁
        [fst≡] = convEqTerm₂ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id ⊢Γ₁) F≡F₁ [fst≡]₁
        G≡G₁ = PE.subst (λ x → Γ ⊩⟨ _ ⟩ wk (lift id) G [ p₁ ]₀ ≡ wk (lift id) x [ p₁ ]₀ / [G] Wk.id ⊢Γ [p₁])
                        (PE.sym G₁≡G′)
                        ([G≡G′] Wk.id ⊢Γ [p₁])
        [snd≡] = convEqTerm₂ ([G] Wk.id ⊢Γ [p₁]) ([G]₁ Wk.id ⊢Γ₁ [p₁]₁) G≡G₁ [snd≡]₁
    in  Σₜ₌ p r (convRed:*: d (sym ΣFG≡ΣF₁G₁)) (convRed:*: d′ (sym ΣFG≡ΣF₁G₁))
            prodₙ prodₙ (≅-conv t≡u (sym ΣFG≡ΣF₁G₁))
            (convTerm₂ [A] [B] [A≡B] [t]) (convTerm₂ [A] [B] [A≡B] [u])
            (PE.refl , PE.refl ,
             [p₁] , [r₁] , [p₂] , [r₂] , [fst≡] , [snd≡])
  convEqTermT₂
    {Γ = Γ}
    (Bᵥ (BΣ 𝕨 p′ q) (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext ok)
       (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁))
    (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
    (Σₜ₌ p r d d′ (ne x) (ne y) t≡u [t] [u] p~r₁) =
    let [A] = Bᵣ′ BΣ! F G D ⊢F ⊢G A≡A [F] [G] G-ext ok
        [B] = Bᵣ′ BΣ! F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁
        [A≡B] = B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]
        ΣF₁G₁≡ΣF′G′       = whrDet* (red D₁ , ΠΣₙ) (red D′ , ΠΣₙ)
        F₁≡F′ , G₁≡G′ , _ = B-PE-injectivity BΣ! BΣ! ΣF₁G₁≡ΣF′G′
        ΣFG≡ΣF₁G₁ = PE.subst (λ x → Γ ⊢ Σʷ p′ , q ▷ F ▹ G ≡ x)
                             (PE.sym ΣF₁G₁≡ΣF′G′) (≅-eq A≡B)
        p~r = ~-conv p~r₁ (sym ΣFG≡ΣF₁G₁)
    in  Σₜ₌ p r (convRed:*: d (sym ΣFG≡ΣF₁G₁)) (convRed:*: d′ (sym ΣFG≡ΣF₁G₁))
            (ne x) (ne y) (≅-conv t≡u (sym ΣFG≡ΣF₁G₁))
            (convTerm₂ [A] [B] [A≡B] [t]) (convTerm₂ [A] [B] [A≡B] [u])
            p~r
  convEqTermT₂ (Uᵥ (Uᵣ l1 l<1 D1) (Uᵣ l2 l<2 D2)) D eq with whrDet* (red D2 , Uₙ) (red D , Uₙ)
  convEqTermT₂
    (Uᵥ (Uᵣ _ l<1 _) (Uᵣ _ l<2 _)) D
    (Uₜ₌ A B d d′ typeA typeB A≡B _ [u] [t≡u])
    | PE.refl =
    Uₜ₌ A B d d′ typeA typeB A≡B _ (irrelevance-⊩< l<2 l<1 [u])
      (irrelevance-⊩<≡ l<2 l<1 [t≡u])
  convEqTermT₂ (Idᵥ ⊩A ⊩B) A≡B t≡u@(_ , _ , t⇒*t′ , u⇒*u′ , _) =
    case whrDet* (red (_⊩ₗId_.⇒*Id ⊩B) , Idₙ) (red ⇒*Id′ , Idₙ) of λ {
      PE.refl →
    case ≅-eq (≅-sym (Id≅Id A≡B)) of λ {
      Id≡Id′ →
      _ , _
    , convRed:*: t⇒*t′ Id≡Id′
    , convRed:*: u⇒*u′ Id≡Id′
    , (case ⊩Id≡∷-view-inhabited ⊩B t≡u of λ where
         (ne t′-n u′-n t′~u′) →
           ne t′-n , ne u′-n , ~-conv t′~u′ Id≡Id′
         (rfl₌ lhs≡rhs) →
             rflₙ , rflₙ
           , lhs′≡rhs′→lhs≡rhs
               (convEqTerm₂ (_⊩ₗId_.⊩Ty ⊩A) (_⊩ₗId_.⊩Ty ⊩B) Ty≡Ty′
                  lhs≡rhs)) }}
    where
    open _⊩ₗId_≡_/_ A≡B
  convEqTermT₂ (embᵥ₁ ≤ᵘ-refl     A≡B) = convEqTermT₂          A≡B
  convEqTermT₂ (embᵥ₁ (≤ᵘ-step p) A≡B) = convEqTermT₂ (embᵥ₁ p A≡B)
  convEqTermT₂ (embᵥ₂ ≤ᵘ-refl     A≡B) = convEqTermT₂          A≡B
  convEqTermT₂ (embᵥ₂ (≤ᵘ-step p) A≡B) = convEqTermT₂ (embᵥ₂ p A≡B)

  -- Conversion of term equality converting from left to right.
  convEqTerm₁ : ∀ {l l′ A B t u} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l′ ⟩ B)
              → Γ ⊩⟨ l ⟩  A ≡ B / [A]
              → Γ ⊩⟨ l ⟩  t ≡ u ∷ A / [A]
              → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ B / [B]
  convEqTerm₁ [A] [B] A≡B t≡u = convEqTermT₁ (goodCases [A] [B] A≡B) A≡B t≡u

  -- Conversion of term equality converting from right to left.
  convEqTerm₂ : ∀ {l l′ A B t u} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l′ ⟩ B)
            → Γ ⊩⟨ l ⟩  A ≡ B / [A]
            → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ B / [B]
            → Γ ⊩⟨ l ⟩  t ≡ u ∷ A / [A]
  convEqTerm₂ [A] [B] A≡B t≡u = convEqTermT₂ (goodCases [A] [B] A≡B) A≡B t≡u
