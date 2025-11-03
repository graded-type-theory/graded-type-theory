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
open import Definition.Typed.Properties R
open import Definition.Typed.Well-formed R
open import Definition.LogicalRelation R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Properties.Escape R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Properties.Kit R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Properties.Primitive R ⦃ eqrel ⦄
open import Definition.LogicalRelation.ShapeView R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Irrelevance R ⦃ eqrel ⦄

open import Tools.Function
open import Tools.Level
open import Tools.Nat hiding (_<_)
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    p q : M
    Γ : Con Term n
    A B t u : Term n

convEqTermNe : Γ ⊢ A ≡ B → Γ ⊩neNf t ≡ u ∷ A → Γ ⊩neNf t ≡ u ∷ B
convEqTermNe A≡B (neNfₜ₌ inc neK neM k≡m) = neNfₜ₌ inc neK neM (~-conv k≡m A≡B)

mutual
  -- Conversion of terms converting from left to right.
  convTerm₁ : ∀ {A B t l l′} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l′ ⟩ B)
            → Γ ⊩⟨ l ⟩  A ≡ B / [A]
            → Γ ⊩⟨ l ⟩  t ∷ A / [A]
            → Γ ⊩⟨ l′ ⟩ t ∷ B / [B]
  convTerm₁ [A] [B] A≡B t = convEqTerm₁ [A] [B] A≡B t

  -- Conversion of terms converting from right to left.
  convTerm₂ : ∀ {A B t l l′} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l′ ⟩ B)
          → Γ ⊩⟨ l ⟩  A ≡ B / [A]
          → Γ ⊩⟨ l′ ⟩ t ∷ B / [B]
          → Γ ⊩⟨ l ⟩  t ∷ A / [A]
  -- NOTE: this would be easier to define by mutual induction with symEq (which needs conversion),
  -- rather than by defining everything from scratch for both left-to-right and right-to-left,
  -- but with the mutual definition termination checking fails in Agda.
  convTerm₂ [A] [B] A≡B t = convEqTerm₂ [A] [B] A≡B t

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
  convEqTermT₁ (Levelᵥ D D′) A≡B t≡u = t≡u
  convEqTermT₁
    (Liftᵥ (Liftᵣ D _ [F]) (Liftᵣ D′ _ [F′]))
    (Lift₌ D″ k≡k′ F≡F′)
    (Liftₜ₌ _ _ t↘ u↘ t≡u)
    = case whrDet* (D″ , Liftₙ) (D′ , Liftₙ) of λ {
      PE.refl →
    let Lift≡Lift = ≅-eq (≅-Lift-cong (escapeLevelEq k≡k′) (escapeEq [F] F≡F′))
    in Liftₜ₌ _ _ (conv↘∷ t↘ Lift≡Lift) (conv↘∷ u↘ Lift≡Lift)
        (convEqTerm₁ [F] [F′] F≡F′ t≡u) }
  convEqTermT₁ (ℕᵥ D D′) A≡B t≡u = t≡u
  convEqTermT₁ (Emptyᵥ D D′) A≡B t≡u = t≡u
  convEqTermT₁ (Unitᵥ _ _) _ t≡u = t≡u
  convEqTermT₁
    (ne (ne _ _ D neK K≡K) (ne _ K₁ D₁ neK₁ K≡K₁)) (ne₌ _ M D′ neM K≡M)
    (neₜ₌ k m d d′ (neNfₜ₌ inc neK₂ neM₁ k≡m)) =
    let K≡K₁ = PE.subst (λ x → _ ⊢ _ ≡ x)
                        (whrDet* (D′ , ne! neM) (D₁ , ne! neK₁))
                        (≅-eq K≡M)
    in  neₜ₌ k m (conv* d K≡K₁) (conv* d′ K≡K₁)
          (neNfₜ₌ inc neK₂ neM₁ (~-conv k≡m K≡K₁))
  convEqTermT₁
    {Γ = Γ}
    (Bᵥ (BΠ p q) (Bᵣ F G D A≡A [F] [G] G-ext ok)
       (Bᵣ F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁))
    (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
    (Πₜ₌ f g d d′ funcF funcG t≡u [t≡u]) =
    let ΠF₁G₁≡ΠF′G′ = whrDet* (D₁ , ΠΣₙ) (D′ , ΠΣₙ)
        ΠFG≡ΠF₁G₁ = PE.subst (λ x → Γ ⊢ Π p , q ▷ F ▹ G ≡ x)
                             (PE.sym ΠF₁G₁≡ΠF′G′) (≅-eq A≡B)
    in  Πₜ₌ f g (conv* d ΠFG≡ΠF₁G₁) (conv* d′ ΠFG≡ΠF₁G₁)
            funcF funcG (≅-conv t≡u ΠFG≡ΠF₁G₁)
            (λ {_} {ρ} [ρ] ⊩v ⊩w v≡w →
               let F₁≡F′ , G₁≡G′ , _ =
                     B-PE-injectivity BΠ! BΠ!
                       (whrDet* (D₁ , ΠΣₙ) (D′ , ΠΣₙ))
                   [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                              ([F] [ρ]) ([F≡F′] [ρ])
                   ⊩v′ = convTerm₂ ([F] [ρ]) ([F]₁ [ρ]) [F≡F₁] ⊩v
                   [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ]₀)
                                                     (PE.sym G₁≡G′))
                              ([G] [ρ] ⊩v′) ([G≡G′] [ρ] ⊩v′)
               in  convEqTerm₁ ([G] [ρ] ⊩v′) ([G]₁ [ρ] ⊩v) [G≡G₁]
                     ([t≡u] [ρ] ⊩v′
                        (convTerm₂ ([F] [ρ]) ([F]₁ [ρ]) [F≡F₁] ⊩w)
                        (convEqTerm₂ ([F] [ρ]) ([F]₁ [ρ]) [F≡F₁] v≡w)))
  convEqTermT₁
    {Γ = Γ}
    (Bᵥ (BΣ 𝕤 p′ q) (Bᵣ F G D A≡A [F] [G] G-ext ok)
       (Bᵣ F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁))
    (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
    (Σₜ₌ p r d d′ pProd rProd p≅r
       ([p₁] , [r₁] , [fst≡] , [snd≡])) =
    let ΣF₁G₁≡ΣF′G′       = whrDet* (D₁ , ΠΣₙ) (D′ , ΠΣₙ)
        F₁≡F′ , G₁≡G′ , _ = B-PE-injectivity BΣ! BΣ! ΣF₁G₁≡ΣF′G′
        ΣFG≡ΣF₁G₁ = PE.subst (λ x → Γ ⊢ Σˢ p′ , q ▷ F ▹ G ≡ x)
                             (PE.sym ΣF₁G₁≡ΣF′G′) (≅-eq A≡B)
        F≡F₁ = PE.subst (λ x → Γ ⊩⟨ _ ⟩ wk id F ≡ wk id x / [F] _)
                 (PE.sym F₁≡F′) ([F≡F′] _)
        [p₁]₁ = convTerm₁ ([F] _) ([F]₁ _) F≡F₁ [p₁]
        [r₁]₁ = convTerm₁ ([F] _) ([F]₁ _) F≡F₁ [r₁]
        [fst≡]₁ = convEqTerm₁ ([F] _) ([F]₁ _) F≡F₁ [fst≡]
        G≡G₁ = PE.subst
                 (λ x →
                    Γ ⊩⟨ _ ⟩ wk (lift id) G [ _ ]₀ ≡
                      wk (lift id) x [ _ ]₀ / [G] _ [p₁])
                 (PE.sym G₁≡G′) ([G≡G′] _ [p₁])
        [snd≡]₁ = convEqTerm₁ ([G] _ [p₁]) ([G]₁ _ [p₁]₁) G≡G₁ [snd≡]
    in  Σₜ₌ p r (conv* d ΣFG≡ΣF₁G₁) (conv* d′ ΣFG≡ΣF₁G₁)
            pProd rProd (≅-conv p≅r ΣFG≡ΣF₁G₁)
            ([p₁]₁ , [r₁]₁ , [fst≡]₁ , [snd≡]₁)
  convEqTermT₁
    {Γ = Γ}
    (Bᵥ (BΣ 𝕨 p′ q) (Bᵣ F G D A≡A [F] [G] G-ext ok)
       (Bᵣ F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁))
    (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
    (Σₜ₌ p r d d′ (prodₙ {t = p₁}) prodₙ p≅r
       (PE.refl , PE.refl , PE.refl , PE.refl ,
        [p₁] , [r₁] , [fst≡] , [snd≡])) =
    let ΣF₁G₁≡ΣF′G′       = whrDet* (D₁ , ΠΣₙ) (D′ , ΠΣₙ)
        F₁≡F′ , G₁≡G′ , _ = B-PE-injectivity BΣ! BΣ! ΣF₁G₁≡ΣF′G′
        ΣFG≡ΣF₁G₁ = PE.subst (λ x → Γ ⊢ Σʷ p′ , q ▷ F ▹ G ≡ x)
                             (PE.sym ΣF₁G₁≡ΣF′G′) (≅-eq A≡B)
        F≡F₁ = PE.subst (λ x → Γ ⊩⟨ _ ⟩ wk id F ≡ wk id x / [F] _)
                 (PE.sym F₁≡F′) ([F≡F′] _)
        [p₁]₁ = convTerm₁ ([F] _) ([F]₁ _) F≡F₁ [p₁]
        [r₁]₁ = convTerm₁ ([F] _) ([F]₁ _) F≡F₁ [r₁]
        [fst≡]₁ = convEqTerm₁ ([F] _) ([F]₁ _) F≡F₁ [fst≡]
        G≡G₁ = PE.subst
                 (λ x →
                    Γ ⊩⟨ _ ⟩ wk (lift id) G [ p₁ ]₀ ≡
                      wk (lift id) x [ p₁ ]₀ / [G] _ [p₁])
                 (PE.sym G₁≡G′) ([G≡G′] _ [p₁])
        [snd≡]₁ = convEqTerm₁ ([G] _ [p₁]) ([G]₁ _ [p₁]₁) G≡G₁ [snd≡]
    in  Σₜ₌ p r (conv* d ΣFG≡ΣF₁G₁) (conv* d′ ΣFG≡ΣF₁G₁)
            prodₙ prodₙ (≅-conv p≅r ΣFG≡ΣF₁G₁)
            (PE.refl , PE.refl , PE.refl , PE.refl ,
             [p₁]₁ , [r₁]₁ , [fst≡]₁ , [snd≡]₁)
  convEqTermT₁
    {Γ = Γ}
    (Bᵥ (BΣ 𝕨 p′ q) (Bᵣ F G D A≡A [F] [G] G-ext ok)
       (Bᵣ F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁))
    (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
    (Σₜ₌ p r d d′ (ne x) (ne y) p≅r (inc , p~r)) =
    let ΣF₁G₁≡ΣF′G′       = whrDet* (D₁ , ΠΣₙ) (D′ , ΠΣₙ)
        F₁≡F′ , G₁≡G′ , _ = B-PE-injectivity BΣ! BΣ! ΣF₁G₁≡ΣF′G′
        ΣFG≡ΣF₁G₁ = PE.subst (λ x → Γ ⊢ Σʷ p′ , q ▷ F ▹ G ≡ x)
                             (PE.sym ΣF₁G₁≡ΣF′G′) (≅-eq A≡B)
        p~r₁ = ~-conv p~r ΣFG≡ΣF₁G₁
    in  Σₜ₌ p r (conv* d ΣFG≡ΣF₁G₁) (conv* d′ ΣFG≡ΣF₁G₁)
          (ne x) (ne y) (≅-conv p≅r ΣFG≡ΣF₁G₁) (inc , p~r₁)
  convEqTermT₁
    (Bᵥ BΣʷ record{} _) _ (Σₜ₌ _ _ _ _ prodₙ (ne _) _ (lift ()))
  convEqTermT₁
    (Bᵥ BΣʷ record{} _) _ (Σₜ₌ _ _ _ _ (ne _) prodₙ _ (lift ()))
  convEqTermT₁
    (Uᵥ (Uᵣ k [k] k< D1) (Uᵣ k′ [k′] k′< D2)) (U₌ _ D k≡k′)
    (Uₜ₌ A B d d′ typeA typeB A≡B [t] [u] [t≡u])
    with whrDet* (D2 , Uₙ) (D , Uₙ)
  ... | PE.refl =
    let Uk≡Uk′ = ≅-eq (≅-U-cong (wf (redFirst* D)) (escapeLevelEq k≡k′))
        ↑k≡↑k′ = ↑ᵘ-cong k≡k′
    in Uₜ₌ A B (conv* d Uk≡Uk′) (conv* d′ Uk≡Uk′) typeA typeB (≅-conv A≡B Uk≡Uk′)
      (irrelevance-⊩< ↑k≡↑k′ k< k′< [t])
      (irrelevance-⊩< ↑k≡↑k′ k< k′< [u])
      (irrelevance-⊩<≡ ↑k≡↑k′ k< k′< [t≡u])
  convEqTermT₁
    (Idᵥ ⊩A ⊩B@record{}) A≡B t≡u@(_ , _ , t⇒*t′ , u⇒*u′ , _) =
    case whrDet* (_⊩ₗId_.⇒*Id ⊩B , Idₙ) (⇒*Id′ , Idₙ) of λ {
      PE.refl →
    case ≅-eq (Id≅Id A≡B) of λ {
      Id≡Id′ →
      _ , _
    , conv* t⇒*t′ Id≡Id′
    , conv* u⇒*u′ Id≡Id′
    , (case ⊩Id≡∷-view-inhabited ⊩A t≡u of λ where
         (ne inc t′-n u′-n t′~u′) →
           ne t′-n , ne u′-n , inc , ~-conv t′~u′ Id≡Id′
         (rfl₌ lhs≡rhs) →
             rflₙ , rflₙ
           , convEqTerm₁ (_⊩ₗId_.⊩Ty ⊩A) (_⊩ₗId_.⊩Ty ⊩B) Ty≡Ty′
               (lhs≡rhs→lhs′≡rhs′ lhs≡rhs)) }}
    where
    open _⊩ₗId_≡_/_ A≡B

  -- Helper function for conversion of term equality converting from right to left.
  convEqTermT₂ : ∀ {l l′ A B t u} {[A] : Γ ⊩⟨ l ⟩ A} {[B] : Γ ⊩⟨ l′ ⟩ B}
             → ShapeView Γ l l′ A B [A] [B]
             → Γ ⊩⟨ l ⟩  A ≡ B / [A]
             → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ B / [B]
             → Γ ⊩⟨ l ⟩  t ≡ u ∷ A / [A]
  convEqTermT₂ (Levelᵥ D D′) A≡B t≡u = t≡u
  convEqTermT₂
    (Liftᵥ (Liftᵣ D _ [F]) (Liftᵣ D′ _ [F′]))
    (Lift₌ D″ k≡k′ F≡F′)
    (Liftₜ₌ _ _ t↘ u↘ t≡u)
    = case whrDet* (D″ , Liftₙ) (D′ , Liftₙ) of λ {
      PE.refl →
    let Lift≡Lift = sym (≅-eq (≅-Lift-cong (escapeLevelEq k≡k′) (escapeEq [F] F≡F′)))
    in Liftₜ₌ _ _ (conv↘∷ t↘ Lift≡Lift) (conv↘∷ u↘ Lift≡Lift)
        (convEqTerm₂ [F] [F′] F≡F′ t≡u) }
  convEqTermT₂ (ℕᵥ D D′) A≡B t≡u = t≡u
  convEqTermT₂ (Emptyᵥ D D′) A≡B t≡u = t≡u
  convEqTermT₂ (Unitᵥ _ _) _ t≡u = t≡u
  convEqTermT₂
    (ne (ne _ _ D neK K≡K) (ne _ K₁ D₁ neK₁ K≡K₁)) (ne₌ _ M D′ neM K≡M)
    (neₜ₌ k m d d′ (neNfₜ₌ inc neK₂ neM₁ k≡m)) =
    let K₁≡K = PE.subst (λ x → _ ⊢ x ≡ _)
                        (whrDet* (D′ , ne! neM) (D₁ , ne! neK₁))
                        (sym (≅-eq K≡M))
    in  neₜ₌ k m (conv* d K₁≡K) (conv* d′ K₁≡K)
          (neNfₜ₌ inc neK₂ neM₁ (~-conv k≡m K₁≡K))
  convEqTermT₂
    {Γ = Γ}
    (Bᵥ (BΠ p q) (Bᵣ F G D A≡A [F] [G] G-ext ok)
       (Bᵣ F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁))
    (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
    (Πₜ₌ f g d d′ funcF funcG t≡u [t≡u]) =
    let ΠF₁G₁≡ΠF′G′ = whrDet* (D₁ , ΠΣₙ) (D′ , ΠΣₙ)
        ΠFG≡ΠF₁G₁ = PE.subst (λ x → Γ ⊢ Π p , q ▷ F ▹ G ≡ x)
                             (PE.sym ΠF₁G₁≡ΠF′G′) (≅-eq A≡B)
    in  Πₜ₌ f g (conv* d (sym ΠFG≡ΠF₁G₁)) (conv* d′ (sym ΠFG≡ΠF₁G₁))
            funcF funcG (≅-conv t≡u (sym ΠFG≡ΠF₁G₁))
            (λ {_} {ρ} [ρ] ⊩v ⊩w v≡w →
               let F₁≡F′ , G₁≡G′ , _ =
                     B-PE-injectivity BΠ! BΠ!
                       (whrDet* (D₁ , ΠΣₙ) (D′ , ΠΣₙ))
                   [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                              ([F] [ρ]) ([F≡F′] [ρ])
                   ⊩v′ = convTerm₁ ([F] [ρ]) ([F]₁ [ρ]) [F≡F₁] ⊩v
                   [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ]₀)
                                                     (PE.sym G₁≡G′))
                              ([G] [ρ] ⊩v) ([G≡G′] [ρ] ⊩v)
               in  convEqTerm₂ ([G] [ρ] ⊩v) ([G]₁ [ρ] ⊩v′) [G≡G₁]
                     ([t≡u] [ρ] ⊩v′
                        (convTerm₁ ([F] [ρ]) ([F]₁ [ρ]) [F≡F₁] ⊩w)
                        (convEqTerm₁ ([F] [ρ]) ([F]₁ [ρ]) [F≡F₁] v≡w)))
  convEqTermT₂
    {Γ = Γ}
    (Bᵥ (BΣ 𝕤 p′ q) (Bᵣ F G D A≡A [F] [G] G-ext ok)
       (Bᵣ F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁))
    (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
    (Σₜ₌ p r d d′ pProd rProd t≡u
       ([p₁]₁ , [r₁]₁ , [fst≡]₁ , [snd≡]₁)) =
    let ΣF₁G₁≡ΣF′G′       = whrDet* (D₁ , ΠΣₙ) (D′ , ΠΣₙ)
        F₁≡F′ , G₁≡G′ , _ = B-PE-injectivity BΣ! BΣ! ΣF₁G₁≡ΣF′G′
        ΣFG≡ΣF₁G₁ = PE.subst (λ x → Γ ⊢ Σˢ p′ , q ▷ F ▹ G ≡ x)
                             (PE.sym ΣF₁G₁≡ΣF′G′) (≅-eq A≡B)
        F≡F₁ = PE.subst (λ x → Γ ⊩⟨ _ ⟩ wk id F ≡ wk id x / [F] _)
                 (PE.sym F₁≡F′) ([F≡F′] _)
        [p₁] = convTerm₂ ([F] _) ([F]₁ _) F≡F₁ [p₁]₁
        [r₁] = convTerm₂ ([F] _) ([F]₁ _) F≡F₁ [r₁]₁
        [fst≡] = convEqTerm₂ ([F] _) ([F]₁ _) F≡F₁ [fst≡]₁
        G≡G₁ = PE.subst
                 (λ x →
                    Γ ⊩⟨ _ ⟩ wk (lift id) G [ _ ]₀ ≡
                      wk (lift id) x [ _ ]₀ / [G] _ [p₁])
                 (PE.sym G₁≡G′) ([G≡G′] _ [p₁])
        [snd≡] = convEqTerm₂ ([G] _ [p₁]) ([G]₁ _ [p₁]₁) G≡G₁ [snd≡]₁
    in  Σₜ₌ p r (conv* d (sym ΣFG≡ΣF₁G₁)) (conv* d′ (sym ΣFG≡ΣF₁G₁))
            pProd rProd (≅-conv t≡u (sym ΣFG≡ΣF₁G₁))
            ([p₁] , [r₁] , [fst≡] , [snd≡])
  convEqTermT₂
    {Γ = Γ}
    (Bᵥ (BΣ 𝕨 p′ q) (Bᵣ F G D A≡A [F] [G] G-ext ok)
       (Bᵣ F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁))
    (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
    (Σₜ₌ p r d d′ (prodₙ {t = p₁}) prodₙ t≡u
       (PE.refl , PE.refl , PE.refl , PE.refl ,
        [p₁]₁ , [r₁]₁ , [fst≡]₁ , [snd≡]₁)) =
    let ΣF₁G₁≡ΣF′G′       = whrDet* (D₁ , ΠΣₙ) (D′ , ΠΣₙ)
        F₁≡F′ , G₁≡G′ , _ = B-PE-injectivity BΣ! BΣ! ΣF₁G₁≡ΣF′G′
        ΣFG≡ΣF₁G₁ = PE.subst (λ x → Γ ⊢ Σʷ p′ , q ▷ F ▹ G ≡ x)
                             (PE.sym ΣF₁G₁≡ΣF′G′) (≅-eq A≡B)
        F≡F₁ = PE.subst (λ x → Γ ⊩⟨ _ ⟩ wk id F ≡ wk id x / [F] _)
                 (PE.sym F₁≡F′) ([F≡F′] _)
        [p₁] = convTerm₂ ([F] _) ([F]₁ _) F≡F₁ [p₁]₁
        [r₁] = convTerm₂ ([F] _) ([F]₁ _) F≡F₁ [r₁]₁
        [fst≡] = convEqTerm₂ ([F] _) ([F]₁ _) F≡F₁ [fst≡]₁
        G≡G₁ = PE.subst
                 (λ x →
                    Γ ⊩⟨ _ ⟩ wk (lift id) G [ p₁ ]₀ ≡
                      wk (lift id) x [ p₁ ]₀ / [G] _ [p₁])
                 (PE.sym G₁≡G′) ([G≡G′] _ [p₁])
        [snd≡] = convEqTerm₂ ([G] _ [p₁]) ([G]₁ _ [p₁]₁) G≡G₁ [snd≡]₁
    in  Σₜ₌ p r (conv* d (sym ΣFG≡ΣF₁G₁)) (conv* d′ (sym ΣFG≡ΣF₁G₁))
            prodₙ prodₙ (≅-conv t≡u (sym ΣFG≡ΣF₁G₁))
            (PE.refl , PE.refl , PE.refl , PE.refl ,
             [p₁] , [r₁] , [fst≡] , [snd≡])
  convEqTermT₂
    {Γ = Γ}
    (Bᵥ (BΣ 𝕨 p′ q) (Bᵣ F G D A≡A [F] [G] G-ext ok)
       (Bᵣ F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁))
    (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
    (Σₜ₌ p r d d′ (ne x) (ne y) t≡u (inc , p~r₁)) =
    let ΣF₁G₁≡ΣF′G′       = whrDet* (D₁ , ΠΣₙ) (D′ , ΠΣₙ)
        F₁≡F′ , G₁≡G′ , _ = B-PE-injectivity BΣ! BΣ! ΣF₁G₁≡ΣF′G′
        ΣFG≡ΣF₁G₁ = PE.subst (λ x → Γ ⊢ Σʷ p′ , q ▷ F ▹ G ≡ x)
                             (PE.sym ΣF₁G₁≡ΣF′G′) (≅-eq A≡B)
        p~r = ~-conv p~r₁ (sym ΣFG≡ΣF₁G₁)
    in  Σₜ₌ p r (conv* d (sym ΣFG≡ΣF₁G₁)) (conv* d′ (sym ΣFG≡ΣF₁G₁))
          (ne x) (ne y) (≅-conv t≡u (sym ΣFG≡ΣF₁G₁)) (inc , p~r)
  convEqTermT₂
    (Bᵥ BΣʷ _ record{}) _ (Σₜ₌ _ _ _ _ prodₙ (ne _) _ (lift ()))
  convEqTermT₂
    (Bᵥ BΣʷ _ record{}) _ (Σₜ₌ _ _ _ _ (ne _) prodₙ _ (lift ()))
  convEqTermT₂
    (Uᵥ (Uᵣ k [k] k< D1) (Uᵣ k′ [k′] k′< D2)) (U₌ _ D k≡k′)
    (Uₜ₌ A B d d′ typeA typeB A≡B [t] [u] [t≡u])
    with whrDet* (D2 , Uₙ) (D , Uₙ)
  ... | PE.refl =
    let Uk≡Uk′ = ≅-eq (≅-U-cong (wf (redFirst* D)) (escapeLevelEq k≡k′))
        ↑k≡↑k′ = ↑ᵘ-cong k≡k′
    in Uₜ₌ A B (conv* d (sym Uk≡Uk′)) (conv* d′ (sym Uk≡Uk′)) typeA typeB (≅-conv A≡B (sym Uk≡Uk′))
      (irrelevance-⊩< (PE.sym ↑k≡↑k′) k′< k< [t])
      (irrelevance-⊩< (PE.sym ↑k≡↑k′) k′< k< [u])
      (irrelevance-⊩<≡ (PE.sym ↑k≡↑k′) k′< k< [t≡u])
  convEqTermT₂
    (Idᵥ ⊩A ⊩B@record{}) A≡B t≡u@(_ , _ , t⇒*t′ , u⇒*u′ , _) =
    case whrDet* (_⊩ₗId_.⇒*Id ⊩B , Idₙ) (⇒*Id′ , Idₙ) of λ {
      PE.refl →
    case ≅-eq (≅-sym (Id≅Id A≡B)) of λ {
      Id≡Id′ →
      _ , _
    , conv* t⇒*t′ Id≡Id′
    , conv* u⇒*u′ Id≡Id′
    , (case ⊩Id≡∷-view-inhabited ⊩B t≡u of λ where
         (ne inc t′-n u′-n t′~u′) →
           ne t′-n , ne u′-n , inc , ~-conv t′~u′ Id≡Id′
         (rfl₌ lhs≡rhs) →
             rflₙ , rflₙ
           , lhs′≡rhs′→lhs≡rhs
               (convEqTerm₂ (_⊩ₗId_.⊩Ty ⊩A) (_⊩ₗId_.⊩Ty ⊩B) Ty≡Ty′
                  lhs≡rhs)) }}
    where
    open _⊩ₗId_≡_/_ A≡B

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
