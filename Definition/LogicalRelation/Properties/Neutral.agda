------------------------------------------------------------------------
-- Atomic neutral terms are in the logical relation (given some assumptions)
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Properties.Neutral
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped M hiding (Wk; K)
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Neutral.Atomic M type-variant
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
import Definition.Typed.Weakening R as Wk
open import Definition.Typed.Well-formed R
open import Definition.LogicalRelation R ⦃ eqrel ⦄
open import Definition.LogicalRelation.ShapeView R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties.Kit R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Properties.Reflexivity R
open import Definition.LogicalRelation.Properties.Escape R
open import Definition.LogicalRelation.Unary R
open import Definition.LogicalRelation.Weakening.Restricted R

open import Tools.Function
open import Tools.Nat hiding (_<_)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Sum

private
  variable
    m : Nat
    Γ : Con Term m
    A B n n′ : Term _
    l : Universe-level

opaque

  -- Neutral reflexive types are reducible (if Neutrals-included
  -- holds).

  neu : Neutrals-included → Neutral A → Γ ⊢≅ A → Γ ⊩⟨ l ⟩ A
  neu inc neA ≅A = ne′ inc _ (id (wf-⊢≡ (≅-eq ≅A) .proj₁)) neA ≅A

opaque

  -- Equal neutral types are reducibly equal.

  neuEq :
    (⊩A : Γ ⊩⟨ l ⟩ A) → Neutral A → Neutral B → Γ ⊢ A ≅ B →
    Γ ⊩⟨ l ⟩ A ≡ B / ⊩A
  neuEq {Γ} {A} {B} [A] neA neB A~B =
    case ne-view neA [A] of λ {
      (ne [A]′@(ne inc _ D neK K≡K)) →
    let A≡K = whnfRed* D (ne neA) in
    ne₌ inc _ (id (wf-⊢≡ (≅-eq A~B) .proj₂)) neB
      (PE.subst (λ x → _ ⊢ x ≅ _) A≡K A~B) }

opaque
 unfolding ⊩Id∷⇔⊩Id≡∷
 mutual

  -- Atomic neutral reflexive terms are reducible (if Neutrals-included
  -- holds).

  neuTerm :
    Neutrals-included → (⊩A : Γ ⊩⟨ l ⟩ A) → Neutralᵃ n → Γ ⊢~ n ∷ A →
    Γ ⊩⟨ l ⟩ n ∷ A / ⊩A
  neuTerm {Γ} {A} {n} inc ⊩A n-ne ~n = neuTerm′ ⊩A
    where
    ⊢n : Γ ⊢ n ∷ A
    ⊢n = wf-⊢≡∷ (≅ₜ-eq (~-to-≅ₜ ~n)) .proj₂ .proj₁

    neuTerm′ : (⊩A : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ n ∷ A / ⊩A
    neuTerm′ (Levelᵣ D) =
      let A≡Level  = subset* D
          n~n′ = ~-conv ~n A≡Level
      in
      term (id (conv ⊢n A≡Level)) (id (conv ⊢n A≡Level))
        (neLvl (ne (neNfₜ₌ inc n-ne n-ne n~n′)))
    neuTerm′ (Liftᵣ′ D [k] [F]) =
      let A≡Lift = subset* D
      in Liftₜ₌ _ _
        (id (conv ⊢n A≡Lift) , ne! n-ne)
        (id (conv ⊢n A≡Lift) , ne! n-ne)
        (neuEqTerm inc [F] (lowerₙᵃ n-ne) (lowerₙᵃ n-ne)
           (~-lower (~-conv ~n A≡Lift)))
    neuTerm′ (Uᵣ′ _ [k] k< D) =
      let A≡U  = subset* D
          n≡n  = ~-to-≅ₜ (~-conv ~n A≡U)
      in
      ⊩U∷U⇔⊩U≡∷U .proj₁
        (Uₜ _ (id (conv ⊢n A≡U)) (ne (ne⁻ n-ne)) n≡n
          (⊩<⇔⊩ k< .proj₂ (neu inc (ne⁻ n-ne) (≅-univ n≡n))))
    neuTerm′ (ℕᵣ D) =
      let A≡ℕ  = subset* D
          n~n′ = ~-conv ~n A≡ℕ
          n≡n  = ~-to-≅ₜ n~n′
      in
      ⊩ℕ∷ℕ⇔⊩ℕ≡∷ℕ .proj₁
        (ℕₜ _ (id (conv ⊢n A≡ℕ)) n≡n (ne (neNfₜ inc n-ne n~n′)))
    neuTerm′ (Emptyᵣ D) =
      let A≡Empty  = subset* D
          n~n′ = ~-conv ~n A≡Empty
          n≡n  = ~-to-≅ₜ n~n′
      in
      ⊩Empty∷Empty⇔⊩Empty≡∷Empty .proj₁
        (Emptyₜ _ (id (conv ⊢n A≡Empty)) n≡n (ne (neNfₜ inc n-ne n~n′)))
    neuTerm′ (Unitᵣ′ D _) =
      let A≡Unit  = subset* D
          n~n′ = ~-conv ~n A≡Unit
      in
      ⊩Unit∷Unit⇔⊩Unit≡∷Unit .proj₁
        (Unitₜ _ (id (conv ⊢n A≡Unit) , ne! n-ne)
           (Unit-prop′→Unit-prop (ne (neNfₜ inc n-ne n~n′))))
    neuTerm′ (ne′ _ _ D neK K≡K) =
      let A≡K = subset* D in
      ⊩ne∷⇔⊩ne≡∷ .proj₁
        (neₜ _ (id (conv ⊢n A≡K)) (neNfₜ inc n-ne (~-conv ~n A≡K)))
    neuTerm′ (Bᵣ BΠ! ⊩A@(Bᵣ F G D A≡A [F] [G] _ ok)) =
      let A≡ΠFG = subset* D in
      ⊩Π∷⇔⊩Π≡∷ ⊩A .proj₁
        (Πₜ _ (id (conv ⊢n A≡ΠFG)) (ne n-ne)
           (~-to-≅ₜ (~-conv ~n A≡ΠFG))
           (λ {_} {ρ = ρ} [ρ] ⊩v ⊩w v≡w →
              neuEqTerm inc ([G] [ρ] ⊩v) (∘ₙᵃ (wkNeutralᵃ n-ne))
                (∘ₙᵃ (wkNeutralᵃ n-ne))
                (~-app (~-wk (∷ʷʳ⊇→∷ʷ⊇ [ρ]) (~-conv ~n A≡ΠFG))
                   (escapeTermEq ([F] [ρ]) v≡w))))
    neuTerm′ (Bᵣ (BΣ 𝕤 _ q) ⊩A@(Bᵣ F G D A≡A [F] [G] G-ext _)) =
      let A≡ΣFG = subset* D
          ⊢n = conv ⊢n A≡ΣFG
          ~n = ~-conv ~n A≡ΣFG

          [F] = [F] _
          _ , ⊢G , _ = inversion-ΠΣ (wf-⊢≡ (≅-eq A≡A) .proj₁)
          [fst] = neuTerm inc [F] (fstₙᵃ n-ne)
                    (PE.subst (_⊢_~_∷_ _ _ _) (PE.sym (wk-id F))
                       (~-fst ⊢G ~n))
          [Gfst] = [G] _ [fst]
          [snd] = neuTerm inc [Gfst] (sndₙᵃ n-ne)
                    (PE.subst (_⊢_~_∷_ _ _ _)
                       (PE.cong (λ x → x [ fst _ _ ]₀)
                          (PE.sym (wk-lift-id G)))
                       (~-snd ⊢G ~n))
      in
      ⊩Σ∷⇔⊩Σ≡∷ ⊩A .proj₁
        (Σₜ _ (id ⊢n) (ne n-ne) (~-to-≅ₜ ~n) (𝕤 _ [fst] [snd]))
    neuTerm′ (Bᵣ (BΣ 𝕨 _ q) ⊩A@(Bᵣ F G D A≡A [F] [G] G-ext _)) =
      let A≡ΣFG = subset* D
          ⊢Γ = wfEq A≡ΣFG
          ⊢n = conv ⊢n A≡ΣFG
          ~n = ~-conv ~n A≡ΣFG
      in
      ⊩Σ∷⇔⊩Σ≡∷ ⊩A .proj₁
        (Σₜ _ (id ⊢n) (ne n-ne) (~-to-≅ₜ ~n) (𝕨-ne inc _ ~n))
    neuTerm′ (Idᵣ ⊩A) =
      let A≡Id = subset* ⇒*Id in
      ⊩Id∷⇔⊩Id≡∷ ⊩A .proj₁
        (Idₜ _ (id (conv ⊢n A≡Id)) (ne n-ne)
           (ne inc n-ne (~-conv ~n A≡Id)))
      where
      open _⊩ₗId_ ⊩A

  -- "Neutrally equal" terms are "reducibly equal" (if
  -- Neutrals-included holds).

  neuEqTerm :
    Neutrals-included →
    (⊩A : Γ ⊩⟨ l ⟩ A) →
    Neutralᵃ n → Neutralᵃ n′ →
    Γ ⊢ n ~ n′ ∷ A →
    Γ ⊩⟨ l ⟩ n ≡ n′ ∷ A / ⊩A
  neuEqTerm {Γ} {A} {n} {n′} inc ⊩A n-ne n′-ne n~n′ = neuEqTerm′ ⊩A
    where
    n≡n′ : Γ ⊢ n ≡ n′ ∷ A
    n≡n′ = ≅ₜ-eq (~-to-≅ₜ n~n′)

    ⊢n : Γ ⊢ n ∷ A
    ⊢n = wf-⊢≡∷ n≡n′ .proj₂ .proj₁

    ⊢n′ : Γ ⊢ n′ ∷ A
    ⊢n′ = wf-⊢≡∷ n≡n′ .proj₂ .proj₂

    neuEqTerm′ :
      (⊩A : Γ ⊩⟨ l ⟩ A) →
      Γ ⊩⟨ l ⟩ n ≡ n′ ∷ A / ⊩A
    neuEqTerm′ (Levelᵣ D) =
      let A≡Level = subset* D
          n~n′₁ = ~-conv n~n′ A≡Level
      in
      term (id (conv ⊢n A≡Level)) (id (conv ⊢n′ A≡Level))
        (neLvl (ne (neNfₜ₌ inc n-ne n′-ne n~n′₁)))
    neuEqTerm′ (Liftᵣ′ D [k] [F]) =
      let A≡Lift = subset* D
      in Liftₜ₌ _ _
        (id (conv ⊢n A≡Lift) , ne! n-ne)
        (id (conv ⊢n′ A≡Lift) , ne! n′-ne)
        (neuEqTerm inc [F] (lowerₙᵃ n-ne) (lowerₙᵃ n′-ne)
           (~-lower (~-conv n~n′ A≡Lift)))
    neuEqTerm′ (Uᵣ′ _ [k] k< D) =
      let A≡U = subset* D
          n~n′₁ = ~-conv n~n′ A≡U
          ≅n , ≅n′ = wf-⊢≅ (~-to-≅ n~n′₁)
          n≡n′ = ~-to-≅ₜ n~n′₁
          ⊩n = neu inc (ne⁻ n-ne) ≅n
      in
      Uₜ₌ _ _ (id (conv ⊢n A≡U)) (id (conv ⊢n′ A≡U))
        (ne (ne⁻ n-ne)) (ne (ne⁻ n′-ne)) n≡n′
        (⊩<⇔⊩ k< .proj₂ ⊩n)
        (⊩<⇔⊩ k< .proj₂ (neu inc (ne⁻ n′-ne) ≅n′))
        (⊩<≡⇔⊩≡′ k< .proj₂ $
         neuEq ⊩n (ne⁻ n-ne) (ne⁻ n′-ne) (≅-univ n≡n′))
    neuEqTerm′ (ℕᵣ D) =
      let A≡ℕ = subset* D
          n~n′₁ = ~-conv n~n′ A≡ℕ
          n≡n′ = ~-to-≅ₜ n~n′₁
      in
      ℕₜ₌ _ _ (id (conv ⊢n A≡ℕ)) (id (conv ⊢n′ A≡ℕ))
        n≡n′ (ne (neNfₜ₌ inc n-ne n′-ne n~n′₁))
    neuEqTerm′ (Emptyᵣ D) =
      let A≡Empty = subset* D
          n~n′₁ = ~-conv n~n′ A≡Empty
          n≡n′ = ~-to-≅ₜ n~n′₁
      in
      Emptyₜ₌ _ _ (id (conv ⊢n A≡Empty))
        (id (conv ⊢n′ A≡Empty)) n≡n′
        (ne (neNfₜ₌ inc n-ne n′-ne n~n′₁))
    neuEqTerm′ (Unitᵣ {s} (Unitᵣ D _)) =
      let A≡Unit = subset* D
          n~n′₁ = ~-conv n~n′ A≡Unit
      in
      Unitₜ₌ _ _ (id (conv ⊢n A≡Unit) , ne! n-ne)
        (id (conv ⊢n′ A≡Unit) , ne! n′-ne)
        ([Unit]-prop′→[Unit]-prop (ne (neNfₜ₌ inc n-ne n′-ne n~n′₁)))
    neuEqTerm′ (ne (ne _ _ D neK K≡K)) =
      let A≡K = subset* D in
      neₜ₌ _ _ (id (conv ⊢n A≡K))
        (id (conv ⊢n′ A≡K))
        (neNfₜ₌ inc n-ne n′-ne (~-conv n~n′ A≡K))
    neuEqTerm′ (Πᵣ′ F G D A≡A [F] [G] G-ext ok) =
      let A≡ΠFG = subset* D
          n~n′₁ = ~-conv n~n′ A≡ΠFG
          n≡n′ = ~-to-≅ₜ n~n′₁
      in
      Πₜ₌ _ _ (id (conv ⊢n A≡ΠFG))
        (id (conv ⊢n′ A≡ΠFG))
        (ne n-ne) (ne n′-ne) n≡n′
        (λ {_} {ρ = ρ} [ρ] ⊩v ⊩w v≡w →
           let v≅w     = escapeTermEq ([F] [ρ]) v≡w
               neN∙a   = ∘ₙᵃ (wkNeutralᵃ n-ne)
               neN′∙a′ = ∘ₙᵃ (wkNeutralᵃ n′-ne)

           in
           neuEqTerm inc ([G] [ρ] ⊩v) neN∙a neN′∙a′
             (~-app (~-wk (∷ʷʳ⊇→∷ʷ⊇ [ρ]) n~n′₁) v≅w))
    neuEqTerm′ (Bᵣ′ BΣˢ F G D A≡A [F] [G] G-ext _) =
      let A≡ΣFG = subset* D
          n~n , n′~n′ = wf-⊢~∷ n~n′
          ⊢nΣ = conv ⊢n A≡ΣFG
          ⊢n′Σ = conv ⊢n′ A≡ΣFG
          n~n′Σ = ~-conv n~n′ A≡ΣFG
          n~nΣ = ~-conv n~n A≡ΣFG
          n′~n′Σ = ~-conv n′~n′ A≡ΣFG

          [F] = [F] _
          _ , ⊢G , _ = inversion-ΠΣ (wf-⊢≡ (≅-eq A≡A) .proj₁)
          [fstn] = neuTerm inc [F] (fstₙᵃ n-ne)
                     (PE.subst (_⊢_~_∷_ _ _ _) (PE.sym (wk-id F))
                        (~-fst ⊢G n~nΣ))
          [fstn′] = neuTerm inc [F] (fstₙᵃ n′-ne)
                      (PE.subst (_⊢_~_∷_ _ _ _) (PE.sym (wk-id F))
                         (~-fst ⊢G n′~n′Σ))
          [fstn≡fstn′] = neuEqTerm inc [F] (fstₙᵃ n-ne) (fstₙᵃ n′-ne)
                           (PE.subst
                             (λ x → _ ⊢ _ ~ _ ∷ x)
                             (PE.sym (wk-id F))
                             (~-fst ⊢G n~n′Σ))
          [Gfstn] = [G] _ [fstn]
          [sndn≡sndn′] = neuEqTerm inc [Gfstn] (sndₙᵃ n-ne)
            (sndₙᵃ n′-ne)
            (PE.subst
               (λ x → _ ⊢ _ ~ _ ∷ x)
               (PE.cong (λ x → x [ fst _ _ ]₀) (PE.sym (wk-lift-id G)))
               (~-snd ⊢G n~n′Σ))
      in
      Σₜ₌ _ _ (id ⊢nΣ) (id ⊢n′Σ)
        (ne n-ne) (ne n′-ne) (~-to-≅ₜ n~n′Σ)
        ([fstn] , [fstn′] , [fstn≡fstn′] , [sndn≡sndn′])
    neuEqTerm′ (Bᵣ′ BΣʷ F G D A≡A [F] [G] G-ext _) =
      let A≡ΣFG = subset* D
          ⊢nΣ = conv ⊢n A≡ΣFG
          ⊢n′Σ = conv ⊢n′ A≡ΣFG
          n~n′Σ = ~-conv n~n′ A≡ΣFG
      in
      Σₜ₌ _ _ (id ⊢nΣ) (id ⊢n′Σ) (ne n-ne) (ne n′-ne) (~-to-≅ₜ n~n′Σ)
        (inc , n~n′Σ)
    neuEqTerm′ (Idᵣ ⊩A) =
      case subset* ⇒*Id of λ
        A≡Id →
      case wf-⊢~∷ n~n′ of λ
        (n~n , n′~n′) →
      (⊩Id≡∷ ⊩A
         (neuTerm inc (Idᵣ ⊩A) n-ne n~n)
         (neuTerm inc (Idᵣ ⊩A) n′-ne n′~n′)
         (inc , ~-conv n~n′ A≡Id))
      where
      open _⊩ₗId_ ⊩A
