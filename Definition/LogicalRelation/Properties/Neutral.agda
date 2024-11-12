------------------------------------------------------------------------
-- Neutral terms are in the logical relation (given some assumptions)
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
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
import Definition.Typed.Weakening R as Wk
open import Definition.Typed.Well-formed R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties.Reflexivity R
open import Definition.LogicalRelation.Properties.Escape R
open import Definition.LogicalRelation.Properties.Symmetry R

open import Tools.Function
open import Tools.Nat hiding (_<_)
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Sum as ⊎

private
  variable
    m : Nat
    Γ : Con Term m
    A B n n′ : Term _
    l : Universe-level

opaque

  -- Neutral reflexive types are reducible.

  neu : Neutral A → Γ ⊢≅ A → Γ ⊩⟨ l ⟩ A
  neu neA ≅A = ne′ _ (idRed:*: (wf-⊢≡ (≅-eq ≅A) .proj₁)) neA ≅A

opaque

  -- Neutrally equal types are of reducible equality.

  neuEq :
    (⊩A : Γ ⊩⟨ l ⟩ A) → Neutral A → Neutral B → Γ ⊢ A ≅ B →
    Γ ⊩⟨ l ⟩ A ≡ B / ⊩A
  neuEq {Γ} {A} {B} [A] neA neB A~B =
    irrelevanceEq (ne-intr (ne-elim neA [A])) [A]
      (neuEq′ (ne-elim neA [A]))
    where
    neuEq′ :
      (⊩A : Γ ⊩⟨ l ⟩ne A) →
      Γ ⊩⟨ l ⟩ A ≡ B / ne-intr ⊩A
    neuEq′ (noemb (ne _ [ ⊢A , ⊢B , D ] neK K≡K)) =
      let A≡K = whnfRed* D (ne neA) in
      ne₌ _ (idRed:*: (wf-⊢≡ (≅-eq A~B) .proj₂)) neB
        (PE.subst (λ x → _ ⊢ x ≅ _) A≡K A~B)
    neuEq′ (emb ≤ᵘ-refl x) = neuEq′ x
    neuEq′ (emb (≤ᵘ-step p) x) = neuEq′ (emb p x)

opaque mutual

  -- Neutral reflexive terms are reducible.

  neuTerm :
    (⊩A : Γ ⊩⟨ l ⟩ A) → Neutral n → Γ ⊢~ n ∷ A →
    Γ ⊩⟨ l ⟩ n ∷ A / ⊩A
  neuTerm {Γ} {A} {n} ⊩A n-ne ~n = neuTerm′ ⊩A
    where
    ⊢n : Γ ⊢ n ∷ A
    ⊢n = wf-⊢≡∷ (≅ₜ-eq (~-to-≅ₜ ~n)) .proj₂ .proj₁

    neuTerm′ : (⊩A : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ n ∷ A / ⊩A
    neuTerm′ (Uᵣ′ l ≤ᵘ-refl [ ⊢A , ⊢B , D ]) =
      let A≡U  = subset* D
          n≡n  = ~-to-≅ₜ (~-conv ~n A≡U)
      in Uₜ _ (idRedTerm:*: (conv ⊢n A≡U)) (ne n-ne) n≡n
        (neu n-ne (~-to-≅ (~-conv ~n A≡U)))
    neuTerm′ (Uᵣ′ _ (≤ᵘ-step p) A⇒*U) =
      irrelevanceTerm (Uᵣ′ _ p A⇒*U) (Uᵣ′ _ (≤ᵘ-step p) A⇒*U)
        (neuTerm (Uᵣ′ _ p A⇒*U) n-ne ~n)
    neuTerm′ (ℕᵣ [ ⊢A , ⊢B , D ]) =
      let A≡ℕ  = subset* D
          n~n′ = ~-conv ~n A≡ℕ
          n≡n  = ~-to-≅ₜ n~n′
      in
      ℕₜ _ (idRedTerm:*: (conv ⊢n A≡ℕ)) n≡n (ne (neNfₜ n-ne n~n′))
    neuTerm′ (Emptyᵣ [ ⊢A , ⊢B , D ]) =
      let A≡Empty  = subset* D
          n~n′ = ~-conv ~n A≡Empty
          n≡n  = ~-to-≅ₜ n~n′
      in
      Emptyₜ _ (idRedTerm:*: (conv ⊢n A≡Empty)) n≡n
        (ne (neNfₜ n-ne n~n′))
    neuTerm′ (Unitᵣ (Unitₜ [ ⊢A , ⊢B , D ] _)) =
      let A≡Unit  = subset* D
          n~n′ = ~-conv ~n A≡Unit
          n≡n′ = ~-to-≅ₜ n~n′
      in
      Unitₜ _ (idRedTerm:*: (conv ⊢n A≡Unit)) n≡n′
        (ne (neNfₜ n-ne n~n′))
    neuTerm′ (ne′ _ [ ⊢A , ⊢B , D ] neK K≡K) =
      let A≡K = subset* D in
      neₜ _ (idRedTerm:*: (conv ⊢n A≡K)) (neNfₜ n-ne (~-conv ~n A≡K))
    neuTerm′ (Πᵣ′ F G D A≡A [F] [G] _ ok) =
      let A≡ΠFG = subset* (red D) in
      Πₜ _ (idRedTerm:*: (conv ⊢n A≡ΠFG)) (ne n-ne)
        (~-to-≅ₜ (~-conv ~n A≡ΠFG))
        (λ {_} {ρ = ρ} [ρ] [a] [b] [a≡b] →
           let a≡b = escapeTermEq ([F] [ρ]) [a≡b]
               neN∘a = ∘ₙ (wkNeutral ρ n-ne)
               neN∘b = ∘ₙ (wkNeutral ρ n-ne)
           in  neuEqTerm ([G] [ρ] [a]) neN∘a neN∘b
                  (~-app (~-wk [ρ] (~-conv ~n A≡ΠFG)) a≡b))

        (λ {_} {ρ = ρ} [ρ] [a] →
           let a≡a = escapeTermEq ([F] [ρ])
                       (reflEqTerm ([F] [ρ]) [a])
            in  neuTerm ([G] [ρ] [a]) (∘ₙ (wkNeutral ρ n-ne))
                  (~-app (~-wk [ρ] (~-conv ~n A≡ΠFG)) a≡a))
    neuTerm′ (Bᵣ′ (BΣ 𝕤 _ q) F G D A≡A [F] [G] G-ext _) =
      let A≡ΣFG = subset* (red D)
          ⊢n = conv ⊢n A≡ΣFG
          ~n = ~-conv ~n A≡ΣFG

          [F] = [F] _
          _ , ⊢G , _ = inversion-ΠΣ (wf-⊢≡ (≅-eq A≡A) .proj₁)
          [fst] = neuTerm [F] (fstₙ n-ne)
                    (PE.subst (_⊢_~_∷_ _ _ _) (PE.sym (wk-id F))
                       (~-fst ⊢G ~n))
          [Gfst] = [G] _ [fst]
          [snd] = neuTerm [Gfst] (sndₙ n-ne)
                    (PE.subst (_⊢_~_∷_ _ _ _)
                       (PE.cong (λ x → x [ fst _ _ ]₀)
                          (PE.sym (wk-lift-id G)))
                       (~-snd ⊢G ~n))
      in
      Σₜ _ (idRedTerm:*: ⊢n) (~-to-≅ₜ ~n) (ne n-ne) ([fst] , [snd])
    neuTerm′ (Bᵣ′ (BΣ 𝕨 _ q) F G D A≡A [F] [G] G-ext _) =
      let A≡ΣFG = subset* (red D)
          ⊢Γ = wfEq A≡ΣFG
          ⊢n = conv ⊢n A≡ΣFG
          ~n = ~-conv ~n A≡ΣFG
      in
      Σₜ _ (idRedTerm:*: ⊢n) (~-to-≅ₜ ~n) (ne n-ne) ~n
    neuTerm′ (Idᵣ ⊩A) =
      case subset* (red ⇒*Id) of λ {
        A≡Id →
        _
      , idRedTerm:*: (conv ⊢n A≡Id)
      , ne n-ne
      , ~-conv ~n A≡Id }
      where
      open _⊩ₗId_ ⊩A
    neuTerm′ (emb ≤ᵘ-refl x) = neuTerm′ x
    neuTerm′ (emb (≤ᵘ-step l<) x) = neuTerm′ (emb l< x)

  -- Neutrally equal terms are of reducible equality.

  neuEqTerm :
    (⊩A : Γ ⊩⟨ l ⟩ A) → Neutral n → Neutral n′ → Γ ⊢ n ~ n′ ∷ A →
    Γ ⊩⟨ l ⟩ n ≡ n′ ∷ A / ⊩A
  neuEqTerm {Γ} {A} {n} {n′} ⊩A n-ne n′-ne n~n′ = neuEqTerm′ ⊩A
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
    neuEqTerm′ (Uᵣ′ l ≤ᵘ-refl [ ⊢A , ⊢B , D ]) =
      let A≡U = subset* D
          n~n′₁ = ~-conv n~n′ A≡U
          n≡n′ = ~-to-≅ₜ n~n′₁
          wfn = neu n-ne (~-to-≅ (~-trans n~n′₁ (~-sym n~n′₁)))
      in
      Uₜ₌ _ _ (idRedTerm:*: (conv ⊢n A≡U)) (idRedTerm:*: (conv ⊢n′ A≡U))
        (ne n-ne) (ne n′-ne) n≡n′ wfn
        (neu n′-ne (~-to-≅ (~-trans (~-sym n~n′₁) n~n′₁)))
        (neuEq wfn n-ne n′-ne (≅-univ n≡n′))
    neuEqTerm′ (Uᵣ′ _ (≤ᵘ-step p) A⇒*U) =
      irrelevanceEqTerm (Uᵣ′ _ p A⇒*U) (Uᵣ′ _ (≤ᵘ-step p) A⇒*U)
        (neuEqTerm (Uᵣ′ _ p A⇒*U) n-ne n′-ne n~n′)
    neuEqTerm′ (ℕᵣ [ ⊢A , ⊢B , D ]) =
      let A≡ℕ = subset* D
          n~n′₁ = ~-conv n~n′ A≡ℕ
          n≡n′ = ~-to-≅ₜ n~n′₁
      in
      ℕₜ₌ _ _ (idRedTerm:*: (conv ⊢n A≡ℕ)) (idRedTerm:*: (conv ⊢n′ A≡ℕ))
        n≡n′ (ne (neNfₜ₌ n-ne n′-ne n~n′₁))
    neuEqTerm′ (Emptyᵣ [ ⊢A , ⊢B , D ]) =
      let A≡Empty = subset* D
          n~n′₁ = ~-conv n~n′ A≡Empty
          n≡n′ = ~-to-≅ₜ n~n′₁
      in
      Emptyₜ₌ _ _ (idRedTerm:*: (conv ⊢n A≡Empty))
        (idRedTerm:*: (conv ⊢n′ A≡Empty)) n≡n′
        (ne (neNfₜ₌ n-ne n′-ne n~n′₁))
    neuEqTerm′ (Unitᵣ {s} (Unitₜ [ ⊢A , ⊢B , D ] _)) =
      let A≡Unit = subset* D
          n~n′₁ = ~-conv n~n′ A≡Unit
          n≡n′ = ~-to-≅ₜ n~n′₁
      in
      case Unit-with-η? s of
        ⊎.[ Unitₜ₌ˢ (conv ⊢n A≡Unit) (conv ⊢n′ A≡Unit)
          , (λ where
               (PE.refl , no-η) →
                 Unitₜ₌ʷ _ _ (idRedTerm:*: (conv ⊢n A≡Unit))
                   (idRedTerm:*: (conv ⊢n′ A≡Unit)) n≡n′
                   (ne (neNfₜ₌ n-ne n′-ne n~n′₁)) no-η)
          ]
    neuEqTerm′ (ne (ne _ [ ⊢A , ⊢B , D ] neK K≡K)) =
      let A≡K = subset* D in
      neₜ₌ _ _ (idRedTerm:*: (conv ⊢n A≡K))
        (idRedTerm:*: (conv ⊢n′ A≡K))
        (neNfₜ₌ n-ne n′-ne (~-conv n~n′ A≡K))
    neuEqTerm′
      [ΠFG]@(Πᵣ′ F G [ ⊢A , ⊢B , D ] A≡A [F] [G] G-ext ok) =
      let A≡ΠFG = subset* D
          n~n′₁ = ~-conv n~n′ A≡ΠFG
          n≡n′ = ~-to-≅ₜ n~n′₁
          n~n = ~-trans n~n′ (~-sym n~n′)
          n′~n′ = ~-trans (~-sym n~n′) n~n′
      in
      Πₜ₌ _ _ (idRedTerm:*: (conv ⊢n A≡ΠFG))
        (idRedTerm:*: (conv ⊢n′ A≡ΠFG))
        (ne n-ne) (ne n′-ne) n≡n′
        (neuTerm [ΠFG] n-ne n~n) (neuTerm [ΠFG] n′-ne n′~n′)
        (λ {_} {ρ = ρ} [ρ] [a] →
           let a≡a = escapeTermEq ([F] [ρ])
                       (reflEqTerm ([F] [ρ]) [a])
               neN∙a   = ∘ₙ (wkNeutral ρ n-ne)
               neN′∙a′ = ∘ₙ (wkNeutral ρ n′-ne)

           in
           neuEqTerm ([G] [ρ] [a]) neN∙a neN′∙a′
             (~-app (~-wk [ρ] n~n′₁) a≡a))
    neuEqTerm′
      [ΣFG]@(Bᵣ′ BΣˢ F G [ ⊢A , ⊢B , D ] A≡A [F] [G] G-ext _) =
      let A≡ΣFG = subset* D
          n~n = ~-trans n~n′ (~-sym n~n′)
          n′~n′ = ~-trans (~-sym n~n′) n~n′
          ⊢nΣ = conv ⊢n A≡ΣFG
          ⊢n′Σ = conv ⊢n′ A≡ΣFG
          n~n′Σ = ~-conv n~n′ A≡ΣFG
          n~nΣ = ~-conv n~n A≡ΣFG
          n′~n′Σ = ~-conv n′~n′ A≡ΣFG

          [F] = [F] _
          _ , ⊢G , _ = inversion-ΠΣ (wf-⊢≡ (≅-eq A≡A) .proj₁)
          [fstn] = neuTerm [F] (fstₙ n-ne)
                     (PE.subst (_⊢_~_∷_ _ _ _) (PE.sym (wk-id F))
                        (~-fst ⊢G n~nΣ))
          [fstn′] = neuTerm [F] (fstₙ n′-ne)
                      (PE.subst (_⊢_~_∷_ _ _ _) (PE.sym (wk-id F))
                         (~-fst ⊢G n′~n′Σ))
          [fstn≡fstn′] = neuEqTerm [F] (fstₙ n-ne) (fstₙ n′-ne)
                           (PE.subst
                             (λ x → _ ⊢ _ ~ _ ∷ x)
                             (PE.sym (wk-id F))
                             (~-fst ⊢G n~n′Σ))
          [Gfstn] = [G] _ [fstn]
          [sndn≡sndn′] = neuEqTerm [Gfstn] (sndₙ n-ne) (sndₙ n′-ne)
            (PE.subst
               (λ x → _ ⊢ _ ~ _ ∷ x)
               (PE.cong (λ x → x [ fst _ _ ]₀) (PE.sym (wk-lift-id G)))
               (~-snd ⊢G n~n′Σ))
      in
      Σₜ₌ _ _ (idRedTerm:*: ⊢nΣ) (idRedTerm:*: ⊢n′Σ)
        (ne n-ne) (ne n′-ne) (~-to-≅ₜ n~n′Σ)
        (neuTerm [ΣFG] n-ne n~n) (neuTerm [ΣFG] n′-ne n′~n′)
        ([fstn] , [fstn′] , [fstn≡fstn′] , [sndn≡sndn′])
    neuEqTerm′
      [ΣFG]@(Bᵣ′ BΣʷ F G [ ⊢A , ⊢B , D ] A≡A [F] [G] G-ext _) =
      let A≡ΣFG = subset* D
          n~n = ~-trans n~n′ (~-sym n~n′)
          n′~n′ = ~-trans (~-sym n~n′) n~n′
          ⊢nΣ = conv ⊢n A≡ΣFG
          ⊢n′Σ = conv ⊢n′ A≡ΣFG
          n~n′Σ = ~-conv n~n′ A≡ΣFG
          n~nΣ = ~-conv n~n A≡ΣFG
          n′~n′Σ = ~-conv n′~n′ A≡ΣFG
      in
      Σₜ₌ _ _ (idRedTerm:*: ⊢nΣ) (idRedTerm:*: ⊢n′Σ)
        (ne n-ne) (ne n′-ne) (~-to-≅ₜ n~n′Σ)
        (neuTerm [ΣFG] n-ne n~n) (neuTerm [ΣFG] n′-ne n′~n′) n~n′Σ
    neuEqTerm′ (Idᵣ ⊩A) =
      case subset* (red ⇒*Id) of λ
        A≡Id →
      case ~-trans n~n′ (~-sym n~n′) of λ
        n~n →
      case ~-trans (~-sym n~n′) n~n′ of λ
        n′~n′ →
      ⊩Id≡∷
        (neuTerm (Idᵣ ⊩A) n-ne n~n)
        (neuTerm (Idᵣ ⊩A) n′-ne n′~n′)
        (~-conv n~n′ A≡Id)
      where
      open _⊩ₗId_ ⊩A
    neuEqTerm′ (emb ≤ᵘ-refl     ⊩A) = neuEqTerm′ ⊩A
    neuEqTerm′ (emb (≤ᵘ-step p) ⊩A) = neuEqTerm′ (emb p ⊩A)
