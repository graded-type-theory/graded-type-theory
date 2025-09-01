------------------------------------------------------------------------
-- Neutral terms are in the logical relation
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Properties.Neutral
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  ⦃ eqrel : EqRelSet R ⦄
  where

open EqRelSet eqrel
open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Untyped.Whnf M type-variant

open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Weakening.Definition R
open import Definition.Typed.Well-formed R

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties.Reflexivity R
open import Definition.LogicalRelation.Properties.Escape R
open import Definition.LogicalRelation.Weakening.Restricted R

open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Sum as ⊎

private
  variable
    l α : Nat
    Γ : Cons _ _
    t t′ A B : Term _

opaque

  neu : Neutralₗ (Γ .defs) A → Γ ⊢≅ A → Γ ⊩⟨ l ⟩ A
  neu neA A≅A = ne′ _ (id (wf-⊢≡ (≅-eq A≅A) .proj₁)) neA A≅A

opaque

  -- Neutral types that are equal are also reducibly equal.

  neuEq :
    (⊩A : Γ ⊩⟨ l ⟩ A) →
    Neutralₗ (Γ .defs) A →
    Neutralₗ (Γ .defs) B →
    Γ ⊢ A ≅ B →
    Γ ⊩⟨ l ⟩ A ≡ B / ⊩A
  neuEq {Γ} {A} {B} [A] neA neB A~B =
    irrelevanceEq (ne-intr (ne-elim neA [A])) [A]
      (neuEq′ (ne-elim neA [A]))
    where
    neuEq′ :
      (⊩A : Γ ⊩⟨ l ⟩ne A) →
      Γ ⊩⟨ l ⟩ A ≡ B / ne-intr ⊩A
    neuEq′ (noemb (ne _ D neK K≡K)) =
      ne₌ _ (id (wf-⊢≡ (≅-eq A~B) .proj₂)) neB
          (PE.subst (λ x → _ ⊢ x ≅ _) (whnfRed* D (ne-whnf neA)) A~B)
    neuEq′ (emb ≤ᵘ-refl x) = neuEq′ x
    neuEq′ (emb (≤ᵘ-step p) x) = neuEq′ (emb p x)

opaque mutual

  -- Neutral reflexive terms are reducible.

  neuTerm :
    (⊩A : Γ ⊩⟨ l ⟩ A) →
    Neutralₗ (Γ .defs) t →
    Γ ⊢~ t ∷ A →
    Γ ⊩⟨ l ⟩ t ∷ A / ⊩A
  neuTerm {Γ} {A} {t} ⊩A t-ne ~t = neuTerm′ ⊩A
    where
    ⊢t : Γ ⊢ t ∷ A
    ⊢t = wf-⊢≡∷ (~-eq ~t) .proj₂ .proj₁

    neuTerm′ : (⊩A : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ t ∷ A / ⊩A
    neuTerm′ (Uᵣ′ l ≤ᵘ-refl D) =
      let A≡U  = subset* D
          t≡t  = ~-to-≅ₜ (~-conv ~t A≡U)
      in Uₜ _ (id (conv ⊢t A≡U)) (ne t-ne) t≡t
        (neu t-ne (~-to-≅ (~-conv ~t A≡U)))
    neuTerm′ (Uᵣ′ _ (≤ᵘ-step p) A⇒*U) =
      irrelevanceTerm (Uᵣ′ _ p A⇒*U) (Uᵣ′ _ (≤ᵘ-step p) A⇒*U)
        (neuTerm (Uᵣ′ _ p A⇒*U) t-ne ~t)
    neuTerm′ (ℕᵣ D) =
      let A≡ℕ  = subset* D
          t~t′ = ~-conv ~t A≡ℕ
          t≡t  = ~-to-≅ₜ t~t′
      in
      ℕₜ _ (id (conv ⊢t A≡ℕ)) t≡t (ne (neNfₜ t-ne t~t′))
    neuTerm′ (Emptyᵣ D) =
      let A≡Empty  = subset* D
          t~t′ = ~-conv ~t A≡Empty
          t≡t  = ~-to-≅ₜ t~t′
      in
      Emptyₜ _ (id (conv ⊢t A≡Empty)) t≡t
        (ne (neNfₜ t-ne t~t′))
    neuTerm′ (Unitᵣ (Unitₜ D _)) =
      let A≡Unit  = subset* D
          t~t′ = ~-conv ~t A≡Unit
          t≡t′ = ~-to-≅ₜ t~t′
      in
      Unitₜ _ (id (conv ⊢t A≡Unit)) t≡t′
        (ne (neNfₜ t-ne t~t′))
    neuTerm′ (ne′ _ D neK K≡K) =
      let A≡K = subset* D in
      neₜ _ (id (conv ⊢t A≡K))
        (neNfₜ t-ne (~-conv ~t A≡K))
    neuTerm′ (Πᵣ′ F G D A≡A [F] [G] _ ok) =
      let A≡ΠFG = subset* D in
      Πₜ _ (id (conv ⊢t A≡ΠFG)) (ne t-ne) (~-to-≅ₜ (~-conv ~t A≡ΠFG))
        (λ [ξ] {_} {ρ} [ρ] [a] [b] [a≡b] →
           let a≡b = escapeTermEq ([F] [ξ] [ρ]) [a≡b]
               neT∘a = ∘ₙ (defn-wkNeutral [ξ] (wkNeutral ρ t-ne))
               neT∘b = ∘ₙ (defn-wkNeutral [ξ] (wkNeutral ρ t-ne))
               ~t∷ = ~-defn-wk [ξ] (~-conv ~t A≡ΠFG)
           in  neuEqTerm ([G] [ξ] [ρ] [a]) neT∘a neT∘b
                 (~-app (~-wk (∷ʷʳ⊇→∷ʷ⊇ [ρ]) ~t∷) a≡b))

        (λ [ξ] {_} {ρ} [ρ] [a] →
           let a≡a = escapeTermEq ([F] [ξ] [ρ])
                       (reflEqTerm ([F] [ξ] [ρ]) [a])
               neT∘a = ∘ₙ (defn-wkNeutral [ξ] (wkNeutral ρ t-ne))
               ~t∷ = ~-defn-wk [ξ] (~-conv ~t A≡ΠFG)
           in  neuTerm ([G] [ξ] [ρ] [a]) neT∘a
                 (~-app (~-wk (∷ʷʳ⊇→∷ʷ⊇ [ρ]) ~t∷) a≡a))
    neuTerm′ (Bᵣ′ (BΣ 𝕤 _ q) F G D A≡A [F] [G] G-ext _) =
      let A≡ΣFG = subset* D
          ⊢t = conv ⊢t A≡ΣFG
          ~t = ~-conv ~t A≡ΣFG

          [F] = [F] _ _
          _ , ⊢G , _ = inversion-ΠΣ (wf-⊢≡ (≅-eq A≡A) .proj₁)
          [fst] = neuTerm [F] (fstₙ t-ne)
                    (PE.subst (_⊢_~_∷_ _ _ _) (PE.sym (wk-id F))
                       (~-fst ⊢G ~t))
          [Gfst] = [G] _ _ [fst]
          [snd] = neuTerm [Gfst] (sndₙ t-ne)
                    (PE.subst (_⊢_~_∷_ _ _ _)
                       (PE.cong (λ x → x [ fst _ _ ]₀)
                          (PE.sym (wk-lift-id G)))
                       (~-snd ⊢G ~t))
      in
      Σₜ _ (id ⊢t) (~-to-≅ₜ ~t) (ne t-ne) ([fst] , [snd])
    neuTerm′ (Bᵣ′ (BΣ 𝕨 _ q) F G D A≡A [F] [G] G-ext _) =
      let A≡ΣFG = subset* D
          ⊢Γ = wfEq A≡ΣFG
          ⊢t = conv ⊢t A≡ΣFG
          ~t = ~-conv ~t A≡ΣFG
      in
      Σₜ _ (id ⊢t) (~-to-≅ₜ ~t) (ne t-ne) ~t
    neuTerm′ (Idᵣ ⊩A) =
      case subset* ⇒*Id of λ {
        A≡Id → _ , id (conv ⊢t A≡Id) , ne t-ne , ~-conv ~t A≡Id }
      where
      open _⊩ₗId_ ⊩A
    neuTerm′ (emb ≤ᵘ-refl x) = neuTerm′ x
    neuTerm′ (emb (≤ᵘ-step l<) x) = neuTerm′ (emb l< x)

  -- "Neutrally equal" neutral terms are "reducibly equal".

  neuEqTerm :
    (⊩A : Γ ⊩⟨ l ⟩ A) →
    Neutralₗ (Γ .defs) t →
    Neutralₗ (Γ .defs) t′ →
    Γ ⊢ t ~ t′ ∷ A →
    Γ ⊩⟨ l ⟩ t ≡ t′ ∷ A / ⊩A
  neuEqTerm {Γ} {A} {t} {t′} ⊩A t-ne t′-ne t~t′ = neuEqTerm′ ⊩A
    where
    t≡t′ : Γ ⊢ t ≡ t′ ∷ A
    t≡t′ = ~-eq t~t′

    ⊢t : Γ ⊢ t ∷ A
    ⊢t = wf-⊢≡∷ t≡t′ .proj₂ .proj₁

    ⊢t′ : Γ ⊢ t′ ∷ A
    ⊢t′ = wf-⊢≡∷ t≡t′ .proj₂ .proj₂

    neuEqTerm′ :
      (⊩A : Γ ⊩⟨ l ⟩ A) →
      Γ ⊩⟨ l ⟩ t ≡ t′ ∷ A / ⊩A
    neuEqTerm′ (Uᵣ′ l ≤ᵘ-refl D) =
      let A≡U = subset* D
          t~t′₁ = ~-conv t~t′ A≡U
          ≅t , ≅t′ = wf-⊢≅ (~-to-≅ t~t′₁)
          t≡t′ = ~-to-≅ₜ t~t′₁
          wfn = neu t-ne ≅t
      in
      Uₜ₌ _ _ (id (conv ⊢t A≡U)) (id (conv ⊢t′ A≡U)) (ne t-ne) (ne t′-ne)
        t≡t′ wfn (neu t′-ne ≅t′) (neuEq wfn t-ne t′-ne (≅-univ t≡t′))
    neuEqTerm′ (Uᵣ′ _ (≤ᵘ-step p) A⇒*U) =
      irrelevanceEqTerm (Uᵣ′ _ p A⇒*U) (Uᵣ′ _ (≤ᵘ-step p) A⇒*U)
        (neuEqTerm (Uᵣ′ _ p A⇒*U) t-ne t′-ne t~t′)
    neuEqTerm′ (ℕᵣ D) =
      let A≡ℕ = subset* D
          t~t′₁ = ~-conv t~t′ A≡ℕ
          t≡t′ = ~-to-≅ₜ t~t′₁
      in
      ℕₜ₌ _ _ (id (conv ⊢t A≡ℕ)) (id (conv ⊢t′ A≡ℕ))
        t≡t′ (ne (neNfₜ₌ t-ne t′-ne t~t′₁))
    neuEqTerm′ (Emptyᵣ D) =
      let A≡Empty = subset* D
          t~t′₁ = ~-conv t~t′ A≡Empty
          t≡t′ = ~-to-≅ₜ t~t′₁
      in
      Emptyₜ₌ _ _ (id (conv ⊢t A≡Empty))
        (id (conv ⊢t′ A≡Empty)) t≡t′
        (ne (neNfₜ₌ t-ne t′-ne t~t′₁))
    neuEqTerm′ (Unitᵣ {s} (Unitₜ D _)) =
      let A≡Unit = subset* D
          t~t′₁ = ~-conv t~t′ A≡Unit
          t≡t′ = ~-to-≅ₜ t~t′₁
      in
      case Unit-with-η? s of
        ⊎.[ Unitₜ₌ˢ (conv ⊢t A≡Unit) (conv ⊢t′ A≡Unit)
          , (λ where
               (PE.refl , no-η) →
                 Unitₜ₌ʷ _ _ (id (conv ⊢t A≡Unit))
                   (id (conv ⊢t′ A≡Unit)) t≡t′
                   (ne (neNfₜ₌ t-ne t′-ne t~t′₁)) no-η)
          ]
    neuEqTerm′ (ne (ne _ D neK K≡K)) =
      let A≡K = subset* D in
      neₜ₌ _ _ (id (conv ⊢t A≡K))
        (id (conv ⊢t′ A≡K))
        (neNfₜ₌ t-ne t′-ne (~-conv t~t′ A≡K))
    neuEqTerm′
      [ΠFG]@(Πᵣ′ F G D A≡A [F] [G] G-ext ok) =
      let A≡ΠFG = subset* D
          t~t′₁ = ~-conv t~t′ A≡ΠFG
          t≡t′ = ~-to-≅ₜ t~t′₁
          t~t , t′~t′ = wf-⊢~∷ t~t′
      in
      Πₜ₌ _ _ (id (conv ⊢t A≡ΠFG))
        (id (conv ⊢t′ A≡ΠFG)) (ne t-ne) (ne t′-ne) t≡t′
        (neuTerm [ΠFG] t-ne t~t) (neuTerm [ΠFG] t′-ne t′~t′)
        (λ [ξ] {_} {ρ} [ρ] [a] →
           let a≡a = escapeTermEq ([F] [ξ] [ρ])
                       (reflEqTerm ([F] [ξ] [ρ]) [a])
               neT∙a   = ∘ₙ (defn-wkNeutral [ξ] (wkNeutral ρ t-ne))
               neT′∙a′ = ∘ₙ (defn-wkNeutral [ξ] (wkNeutral ρ t′-ne))
           in neuEqTerm ([G] [ξ] [ρ] [a]) neT∙a neT′∙a′
                (~-app (~-wk (∷ʷʳ⊇→∷ʷ⊇ [ρ]) (~-defn-wk [ξ] t~t′₁)) a≡a))
    neuEqTerm′
      [ΣFG]@(Bᵣ′ BΣˢ F G D A≡A [F] [G] G-ext _) =
      let A≡ΣFG = subset* D
          t~t , t′~t′ = wf-⊢~∷ t~t′
          ⊢tΣ = conv ⊢t A≡ΣFG
          ⊢t′Σ = conv ⊢t′ A≡ΣFG
          t~t′Σ = ~-conv t~t′ A≡ΣFG
          t~tΣ = ~-conv t~t A≡ΣFG
          t′~t′Σ = ~-conv t′~t′ A≡ΣFG

          [F] = [F] _ _
          _ , ⊢G , _ = inversion-ΠΣ (wf-⊢≡ (≅-eq A≡A) .proj₁)
          [fstn] = neuTerm [F] (fstₙ t-ne)
                     (PE.subst (_⊢_~_∷_ _ _ _) (PE.sym (wk-id F))
                        (~-fst ⊢G t~tΣ))
          [fstn′] = neuTerm [F] (fstₙ t′-ne)
                      (PE.subst (_⊢_~_∷_ _ _ _) (PE.sym (wk-id F))
                         (~-fst ⊢G t′~t′Σ))
          [fstn≡fstn′] = neuEqTerm [F] (fstₙ t-ne) (fstₙ t′-ne)
                           (PE.subst
                             (λ x → _ ⊢ _ ~ _ ∷ x)
                             (PE.sym (wk-id F))
                             (~-fst ⊢G t~t′Σ))
          [Gfstn] = [G] _ _ [fstn]
          [sndn≡sndn′] = neuEqTerm [Gfstn] (sndₙ t-ne) (sndₙ t′-ne)
            (PE.subst
               (λ x → _ ⊢ _ ~ _ ∷ x)
               (PE.cong (λ x → x [ fst _ _ ]₀) (PE.sym (wk-lift-id G)))
               (~-snd ⊢G t~t′Σ))
      in
      Σₜ₌ _ _ (id ⊢tΣ) (id ⊢t′Σ) (ne t-ne) (ne t′-ne) (~-to-≅ₜ t~t′Σ)
        (neuTerm [ΣFG] t-ne t~t) (neuTerm [ΣFG] t′-ne t′~t′)
        ([fstn] , [fstn′] , [fstn≡fstn′] , [sndn≡sndn′])
    neuEqTerm′
      [ΣFG]@(Bᵣ′ BΣʷ F G D A≡A [F] [G] G-ext _) =
      let A≡ΣFG = subset* D
          t~t , t′~t′ = wf-⊢~∷ t~t′
          ⊢tΣ = conv ⊢t A≡ΣFG
          ⊢t′Σ = conv ⊢t′ A≡ΣFG
          t~t′Σ = ~-conv t~t′ A≡ΣFG
          t~tΣ = ~-conv t~t A≡ΣFG
          t′~t′Σ = ~-conv t′~t′ A≡ΣFG
      in
      Σₜ₌ _ _ (id ⊢tΣ) (id ⊢t′Σ) (ne t-ne) (ne t′-ne) (~-to-≅ₜ t~t′Σ)
        (neuTerm [ΣFG] t-ne t~t) (neuTerm [ΣFG] t′-ne t′~t′)
        t~t′Σ
    neuEqTerm′ (Idᵣ ⊩A) =
      case subset* ⇒*Id of λ
        A≡Id →
      case wf-⊢~∷ t~t′ of λ
        (t~t , t′~t′) →
      ⊩Id≡∷
        (neuTerm (Idᵣ ⊩A) t-ne t~t)
        (neuTerm (Idᵣ ⊩A) t′-ne t′~t′)
        (~-conv t~t′ A≡Id)
      where
      open _⊩ₗId_ ⊩A
    neuEqTerm′ (emb ≤ᵘ-refl     ⊩A) = neuEqTerm′ ⊩A
    neuEqTerm′ (emb (≤ᵘ-step p) ⊩A) = neuEqTerm′ (emb p ⊩A)
