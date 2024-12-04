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
<<<<<<< HEAD
open import Definition.LogicalRelation R {{eqrel}}
open import Definition.LogicalRelation.ShapeView R {{eqrel}}
=======
open import Definition.Typed.Well-formed R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.ShapeView R
>>>>>>> master
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

<<<<<<< HEAD
  -- Helper function for reducible neutral equality of a specific type of derivation.
neuEq′ : ∀ {l A B} ([A] : Γ ⊩⟨ l ⟩ne A)
         (neA : Neutral A)
         (neB : Neutral B)
       → Γ ⊢ B
       → Γ ⊢ A ≅ B
       → Γ ⊩⟨ l ⟩ A ≡ B / ne-intr [A]
neuEq′ (noemb (ne _ [ ⊢A , ⊢B , D ] neK K≡K)) neA neB B A~B =
  let A≡K = whnfRed* D (ne neA)
  in  ne₌ _ (idRed:*: B) neB (PE.subst (λ x → _ ⊢ x ≅ _) A≡K A~B)
neuEq′ (emb p x) neB A:≡:B = {!neuEq′ x neB A:≡:B!}
=======
  -- Neutral reflexive types are reducible.
>>>>>>> master

  neu : Neutral A → Γ ⊢≅ A → Γ ⊩⟨ l ⟩ A
  neu neA ≅A = ne′ _ (id (wf-⊢≡ (≅-eq ≅A) .proj₁)) neA ≅A

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
    neuEq′ (noemb (ne _ D neK K≡K)) =
      let A≡K = whnfRed* D (ne neA) in
      ne₌ _ (id (wf-⊢≡ (≅-eq A~B) .proj₂)) neB
        (PE.subst (λ x → _ ⊢ x ≅ _) A≡K A~B)
    neuEq′ (emb ≤ᵘ-refl x) = neuEq′ x
    neuEq′ (emb (≤ᵘ-step p) x) = neuEq′ (emb p x)

opaque mutual

  -- Neutral reflexive terms are reducible.
<<<<<<< HEAD
  neuTerm : ∀ {l A n} ([A] : Γ ⊩⟨ l ⟩ A) (neN : Neutral n)
          → Γ ⊢ n ∷ A
          → Γ ⊢ n ~ n ∷ A
          → Γ ⊩⟨ l ⟩ n ∷ A / [A]
  neuTerm (Levelᵣ [ ⊢A , ⊢B , D ]) neN n n~n =
    let A≡Level = subset* D
        n~n′ = ~-conv n~n A≡Level
        n≡n  = ~-to-≅ₜ (~-conv n~n A≡Level)
    in Levelₜ _ (idRedTerm:*: (conv n A≡Level)) n≡n (ne (neNfₜ neN (conv n A≡Level) n~n′))
  neuTerm (Uᵣ′ l [l] p [ ⊢A , ⊢B , D ]) neN n n~n = {!!}
  -- neuTerm (Uᵣ′ l [l] ≤ᵘ-refl [ ⊢A , ⊢B , D ]) neN n n~n =
  --   let A≡U  = subset* D
  --       n≡n  = ~-to-≅ₜ (~-conv n~n A≡U)
  --   in Uₜ _ (idRedTerm:*: (conv n A≡U)) (ne neN) n≡n
  --     (neu neN (univ (conv n A≡U)) (~-to-≅ (~-conv n~n A≡U)))
  -- neuTerm (Uᵣ′ l [l] (≤ᵘ-step p) A⇒*U) n-ne ⊢n n~n =
  --   irrelevanceTerm (Uᵣ′ _ [l] p A⇒*U) (Uᵣ′ _ [l] (≤ᵘ-step p) A⇒*U)
  --     (neuTerm (Uᵣ′ _ [l] p A⇒*U) n-ne ⊢n n~n)
  neuTerm (ℕᵣ [ ⊢A , ⊢B , D ]) neN n n~n =
    let A≡ℕ  = subset* D
        n~n′ = ~-conv n~n A≡ℕ
        n≡n  = ~-to-≅ₜ n~n′
    in  ℕₜ _ (idRedTerm:*: (conv n A≡ℕ)) n≡n (ne (neNfₜ neN (conv n A≡ℕ) n~n′))
  neuTerm (Emptyᵣ [ ⊢A , ⊢B , D ]) neN n n~n =
    let A≡Empty  = subset* D
        n~n′ = ~-conv n~n A≡Empty
        n≡n  = ~-to-≅ₜ n~n′
    in  Emptyₜ _ (idRedTerm:*: (conv n A≡Empty)) n≡n (ne (neNfₜ neN (conv n A≡Empty) n~n′))
  neuTerm (Unitᵣ (Unitₜ k [k] k≡ [ ⊢A , ⊢B , D ] _)) neN n n~n =
    let A≡Unit  = subset* D
        n~n′ = ~-conv n~n A≡Unit
        n≡n′ = ~-to-≅ₜ n~n′
    in  Unitₜ _ (idRedTerm:*: (conv n A≡Unit)) n≡n′
              (ne (neNfₜ neN (conv n A≡Unit) n~n′))
  neuTerm (ne′ _ [ ⊢A , ⊢B , D ] neK K≡K) neN n n~n =
    let A≡K = subset* D
    in  neₜ _ (idRedTerm:*: (conv n A≡K)) (neNfₜ neN (conv n A≡K)
            (~-conv n~n A≡K))
  neuTerm (Πᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext ok) neN n n~n =
    let A≡ΠFG = subset* (red D)
    in  Πₜ _ (idRedTerm:*: (conv n A≡ΠFG)) (ne neN) (~-to-≅ₜ (~-conv n~n A≡ΠFG))
           (λ {_} {ρ} [ρ] ⊢Δ [a] [b] [a≡b] →
              let A≡ΠFG = subset* (red D)
                  ρA≡ρΠFG = Wk.wkEq [ρ] ⊢Δ (subset* (red D))
                  G[a]≡G[b] = escapeEq ([G] [ρ] ⊢Δ [b])
                                          (symEq ([G] [ρ] ⊢Δ [a]) ([G] [ρ] ⊢Δ [b])
                                                 (G-ext [ρ] ⊢Δ [a] [b] [a≡b]))
                  a = escapeTerm ([F] [ρ] ⊢Δ) [a]
                  b = escapeTerm ([F] [ρ] ⊢Δ) [b]
                  a≡b = escapeTermEq ([F] [ρ] ⊢Δ) [a≡b]
                  ⊢ρF = Wk.wk [ρ] ⊢Δ ⊢F
                  ⊢ρG = Wk.wk (Wk.lift [ρ]) (⊢Δ ∙ ⊢ρF) ⊢G
                  A≡ΠFG₁ = trans A≡ΠFG
                             (ΠΣ-cong ⊢F (refl ⊢F) (refl ⊢G) ok)
                  ρA≡ρΠFG₁ = trans ρA≡ρΠFG
                               (ΠΣ-cong ⊢ρF (refl ⊢ρF) (refl ⊢ρG) ok)
                  ρA≡ρΠFG₂ = trans ρA≡ρΠFG
                               (ΠΣ-cong ⊢ρF (refl ⊢ρF) (refl ⊢ρG) ok)
                  ρn₁ = conv (Wk.wkTerm [ρ] ⊢Δ n) ρA≡ρΠFG₁
                  ρn₂ = conv (Wk.wkTerm [ρ] ⊢Δ n) ρA≡ρΠFG₂
                  neN∘a = ∘ₙ (wkNeutral ρ neN)
                  neN∘b = ∘ₙ (wkNeutral ρ neN)
              in  neuEqTerm ([G] [ρ] ⊢Δ [a]) neN∘a neN∘b
                            (ρn₁ ∘ⱼ a) (conv (ρn₂ ∘ⱼ b) (≅-eq G[a]≡G[b]))
                            (~-app (~-wk [ρ] ⊢Δ (~-conv n~n A≡ΠFG₁))
                                   a≡b))
=======
>>>>>>> master

  neuTerm :
    (⊩A : Γ ⊩⟨ l ⟩ A) → Neutral n → Γ ⊢~ n ∷ A →
    Γ ⊩⟨ l ⟩ n ∷ A / ⊩A
  neuTerm {Γ} {A} {n} ⊩A n-ne ~n = neuTerm′ ⊩A
    where
<<<<<<< HEAD
    open _⊩ₗId_ ⊩A
  neuTerm (emb p x) neN n = {!neuTerm x neN n!}

  -- Neutrally equal terms are of reducible equality.
  neuEqTerm : ∀ {l A n n′} ([A] : Γ ⊩⟨ l ⟩ A)
              (neN : Neutral n) (neN′ : Neutral n′)
            → Γ ⊢ n  ∷ A
            → Γ ⊢ n′ ∷ A
            → Γ ⊢ n ~ n′ ∷ A
            → Γ ⊩⟨ l ⟩ n ≡ n′ ∷ A / [A]
  neuEqTerm (Levelᵣ [ ⊢A , ⊢B , D ]) neN neN′ n n′ n~n′ =
    let A≡Level = subset* D
        n~n′₁ = ~-conv n~n′ A≡Level
        n≡n′  = ~-to-≅ₜ n~n′₁
    in  Levelₜ₌ _ _ (idRedTerm:*: (conv n A≡Level)) (idRedTerm:*: (conv n′ A≡Level))
            n≡n′ (ne (neNfₜ₌ neN neN′ n~n′₁))
  neuEqTerm (Uᵣ′ l [l] p [ ⊢A , ⊢B , D ]) neN neN′ n n′ n~n′ = {!!}
  -- neuEqTerm (Uᵣ′ l [l] ≤ᵘ-refl [ ⊢A , ⊢B , D ]) neN neN′ n n′ n~n′ =
  --   let A≡U = subset* D
  --       n~n′₁ = ~-conv n~n′ A≡U
  --       n≡n′ = ~-to-≅ₜ n~n′₁
  --       nU = univ (conv n A≡U)
  --       nU′ = univ (conv n′ A≡U)
  --       wfn = neu neN nU (~-to-≅ (~-trans n~n′₁ (~-sym n~n′₁)))
  --   in Uₜ₌ _ _ (idRedTerm:*: (conv n A≡U)) (idRedTerm:*: (conv n′ A≡U)) (ne neN) (ne neN′) n≡n′
  --     wfn (neu neN′ nU′ (~-to-≅ (~-trans (~-sym n~n′₁) n~n′₁)))
  --     (neuEq wfn neN neN′ nU′ (≅-univ n≡n′))
  -- neuEqTerm (Uᵣ′ _ [l] (≤ᵘ-step p) A⇒*U) n-ne n′-ne ⊢n ⊢n′ n~n′ =
  --   irrelevanceEqTerm (Uᵣ′ _ [l] p A⇒*U) (Uᵣ′ _ [l] (≤ᵘ-step p) A⇒*U)
  --     (neuEqTerm (Uᵣ′ _ [l] p A⇒*U) n-ne n′-ne ⊢n ⊢n′ n~n′)
  neuEqTerm (ℕᵣ [ ⊢A , ⊢B , D ]) neN neN′ n n′ n~n′ =
    let A≡ℕ = subset* D
        n~n′₁ = ~-conv n~n′ A≡ℕ
        n≡n′ = ~-to-≅ₜ n~n′₁
    in  ℕₜ₌ _ _ (idRedTerm:*: (conv n A≡ℕ)) (idRedTerm:*: (conv n′ A≡ℕ))
            n≡n′ (ne (neNfₜ₌ neN neN′ n~n′₁))
  neuEqTerm (Emptyᵣ [ ⊢A , ⊢B , D ]) neN neN′ n n′ n~n′ =
    let A≡Empty = subset* D
        n~n′₁ = ~-conv n~n′ A≡Empty
        n≡n′ = ~-to-≅ₜ n~n′₁
    in  Emptyₜ₌ _ _ (idRedTerm:*: (conv n A≡Empty)) (idRedTerm:*: (conv n′ A≡Empty))
            n≡n′ (ne (neNfₜ₌ neN neN′ n~n′₁))
  neuEqTerm (Unitᵣ {s} (Unitₜ k [k] k≡ [ ⊢A , ⊢B , D ] _)) neN neN′ n n′ n~n′ =
    let A≡Unit = subset* D
        n~n′₁ = ~-conv n~n′ A≡Unit
        n≡n′ = ~-to-≅ₜ n~n′₁
    in  case Unit-with-η? s of
          ⊎.[ Unitₜ₌ˢ (conv n A≡Unit) (conv n′ A≡Unit)
            , (λ where
                 (PE.refl , no-η) →
                   Unitₜ₌ʷ _ _ (idRedTerm:*: (conv n A≡Unit))
                     (idRedTerm:*: (conv n′ A≡Unit)) n≡n′
                     (ne (neNfₜ₌ neN neN′ n~n′₁)) no-η)
            ]
  neuEqTerm (ne (ne _ [ ⊢A , ⊢B , D ] neK K≡K)) neN neN′ n n′ n~n′ =
    let A≡K = subset* D
    in  neₜ₌ _ _ (idRedTerm:*: (conv n A≡K)) (idRedTerm:*: (conv n′ A≡K))
             (neNfₜ₌ neN neN′ (~-conv n~n′ A≡K))
  neuEqTerm
    (Πᵣ′ F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext ok)
    neN neN′ n n′ n~n′ =
    let [ΠFG] = Πᵣ′ F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext ok
        A≡ΠFG = subset* D
        n~n′₁ = ~-conv n~n′ A≡ΠFG
        n≡n′ = ~-to-≅ₜ n~n′₁
        n~n = ~-trans n~n′ (~-sym n~n′)
        n′~n′ = ~-trans (~-sym n~n′) n~n′
    in  Πₜ₌ _ _ (idRedTerm:*: (conv n A≡ΠFG)) (idRedTerm:*: (conv n′ A≡ΠFG))
            (ne neN) (ne neN′) n≡n′
            (neuTerm [ΠFG] neN n n~n) (neuTerm [ΠFG] neN′ n′ n′~n′)
            (λ {_} {ρ} [ρ] ⊢Δ [a] →
               let ρA≡ρΠFG = Wk.wkEq [ρ] ⊢Δ A≡ΠFG
                   ρn = Wk.wkTerm [ρ] ⊢Δ n
                   ρn′ = Wk.wkTerm [ρ] ⊢Δ n′
                   a = escapeTerm ([F] [ρ] ⊢Δ) [a]
                   a≡a = escapeTermEq ([F] [ρ] ⊢Δ) (reflEqTerm ([F] [ρ] ⊢Δ) [a])
                   neN∙a   = ∘ₙ (wkNeutral ρ neN)
                   neN′∙a′ = ∘ₙ (wkNeutral ρ neN′)
                   ⊢ρF = Wk.wk [ρ] ⊢Δ ⊢F
                   ⊢ρG = Wk.wk (Wk.lift [ρ]) (⊢Δ ∙ ⊢ρF) ⊢G
                   ρA≡ρΠp₁FG = trans ρA≡ρΠFG
                                 (ΠΣ-cong ⊢ρF (refl ⊢ρF) (refl ⊢ρG) ok)
                   ρA≡ρΠp₂FG = trans ρA≡ρΠFG
                                 (ΠΣ-cong ⊢ρF (refl ⊢ρF) (refl ⊢ρG) ok)
                   ΠpFG≡Πp₁FG = ΠΣ-cong ⊢F (refl ⊢F) (refl ⊢G) ok
=======
    ⊢n : Γ ⊢ n ∷ A
    ⊢n = wf-⊢≡∷ (≅ₜ-eq (~-to-≅ₜ ~n)) .proj₂ .proj₁

    neuTerm′ : (⊩A : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ n ∷ A / ⊩A
    neuTerm′ (Uᵣ′ l ≤ᵘ-refl D) =
      let A≡U  = subset* D
          n≡n  = ~-to-≅ₜ (~-conv ~n A≡U)
      in Uₜ _ (id (conv ⊢n A≡U)) (ne n-ne) n≡n
        (neu n-ne (~-to-≅ (~-conv ~n A≡U)))
    neuTerm′ (Uᵣ′ _ (≤ᵘ-step p) A⇒*U) =
      irrelevanceTerm (Uᵣ′ _ p A⇒*U) (Uᵣ′ _ (≤ᵘ-step p) A⇒*U)
        (neuTerm (Uᵣ′ _ p A⇒*U) n-ne ~n)
    neuTerm′ (ℕᵣ D) =
      let A≡ℕ  = subset* D
          n~n′ = ~-conv ~n A≡ℕ
          n≡n  = ~-to-≅ₜ n~n′
      in
      ℕₜ _ (id (conv ⊢n A≡ℕ)) n≡n (ne (neNfₜ n-ne n~n′))
    neuTerm′ (Emptyᵣ D) =
      let A≡Empty  = subset* D
          n~n′ = ~-conv ~n A≡Empty
          n≡n  = ~-to-≅ₜ n~n′
      in
      Emptyₜ _ (id (conv ⊢n A≡Empty)) n≡n
        (ne (neNfₜ n-ne n~n′))
    neuTerm′ (Unitᵣ (Unitₜ D _)) =
      let A≡Unit  = subset* D
          n~n′ = ~-conv ~n A≡Unit
          n≡n′ = ~-to-≅ₜ n~n′
      in
      Unitₜ _ (id (conv ⊢n A≡Unit)) n≡n′
        (ne (neNfₜ n-ne n~n′))
    neuTerm′ (ne′ _ D neK K≡K) =
      let A≡K = subset* D in
      neₜ _ (id (conv ⊢n A≡K)) (neNfₜ n-ne (~-conv ~n A≡K))
    neuTerm′ (Πᵣ′ F G D A≡A [F] [G] _ ok) =
      let A≡ΠFG = subset* D in
      Πₜ _ (id (conv ⊢n A≡ΠFG)) (ne n-ne)
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
      let A≡ΣFG = subset* D
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
      Σₜ _ (id ⊢n) (~-to-≅ₜ ~n) (ne n-ne) ([fst] , [snd])
    neuTerm′ (Bᵣ′ (BΣ 𝕨 _ q) F G D A≡A [F] [G] G-ext _) =
      let A≡ΣFG = subset* D
          ⊢Γ = wfEq A≡ΣFG
          ⊢n = conv ⊢n A≡ΣFG
          ~n = ~-conv ~n A≡ΣFG
      in
      Σₜ _ (id ⊢n) (~-to-≅ₜ ~n) (ne n-ne) ~n
    neuTerm′ (Idᵣ ⊩A) =
      case subset* ⇒*Id of λ {
        A≡Id →
        _
      , id (conv ⊢n A≡Id)
      , ne n-ne
      , ~-conv ~n A≡Id }
      where
      open _⊩ₗId_ ⊩A
    neuTerm′ (emb ≤ᵘ-refl x) = neuTerm′ x
    neuTerm′ (emb (≤ᵘ-step l<) x) = neuTerm′ (emb l< x)

  -- Neutrally equal terms are of reducible equality.
>>>>>>> master

  neuEqTerm :
    (⊩A : Γ ⊩⟨ l ⟩ A) → Neutral n → Neutral n′ → Γ ⊢ n ~ n′ ∷ A →
    Γ ⊩⟨ l ⟩ n ≡ n′ ∷ A / ⊩A
  neuEqTerm {Γ} {A} {n} {n′} ⊩A n-ne n′-ne n~n′ = neuEqTerm′ ⊩A
    where
<<<<<<< HEAD
    open _⊩ₗId_ ⊩A
  neuEqTerm (emb p     ⊩A) = {! neuEqTerm ⊩A!}
=======
    n≡n′ : Γ ⊢ n ≡ n′ ∷ A
    n≡n′ = ≅ₜ-eq (~-to-≅ₜ n~n′)

    ⊢n : Γ ⊢ n ∷ A
    ⊢n = wf-⊢≡∷ n≡n′ .proj₂ .proj₁

    ⊢n′ : Γ ⊢ n′ ∷ A
    ⊢n′ = wf-⊢≡∷ n≡n′ .proj₂ .proj₂

    neuEqTerm′ :
      (⊩A : Γ ⊩⟨ l ⟩ A) →
      Γ ⊩⟨ l ⟩ n ≡ n′ ∷ A / ⊩A
    neuEqTerm′ (Uᵣ′ l ≤ᵘ-refl D) =
      let A≡U = subset* D
          n~n′₁ = ~-conv n~n′ A≡U
          ≅n , ≅n′ = wf-⊢≅ (~-to-≅ n~n′₁)
          n≡n′ = ~-to-≅ₜ n~n′₁
          wfn = neu n-ne ≅n
      in
      Uₜ₌ _ _ (id (conv ⊢n A≡U)) (id (conv ⊢n′ A≡U))
        (ne n-ne) (ne n′-ne) n≡n′ wfn (neu n′-ne ≅n′)
        (neuEq wfn n-ne n′-ne (≅-univ n≡n′))
    neuEqTerm′ (Uᵣ′ _ (≤ᵘ-step p) A⇒*U) =
      irrelevanceEqTerm (Uᵣ′ _ p A⇒*U) (Uᵣ′ _ (≤ᵘ-step p) A⇒*U)
        (neuEqTerm (Uᵣ′ _ p A⇒*U) n-ne n′-ne n~n′)
    neuEqTerm′ (ℕᵣ D) =
      let A≡ℕ = subset* D
          n~n′₁ = ~-conv n~n′ A≡ℕ
          n≡n′ = ~-to-≅ₜ n~n′₁
      in
      ℕₜ₌ _ _ (id (conv ⊢n A≡ℕ)) (id (conv ⊢n′ A≡ℕ))
        n≡n′ (ne (neNfₜ₌ n-ne n′-ne n~n′₁))
    neuEqTerm′ (Emptyᵣ D) =
      let A≡Empty = subset* D
          n~n′₁ = ~-conv n~n′ A≡Empty
          n≡n′ = ~-to-≅ₜ n~n′₁
      in
      Emptyₜ₌ _ _ (id (conv ⊢n A≡Empty))
        (id (conv ⊢n′ A≡Empty)) n≡n′
        (ne (neNfₜ₌ n-ne n′-ne n~n′₁))
    neuEqTerm′ (Unitᵣ {s} (Unitₜ D _)) =
      let A≡Unit = subset* D
          n~n′₁ = ~-conv n~n′ A≡Unit
          n≡n′ = ~-to-≅ₜ n~n′₁
      in
      case Unit-with-η? s of
        ⊎.[ Unitₜ₌ˢ (conv ⊢n A≡Unit) (conv ⊢n′ A≡Unit)
          , (λ where
               (PE.refl , no-η) →
                 Unitₜ₌ʷ _ _ (id (conv ⊢n A≡Unit))
                   (id (conv ⊢n′ A≡Unit)) n≡n′
                   (ne (neNfₜ₌ n-ne n′-ne n~n′₁)) no-η)
          ]
    neuEqTerm′ (ne (ne _ D neK K≡K)) =
      let A≡K = subset* D in
      neₜ₌ _ _ (id (conv ⊢n A≡K))
        (id (conv ⊢n′ A≡K))
        (neNfₜ₌ n-ne n′-ne (~-conv n~n′ A≡K))
    neuEqTerm′
      [ΠFG]@(Πᵣ′ F G D A≡A [F] [G] G-ext ok) =
      let A≡ΠFG = subset* D
          n~n′₁ = ~-conv n~n′ A≡ΠFG
          n≡n′ = ~-to-≅ₜ n~n′₁
          n~n , n′~n′ = wf-⊢~∷ n~n′
      in
      Πₜ₌ _ _ (id (conv ⊢n A≡ΠFG))
        (id (conv ⊢n′ A≡ΠFG))
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
      [ΣFG]@(Bᵣ′ BΣˢ F G D A≡A [F] [G] G-ext _) =
      let A≡ΣFG = subset* D
          n~n , n′~n′ = wf-⊢~∷ n~n′
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
      Σₜ₌ _ _ (id ⊢nΣ) (id ⊢n′Σ)
        (ne n-ne) (ne n′-ne) (~-to-≅ₜ n~n′Σ)
        (neuTerm [ΣFG] n-ne n~n) (neuTerm [ΣFG] n′-ne n′~n′)
        ([fstn] , [fstn′] , [fstn≡fstn′] , [sndn≡sndn′])
    neuEqTerm′
      [ΣFG]@(Bᵣ′ BΣʷ F G D A≡A [F] [G] G-ext _) =
      let A≡ΣFG = subset* D
          n~n , n′~n′ = wf-⊢~∷ n~n′
          ⊢nΣ = conv ⊢n A≡ΣFG
          ⊢n′Σ = conv ⊢n′ A≡ΣFG
          n~n′Σ = ~-conv n~n′ A≡ΣFG
          n~nΣ = ~-conv n~n A≡ΣFG
          n′~n′Σ = ~-conv n′~n′ A≡ΣFG
      in
      Σₜ₌ _ _ (id ⊢nΣ) (id ⊢n′Σ)
        (ne n-ne) (ne n′-ne) (~-to-≅ₜ n~n′Σ)
        (neuTerm [ΣFG] n-ne n~n) (neuTerm [ΣFG] n′-ne n′~n′) n~n′Σ
    neuEqTerm′ (Idᵣ ⊩A) =
      case subset* ⇒*Id of λ
        A≡Id →
      case wf-⊢~∷ n~n′ of λ
        (n~n , n′~n′) →
      ⊩Id≡∷
        (neuTerm (Idᵣ ⊩A) n-ne n~n)
        (neuTerm (Idᵣ ⊩A) n′-ne n′~n′)
        (~-conv n~n′ A≡Id)
      where
      open _⊩ₗId_ ⊩A
    neuEqTerm′ (emb ≤ᵘ-refl     ⊩A) = neuEqTerm′ ⊩A
    neuEqTerm′ (emb (≤ᵘ-step p) ⊩A) = neuEqTerm′ (emb p ⊩A)
>>>>>>> master
