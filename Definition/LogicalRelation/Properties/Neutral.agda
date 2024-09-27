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
open import Definition.Typed.Properties R
import Definition.Typed.Weakening R as Wk
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

-- Neutral reflexive types are reducible.
neu : ∀ {l A} (neA : Neutral A)
    → Γ ⊢ A
    → Γ ⊢ A ≅ A
    → Γ ⊩⟨ l ⟩ A
neu neA A A~A = ne′ _ (idRed:*: A) neA A~A

  -- Helper function for reducible neutral equality of a specific type of derivation.
neuEq′ : ∀ {l A B} ([A] : Γ ⊩⟨ l ⟩ne A)
         (neA : Neutral A)
         (neB : Neutral B)
       → Γ ⊢ B
       → Γ ⊢ A ≅ B
       → Γ ⊩⟨ l ⟩ A ≡ B / ne-intr [A]
neuEq′ (noemb (ne K [ ⊢A , ⊢B , D ] neK K≡K)) neA neB B A~B =
  let A≡K = whnfRed* D (ne neA)
  in  ne₌ _ (idRed:*: B) neB (PE.subst (λ x → _ ⊢ x ≅ _) A≡K A~B)
neuEq′ (emb ≤ᵘ-refl x) neB A:≡:B = neuEq′ x neB A:≡:B
neuEq′ (emb (≤ᵘ-step p) x) neB A:≡:B = neuEq′ (emb p x) neB A:≡:B

-- Neutrally equal types are of reducible equality.
neuEq : ∀ {l A B} ([A] : Γ ⊩⟨ l ⟩ A)
        (neA : Neutral A)
        (neB : Neutral B)
      → Γ ⊢ B
      → Γ ⊢ A ≅ B
      → Γ ⊩⟨ l ⟩ A ≡ B / [A]
neuEq [A] neA neB B A~B =
  irrelevanceEq (ne-intr (ne-elim neA [A]))
                [A]
                (neuEq′ (ne-elim neA [A]) neA neB B A~B)

mutual

  -- Neutral reflexive terms are reducible.
  neuTerm : ∀ {l A n} ([A] : Γ ⊩⟨ l ⟩ A) (neN : Neutral n)
          → Γ ⊢ n ∷ A
          → Γ ⊢ n ~ n ∷ A
          → Γ ⊩⟨ l ⟩ n ∷ A / [A]
  neuTerm (Uᵣ′ l ≤ᵘ-refl [ ⊢A , ⊢B , D ]) neN n n~n =
    let A≡U  = subset* D
        n≡n  = ~-to-≅ₜ (~-conv n~n A≡U)
    in Uₜ _ (idRedTerm:*: (conv n A≡U)) (ne neN) n≡n
      (neu neN (univ (conv n A≡U)) (~-to-≅ (~-conv n~n A≡U)))
  neuTerm (Uᵣ′ _ (≤ᵘ-step p) A⇒*U) n-ne ⊢n n~n =
    irrelevanceTerm (Uᵣ′ _ p A⇒*U) (Uᵣ′ _ (≤ᵘ-step p) A⇒*U)
      (neuTerm (Uᵣ′ _ p A⇒*U) n-ne ⊢n n~n)
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
  neuTerm (Unitᵣ (Unitₜ [ ⊢A , ⊢B , D ] _)) neN n n~n =
    let A≡Unit  = subset* D
        n~n′ = ~-conv n~n A≡Unit
        n≡n′ = ~-to-≅ₜ n~n′
    in  Unitₜ _ (idRedTerm:*: (conv n A≡Unit)) n≡n′
              (ne (neNfₜ neN (conv n A≡Unit) n~n′))
  neuTerm (ne′ K [ ⊢A , ⊢B , D ] neK K≡K) neN n n~n =
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

           (λ {_} {ρ} [ρ] ⊢Δ [a] →
              let ρA≡ρΠFG = Wk.wkEq [ρ] ⊢Δ (subset* (red D))
                  a = escapeTerm ([F] [ρ] ⊢Δ) [a]
                  a≡a = escapeTermEq ([F] [ρ] ⊢Δ) (reflEqTerm ([F] [ρ] ⊢Δ) [a])
                  ⊢ρF = Wk.wk [ρ] ⊢Δ ⊢F
                  ⊢ρG = Wk.wk (Wk.lift [ρ]) (⊢Δ ∙ ⊢ρF) ⊢G
                  A≡ΠFG′ = trans A≡ΠFG
                             (ΠΣ-cong ⊢F (refl ⊢F) (refl ⊢G) ok)
                  ρA≡ρΠFG′ = trans ρA≡ρΠFG
                               (ΠΣ-cong ⊢ρF (refl ⊢ρF) (refl ⊢ρG) ok)
               in  neuTerm ([G] [ρ] ⊢Δ [a]) (∘ₙ (wkNeutral ρ neN))
                           (conv (Wk.wkTerm [ρ] ⊢Δ n) ρA≡ρΠFG′ ∘ⱼ a)
                           (~-app (~-wk [ρ] ⊢Δ (~-conv n~n A≡ΠFG′)) a≡a))
  neuTerm (Bᵣ′ (BΣ 𝕤 _ q) F G D ⊢F ⊢G A≡A [F] [G] G-ext _) neN ⊢n n~n =
    let A≡ΣFG = subset* (red D)
        ⊢Γ = wf ⊢F
        ⊢n = conv ⊢n A≡ΣFG
        n~n = ~-conv n~n A≡ΣFG

        [F] = [F] Wk.id ⊢Γ
        [fst] = neuTerm [F] (fstₙ neN)
                        (PE.subst
                          (λ x → _ ⊢ fst _ _ ∷ x)
                          (PE.sym (wk-id F))
                          (fstⱼ ⊢F ⊢G ⊢n))
                        (PE.subst
                          (λ x → _ ⊢ _ ~ _ ∷ x)
                          (PE.sym (wk-id F))
                          (~-fst ⊢F ⊢G n~n))
        [Gfst] = [G] Wk.id ⊢Γ [fst]
        [snd] = neuTerm [Gfst] (sndₙ neN)
                        (PE.subst
                          (λ x → _ ⊢ snd _ _ ∷ x)
                          (PE.cong (λ x → x [ fst _ _ ]₀)
                             (PE.sym (wk-lift-id G)))
                          (sndⱼ ⊢F ⊢G ⊢n))
                        (PE.subst
                          (λ x → _ ⊢ _ ~ _ ∷ x)
                          (PE.cong (λ x → x [ fst _ _ ]₀)
                             (PE.sym (wk-lift-id G)))
                          (~-snd ⊢F ⊢G n~n))
    in  Σₜ _ (idRedTerm:*: ⊢n) (~-to-≅ₜ n~n) (ne neN) ([fst] , [snd])
  neuTerm (Bᵣ′ (BΣ 𝕨 _ q) F G D ⊢F ⊢G A≡A [F] [G] G-ext _) neN ⊢n n~n =
    let A≡ΣFG = subset* (red D)
        ⊢Γ = wf ⊢F
        ⊢n = conv ⊢n A≡ΣFG
        n~n = ~-conv n~n A≡ΣFG
    in  Σₜ _ (idRedTerm:*: ⊢n) (~-to-≅ₜ n~n) (ne neN) n~n
  neuTerm (Idᵣ ⊩A) n-n ⊢n n~n =
    case subset* (red ⇒*Id) of λ {
      A≡Id →
      _
    , idRedTerm:*: (conv ⊢n A≡Id)
    , ne n-n
    , ~-conv n~n A≡Id }
    where
    open _⊩ₗId_ ⊩A
  neuTerm (emb ≤ᵘ-refl x) neN n = neuTerm x neN n
  neuTerm (emb (≤ᵘ-step l<) x) neN n = neuTerm (emb l< x) neN n

  -- Neutrally equal terms are of reducible equality.
  neuEqTerm : ∀ {l A n n′} ([A] : Γ ⊩⟨ l ⟩ A)
              (neN : Neutral n) (neN′ : Neutral n′)
            → Γ ⊢ n  ∷ A
            → Γ ⊢ n′ ∷ A
            → Γ ⊢ n ~ n′ ∷ A
            → Γ ⊩⟨ l ⟩ n ≡ n′ ∷ A / [A]
  neuEqTerm (Uᵣ′ l ≤ᵘ-refl [ ⊢A , ⊢B , D ]) neN neN′ n n′ n~n′ =
    let A≡U = subset* D
        n~n′₁ = ~-conv n~n′ A≡U
        n≡n′ = ~-to-≅ₜ n~n′₁
        nU = univ (conv n A≡U)
        nU′ = univ (conv n′ A≡U)
        wfn = neu neN nU (~-to-≅ (~-trans n~n′₁ (~-sym n~n′₁)))
    in Uₜ₌ _ _ (idRedTerm:*: (conv n A≡U)) (idRedTerm:*: (conv n′ A≡U)) (ne neN) (ne neN′) n≡n′
      wfn (neu neN′ nU′ (~-to-≅ (~-trans (~-sym n~n′₁) n~n′₁)))
      (neuEq wfn neN neN′ nU′ (≅-univ n≡n′))
  neuEqTerm (Uᵣ′ _ (≤ᵘ-step p) A⇒*U) n-ne n′-ne ⊢n ⊢n′ n~n′ =
    irrelevanceEqTerm (Uᵣ′ _ p A⇒*U) (Uᵣ′ _ (≤ᵘ-step p) A⇒*U)
      (neuEqTerm (Uᵣ′ _ p A⇒*U) n-ne n′-ne ⊢n ⊢n′ n~n′)
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
  neuEqTerm (Unitᵣ {s} (Unitₜ [ ⊢A , ⊢B , D ] _)) neN neN′ n n′ n~n′ =
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
  neuEqTerm (ne (ne K [ ⊢A , ⊢B , D ] neK K≡K)) neN neN′ n n′ n~n′ =
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

               in  neuEqTerm ([G] [ρ] ⊢Δ [a]) neN∙a neN′∙a′
                     (conv ρn ρA≡ρΠp₁FG ∘ⱼ a)
                     (conv ρn′ ρA≡ρΠp₂FG ∘ⱼ a)
                     (~-app (~-wk [ρ] ⊢Δ (~-conv n~n′₁ ΠpFG≡Πp₁FG)) a≡a))
  neuEqTerm
    [ΣFG]@(Bᵣ′ BΣˢ F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext _)
    neN neN′ ⊢n ⊢n′ n~n′ =
    let A≡ΣFG = subset* D
        n~n = ~-trans n~n′ (~-sym n~n′)
        n′~n′ = ~-trans (~-sym n~n′) n~n′
        ⊢nΣ = conv ⊢n A≡ΣFG
        ⊢n′Σ = conv ⊢n′ A≡ΣFG
        n~n′Σ = ~-conv n~n′ A≡ΣFG
        n~nΣ = ~-conv n~n A≡ΣFG
        n′~n′Σ = ~-conv n′~n′ A≡ΣFG

        ⊢Γ = wf ⊢F
        [F] = [F] Wk.id ⊢Γ
        ⊢fstnΣ = (PE.subst
                (λ x → _ ⊢ fst _ _ ∷ x)
                (PE.sym (wk-id F))
                (fstⱼ ⊢F ⊢G ⊢nΣ))
        ⊢fstn′Σ = (PE.subst
                    (λ x → _ ⊢ fst _ _ ∷ x)
                    (PE.sym (wk-id F))
                    (fstⱼ ⊢F ⊢G ⊢n′Σ))
        [fstn] = neuTerm [F] (fstₙ neN)
                         ⊢fstnΣ
                         (PE.subst
                           (λ x → _ ⊢ _ ~ _ ∷ x)
                           (PE.sym (wk-id F))
                           (~-fst ⊢F ⊢G n~nΣ))
        [fstn′] = neuTerm [F] (fstₙ neN′)
                          ⊢fstn′Σ
                          (PE.subst
                            (λ x → _ ⊢ _ ~ _ ∷ x)
                            (PE.sym (wk-id F))
                            (~-fst ⊢F ⊢G n′~n′Σ))
        [fstn≡fstn′] = neuEqTerm [F] (fstₙ neN) (fstₙ neN′)
                         ⊢fstnΣ
                         ⊢fstn′Σ
                         (PE.subst
                           (λ x → _ ⊢ _ ~ _ ∷ x)
                           (PE.sym (wk-id F))
                           (~-fst ⊢F ⊢G n~n′Σ))
        [Gfstn] = [G] Wk.id ⊢Γ [fstn]
        [Gfstn′] = PE.subst (λ x → _ ⊩⟨ _ ⟩ x [ fst _ _ ]₀)
                     (wk-lift-id G) ([G] Wk.id ⊢Γ [fstn′])
        [fstn′≡fstn] = symEqTerm [F] [fstn≡fstn′]
        [Gfstn′≡Gfstn] = irrelevanceEq″
          (PE.cong (λ x → x [ fst _ _ ]₀) (wk-lift-id G))
          (PE.cong (λ x → x [ fst _ _ ]₀) (wk-lift-id G))
          ([G] Wk.id ⊢Γ [fstn′]) [Gfstn′]
          (G-ext Wk.id ⊢Γ [fstn′] [fstn] [fstn′≡fstn])
        Gfstn′≡Gfstn = ≅-eq (escapeEq [Gfstn′] [Gfstn′≡Gfstn])
        [sndn≡sndn′] = neuEqTerm [Gfstn] (sndₙ neN) (sndₙ neN′)
          (PE.subst
             (λ x → _ ⊢ snd _ _ ∷ x)
             (PE.cong (λ x → x [ fst _ _ ]₀) (PE.sym (wk-lift-id G)))
             (sndⱼ ⊢F ⊢G ⊢nΣ))
          (PE.subst
             (λ x → _ ⊢ snd _ _ ∷ x)
             (PE.cong (λ x → x [ fst _ _ ]₀) (PE.sym (wk-lift-id G)))
             (conv (sndⱼ ⊢F ⊢G ⊢n′Σ) Gfstn′≡Gfstn))
          (PE.subst
             (λ x → _ ⊢ _ ~ _ ∷ x)
             (PE.cong (λ x → x [ fst _ _ ]₀) (PE.sym (wk-lift-id G)))
             (~-snd ⊢F ⊢G n~n′Σ))
    in  Σₜ₌ _ _ (idRedTerm:*: ⊢nΣ) (idRedTerm:*: ⊢n′Σ)
            (ne neN) (ne neN′) (~-to-≅ₜ n~n′Σ)
            (neuTerm [ΣFG] neN ⊢n n~n) (neuTerm [ΣFG] neN′ ⊢n′ n′~n′)
            ([fstn] , [fstn′] , [fstn≡fstn′] , [sndn≡sndn′])
  neuEqTerm
    [ΣFG]@(Bᵣ′ BΣʷ F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext _)
    neN neN′ ⊢n ⊢n′ n~n′ =
    let A≡ΣFG = subset* D
        n~n = ~-trans n~n′ (~-sym n~n′)
        n′~n′ = ~-trans (~-sym n~n′) n~n′
        ⊢nΣ = conv ⊢n A≡ΣFG
        ⊢n′Σ = conv ⊢n′ A≡ΣFG
        n~n′Σ = ~-conv n~n′ A≡ΣFG
        n~nΣ = ~-conv n~n A≡ΣFG
        n′~n′Σ = ~-conv n′~n′ A≡ΣFG
    in  Σₜ₌ _ _ (idRedTerm:*: ⊢nΣ) (idRedTerm:*: ⊢n′Σ)
            (ne neN) (ne neN′) (~-to-≅ₜ n~n′Σ)
            (neuTerm [ΣFG] neN ⊢n n~n) (neuTerm [ΣFG] neN′ ⊢n′ n′~n′)
            n~n′Σ
  neuEqTerm (Idᵣ ⊩A) n-n n′-n ⊢n ⊢n′ n~n′ =
    case subset* (red ⇒*Id) of λ {
      A≡Id →
    case ~-trans n~n′ (~-sym n~n′) of λ {
      n~n →
    case ~-trans (~-sym n~n′) n~n′ of λ {
      n′~n′ →
    ⊩Id≡∷
      (neuTerm (Idᵣ ⊩A) n-n ⊢n n~n)
      (neuTerm (Idᵣ ⊩A) n′-n ⊢n′ n′~n′)
      (~-conv n~n′ A≡Id) }}}
    where
    open _⊩ₗId_ ⊩A
  neuEqTerm (emb ≤ᵘ-refl     ⊩A) = neuEqTerm ⊩A
  neuEqTerm (emb (≤ᵘ-step p) ⊩A) = neuEqTerm (emb p ⊩A)
