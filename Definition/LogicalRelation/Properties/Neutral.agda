open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.Neutral
  {a} (M : Set a) {{eqrel : EqRelSet M}} where

open EqRelSet {{...}}

open import Definition.Untyped M hiding (Wk; _∷_)
open import Definition.Untyped.Properties M
open import Definition.Typed M
open import Definition.Typed.Properties M
import Definition.Typed.Weakening M as Wk
open import Definition.LogicalRelation M
open import Definition.LogicalRelation.ShapeView M
open import Definition.LogicalRelation.Irrelevance M
open import Definition.LogicalRelation.Properties.Reflexivity M
open import Definition.LogicalRelation.Properties.Escape M
open import Definition.LogicalRelation.Properties.Symmetry M

open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality as PE
  using (≈-refl; ≈-sym; ≈-trans)

private
  variable
    m : Nat
    Γ : Con Term m

-- Neutral reflexive types are reducible.
neu : ∀ {l A} (neA : Neutral A)
    → Γ ⊢ A
    → Γ ⊢ A ~ A ∷ U
    → Γ ⊩⟨ l ⟩ A
neu neA A A~A = ne′ _ (idRed:*: A) neA A~A

  -- Helper function for reducible neutral equality of a specific type of derivation.
neuEq′ : ∀ {l A B} ([A] : Γ ⊩⟨ l ⟩ne A)
         (neA : Neutral A)
         (neB : Neutral B)
       → Γ ⊢ A → Γ ⊢ B
       → Γ ⊢ A ~ B ∷ U
       → Γ ⊩⟨ l ⟩ A ≡ B / ne-intr [A]
neuEq′ (noemb (ne K [ ⊢A , ⊢B , D ] neK K≡K)) neA neB A B A~B =
  let A≡K = whnfRed* D (ne neA)
  in  ne₌ _ (idRed:*: B) neB (PE.subst (λ x → _ ⊢ x ~ _ ∷ _) A≡K A~B)
neuEq′ (emb 0<1 x) neB A:≡:B = neuEq′ x neB A:≡:B

-- Neutrally equal types are of reducible equality.
neuEq : ∀ {l A B} ([A] : Γ ⊩⟨ l ⟩ A)
        (neA : Neutral A)
        (neB : Neutral B)
      → Γ ⊢ A → Γ ⊢ B
      → Γ ⊢ A ~ B ∷ U
      → Γ ⊩⟨ l ⟩ A ≡ B / [A]
neuEq [A] neA neB A B A~B =
  irrelevanceEq (ne-intr (ne-elim neA [A]))
                [A]
                (neuEq′ (ne-elim neA [A]) neA neB A B A~B)

mutual
  -- Neutral reflexive terms are reducible.
  neuTerm : ∀ {l A n} ([A] : Γ ⊩⟨ l ⟩ A) (neN : Neutral n)
          → Γ ⊢ n ∷ A
          → Γ ⊢ n ~ n ∷ A
          → Γ ⊩⟨ l ⟩ n ∷ A / [A]
  neuTerm (Uᵣ′ .⁰ 0<1 ⊢Γ) neN n n~n =
    Uₜ _ (idRedTerm:*: n) (ne neN) (~-to-≅ₜ n~n) (neu neN (univ n) n~n)
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
  neuTerm (Unitᵣ [ ⊢A , ⊢B , D ]) neN n n~n =
    let A≡Unit  = subset* D
        n~n′ = ~-conv n~n A≡Unit
    in  Unitₜ _ (idRedTerm:*: (conv n A≡Unit)) (ne neN)
  neuTerm (ne′ K [ ⊢A , ⊢B , D ] neK K≡K) neN n n~n =
    let A≡K = subset* D
    in  neₜ _ (idRedTerm:*: (conv n A≡K)) (neNfₜ neN (conv n A≡K)
            (~-conv n~n A≡K))
  neuTerm (Πᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) neN n n~n =
    let A≡ΠFG = subset* (red D)
    in  Πₜ _ (idRedTerm:*: (conv n A≡ΠFG)) (ne neN) (~-to-≅ₜ (~-conv n~n A≡ΠFG))
           (λ {_} {ρ} [ρ] ⊢Δ [a] [b] [a≡b] p≈p₁ p≈p₂ →
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
                  A≡ΠFG₁ = trans A≡ΠFG (Π-cong ⊢F (refl ⊢F) (refl ⊢G) p≈p₁ ≈-refl)
                  ρA≡ρΠFG₁ = trans ρA≡ρΠFG (Π-cong ⊢ρF (refl ⊢ρF) (refl ⊢ρG) p≈p₁ ≈-refl)
                  ρA≡ρΠFG₂ = trans ρA≡ρΠFG (Π-cong ⊢ρF (refl ⊢ρF) (refl ⊢ρG) p≈p₂ ≈-refl)
                  ρn₁ = conv (Wk.wkTerm [ρ] ⊢Δ n) ρA≡ρΠFG₁
                  ρn₂ = conv (Wk.wkTerm [ρ] ⊢Δ n) ρA≡ρΠFG₂
                  neN∘a = ∘ₙ (wkNeutral ρ neN)
                  neN∘b = ∘ₙ (wkNeutral ρ neN)
              in  neuEqTerm ([G] [ρ] ⊢Δ [a]) neN∘a neN∘b
                            (ρn₁ ∘ⱼ a) (conv (ρn₂ ∘ⱼ b) (≅-eq G[a]≡G[b]))
                            (~-app (~-wk [ρ] ⊢Δ (~-conv n~n A≡ΠFG₁))
                                   a≡b ≈-refl (≈-trans (≈-sym p≈p₁) p≈p₂)))

           (λ {_} {ρ} [ρ] ⊢Δ [a] p≈p′ →
              let ρA≡ρΠFG = Wk.wkEq [ρ] ⊢Δ (subset* (red D))
                  a = escapeTerm ([F] [ρ] ⊢Δ) [a]
                  a≡a = escapeTermEq ([F] [ρ] ⊢Δ) (reflEqTerm ([F] [ρ] ⊢Δ) [a])
                  ⊢ρF = Wk.wk [ρ] ⊢Δ ⊢F
                  ⊢ρG = Wk.wk (Wk.lift [ρ]) (⊢Δ ∙ ⊢ρF) ⊢G
                  A≡ΠFG′ = trans A≡ΠFG (Π-cong ⊢F (refl ⊢F) (refl ⊢G) p≈p′ ≈-refl)
                  ρA≡ρΠFG′ = trans ρA≡ρΠFG
                                   (Π-cong ⊢ρF (refl ⊢ρF) (refl ⊢ρG) p≈p′ ≈-refl)
               in  neuTerm ([G] [ρ] ⊢Δ [a]) (∘ₙ (wkNeutral ρ neN))
                           (conv (Wk.wkTerm [ρ] ⊢Δ n) ρA≡ρΠFG′ ∘ⱼ a)
                           (~-app (~-wk [ρ] ⊢Δ (~-conv n~n A≡ΠFG′)) a≡a ≈-refl ≈-refl))
  neuTerm (Bᵣ′ (BΣ Σₚ q) F G D ⊢F ⊢G A≡A [F] [G] G-ext) neN ⊢n n~n =
    let A≡ΣFG = subset* (red D)
        ⊢Γ = wf ⊢F
        ⊢n = conv ⊢n A≡ΣFG
        n~n = ~-conv n~n A≡ΣFG

        [F] = [F] Wk.id ⊢Γ
        [fst] = neuTerm [F] (fstₙ neN)
                        (PE.subst
                          (λ x → _ ⊢ fst _ ∷ x)
                          (PE.sym (wk-id F))
                          (fstⱼ ⊢F ⊢G ⊢n))
                        (PE.subst
                          (λ x → _ ⊢ _ ~ _ ∷ x)
                          (PE.sym (wk-id F))
                          (~-fst ⊢F ⊢G n~n))
        [Gfst] = [G] Wk.id ⊢Γ [fst]
        [snd] = neuTerm [Gfst] (sndₙ neN)
                        (PE.subst
                          (λ x → _ ⊢ snd _ ∷ x)
                          (PE.cong (λ x → x [ fst _ ]) (PE.sym (wk-lift-id G)))
                          (sndⱼ ⊢F ⊢G ⊢n))
                        (PE.subst
                          (λ x → _ ⊢ _ ~ _ ∷ x)
                          (PE.cong (λ x → x [ fst _ ]) (PE.sym (wk-lift-id G)))
                          (~-snd ⊢F ⊢G n~n))
    in  Σₜ _ (idRedTerm:*: ⊢n) (~-to-≅ₜ n~n) (ne neN) ([fst] , [snd])
  neuTerm (Bᵣ′ (BΣ Σᵣ q) F G D ⊢F ⊢G A≡A [F] [G] G-ext) neN ⊢n n~n =
    let A≡ΣFG = subset* (red D)
        ⊢Γ = wf ⊢F
        ⊢n = conv ⊢n A≡ΣFG
        n~n = ~-conv n~n A≡ΣFG
    in  Σₜ _ (idRedTerm:*: ⊢n) (~-to-≅ₜ n~n) (ne neN) n~n
  neuTerm (emb 0<1 x) neN n = neuTerm x neN n

  -- Neutrally equal terms are of reducible equality.
  neuEqTerm : ∀ {l A n n′} ([A] : Γ ⊩⟨ l ⟩ A)
              (neN : Neutral n) (neN′ : Neutral n′)
            → Γ ⊢ n  ∷ A
            → Γ ⊢ n′ ∷ A
            → Γ ⊢ n ~ n′ ∷ A
            → Γ ⊩⟨ l ⟩ n ≡ n′ ∷ A / [A]
  neuEqTerm (Uᵣ′ .⁰ 0<1 ⊢Γ) neN neN′ n n′ n~n′ =
    let [n]  = neu neN  (univ n) (~-trans n~n′ (~-sym n~n′))
        [n′] = neu neN′ (univ n′) (~-trans (~-sym n~n′) n~n′)
    in  Uₜ₌ _ _ (idRedTerm:*: n) (idRedTerm:*: n′) (ne neN) (ne neN′)
            (~-to-≅ₜ n~n′) [n] [n′] (neuEq [n] neN neN′ (univ n) (univ n′) n~n′)
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
  neuEqTerm (Unitᵣ [ ⊢A , ⊢B , D ]) neN neN′ n n′ n~n′ =
    let A≡Unit = subset* D
    in  Unitₜ₌ (conv n A≡Unit) (conv n′ A≡Unit)
  neuEqTerm (ne (ne K [ ⊢A , ⊢B , D ] neK K≡K)) neN neN′ n n′ n~n′ =
    let A≡K = subset* D
    in  neₜ₌ _ _ (idRedTerm:*: (conv n A≡K)) (idRedTerm:*: (conv n′ A≡K))
             (neNfₜ₌ neN neN′ (~-conv n~n′ A≡K))
  neuEqTerm (Πᵣ′ F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext) neN neN′ n n′ n~n′ =
    let [ΠFG] = Πᵣ′ F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext
        A≡ΠFG = subset* D
        n~n′₁ = ~-conv n~n′ A≡ΠFG
        n≡n′ = ~-to-≅ₜ n~n′₁
        n~n = ~-trans n~n′ (~-sym n~n′)
        n′~n′ = ~-trans (~-sym n~n′) n~n′
    in  Πₜ₌ _ _ (idRedTerm:*: (conv n A≡ΠFG)) (idRedTerm:*: (conv n′ A≡ΠFG))
            (ne neN) (ne neN′) n≡n′
            (neuTerm [ΠFG] neN n n~n) (neuTerm [ΠFG] neN′ n′ n′~n′)
            (λ {_} {ρ} [ρ] ⊢Δ [a] p≈p₁ p≈p₂ →
               let ρA≡ρΠFG = Wk.wkEq [ρ] ⊢Δ A≡ΠFG
                   ρn = Wk.wkTerm [ρ] ⊢Δ n
                   ρn′ = Wk.wkTerm [ρ] ⊢Δ n′
                   a = escapeTerm ([F] [ρ] ⊢Δ) [a]
                   a≡a = escapeTermEq ([F] [ρ] ⊢Δ) (reflEqTerm ([F] [ρ] ⊢Δ) [a])
                   neN∙a   = ∘ₙ (wkNeutral ρ neN)
                   neN′∙a′ = ∘ₙ (wkNeutral ρ neN′)
                   ⊢ρF = Wk.wk [ρ] ⊢Δ ⊢F
                   ⊢ρG = Wk.wk (Wk.lift [ρ]) (⊢Δ ∙ ⊢ρF) ⊢G
                   ρA≡ρΠp₁FG = trans ρA≡ρΠFG (Π-cong ⊢ρF (refl ⊢ρF) (refl ⊢ρG) p≈p₁ ≈-refl)
                   ρA≡ρΠp₂FG = trans ρA≡ρΠFG (Π-cong ⊢ρF (refl ⊢ρF) (refl ⊢ρG) p≈p₂ ≈-refl)
                   ΠpFG≡Πp₁FG = Π-cong ⊢F (refl ⊢F) (refl ⊢G) p≈p₁ ≈-refl

               in  neuEqTerm ([G] [ρ] ⊢Δ [a]) neN∙a neN′∙a′
                             (conv ρn ρA≡ρΠp₁FG ∘ⱼ a)
                             (conv ρn′ ρA≡ρΠp₂FG ∘ⱼ a)
                             (~-app (~-wk [ρ] ⊢Δ (~-conv n~n′₁ ΠpFG≡Πp₁FG)) a≡a ≈-refl (≈-trans (≈-sym p≈p₁) p≈p₂)))
  neuEqTerm [ΣFG]@(Bᵣ′ BΣₚ F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext) neN neN′ ⊢n ⊢n′ n~n′ =
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
                (λ x → _ ⊢ fst _ ∷ x)
                (PE.sym (wk-id F))
                (fstⱼ ⊢F ⊢G ⊢nΣ))
        ⊢fstn′Σ = (PE.subst
                    (λ x → _ ⊢ fst _ ∷ x)
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
        [Gfstn′] = PE.subst (λ x → _ ⊩⟨ _ ⟩ x [ fst _ ]) (wk-lift-id G) ([G] Wk.id ⊢Γ [fstn′])
        [fstn′≡fstn] = symEqTerm [F] [fstn≡fstn′]
        [Gfstn′≡Gfstn] = irrelevanceEq″
                           (PE.cong (λ x → x [ fst _ ]) (wk-lift-id G))
                           (PE.cong (λ x → x [ fst _ ]) (wk-lift-id G))
                           ([G] Wk.id ⊢Γ [fstn′]) [Gfstn′]
                           (G-ext Wk.id ⊢Γ [fstn′] [fstn] [fstn′≡fstn])
        Gfstn′≡Gfstn = ≅-eq (escapeEq [Gfstn′] [Gfstn′≡Gfstn])
        [sndn≡sndn′] = neuEqTerm [Gfstn] (sndₙ neN) (sndₙ neN′)
                          (PE.subst
                            (λ x → _ ⊢ snd _ ∷ x)
                            (PE.cong (λ x → x [ fst _ ]) (PE.sym (wk-lift-id G)))
                            (sndⱼ ⊢F ⊢G ⊢nΣ))
                          (PE.subst
                            (λ x → _ ⊢ snd _ ∷ x)
                            (PE.cong (λ x → x [ fst _ ]) (PE.sym (wk-lift-id G)))
                            (conv (sndⱼ ⊢F ⊢G ⊢n′Σ) Gfstn′≡Gfstn))
                          (PE.subst
                            (λ x → _ ⊢ _ ~ _ ∷ x)
                            (PE.cong (λ x → x [ fst _ ]) (PE.sym (wk-lift-id G)))
                            (~-snd ⊢F ⊢G n~n′Σ))
    in  Σₜ₌ _ _ (idRedTerm:*: ⊢nΣ) (idRedTerm:*: ⊢n′Σ)
            (ne neN) (ne neN′) (~-to-≅ₜ n~n′Σ)
            (neuTerm [ΣFG] neN ⊢n n~n) (neuTerm [ΣFG] neN′ ⊢n′ n′~n′)
            ([fstn] , [fstn′] , [fstn≡fstn′] , [sndn≡sndn′])
  neuEqTerm [ΣFG]@(Bᵣ′ BΣᵣ F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext) neN neN′ ⊢n ⊢n′ n~n′ =
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
  neuEqTerm (emb 0<1 x) neN neN′ n:≡:n′ = neuEqTerm x neN neN′ n:≡:n′
