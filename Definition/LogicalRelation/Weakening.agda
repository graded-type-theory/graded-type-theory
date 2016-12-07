open import Definition.EqualityRelation

module Definition.LogicalRelation.Weakening {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped as U hiding (wk)
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening as T hiding (wk; wkEq; wkTerm; wkEqTerm)
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties.Reflexivity
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Tactic

open import Tools.Product
open import Tools.Unit
import Tools.PropositionalEquality as PE

mutual
  wkTermℕ : ∀ {Γ Δ n} (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ)
          → Γ ⊩ℕ n ∷ℕ → Δ ⊩ℕ U.wk (toWk ρ) n ∷ℕ
  wkTermℕ ρ ⊢Δ (ℕₜ n d n≡n natN prop) =
    ℕₜ (U.wk (toWk ρ) n) (wkRed:*:Term ρ ⊢Δ d)
       (≅ₜ-wk ρ ⊢Δ n≡n) (wkNatural (toWk ρ) natN)
       (wkNatural-prop ρ ⊢Δ natN prop)

  wkNatural-prop : ∀ {Γ Δ n} (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ) (natN : Natural n)
                 → natural-prop Γ n natN
                 → natural-prop Δ (wkₜ ρ n) (wkNatural (toWk ρ) natN)
  wkNatural-prop ρ ⊢Δ suc n = wkTermℕ ρ ⊢Δ n
  wkNatural-prop ρ ⊢Δ zero n = n
  wkNatural-prop ρ ⊢Δ (ne x) (neₜ ⊢t t≡t) = neₜ (T.wkTerm ρ ⊢Δ ⊢t) (≅ₜ-wk ρ ⊢Δ t≡t)

mutual
  wkEqTermℕ : ∀ {Γ Δ t u} (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ)
            → Γ ⊩ℕ t ≡ u ∷ℕ
            → Δ ⊩ℕ U.wk (toWk ρ) t ≡ U.wk (toWk ρ) u ∷ℕ
  wkEqTermℕ ρ ⊢Δ (ℕₜ₌ k k' d d' t≡u prop) =
    ℕₜ₌ (U.wk (toWk ρ) k) (U.wk (toWk ρ) k') (wkRed:*:Term ρ ⊢Δ d)
        (wkRed:*:Term ρ ⊢Δ d') (≅ₜ-wk ρ ⊢Δ t≡u)
        (wk[Natural]-prop ρ ⊢Δ prop)

  wk[Natural]-prop : ∀ {Γ Δ n n'} (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ)
                   → [Natural]-prop Γ n n'
                   → [Natural]-prop Δ (U.wk (toWk ρ) n) (U.wk (toWk ρ) n')
  wk[Natural]-prop ρ ⊢Δ (suc [n≡n']) = suc (wkEqTermℕ ρ ⊢Δ [n≡n'])
  wk[Natural]-prop ρ ⊢Δ zero = zero
  wk[Natural]-prop ρ ⊢Δ (ne x x₁ n≡n') =
    ne (wkNeutral (toWk ρ) x) (wkNeutral (toWk ρ) x₁) (≅ₜ-wk ρ ⊢Δ n≡n')

wk : ∀ {l Γ Δ A} → (ρ : Γ ⊆ Δ) → ⊢ Δ → Γ ⊩⟨ l ⟩ A → Δ ⊩⟨ l ⟩ wkₜ ρ A
wk ρ ⊢Δ (U' l' l< ⊢Γ) = U (U l' l< ⊢Δ)
wk ρ ⊢Δ (ℕ D) = ℕ (wkRed:*: ρ ⊢Δ D)
wk ρ ⊢Δ (ne' K D neK K≡K) =
  ne' (wkₜ ρ K) (wkRed:*: ρ ⊢Δ D) (wkNeutral (toWk ρ) neK) (≅-wk ρ ⊢Δ K≡K)
wk {l} {Γ} {Δ} ρ ⊢Δ (Π' F G D ⊢F ⊢G A≡A [F] [G] G-ext) =
  let ⊢ρF = T.wk ρ ⊢Δ ⊢F
      [F]' : ∀ {E} (η : Δ ⊆ E) (η′ : Γ ⊆ Δ) (⊢E : ⊢ E)
           → E ⊩⟨ l ⟩ wkₜ η (wkₜ η′ F)
      [F]' η η′ ⊢E = irrelevance'
                              (wk-comp-comm η η′)
                              ([F] (η •ₜ η′) ⊢E)
      [a]' : ∀ {E a} (η : Δ ⊆ E) (η′ : Γ ⊆ Δ) (⊢E : ⊢ E)
             ([a] : E ⊩⟨ l ⟩ a ∷ wkₜ η (wkₜ η′ F) / [F]' η η′ ⊢E)
           → E ⊩⟨ l ⟩ a ∷ wkₜ (η •ₜ η′) F / [F] (η •ₜ η′) ⊢E
      [a]' η η′ ⊢E [a] = irrelevanceTerm' (PE.sym (wk-comp-comm η η′))
                                          ([F]' η η′ ⊢E) ([F] (η •ₜ η′) ⊢E) [a]
      [G]' : ∀ {E a} (η : Δ ⊆ E) (η′ : Γ ⊆ Δ) (⊢E : ⊢ E)
             ([a] : E ⊩⟨ l ⟩ a ∷ wkₜ η (wkₜ η′ F) / [F]' η η′ ⊢E)
           → E ⊩⟨ l ⟩ wkLiftₜ (η •ₜ η′) G [ a ]
      [G]' η η′ ⊢E [a] = [G] (η •ₜ η′) ⊢E ([a]' η η′ ⊢E [a])
  in  Π (Π (wkₜ ρ F) (wkLiftₜ ρ G) (T.wkRed:*: ρ ⊢Δ D) ⊢ρF
           (T.wk (lift ρ) (⊢Δ ∙ ⊢ρF) ⊢G)
           (≅-wk ρ ⊢Δ A≡A)
           (λ ρ₁ ⊢Δ₁ → irrelevance' (wk-comp-comm ρ₁ ρ)
                                    ([F] (ρ₁ •ₜ ρ) ⊢Δ₁))
           (λ ρ₁ ⊢Δ₁ [a] → irrelevance' (wk-comp-comm-subst ρ₁ ρ G)
                                        ([G]' ρ₁ ρ ⊢Δ₁ [a]))
           (λ ρ₁ ⊢Δ₁ [a] [b] [a≡b] →
              let [a≡b]' = irrelevanceEqTerm' (PE.sym (wk-comp-comm ρ₁ ρ))
                                              ([F]' ρ₁ ρ ⊢Δ₁)
                                              ([F] (ρ₁ •ₜ ρ) ⊢Δ₁)
                                              [a≡b]
              in  irrelevanceEq'' (wk-comp-comm-subst ρ₁ ρ G)
                                  (wk-comp-comm-subst ρ₁ ρ G)
                                  ([G]' ρ₁ ρ ⊢Δ₁ [a])
                                  (irrelevance'
                                            (wk-comp-comm-subst ρ₁ ρ G)
                                            ([G]' ρ₁ ρ ⊢Δ₁ [a]))
                                  (G-ext (ρ₁ •ₜ ρ) ⊢Δ₁
                                         ([a]' ρ₁ ρ ⊢Δ₁ [a])
                                         ([a]' ρ₁ ρ ⊢Δ₁ [b])
                                         [a≡b]')))
wk ρ ⊢Δ (emb 0<1 x) = emb 0<1 (wk ρ ⊢Δ x)

wkEq : ∀ {l Γ Δ A B} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ)
       ([A] : Γ ⊩⟨ l ⟩ A)
     → Γ ⊩⟨ l ⟩ A ≡ B / [A]
     → Δ ⊩⟨ l ⟩ wkₜ ρ A ≡ wkₜ ρ B / wk ρ ⊢Δ [A]
wkEq ρ ⊢Δ (U' _ _ _) PE.refl = PE.refl
wkEq ρ ⊢Δ (ℕ D) A≡B = wkRed* ρ ⊢Δ A≡B
wkEq ρ ⊢Δ (ne' _ _ _ _) (ne₌ M D' neM K≡M) =
  ne₌ (U.wk (toWk ρ) M) (wkRed:*: ρ ⊢Δ D')
      (wkNeutral (toWk ρ) neM) (≅-wk ρ ⊢Δ K≡M)
wkEq ρ ⊢Δ (Π' F G D ⊢F ⊢G A≡A [F] [G] G-ext)
          (Π₌ F' G' D' A≡B [F≡F'] [G≡G']) =
  -- TODO Minimize duplicates
  Π₌ (wkₜ ρ F') (wkLiftₜ ρ G') (T.wkRed* ρ ⊢Δ D') (≅-wk ρ ⊢Δ A≡B)
     (λ ρ₁ ⊢Δ₁ → irrelevanceEq'' (wk-comp-comm ρ₁ ρ)
                                 (wk-comp-comm ρ₁ ρ)
                                 ([F] (ρ₁ •ₜ ρ) ⊢Δ₁)
                                 (irrelevance' (wk-comp-comm ρ₁ ρ)
                                               ([F] (ρ₁ •ₜ ρ) ⊢Δ₁))
                                 ([F≡F'] (ρ₁ •ₜ ρ) ⊢Δ₁))
     (λ ρ₁ ⊢Δ₁ [a] →
        let [a]' = irrelevanceTerm' (PE.sym (wk-comp-comm ρ₁ ρ))
                                    (irrelevance' (wk-comp-comm ρ₁ ρ)
                                                  ([F] (ρ₁ •ₜ ρ) ⊢Δ₁))
                                    ([F] (ρ₁ •ₜ ρ) ⊢Δ₁) [a]
        in  irrelevanceEq'' (wk-comp-comm-subst ρ₁ ρ G)
                            (wk-comp-comm-subst ρ₁ ρ G')
                            ([G] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]')
                            (irrelevance' (wk-comp-comm-subst ρ₁ ρ G)
                                          ([G] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]'))
                            ([G≡G'] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]'))
wkEq ρ ⊢Δ (emb 0<1 x) A≡B = wkEq ρ ⊢Δ x A≡B

wkTerm : ∀ {l Γ Δ A t} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ)
         ([A] : Γ ⊩⟨ l ⟩ A)
       → Γ ⊩⟨ l ⟩ t ∷ A / [A]
       → Δ ⊩⟨ l ⟩ wkₜ ρ t ∷ wkₜ ρ A / wk ρ ⊢Δ [A]
wkTerm ρ ⊢Δ (U' .⁰ 0<1 ⊢Γ) (Uₜ ⊢t t≡t ⊩t) =
  Uₜ (T.wkTerm ρ ⊢Δ ⊢t) (≅ₜ-wk ρ ⊢Δ t≡t) (wk ρ ⊢Δ ⊩t)
wkTerm ρ ⊢Δ (ℕ D) [t] = wkTermℕ ρ ⊢Δ [t]
wkTerm ρ ⊢Δ (ne' K D neK K≡K) (neₜ ⊢t t≡t) =
  neₜ (T.wkTerm ρ ⊢Δ ⊢t) (≅ₜ-wk ρ ⊢Δ t≡t)
wkTerm ρ ⊢Δ (Π' F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Πₜ ⊢t t≡t [ta≡tb] [ta]) =
  T.wkTerm ρ ⊢Δ ⊢t
  , ≅ₜ-wk ρ ⊢Δ t≡t
  -- TODO Minimize duplicates
  , (λ ρ₁ ⊢Δ₁ [a] [b] [a≡b] →
       let F-compEq = PE.sym (wk-comp-comm ρ₁ ρ)
           G-compEq = wk-comp-comm-subst ρ₁ ρ G
           [F]₁ = [F] (ρ₁ •ₜ ρ) ⊢Δ₁
           [F]₂ = irrelevance' (wk-comp-comm ρ₁ ρ) [F]₁
           [a]' = irrelevanceTerm' F-compEq [F]₂ [F]₁ [a]
           [b]' = irrelevanceTerm' F-compEq [F]₂ [F]₁ [b]
           [G]₁ = [G] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]'
           [G]₂ = irrelevance' G-compEq [G]₁
           [a≡b]' = irrelevanceEqTerm' F-compEq [F]₂ [F]₁ [a≡b]
       in  irrelevanceEqTerm'' (PE.cong (λ x → x ∘ _) (wk-comp-comm ρ₁ ρ))
                               (PE.cong (λ x → x ∘ _) (wk-comp-comm ρ₁ ρ))
                               G-compEq
                               [G]₁ [G]₂
                               ([ta≡tb] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]' [b]' [a≡b]'))
  , (λ ρ₁ ⊢Δ₁ [a] →
       let [F]₁ = [F] (ρ₁ •ₜ ρ) ⊢Δ₁
           [F]₂ = irrelevance' (wk-comp-comm ρ₁ ρ) [F]₁
           [a]' = irrelevanceTerm' (PE.sym (wk-comp-comm ρ₁ ρ)) [F]₂ [F]₁ [a]
           [G]₁ = [G] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]'
           [G]₂ = irrelevance' (wk-comp-comm-subst ρ₁ ρ G) [G]₁
       in  irrelevanceTerm'' (wk-comp-comm-subst ρ₁ ρ G)
                             (PE.cong (λ x → x ∘ _) (wk-comp-comm ρ₁ ρ))
                             [G]₁ [G]₂ ([ta] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]'))
wkTerm ρ ⊢Δ (emb 0<1 x) t = wkTerm ρ ⊢Δ x t

wkEqTerm : ∀ {l Γ Δ A t u} → (ρ : Γ ⊆ Δ) (⊢Δ : ⊢ Δ)
           ([A] : Γ ⊩⟨ l ⟩ A)
         → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
         → Δ ⊩⟨ l ⟩ wkₜ ρ t ≡ wkₜ ρ u ∷ wkₜ ρ A / wk ρ ⊢Δ [A]
wkEqTerm ρ ⊢Δ (U' .⁰ 0<1 ⊢Γ) (Uₜ₌ ⊢t ⊢u t≡u ⊩t ⊩u [t≡u]) =
  Uₜ₌ (T.wkTerm ρ ⊢Δ ⊢t) (T.wkTerm ρ ⊢Δ ⊢u) (≅ₜ-wk ρ ⊢Δ t≡u)
      (wk ρ ⊢Δ ⊩t) (wk ρ ⊢Δ ⊩u) (wkEq ρ ⊢Δ ⊩t [t≡u])
wkEqTerm ρ ⊢Δ (ℕ D) [t≡u] = wkEqTermℕ ρ ⊢Δ [t≡u]
wkEqTerm ρ ⊢Δ (ne' _ _ _ _) t≡u = ≅ₜ-wk ρ ⊢Δ t≡u
wkEqTerm ρ ⊢Δ (Π' F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Πₜ₌ t≡u ⊩t ⊩u [t≡u]) =
  -- TODO Minimize duplicates
  let [A] = Π' F G D ⊢F ⊢G A≡A [F] [G] G-ext
  in  ≅ₜ-wk ρ ⊢Δ t≡u , wkTerm ρ ⊢Δ [A] ⊩t , wkTerm ρ ⊢Δ [A] ⊩u
  ,   (λ ρ₁ ⊢Δ₁ [a] →
         let [F]₁ = [F] (ρ₁ •ₜ ρ) ⊢Δ₁
             [F]₂ = irrelevance' (wk-comp-comm ρ₁ ρ) [F]₁
             [a]' = irrelevanceTerm' (PE.sym (wk-comp-comm ρ₁ ρ)) [F]₂ [F]₁ [a]
             [G]₁ = [G] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]'
             [G]₂ = irrelevance' (wk-comp-comm-subst ρ₁ ρ G) [G]₁
         in  irrelevanceEqTerm'' (PE.cong (λ y → y ∘ _) (wk-comp-comm ρ₁ ρ))
                                 (PE.cong (λ y → y ∘ _) (wk-comp-comm ρ₁ ρ))
                                 (wk-comp-comm-subst ρ₁ ρ G)
                                 [G]₁ [G]₂
                                 ([t≡u] (ρ₁ •ₜ ρ) ⊢Δ₁ [a]'))
wkEqTerm ρ ⊢Δ (emb 0<1 x) t≡u = wkEqTerm ρ ⊢Δ x t≡u
