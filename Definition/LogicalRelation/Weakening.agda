------------------------------------------------------------------------
-- The logical relation is closed under weakening
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Weakening
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped M as U hiding (wk; K)
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Typed.Weakening R as T hiding (wk; wkEq; wkTerm; wkEqTerm)
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Weakening.Restricted R

open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

private
  variable
    m n : Nat
    ρ : Wk m n
    Γ Δ : Con Term m
    A B t u : Term m
    l : Universe-level
    s : Strength

-- Weakening of neutrals in WHNF

wkEqTermNe : ∀ {k k′ A} → ρ ∷ʷ Δ ⊇ Γ
           → Γ ⊩neNf k ≡ k′ ∷ A → Δ ⊩neNf U.wk ρ k ≡ U.wk ρ k′ ∷ U.wk ρ A
wkEqTermNe {ρ} [ρ] (neNfₜ₌ inc neK neM k≡m) =
  neNfₜ₌ inc (wkNeutral ρ neK) (wkNeutral ρ neM) (~-wk [ρ] k≡m)

-- Weakening of reducible natural numbers

mutual
  wkEqTermℕ : ∀ {t u} → ρ ∷ʷ Δ ⊇ Γ
            → Γ ⊩ℕ t ≡ u ∷ℕ
            → Δ ⊩ℕ U.wk ρ t ≡ U.wk ρ u ∷ℕ
  wkEqTermℕ {ρ = ρ} [ρ] (ℕₜ₌ k k′ d d′ t≡u prop) =
    ℕₜ₌ (U.wk ρ k) (U.wk ρ k′) (wkRed*Term [ρ] d)
        (wkRed*Term [ρ] d′) (≅ₜ-wk [ρ] t≡u)
        (wk[Natural]-prop [ρ] prop)

  wk[Natural]-prop : ∀ {n n′} → ρ ∷ʷ Δ ⊇ Γ
                   → [Natural]-prop Γ n n′
                   → [Natural]-prop Δ (U.wk ρ n) (U.wk ρ n′)
  wk[Natural]-prop ρ (sucᵣ [n≡n′]) = sucᵣ (wkEqTermℕ ρ [n≡n′])
  wk[Natural]-prop ρ zeroᵣ = zeroᵣ
  wk[Natural]-prop ρ (ne x) = ne (wkEqTermNe ρ x)

-- Empty

wk[Empty]-prop : ∀ {n n′} → ρ ∷ʷ Δ ⊇ Γ
  → [Empty]-prop Γ n n′
  → [Empty]-prop Δ (U.wk ρ n) (U.wk ρ n′)
wk[Empty]-prop ρ (ne x) = ne (wkEqTermNe ρ x)

wkEqTermEmpty : ∀ {t u} → ρ ∷ʷ Δ ⊇ Γ
  → Γ ⊩Empty t ≡ u ∷Empty
  → Δ ⊩Empty U.wk ρ t ≡ U.wk ρ u ∷Empty
wkEqTermEmpty {ρ} [ρ] (Emptyₜ₌ k k′ d d′ t≡u prop) =
  Emptyₜ₌ (U.wk ρ k) (U.wk ρ k′) (wkRed*Term [ρ] d)
      (wkRed*Term [ρ] d′) (≅ₜ-wk [ρ] t≡u) (wk[Empty]-prop [ρ] prop)

-- Unit

wk[Unitʷ]-prop : ∀ {t u} → ρ ∷ʷ Δ ⊇ Γ
               → [Unitʷ]-prop Γ l t u
               → [Unitʷ]-prop Δ l (U.wk ρ t) (U.wk ρ u)
wk[Unitʷ]-prop [ρ] starᵣ = starᵣ
wk[Unitʷ]-prop [ρ] (ne x) = ne (wkEqTermNe [ρ] x)

-- Weakening for [Unit]-prop.
wk[Unit]-prop :
  ρ ∷ʷ Δ ⊇ Γ →
  [Unit]-prop Γ l s t u →
  [Unit]-prop Δ l s (U.wk ρ t) (U.wk ρ u)
wk[Unit]-prop ρ (Unitₜ₌ʷ prop no-η) =
  Unitₜ₌ʷ (wk[Unitʷ]-prop ρ prop) no-η
wk[Unit]-prop ρ (Unitₜ₌ˢ η) =
  Unitₜ₌ˢ η

-- Weakening of the logical relation

wk :
  {ρ : Wk m n} →
  ρ ∷ʷʳ Δ ⊇ Γ → Γ ⊩⟨ l ⟩ A → Δ ⊩⟨ l ⟩ U.wk ρ A

wkEq :
  ([ρ] : ρ ∷ʷʳ Δ ⊇ Γ) ([A] : Γ ⊩⟨ l ⟩ A) →
  Γ ⊩⟨ l ⟩ A ≡ B / [A] →
  Δ ⊩⟨ l ⟩ U.wk ρ A ≡ U.wk ρ B / wk [ρ] [A]

wkEqTerm :
  ([ρ] : ρ ∷ʷʳ Δ ⊇ Γ) ([A] : Γ ⊩⟨ l ⟩ A) →
  Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A] →
  Δ ⊩⟨ l ⟩ U.wk ρ t ≡ U.wk ρ u ∷ U.wk ρ A / wk [ρ] [A]

wkTerm :
  ([ρ] : ρ ∷ʷʳ Δ ⊇ Γ) ([A] : Γ ⊩⟨ l ⟩ A) →
   Γ ⊩⟨ l ⟩ t ∷ A / [A] →
   Δ ⊩⟨ l ⟩ U.wk ρ t ∷ U.wk ρ A / wk [ρ] [A]
wkTerm ⊩A ⊩t = wkEqTerm ⊩A ⊩t

wk ρ (Uᵣ′ l′ l< D) = Uᵣ′ l′ l< (wkRed* (∷ʷʳ⊇→∷ʷ⊇ ρ) D)
wk ρ (ℕᵣ D) = ℕᵣ (wkRed* (∷ʷʳ⊇→∷ʷ⊇ ρ) D)
wk ρ (Emptyᵣ D) = Emptyᵣ (wkRed* (∷ʷʳ⊇→∷ʷ⊇ ρ) D)
wk ρ (Unitᵣ′ l′ l′≤ D ok) =
  Unitᵣ′ l′ l′≤ (wkRed* (∷ʷʳ⊇→∷ʷ⊇ ρ) D) ok
wk {ρ} [ρ] (ne′ inc _ D neK K≡K) =
  let [ρ] = ∷ʷʳ⊇→∷ʷ⊇ [ρ] in
  ne′ inc (U.wk ρ _) (wkRed* [ρ] D) (wkNeutral ρ neK) (≅-wk [ρ] K≡K)
wk {m} {Δ} {Γ} {l} {A} {ρ} [ρ] (Πᵣ′ F G D A≡A [F] [G] G-ext ok) =
  let [ρ]′ = ∷ʷʳ⊇→∷ʷ⊇ [ρ]
      [F]′ : ∀ {k} {ρ : Wk k m} {ρ′ E}
             ([ρ] : ρ ∷ʷʳ E ⊇ Δ) ([ρ′] : ρ′ ∷ʷʳ Δ ⊇ Γ)
           → E ⊩⟨ l ⟩ U.wk ρ (U.wk ρ′ F)
      [F]′ {_} {ρ} {ρ′} [ρ] [ρ′] =
        irrelevance′ (PE.sym (wk-comp ρ ρ′ F)) ([F] ([ρ] •ₜʷʳ [ρ′]))
      [a]′ : ∀ {k} {ρ : Wk k m} {ρ′ E a}
             ([ρ] : ρ ∷ʷʳ E ⊇ Δ) ([ρ′] : ρ′ ∷ʷʳ Δ ⊇ Γ)
             ([a] : E ⊩⟨ l ⟩ a ∷ U.wk ρ (U.wk ρ′ F) / [F]′ [ρ] [ρ′])
           → E ⊩⟨ l ⟩ a ∷ U.wk (ρ • ρ′) F / [F] ([ρ] •ₜʷʳ [ρ′])
      [a]′ {_} {ρ} {ρ′} [ρ] [ρ′] [a] =
        irrelevanceTerm′ (wk-comp ρ ρ′ F) ([F]′ [ρ] [ρ′]) ([F] _) [a]
      [G]′ : ∀ {k} {ρ : Wk k m} {ρ′} {E} {a}
             ([ρ] : ρ ∷ʷʳ E ⊇ Δ) ([ρ′] : ρ′ ∷ʷʳ Δ ⊇ Γ)
             ([a] : E ⊩⟨ l ⟩ a ∷ U.wk ρ (U.wk ρ′ F) / [F]′ [ρ] [ρ′])
           → E ⊩⟨ l ⟩ U.wk (lift (ρ • ρ′)) G [ a ]₀
      [G]′ {_} η η′ [a] = [G] _ ([a]′ η η′ [a])
  in  Πᵣ′ (U.wk ρ F) (U.wk (lift ρ) G) (T.wkRed* [ρ]′ D)
           (≅-wk [ρ]′ A≡A)
           (λ {_} {ρ₁} [ρ₁] → irrelevance′ (PE.sym (wk-comp ρ₁ ρ F))
                                ([F] _))
           (λ {_} {ρ₁} [ρ₁] [a] → irrelevance′ (wk-comp-subst ρ₁ ρ G)
                                    ([G]′ [ρ₁] [ρ] [a]))
           (λ {_} {ρ₁} [ρ₁] [a] [b] [a≡b] →
              let [a≡b]′ = irrelevanceEqTerm′ (wk-comp ρ₁ ρ F)
                             ([F]′ [ρ₁] [ρ]) ([F] _) [a≡b]
              in  irrelevanceEq″ (wk-comp-subst ρ₁ ρ G)
                                  (wk-comp-subst ρ₁ ρ G)
                                  ([G]′ [ρ₁] [ρ] [a])
                                  (irrelevance′
                                            (wk-comp-subst ρ₁ ρ G)
                                            ([G]′ [ρ₁] [ρ] [a]))
                                  (G-ext _
                                         ([a]′ [ρ₁] [ρ] [a])
                                         ([a]′ [ρ₁] [ρ] [b])
                                         [a≡b]′))
           ok
wk {m} {Δ} {Γ} {l} {A} {ρ} [ρ] (Σᵣ′ F G D A≡A [F] [G] G-ext ok) =
  let [ρ]′ = ∷ʷʳ⊇→∷ʷ⊇ [ρ]
      [F]′ : ∀ {k} {ρ : Wk k m} {ρ′ E}
             ([ρ] : ρ ∷ʷʳ E ⊇ Δ) ([ρ′] : ρ′ ∷ʷʳ Δ ⊇ Γ)
           → E ⊩⟨ l ⟩ U.wk ρ (U.wk ρ′ F)
      [F]′ {_} {ρ} {ρ′} [ρ] [ρ′] =
        irrelevance′ (PE.sym (wk-comp ρ ρ′ F)) ([F] ([ρ] •ₜʷʳ [ρ′]))
      [a]′ : ∀ {k} {ρ : Wk k m} {ρ′ E a}
             ([ρ] : ρ ∷ʷʳ E ⊇ Δ) ([ρ′] : ρ′ ∷ʷʳ Δ ⊇ Γ)
             ([a] : E ⊩⟨ l ⟩ a ∷ U.wk ρ (U.wk ρ′ F) / [F]′ [ρ] [ρ′])
           → E ⊩⟨ l ⟩ a ∷ U.wk (ρ • ρ′) F / [F] ([ρ] •ₜʷʳ [ρ′])
      [a]′ {_} {ρ} {ρ′} [ρ] [ρ′] [a] =
        irrelevanceTerm′ (wk-comp ρ ρ′ F) ([F]′ [ρ] [ρ′]) ([F] _) [a]
      [G]′ : ∀ {k} {ρ : Wk k m} {ρ′ E a}
             ([ρ] : ρ ∷ʷʳ E ⊇ Δ) ([ρ′] : ρ′ ∷ʷʳ Δ ⊇ Γ)
             ([a] : E ⊩⟨ l ⟩ a ∷ U.wk ρ (U.wk ρ′ F) / [F]′ [ρ] [ρ′])
           → E ⊩⟨ l ⟩ U.wk (lift (ρ • ρ′)) G [ a ]₀
      [G]′ {_} η η′ [a] = [G] _ ([a]′ η η′ [a])
  in  Σᵣ′ (U.wk ρ F) (U.wk (lift ρ) G) (T.wkRed* [ρ]′ D)
           (≅-wk [ρ]′ A≡A)
           (λ {_} {ρ₁} [ρ₁] → irrelevance′ (PE.sym (wk-comp ρ₁ ρ F))
                                ([F] _))
           (λ {_} {ρ₁} [ρ₁] [a] → irrelevance′ (wk-comp-subst ρ₁ ρ G)
                                    ([G]′ [ρ₁] [ρ] [a]))
           (λ {_} {ρ₁} [ρ₁] [a] [b] [a≡b] →
              let [a≡b]′ = irrelevanceEqTerm′ (wk-comp ρ₁ ρ F)
                             ([F]′ [ρ₁] [ρ]) ([F] _) [a≡b]
              in  irrelevanceEq″ (wk-comp-subst ρ₁ ρ G)
                                  (wk-comp-subst ρ₁ ρ G)
                                  ([G]′ [ρ₁] [ρ] [a])
                                  (irrelevance′
                                            (wk-comp-subst ρ₁ ρ G)
                                            ([G]′ [ρ₁] [ρ] [a]))
                                  (G-ext _
                                         ([a]′ [ρ₁] [ρ] [a])
                                         ([a]′ [ρ₁] [ρ] [b])
                                         [a≡b]′))
           ok
wk ρ∷⊇ (Idᵣ ⊩A) = Idᵣ (record
  { ⇒*Id  = wkRed* (∷ʷʳ⊇→∷ʷ⊇ ρ∷⊇) ⇒*Id
  ; ⊩Ty   = wk ρ∷⊇ ⊩Ty
  ; ⊩lhs  = wkTerm ρ∷⊇ ⊩Ty ⊩lhs
  ; ⊩rhs  = wkTerm ρ∷⊇ ⊩Ty ⊩rhs
  })
  where
  open _⊩ₗId_ ⊩A

wkEq ρ (Uᵣ′ l l< D) D′ = wkRed* (∷ʷʳ⊇→∷ʷ⊇ ρ) D′
wkEq ρ (ℕᵣ D) A≡B = wkRed* (∷ʷʳ⊇→∷ʷ⊇ ρ) A≡B
wkEq ρ (Emptyᵣ D) A≡B = wkRed* (∷ʷʳ⊇→∷ʷ⊇ ρ) A≡B
wkEq ρ (Unitᵣ′ _ _ D _) A≡B = wkRed* (∷ʷʳ⊇→∷ʷ⊇ ρ) A≡B
wkEq {ρ = ρ} [ρ] (ne′ _ _ _ _ _) (ne₌ inc M D′ neM K≡M) =
  let [ρ] = ∷ʷʳ⊇→∷ʷ⊇ [ρ] in
  ne₌ inc (U.wk ρ M) (wkRed* [ρ] D′) (wkNeutral ρ neM)
    (≅-wk [ρ] K≡M)
wkEq
  {ρ}
  [ρ] (Πᵣ′ F G D A≡A [F] [G] G-ext _) (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  let [ρ]′ = ∷ʷʳ⊇→∷ʷ⊇ [ρ] in
  B₌ (U.wk ρ F′)
     (U.wk (lift ρ) G′) (T.wkRed* [ρ]′ D′) (≅-wk [ρ]′ A≡B)
     (λ {_} {ρ₁} [ρ₁] → irrelevanceEq″ (PE.sym (wk-comp ρ₁ ρ F))
                          (PE.sym (wk-comp ρ₁ ρ F′))
                          ([F] ([ρ₁] •ₜʷʳ [ρ]))
                          (irrelevance′ (PE.sym (wk-comp ρ₁ ρ F))
                             ([F] _))
                          ([F≡F′] _))
     (λ {_} {ρ₁} [ρ₁] [a] →
        let [a]′ = irrelevanceTerm′ (wk-comp ρ₁ ρ F)
                     (irrelevance′ (PE.sym (wk-comp ρ₁ ρ F)) ([F] _))
                     ([F] _) [a]
        in  irrelevanceEq″ (wk-comp-subst ρ₁ ρ G)
                            (wk-comp-subst ρ₁ ρ G′)
                            ([G] _ [a]′)
                            (irrelevance′ (wk-comp-subst ρ₁ ρ G)
                                          ([G] _ [a]′))
                            ([G≡G′] _ [a]′))
wkEq
  {ρ}
  [ρ] (Σᵣ′ F G D A≡A [F] [G] G-ext _) (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  let [ρ]′ = ∷ʷʳ⊇→∷ʷ⊇ [ρ] in
  B₌ (U.wk ρ F′) (U.wk (lift ρ) G′) (T.wkRed* [ρ]′ D′) (≅-wk [ρ]′ A≡B)
     (λ {_} {ρ₁} [ρ₁] → irrelevanceEq″ (PE.sym (wk-comp ρ₁ ρ F))
                          (PE.sym (wk-comp ρ₁ ρ F′))
                          ([F] ([ρ₁] •ₜʷʳ [ρ]))
                          (irrelevance′ (PE.sym (wk-comp ρ₁ ρ F))
                                        ([F] _))
                          ([F≡F′] _))
     (λ {_} {ρ₁} [ρ₁] [a] →
        let [a]′ = irrelevanceTerm′ (wk-comp ρ₁ ρ F)
                     (irrelevance′ (PE.sym (wk-comp ρ₁ ρ F)) ([F] _))
                     ([F] _) [a]
        in  irrelevanceEq″ (wk-comp-subst ρ₁ ρ G)
                            (wk-comp-subst ρ₁ ρ G′)
                            ([G] _ [a]′)
                            (irrelevance′ (wk-comp-subst ρ₁ ρ G)
                                          ([G] _ [a]′))
                            ([G≡G′] _ [a]′))
wkEq ρ∷⊇ (Idᵣ ⊩A) A≡B = Id₌′
  (wkRed* (∷ʷʳ⊇→∷ʷ⊇ ρ∷⊇) ⇒*Id′)
  (wkEq ρ∷⊇ ⊩Ty Ty≡Ty′)
  (wkEqTerm ρ∷⊇ ⊩Ty lhs≡lhs′)
  (wkEqTerm ρ∷⊇ ⊩Ty rhs≡rhs′)
  where
  open _⊩ₗId_ ⊩A
  open _⊩ₗId_≡_/_ A≡B

wkEqTerm
  {ρ} {l = 1+ l′} [ρ] (Uᵣ′ l (≤ᵘ-step l<) D)
  (Uₜ₌ A B d d′ typeA typeB A≡B [t] [u] [t≡u]) =
  let wkET′ = wkEqTerm {ρ = ρ} [ρ] (Uᵣ′ l l< D)
                (Uₜ₌ A B d d′ typeA typeB A≡B [t] [u] [t≡u])
  in
  irrelevanceEqTerm (wk [ρ] (Uᵣ′ l l< D))
    (wk [ρ] (Uᵣ′ l (≤ᵘ-step l<) D)) wkET′
wkEqTerm
  {ρ} [ρ] (Uᵣ′ l ≤ᵘ-refl D)
  (Uₜ₌ A B d d′ typeA typeB A≡B [t] [u] [t≡u]) =
  let [ρ]′ = ∷ʷʳ⊇→∷ʷ⊇ [ρ] in
  Uₜ₌ (U.wk ρ A) (U.wk ρ B) (wkRed*Term [ρ]′ d) (wkRed*Term [ρ]′ d′)
      (wkType ρ typeA) (wkType ρ typeB) (≅ₜ-wk [ρ]′ A≡B) (wk [ρ] [t])
      (wk [ρ] [u]) (wkEq [ρ] [t] [t≡u])
wkEqTerm ρ (ℕᵣ D) [t≡u] = wkEqTermℕ (∷ʷʳ⊇→∷ʷ⊇ ρ) [t≡u]
wkEqTerm ρ (Emptyᵣ D) [t≡u] = wkEqTermEmpty (∷ʷʳ⊇→∷ʷ⊇ ρ) [t≡u]
wkEqTerm ρ (Unitᵣ′ _ _ _ _) (Unitₜ₌ _ _ ↘v ↘w prop) =
  let ρ = ∷ʷʳ⊇→∷ʷ⊇ ρ in
  Unitₜ₌ _ _ (wkRed↘Term ρ ↘v) (wkRed↘Term ρ ↘w) (wk[Unit]-prop ρ prop)
wkEqTerm {ρ} [ρ] (ne′ _ _ D neK K≡K) (neₜ₌ k m d d′ nf) =
  let [ρ]′ = ∷ʷʳ⊇→∷ʷ⊇ [ρ] in
  neₜ₌ (U.wk ρ k) (U.wk ρ m) (wkRed*Term [ρ]′ d)
    (wkRed*Term [ρ]′ d′) (wkEqTermNe [ρ]′ nf)
wkEqTerm {ρ} [ρ] (Πᵣ′ F G _ _ [F] [G] _ _)
  (Πₜ₌ f g d d′ funcF funcG f≡g [f≡g]) =
  let [ρ]′ = ∷ʷʳ⊇→∷ʷ⊇ [ρ]
  in  Πₜ₌ (U.wk ρ f) (U.wk ρ g)
          (wkRed*Term [ρ]′ d) (wkRed*Term [ρ]′ d′)
          (wkFunction ρ funcF) (wkFunction ρ funcG) (≅ₜ-wk [ρ]′ f≡g)
          (λ {_} {ρ₁} [ρ₁] ⊩v ⊩w v≡w →
             let eq   = wk-comp ρ₁ ρ F
                 [F]₁ = [F] _
                 [F]₂ = irrelevance′ (PE.sym eq) [F]₁
                 ⊩v′  = irrelevanceTerm′ eq [F]₂ [F]₁ ⊩v
                 [G]₁ = [G] _ ⊩v′
                 [G]₂ = irrelevance′ (wk-comp-subst ρ₁ ρ G) [G]₁
             in  irrelevanceEqTerm″ (PE.cong (λ y → y ∘ _) (PE.sym (wk-comp ρ₁ ρ _)))
                                    (PE.cong (λ y → y ∘ _) (PE.sym (wk-comp ρ₁ ρ _)))
                                    (wk-comp-subst ρ₁ ρ G)
                                    [G]₁ [G]₂
                   ([f≡g] _ ⊩v′ (irrelevanceTerm′ eq [F]₂ [F]₁ ⊩w)
                      (irrelevanceEqTerm′ eq [F]₂ [F]₁ v≡w)))
wkEqTerm {ρ} [ρ] [A]@(Bᵣ′ BΣʷ F G _ _ [F] [G] _ _)
         (Σₜ₌ p r d d′ (prodₙ {t = p₁}) prodₙ p≅r
            (PE.refl , PE.refl , PE.refl , PE.refl ,
             [p₁] , [r₁] , [fst≡] , [snd≡])) =
  let [ρ]′ = ∷ʷʳ⊇→∷ʷ⊇ [ρ]
      ρidF≡idρF = begin
                    U.wk ρ (U.wk id F)
                  ≡⟨ PE.cong (U.wk ρ) (wk-id F) ⟩
                    U.wk ρ F
                  ≡⟨ PE.sym (wk-id (U.wk ρ F)) ⟩
                    U.wk id (U.wk ρ F)
                  ∎
      [ρF] = irrelevance′ (PE.sym (wk-comp id ρ F)) ([F] [ρ])
      [ρp₁] = wkTerm [ρ] ([F] _) [p₁]
      [ρp₁]′ = irrelevanceTerm′
                  ρidF≡idρF
                  (wk [ρ] ([F] _)) [ρF]
                  [ρp₁]
      [ρr₁] = wkTerm [ρ] ([F] _) [r₁]
      [ρr₁]′ = irrelevanceTerm′
                  ρidF≡idρF
                  (wk [ρ] ([F] _)) [ρF]
                  [ρr₁]
      [ρfst≡] = wkEqTerm [ρ] ([F] _) [fst≡]
      [ρfst≡]′ = irrelevanceEqTerm′
                   ρidF≡idρF
                   (wk [ρ] ([F] _)) [ρF]
                   [ρfst≡]
      [ρsnd≡] = wkEqTerm [ρ] ([G] _ [p₁]) [snd≡]
      [ρG]′ = irrelevance′ (wk-comp-subst id ρ G)
                ([G] [ρ]
                   (irrelevanceTerm′ (wk-comp id ρ F)
                      [ρF] ([F] [ρ]) [ρp₁]′))
      ρG-eq = λ t → (begin
                    U.wk ρ (U.wk (lift id) G [ t ]₀)
                  ≡⟨ PE.cong (λ x → U.wk ρ (x [ t ]₀)) (wk-lift-id G) ⟩
                    U.wk ρ (G [ t ]₀)
                  ≡⟨ wk-β G ⟩
                    (U.wk (lift ρ) G) [ U.wk ρ t ]₀
                  ≡⟨ PE.cong (λ x → x [ U.wk ρ t ]₀) (PE.sym (wk-lift-id (U.wk (lift ρ) G))) ⟩
                    (U.wk (lift id) (U.wk (lift ρ) G)) [ U.wk ρ t ]₀
                  ∎)
      [ρsnd≡]′ = irrelevanceEqTerm′
                  (ρG-eq p₁)
                  (wk [ρ] ([G] _ [p₁])) [ρG]′
                  [ρsnd≡]
  in  Σₜ₌ (U.wk ρ p) (U.wk ρ r)
          (wkRed*Term [ρ]′ d) (wkRed*Term [ρ]′ d′)
          (wkProduct ρ prodₙ) (wkProduct ρ prodₙ) (≅ₜ-wk [ρ]′ p≅r)
          (PE.refl , PE.refl , PE.refl , PE.refl ,
           irrelevanceTerm [ρF]
              (irrelevance′ (PE.sym (wk-comp id ρ F)) _) [ρp₁]′ ,
           irrelevanceTerm [ρF]
             (irrelevance′ (PE.sym (wk-comp id ρ F)) _) [ρr₁]′ ,
           irrelevanceEqTerm [ρF]
             (irrelevance′ (PE.sym (wk-comp id ρ F)) _) [ρfst≡]′ ,
           irrelevanceEqTerm [ρG]′
             (irrelevance′ (wk-comp-subst id ρ G) _) [ρsnd≡]′)
wkEqTerm
  {ρ} [ρ] [A]@(Bᵣ′ BΣʷ _ _ _ _ _ _ _ _)
  (Σₜ₌ p r d d′ (ne x) (ne y) p≅r (inc , p~r)) =
  let [ρ]′ = ∷ʷʳ⊇→∷ʷ⊇ [ρ]
  in  Σₜ₌ (U.wk ρ p) (U.wk ρ r)
          (wkRed*Term [ρ]′ d) (wkRed*Term [ρ]′ d′)
          (wkProduct ρ (ne x)) (wkProduct ρ (ne y)) (≅ₜ-wk [ρ]′ p≅r)
          (inc , ~-wk [ρ]′ p~r)
wkEqTerm
  {ρ} [ρ] [A]@(Bᵣ′ BΣˢ F G _ _ [F] [G] _ _)
  (Σₜ₌ p r d d′ pProd rProd p≅r ([fstp] , [fstr] , [fst≡] , [snd≡])) =
  let [ρ]′ = ∷ʷʳ⊇→∷ʷ⊇ [ρ]
      ρidF≡idρF = begin
                    U.wk ρ (U.wk id F)
                  ≡⟨ PE.cong (U.wk ρ) (wk-id F) ⟩
                    U.wk ρ F
                  ≡⟨ PE.sym (wk-id (U.wk ρ F)) ⟩
                    U.wk id (U.wk ρ F)
                  ∎
      [ρF] = irrelevance′ (PE.sym (wk-comp id ρ F)) ([F] [ρ])
      [ρfstp] = wkTerm [ρ] ([F] _) [fstp]
      [ρfstp]′ = irrelevanceTerm′
                  ρidF≡idρF
                  (wk [ρ] ([F] _)) [ρF]
                  [ρfstp]
      [ρfstr] = wkTerm [ρ] ([F] _) [fstr]
      [ρfstr]′ = irrelevanceTerm′
                  ρidF≡idρF
                  (wk [ρ] ([F] _)) [ρF]
                  [ρfstr]
      [ρfst≡] = wkEqTerm [ρ] ([F] _) [fst≡]
      [ρfst≡]′ = irrelevanceEqTerm′
                   ρidF≡idρF
                   (wk [ρ] ([F] _)) [ρF]
                   [ρfst≡]
      [ρsnd≡] = wkEqTerm [ρ] ([G] _ [fstp]) [snd≡]
      [ρG]′ = irrelevance′ (wk-comp-subst id ρ G)
                ([G] [ρ]
                   (irrelevanceTerm′ (wk-comp id ρ F)
                      [ρF] ([F] [ρ]) [ρfstp]′))
      [ρsnd≡]′ = irrelevanceEqTerm′
        (begin
           U.wk ρ (U.wk (lift id) G [ fst _ p ]₀)                    ≡⟨ PE.cong (λ x → U.wk ρ (x [ fst _ p ]₀)) (wk-lift-id G) ⟩
           U.wk ρ (G [ fst _ p ]₀)                                   ≡⟨ wk-β G ⟩
           (U.wk (lift ρ) G) [ fst _ (U.wk ρ p) ]₀                   ≡⟨ PE.cong (λ x → x [ fst _ (U.wk ρ p) ]₀)
                                                                         (PE.sym (wk-lift-id (U.wk (lift ρ) G))) ⟩
           (U.wk (lift id) (U.wk (lift ρ) G)) [ fst _ (U.wk ρ p) ]₀  ∎)
        (wk [ρ] ([G] _ [fstp])) [ρG]′
        [ρsnd≡]
  in  Σₜ₌ (U.wk ρ p) (U.wk ρ r)
          (wkRed*Term [ρ]′ d) (wkRed*Term [ρ]′ d′)
          (wkProduct ρ pProd) (wkProduct ρ rProd) (≅ₜ-wk [ρ]′ p≅r)
          (irrelevanceTerm [ρF]
             (irrelevance′ (PE.sym (wk-comp id ρ F)) _) [ρfstp]′ ,
           irrelevanceTerm [ρF]
             (irrelevance′ (PE.sym (wk-comp id ρ F)) _) [ρfstr]′ ,
           irrelevanceEqTerm [ρF]
             (irrelevance′ (PE.sym (wk-comp id ρ F)) _) [ρfst≡]′ ,
           irrelevanceEqTerm [ρG]′
             (irrelevance′ (wk-comp-subst id ρ G) _) [ρsnd≡]′)
wkEqTerm ρ∷⊇ (Idᵣ ⊩A) t≡u@(_ , _ , t⇒*t′ , u⇒*u′ , _) =
  let ρ∷⊇′ = ∷ʷʳ⊇→∷ʷ⊇ ρ∷⊇ in
    _ , _
  , wkRed*Term ρ∷⊇′ t⇒*t′
  , wkRed*Term ρ∷⊇′ u⇒*u′
  , (case ⊩Id≡∷-view-inhabited ⊩A t≡u of λ where
       (rfl₌ lhs≡rhs) →
           rflₙ , rflₙ
         , wkEqTerm ρ∷⊇ ⊩Ty lhs≡rhs
       (ne inc t′-n u′-n t′~u′) →
           ne (wkNeutral _ t′-n)
         , ne (wkNeutral _ u′-n)
         , inc
         , ~-wk ρ∷⊇′ t′~u′)
  where
  open _⊩ₗId_ ⊩A

-- Impossible cases
wkEqTerm _ (Bᵣ BΣʷ record{}) (Σₜ₌ _ _ _ _ prodₙ (ne _) _ ())
wkEqTerm _ (Bᵣ BΣʷ record{}) (Σₜ₌ _ _ _ _ (ne _) prodₙ _ ())
