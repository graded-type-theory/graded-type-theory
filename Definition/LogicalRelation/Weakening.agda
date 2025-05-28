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
open import Definition.Untyped.Whnf M type-variant
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Weakening R as T hiding (wk; wkEq; wkTerm; wkEqTerm)
open import Definition.Typed.Weakening.Definition R
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
    m n κ : Nat
    ρ : Wk m n
    ∇ : DCon (Term 0) κ
    Γ Δ : Con Term m
    A B t t₁ t₂ u : Term m
    l : Universe-level

-- Weakening of neutral terms in WHNF

wkTermNe : ∀ {k A} → ∇ » ρ ∷ʷ Δ ⊇ Γ
         → ∇ » Γ ⊩neNf k ∷ A → ∇ » Δ ⊩neNf U.wk ρ k ∷ U.wk ρ A
wkTermNe {ρ} [ρ] (neNfₜ neK k≡k) =
  neNfₜ (wkNeutral ρ neK) (~-wk [ρ] k≡k)

wkEqTermNe : ∀ {k k′ A} → ∇ » ρ ∷ʷ Δ ⊇ Γ
           → ∇ » Γ ⊩neNf k ≡ k′ ∷ A → ∇ » Δ ⊩neNf U.wk ρ k ≡ U.wk ρ k′ ∷ U.wk ρ A
wkEqTermNe {ρ} [ρ] (neNfₜ₌ neK neM k≡m) =
  neNfₜ₌ (wkNeutral ρ neK) (wkNeutral ρ neM) (~-wk [ρ] k≡m)

-- Weakening of reducible natural numbers

mutual
  wkTermℕ : ∀ {n} → ∇ » ρ ∷ʷ Δ ⊇ Γ
          → ∇ » Γ ⊩ℕ n ∷ℕ → ∇ » Δ ⊩ℕ U.wk ρ n ∷ℕ
  wkTermℕ {ρ} [ρ] (ℕₜ n d n≡n prop) =
    ℕₜ (U.wk ρ n) (wkRed*Term [ρ] d) (≅ₜ-wk [ρ] n≡n)
       (wkNatural-prop [ρ] prop)

  wkNatural-prop : ∀ {n} → ∇ » ρ ∷ʷ Δ ⊇ Γ
                 → Natural-prop ∇ Γ n
                 → Natural-prop ∇ Δ (U.wk ρ n)
  wkNatural-prop ρ (sucᵣ n) = sucᵣ (wkTermℕ ρ n)
  wkNatural-prop ρ zeroᵣ = zeroᵣ
  wkNatural-prop ρ (ne nf) = ne (wkTermNe ρ nf)

mutual
  wkEqTermℕ : ∀ {t u} → ∇ » ρ ∷ʷ Δ ⊇ Γ
            → ∇ » Γ ⊩ℕ t ≡ u ∷ℕ
            → ∇ » Δ ⊩ℕ U.wk ρ t ≡ U.wk ρ u ∷ℕ
  wkEqTermℕ {ρ = ρ} [ρ] (ℕₜ₌ k k′ d d′ t≡u prop) =
    ℕₜ₌ (U.wk ρ k) (U.wk ρ k′) (wkRed*Term [ρ] d)
        (wkRed*Term [ρ] d′) (≅ₜ-wk [ρ] t≡u)
        (wk[Natural]-prop [ρ] prop)

  wk[Natural]-prop : ∀ {n n′} → ∇ » ρ ∷ʷ Δ ⊇ Γ
                   → [Natural]-prop ∇ Γ n n′
                   → [Natural]-prop ∇ Δ (U.wk ρ n) (U.wk ρ n′)
  wk[Natural]-prop ρ (sucᵣ [n≡n′]) = sucᵣ (wkEqTermℕ ρ [n≡n′])
  wk[Natural]-prop ρ zeroᵣ = zeroᵣ
  wk[Natural]-prop ρ (ne nf) = ne (wkEqTermNe ρ nf)

-- Empty
wkTermEmpty : ∀ {n} → ∇ » ρ ∷ʷ Δ ⊇ Γ
  → ∇ » Γ ⊩Empty n ∷Empty → ∇ » Δ ⊩Empty U.wk ρ n ∷Empty
wkTermEmpty {ρ} [ρ] (Emptyₜ n d n≡n (ne nf)) =
  Emptyₜ (U.wk ρ n) (wkRed*Term [ρ] d) (≅ₜ-wk [ρ] n≡n)
     (ne (wkTermNe [ρ] nf))

wk[Empty]-prop : ∀ {n n′} → ∇ » ρ ∷ʷ Δ ⊇ Γ
  → [Empty]-prop ∇ Γ n n′
  → [Empty]-prop ∇ Δ (U.wk ρ n) (U.wk ρ n′)
wk[Empty]-prop ρ (ne nf) = ne (wkEqTermNe ρ nf)

wkEqTermEmpty : ∀ {t u} → ∇ » ρ ∷ʷ Δ ⊇ Γ
  → ∇ » Γ ⊩Empty t ≡ u ∷Empty
  → ∇ » Δ ⊩Empty U.wk ρ t ≡ U.wk ρ u ∷Empty
wkEqTermEmpty {ρ} [ρ] (Emptyₜ₌ k k′ d d′ t≡u prop) =
  Emptyₜ₌ (U.wk ρ k) (U.wk ρ k′) (wkRed*Term [ρ] d)
      (wkRed*Term [ρ] d′) (≅ₜ-wk [ρ] t≡u) (wk[Empty]-prop [ρ] prop)

-- Unit
wkUnit-prop : ∀ {s t} → ∇ » ρ ∷ʷ Δ ⊇ Γ
            → Unit-prop ∇ Γ l s t
            → Unit-prop ∇ Δ l s (U.wk ρ t)
wkUnit-prop [ρ] starᵣ = starᵣ
wkUnit-prop [ρ] (ne nf) = ne (wkTermNe [ρ] nf)

wk[Unitʷ]-prop : ∀ {t u} → ∇ » ρ ∷ʷ Δ ⊇ Γ
               → [Unitʷ]-prop ∇ Γ l t u
               → [Unitʷ]-prop ∇ Δ l (U.wk ρ t) (U.wk ρ u)
wk[Unitʷ]-prop [ρ] starᵣ = starᵣ
wk[Unitʷ]-prop [ρ] (ne nf) = ne (wkEqTermNe [ρ] nf)

wkTermUnit : ∀ {n s} → ∇ » ρ ∷ʷ Δ ⊇ Γ
           → ∇ » Γ ⊩Unit⟨ l , s ⟩ n ∷Unit → ∇ » Δ ⊩Unit⟨ l , s ⟩ U.wk ρ n ∷Unit
wkTermUnit {ρ} [ρ] (Unitₜ n d n≡n prop) =
  Unitₜ (U.wk ρ n) (wkRed*Term [ρ] d) (≅ₜ-wk [ρ] n≡n)
    (wkUnit-prop [ρ] prop)

wkEqTermUnit : ∀ {t u s} → ∇ » ρ ∷ʷ Δ ⊇ Γ
          → ∇ » Γ ⊩Unit⟨ l , s ⟩ t ≡ u ∷Unit
          → ∇ » Δ ⊩Unit⟨ l , s ⟩ U.wk ρ t ≡ U.wk ρ u ∷Unit
wkEqTermUnit [ρ] (Unitₜ₌ˢ ⊢t ⊢u ok) =
  Unitₜ₌ˢ (T.wkTerm [ρ] ⊢t) (T.wkTerm [ρ] ⊢u) ok
wkEqTermUnit {ρ} [ρ] (Unitₜ₌ʷ k k′ d d′ k≡k′ prop ok) =
  Unitₜ₌ʷ (U.wk ρ k) (U.wk ρ k′) (wkRed*Term [ρ] d)
    (wkRed*Term [ρ] d′) (≅ₜ-wk [ρ] k≡k′) (wk[Unitʷ]-prop [ρ] prop) ok

-- Weakening of the logical relation

wk :
  {∇ : DCon (Term 0) κ} {ρ : Wk m n} →
  ∇ » ρ ∷ʷʳ Δ ⊇ Γ → ∇ » Γ ⊩⟨ l ⟩ A → ∇ » Δ ⊩⟨ l ⟩ U.wk ρ A

wkEq :
  ([ρ] : ∇ » ρ ∷ʷʳ Δ ⊇ Γ) ([A] : ∇ » Γ ⊩⟨ l ⟩ A) →
  ∇ » Γ ⊩⟨ l ⟩ A ≡ B / [A] →
  ∇ » Δ ⊩⟨ l ⟩ U.wk ρ A ≡ U.wk ρ B / wk [ρ] [A]

wkTerm :
  ([ρ] : ∇ » ρ ∷ʷʳ Δ ⊇ Γ) ([A] : ∇ » Γ ⊩⟨ l ⟩ A) →
   ∇ » Γ ⊩⟨ l ⟩ t ∷ A / [A] →
   ∇ » Δ ⊩⟨ l ⟩ U.wk ρ t ∷ U.wk ρ A / wk [ρ] [A]

wkEqTerm :
  ([ρ] : ∇ » ρ ∷ʷʳ Δ ⊇ Γ) ([A] : ∇ » Γ ⊩⟨ l ⟩ A) →
  ∇ » Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A] →
  ∇ » Δ ⊩⟨ l ⟩ U.wk ρ t ≡ U.wk ρ u ∷ U.wk ρ A / wk [ρ] [A]

wk ρ (Uᵣ′ l′ l< D) = Uᵣ′ l′ l< (wkRed* (∷ʷʳ⊇→∷ʷ⊇ ρ) D)
wk ρ (ℕᵣ D) = ℕᵣ (wkRed* (∷ʷʳ⊇→∷ʷ⊇ ρ) D)
wk ρ (Emptyᵣ D) = Emptyᵣ (wkRed* (∷ʷʳ⊇→∷ʷ⊇ ρ) D)
wk ρ (Unitᵣ (Unitₜ D ok)) =
  Unitᵣ (Unitₜ (wkRed* (∷ʷʳ⊇→∷ʷ⊇ ρ) D) ok)
wk {ρ} [ρ] (ne′ _ D neK K≡K) =
  let [ρ] = ∷ʷʳ⊇→∷ʷ⊇ [ρ] in
  ne′ (U.wk ρ _) (wkRed* [ρ] D) (wkNeutral ρ neK) (≅-wk [ρ] K≡K)
wk {κ} {m} {Δ} {Γ} {l} {A} {∇} {ρ} [ρ] (Πᵣ′ F G D A≡A [F] [G] G-ext ok) =
  let [ρ]′ = ∷ʷʳ⊇→∷ʷ⊇ [ρ]
      [F]′ : ∀ {κ′} {ξ : DExt _ κ′ κ} {∇′ : DCon (Term 0) κ′} ([ξ] : ξ » ∇′ ⊇ ∇)
               {k} {ρ : Wk k m} {ρ′ E}
             ([ρ] : ∇′ » ρ ∷ʷʳ E ⊇ Δ) ([ρ′] : ∇′ » ρ′ ∷ʷʳ Δ ⊇ Γ)
           → ∇′ » E ⊩⟨ l ⟩ U.wk ρ (U.wk ρ′ F)
      [F]′ [ξ] {_} {ρ} {ρ′} [ρ] [ρ′] =
        irrelevance′ (PE.sym (wk-comp ρ ρ′ F)) ([F] [ξ] ([ρ] •ₜʷʳ [ρ′]))
      [a]′ : ∀ {κ′} {ξ : DExt _ κ′ κ} {∇′ : DCon (Term 0) κ′} ([ξ] : ξ » ∇′ ⊇ ∇)
               {k} {ρ : Wk k m} {ρ′ E a}
             ([ρ] : ∇′ » ρ ∷ʷʳ E ⊇ Δ) ([ρ′] : ∇′ » ρ′ ∷ʷʳ Δ ⊇ Γ)
             ([a] : ∇′ » E ⊩⟨ l ⟩ a ∷ U.wk ρ (U.wk ρ′ F) / [F]′ [ξ] [ρ] [ρ′])
           → ∇′ » E ⊩⟨ l ⟩ a ∷ U.wk (ρ • ρ′) F / [F] [ξ] ([ρ] •ₜʷʳ [ρ′])
      [a]′ [ξ] {_} {ρ} {ρ′} [ρ] [ρ′] [a] =
        irrelevanceTerm′ (wk-comp ρ ρ′ F) ([F]′ [ξ] [ρ] [ρ′]) ([F] [ξ] _) [a]
      [G]′ : ∀ {κ′} {ξ : DExt _ κ′ κ} {∇′ : DCon (Term 0) κ′} ([ξ] : ξ » ∇′ ⊇ ∇)
               {k} {ρ : Wk k m} {ρ′} {E} {a}
             ([ρ] : ∇′ » ρ ∷ʷʳ E ⊇ Δ) ([ρ′] : ∇′ » ρ′ ∷ʷʳ Δ ⊇ Γ)
             ([a] : ∇′ » E ⊩⟨ l ⟩ a ∷ U.wk ρ (U.wk ρ′ F) / [F]′ [ξ] [ρ] [ρ′])
           → ∇′ » E ⊩⟨ l ⟩ U.wk (lift (ρ • ρ′)) G [ a ]₀
      [G]′ [ξ] {_} η η′ [a] = [G] [ξ] _ ([a]′ [ξ] η η′ [a])
  in  Πᵣ′ (U.wk ρ F) (U.wk (lift ρ) G) (T.wkRed* [ρ]′ D)
           (≅-wk [ρ]′ A≡A)
           (λ [ξ] {_} {ρ₁} [ρ₁] → irrelevance′ (PE.sym (wk-comp ρ₁ ρ F))
                                    ([F] [ξ] _))
           (λ [ξ] {_} {ρ₁} [ρ₁] [a] → irrelevance′ (wk-comp-subst ρ₁ ρ G)
                                        ([G]′ [ξ] [ρ₁] (defn-wkWkʷʳ [ξ] [ρ]) [a]))
           (λ [ξ] {_} {ρ₁} [ρ₁] [a] [b] [a≡b] →
              let [ρ] = defn-wkWkʷʳ [ξ] [ρ]
                  [a≡b]′ = irrelevanceEqTerm′ (wk-comp ρ₁ ρ F)
                             ([F]′ [ξ] [ρ₁] [ρ]) ([F] [ξ] _) [a≡b]
              in  irrelevanceEq″ (wk-comp-subst ρ₁ ρ G)
                                  (wk-comp-subst ρ₁ ρ G)
                                  ([G]′ [ξ] [ρ₁] [ρ] [a])
                                  (irrelevance′
                                            (wk-comp-subst ρ₁ ρ G)
                                            ([G]′ [ξ] [ρ₁] [ρ] [a]))
                                  (G-ext _ _
                                         ([a]′ [ξ] [ρ₁] [ρ] [a])
                                         ([a]′ [ξ] [ρ₁] [ρ] [b])
                                         [a≡b]′))
           ok
wk {κ} {m} {Δ} {Γ} {l} {A} {∇} {ρ} [ρ] (Σᵣ′ F G D A≡A [F] [G] G-ext ok) =
  let [ρ]′ = ∷ʷʳ⊇→∷ʷ⊇ [ρ]
      [F]′ : ∀ {κ′} {ξ : DExt _ κ′ κ} {∇′ : DCon (Term 0) κ′} ([ξ] : ξ » ∇′ ⊇ ∇)
               {k} {ρ : Wk k m} {ρ′ E}
             ([ρ] : ∇′ » ρ ∷ʷʳ E ⊇ Δ) ([ρ′] : ∇′ » ρ′ ∷ʷʳ Δ ⊇ Γ)
           → ∇′ » E ⊩⟨ l ⟩ U.wk ρ (U.wk ρ′ F)
      [F]′ [ξ] {_} {ρ} {ρ′} [ρ] [ρ′] =
        irrelevance′ (PE.sym (wk-comp ρ ρ′ F)) ([F] [ξ] ([ρ] •ₜʷʳ [ρ′]))
      [a]′ : ∀ {κ′} {ξ : DExt _ κ′ κ} {∇′ : DCon (Term 0) κ′} ([ξ] : ξ » ∇′ ⊇ ∇)
               {k} {ρ : Wk k m} {ρ′ E a}
             ([ρ] : ∇′ » ρ ∷ʷʳ E ⊇ Δ) ([ρ′] : ∇′ » ρ′ ∷ʷʳ Δ ⊇ Γ)
             ([a] : ∇′ » E ⊩⟨ l ⟩ a ∷ U.wk ρ (U.wk ρ′ F) / [F]′ [ξ] [ρ] [ρ′])
           → ∇′ » E ⊩⟨ l ⟩ a ∷ U.wk (ρ • ρ′) F / [F] [ξ] ([ρ] •ₜʷʳ [ρ′])
      [a]′ [ξ] {_} {ρ} {ρ′} [ρ] [ρ′] [a] =
        irrelevanceTerm′ (wk-comp ρ ρ′ F) ([F]′ [ξ] [ρ] [ρ′]) ([F] [ξ] _) [a]
      [G]′ : ∀ {κ′} {ξ : DExt _ κ′ κ} {∇′ : DCon (Term 0) κ′} ([ξ] : ξ » ∇′ ⊇ ∇)
               {k} {ρ : Wk k m} {ρ′ E a}
             ([ρ] : ∇′ » ρ ∷ʷʳ E ⊇ Δ) ([ρ′] : ∇′ » ρ′ ∷ʷʳ Δ ⊇ Γ)
             ([a] : ∇′ » E ⊩⟨ l ⟩ a ∷ U.wk ρ (U.wk ρ′ F) / [F]′ [ξ] [ρ] [ρ′])
           → ∇′ » E ⊩⟨ l ⟩ U.wk (lift (ρ • ρ′)) G [ a ]₀
      [G]′ [ξ] {_} η η′ [a] = [G] [ξ] _ ([a]′ [ξ] η η′ [a])
  in  Σᵣ′ (U.wk ρ F) (U.wk (lift ρ) G) (T.wkRed* [ρ]′ D)
           (≅-wk [ρ]′ A≡A)
           (λ [ξ] {_} {ρ₁} [ρ₁] → irrelevance′ (PE.sym (wk-comp ρ₁ ρ F))
                                    ([F] [ξ] _))
           (λ [ξ] {_} {ρ₁} [ρ₁] [a] → irrelevance′ (wk-comp-subst ρ₁ ρ G)
                                        ([G]′ [ξ] [ρ₁] (defn-wkWkʷʳ [ξ] [ρ]) [a]))
           (λ [ξ] {_} {ρ₁} [ρ₁] [a] [b] [a≡b] →
              let [ρ] = defn-wkWkʷʳ [ξ] [ρ]
                  [a≡b]′ = irrelevanceEqTerm′ (wk-comp ρ₁ ρ F)
                             ([F]′ [ξ] [ρ₁] [ρ]) ([F] [ξ] _) [a≡b]
              in  irrelevanceEq″ (wk-comp-subst ρ₁ ρ G)
                                  (wk-comp-subst ρ₁ ρ G)
                                  ([G]′ [ξ] [ρ₁] [ρ] [a])
                                  (irrelevance′
                                            (wk-comp-subst ρ₁ ρ G)
                                            ([G]′ [ξ] [ρ₁] [ρ] [a]))
                                  (G-ext [ξ] _
                                         ([a]′ [ξ] [ρ₁] [ρ] [a])
                                         ([a]′ [ξ] [ρ₁] [ρ] [b])
                                         [a≡b]′))
           ok
wk ρ∷⊇ (Idᵣ ⊩A) = Idᵣ (record
  { ⇒*Id  = wkRed* (∷ʷʳ⊇→∷ʷ⊇ ρ∷⊇) ⇒*Id
  ; ⊩Ty   = wk ρ∷⊇ ⊩Ty
  ; ⊩lhs  = wkTerm ρ∷⊇ ⊩Ty ⊩lhs
  ; ⊩rhs  = wkTerm ρ∷⊇ ⊩Ty ⊩rhs
  })
  where
  open _»_⊩ₗId_ ⊩A
wk ρ (emb ≤ᵘ-refl x) = emb ≤ᵘ-refl (wk ρ x)
wk ρ (emb (≤ᵘ-step l<) x) = emb-<-⊩ ≤ᵘ-refl (wk ρ (emb l< x))

wkEq ρ (Uᵣ′ l l< D) D′ = wkRed* (∷ʷʳ⊇→∷ʷ⊇ ρ) D′
wkEq ρ (ℕᵣ D) A≡B = wkRed* (∷ʷʳ⊇→∷ʷ⊇ ρ) A≡B
wkEq ρ (Emptyᵣ D) A≡B = wkRed* (∷ʷʳ⊇→∷ʷ⊇ ρ) A≡B
wkEq ρ (Unitᵣ (Unitₜ D _)) A≡B = wkRed* (∷ʷʳ⊇→∷ʷ⊇ ρ) A≡B
wkEq {ρ = ρ} [ρ] (ne′ _ _ _ _) (ne₌ M D′ neM K≡M) =
  let [ρ] = ∷ʷʳ⊇→∷ʷ⊇ [ρ] in
  ne₌ (U.wk ρ M) (wkRed* [ρ] D′) (wkNeutral ρ neM) (≅-wk [ρ] K≡M)
wkEq
  {ρ}
  [ρ] (Πᵣ′ F G D A≡A [F] [G] G-ext _) (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  let [ρ]′ = ∷ʷʳ⊇→∷ʷ⊇ [ρ] in
  B₌ (U.wk ρ F′)
     (U.wk (lift ρ) G′) (T.wkRed* [ρ]′ D′) (≅-wk [ρ]′ A≡B)
     (λ [ξ] {_} {ρ₁} [ρ₁] → irrelevanceEq″ (PE.sym (wk-comp ρ₁ ρ F))
                              (PE.sym (wk-comp ρ₁ ρ F′))
                              ([F] [ξ] ([ρ₁] •ₜʷʳ defn-wkWkʷʳ [ξ] [ρ]))
                              (irrelevance′ (PE.sym (wk-comp ρ₁ ρ F))
                                ([F] [ξ] _))
                              ([F≡F′] [ξ] _))
     (λ [ξ] {_} {ρ₁} [ρ₁] [a] →
        let [a]′ = irrelevanceTerm′ (wk-comp ρ₁ ρ F)
                     (irrelevance′ (PE.sym (wk-comp ρ₁ ρ F)) ([F] [ξ] _))
                     ([F] [ξ] _) [a]
        in  irrelevanceEq″ (wk-comp-subst ρ₁ ρ G)
                            (wk-comp-subst ρ₁ ρ G′)
                            ([G] [ξ] _ [a]′)
                            (irrelevance′ (wk-comp-subst ρ₁ ρ G)
                                          ([G] [ξ] _ [a]′))
                            ([G≡G′] [ξ] _ [a]′))
wkEq
  {ρ}
  [ρ] (Σᵣ′ F G D A≡A [F] [G] G-ext _) (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  let [ρ]′ = ∷ʷʳ⊇→∷ʷ⊇ [ρ] in
  B₌ (U.wk ρ F′) (U.wk (lift ρ) G′) (T.wkRed* [ρ]′ D′) (≅-wk [ρ]′ A≡B)
     (λ [ξ] {_} {ρ₁} [ρ₁] → irrelevanceEq″ (PE.sym (wk-comp ρ₁ ρ F))
                              (PE.sym (wk-comp ρ₁ ρ F′))
                              ([F] [ξ] ([ρ₁] •ₜʷʳ defn-wkWkʷʳ [ξ] [ρ]))
                              (irrelevance′ (PE.sym (wk-comp ρ₁ ρ F))
                                            ([F] [ξ] _))
                              ([F≡F′] [ξ] _))
     (λ [ξ] {_} {ρ₁} [ρ₁] [a] →
        let [a]′ = irrelevanceTerm′ (wk-comp ρ₁ ρ F)
                     (irrelevance′ (PE.sym (wk-comp ρ₁ ρ F)) ([F] [ξ] _))
                     ([F] [ξ] _) [a]
        in  irrelevanceEq″ (wk-comp-subst ρ₁ ρ G)
                            (wk-comp-subst ρ₁ ρ G′)
                            ([G] [ξ] _ [a]′)
                            (irrelevance′ (wk-comp-subst ρ₁ ρ G)
                                          ([G] [ξ] _ [a]′))
                            ([G≡G′] [ξ] _ [a]′))
wkEq ρ∷⊇ (Idᵣ ⊩A) A≡B = Id₌′
  (wkRed* (∷ʷʳ⊇→∷ʷ⊇ ρ∷⊇) ⇒*Id′)
  (wkEq ρ∷⊇ ⊩Ty Ty≡Ty′)
  (wkEqTerm ρ∷⊇ ⊩Ty lhs≡lhs′)
  (wkEqTerm ρ∷⊇ ⊩Ty rhs≡rhs′)
  where
  open _»_⊩ₗId_ ⊩A
  open _»_⊩ₗId_≡_/_ A≡B
wkEq ρ (emb ≤ᵘ-refl x) A≡B = wkEq ρ x A≡B
wkEq ρ (emb (≤ᵘ-step p) ⊩A) A≡B =
  let ⊩A′ = wk ρ (emb p ⊩A) in
  irrelevanceEq ⊩A′ (emb-<-⊩ ≤ᵘ-refl ⊩A′) (wkEq ρ (emb p ⊩A) A≡B)

wkTerm
  {ρ} {l = 1+ l}
  [ρ] ⊩U@(Uᵣ′ l′ (≤ᵘ-step l<) D) (Uₜ A d typeA A≡A [t]) =
  let nRes = wkTerm [ρ] (Uᵣ′ l′ l< D) (Uₜ A d typeA A≡A [t])
  in irrelevanceTerm (wk [ρ] (Uᵣ′ l′ l< D)) (wk [ρ] ⊩U) nRes
wkTerm {ρ} [ρ] (Uᵣ′ l ≤ᵘ-refl D) (Uₜ A d typeA A≡A [t]) =
  let [ρ]′ = ∷ʷʳ⊇→∷ʷ⊇ [ρ] in
  Uₜ (U.wk ρ A) (wkRed*Term [ρ]′ d) (wkType ρ typeA) (≅ₜ-wk [ρ]′ A≡A)
    (wk [ρ] [t])
wkTerm ρ (ℕᵣ D) [t] = wkTermℕ (∷ʷʳ⊇→∷ʷ⊇ ρ) [t]
wkTerm ρ (Emptyᵣ D) [t] = wkTermEmpty (∷ʷʳ⊇→∷ʷ⊇ ρ) [t]
wkTerm ρ (Unitᵣ (Unitₜ D _)) [t] = wkTermUnit (∷ʷʳ⊇→∷ʷ⊇ ρ) [t]
wkTerm {ρ} [ρ] (ne′ _ D neK K≡K) (neₜ k d nf) =
  let [ρ] = ∷ʷʳ⊇→∷ʷ⊇ [ρ] in
  neₜ (U.wk ρ k) (wkRed*Term [ρ] d) (wkTermNe [ρ] nf)
wkTerm
  {ρ} [ρ] (Πᵣ′ F G D A≡A [F] [G] G-ext _) (Πₜ f d funcF f≡f [f] [f]₁) =
  let [ρ]′ = ∷ʷʳ⊇→∷ʷ⊇ [ρ] in
  Πₜ (U.wk ρ f) (wkRed*Term [ρ]′ d) (wkFunction ρ funcF)
     (≅ₜ-wk [ρ]′ f≡f)
     (λ [ξ] {_} {ρ₁} [ρ₁] [a] [b] [a≡b] →
        let F-compEq = wk-comp ρ₁ ρ F
            G-compEq = wk-comp-subst ρ₁ ρ G
            [F]₁ = [F] [ξ] _
            [F]₂ = irrelevance′ (PE.sym (wk-comp ρ₁ ρ F)) [F]₁
            [a]′ = irrelevanceTerm′ F-compEq [F]₂ [F]₁ [a]
            [b]′ = irrelevanceTerm′ F-compEq [F]₂ [F]₁ [b]
            [G]₁ = [G] [ξ] _ [a]′
            [G]₂ = irrelevance′ G-compEq [G]₁
            [a≡b]′ = irrelevanceEqTerm′ F-compEq [F]₂ [F]₁ [a≡b]
        in  irrelevanceEqTerm″
              (PE.cong (λ x → x ∘ _) (PE.sym (wk-comp ρ₁ ρ _)))
              (PE.cong (λ x → x ∘ _) (PE.sym (wk-comp ρ₁ ρ _)))
              G-compEq
              [G]₁ [G]₂
              ([f] [ξ] _ [a]′ [b]′ [a≡b]′))
     (λ [ξ] {_} {ρ₁} [ρ₁] [a] →
        let [F]₁ = [F] [ξ] _
            [F]₂ = irrelevance′ (PE.sym (wk-comp ρ₁ ρ F)) [F]₁
            [a]′ = irrelevanceTerm′ (wk-comp ρ₁ ρ F) [F]₂ [F]₁ [a]
            [G]₁ = [G] [ξ] _ [a]′
            [G]₂ = irrelevance′ (wk-comp-subst ρ₁ ρ G) [G]₁
        in  irrelevanceTerm″ (wk-comp-subst ρ₁ ρ G)
              (PE.cong (λ x → x ∘ _) (PE.sym (wk-comp ρ₁ ρ _)))
              [G]₁ [G]₂ ([f]₁ [ξ] _ [a]′))
wkTerm {ρ} [ρ] [A]@(Bᵣ′ BΣʷ F G D A≡A [F] [G] G-ext _)
       (Σₜ p d p≅p (prodₙ {t = p₁}) (PE.refl , [p₁] , [p₂] , PE.refl)) =
  let [ρ]′ = ∷ʷʳ⊇→∷ʷ⊇ [ρ]
      [ρF] = irrelevance′ (PE.sym (wk-comp id ρ F)) ([F] id [ρ])
      [ρp₁] = wkTerm [ρ] ([F] id _) [p₁]
      [ρp₁]′ = (irrelevanceTerm′
                  (begin
                    U.wk ρ (U.wk id F)
                  ≡⟨ PE.cong (U.wk ρ) (wk-id F) ⟩
                    U.wk ρ F
                  ≡⟨ PE.sym (wk-id (U.wk ρ F)) ⟩
                    U.wk id (U.wk ρ F)
                  ∎)
                  (wk [ρ] ([F] id _))
                  [ρF]
                  [ρp₁])
      [ρp₂] = wkTerm [ρ] ([G] id _ [p₁]) [p₂]
      [ρG]′ = irrelevance′ (wk-comp-subst id ρ G)
                ([G] id [ρ]
                   (irrelevanceTerm′ (wk-comp id ρ F)
                      [ρF] ([F] id [ρ]) [ρp₁]′))
      [ρp₂]′ = irrelevanceTerm′
                  (begin
                    U.wk ρ (U.wk (lift id) G [ p₁ ]₀)
                  ≡⟨ PE.cong (λ x → U.wk ρ (x [ p₁ ]₀)) (wk-lift-id G) ⟩
                    U.wk ρ (G [ p₁ ]₀)
                  ≡⟨ wk-β G ⟩
                    (U.wk (lift ρ) G) [ U.wk ρ p₁ ]₀
                  ≡⟨ PE.cong (λ x → x [ U.wk ρ p₁ ]₀) (PE.sym (wk-lift-id (U.wk (lift ρ) G))) ⟩
                    (U.wk (lift id) (U.wk (lift ρ) G)) [ U.wk ρ p₁ ]₀
                  ∎)
                  (wk [ρ] ([G] id _ [p₁])) [ρG]′
                  [ρp₂]
  in
  Σₜ (U.wk ρ p) (wkRed*Term [ρ]′ d) (≅ₜ-wk [ρ]′ p≅p)
    (wkProduct ρ prodₙ)
    (PE.refl ,
     irrelevanceTerm [ρF]
       (irrelevance′ (PE.sym (wk-comp id ρ F)) _) [ρp₁]′ ,
     irrelevanceTerm [ρG]′ (irrelevance′ (wk-comp-subst id ρ G) _)
       [ρp₂]′ ,
     PE.refl)
wkTerm {ρ} [ρ] [A]@(Bᵣ′ BΣʷ F G D A≡A [F] [G] G-ext _)
       (Σₜ p d p≅p (ne x) p~p) =
  let [ρ]′ = ∷ʷʳ⊇→∷ʷ⊇ [ρ] in
  Σₜ (U.wk ρ p) (wkRed*Term [ρ]′ d) (≅ₜ-wk [ρ]′ p≅p)
     (wkProduct ρ (ne x)) (~-wk [ρ]′ p~p)
wkTerm
  {ρ} [ρ] [A]@(Bᵣ′ BΣˢ F G D A≡A [F] [G] G-ext _)
  (Σₜ p d p≅p pProd ([fst] , [snd])) =
  let [ρ]′ = ∷ʷʳ⊇→∷ʷ⊇ [ρ]
      [ρF] = irrelevance′ (PE.sym (wk-comp id ρ F)) ([F] id [ρ])
      [ρfst] = wkTerm [ρ] ([F] id _) [fst]
      [ρfst]′ = (irrelevanceTerm′
                  (begin
                    U.wk ρ (U.wk id F)
                  ≡⟨ PE.cong (U.wk ρ) (wk-id F) ⟩
                    U.wk ρ F
                  ≡⟨ PE.sym (wk-id (U.wk ρ F)) ⟩
                    U.wk id (U.wk ρ F)
                  ∎)
                  (wk [ρ] ([F] id _))
                  [ρF]
                  [ρfst])
      [ρsnd] = wkTerm [ρ] ([G] id _ [fst]) [snd]
      [ρG]′ = irrelevance′ (wk-comp-subst id ρ G)
                ([G] id [ρ]
                   (irrelevanceTerm′ (wk-comp id ρ F)
                      [ρF] ([F] id [ρ]) [ρfst]′))
      [ρsnd]′ = irrelevanceTerm′
        (begin
           U.wk ρ (U.wk (lift id) G [ fst _ p ]₀)                    ≡⟨ PE.cong (λ x → U.wk ρ (x [ fst _ p ]₀)) (wk-lift-id G) ⟩
           U.wk ρ (G [ fst _ p ]₀)                                   ≡⟨ wk-β G ⟩
           (U.wk (lift ρ) G) [ fst _ (U.wk ρ p) ]₀                   ≡⟨ PE.cong (λ x → x [ fst _ (U.wk ρ p) ]₀)
                                                                         (PE.sym (wk-lift-id (U.wk (lift ρ) G))) ⟩
           (U.wk (lift id) (U.wk (lift ρ) G)) [ fst _ (U.wk ρ p) ]₀  ∎)
        (wk [ρ] ([G] id _ [fst])) [ρG]′
        [ρsnd]
  in  Σₜ (U.wk ρ p) (wkRed*Term [ρ]′ d) (≅ₜ-wk [ρ]′ p≅p)
         (wkProduct ρ pProd)
         ( irrelevanceTerm [ρF]
             (irrelevance′ (PE.sym (wk-comp id ρ F)) _) [ρfst]′
         , irrelevanceTerm [ρG]′
             (irrelevance′ (wk-comp-subst id ρ G) _) [ρsnd]′
         )
wkTerm ρ∷⊇ (Idᵣ ⊩A) ⊩t@(_ , t⇒*u , _) =
  let ρ∷⊇′ = ∷ʷʳ⊇→∷ʷ⊇ ρ∷⊇ in
    _
  , wkRed*Term ρ∷⊇′ t⇒*u
  , (case ⊩Id∷-view-inhabited ⊩t of λ where
       (rflᵣ lhs≡rhs) → rflₙ , wkEqTerm ρ∷⊇ ⊩Ty lhs≡rhs
       (ne u-n u~u)   → ne (wkNeutral _ u-n) , ~-wk ρ∷⊇′ u~u)
  where
  open _»_⊩ₗId_ ⊩A
wkTerm ρ (emb ≤ᵘ-refl x) t = wkTerm ρ x t
wkTerm ρ (emb (≤ᵘ-step l<) x) t =
  let wkn = wkTerm ρ (emb l< x) t
  in irrelevanceTerm (wk ρ (emb l< x))
    (wk ρ (emb (≤ᵘ-step l<) x)) wkn
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
wkEqTerm ρ (Unitᵣ (Unitₜ D _)) [t≡u] = wkEqTermUnit (∷ʷʳ⊇→∷ʷ⊇ ρ) [t≡u]
wkEqTerm {ρ} [ρ] (ne′ _ D neK K≡K) (neₜ₌ k m d d′ nf) =
  let [ρ]′ = ∷ʷʳ⊇→∷ʷ⊇ [ρ] in
  neₜ₌ (U.wk ρ k) (U.wk ρ m) (wkRed*Term [ρ]′ d)
    (wkRed*Term [ρ]′ d′) (wkEqTermNe [ρ]′ nf)
wkEqTerm {ρ} [ρ] (Πᵣ′ F G D A≡A [F] [G] G-ext ok)
                    (Πₜ₌ f g d d′ funcF funcG f≡g [t] [u] [f≡g]) =
  let [ρ]′ = ∷ʷʳ⊇→∷ʷ⊇ [ρ]
      [A] = Πᵣ′ F G D A≡A [F] [G] G-ext ok
  in  Πₜ₌ (U.wk ρ f) (U.wk ρ g)
          (wkRed*Term [ρ]′ d) (wkRed*Term [ρ]′ d′)
          (wkFunction ρ funcF) (wkFunction ρ funcG)
          (≅ₜ-wk [ρ]′ f≡g) (wkTerm [ρ] [A] [t]) (wkTerm [ρ] [A] [u])
          (λ [ξ] {_} {ρ₁} [ρ₁] [a] →
             let [F]₁ = [F] [ξ] _
                 [F]₂ = irrelevance′ (PE.sym (wk-comp ρ₁ ρ F)) [F]₁
                 [a]′ = irrelevanceTerm′ (wk-comp ρ₁ ρ F) [F]₂ [F]₁ [a]
                 [G]₁ = [G] [ξ] _ [a]′
                 [G]₂ = irrelevance′ (wk-comp-subst ρ₁ ρ G) [G]₁
             in  irrelevanceEqTerm″ (PE.cong (λ y → y ∘ _) (PE.sym (wk-comp ρ₁ ρ _)))
                                    (PE.cong (λ y → y ∘ _) (PE.sym (wk-comp ρ₁ ρ _)))
                                    (wk-comp-subst ρ₁ ρ G)
                                    [G]₁ [G]₂
                                    ([f≡g] [ξ] _ [a]′))
wkEqTerm {ρ} [ρ] [A]@(Bᵣ′ BΣʷ F G D A≡A [F] [G] G-ext ok)
         (Σₜ₌ p r d d′ (prodₙ {t = p₁}) prodₙ p≅r [t] [u]
            (PE.refl , PE.refl ,
             [p₁] , [r₁] , [p₂] , [r₂] , [fst≡] , [snd≡])) =
  let [ρ]′ = ∷ʷʳ⊇→∷ʷ⊇ [ρ]
      [A] = Σᵣ′ F G D A≡A [F] [G] G-ext ok
      ρidF≡idρF = begin
                    U.wk ρ (U.wk id F)
                  ≡⟨ PE.cong (U.wk ρ) (wk-id F) ⟩
                    U.wk ρ F
                  ≡⟨ PE.sym (wk-id (U.wk ρ F)) ⟩
                    U.wk id (U.wk ρ F)
                  ∎
      [ρF] = irrelevance′ (PE.sym (wk-comp id ρ F)) ([F] id [ρ])
      [ρp₁] = wkTerm [ρ] ([F] id _) [p₁]
      [ρp₁]′ = irrelevanceTerm′
                  ρidF≡idρF
                  (wk [ρ] ([F] id _)) [ρF]
                  [ρp₁]
      [ρr₁] = wkTerm [ρ] ([F] id _) [r₁]
      [ρr₁]′ = irrelevanceTerm′
                  ρidF≡idρF
                  (wk [ρ] ([F] id _)) [ρF]
                  [ρr₁]
      [ρfst≡] = wkEqTerm [ρ] ([F] id _) [fst≡]
      [ρfst≡]′ = irrelevanceEqTerm′
                   ρidF≡idρF
                   (wk [ρ] ([F] id _)) [ρF]
                   [ρfst≡]
      [ρsnd≡] = wkEqTerm [ρ] ([G] id _ [p₁]) [snd≡]
      [ρG]′ = irrelevance′ (wk-comp-subst id ρ G)
                ([G] id [ρ]
                   (irrelevanceTerm′ (wk-comp id ρ F)
                      [ρF] ([F] id [ρ]) [ρp₁]′))
      [ρG]″ = irrelevance′ (wk-comp-subst id ρ G)
                ([G] id [ρ]
                   (irrelevanceTerm′ (wk-comp id ρ F)
                      [ρF] ([F] id [ρ]) [ρr₁]′))
      ρG-eq = λ t → (begin
                    U.wk ρ (U.wk (lift id) G [ t ]₀)
                  ≡⟨ PE.cong (λ x → U.wk ρ (x [ t ]₀)) (wk-lift-id G) ⟩
                    U.wk ρ (G [ t ]₀)
                  ≡⟨ wk-β G ⟩
                    (U.wk (lift ρ) G) [ U.wk ρ t ]₀
                  ≡⟨ PE.cong (λ x → x [ U.wk ρ t ]₀) (PE.sym (wk-lift-id (U.wk (lift ρ) G))) ⟩
                    (U.wk (lift id) (U.wk (lift ρ) G)) [ U.wk ρ t ]₀
                  ∎)
      [ρp₂] = wkTerm [ρ] ([G] id _ [p₁]) [p₂]
      [ρp₂]′ = irrelevanceTerm′ (ρG-eq p₁) (wk [ρ] ([G] id _ [p₁]))
                 [ρG]′ [ρp₂]
      [ρr₂] = wkTerm [ρ] ([G] id _ [r₁]) [r₂]
      [ρr₂]′ = irrelevanceTerm′ (ρG-eq _) (wk [ρ] ([G] id _ [r₁]))
                 [ρG]″ [ρr₂]
      [ρsnd≡]′ = irrelevanceEqTerm′
                  (ρG-eq p₁)
                  (wk [ρ] ([G] id _ [p₁])) [ρG]′
                  [ρsnd≡]
  in  Σₜ₌ (U.wk ρ p) (U.wk ρ r)
          (wkRed*Term [ρ]′ d) (wkRed*Term [ρ]′ d′)
          (wkProduct ρ prodₙ) (wkProduct ρ prodₙ)
          (≅ₜ-wk [ρ]′ p≅r) (wkTerm [ρ] [A] [t]) (wkTerm [ρ] [A] [u])
          (PE.refl , PE.refl ,
           irrelevanceTerm [ρF]
              (irrelevance′ (PE.sym (wk-comp id ρ F)) _) [ρp₁]′ ,
           irrelevanceTerm [ρF]
             (irrelevance′ (PE.sym (wk-comp id ρ F)) _) [ρr₁]′ ,
           irrelevanceTerm [ρG]′
             (irrelevance′ (wk-comp-subst id ρ G) _) [ρp₂]′ ,
           irrelevanceTerm [ρG]″
             (irrelevance′ (wk-comp-subst id ρ G) _) [ρr₂]′ ,
           irrelevanceEqTerm [ρF]
             (irrelevance′ (PE.sym (wk-comp id ρ F)) _) [ρfst≡]′ ,
           irrelevanceEqTerm [ρG]′
             (irrelevance′ (wk-comp-subst id ρ G) _) [ρsnd≡]′)
wkEqTerm {ρ} [ρ] [A]@(Bᵣ′ BΣʷ F G D A≡A [F] [G] G-ext ok)
         (Σₜ₌ p r d d′ (ne x) (ne y) p≅r [t] [u] p~r) =
  let [ρ]′ = ∷ʷʳ⊇→∷ʷ⊇ [ρ]
      [A] = Σᵣ′ F G D A≡A [F] [G] G-ext ok
  in  Σₜ₌ (U.wk ρ p) (U.wk ρ r)
          (wkRed*Term [ρ]′ d) (wkRed*Term [ρ]′ d′)
          (wkProduct ρ (ne x)) (wkProduct ρ (ne y))
          (≅ₜ-wk [ρ]′ p≅r) (wkTerm [ρ] [A] [t]) (wkTerm [ρ] [A] [u])
          (~-wk [ρ]′ p~r)
wkEqTerm {ρ} [ρ] [A]@(Bᵣ′ BΣˢ F G D A≡A [F] [G] G-ext ok)
         (Σₜ₌ p r d d′ pProd rProd p≅r [t] [u] ([fstp] , [fstr] , [fst≡] , [snd≡])) =
  let [ρ]′ = ∷ʷʳ⊇→∷ʷ⊇ [ρ]
      [A] = Σᵣ′ F G D A≡A [F] [G] G-ext ok
      ρidF≡idρF = begin
                    U.wk ρ (U.wk id F)
                  ≡⟨ PE.cong (U.wk ρ) (wk-id F) ⟩
                    U.wk ρ F
                  ≡⟨ PE.sym (wk-id (U.wk ρ F)) ⟩
                    U.wk id (U.wk ρ F)
                  ∎
      [ρF] = irrelevance′ (PE.sym (wk-comp id ρ F)) ([F] id [ρ])
      [ρfstp] = wkTerm [ρ] ([F] id _) [fstp]
      [ρfstp]′ = irrelevanceTerm′
                  ρidF≡idρF
                  (wk [ρ] ([F] id _)) [ρF]
                  [ρfstp]
      [ρfstr] = wkTerm [ρ] ([F] id _) [fstr]
      [ρfstr]′ = irrelevanceTerm′
                  ρidF≡idρF
                  (wk [ρ] ([F] id _)) [ρF]
                  [ρfstr]
      [ρfst≡] = wkEqTerm [ρ] ([F] id _) [fst≡]
      [ρfst≡]′ = irrelevanceEqTerm′
                   ρidF≡idρF
                   (wk [ρ] ([F] id _)) [ρF]
                   [ρfst≡]
      [ρsnd≡] = wkEqTerm [ρ] ([G] id _ [fstp]) [snd≡]
      [ρG]′ = irrelevance′ (wk-comp-subst id ρ G)
                ([G] id [ρ]
                   (irrelevanceTerm′ (wk-comp id ρ F)
                      [ρF] ([F] id [ρ]) [ρfstp]′))
      [ρsnd≡]′ = irrelevanceEqTerm′
        (begin
           U.wk ρ (U.wk (lift id) G [ fst _ p ]₀)                    ≡⟨ PE.cong (λ x → U.wk ρ (x [ fst _ p ]₀)) (wk-lift-id G) ⟩
           U.wk ρ (G [ fst _ p ]₀)                                   ≡⟨ wk-β G ⟩
           (U.wk (lift ρ) G) [ fst _ (U.wk ρ p) ]₀                   ≡⟨ PE.cong (λ x → x [ fst _ (U.wk ρ p) ]₀)
                                                                         (PE.sym (wk-lift-id (U.wk (lift ρ) G))) ⟩
           (U.wk (lift id) (U.wk (lift ρ) G)) [ fst _ (U.wk ρ p) ]₀  ∎)
        (wk [ρ] ([G] id _ [fstp])) [ρG]′
        [ρsnd≡]
  in  Σₜ₌ (U.wk ρ p) (U.wk ρ r)
          (wkRed*Term [ρ]′ d) (wkRed*Term [ρ]′ d′)
          (wkProduct ρ pProd) (wkProduct ρ rProd)
          (≅ₜ-wk [ρ]′ p≅r) (wkTerm [ρ] [A] [t]) (wkTerm [ρ] [A] [u])
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
       (ne t′-n u′-n t′~u′) →
           ne (wkNeutral _ t′-n)
         , ne (wkNeutral _ u′-n)
         , ~-wk ρ∷⊇′ t′~u′)
  where
  open _»_⊩ₗId_ ⊩A
wkEqTerm ρ (emb ≤ᵘ-refl x) t≡u = wkEqTerm ρ x t≡u
wkEqTerm ρ (emb (≤ᵘ-step s) x) t≡u =
  let wkET′ = wkEqTerm ρ (emb s x) t≡u
  in irrelevanceEqTerm (wk ρ (emb s x)) (wk ρ (emb (≤ᵘ-step s) x)) wkET′

-- Impossible cases
wkEqTerm _ (Bᵣ BΣʷ record{}) (Σₜ₌ _ _ _ _ prodₙ  (ne _) _ _ _ ())
wkEqTerm _ (Bᵣ BΣʷ record{}) (Σₜ₌ _ _ _ _ (ne _) prodₙ  _ _ _ ())
