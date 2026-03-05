------------------------------------------------------------------------
-- Properties of the untyped syntax
-- Laws for weakenings and substitutions.
------------------------------------------------------------------------

module Definition.Untyped.Properties {a} (M : Set a) where

open import Definition.Untyped M
open import Definition.Untyped.Inversion M
open import Definition.Untyped.Properties.NotParametrised public

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.List
open import Tools.Nat as Nat
open import Tools.Relation
open import Tools.Product as Σ
open import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum
open import Tools.Vec as Vec using (ε)

private
  variable
    j ℓ m m₁ m₂ n n₁ n₂ o α β : Nat
    x x₁ x₂ : Fin _
    as : List _
    eq eq₁ eq₂ : _ ≡ _
    𝕋 𝕌 : Set _
    ∇ ∇′ : DCon _ _
    ξ : DExt _ _ _
    Γ : Con Term _
    Δ : Cons _ _
    φ : Unfolding _
    A A₁ A₂ B₁ B₂ E F G H l l′ l₁ l₂ t t₁ t₂ u u₁ u₂ v v₁ v₂ w w₁ w₂ :
      Term[ _ ] _
    k : Term-kind
    ts₁ ts₂ : Args _ _
    ρ ρ′ : Wk m n
    η : Wk n ℓ
    σ σ₁ σ₂ σ′ : Subst m n
    p p₁ p₂ q q₁ q₂ r r₁ r₂ : M
    s s₁ s₂ : Strength
    b₁ b₂ : BinderMode
    f : 𝕋 → 𝕌

------------------------------------------------------------------------
-- Properties of definition contexts

opaque

  ↦∷∈⇒↦∈ : ∀ {A t} → α ↦ t ∷ A ∈ ∇ → α ↦∷ A ∈ ∇
  ↦∷∈⇒↦∈ here        = here
  ↦∷∈⇒↦∈ (there α↦t) = there (↦∷∈⇒↦∈ α↦t)

opaque

  ↦⊘∈⇒↦∈ : ∀ {A} → α ↦⊘∷ A ∈ ∇ → α ↦∷ A ∈ ∇
  ↦⊘∈⇒↦∈ here        = here
  ↦⊘∈⇒↦∈ (there α↦⊘) = there (↦⊘∈⇒↦∈ α↦⊘)

opaque

  scoped-↦∈ : ∀ {∇ : DCon 𝕋 n} {A} → α ↦∷ A ∈ ∇ → α < n
  scoped-↦∈ here         = s≤s ≤-refl
  scoped-↦∈ (there α↦∷A) = s≤s (≤⇒pred≤ (scoped-↦∈ α↦∷A))

opaque

  scoped-↦∷∈ : ∀ {∇ : DCon 𝕋 n} {A t} → α ↦ t ∷ A ∈ ∇ → α < n
  scoped-↦∷∈ α↦t = scoped-↦∈ (↦∷∈⇒↦∈ α↦t)

opaque

  scoped-↦⊘∈ : ∀ {∇ : DCon 𝕋 n} {A} → α ↦⊘∷ A ∈ ∇ → α < n
  scoped-↦⊘∈ α↦⊘ = scoped-↦∈ (↦⊘∈⇒↦∈ α↦⊘)

opaque

  unique-↦∈ : ∀ {A B} → α ↦∷ A ∈ ∇ → β ↦∷ B ∈ ∇ → α ≡ β → A ≡ B
  unique-↦∈ here        here        _    = refl
  unique-↦∈ here        (there α↦u) refl = ⊥-elim (n≮n _ (scoped-↦∈ α↦u))
  unique-↦∈ (there α↦t) here        refl = ⊥-elim (n≮n _ (scoped-↦∈ α↦t))
  unique-↦∈ (there α↦t) (there β↦u) α≡β  = unique-↦∈ α↦t β↦u α≡β

opaque

  unique-↦∷∈ :
    ∀ {A B t u} → α ↦ t ∷ A ∈ ∇ → β ↦ u ∷ B ∈ ∇ → α ≡ β → A ≡ B × t ≡ u
  unique-↦∷∈ here        here        _    = refl , refl
  unique-↦∷∈ here        (there α↦u) refl = ⊥-elim (n≮n _ (scoped-↦∷∈ α↦u))
  unique-↦∷∈ (there α↦t) here        refl = ⊥-elim (n≮n _ (scoped-↦∷∈ α↦t))
  unique-↦∷∈ (there α↦t) (there β↦u) α≡β  = unique-↦∷∈ α↦t β↦u α≡β

opaque

  unique-↦⊘∈ : ∀ {A B} → α ↦⊘∷ A ∈ ∇ → β ↦⊘∷ B ∈ ∇ → α ≡ β → A ≡ B
  unique-↦⊘∈ α↦⊘ β↦⊘ α≡β = unique-↦∈ (↦⊘∈⇒↦∈ α↦⊘) (↦⊘∈⇒↦∈ β↦⊘) α≡β

opaque

  coerce-↦∷∈ : ∀ {A B t} → α ↦∷ B ∈ ∇ → α ↦ t ∷ A ∈ ∇ → α ↦ t ∷ B ∈ ∇
  coerce-↦∷∈ α↦∷B α↦t = subst (_ ↦ _ ∷_∈ _)
                              (unique-↦∈ (↦∷∈⇒↦∈ α↦t) α↦∷B refl)
                              α↦t

opaque

  coerce-↦⊘∈ : ∀ {A B} → α ↦∷ B ∈ ∇ → α ↦⊘∷ A ∈ ∇ → α ↦⊘∷ B ∈ ∇
  coerce-↦⊘∈ α↦∷B α↦⊘ = subst (_ ↦⊘∷_∈ _)
                              (unique-↦∈ (↦⊘∈⇒↦∈ α↦⊘) α↦∷B refl)
                              α↦⊘

opaque

  dichotomy-↦∈ : ∀ {A} → α ↦∷ A ∈ ∇ → (∃ λ t → α ↦ t ∷ A ∈ ∇) ⊎ (α ↦⊘∷ A ∈ ∇)
  dichotomy-↦∈ {∇ = ∇ ∙⟨ opa φ ⟩[ t ∷ A ]} here         = inj₂ here
  dichotomy-↦∈ {∇ = ∇ ∙⟨ tra   ⟩[ t ∷ A ]} here         = inj₁ (t , here)
  dichotomy-↦∈                             (there α↦∷A) =
    case dichotomy-↦∈ α↦∷A of λ where
      (inj₁ (t , α↦t)) → inj₁ (t , there α↦t)
      (inj₂ α↦⊘)       → inj₂ (there α↦⊘)

opaque

  exclusion-↦∈ :
    ∀ {A B t} → α ↦⊘∷ A ∈ ∇ → ¬ α ↦ t ∷ B ∈ ∇
  exclusion-↦∈ here        (there α↦t) = n≮n _ (scoped-↦∷∈ α↦t)
  exclusion-↦∈ (there α↦⊘) here        = n≮n _ (scoped-↦⊘∈ α↦⊘)
  exclusion-↦∈ (there α↦⊘) (there α↦t) = exclusion-↦∈ α↦⊘ α↦t

------------------------------------------------------------------------
-- Lemmas about _⊔ᵒ_

opaque
  unfolding _⊔ᵒ_

  -- The function _⊔ᵒ_ is associative.

  assoc-⊔ᵒ :
    (φ φ′ φ″ : Unfolding n) → φ ⊔ᵒ (φ′ ⊔ᵒ φ″) PE.≡ (φ ⊔ᵒ φ′) ⊔ᵒ φ″
  assoc-⊔ᵒ ε ε ε = PE.refl
  assoc-⊔ᵒ (φ ⁰) (φ′ ⁰) (φ″ ⁰) = PE.cong _⁰ (assoc-⊔ᵒ φ φ′ φ″)
  assoc-⊔ᵒ (φ ⁰) (φ′ ⁰) (φ″ ¹) = PE.cong _¹ (assoc-⊔ᵒ φ φ′ φ″)
  assoc-⊔ᵒ (φ ⁰) (φ′ ¹) (φ″ ⁰) = PE.cong _¹ (assoc-⊔ᵒ φ φ′ φ″)
  assoc-⊔ᵒ (φ ⁰) (φ′ ¹) (φ″ ¹) = PE.cong _¹ (assoc-⊔ᵒ φ φ′ φ″)
  assoc-⊔ᵒ (φ ¹) (φ′ ⁰) (φ″ ⁰) = PE.cong _¹ (assoc-⊔ᵒ φ φ′ φ″)
  assoc-⊔ᵒ (φ ¹) (φ′ ⁰) (φ″ ¹) = PE.cong _¹ (assoc-⊔ᵒ φ φ′ φ″)
  assoc-⊔ᵒ (φ ¹) (φ′ ¹) (φ″ ⁰) = PE.cong _¹ (assoc-⊔ᵒ φ φ′ φ″)
  assoc-⊔ᵒ (φ ¹) (φ′ ¹) (φ″ ¹) = PE.cong _¹ (assoc-⊔ᵒ φ φ′ φ″)

opaque
  unfolding _⊔ᵒ_

  -- The function _⊔ᵒ_ is commutative.

  comm-⊔ᵒ : (φ φ′ : Unfolding n) → φ ⊔ᵒ φ′ PE.≡ φ′ ⊔ᵒ φ
  comm-⊔ᵒ ε ε = PE.refl
  comm-⊔ᵒ (φ ⁰) (φ′ ⁰) = PE.cong _⁰ (comm-⊔ᵒ φ φ′)
  comm-⊔ᵒ (φ ⁰) (φ′ ¹) = PE.cong _¹ (comm-⊔ᵒ φ φ′)
  comm-⊔ᵒ (φ ¹) (φ′ ⁰) = PE.cong _¹ (comm-⊔ᵒ φ φ′)
  comm-⊔ᵒ (φ ¹) (φ′ ¹) = PE.cong _¹ (comm-⊔ᵒ φ φ′)

opaque
  unfolding ones _⊔ᵒ_

  -- The unfolding ones is a left zero for _⊔ᵒ_.

  ones-⊔ᵒˡ : ones ⊔ᵒ φ ≡ ones
  ones-⊔ᵒˡ {φ = ε}         = refl
  ones-⊔ᵒˡ {φ = _ Vec.∷ _} = cong (_ Vec.∷_) ones-⊔ᵒˡ

opaque

  -- The unfolding ones is a right zero for _⊔ᵒ_.

  ones-⊔ᵒʳ : φ ⊔ᵒ ones ≡ ones
  ones-⊔ᵒʳ {φ} =
    φ ⊔ᵒ ones  ≡⟨ comm-⊔ᵒ _ _ ⟩
    ones ⊔ᵒ φ  ≡⟨ ones-⊔ᵒˡ ⟩
    ones       ∎

opaque
  unfolding zeros _⊔ᵒ_

  -- The unfolding zeros is a left unit for _⊔ᵒ_.

  zeros-⊔ᵒˡ : zeros ⊔ᵒ φ PE.≡ φ
  zeros-⊔ᵒˡ {φ = ε}         = refl
  zeros-⊔ᵒˡ {φ = _ Vec.∷ _} = cong (_ Vec.∷_) zeros-⊔ᵒˡ

opaque

  -- The unfolding zeros is a right unit for _⊔ᵒ_.

  zeros-⊔ᵒʳ : φ ⊔ᵒ zeros PE.≡ φ
  zeros-⊔ᵒʳ {φ} =
    φ ⊔ᵒ zeros  ≡⟨ comm-⊔ᵒ _ _ ⟩
    zeros ⊔ᵒ φ  ≡⟨ zeros-⊔ᵒˡ ⟩
    φ           ∎

------------------------------------------------------------------------
-- Properties of glassification

opaque

  glassify-↦∈ : ∀ {A} → α ↦∷ A ∈ ∇ → α ↦∷ A ∈ glassify ∇
  glassify-↦∈ here         = here
  glassify-↦∈ (there α↦∷A) = there (glassify-↦∈ α↦∷A)

opaque

  unglass-↦∈ : ∀ {A} → α ↦∷ A ∈ glassify ∇ → α ↦∷ A ∈ ∇
  unglass-↦∈ {∇ = ε}                 ()
  unglass-↦∈ {∇ = ∇ ∙⟨ ω ⟩[ t ∷ A ]} here         = here
  unglass-↦∈ {∇ = ∇ ∙⟨ ω ⟩[ t ∷ A ]} (there α↦∷A) = there (unglass-↦∈ α↦∷A)

opaque

  glassify-↦∷∈ : ∀ {A t} → α ↦ t ∷ A ∈ ∇ → α ↦ t ∷ A ∈ glassify ∇
  glassify-↦∷∈ here        = here
  glassify-↦∷∈ (there α↦t) = there (glassify-↦∷∈ α↦t)

opaque

  glass-↦⊘∈ : ∀ {A} → ¬ α ↦⊘∷ A ∈ glassify ∇
  glass-↦⊘∈ {∇ = ε}                 ()
  glass-↦⊘∈ {∇ = ∇ ∙⟨ ω ⟩[ t ∷ A ]} (there α↦⊘) = glass-↦⊘∈ α↦⊘

opaque

  glass-↦∈ : ∀ {A} → α ↦∷ A ∈ glassify ∇ → ∃ λ t → α ↦ t ∷ A ∈ glassify ∇
  glass-↦∈ α↦∷A = case dichotomy-↦∈ α↦∷A of λ where
    (inj₁ ∃t)  → ∃t
    (inj₂ α↦⊘) → ⊥-elim (glass-↦⊘∈ α↦⊘)

opaque

  glassify-↦∈′ : ∀ {A} → α ↦∷ A ∈ ∇ → ∃ λ t → α ↦ t ∷ A ∈ glassify ∇
  glassify-↦∈′ = glass-↦∈ ∘→ glassify-↦∈

opaque

  -- The functions glassify and map-DCon f commute.

  glassify-map-DCon : glassify (map-DCon f ∇) ≡ map-DCon f (glassify ∇)
  glassify-map-DCon {∇ = ε}    = refl
  glassify-map-DCon {∇ = _ ∙!} = cong _∙! glassify-map-DCon

------------------------------------------------------------------------
-- Properties of toTerm and fromTerm.

opaque

  -- Converting to the alternative term representation and back is
  -- identity.

  toTerm∘fromTerm : (t : Term[ k ] n) → toTerm (fromTerm t) ≡ t
  toTerm∘fromTerm (var x) = refl
  toTerm∘fromTerm (defn α) = refl
  toTerm∘fromTerm Level = refl
  toTerm∘fromTerm zeroᵘ = refl
  toTerm∘fromTerm (sucᵘ l) = cong sucᵘ (toTerm∘fromTerm l)
  toTerm∘fromTerm (l₁ supᵘ l₂) =
    cong₂ _supᵘ_ (toTerm∘fromTerm l₁) (toTerm∘fromTerm l₂)
  toTerm∘fromTerm (ωᵘ+ _) = refl
  toTerm∘fromTerm (level t) = cong level (toTerm∘fromTerm t)
  toTerm∘fromTerm (U l) = cong U (toTerm∘fromTerm l)
  toTerm∘fromTerm (Lift l A) =
    cong₂ Lift (toTerm∘fromTerm l) (toTerm∘fromTerm A)
  toTerm∘fromTerm (lift a) =
    cong lift (toTerm∘fromTerm a)
  toTerm∘fromTerm (lower a) =
    cong lower (toTerm∘fromTerm a)
  toTerm∘fromTerm (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B) =
    cong₂ (ΠΣ⟨ b ⟩ p , q ▷_▹_) (toTerm∘fromTerm A) (toTerm∘fromTerm B)
  toTerm∘fromTerm (lam p t) =
    cong (lam p) (toTerm∘fromTerm t)
  toTerm∘fromTerm (t ∘⟨ p ⟩ u) =
    cong₂ (_∘⟨ p ⟩_) (toTerm∘fromTerm t) (toTerm∘fromTerm u)
  toTerm∘fromTerm (prod s p t u) =
    cong₂ (prod s p) (toTerm∘fromTerm t) (toTerm∘fromTerm u)
  toTerm∘fromTerm (fst p t) =
    cong (fst p) (toTerm∘fromTerm t)
  toTerm∘fromTerm (snd p t) =
    cong (snd p) (toTerm∘fromTerm t)
  toTerm∘fromTerm (prodrec r p q A t u) =
    cong₃ (prodrec r p q) (toTerm∘fromTerm A)
      (toTerm∘fromTerm t) (toTerm∘fromTerm u)
  toTerm∘fromTerm ℕ = refl
  toTerm∘fromTerm zero = refl
  toTerm∘fromTerm (suc t) =
    cong suc (toTerm∘fromTerm t)
  toTerm∘fromTerm (natrec p q r A z s n) =
    cong₄ (natrec p q r) (toTerm∘fromTerm A) (toTerm∘fromTerm z)
      (toTerm∘fromTerm s) (toTerm∘fromTerm n)
  toTerm∘fromTerm (Unit s) = refl
  toTerm∘fromTerm (star s) = refl
  toTerm∘fromTerm (unitrec p q A t u) =
    cong₃ (unitrec p q) (toTerm∘fromTerm A)
      (toTerm∘fromTerm t) (toTerm∘fromTerm u)
  toTerm∘fromTerm Empty = refl
  toTerm∘fromTerm (emptyrec p A t) =
    cong₂ (emptyrec p) (toTerm∘fromTerm A) (toTerm∘fromTerm t)
  toTerm∘fromTerm (Id A t u) =
    cong₃ Id (toTerm∘fromTerm A) (toTerm∘fromTerm t) (toTerm∘fromTerm u)
  toTerm∘fromTerm rfl = refl
  toTerm∘fromTerm (J p q A t B u v w) =
    cong₆ (J p q) (toTerm∘fromTerm A) (toTerm∘fromTerm t)
      (toTerm∘fromTerm B) (toTerm∘fromTerm u)
      (toTerm∘fromTerm v) (toTerm∘fromTerm w)
  toTerm∘fromTerm (K p A t B u v) =
    cong₅ (K p) (toTerm∘fromTerm A) (toTerm∘fromTerm t)
      (toTerm∘fromTerm B) (toTerm∘fromTerm u) (toTerm∘fromTerm v)
  toTerm∘fromTerm ([]-cong s l A t u v) =
    cong₅ ([]-cong s) (toTerm∘fromTerm l) (toTerm∘fromTerm A)
      (toTerm∘fromTerm t) (toTerm∘fromTerm u) (toTerm∘fromTerm v)

opaque

  -- Converting from the alternative term representation and back is
  -- identity.

  fromTerm∘toTerm : (t : Term[ k ]′ n) → fromTerm (toTerm t) ≡ t
  fromTerm∘toTerm (var x) =
    refl
  fromTerm∘toTerm (con (defnᵏ α) []) =
    refl
  fromTerm∘toTerm (con Levelᵏ []) =
    refl
  fromTerm∘toTerm (con zeroᵘᵏ []) =
    refl
  fromTerm∘toTerm (con sucᵘᵏ (t ∷ₜ [])) =
    cong (λ t → con sucᵘᵏ (t ∷ₜ [])) (fromTerm∘toTerm t)
  fromTerm∘toTerm (con supᵘᵏ (t₁ ∷ₜ t₂ ∷ₜ [])) =
    cong₂ (λ t₁ t₂ → con supᵘᵏ (t₁ ∷ₜ t₂ ∷ₜ [])) (fromTerm∘toTerm t₁)
      (fromTerm∘toTerm t₂)
  fromTerm∘toTerm (con (ωᵘ+ᵏ _) []) =
    refl
  fromTerm∘toTerm (con levelᵏ (t ∷ₜ [])) =
    cong (λ t → con levelᵏ (t ∷ₜ [])) (fromTerm∘toTerm t)
  fromTerm∘toTerm (con Uᵏ (l ∷ₜ [])) =
    cong (λ l → con Uᵏ (l ∷ₜ [])) (fromTerm∘toTerm l)
  fromTerm∘toTerm (con Liftᵏ (l ∷ₜ A ∷ₜ [])) =
    cong₂ (λ l A → con Liftᵏ (l ∷ₜ A ∷ₜ [])) (fromTerm∘toTerm l)
      (fromTerm∘toTerm A)
  fromTerm∘toTerm (con liftᵏ (t ∷ₜ [])) =
    cong (λ t → con liftᵏ (t ∷ₜ [])) (fromTerm∘toTerm t)
  fromTerm∘toTerm (con lowerᵏ (t ∷ₜ [])) =
    cong (λ t → con lowerᵏ (t ∷ₜ [])) (fromTerm∘toTerm t)
  fromTerm∘toTerm (con Emptyᵏ []) = refl
  fromTerm∘toTerm (con (emptyrecᵏ p) (A ∷ₜ t ∷ₜ [])) =
    cong₂ (λ A t → con (emptyrecᵏ p) (A ∷ₜ t ∷ₜ [])) (fromTerm∘toTerm A)
      (fromTerm∘toTerm t)
  fromTerm∘toTerm (con (Unitᵏ s) []) =
    refl
  fromTerm∘toTerm (con (starᵏ s) []) =
    refl
  fromTerm∘toTerm (con (unitrecᵏ p q) (A ∷ₜ t ∷ₜ u ∷ₜ [])) =
    cong₃ (λ A t u → con (unitrecᵏ p q) (A ∷ₜ t ∷ₜ u ∷ₜ []))
      (fromTerm∘toTerm A) (fromTerm∘toTerm t) (fromTerm∘toTerm u)
  fromTerm∘toTerm (con (ΠΣᵏ b p q) (A ∷ₜ B ∷ₜ [])) =
    cong₂ (λ A B → con (ΠΣᵏ b p q) (A ∷ₜ B ∷ₜ [])) (fromTerm∘toTerm A)
      (fromTerm∘toTerm B)
  fromTerm∘toTerm (con (lamᵏ p) (t ∷ₜ [])) =
    cong (λ t → con (lamᵏ p) (t ∷ₜ [])) (fromTerm∘toTerm t)
  fromTerm∘toTerm (con (appᵏ p) (t ∷ₜ u ∷ₜ [])) =
    cong₂ (λ t u → con (appᵏ p) (t ∷ₜ u ∷ₜ [])) (fromTerm∘toTerm t)
      (fromTerm∘toTerm u)
  fromTerm∘toTerm (con (prodᵏ s p) (t ∷ₜ u ∷ₜ [])) =
    cong₂ (λ t u → con (prodᵏ s p) (t ∷ₜ u ∷ₜ [])) (fromTerm∘toTerm t)
      (fromTerm∘toTerm u)
  fromTerm∘toTerm (con (fstᵏ p) (t ∷ₜ [])) =
    cong (λ t → con (fstᵏ p) (t ∷ₜ [])) (fromTerm∘toTerm t)
  fromTerm∘toTerm (con (sndᵏ p) (t ∷ₜ [])) =
    cong (λ t → con (sndᵏ p) (t ∷ₜ [])) (fromTerm∘toTerm t)
  fromTerm∘toTerm (con (prodrecᵏ r p q) (A ∷ₜ t ∷ₜ u ∷ₜ [])) =
    cong₃ (λ A t u → con (prodrecᵏ r p q) (A ∷ₜ t ∷ₜ u ∷ₜ []))
      (fromTerm∘toTerm A) (fromTerm∘toTerm t) (fromTerm∘toTerm u)
  fromTerm∘toTerm (con ℕᵏ []) =
    refl
  fromTerm∘toTerm (con zeroᵏ []) =
    refl
  fromTerm∘toTerm (con sucᵏ (t ∷ₜ [])) =
    cong (λ t → con sucᵏ (t ∷ₜ [])) (fromTerm∘toTerm t)
  fromTerm∘toTerm (con (natrecᵏ p q r) (A ∷ₜ z ∷ₜ s ∷ₜ n ∷ₜ [])) =
    cong₄ (λ A z s n → con (natrecᵏ p q r) (A ∷ₜ z ∷ₜ s ∷ₜ n ∷ₜ []))
      (fromTerm∘toTerm A) (fromTerm∘toTerm z) (fromTerm∘toTerm s)
      (fromTerm∘toTerm n)
  fromTerm∘toTerm (con Idᵏ (A ∷ₜ t ∷ₜ u ∷ₜ [])) =
    cong₃ (λ A t u → con Idᵏ (A ∷ₜ t ∷ₜ u ∷ₜ [])) (fromTerm∘toTerm A)
      (fromTerm∘toTerm t) (fromTerm∘toTerm u)
  fromTerm∘toTerm (con rflᵏ []) = refl
  fromTerm∘toTerm (con (Jᵏ p q) (A ∷ₜ t ∷ₜ B ∷ₜ u ∷ₜ v ∷ₜ w ∷ₜ [])) =
    cong₆ (λ A t B u v w →
            con (Jᵏ p q) (A ∷ₜ t ∷ₜ B ∷ₜ u ∷ₜ v ∷ₜ w ∷ₜ []))
      (fromTerm∘toTerm A) (fromTerm∘toTerm t) (fromTerm∘toTerm B)
      (fromTerm∘toTerm u) (fromTerm∘toTerm v) (fromTerm∘toTerm w)
  fromTerm∘toTerm (con (Kᵏ p) (A ∷ₜ t ∷ₜ B ∷ₜ u ∷ₜ v ∷ₜ [])) =
    cong₅ (λ A t B u v → con (Kᵏ p) (A ∷ₜ t ∷ₜ B ∷ₜ u ∷ₜ v ∷ₜ []))
      (fromTerm∘toTerm A) (fromTerm∘toTerm t) (fromTerm∘toTerm B)
      (fromTerm∘toTerm u) (fromTerm∘toTerm v)
  fromTerm∘toTerm (con ([]-congᵏ s) (l ∷ₜ A ∷ₜ t ∷ₜ u ∷ₜ v ∷ₜ [])) =
    cong₅
      (λ l A t u v → con ([]-congᵏ s) (l ∷ₜ A ∷ₜ t ∷ₜ u ∷ₜ v ∷ₜ []))
      (fromTerm∘toTerm l) (fromTerm∘toTerm A) (fromTerm∘toTerm t)
      (fromTerm∘toTerm u) (fromTerm∘toTerm v)

opaque

  -- The function toTerm is injective.

  toTerm-injective :
    {t₁ t₂ : Term[ k ]′ n} → toTerm t₁ ≡ toTerm t₂ → t₁ ≡ t₂
  toTerm-injective {t₁} {t₂} eq =
    t₁                    ≡˘⟨ fromTerm∘toTerm _ ⟩
    fromTerm (toTerm t₁)  ≡⟨ cong fromTerm eq ⟩
    fromTerm (toTerm t₂)  ≡⟨ fromTerm∘toTerm _ ⟩
    t₂                    ∎

opaque

  -- The function fromTerm is injective.

  fromTerm-injective : fromTerm t₁ ≡ fromTerm t₂ → t₁ ≡ t₂
  fromTerm-injective {t₁} {t₂} eq =
    t₁                    ≡˘⟨ toTerm∘fromTerm _ ⟩
    toTerm (fromTerm t₁)  ≡⟨ cong toTerm eq ⟩
    toTerm (fromTerm t₂)  ≡⟨ toTerm∘fromTerm _ ⟩
    t₂                    ∎

------------------------------------------------------------------------
-- No-confusion lemmas

Level≢B : ∀ W → Level PE.≢ ⟦ W ⟧ F ▹ G
Level≢B (BΠ p q) ()
Level≢B (BΣ m p q) ()

Level≢ΠΣ : ∀ b → Level PE.≢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G
Level≢ΠΣ BMΠ ()
Level≢ΠΣ (BMΣ s) ()

U≢B : ∀ W → U l PE.≢ ⟦ W ⟧ F ▹ G
U≢B (BΠ p q) ()
U≢B (BΣ m p q) ()

U≢ΠΣ : ∀ b → U l PE.≢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G
U≢ΠΣ BMΠ ()
U≢ΠΣ (BMΣ s) ()

Lift≢B : ∀ W → Lift l A PE.≢ ⟦ W ⟧ F ▹ G
Lift≢B (BΠ p q) ()
Lift≢B (BΣ m p q) ()

Lift≢ΠΣ : ∀ b → Lift l A PE.≢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G
Lift≢ΠΣ BMΠ ()
Lift≢ΠΣ (BMΣ s) ()

ℕ≢B : ∀ W → ℕ PE.≢ ⟦ W ⟧ F ▹ G
ℕ≢B (BΠ p q) ()
ℕ≢B (BΣ m p q) ()

ℕ≢ΠΣ : ∀ b → ℕ PE.≢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G
ℕ≢ΠΣ BMΠ ()
ℕ≢ΠΣ (BMΣ s) ()

Empty≢B : ∀ W → Empty PE.≢ ⟦ W ⟧ F ▹ G
Empty≢B (BΠ p q) ()
Empty≢B (BΣ m p q) ()

Empty≢ΠΣ : ∀ b → Empty PE.≢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G
Empty≢ΠΣ BMΠ ()
Empty≢ΠΣ (BMΣ _) ()

Unit≢B : ∀ W → Unit s PE.≢ ⟦ W ⟧ F ▹ G
Unit≢B (BΠ p q) ()
Unit≢B (BΣ m p q) ()

Unit≢ΠΣ : ∀ b → Unit s PE.≢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G
Unit≢ΠΣ BMΠ ()
Unit≢ΠΣ (BMΣ _) ()

Id≢⟦⟧▷ : ∀ W → Id A t u PE.≢ ⟦ W ⟧ F ▹ G
Id≢⟦⟧▷ (BΠ _ _)   ()
Id≢⟦⟧▷ (BΣ _ _ _) ()

Id≢ΠΣ : ∀ b → Id A t u PE.≢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G
Id≢ΠΣ BMΠ     ()
Id≢ΠΣ (BMΣ _) ()

Π≢Σ : ∀ {m} → Π p₁ , q₁ ▷ F ▹ G PE.≢ Σ⟨ m ⟩ p₂ , q₂ ▷ H ▹ E
Π≢Σ ()

Σˢ≢Σʷ : Σˢ p₁ , q₁ ▷ F ▹ G PE.≢ Σʷ p₂ , q₂ ▷ H ▹ E
Σˢ≢Σʷ ()

------------------------------------------------------------------------
-- Weakening properties

opaque

  -- Relating weakening of terms with weakening of the alternative
  -- term representation.

  wk≡wk′ : (t : Term[ k ] n) → wk ρ t ≡ toTerm (wk′ ρ (fromTerm t))
  wk≡wk′ (var x) = refl
  wk≡wk′ (defn α) = refl
  wk≡wk′ Level = refl
  wk≡wk′ zeroᵘ = refl
  wk≡wk′ (sucᵘ t) = cong sucᵘ (wk≡wk′ t)
  wk≡wk′ (t₁ supᵘ t₂) = cong₂ _supᵘ_ (wk≡wk′ t₁) (wk≡wk′ t₂)
  wk≡wk′ (ωᵘ+ _) = refl
  wk≡wk′ (level t) = cong level (wk≡wk′ t)
  wk≡wk′ (U l) = cong U (wk≡wk′ l)
  wk≡wk′ (Lift l A) = cong₂ Lift (wk≡wk′ l) (wk≡wk′ A)
  wk≡wk′ (lift a) = cong lift (wk≡wk′ a)
  wk≡wk′ (lower a) = cong lower (wk≡wk′ a)
  wk≡wk′ (ΠΣ⟨ b ⟩ p , q ▷ t ▹ t₁) =
    cong₂ (ΠΣ⟨ b ⟩ p , q ▷_▹_) (wk≡wk′ t) (wk≡wk′ t₁)
  wk≡wk′ (lam p t) = cong (lam p) (wk≡wk′ t)
  wk≡wk′ (t ∘⟨ p ⟩ t₁) = cong₂ _∘_ (wk≡wk′ t) (wk≡wk′ t₁)
  wk≡wk′ (prod x p t t₁) = cong₂ prod! (wk≡wk′ t) (wk≡wk′ t₁)
  wk≡wk′ (fst p t) = cong (fst p) (wk≡wk′ t)
  wk≡wk′ (snd p t) = cong (snd p) (wk≡wk′ t)
  wk≡wk′ (prodrec r p q t t₁ t₂) =
    cong₃ (prodrec r p q) (wk≡wk′ t) (wk≡wk′ t₁) (wk≡wk′ t₂)
  wk≡wk′ ℕ = refl
  wk≡wk′ zero = refl
  wk≡wk′ (suc t) = cong suc (wk≡wk′ t)
  wk≡wk′ (natrec p q r t t₁ t₂ t₃) =
    cong₄ (natrec p q r) (wk≡wk′ t) (wk≡wk′ t₁) (wk≡wk′ t₂) (wk≡wk′ t₃)
  wk≡wk′ (Unit x) = refl
  wk≡wk′ (star x) = refl
  wk≡wk′ (unitrec p q t t₁ t₂) =
    cong₃ (unitrec p q) (wk≡wk′ t) (wk≡wk′ t₁) (wk≡wk′ t₂)
  wk≡wk′ Empty = refl
  wk≡wk′ (emptyrec p t t₁) =
    cong₂ (emptyrec p) (wk≡wk′ t) (wk≡wk′ t₁)
  wk≡wk′ (Id t t₁ t₂) =
    cong₃ Id (wk≡wk′ t) (wk≡wk′ t₁) (wk≡wk′ t₂)
  wk≡wk′ rfl = refl
  wk≡wk′ (J p q t t₁ t₂ t₃ t₄ t₅) =
    cong₆ (J p q) (wk≡wk′ t) (wk≡wk′ t₁) (wk≡wk′ t₂)
      (wk≡wk′ t₃) (wk≡wk′ t₄) (wk≡wk′ t₅)
  wk≡wk′ (K p t t₁ t₂ t₃ t₄) =
    cong₅ (K p) (wk≡wk′ t) (wk≡wk′ t₁) (wk≡wk′ t₂)
      (wk≡wk′ t₃) (wk≡wk′ t₄)
  wk≡wk′ ([]-cong _ l A t u v) =
    cong₅ []-cong! (wk≡wk′ l) (wk≡wk′ A) (wk≡wk′ t) (wk≡wk′ u)
      (wk≡wk′ v)

opaque mutual

  -- If two weakenings are equal under wkVar, then they are equal under
  -- wk′.

  wkVar-to-wk′ :
    (∀ x → wkVar ρ x ≡ wkVar ρ′ x) →
    (t : Term[ k ]′ n) → wk′ ρ t ≡ wk′ ρ′ t
  wkVar-to-wk′ eq (var x)    = cong var (eq x)
  wkVar-to-wk′ eq (con k ts) = cong (con k) (wkVar-to-wkArgs eq ts)

  wkVar-to-wkArgs :
    (∀ x → wkVar ρ x ≡ wkVar ρ′ x) →
    (ts : Args n as) → wkArgs ρ ts ≡ wkArgs ρ′ ts
  wkVar-to-wkArgs eq []              = refl
  wkVar-to-wkArgs eq (_∷ₜ_ {m} t ts) =
    cong₂ _∷ₜ_ (wkVar-to-wk′ (wkVar-lifts eq m) t)
      (wkVar-to-wkArgs eq ts)

opaque

  -- Extensionally equal weakenings, if applied to a term,
  -- yield the same weakened term.  Or:
  -- If two weakenings are equal under wkVar, then they are equal under
  -- wk.

  wkVar-to-wk :
    (∀ x → wkVar ρ x ≡ wkVar ρ′ x) →
    (t : Term[ k ] n) → wk ρ t ≡ wk ρ′ t
  wkVar-to-wk {ρ} {ρ′} eq t = begin
    wk ρ t                       ≡⟨ wk≡wk′ t ⟩
    toTerm (wk′ ρ (fromTerm t))  ≡⟨ cong toTerm (wkVar-to-wk′ eq _) ⟩
    toTerm (wk′ ρ′ (fromTerm t)) ≡˘⟨ wk≡wk′ t ⟩
    wk ρ′ t                      ∎

opaque mutual

  -- id is the identity renaming for the alternative term representation

  wk′-id : (t : Term[ k ]′ n) → wk′ id t ≡ t
  wk′-id (var x)    = refl
  wk′-id (con k ts) = cong (con k) (wkArgs-id ts)

  wkArgs-id : (ts : Args n as) → wkArgs id ts ≡ ts
  wkArgs-id []              = refl
  wkArgs-id (_∷ₜ_ {m} t ts) =
    cong₂ _∷ₜ_ (trans (wkVar-to-wk′ (wkVar-lifts-id m) t) (wk′-id t))
      (wkArgs-id ts)

opaque

  -- id is the identity renaming.

  wk-id : (t : Term[ k ] n) → wk id t ≡ t
  wk-id t = begin
    wk id t                      ≡⟨ wk≡wk′ t ⟩
    toTerm (wk′ id (fromTerm t)) ≡⟨ cong toTerm (wk′-id _) ⟩
    toTerm (fromTerm t)          ≡⟨ toTerm∘fromTerm _ ⟩
    t                            ∎

-- lift id  is also the identity renaming.

wk-lift-id : (t : Term[ k ] (1+ n)) → wk (lift id) t ≡ t
wk-lift-id t = trans (wkVar-to-wk wkVar-lift-id t) (wk-id t)

opaque mutual

  -- The function wk′ commutes with composition.

  wk′-comp :
    (ρ : Wk m ℓ) (ρ′ : Wk ℓ n) (t : Term[ k ]′ n) →
    wk′ ρ (wk′ ρ′ t) ≡ wk′ (ρ • ρ′) t
  wk′-comp ρ ρ′ (var x)    = cong var (wkVar-comp ρ ρ′ x)
  wk′-comp _ _  (con k ts) = cong (con k) (wkArgs-comp ts)

  wkArgs-comp :
    (ts : Args n as) →
    wkArgs ρ (wkArgs ρ′ ts) ≡ wkArgs (ρ • ρ′) ts
  wkArgs-comp []              = refl
  wkArgs-comp (_∷ₜ_ {m} t ts) =
    cong₂ _∷ₜ_
      (trans (wk′-comp _ _ t) (wkVar-to-wk′ (wkVar-comps m _ _) t))
      (wkArgs-comp ts)

opaque

  -- The function wk commutes with composition.

  wk-comp :
    (ρ : Wk m ℓ) (ρ′ : Wk ℓ n) (t : Term[ k ] n) →
    wk ρ (wk ρ′ t) ≡ wk (ρ • ρ′) t
  wk-comp ρ ρ′ t = begin
    wk ρ (wk ρ′ t)                                           ≡⟨ cong (wk ρ) (wk≡wk′ t) ⟩
    wk ρ (toTerm (wk′ ρ′ (fromTerm t)))                      ≡⟨ wk≡wk′ _ ⟩
    toTerm (wk′ ρ (fromTerm (toTerm (wk′ ρ′ (fromTerm t))))) ≡⟨ cong (λ x → toTerm (wk′ ρ x)) (fromTerm∘toTerm _) ⟩
    toTerm (wk′ ρ (wk′ ρ′ (fromTerm t)))                     ≡⟨ cong toTerm (wk′-comp ρ ρ′ _) ⟩
    toTerm (wk′ (ρ • ρ′) (fromTerm t))                       ≡˘⟨ wk≡wk′ t ⟩
    wk (ρ • ρ′) t                                            ∎

opaque

  -- id is the right identity of weakening composition

  •-idʳ : (ρ : Wk m n) → ρ • id ≡ ρ
  •-idʳ id = refl
  •-idʳ (step ρ) = cong step (•-idʳ ρ)
  •-idʳ (lift ρ) = refl


opaque

  -- A composition lemma for wk₀.

  wk₀-comp : (ρ : Wk m n) (t : Term[ k ] 0) → wk ρ (wk wk₀ t) ≡ wk wk₀ t
  wk₀-comp ρ t = begin
    wk ρ (wk wk₀ t) ≡⟨ wk-comp ρ wk₀ t ⟩
    wk (ρ • wk₀) t  ≡⟨ cong (λ w → wk w t) (wk₀-invariant ρ) ⟩
    wk wk₀ t        ∎


-- The following lemmata are variations on the equality
--
--   wk1 ∘ ρ = lift ρ ∘ wk1.
--
-- Typing:  Γ∙A ≤ Γ ≤ Δ  <==>  Γ∙A ≤ Δ∙A ≤ Δ.

wk1-wk : (ρ : Wk m n) (t : Term[ k ] n) → wk1 (wk ρ t) ≡ wk (step ρ) t
wk1-wk ρ t = wk-comp (step id) ρ t

lift-wk1 :
  (ρ : Wk m n) (t : Term[ k ] n) → wk (lift ρ) (wk1 t) ≡ wk (step ρ) t
lift-wk1 pr A = trans (wk-comp (lift pr) (step id) A)
                      (sym (cong (λ x → wk x A) (lift-step-comp pr)))

wk1-wk≡lift-wk1 :
  (ρ : Wk m n) (t : Term[ k ] n) → wk1 (wk ρ t) ≡ wk (lift ρ) (wk1 t)
wk1-wk≡lift-wk1 ρ t = trans (wk1-wk ρ t) (sym (lift-wk1 ρ t))

opaque mutual

  -- The function wk′ ρ is injective.

  wk′-injective : {t₁ t₂ : Term[ k ]′ n} → wk′ ρ t₁ ≡ wk′ ρ t₂ → t₁ ≡ t₂
  wk′-injective {t₁ = var x₁} {t₂ = var x₂} eq =
    cong var (wkVar-injective (var-cong⁻¹ eq))
  wk′-injective {t₁ = var _}      {t₂ = con _ _}    ()
  wk′-injective {t₁ = con _ _}    {t₂ = var _}      ()
  wk′-injective {t₁ = con k₁ ts₁} {t₂ = con k₂ ts₂} eq
    with con-cong⁻¹ eq
  … | refl , refl , eq = cong (con _) (wkArgs-injective eq)

  -- The function wkArgs ρ is injective.

  wkArgs-injective : wkArgs ρ ts₁ ≡ wkArgs ρ ts₂ → ts₁ ≡ ts₂
  wkArgs-injective {ts₁ = []}     {ts₂ = []}     _  = refl
  wkArgs-injective {ts₁ = _ ∷ₜ _} {ts₂ = _ ∷ₜ _} eq with ∷-cong⁻¹ eq
  … | eq₁ , eq₂ = cong₂ _∷ₜ_ (wk′-injective eq₁) (wkArgs-injective eq₂)

opaque

  -- The function wk ρ is injective.

  wk-injective : wk ρ t₁ ≡ wk ρ t₂ → t₁ ≡ t₂
  wk-injective {ρ} {t₁} {t₂} =
    wk ρ t₁ ≡ wk ρ t₂                                            →⟨ (λ eq → trans (sym (wk≡wk′ _)) (trans eq (wk≡wk′ _))) ⟩
    toTerm (wk′ ρ (fromTerm t₁)) ≡ toTerm (wk′ ρ (fromTerm t₂))  →⟨ toTerm-injective ⟩
    wk′ ρ (fromTerm t₁) ≡ wk′ ρ (fromTerm t₂)                    →⟨ wk′-injective ⟩
    fromTerm t₁ ≡ fromTerm t₂                                    →⟨ fromTerm-injective ⟩
    t₁ ≡ t₂                                                      □

------------------------------------------------------------------------
-- Substitution properties.

opaque

  -- Relating substitution of terms with substitution of the alternative
  -- term representation.

  subst≡subst′ :
    (t : Term[ k ] n) → t [ σ ] ≡ toTerm (fromTerm t [ σ ]′)
  subst≡subst′ (var x) = sym (toTerm∘fromTerm _)
  subst≡subst′ (defn α) = refl
  subst≡subst′ Level = refl
  subst≡subst′ zeroᵘ = refl
  subst≡subst′ (sucᵘ t) = cong sucᵘ (subst≡subst′ t)
  subst≡subst′ (t₁ supᵘ t₂) =
    cong₂ _supᵘ_ (subst≡subst′ t₁) (subst≡subst′ t₂)
  subst≡subst′ (ωᵘ+ _) =
    refl
  subst≡subst′ (level t) =
    cong level (subst≡subst′ t)
  subst≡subst′ (U l) = cong U (subst≡subst′ l)
  subst≡subst′ (Lift l A) = cong₂ Lift (subst≡subst′ l) (subst≡subst′ A)
  subst≡subst′ (lift a) = cong lift (subst≡subst′ a)
  subst≡subst′ (lower a) = cong lower (subst≡subst′ a)
  subst≡subst′ (ΠΣ⟨ b ⟩ p , q ▷ t ▹ t₁) =
    cong₂ (ΠΣ⟨ b ⟩ p , q ▷_▹_) (subst≡subst′ t) (subst≡subst′ t₁)
  subst≡subst′ (lam p t) = cong (lam p) (subst≡subst′ t)
  subst≡subst′ (t ∘⟨ p ⟩ t₁) =
    cong₂ _∘_ (subst≡subst′ t) (subst≡subst′ t₁)
  subst≡subst′ (prod x p t t₁) =
    cong₂ prod! (subst≡subst′ t) (subst≡subst′ t₁)
  subst≡subst′ (fst p t) = cong (fst p) (subst≡subst′ t)
  subst≡subst′ (snd p t) = cong (snd p) (subst≡subst′ t)
  subst≡subst′ (prodrec r p q t t₁ t₂) =
    cong₃ (prodrec r p q) (subst≡subst′ t)
      (subst≡subst′ t₁) (subst≡subst′ t₂)
  subst≡subst′ ℕ = refl
  subst≡subst′ zero = refl
  subst≡subst′ (suc t) = cong suc (subst≡subst′ t)
  subst≡subst′ (natrec p q r t t₁ t₂ t₃) =
    cong₄ (natrec p q r) (subst≡subst′ t)
      (subst≡subst′ t₁) (subst≡subst′ t₂) (subst≡subst′ t₃)
  subst≡subst′ (Unit x) = refl
  subst≡subst′ (star x) = refl
  subst≡subst′ (unitrec p q t t₁ t₂) =
    cong₃ (unitrec p q) (subst≡subst′ t)
      (subst≡subst′ t₁) (subst≡subst′ t₂)
  subst≡subst′ Empty = refl
  subst≡subst′ (emptyrec p t t₁) =
    cong₂ (emptyrec p) (subst≡subst′ t) (subst≡subst′ t₁)
  subst≡subst′ (Id t t₁ t₂) =
    cong₃ Id (subst≡subst′ t) (subst≡subst′ t₁) (subst≡subst′ t₂)
  subst≡subst′ rfl = refl
  subst≡subst′ (J p q t t₁ t₂ t₃ t₄ t₅) =
    cong₆ (J p q) (subst≡subst′ t) (subst≡subst′ t₁) (subst≡subst′ t₂)
      (subst≡subst′ t₃) (subst≡subst′ t₄) (subst≡subst′ t₅)
  subst≡subst′ (K p t t₁ t₂ t₃ t₄) =
    cong₅ (K p) (subst≡subst′ t) (subst≡subst′ t₁) (subst≡subst′ t₂)
      (subst≡subst′ t₃) (subst≡subst′ t₄)
  subst≡subst′ ([]-cong _ l A t u v) =
    cong₅ []-cong! (subst≡subst′ l) (subst≡subst′ A) (subst≡subst′ t)
      (subst≡subst′ u) (subst≡subst′ v)

-- Two substitutions σ and σ′ are equal if they are pointwise equal,
-- i.e., agree on all variables.
--
--   ∀ x →  σ x ≡ σ′ x

-- If  σ = σ′  then  lift σ = lift σ′.

substVar-lift : (∀ x → σ x ≡ σ′ x) → ∀ x → liftSubst σ x ≡ liftSubst σ′ x

substVar-lift eq x0     = refl
substVar-lift eq (x +1) = cong wk1 (eq x)

substVar-lifts : (∀ x → σ x ≡ σ′ x) → ∀ n x → liftSubstn σ n x ≡ liftSubstn σ′ n x

substVar-lifts eq 0 x           = eq x
substVar-lifts eq (1+ n) x0     = refl
substVar-lifts eq (1+ n) (x +1) = cong wk1 (substVar-lifts eq n x)

opaque

  -- A form of congruence for consSubst.

  consSubst-cong :
    t₁ ≡ t₂ →
    (∀ x → σ₁ x ≡ σ₂ x) →
    ∀ x → consSubst σ₁ t₁ x ≡ consSubst σ₂ t₂ x
  consSubst-cong refl _  x0     = refl
  consSubst-cong _    eq (x +1) = eq x

opaque

  -- An η-law for consSubst.

  consSubst-η : ∀ x → consSubst (tail σ) (head σ) x ≡ σ x
  consSubst-η x0     = refl
  consSubst-η (_ +1) = refl

-- If σ = σ′ then wk1Subst σ = wk1Subst σ′.

wk1Subst-cong :
  (∀ x → σ x ≡ σ′ x) →
  ∀ x → wk1Subst σ x ≡ wk1Subst σ′ x
wk1Subst-cong eq x = cong wk1 (eq x)

opaque

  -- A preservation lemma for wkSubst.

  wkSubst-cong :
    (∀ x → σ₁ x ≡ σ₂ x) →
    ∀ x → wkSubst n σ₁ x ≡ wkSubst n σ₂ x
  wkSubst-cong {n = 0}    σ₁≡σ₂ = σ₁≡σ₂
  wkSubst-cong {n = 1+ _} σ₁≡σ₂ = wk1Subst-cong (wkSubst-cong σ₁≡σ₂)

opaque mutual

  -- If  σ = σ′  then  t [ σ ]′ = t [ σ′ ]′.

  substVar-to-subst′ :
    ((x : Fin n) → σ x ≡ σ′ x) →
    (t : Term[ k ]′ n) → t [ σ ]′ ≡ t [ σ′ ]′
  substVar-to-subst′ eq (var x)    = cong fromTerm (eq x)
  substVar-to-subst′ eq (con k ts) =
    cong (con k) (substVar-to-substArgs eq ts)

  substVar-to-substArgs :
    ((x : Fin n) → σ₁ x ≡ σ₂ x) →
    (ts : Args n as) → substArgs ts σ₁ ≡ substArgs ts σ₂
  substVar-to-substArgs eq []              = refl
  substVar-to-substArgs eq (_∷ₜ_ {m} t ts) =
    cong₂ _∷ₜ_ (substVar-to-subst′ (substVar-lifts eq m) t)
      (substVar-to-substArgs eq ts)

opaque

  -- If σ₁ and σ₂ are pointwise equal, then t [ σ₁ ] is equal to
  -- t [ σ₂ ].

  substVar-to-subst :
    ((x : Fin n) → σ₁ x ≡ σ₂ x) →
    (t : Term[ k ] n) → t [ σ₁ ] ≡ t [ σ₂ ]
  substVar-to-subst {σ₁} {σ₂} eq t =
    t [ σ₁ ]                     ≡⟨ subst≡subst′ t ⟩
    toTerm (fromTerm t [ σ₁ ]′)  ≡⟨ cong toTerm (substVar-to-subst′ eq (fromTerm t)) ⟩
    toTerm (fromTerm t [ σ₂ ]′)  ≡˘⟨ subst≡subst′ t ⟩
    t [ σ₂ ]                     ∎

-- lift id = id  (as substitutions)

subst-lift-id : (x : Fin (1+ n)) → (liftSubst idSubst) x ≡ idSubst x
subst-lift-id x0     = refl
subst-lift-id (x +1) = refl

subst-lifts-id : (n : Nat) → (x : Fin (n + m)) → (liftSubstn idSubst n) x ≡ idSubst x
subst-lifts-id 0 x = refl
subst-lifts-id (1+ n) x0 = refl
subst-lifts-id (1+ n) (x +1) = cong wk1 (subst-lifts-id n x)

opaque mutual

  -- idSubst is the identity substitution for the alternative term
  -- representation.

  subst′-id : (t : Term[ k ]′ n) → t [ idSubst ]′ ≡ t
  subst′-id (var x) = refl
  subst′-id (con k ts) = cong (con k) (substArgs-id ts)

  substArgs-id : (ts : Args n as) → substArgs ts idSubst ≡ ts
  substArgs-id []              = refl
  substArgs-id (_∷ₜ_ {m} t ts) =
    cong₂ _∷ₜ_
      (trans (substVar-to-subst′ (subst-lifts-id m) t) (subst′-id _))
      (substArgs-id ts)

opaque

  -- idSubst is the identity substitution.

  subst-id : (t : Term[ k ] n) → t [ idSubst ] ≡ t
  subst-id t = begin
    t [ idSubst ]                    ≡⟨ subst≡subst′ t ⟩
    toTerm (fromTerm t [ idSubst ]′) ≡⟨ cong toTerm (subst′-id (fromTerm t)) ⟩
    toTerm (fromTerm t)              ≡⟨ toTerm∘fromTerm t ⟩
    t                                ∎

opaque

  -- The identity substitution is a left identity for _ₛ•ₛ_ (in a
  -- certain sense).

  idSubst-ₛ•ₛˡ : (x : Fin n) → (idSubst ₛ•ₛ σ) x ≡ σ x
  idSubst-ₛ•ₛˡ _ = subst-id _

opaque

  -- The identity substitution is a right identity for _ₛ•ₛ_ (in a
  -- certain sense).

  idSubst-ₛ•ₛʳ : (x : Fin n) → (σ ₛ•ₛ idSubst) x ≡ σ x
  idSubst-ₛ•ₛʳ _ = refl

opaque

  -- The substitution liftSubstn idSubst m does not have any effect.

  [idSubst⇑ⁿ]≡ :
    ∀ m {t : Term[ k ] (m + n)} → t [ liftSubstn idSubst m ] ≡ t
  [idSubst⇑ⁿ]≡ m {t} =
    t [ liftSubstn idSubst m ]  ≡⟨ substVar-to-subst (subst-lifts-id m) t ⟩
    t [ idSubst ]               ≡⟨ subst-id _ ⟩
    t                           ∎

-- Correctness of composition of weakening and substitution.

-- Composition of liftings is lifting of the composition.
-- lift ρ •ₛ lift σ = lift (ρ •ₛ σ)

subst-lift-•ₛ : (t : Term[ k ] (1+ n))
              → t [ lift ρ •ₛ liftSubst σ ]
              ≡ t [ liftSubst (ρ •ₛ σ) ]
subst-lift-•ₛ =
  substVar-to-subst (λ { x0 → refl ; (x +1) → sym (wk1-wk≡lift-wk1 _ _)})

helper1 : (n : Nat) (x : Fin (1+ n + m)) →
      (lift (liftn ρ n) •ₛ liftSubst (liftSubstn σ n)) x ≡
      liftSubst (liftSubstn (ρ •ₛ σ) n) x
helper1 0      x0     = refl
helper1 0      (x +1) = sym (wk1-wk≡lift-wk1 _ _)
helper1 (1+ n) x0     = refl
helper1 (1+ n) (x +1) = trans (sym (wk1-wk≡lift-wk1 _ _)) (cong wk1 (helper1 n x))

subst-lifts-•ₛ :
  ∀ m (t : Term[ k ] (m + n)) →
  t [ liftn ρ m •ₛ (σ ⇑[ m ]) ] ≡ t [ (ρ •ₛ σ) ⇑[ m ] ]
subst-lifts-•ₛ 0 t = refl
subst-lifts-•ₛ (1+ n) t = substVar-to-subst (helper1 n) t

subst′-lifts-•ₛ :
  ∀ m (t : Term[ k ]′ (m + n)) →
  t [ liftn ρ m •ₛ (σ ⇑[ m ]) ]′ ≡ t [ (ρ •ₛ σ) ⇑[ m ] ]′
subst′-lifts-•ₛ 0 t = refl
subst′-lifts-•ₛ (1+ n) t = substVar-to-subst′ (helper1 n) t


-- lift σ ₛ• lift ρ = lift (σ ₛ• ρ)

subst-lift-ₛ• : (t : Term[ k ] (1+ n))
              → t [ liftSubst σ ₛ• lift ρ ]
              ≡ t [ liftSubst (σ ₛ• ρ) ]
subst-lift-ₛ• = substVar-to-subst (λ { x0 → refl ; (x +1) → refl})

helper2 : (n : Nat) → (x : Fin (1+ n + m))
        → liftSubst (liftSubstn σ n) (wkVar (lift (liftn ρ n)) x) ≡
          liftSubst (liftSubstn (λ x₁ → σ (wkVar ρ x₁)) n) x
helper2 0 x0          = refl
helper2 0 (x +1)      = refl
helper2 (1+ n) x0     = refl
helper2 (1+ n) (x +1) = cong wk1 (helper2 n x)

subst-lifts-ₛ• :
  ∀ m (t : Term[ k ] (m + n)) →
  t [ (σ ⇑[ m ]) ₛ• liftn ρ m ] ≡ t [ (σ ₛ• ρ) ⇑[ m ] ]
subst-lifts-ₛ• 0 t = refl
subst-lifts-ₛ• (1+ n) t = substVar-to-subst (helper2 n) t

opaque

  -- A variant of the above property for the alternative term
  -- representation.

  subst′-lifts-ₛ• :
    ∀ m (t : Term[ k ]′ (m + n)) →
    t [ (σ ⇑[ m ]) ₛ• liftn ρ m ]′ ≡ t [ (σ ₛ• ρ) ⇑[ m ] ]′
  subst′-lifts-ₛ• 0 t = refl
  subst′-lifts-ₛ• (1+ n) t = substVar-to-subst′ (helper2 n) t



opaque mutual

  -- Soundness of weakening-substitution composition for the alternative
  -- term representation.

  wk′-subst′ : (t : Term[ k ]′ n) → wk′ ρ (t [ σ ]′) ≡ t [ ρ •ₛ σ ]′
  wk′-subst′ {ρ} {σ} (var x) = begin
    wk′ ρ (var x [ σ ]′)                       ≡⟨⟩
    wk′ ρ (fromTerm (σ x))                     ≡˘⟨ fromTerm∘toTerm _ ⟩
    fromTerm (toTerm (wk′ ρ (fromTerm (σ x)))) ≡˘⟨ cong fromTerm (wk≡wk′ (σ x)) ⟩
    fromTerm (wk ρ (σ x))                      ≡⟨⟩
    (var x [ ρ •ₛ σ ]′)                        ∎
  wk′-subst′ (con k ts) = cong (con k) (wkArgs-substArgs ts)

  wkArgs-substArgs :
    (ts : Args n as) → wkArgs ρ (substArgs ts σ) ≡ substArgs ts (ρ •ₛ σ)
  wkArgs-substArgs []              = refl
  wkArgs-substArgs (_∷ₜ_ {m} t ts) =
    cong₂ _∷ₜ_
      (trans (wk′-subst′ t)
         (substVar-to-subst′ (subst-lifts-•ₛ m ∘→ var) t))
      (wkArgs-substArgs ts)

opaque

  -- Soundness of weakening-substitution composition.

  wk-subst : (t : Term[ k ] n) → wk ρ (t [ σ ]) ≡ t [ ρ •ₛ σ ]
  wk-subst {ρ} {σ} t = begin
    wk ρ (t [ σ ])                                         ≡⟨ cong (wk ρ) (subst≡subst′ t) ⟩
    wk ρ (toTerm (fromTerm t [ σ ]′))                      ≡⟨ wk≡wk′ _ ⟩
    toTerm (wk′ ρ (fromTerm (toTerm (fromTerm t [ σ ]′)))) ≡⟨ cong (λ x → toTerm (wk′ ρ x)) (fromTerm∘toTerm _ ) ⟩
    toTerm (wk′ ρ (fromTerm t [ σ ]′))                     ≡⟨ cong toTerm (wk′-subst′ (fromTerm t)) ⟩
    toTerm (fromTerm t [ ρ •ₛ σ ]′)                        ≡˘⟨ subst≡subst′ t ⟩
    t [ ρ •ₛ σ ]                                           ∎

-- _[ σ ] ∘ wk ρ = _[ σ •ₛ ρ ]

mutual

  -- Soundness of substitution-weakening composition for the alternative
  -- term representation.

  subst′-wk′ : (t : Term[ k ]′ n) → wk′ ρ t [ σ ]′ ≡ t [ σ ₛ• ρ ]′
  subst′-wk′ (var x)    = refl
  subst′-wk′ (con k ts) = cong (con k) (substArgs-wkArgs ts)

  substArgs-wkArgs :
    (ts : Args n as) → substArgs (wkArgs ρ ts) σ ≡ substArgs ts (σ ₛ• ρ)
  substArgs-wkArgs []              = refl
  substArgs-wkArgs (_∷ₜ_ {m} t ts) =
    cong₂ _∷ₜ_
      (trans (subst′-wk′ t)
         (substVar-to-subst′ (subst-lifts-ₛ• m ∘→ var) t))
      (substArgs-wkArgs ts)

opaque

  -- Soundness of substitution-weakening composition.

  subst-wk : (t : Term[ k ] n) → wk ρ t [ σ ] ≡ t [ σ ₛ• ρ ]
  subst-wk {ρ} {σ} t = begin
    wk ρ t [ σ ]                                           ≡⟨ cong (_[ σ ]) (wk≡wk′ t) ⟩
    toTerm (wk′ ρ (fromTerm t)) [ σ ]                      ≡⟨ subst≡subst′ (toTerm (wk′ ρ (fromTerm t))) ⟩
    toTerm (fromTerm (toTerm (wk′ ρ (fromTerm t))) [ σ ]′) ≡⟨ cong (λ x → toTerm (x [ σ ]′)) (fromTerm∘toTerm (wk′ ρ (fromTerm t))) ⟩
    toTerm (wk′ ρ (fromTerm t) [ σ ]′)                     ≡⟨ cong toTerm (subst′-wk′ (fromTerm t)) ⟩
    toTerm (fromTerm t [ σ ₛ• ρ ]′)                        ≡˘⟨ subst≡subst′ t ⟩
    t [ σ ₛ• ρ ]                                           ∎

opaque

  -- Applying wk1Subst σ is the same thing as applying σ and then
  -- weakening one step.

  wk1Subst-wk1 : (t : Term[ k ] n) → t [ wk1Subst σ ] ≡ wk1 (t [ σ ])
  wk1Subst-wk1 {σ} t =
    t [ wk1Subst σ ]    ≡⟨⟩
    t [ step id •ₛ σ ]  ≡˘⟨ wk-subst t ⟩
    wk1 (t [ σ ])       ∎

opaque

  -- Applying liftSubst σ to wk1 t amounts to the same thing as first
  -- applying σ and then weakening the result one step.

  wk1-liftSubst :
    (t : Term[ k ] n) → wk1 t [ liftSubst σ ] ≡ wk1 (t [ σ ])
  wk1-liftSubst {σ} t =
    wk1 t [ liftSubst σ ]         ≡⟨ subst-wk t ⟩
    t [ liftSubst σ ₛ• step id ]  ≡⟨⟩
    t [ wk1Subst σ ]              ≡⟨ wk1Subst-wk1 t ⟩
    wk1 (t [ σ ])                 ∎

opaque

  -- Applying σ ⇑[ 2 ] to wk2 t amounts to the same thing as first
  -- applying σ and then weakening the result two steps.

  wk2-liftSubst :
    (t : Term[ k ] n) → wk2 t [ σ ⇑[ 2 ] ] ≡ wk2 (t [ σ ])
  wk2-liftSubst {σ} t =
    wk2 t [ σ ⇑[ 2 ] ]   ≡⟨ wk1-liftSubst (wk1 t) ⟩
    wk1 (wk1 t [ σ ⇑ ])  ≡⟨ cong wk1 (wk1-liftSubst t) ⟩
    wk2 (t [ σ ])        ∎

-- Composition of liftings is lifting of the composition.

wk-subst-lift : (G : Term[ k ] (1+ n))
              → wk (lift ρ) (G [ liftSubst σ ])
              ≡ G [ liftSubst (ρ •ₛ σ) ]
wk-subst-lift G = trans (wk-subst G) (subst-lift-•ₛ G)

-- Renaming with ρ is the same as substituting with ρ turned into a substitution.

wk≡subst : (ρ : Wk m n) (t : Term[ k ] n) → wk ρ t ≡ t [ toSubst ρ ]
wk≡subst ρ t = trans (cong (wk ρ) (sym (subst-id t))) (wk-subst t)

opaque

  -- The function toSubst commutes, in a certain sense, with lifting.

  toSubst-liftn : ∀ k x → toSubst (liftn ρ k) x ≡ (toSubst ρ ⇑[ k ]) x
  toSubst-liftn 0      _      = refl
  toSubst-liftn (1+ _) x0     = refl
  toSubst-liftn (1+ k) (x +1) =
    cong wk1 $ toSubst-liftn k x

opaque

  -- The application of a lifted weakening can be expressed as the
  -- application of a lifted substitution.

  wk-liftn :
    ∀ m {t : Term[ k ] (m + n)} →
    wk (liftn ρ m) t ≡ t [ toSubst ρ ⇑[ m ] ]
  wk-liftn {ρ} m {t} =
    wk (liftn ρ m) t           ≡⟨ wk≡subst _ _ ⟩
    t [ toSubst (liftn ρ m) ]  ≡⟨ substVar-to-subst (toSubst-liftn m) t ⟩
    t [ toSubst ρ ⇑[ m ] ]     ∎

-- Composition of substitutions.

-- Composition of liftings is lifting of the composition.

substCompLift : ∀ x
              → (liftSubst σ ₛ•ₛ liftSubst σ′) x
              ≡ (liftSubst (σ ₛ•ₛ σ′)) x
substCompLift                    x0    = refl
substCompLift {σ = σ} {σ′ = σ′} (x +1) = trans (subst-wk (σ′ x)) (sym (wk-subst (σ′ x)))

substCompLifts : ∀ n x
              → (liftSubstn σ n ₛ•ₛ liftSubstn σ′ n) x
              ≡ (liftSubstn (σ ₛ•ₛ σ′) n) x
substCompLifts                   0       x     = refl
substCompLifts                   (1+ n)  x0    = refl
substCompLifts {σ = σ} {σ′ = σ′} (1+ n) (x +1) =
  trans (substCompLift {σ = liftSubstn σ n} {σ′ = liftSubstn σ′ n} (x +1))
        (cong wk1 (substCompLifts n x))


opaque mutual

  -- Soundness of the composition of substitutions for the alternative
  -- term representation.

  subst′CompEq :
    (t : Term[ k ]′ n) → t [ σ′ ]′ [ σ ]′ ≡ t [ σ ₛ•ₛ σ′ ]′
  subst′CompEq {σ′} {σ} (var x) = begin
    fromTerm (σ′ x) [ σ ]′                     ≡˘⟨ fromTerm∘toTerm _ ⟩
    fromTerm (toTerm (fromTerm (σ′ x) [ σ ]′)) ≡˘⟨ cong fromTerm (subst≡subst′ (σ′ x)) ⟩
    fromTerm (σ′ x [ σ ])                      ∎
  subst′CompEq (con k ts) = cong (con k) (substArgsCompEq ts)

  substArgsCompEq :
    (ts : Args n as) →
    substArgs (substArgs ts σ₂) σ₁ ≡ substArgs ts (σ₁ ₛ•ₛ σ₂)
  substArgsCompEq []              = refl
  substArgsCompEq (_∷ₜ_ {m} t ts) =
    cong₂ _∷ₜ_
      (trans (subst′CompEq t) (substVar-to-subst′ (substCompLifts m) t))
      (substArgsCompEq ts)

opaque

  -- Soundness of the composition of substitutions.

  substCompEq : (t : Term[ k ] n) → t [ σ′ ] [ σ ] ≡ t [ σ ₛ•ₛ σ′ ]
  substCompEq {σ′} {σ} t = begin
    t [ σ′ ] [ σ ]                                         ≡⟨ subst≡subst′ (t [ σ′ ]) ⟩
    toTerm (fromTerm (t [ σ′ ]) [ σ ]′)                    ≡⟨ cong (λ x → toTerm (fromTerm x [ σ ]′)) (subst≡subst′ t) ⟩
    toTerm (fromTerm (toTerm (fromTerm t [ σ′ ]′)) [ σ ]′) ≡⟨ cong (λ x → toTerm (x [ σ ]′)) (fromTerm∘toTerm (fromTerm t [ σ′ ]′)) ⟩
    toTerm ((fromTerm t [ σ′ ]′) [ σ ]′)                   ≡⟨ cong toTerm (subst′CompEq (fromTerm t)) ⟩
    toTerm (fromTerm t [ σ ₛ•ₛ σ′ ]′)                      ≡˘⟨ subst≡subst′ t ⟩
    t [ σ ₛ•ₛ σ′ ]                                         ∎

-- Weakening single substitutions.

-- Pulling apart a weakening composition in specific context _[a].

wk-comp-subst :
  (ρ : Wk m ℓ) (ρ′ : Wk ℓ n) (t : Term[ k ] (1+ n)) →
  wk (lift (ρ • ρ′)) t [ u ]₀ ≡ wk (lift ρ) (wk (lift ρ′) t) [ u ]₀
wk-comp-subst _ _ t =
  cong _[ _ ]₀ (sym (wk-comp _ _ t))

-- Pushing a weakening into a single substitution.
-- ρ (t[a]) = ((lift ρ) t)[ρ a]

wk-β :
  (t : Term[ k ] (1+ n)) → wk ρ (t [ u ]₀) ≡ wk (lift ρ) t [ wk ρ u ]₀
wk-β t = trans (wk-subst t) (sym (trans (subst-wk t)
               (substVar-to-subst (λ { x0 → refl ; (x +1) → refl}) t)))

-- Pushing a weakening into a single shifting substitution.
-- If  ρ′ = lift ρ  then  ρ′(t[a]↑) = ρ′(t) [ρ′(a)]↑

wk-β↑ :
  (t : Term[ k ] (1+ n)) →
  wk (lift ρ) (t [ u ]↑) ≡ wk (lift ρ) t [ wk (lift ρ) u ]↑
wk-β↑ t = trans (wk-subst t) (sym (trans (subst-wk t)
                (substVar-to-subst (λ { x0 → refl ; (x +1) → refl}) t)))

-- Pushing a weakening into a double shifting substitution.

wk-β↑² :
  (t : Term[ k ] (1+ n)) →
  wk (liftn ρ 2) (t [ u ]↑²) ≡ wk (lift ρ) t [ wk (liftn ρ 2) u ]↑²
wk-β↑² t = trans (wk-subst t) (sym (trans (subst-wk t)
                 (substVar-to-subst (λ { x0 → refl ; (x +1) → refl}) t)))


-- Composing a singleton substitution and a lifted substitution.
-- sg u ∘ lift σ = cons id u ∘ lift σ = cons σ u

substVarSingletonComp : ∀ {u} (x : Fin (1+ n))
  → (sgSubst u ₛ•ₛ liftSubst σ) x ≡ (consSubst σ u) x
substVarSingletonComp x0 = refl
substVarSingletonComp {σ = σ} (x +1) = trans (subst-wk (σ x)) (subst-id (σ x))

-- The same again, as action on a term t.

substSingletonComp :
  (t : Term[ k ] (1+ n)) →
  t [ sgSubst u ₛ•ₛ (σ ⇑) ] ≡ t [ consSubst σ u ]
substSingletonComp = substVar-to-subst substVarSingletonComp

-- A single substitution after a lifted substitution.
-- ((lift σ) G)[t] = (cons σ t)(G)

singleSubstComp :
  ∀ u (σ : Subst m n) (t : Term[ k ] (1+ n)) →
  t [ σ ⇑ ] [ u ]₀ ≡ t [ consSubst σ u ]
singleSubstComp _ _ t =
  trans (substCompEq t) (substSingletonComp t)

-- A single substitution after a lifted substitution (with weakening).
-- ((lift (ρ ∘ σ)) G)[t]₀ = (cons (ρ ∘ σ) t)(G)

singleSubstWkComp :
  ∀ u (σ : Subst m n) (t : Term[ k ] (1+ n)) →
  wk (lift ρ) (t [ σ ⇑ ]) [ u ]₀ ≡ t [ consSubst (ρ •ₛ σ) u ]
singleSubstWkComp _ _ t =
  trans (cong _[ _ ] (trans (wk-subst t) (subst-lift-•ₛ t)))
    (trans (substCompEq t) (substSingletonComp t))

-- Pushing a substitution into a single substitution.

singleSubstLift :
  ∀ (t : Term[ k ] (1+ n)) u → t [ u ]₀ [ σ ] ≡ t [ σ ⇑ ] [ u [ σ ] ]₀
singleSubstLift t _ =
  trans (substCompEq t) $
  trans (substVar-to-subst (λ { x0 → refl; (_ +1) → refl}) t) $
  sym $
  trans (substCompEq t) $
  substSingletonComp t

-- More specific laws.

idWkLiftSubstLemma :
  (σ : Subst m n) (t : Term[ k ] (1+ n)) →
  wk (lift (step id)) (t [ σ ⇑ ]) [ var x0 ]₀ ≡ t [ σ ⇑ ]
idWkLiftSubstLemma _ t =
  trans (singleSubstWkComp _ _ t)
    (substVar-to-subst (λ { x0 → refl; (_ +1) → refl}) t)

substVarComp↑ : ∀ {t} (σ : Subst m n) x
  → (consSubst (wk1Subst idSubst) (t [ liftSubst σ ]) ₛ•ₛ liftSubst σ) x
  ≡ (liftSubst σ ₛ•ₛ consSubst (wk1Subst idSubst) t) x
substVarComp↑ σ x0 = refl
substVarComp↑ σ (x +1) = trans (subst-wk (σ x)) (sym (wk≡subst (step id) (σ x)))

singleSubstLift↑ :
  ∀ (σ : Subst m n) (t : Term[ k ] (1+ n)) u →
  t [ u ]↑ [ σ ⇑ ] ≡ t [ σ ⇑ ] [ u [ σ ⇑ ] ]↑
singleSubstLift↑ _ t _ =
  trans (substCompEq t) $
  sym $
  trans (substCompEq t) $
  substVar-to-subst (substVarComp↑ _) t

substConsComp :
  t [ consSubst (λ x → σ (x +1)) (u [ tail σ ]) ] ≡
  t [ consSubst (λ x → var (x +1)) (wk1 u) ] [ σ ]
substConsComp {t} {u} =
  trans
    (substVar-to-subst (λ { x0 → sym (subst-wk u); (_ +1) → refl }) t) $
  sym (substCompEq t)

wkSingleSubstId :
  (t : Term[ k ] (1+ n)) → (wk (lift (step id)) t) [ var x0 ]₀ ≡ t
wkSingleSubstId t =
  trans (subst-wk t) $
  trans (substVar-to-subst (λ { x0 → refl; (_ +1) → refl }) t) $
  subst-id _

wkSingleSubstWk1 :
  (t : Term[ k ] (1+ n)) →
  wk (lift (step (step id))) t [ var (x0 +1) ]₀ ≡ wk1 t
wkSingleSubstWk1 t =
  trans (subst-wk t) $
  trans (substVar-to-subst (λ { x0 → refl; (_ +1) → refl }) t) $
  sym (wk≡subst _ _)

cons-wk-subst :
  ∀ (ρ : Wk m n) (σ : Subst n ℓ) u (t : Term[ k ] (1+ ℓ)) →
  t [ sgSubst u ₛ• lift ρ ₛ•ₛ (σ ⇑) ] ≡ t [ consSubst (ρ •ₛ σ) u ]
cons-wk-subst _ σ _ =
  substVar-to-subst
    (λ { x0     → refl
       ; (x +1) → trans (subst-wk (σ x)) (sym (wk≡subst _ _))
       })

-- A specific equation on weakenings used for the reduction of natrec.

wk-β-natrec :
  (ρ : Wk m n) (t : Term[ k ] (1+ n)) →
  wk (liftn ρ 2) (t [ suc (var x1) ]↑²) ≡
  wk (lift ρ) t [ suc (var x1) ]↑²
wk-β-natrec _ = wk-β↑²

-- A specific equation on eakenings used for the reduction of prodrec.

wk-β-prodrec :
  (ρ : Wk m n) (t : Term[ k ] (1+ n)) →
  wk (liftn ρ 2) (t [ prod s p (var x1) (var x0) ]↑²) ≡
  wk (lift ρ) t [ prod s p (var x1) (var x0) ]↑²
wk-β-prodrec _ = wk-β↑²

wk-β-doubleSubst :
  (ρ : Wk m n) (t : Term[ k ] (2+ n)) (u v : Term n) →
  wk ρ (t [ u , v ]₁₀) ≡ wk (liftn ρ 2) t [ wk ρ u , wk ρ v ]₁₀
wk-β-doubleSubst ρ t u v =
  wk ρ (t [ σₜ u v ])                      ≡⟨ wk-subst t ⟩
  t [ ρ •ₛ σₜ u v ]                        ≡⟨ substVar-to-subst eq′ t ⟩
  t [ σₜ (wk ρ u) (wk ρ v) ₛ• liftn ρ 2 ]  ≡⟨ sym (subst-wk t) ⟩
  wk (liftn ρ 2) t [ wk ρ u , wk ρ v ]₁₀   ∎
  where
  σₜ : (u v : Term ℓ) → Subst ℓ (2+ ℓ)
  σₜ u v = consSubst (consSubst idSubst u) v

  eq′ :
    ∀ x →
    substVar (ρ •ₛ σₜ u v) x ≡
    substVar (σₜ (wk ρ u) (wk ρ v)) (wkVar (liftn ρ 2) x)
  eq′ x0      = refl
  eq′ (x0 +1) = refl
  eq′ (_ +2)  = refl

natrecSucCaseLemma : (x : Fin (1+ n))
  → (liftSubstn σ 2 ₛ•ₛ consSubst (wkSubst 2 idSubst) (suc (var x1))) x
  ≡ (consSubst (wkSubst 2 idSubst) (suc (var x1)) ₛ•ₛ liftSubst σ) x
natrecSucCaseLemma x0 = refl
natrecSucCaseLemma {σ = σ} (_+1 x) = begin
  wk1 (wk1 (σ x))
    ≡⟨ wk-comp (step id) (step id) (σ x) ⟩
  wk (step id • step id) (σ x)
    ≡⟨ wk≡subst (step id • step id) (σ x) ⟩
  σ x [ wkSubst 2 idSubst ]
    ≡⟨⟩
  σ x [ consSubst (wkSubst 2 idSubst) (suc (var x1)) ₛ• step id ]
    ≡˘⟨ subst-wk (σ x) ⟩
  wk1 (σ x) [ consSubst (wkSubst 2 idSubst) (suc (var x1)) ] ∎

natrecSucCase :
  (σ : Subst m n) (t : Term[ k ] (1+ n)) →
  t [ suc (var x1) ]↑² [ σ ⇑[ 2 ] ] ≡
  t [ σ ⇑ ] [ suc (var x1) ]↑²
natrecSucCase σ t = begin
  t [ suc (var x1) ]↑² [ σ ⇑[ 2 ] ]  ≡⟨ substCompEq t ⟩
  t [ (σ ⇑[ 2 ]) ₛ•ₛ σₛ ]            ≡⟨ substVar-to-subst natrecSucCaseLemma t ⟩
  t [ σₛ ₛ•ₛ (σ ⇑) ]                 ≡˘⟨ substCompEq t ⟩
  t [ σ ⇑ ] [ suc (var x1) ]↑²       ∎
  where
  σₛ : Subst (2+ ℓ) (1+ ℓ)
  σₛ = consSubst (wkSubst 2 idSubst) (suc (var x1))

natrecIrrelevantSubstLemma : ∀ p q r F z s m (σ : Subst ℓ n) (x : Fin (1+ n))
  → (sgSubst (natrec p q r
               (F [ liftSubst σ ])
               (z [ σ ])
               (s [ liftSubstn σ 2 ])
               m
             )
     ₛ•ₛ liftSubst (sgSubst m)
     ₛ•ₛ liftSubst (liftSubst σ)
     ₛ•  step id
     ₛ•ₛ consSubst (tail idSubst) (suc (var x0))) x
  ≡ (consSubst σ (suc m)) x
natrecIrrelevantSubstLemma p q r F z s m σ x0 =
  cong suc (trans (subst-wk m) (subst-id m))
natrecIrrelevantSubstLemma p q r F z s m σ (x +1) =
  trans (subst-wk (wk (step id) (σ x)))
           (trans (subst-wk (σ x))
                     (subst-id (σ x)))

natrecIrrelevantSubst : ∀ p q r F z s m (σ : Subst ℓ n)
  → F [ consSubst σ (suc m) ]
  ≡ wk1 (F [ suc (var x0) ]↑)
           [ liftSubstn σ 2 ]
           [ liftSubst (sgSubst m) ]
           [ natrec p q r (F [ liftSubst σ ]) (z [ σ ]) (s [ liftSubstn σ 2 ]) m ]₀
natrecIrrelevantSubst p q r F z s m σ =
  sym (trans (substCompEq (_[ liftSubstn σ 2 ]
        (wk (step id)
         (F [ consSubst (tail idSubst) (suc (var x0)) ]))))
         (trans (substCompEq (wk (step id)
        (F [ consSubst (tail idSubst) (suc (var x0)) ])))
        (trans
           (subst-wk (F [ consSubst (tail idSubst) (suc (var x0)) ]))
           (trans (substCompEq F)
                     (substVar-to-subst (natrecIrrelevantSubstLemma p q r F z s m σ) F)))))

natrecIrrelevantSubstLemma′ : ∀ (p q r : M) F z s n (x : Fin (1+ m))
  → (sgSubst (natrec p q r F z s n)
     ₛ•ₛ liftSubst (sgSubst n)
     ₛ•  step id
     ₛ•ₛ consSubst (tail idSubst) (suc (var x0))) x
  ≡ (consSubst var (suc n)) x
natrecIrrelevantSubstLemma′ p q r F z s n x0 =
  cong suc (trans (subst-wk n) (subst-id n))
natrecIrrelevantSubstLemma′ p q r F z s n (x +1) = refl

natrecIrrelevantSubst′ : ∀ p q r (F : Term (1+ m)) z s n
  → wk1 (F [ suc (var x0) ]↑) [ (liftSubst (sgSubst n)) ] [ natrec p q r F z s n ]₀
  ≡ F [ suc n ]₀
natrecIrrelevantSubst′ p q r F z s n =
  trans (substCompEq (wk (step id)
                         (F [ consSubst (tail idSubst) (suc (var x0)) ])))
        (trans (subst-wk (F [ consSubst (tail idSubst) (suc (var x0)) ]))
               (trans (substCompEq F)
                      (substVar-to-subst (natrecIrrelevantSubstLemma′ p q r F z s n) F)))

cons0wkLift1-id :
  (σ : Subst m n) (t : Term[ k ] (1+ n)) →
  wk (lift (step id)) (t [ σ ⇑ ]) [ var x0 ]₀ ≡ t [ σ ⇑ ]
cons0wkLift1-id σ t =
  trans (subst-wk (t [ _ ])) $
  trans (substVar-to-subst (λ { x0 → refl; (_ +1) → refl }) (t [ _ ])) $
  subst-id _

substConsId :
  (t : Term[ k ] (1+ n)) →
  t [ consSubst σ (u [ σ ]) ] ≡ t [ u ]₀ [ σ ]
substConsId t =
  sym $
  trans (substCompEq t) $
  substVar-to-subst (λ { x0 → refl; (_ +1) → refl }) t

substConsTailId :
  t [ consSubst (tail σ) (u [ σ ]) ] ≡
  t [ consSubst (tail idSubst) u ] [ σ ]
substConsTailId {t} =
  trans (substVar-to-subst (λ { x0 → refl; (_ +1) → refl }) t) $
  sym (substCompEq t)

substConcatSingleton′ :
  (t : Term[ k ] (1+ n)) →
  t [ σ ₛ•ₛ sgSubst u ] ≡ t [ consSubst σ (u [ σ ]) ]
substConcatSingleton′ t = substVar-to-subst (λ { x0 → refl ; (x +1) → refl}) t

step-consSubst :
  (t : Term[ k ] n) →
  wk (step ρ) t [ consSubst σ u ] ≡ wk ρ t [ σ ]
step-consSubst {ρ} {σ} {u} t = begin
  wk (step ρ) t [ consSubst σ u ] ≡⟨ subst-wk t ⟩
  t [ consSubst σ u ₛ• step ρ ]   ≡⟨ substVar-to-subst (λ _ → refl) t ⟩
  t [ σ ₛ• ρ ]                    ≡˘⟨ subst-wk t ⟩
  wk ρ t [ σ ]                    ∎


wk1-tail : (t : Term[ k ] n) → wk1 t [ σ ] ≡ t [ tail σ ]
wk1-tail {σ = σ} t = begin
  wk1 t [ σ ]          ≡⟨⟩
  wk (step id) t [ σ ] ≡⟨ subst-wk t ⟩
  t [ σ ₛ• step id ]   ≡⟨⟩
  t [ tail σ ]         ∎

wk1-tailId : (t : Term[ k ] n) → wk1 t ≡ t [ tail idSubst ]
wk1-tailId t = trans (sym (subst-id (wk1 t))) (subst-wk t)

wk2-tail : (t : Term[ k ] n) → wk2 t [ σ ] ≡ t [ tail[ 2 ] σ ]
wk2-tail {σ = σ} t = begin
  wk2 t [ σ ]          ≡⟨ wk1-tail (wk1 t) ⟩
  wk1 t [ tail σ ]     ≡⟨ wk1-tail t ⟩
  t [ tail (tail σ) ]  ∎

opaque

  -- The function tail[_] could (up to pointwise equality) have been
  -- defined using _ₛ•ₛ_, wkSubst and idSubst.

  tail[]≡ :
    ∀ k {σ : Subst m (k + n)} →
    ∀ x → tail[ k ] σ x ≡ (σ ₛ•ₛ wkSubst k idSubst) x
  tail[]≡ 0          _ = refl
  tail[]≡ (1+ k) {σ} x =
    tail[ k ] (tail σ) x                    ≡⟨ tail[]≡ k _ ⟩
    (tail σ ₛ•ₛ wkSubst k idSubst) x        ≡⟨⟩
    wkSubst k idSubst x [ tail σ ]          ≡˘⟨ wk1-tail (wkSubst k _ _) ⟩
    wk1 (wkSubst k idSubst x) [ σ ]         ≡⟨⟩
    (σ ₛ•ₛ wk1Subst (wkSubst k idSubst)) x  ≡⟨⟩
    (σ ₛ•ₛ wkSubst (1+ k) idSubst) x        ∎

step-sgSubst : ∀ (t : Term[ k ] n) u → wk (step ρ) t [ u ]₀ ≡ wk ρ t
step-sgSubst t _ = trans (step-consSubst t) (subst-id _)

wk1-sgSubst : ∀ (t : Term[ k ] n) u → wk1 t [ u ]₀ ≡ t
wk1-sgSubst _ _ = trans (step-sgSubst _ _) (wk-id _)

opaque

  -- Weakening twice and then substituting something for the two new
  -- variables amounts to the same thing as doing nothing.

  wk2-[,] : wk2 t [ u , v ]₁₀ ≡ t
  wk2-[,] {t} {u} {v} =
    wk2 t [ u , v ]₁₀  ≡⟨ wk2-tail t ⟩
    t [ idSubst ]      ≡⟨ subst-id _ ⟩
    t                  ∎

opaque

  -- A variant of wk2-[,] for wk₂.

  wk₂-[,] : wk₂ t [ u , v ]₁₀ ≡ t
  wk₂-[,] {t} {u} {v} =
    wk₂ t [ u , v ]₁₀  ≡⟨ subst-wk t ⟩
    t [ idSubst ]      ≡⟨ subst-id _ ⟩
    t                  ∎

-- Substituting variable one into t using _[_]↑² amounts to the same
-- thing as applying wk1 to t.

[1]↑² : t [ var x1 ]↑² ≡ wk1 t
[1]↑² {t = t} =
  t [ consSubst (λ x → var (x +2)) (var x1) ]  ≡⟨ (flip substVar-to-subst t λ where
                                                     x0     → refl
                                                     (_ +1) → refl) ⟩
  t [ (λ x → var (x +1)) ]                     ≡˘⟨ wk≡subst _ _ ⟩
  wk1 t                                        ∎

-- Substituting wk1 u into t using _[_]↑² amounts to the same thing as
-- substituting u into t using _[_]↑ and then weakening one step.

[wk1]↑² : (t : Term[ k ] (1 + n)) → t [ wk1 u ]↑² ≡ wk1 (t [ u ]↑)
[wk1]↑² {u = u} t =
  t [ consSubst (λ x → var (x +2)) (wk1 u) ]  ≡⟨ (flip substVar-to-subst t λ where
                                                      x0     → refl
                                                      (_ +1) → refl) ⟩
  t [ wk1 ∘→ consSubst (λ x → var (x +1)) u ] ≡˘⟨ wk-subst t ⟩
  wk1 (t [ consSubst (λ x → var (x +1)) u ])  ∎

subst-β-prodrec :
  (t : Term[ k ] (1+ n)) (σ : Subst m n) →
  t [ prod s p (var x1) (var x0) ]↑² [ σ ⇑[ 2 ] ] ≡
  t [ σ ⇑ ] [ prod s p (var x1) (var x0) ]↑²
subst-β-prodrec {n} t σ =
   t [ t₁′ ]↑² [ σ ⇑[ 2 ] ]                           ≡⟨ substCompEq t ⟩
   t [ (σ ⇑[ 2 ]) ₛ•ₛ replace₁ 2 t₁′ ]                ≡⟨ substVar-to-subst varEq t ⟩
   t [ consSubst (wkSubst 2 idSubst) t₂′ ₛ•ₛ (σ ⇑) ]  ≡˘⟨ substCompEq t ⟩
   t [ σ ⇑ ] [ t₂′ ]↑²                                ∎
   where
   t₁′ = prod! (var (x0 +1)) (var x0)
   t₂′ = prod! (var (x0 +1)) (var x0)
   varEq :
     (x : Fin (1+ n)) →
     (liftSubstn σ 2 ₛ•ₛ consSubst (wkSubst 2 idSubst) t₁′) x ≡
     (consSubst (wkSubst 2 idSubst) t₂′ ₛ•ₛ liftSubst σ) x
   varEq x0 = refl
   varEq (x +1) = begin
     wk1 (wk1 (σ x))
       ≡⟨ wk≡subst (step id) (wk1 (σ x)) ⟩
     wk1 (σ x) [ wk1Subst idSubst ]
       ≡⟨ subst-wk (σ x) ⟩
     σ x [ wk1Subst idSubst ₛ• step id ]
       ≡⟨ substVar-to-subst (λ x₁ → refl) (σ x) ⟩
     σ x [ (λ y → var (y +2)) ]
       ≡˘⟨ wk1-tail (σ x) ⟩
     wk1 (σ x) [ consSubst (λ y → var (y +2)) t₂′ ] ∎

substComp↑² :
  (t : Term (1+ n)) (u : Term (2 + n)) →
  t [ consSubst (tail[ 2 ] σ) (u [ σ ]) ] ≡ t [ u ]↑² [ σ ]
substComp↑² {σ} t u =
  t [ consSubst (tail[ 2 ] σ) (u [ σ ]) ]  ≡⟨ substVar-to-subst (λ { x0 → refl; (_ +1) → refl }) t ⟩
  t [ σ ₛ•ₛ replace₁ 2 u ]                 ≡˘⟨ substCompEq t ⟩
  t [ u ]↑² [ σ ]                          ∎

substCompProdrec :
  (t : Term[ k ] (1+ n)) (u v : Term m) (σ : Subst m n) →
  t [ σ ⇑ ] [ prod s p u v ]₀ ≡
  t [ prod s p (var x1) (var x0) ]↑² [ consSubst (consSubst σ u) v ]
substCompProdrec t u v σ =
   t [ σ ⇑ ] [ prod! u v ]₀                             ≡⟨ substCompEq t ⟩
   t [ sgSubst (prod! u v) ₛ•ₛ (σ ⇑) ]                  ≡⟨ flip substVar-to-subst t
                                                             (λ { x0 → refl; (x +1) → trans (wk1-tail (σ x)) (subst-id _) }) ⟩
   t [ consSubst (consSubst σ u) v ₛ•ₛ replace₁ 2 px ]  ≡˘⟨ substCompEq t ⟩
   t [ px ]↑² [ consSubst (consSubst σ u) v ]           ∎
   where
   px = prod! (var (x0 +1)) (var x0)

opaque

  -- A variant of the previous lemma.

  [1,0]↑²[,] :
    (t : Term[ k ] (1+ n)) →
    t [ prod s p (var x1) (var x0) ]↑² [ u , v ]₁₀ ≡
    t [ prod s p u v ]₀
  [1,0]↑²[,] {s} {p} {u} {v} t =
    t [ prod s p (var x1) (var x0) ]↑² [ u , v ]₁₀  ≡˘⟨ substCompProdrec t _ _ _ ⟩

    t [ liftSubst idSubst ] [ prod s p u v ]₀       ≡⟨ cong _[ _ ] $
                                                       trans (substVar-to-subst subst-lift-id t) $
                                                       subst-id t ⟩
    t [ prod s p u v ]₀                             ∎

opaque

  -- A generalisation of doubleSubstComp (given below).

  doubleSubstComp′ :
    (t : Term[ k ] (2+ n)) →
    t [ liftSubstn σ₁ 2 ] [ consSubst (consSubst σ₂ u) v ] ≡
    t [ consSubst (consSubst (σ₂ ₛ•ₛ σ₁) u) v ]
  doubleSubstComp′ {σ₁} {σ₂} {u} {v} t =
    t [ liftSubstn σ₁ 2 ] [ consSubst (consSubst σ₂ u) v ]  ≡⟨ substCompEq t ⟩
    t [ consSubst (consSubst σ₂ u) v ₛ•ₛ liftSubstn σ₁ 2 ]  ≡⟨ (flip substVar-to-subst t λ {
                                                                  x0          → refl;
                                                                  (x0 +1)     → refl;
                                                                  ((x +1) +1) →
      wk2 (σ₁ x) [ consSubst (consSubst σ₂ u) v ]                   ≡⟨ wk2-tail (σ₁ _) ⟩
      σ₁ x [ σ₂ ]                                                   ∎ }) ⟩

    t [ consSubst (consSubst (σ₂ ₛ•ₛ σ₁) u) v ]             ∎

doubleSubstComp :
  (t : Term[ k ] (2+ n)) (u v : Term m) (σ : Subst m n) →
  t [ σ ⇑[ 2 ] ] [ u , v ]₁₀ ≡ t [ consSubst (consSubst σ u) v ]
doubleSubstComp t u v σ =
  t [ σ ⇑[ 2 ] ] [ u , v ]₁₀                       ≡⟨ doubleSubstComp′ t ⟩
  t [ consSubst (consSubst (idSubst ₛ•ₛ σ) u) v ]  ≡⟨ flip substVar-to-subst t $ consSubst-cong refl $ consSubst-cong refl idSubst-ₛ•ₛˡ ⟩
  t [ consSubst (consSubst σ u) v ]                ∎

head-tail-subst :
  (t : Term[ k ] (1+ n)) → t [ σ ] ≡ t [ consSubst (tail σ) (head σ) ]
head-tail-subst t =
  substVar-to-subst (λ { x0 → refl ; (x +1) → refl}) t

opaque

  -- Applying a weakening followed by a closing substitution to a closed term
  -- is the same as doing nothing.

  wk-subst-closed : {ρ : Wk n 0} {σ : Subst 0 n}
                  → (t : Term[ k ] 0)
                  → wk ρ t [ σ ] ≡ t
  wk-subst-closed {0} {ρ = id} {σ} t = begin
    wk id t [ σ ] ≡⟨ cong (_[ σ ]) (wk-id t) ⟩
    t [ σ ]       ≡⟨ substVar-to-subst (λ ()) t ⟩
    t [ idSubst ] ≡⟨ subst-id t ⟩
    t             ∎
  wk-subst-closed {1+ n} {ρ = step ρ} {σ} t = begin
    wk (step ρ) t [ σ ]                           ≡⟨ head-tail-subst (wk (step ρ) t) ⟩
    wk (step ρ) t [ consSubst (tail σ) (head σ) ] ≡⟨ step-consSubst t ⟩
    wk ρ t [ tail σ ]                             ≡⟨ wk-subst-closed t ⟩
    t                                             ∎

opaque

  -- A special case of the property above

  wk₀-subst : (t : Term[ k ] 0) → wk wk₀ t [ σ ] ≡ t
  wk₀-subst t = wk-subst-closed t

opaque

  -- A variant of wk₀-subst.

  wk₀-closed : {t : Term[ k ] 0} → wk wk₀ t ≡ t
  wk₀-closed {t} =
    wk wk₀ t              ≡˘⟨ subst-id _ ⟩
    wk wk₀ t [ idSubst ]  ≡⟨ wk₀-subst _ ⟩
    t                     ∎

opaque

  -- The result of applying a substitution to wk wk₀ t is wk wk₀ t.

  wk-wk₀-[]≡ : wk wk₀ t [ σ ] ≡ wk wk₀ t
  wk-wk₀-[]≡ {t} {σ} =
    wk wk₀ t [ σ ]     ≡⟨ subst-wk t ⟩
    t [ σ ₛ• wk₀ ]     ≡⟨ substVar-to-subst (λ ()) t ⟩
    t [ toSubst wk₀ ]  ≡˘⟨ wk≡subst _ _ ⟩
    wk wk₀ t           ∎

opaque

  -- A version of the above property involving lifted weakenings and
  -- substitutions

  wk-subst-lift-closed : {ρ : Wk n 0} {σ : Subst 0 n}
                       → (t : Term[ k ] 1)
                       → wk (lift ρ) t [ liftSubst σ ] ≡ t
  wk-subst-lift-closed {ρ} {σ} t = begin
    wk (lift ρ) t [ liftSubst σ ]  ≡⟨ subst-wk t ⟩
    t [ liftSubst σ ₛ• lift ρ ]    ≡⟨ subst-lift-ₛ• t ⟩
    t [ liftSubst (σ ₛ• ρ) ]       ≡⟨ substVar-to-subst (substVar-lift (λ ())) t ⟩
    t [ liftSubst idSubst ]        ≡⟨ substVar-to-subst subst-lift-id t ⟩
    t [ idSubst ]                  ≡⟨ subst-id t ⟩
    t                              ∎

opaque

  lifts-step-sgSubst :
    (m : Nat) (t : Term (m + n)) →
    wk (liftn ρ m) t ≡ wk (liftn (step ρ) m) t [ sgSubst u ⇑[ m ] ]
  lifts-step-sgSubst {ρ} {u} m t =
    wk (liftn ρ m) t                              ≡⟨ wk≡subst (liftn ρ m) t ⟩
    t [ toSubst (liftn ρ m) ]                     ≡⟨ substVar-to-subst (lemma m) t ⟩
    t [ (sgSubst u ₛ• step ρ) ⇑[ m ] ]            ≡˘⟨ subst-lifts-ₛ• m t ⟩
    t [ (sgSubst u ⇑[ m ]) ₛ• liftn (step ρ) m ]  ≡˘⟨ subst-wk t ⟩
    wk (liftn (step ρ) m) t [ sgSubst u ⇑[ m ] ]  ∎
    where
    lemma :
      ∀ (m : Nat) x →
      toSubst (liftn ρ m) x ≡ ((sgSubst u ₛ• step ρ) ⇑[ m ]) x
    lemma 0      _      = refl
    lemma (1+ _) x0     = refl
    lemma (1+ m) (x +1) = cong wk1 (lemma m x)

opaque

  lifts-step-[,] :
    (m : Nat) (t : Term[ k ] (m + n)) →
    wk (liftn ρ m) t ≡
    wk (liftn (stepn ρ 2) m) t [ consSubst (sgSubst u) v ⇑[ m ] ]
  lifts-step-[,] {ρ} {u} {v} m t =
    wk (liftn ρ m) t                                               ≡⟨ wk≡subst (liftn ρ m) t ⟩
    t [ toSubst (liftn ρ m) ]                                      ≡⟨ substVar-to-subst (lemma m) t ⟩
    t [ (consSubst (sgSubst u) v ⇑[ m ]) ₛ• liftn (stepn ρ 2) m ]  ≡˘⟨ subst-wk t ⟩
    wk (liftn (stepn ρ 2) m) t [ consSubst (sgSubst u) v ⇑[ m ] ]  ∎
    where
    lemma :
      ∀ (m : Nat) x →
      toSubst (liftn ρ m) x ≡
      ((consSubst (sgSubst u) v ⇑[ m ]) ₛ• liftn (stepn ρ 2) m) x
    lemma 0      _      = refl
    lemma (1+ m) x0     = refl
    lemma (1+ m) (x +1) = cong wk1 (lemma m x)

opaque

  -- The application of a substitution to a closed term amounts to the
  -- same thing as weakening the term.

  []≡wk-wk₀ : {σ : Subst n 0} (t : Term[ k ] 0) → t [ σ ] ≡ wk wk₀ t
  []≡wk-wk₀ {σ} t =
    t [ σ ]            ≡⟨ substVar-to-subst (λ ()) t ⟩
    t [ toSubst wk₀ ]  ≡˘⟨ wk≡subst _ _ ⟩
    wk wk₀ t           ∎

opaque

  -- A variant of []≡wk-wk₀.

  []-closed : {t : Term[ k ] 0} → t [ σ ] ≡ t
  []-closed {σ} {t} =
    t [ σ ]   ≡⟨ []≡wk-wk₀ t ⟩
    wk wk₀ t  ≡⟨ wk₀-closed ⟩
    t         ∎

opaque

  -- One can express _[_,_]₁₀ using _[_]₀ and wk1.

  [,]≡[wk1]₀[]₀ :
    (t : Term[ k ] (2+ n)) → t [ u , v ]₁₀ PE.≡ t [ wk1 v ]₀ [ u ]₀
  [,]≡[wk1]₀[]₀ {u} {v} t =
    t [ u , v ]₁₀             ≡˘⟨ PE.cong (t [ _ ,_]₁₀) $ wk1-sgSubst _ _ ⟩
    t [ u , wk1 v [ u ]₀ ]₁₀  ≡⟨ substConsId t ⟩
    t [ wk1 v ]₀ [ u ]₀       ∎

opaque

  -- One can fuse an application of _[_,_] and an application of _[_]
  -- into an application of _[_].

  [,]-[]-fusion :
    (t : Term[ k ] (2+ n)) →
    t [ u , v ]₁₀ [ σ ] ≡
    t [ consSubst (consSubst σ (u [ σ ])) (v [ σ ]) ]
  [,]-[]-fusion {u} {v} {σ} t =
    t [ u , v ]₁₀ [ σ ]                                ≡⟨ substCompEq t ⟩
    t [ σ ₛ•ₛ consSubst (sgSubst u) v ]                ≡⟨ (flip substVar-to-subst t λ where
                                                             x0      → refl
                                                             (x0 +1) → refl
                                                             (_ +2)  → refl) ⟩
    t [ consSubst (consSubst σ (u [ σ ])) (v [ σ ]) ]  ∎

opaque

  -- The function _[_,_]₁₀ kind of commutes with _[_].

  [,]-[]-commute :
    (t : Term[ k ] (2+ n)) →
    t [ u , v ]₁₀ [ σ ] ≡
    t [ liftSubstn σ 2 ] [ u [ σ ] , v [ σ ] ]₁₀
  [,]-[]-commute {u} {v} {σ} t =
    t [ u , v ]₁₀ [ σ ]                                ≡⟨ [,]-[]-fusion t ⟩
    t [ consSubst (consSubst σ (u [ σ ])) (v [ σ ]) ]  ≡˘⟨ doubleSubstComp t _ _ _ ⟩
    t [ liftSubstn σ 2 ] [ u [ σ ] , v [ σ ] ]₁₀       ∎

opaque

  -- A lemma related to Unit.

  ≡Unit-wk1[]₀ :
    Unit s ≡ Unit s [ t ]₀
  ≡Unit-wk1[]₀ {s} {t} = refl

opaque

  -- A lemma related to Id.

  ≡Id-wk1-wk1-0[]₀ :
    Id A t u ≡ Id (wk1 A) (wk1 t) (var x0) [ u ]₀
  ≡Id-wk1-wk1-0[]₀ {A} {t} {u} =
    Id A t u                            ≡˘⟨ cong₂ (λ A t → Id A t _) (wk1-sgSubst _ _) (wk1-sgSubst _ _) ⟩
    Id (wk1 A [ u ]₀) (wk1 t [ u ]₀) u  ≡⟨⟩
    Id (wk1 A) (wk1 t) (var x0) [ u ]₀  ∎

opaque

  -- A variant of the previous lemma.

  ≡Id-wk2-wk2-1[,] :
    Id A t u ≡ Id (wk2 A) (wk2 t) (var x1) [ u , v ]₁₀
  ≡Id-wk2-wk2-1[,] {A} {t} {u} {v} =
    Id A t u                                      ≡˘⟨ cong₂ (λ A t → Id A t _) wk2-[,] wk2-[,] ⟩
    Id (wk2 A [ u , v ]₁₀) (wk2 t [ u , v ]₁₀) u  ≡⟨⟩
    Id (wk2 A) (wk2 t) (var x1) [ u , v ]₁₀       ∎

opaque

  -- Another lemma related to Id.

  Id-wk1-wk1-0[⇑]≡ :
    ∀ A t →
    Id (wk1 A) (wk1 t) (var x0) [ liftSubst σ ] ≡
    Id (wk1 (A [ σ ])) (wk1 (t [ σ ])) (var x0)
  Id-wk1-wk1-0[⇑]≡ {σ} A t =
    Id (wk1 A) (wk1 t) (var x0) [ liftSubst σ ]                  ≡⟨⟩
    Id (wk1 A [ liftSubst σ ]) (wk1 t [ liftSubst σ ]) (var x0)  ≡⟨ cong₂ (λ A t → Id A t _) (wk1-liftSubst A) (wk1-liftSubst t) ⟩
    Id (wk1 (A [ σ ])) (wk1 (t [ σ ])) (var x0)                  ∎

opaque

  -- A _[t]₀ after _[u]↑ has the same effect as _[u[t]₀]₀.

  []↑-[]₀ :
    (t : Term[ k ] (1+ n)) →
    t [ u ]↑ [ v ]₀ ≡ t [ u [ v ]₀ ]₀
  []↑-[]₀ {u} {v} t =
    t [ u ]↑ [ v ]₀                   ≡⟨ substCompEq t ⟩
    t [ sgSubst v ₛ•ₛ replace₁ 1 u ]  ≡⟨ substVar-to-subst lemma t ⟩
    t [ u [ v ]₀ ]₀                   ∎
    where
    lemma : ∀ x → (sgSubst v ₛ•ₛ replace₁ 1 u) x ≡ sgSubst (u [ v ]₀) x
    lemma x0     = refl
    lemma (_ +1) = refl

opaque

  -- A lemma related to natrec

  lift-step-natrec : ∀ A z s n
                   → natrec p q r
                            (wk (lift ρ) A [ liftSubst σ ])
                            (wk ρ z [ σ ])
                            (wk (liftn ρ 2) s [ liftSubstn σ 2 ])
                            n
                   ≡ natrec p q r
                            (wk (liftn ρ 2) (wk (lift (step id)) A) [ liftSubst (consSubst σ u) ])
                            (wk (lift ρ) (wk1 z) [ consSubst σ u ])
                            (wk (liftn ρ 3) (wk (liftn (step id) 2) s) [ liftSubstn (consSubst σ u) 2 ])
                            n
  lift-step-natrec {ρ} {σ} {u} A z s n =
    case begin
           wk (lift ρ) A [ liftSubst σ ]
             ≡⟨ subst-wk A ⟩
           A [ liftSubst σ ₛ• lift ρ ]
             ≡⟨ substVar-to-subst (λ { x0 → refl ; (_+1 x) → refl}) A ⟩
           A [ liftSubst (consSubst σ u) ₛ• lift (step ρ) ]
             ≡˘⟨ cong (λ x → A [ liftSubst (consSubst σ u) ₛ• lift (step x) ]) (•-idʳ ρ) ⟩
           A [ liftSubst (consSubst σ u) ₛ• lift (step (ρ • id)) ]
             ≡˘⟨ subst-wk A ⟩
           wk (lift (step (ρ • id))) A [ liftSubst (consSubst σ u) ]
             ≡˘⟨ cong (_[ liftSubst (consSubst σ u) ]) (wk-comp (liftn ρ 2) (lift (step id)) A) ⟩
           wk (liftn ρ 2) (wk (lift (step id)) A) [ liftSubst (consSubst σ u) ] ∎ of λ
      A≡A′ →
    case begin
           wk ρ z [ σ ]                          ≡˘⟨ step-consSubst z ⟩
           wk (step ρ) z [ consSubst σ u ]       ≡˘⟨ cong (_[ consSubst σ u ]) (lift-wk1 ρ z) ⟩
           wk (lift ρ) (wk1 z) [ consSubst σ u ] ∎ of λ
      z≡z′ →
    case begin
           wk (liftn ρ 2) s [ liftSubstn σ 2 ]
             ≡⟨ subst-wk s ⟩
           s [ liftSubstn σ 2 ₛ• liftn ρ 2 ]
             ≡⟨ substVar-to-subst (λ { x0 → refl ; (x0 +1) → refl ; (x +2) → refl}) s ⟩
           s [ liftSubstn (consSubst σ u) 2 ₛ• liftn (step ρ) 2 ]
             ≡˘⟨ subst-wk s ⟩
           wk (liftn (step ρ) 2) s [ liftSubstn (consSubst σ u) 2 ]
             ≡˘⟨ cong (λ x → wk (liftn (step x) 2) s [ liftSubstn (consSubst σ u) 2 ]) (•-idʳ ρ) ⟩
           wk (liftn (step (ρ • id)) 2) s [ liftSubstn (consSubst σ u) 2 ]
             ≡˘⟨ cong (_[ liftSubstn (consSubst σ u) 2 ]) (wk-comp (liftn ρ 3) (liftn (step id) 2) s) ⟩
           wk (liftn ρ 3) (wk (liftn (step id) 2) s) [ liftSubstn (consSubst σ u) 2 ] ∎ of λ
      s≡s′ →
    cong₃ (λ A z s → natrec _ _ _ A z s n)
      A≡A′ z≡z′ s≡s′

opaque

  -- A lemma related to natrec, similar to the one above

  lift-step-natrec′ : ∀ A z s t
                    → let σ′ = consSubst (consSubst σ u) v in
                      natrec p q r
                             (wk (lift ρ) A [ liftSubst σ ])
                             (wk ρ z [ σ ])
                             (wk (liftn ρ 2) s [ liftSubstn σ 2 ])
                             (t [ σ ])
                    ≡ natrec p q r
                             (wk (lift (step (step id))) (wk (lift ρ) A) [ liftSubst σ′ ])
                             (wk (step (step id)) (wk ρ z) [ σ′ ])
                             (wk (liftn (step (step id)) 2) (wk (liftn ρ 2) s) [ liftSubstn σ′ 2 ])
                             (wk (step (step id)) t [ σ′ ] )
  lift-step-natrec′ {(m)} {(n)} {σ} {u} {v} {ρ} A z s t =
    case begin
           wk (lift ρ) A [ liftSubst σ ]                               ≡⟨ subst-wk A ⟩
           A [ liftSubst σ ₛ• lift ρ ]                                 ≡⟨ substVar-to-subst (λ { x0 → refl ; (x +1) → refl}) A ⟩
           A [ liftSubst σ₊ ₛ• lift (step (step ρ)) ]                  ≡˘⟨ subst-wk A ⟩
           wk (lift (step (step ρ))) A [ liftSubst σ₊ ]                ≡˘⟨ cong (_[ liftSubst σ₊ ]) (wk-comp _ _ A) ⟩
           wk (lift (step (step id))) (wk (lift ρ) A) [ liftSubst σ₊ ] ∎ of λ
      A≡A′ →
    case begin
           wk ρ z [ σ ]                        ≡⟨ subst-wk z ⟩
           z [ σ ₛ• ρ ]                        ≡⟨ substVar-to-subst (λ _ → refl) z ⟩
           z [ σ₊ ₛ• step (step ρ) ]           ≡˘⟨ subst-wk z ⟩
           wk (step (step ρ)) z [ σ₊ ]         ≡˘⟨ cong (_[ σ₊ ]) (wk-comp _ _ z) ⟩
           wk (step (step id)) (wk ρ z) [ σ₊ ] ∎ of λ
      z≡z′ →
    case begin
           wk (liftn ρ 2) s [ liftSubstn σ 2 ]                                  ≡⟨ subst-wk s ⟩
           s [ liftSubstn σ 2 ₛ• liftn ρ 2 ]                                    ≡⟨ substVar-to-subst (λ { x0 → refl ; (x0 +1) → refl ; (x +2) → refl }) s ⟩
           s [ liftSubstn σ₊ 2 ₛ• liftn (step (step ρ)) 2 ]                     ≡˘⟨ subst-wk s ⟩
           wk (liftn (step (step ρ)) 2) s [ liftSubstn σ₊ 2 ]                   ≡˘⟨ cong (_[ liftSubstn σ₊ 2 ]) (wk-comp _ _ s) ⟩
           wk (liftn (step (step id)) 2) (wk (liftn ρ 2) s) [ liftSubstn σ₊ 2 ] ∎ of λ
      s≡s′ →
    cong₄ (natrec _ _ _) A≡A′ z≡z′ s≡s′
      (sym (trans (step-consSubst t) (wk1-tail t)))
    where
    σ₊ : Subst m (2+ n)
    σ₊ = consSubst (consSubst σ u) v

------------------------------------------------------------------------
-- Some lemmas related to wk[_], wk[_]′ and wkSubst

opaque

  -- The functions wk[_] and wk[_]′ are interchangeable.

  wk[]≡wk[]′ : wk[ n ] t ≡ wk[ n ]′ t
  wk[]≡wk[]′ {n = 0} {t} =
    t        ≡˘⟨ wk-id _ ⟩
    wk id t  ∎
  wk[]≡wk[]′ {n = 1+ n} {t} =
    wk1 (wk[ n ] t)   ≡⟨ cong wk1 wk[]≡wk[]′ ⟩
    wk1 (wk[ n ]′ t)  ≡⟨ wk-comp _ _ _ ⟩
    wk[ 1+ n ]′ t     ∎

opaque

  -- Applications of wk[_] can be expressed using a substitution.

  wk[]≡[] : ∀ n → wk[ n ] t ≡ t [ wkSubst n idSubst ]
  wk[]≡[] {t} 0 =
    t              ≡˘⟨ subst-id _ ⟩
    t [ idSubst ]  ∎
  wk[]≡[] {t} (1+ n) =
    wk1 (wk[ n ] t)                               ≡⟨ cong wk1 $ wk[]≡[] n ⟩
    wk1 (t [ wkSubst n idSubst ])                 ≡⟨ wk≡subst _ _ ⟩
    t [ wkSubst n idSubst ] [ wk1Subst idSubst ]  ≡⟨ substCompEq t ⟩
    t [ wk1Subst idSubst ₛ•ₛ wkSubst n idSubst ]  ≡⟨ substVar-to-subst lemma t ⟩
    t [ wkSubst (1+ n) idSubst ]                  ∎
    where
    lemma :
      (x : Fin m) →
      (wk1Subst idSubst ₛ•ₛ wkSubst n idSubst) x ≡
      wkSubst (1+ n) idSubst x
    lemma x =
      (wk1Subst idSubst ₛ•ₛ wkSubst n idSubst) x  ≡⟨⟩
      wkSubst n idSubst x [ wk1Subst idSubst ]    ≡⟨ wk1Subst-wk1 (wkSubst n _ _) ⟩
      wk1 (wkSubst n idSubst x [ idSubst ])       ≡⟨ cong wk1 $ subst-id _ ⟩
      wk1 (wkSubst n idSubst x)                   ≡⟨⟩
      wkSubst (1+ n) idSubst x                    ∎

opaque

  -- A lemma relating wk[_] and wkSubst.

  wk[]≡wkSubst : ∀ n x → wk[ n ] (σ x) ≡ wkSubst n σ x
  wk[]≡wkSubst 0      _ = refl
  wk[]≡wkSubst (1+ n) _ = cong wk1 (wk[]≡wkSubst n _)

opaque

  -- A composition lemma for wkSubst.

  wkSubst-idSubst-ₛ•ₛ :
    ∀ n x → (wkSubst n idSubst ₛ•ₛ σ) x ≡ wkSubst n σ x
  wkSubst-idSubst-ₛ•ₛ {σ} n x =
    σ x [ wkSubst n idSubst ]  ≡˘⟨ wk[]≡[] n ⟩
    wk[ n ] (σ x)              ≡⟨ wk[]≡wkSubst n _ ⟩
    wkSubst n σ x              ∎

opaque

  -- A composition lemma for wkSubst.

  wkSubst-comp :
    ∀ m x →
    subst Term (+-assoc m n o) (wkSubst (m + n) σ x) ≡
    wkSubst m (wkSubst n σ) x
  wkSubst-comp             0      _ = refl
  wkSubst-comp {n} {o} {σ} (1+ m) x =
    subst Term (cong 1+ (+-assoc m n o)) (wk1 (wkSubst (m + n) σ x))  ≡⟨ lemma {eq = +-assoc m _ _} ⟩
    wk1 (subst Term (+-assoc m n o) (wkSubst (m + n) σ x))            ≡⟨ cong wk1 $ wkSubst-comp m _ ⟩
    wk1 (wkSubst m (wkSubst n σ) x)                                   ∎
    where
    lemma :
      subst Term (cong 1+ eq) (wk1 t) ≡
      wk1 (subst Term eq t)
    lemma {eq = refl} = refl

opaque

  -- A composition lemma for wk[_].

  wk[]-comp :
    ∀ m →
    subst Term[ k ] (+-assoc m n o) (wk[ m + n ] t) ≡
    wk[ m ] (wk[ n ] t)
  wk[]-comp {k} {n} {o} {t} m =
    subst Term[ k ] (+-assoc m n o) (wk[ m + n ] t)                  ≡⟨ cong (subst _ _) $ wk[]≡[] (m + _) ⟩
    subst Term[ k ] (+-assoc m n o) (t [ wkSubst (m + n) idSubst ])  ≡⟨ lemma t ⟩
    t [ subst Term (+-assoc m n o) ∘→ wkSubst (m + n) idSubst ]      ≡⟨ flip substVar-to-subst t $ wkSubst-comp m ⟩
    t [ wkSubst m (wkSubst n idSubst) ]                              ≡˘⟨ flip substVar-to-subst t $ wkSubst-idSubst-ₛ•ₛ m ⟩
    t [ wkSubst m idSubst ₛ•ₛ wkSubst n idSubst ]                    ≡˘⟨ substCompEq t ⟩
    t [ wkSubst n idSubst ] [ wkSubst m idSubst ]                    ≡˘⟨ wk[]≡[] m ⟩
    wk[ m ] (t [ wkSubst n idSubst ])                                ≡˘⟨ cong wk[ m ] $ wk[]≡[] n ⟩
    wk[ m ] (wk[ n ] t)                                              ∎
    where
    lemma :
      ∀ t → subst Term[ k ] eq (t [ σ ]) ≡ t [ subst Term eq ∘→ σ ]
    lemma {eq = refl} _ = refl

opaque

  -- A composition lemma for wk[_]′.

  wk[]′-comp :
    ∀ m →
    subst Term[ k ] (+-assoc m n o) (wk[ m + n ]′ t) ≡
    wk[ m ]′ (wk[ n ]′ t)
  wk[]′-comp {k} {n} {o} {t} m =
    subst Term[ k ] (+-assoc m n o) (wk[ m + n ]′ t)  ≡˘⟨ cong (subst Term[ _ ] (+-assoc m _ _)) wk[]≡wk[]′ ⟩
    subst Term[ k ] (+-assoc m n o) (wk[ m + n ] t)   ≡⟨ wk[]-comp m ⟩
    wk[ m ] (wk[ n ] t)                               ≡⟨ trans wk[]≡wk[]′ $
                                                         cong wk[ _ ]′ wk[]≡wk[]′ ⟩
    wk[ m ]′ (wk[ n ]′ t)                             ∎

opaque

  -- A composition lemma for wk[_] and wk[_]′.

  wk[]-wk[]′-comp :
    ∀ m →
    subst Term[ k ] (+-assoc m n o) (wk[ m + n ]′ t) ≡
    wk[ m ] (wk[ n ]′ t)
  wk[]-wk[]′-comp {k} {n} {o} {t} m =
    subst Term[ k ] (+-assoc m n o) (wk[ m + n ]′ t)  ≡⟨ wk[]′-comp _ ⟩
    wk[ m ]′ (wk[ n ]′ t)                             ≡˘⟨ wk[]≡wk[]′ ⟩
    wk[ m ] (wk[ n ]′ t)                              ∎

opaque

  -- A lemma relating wk[_], _[_] and _⇑[_].

  wk[]-⇑[] : ∀ n → wk[ n ] t [ σ ⇑[ n ] ] ≡ wk[ n ] (t [ σ ])
  wk[]-⇑[]         0      = refl
  wk[]-⇑[] {t} {σ} (1+ n) =
    wk1 (wk[ n ] t) [ σ ⇑[ n ] ⇑ ]  ≡⟨ wk1-liftSubst (wk[ n ] _) ⟩
    wk1 (wk[ n ] t [ σ ⇑[ n ] ])    ≡⟨ cong wk1 $ wk[]-⇑[] n ⟩
    wk1 (wk[ n ] (t [ σ ]))         ∎

opaque

  -- A lemma relating wk[_]′, _[_] and _⇑[_].

  wk[]′-[⇑] :
    (t : Term[ k ] m) → wk[ n ]′ t [ σ ⇑[ n ] ] ≡ wk[ n ]′ (t [ σ ])
  wk[]′-[⇑] {n} {σ} t =
    wk[ n ]′ t [ σ ⇑[ n ] ]  ≡˘⟨ cong _[ _ ] $ wk[]≡wk[]′ {t = t} ⟩
    wk[ n ] t [ σ ⇑[ n ] ]   ≡⟨ wk[]-⇑[] n ⟩
    wk[ n ] (t [ σ ])        ≡⟨ wk[]≡wk[]′ ⟩
    wk[ n ]′ (t [ σ ])       ∎

opaque

  -- Applying _[ u ]↑ to a term that has been weakened at least one
  -- step amounts to the same thing as doing nothing.

  wk[]′-[]↑ : wk[ 1+ n ]′ t [ u ]↑ ≡ wk[ 1+ n ]′ t
  wk[]′-[]↑ {n} {t} {u} =
    wk[ 1+ n ]′ t [ u ]↑                                     ≡⟨⟩
    wk[ 1+ n ]′ t [ consSubst (wk1Subst idSubst) u ]         ≡⟨ subst-wk t ⟩
    t [ consSubst (wk1Subst idSubst) u ₛ• stepn id (1+ n) ]  ≡⟨⟩
    t [ toSubst (stepn id (1+ n)) ]                          ≡˘⟨ wk≡subst _ _ ⟩
    wk[ 1+ n ]′ t                                            ∎

opaque

  -- A variant of wk1-sgSubst.

  wk[1+]′-[]₀≡ : wk[ 1+ n ]′ t [ u ]₀ ≡ wk[ n ]′ t
  wk[1+]′-[]₀≡ {n} {t} {u} =
    wk[ 1+ n ]′ t [ u ]₀  ≡˘⟨ cong _[ _ ]₀ $ wk[]≡wk[]′ {n = 1+ n} ⟩
    wk[ 1+ n ] t [ u ]₀   ≡⟨ wk1-sgSubst _ _ ⟩
    wk[ n ] t             ≡⟨ wk[]≡wk[]′ ⟩
    wk[ n ]′ t            ∎

opaque

  -- A variant of wk1-sgSubst.

  wk[+1]′-[₀⇑]≡ :
    {t : Term[ k ] m} →
    subst Term[ k ] (+-assoc n _ _) (wk[ n + 1 ]′ t)
      [ sgSubst u ⇑[ n ] ] ≡
    wk[ n ]′ t
  wk[+1]′-[₀⇑]≡ {k} {n} {u} {t} =
    subst Term[ k ] (+-assoc n _ _) (wk[ n + 1 ]′ t) [ sgSubst u ⇑[ n ] ]  ≡⟨ cong _[ _ ] $ wk[]′-comp {t = t} _ ⟩
    wk[ n ]′ (wk1 t) [ sgSubst u ⇑[ n ] ]                                  ≡⟨ wk[]′-[⇑] (wk1 t) ⟩
    wk[ n ]′ (wk1 t [ u ]₀)                                                ≡⟨ cong wk[ _ ]′ $ wk1-sgSubst _ _ ⟩
    wk[ n ]′ t                                                             ∎

opaque

  -- A variant of wk₂-[,].

  wk[2+]′-[,]≡ : wk[ 2+ n ]′ t [ u , v ]₁₀ ≡ wk[ n ]′ t
  wk[2+]′-[,]≡ {n} {t} {u} {v} =
    wk[ 2+ n ]′ t [ u , v ]₁₀  ≡˘⟨ cong _[ _ , _ ]₁₀ $ wk[]≡wk[]′ {n = 2+ n} ⟩
    wk[ 2+ n ] t [ u , v ]₁₀   ≡⟨ wk2-[,] ⟩
    wk[ n ] t                  ≡⟨ wk[]≡wk[]′ ⟩
    wk[ n ]′ t                 ∎

opaque

  -- A variant of wk₂-[,].

  wk[2+]′[,⇑]≡ :
    {t : Term[ k ] m} →
    subst Term[ k ] (+-assoc n _ _) (wk[ n + 2 ]′ t)
      [ consSubst (sgSubst u) v ⇑[ n ] ] ≡
    wk[ n ]′ t
  wk[2+]′[,⇑]≡ {k} {n} {u} {v} {t} =
    subst Term[ k ] (+-assoc n _ _) (wk[ n + 2 ]′ t)
      [ consSubst (sgSubst u) v ⇑[ n ] ]                      ≡⟨ cong _[ _ ] $ wk[]′-comp n ⟩
    wk[ n ]′ (wk[ 2 ]′ t) [ consSubst (sgSubst u) v ⇑[ n ] ]  ≡⟨ wk[]′-[⇑] (wk[ _ ]′ t) ⟩
    wk[ n ]′ (wk[ 2 ]′ t [ u , v ]₁₀)                         ≡⟨ cong wk[ _ ]′ wk₂-[,] ⟩
    wk[ n ]′ t                                                ∎

opaque

  -- A variant of wk2-tail using wk₂

  wk₂-tail : (t : Term[ k ] n) → wk₂ t [ σ ] ≡ t [ tail[ 2 ] σ ]
  wk₂-tail {σ} t = begin
    wk₂ t [ σ ]        ≡˘⟨ cong _[ σ ] $ wk[]≡wk[]′ {t = t} ⟩
    wk2 t [ σ ]        ≡⟨ wk2-tail t ⟩
    t [ tail[ 2 ] σ ]  ∎

opaque

  -- One can combine wk (lift (step id)) and wk[ 1+ k ]′.

  wk-lift-step-id-wk[1+]′≡ :
    wk (lift (step id)) (wk[ 1+ n ]′ t) ≡ wk[ 2+ n ]′ t
  wk-lift-step-id-wk[1+]′≡ {n} {t} =
    wk (lift (step id)) (wk[ 1+ n ]′ t)     ≡˘⟨ cong (wk _) $ wk-comp _ _ _ ⟩
    wk (lift (step id)) (wk1 (wk[ n ]′ t))  ≡˘⟨ wk1-wk≡lift-wk1 _ _ ⟩
    wk[ 2 ] (wk[ n ]′ t)                    ≡⟨ trans (wk[]≡wk[]′ {n = 2}) $
                                               wk-comp _ _ _ ⟩
    wk[ 2+ n ]′ t                           ∎

opaque

  -- The function wk[ n ]′ commutes, in a certain sense, with
  -- weakening.

  wk⇑[]-wk[]≡ :
    ∀ n → wk (liftn ρ n) (wk[ n ]′ t) PE.≡ wk[ n ]′ (wk ρ t)
  wk⇑[]-wk[]≡ {ρ} {t} n =
    wk (liftn ρ n) (wk[ n ]′ t)    ≡⟨ wk-comp _ _ _ ⟩
    wk (liftn ρ n • stepn id n) t  ≡˘⟨ cong (flip wk _) (liftn-stepn-comp n) ⟩
    wk (stepn ρ n) t               ≡˘⟨ cong (flip wk _) (stepn-id-• n) ⟩
    wk (stepn id n • ρ) t          ≡˘⟨ wk-comp _ _ _ ⟩
    wk[ n ]′ (wk ρ t)              ∎

------------------------------------------------------------------------
-- Some lemmas related to _[_][_]↑

opaque

  -- An application of _[_][_]↑ followed by an application of _[_] can
  -- be expressed using a single application of _[_] in a certain way.

  [][]↑-[] :
    ∀ m {u} {σ : Subst n₁ (m + n₂)} (t : Term[ k ] (1+ n₂)) →
    t [ m ][ u ]↑ [ σ ] ≡ t [ consSubst (tail[ m ] σ) (u [ σ ]) ]
  [][]↑-[] m {u} {σ} t =
    t [ m ][ u ]↑ [ σ ]                      ≡⟨ substCompEq t ⟩

    t [ σ ₛ•ₛ replace₁ m u ]                 ≡˘⟨ (flip substVar-to-subst t λ where
                                                    x0     → refl
                                                    (_ +1) → tail[]≡ m _) ⟩
    t [ consSubst (tail[ m ] σ) (u [ σ ]) ]  ∎

private

  -- An example of how [][]↑-[] can be used. See also [][]↑-[₀⇑]
  -- below.

  _ : (t : Term[ k ] (1+ n)) → t [ u ]↑ [ v ]₀ ≡ t [ u [ v ]₀ ]₀
  _ = [][]↑-[] 1

private

  -- An example of how [][]↑-[] can be used.

  _ :
    (t : Term[ k ] (2+ n)) →
    t [ u ]↑ [ v , w ]₁₀ ≡ t [ v , u [ v , w ]₁₀ ]₁₀
  _ = [][]↑-[] 1

private

  -- An example of how [][]↑-[] can be used.

  _ :
    (t : Term[ k ] (1+ n)) →
    t [ 2 ][ u ]↑ [ v , w ]₁₀ ≡ t [ u [ v , w ]₁₀ ]₀
  _ = [][]↑-[] 2

opaque

  -- One can express _[_][_]↑ using some other operations.

  [][]↑≡′ :
    (t : Term[ k ] (1+ m)) →
    t [ n ][ u ]↑ ≡ t [ consSubst (tail[ n ] idSubst) u ]
  [][]↑≡′ {n} {u} t =
    t [ n ][ u ]↑                                        ≡˘⟨ subst-id _ ⟩
    t [ n ][ u ]↑ [ idSubst ]                            ≡⟨ [][]↑-[] _ t ⟩
    t [ consSubst (tail[ n ] idSubst) (u [ idSubst ]) ]  ≡⟨ substVar-to-subst (consSubst-cong (subst-id _) (λ _ → refl)) t ⟩
    t [ consSubst (tail[ n ] idSubst) u ]                ∎

opaque

  -- One can express _[_][_]↑ using some other operations.

  [][]↑≡ :
    (t : Term[ k ] (1+ m)) →
    t [ n ][ u ]↑ ≡ wk (lift (stepn id n)) t [ u ]₀
  [][]↑≡ {n} {u} t =
      t [ replace₁ n u ]                    ≡⟨ (flip substVar-to-subst t λ where
                                                  x0     → refl
                                                  (x +1) →
                                                    trans (sym $ wk[]≡wkSubst n _) $
                                                    wk[]≡wk[]′ {t = var x}) ⟩
      t [ sgSubst u ₛ• lift (stepn id n) ]  ≡˘⟨ subst-wk t ⟩
      wk (lift (stepn id n)) t [ u ]₀       ∎

opaque

  -- The function _[_][_]↑ commutes (in a certain sense) with _[_].

  [][]↑-commutes :
    (t : Term[ k ] (1+ m)) →
    t [ n ][ u ]↑ [ σ ⇑[ n ] ] ≡
    t [ σ ⇑ ] [ n ][ u [ σ ⇑[ n ] ] ]↑
  [][]↑-commutes {m} {n} {u} {σ} t =
    t [ n ][ u ]↑ [ σ ⇑[ n ] ]                   ≡⟨ substCompEq t ⟩
    t [ (σ ⇑[ n ]) ₛ•ₛ replace₁ n u ]            ≡⟨ (flip substVar-to-subst t λ where
                                                       x0     → refl
                                                       (x +1) → lemma (var x)) ⟩
    t [ replace₁ n (u [ σ ⇑[ n ] ]) ₛ•ₛ (σ ⇑) ]  ≡˘⟨ substCompEq t ⟩
    t [ σ ⇑ ] [ n ][ u [ σ ⇑[ n ] ] ]↑           ∎
    where
    lemma :
      (t : Term[ k ] m) →
      t [ wkSubst n idSubst ] [ σ ⇑[ n ] ] ≡
      wk1 (t [ σ ]) [ n ][ u [ σ ⇑[ n ] ] ]↑
    lemma t =
      t [ wkSubst n idSubst ] [ σ ⇑[ n ] ]    ≡˘⟨ cong _[ _ ] $ wk[]≡[] n ⟩
      wk[ n ] t [ σ ⇑[ n ] ]                  ≡⟨ wk[]-⇑[] n ⟩
      wk[ n ] (t [ σ ])                       ≡⟨ wk[]≡[] n ⟩
      t [ σ ] [ wkSubst n idSubst ]           ≡˘⟨ subst-wk (t [ _ ]) ⟩
      wk1 (t [ σ ]) [ n ][ u [ σ ⇑[ n ] ] ]↑  ∎

opaque

  -- The function _[_][_]↑ commutes (in another sense) with _[_].

  [][]↑-commutes-+ :
    let cast =
          subst₂ Subst (sym $ +-assoc ℓ m₂ n) (sym $ +-assoc ℓ m₁ n)
    in
    (t : Term[ k ] (1+ n)) →
    (∀ x → wk[ m₁ ] (var x) [ σ ] ≡ wk[ m₂ ] (var x)) →
    t [ ℓ + m₁ ][ u ]↑ [ cast (σ ⇑[ ℓ ]) ] ≡
    t [ ℓ + m₂ ][ u [ cast (σ ⇑[ ℓ ]) ] ]↑
  [][]↑-commutes-+ {ℓ} {m₂} {n} {m₁} {σ} {u} t hyp =
    t [ consSubst (wkSubst (ℓ + m₁) idSubst) u ] [ cast₁ (σ ⇑[ ℓ ]) ]    ≡⟨ substCompEq t ⟩

    t [ cast₁ (σ ⇑[ ℓ ]) ₛ•ₛ consSubst (wkSubst (ℓ + m₁) idSubst) u ]    ≡⟨ (flip substVar-to-subst t λ where
                                                                               x0     → refl
                                                                               (_ +1) → lemma₂ _) ⟩
    t [ consSubst (wkSubst (ℓ + m₂) idSubst) (u [ cast₁ (σ ⇑[ ℓ ]) ]) ]  ∎
    where
    cast₁ :
      Subst (ℓ + (m₂ + n)) (ℓ + (m₁ + n)) →
      Subst (ℓ + m₂ + n) (ℓ + m₁ + n)
    cast₁ = subst₂ Subst (sym $ +-assoc ℓ _ _) (sym $ +-assoc ℓ _ _)

    cast₂ : Term (ℓ + (m₂ + n)) → Term (ℓ + m₂ + n)
    cast₂ = subst Term (sym $ +-assoc ℓ _ _)

    lemma₁ :
      v [ subst₂ Subst eq₁ (sym eq₂) σ′ ] ≡
      subst Term eq₁ (subst Term eq₂ v [ σ′ ])
    lemma₁ {eq₁ = refl} {eq₂ = refl} = refl

    lemma₂ :
      ∀ x →
      wkSubst (ℓ + m₁) idSubst x [ cast₁ (σ ⇑[ ℓ ]) ] ≡
      wkSubst (ℓ + m₂) idSubst x
    lemma₂ x =
      wkSubst (ℓ + m₁) idSubst x [ cast₁ (σ ⇑[ ℓ ]) ]       ≡˘⟨ cong _[ _ ] $ wk[]≡wkSubst (ℓ + _) _ ⟩

      wk[ ℓ + m₁ ] (var x) [ cast₁ (σ ⇑[ ℓ ]) ]             ≡⟨ lemma₁ {eq₁ = sym $ +-assoc ℓ _ _} {eq₂ = +-assoc ℓ _ _} ⟩

      cast₂
        (subst Term (+-assoc ℓ _ _) (wk[ ℓ + m₁ ] (var x))
           [ σ ⇑[ ℓ ] ])                                    ≡⟨ cong cast₂ $ cong _[ _ ] $ wk[]-comp ℓ ⟩

      cast₂ (wk[ ℓ ] (wk[ m₁ ] (var x)) [ σ ⇑[ ℓ ] ])       ≡⟨ cong cast₂ $ wk[]-⇑[] ℓ ⟩

      cast₂ (wk[ ℓ ] (wk[ m₁ ] (var x) [ σ ]))              ≡⟨ cong cast₂ $ cong wk[ ℓ ] $ hyp _ ⟩

      cast₂ (wk[ ℓ ] (wk[ m₂ ] (var x)))                    ≡⟨ swap-subst $ wk[]-comp ℓ ⟩

      wk[ ℓ + m₂ ] (var x)                                  ≡⟨ wk[]≡[] (ℓ + _) ⟩

      var x [ wkSubst (ℓ + m₂) idSubst ]                    ≡⟨⟩

      wkSubst (ℓ + m₂) idSubst x                            ∎

opaque

  -- A variant of [][]↑-commutes-+.

  [][]↑-[₀⇑] :
    ∀ ℓ {u} (t : Term[ k ] (1+ n)) →
    let cast =
          subst₂ Subst (sym $ +-assoc ℓ m n) (sym $ +-assoc ℓ (1+ m) n)
    in
    t [ ℓ + 1+ m ][ u ]↑ [ cast (sgSubst v ⇑[ ℓ ]) ] ≡
    t [ ℓ + m ][ u [ cast (sgSubst v ⇑[ ℓ ]) ] ]↑
  [][]↑-[₀⇑] {m} {v} _ t =
    [][]↑-commutes-+ t λ x →
      wk[ 1+ m ] (var x) [ v ]₀     ≡⟨⟩
      wk1 (wk[ m ] (var x)) [ v ]₀  ≡⟨ wk1-sgSubst _ _ ⟩
      wk[ m ] (var x)               ∎

private opaque

  -- An example of how [][]↑-[₀⇑] can be used. Note that the cast
  -- "disappears".

  _ :
    (t : Term[ k ] (1+ m)) →
    t [ 1+ n ][ u ]↑ [ v ]₀ ≡
    t [ n ][ u [ v ]₀ ]↑
  _ = [][]↑-[₀⇑] 0

opaque

  -- A variant of [][]↑-commutes-+.

  [][]↑-[,⇑] :
    ∀ ℓ {u} (t : Term[ k ] (1+ n)) →
    let cast =
          subst₂ Subst (sym $ +-assoc ℓ m n) (sym $ +-assoc ℓ (2+ m) n)
    in
    t [ ℓ + 2+ m ][ u ]↑ [ cast (consSubst (sgSubst v) w ⇑[ ℓ ]) ] ≡
    t [ ℓ + m ][ u [ cast (consSubst (sgSubst v) w ⇑[ ℓ ]) ] ]↑
  [][]↑-[,⇑] {m} {v} {w} _ t =
    [][]↑-commutes-+ t λ x →
      wk[ 2+ m ] (var x) [ v , w ]₁₀  ≡⟨ wk2-[,] ⟩
      wk[ m ] (var x)                 ∎

private opaque

  -- An example of how [][]↑-[,⇑] can be used.

  _ :
    (t : Term[ k ] (1+ m)) →
    t [ 2+ n ][ u ]↑ [ v , w ]₁₀ ≡
    t [ n ][ u [ v , w ]₁₀ ]↑
  _ = [][]↑-[,⇑] 0

opaque

  -- A variant of [][]↑-commutes-+.

  [][]↑-[↑⇑] :
    ∀ ℓ {u} (t : Term[ k ] (1+ n)) →
    let σ    = wk1Subst idSubst
        cast =
          subst₂ Subst (sym $ +-assoc ℓ (1+ m) n)
            (sym $ +-assoc ℓ (1+ m) n)
    in
    t [ ℓ + 1+ m ][ u ]↑ [ cast (consSubst σ v ⇑[ ℓ ]) ] ≡
    t [ ℓ + 1+ m ][ u [ cast (consSubst σ v ⇑[ ℓ ]) ] ]↑
  [][]↑-[↑⇑] {m} {v} _ t =
    [][]↑-commutes-+ t λ x →
      wk[ 1+ m ] (var x) [ consSubst (wk1Subst idSubst) v ]  ≡⟨ wk1-tail (wk[ m ] _) ⟩
      wk[ m ] (var x) [ wk1Subst idSubst ]                   ≡˘⟨ wk[]≡[] 1 ⟩
      wk[ 1+ m ] (var x)                                     ∎

private opaque

  -- An example of how [][]↑-[↑⇑] can be used.

  _ :
    (t : Term[ k ] (1+ m)) →
    t [ 1+ n ][ u ]↑ [ v ]↑ ≡
    t [ 1+ n ][ u [ v ]↑ ]↑
  _ = [][]↑-[↑⇑] 0

opaque

  -- A weakening lemma for _[_][_]↑.

  [][wk[]′]↑ :
    (t : Term[ k ] (1+ m)) →
    t [ n ][ wk[ n ]′ u ]↑ ≡ wk[ n ]′ (t [ u ]₀)
  [][wk[]′]↑ {n} {u} t =
    t [ n ][ wk[ n ]′ u ]↑                    ≡⟨ [][]↑≡ t ⟩
    wk (lift (stepn id n)) t [ wk[ n ]′ u ]₀  ≡˘⟨ wk-β t ⟩
    wk[ n ]′ (t [ u ]₀)                       ∎

opaque

  -- A weakening lemma for _[_][_]↑.

  wk[]′[][]↑ :
    ∀ ℓ →
    let cast = λ {k} → subst Term[ k ] (sym $ +-assoc ℓ m n) in
    (t : Term[ k ] (1+ n)) →
    cast (wk[ ℓ ]′ (t [ m ][ u ]↑)) ≡
    t [ ℓ + m ][ cast (wk[ ℓ ]′ u) ]↑
  wk[]′[][]↑ {m} {n} {u} ℓ t =
    cast (wk[ ℓ ]′ (t [ consSubst (wkSubst m idSubst) u ]))        ≡⟨ cong cast $ wk-subst t ⟩
    cast (t [ stepn id ℓ •ₛ consSubst (wkSubst m idSubst) u ])     ≡⟨ lemma₁ ⟩
    t [ cast ∘→ (stepn id ℓ •ₛ consSubst (wkSubst m idSubst) u) ]  ≡⟨ (flip substVar-to-subst t λ where
                                                                         x0     → refl
                                                                         (_ +1) → lemma₂ _) ⟩
    t [ consSubst (wkSubst (ℓ + m) idSubst) (cast (wk[ ℓ ]′ u)) ]  ∎
    where
    cast : Term[ k ] (ℓ + (m + n)) → Term[ k ] ((ℓ + m) + n)
    cast = subst Term[ _ ] (sym $ +-assoc ℓ m n)

    lemma₁ : cast (t [ σ ]) ≡ t [ cast ∘→ σ ]
    lemma₁ rewrite +-assoc ℓ m n = refl

    lemma₂ :
      ∀ x →
      cast (wk[ ℓ ]′ (wkSubst m idSubst x)) ≡ wkSubst (ℓ + m) idSubst x
    lemma₂ x =
      cast (wk[ ℓ ]′ (wkSubst m idSubst x))   ≡˘⟨ cong cast wk[]≡wk[]′ ⟩
      cast (wk[ ℓ ] (wkSubst m idSubst x))    ≡⟨ cong cast $ wk[]≡wkSubst ℓ _ ⟩
      cast (wkSubst ℓ (wkSubst m idSubst) x)  ≡⟨ swap-subst $ wkSubst-comp ℓ _ ⟩
      wkSubst (ℓ + m) idSubst x               ∎

private opaque

  -- An example of how wk[]′[][]↑ can be used.

  _ :
    (t : Term[ k ] (1+ m)) →
    wk1 (t [ n ][ u ]↑) ≡ t [ 1+ n ][ wk1 u ]↑
  _ = wk[]′[][]↑ 1

opaque

  -- A weakening lemma for _[_][_]↑.

  wk1-[][]↑ : ∀ n {u} → wk1 t [ n ][ u ]↑ ≡ wk[ n ] t
  wk1-[][]↑ {t} n {u} =
    wk1 t [ consSubst (wkSubst n idSubst) u ]         ≡⟨ subst-wk t ⟩
    t [ consSubst (wkSubst n idSubst) u ₛ• step id ]  ≡⟨⟩
    t [ wkSubst n idSubst ]                           ≡˘⟨ wk[]≡[] n ⟩
    wk[ n ] t                                         ∎

opaque

  -- A weakening lemma for _[_][_]↑.

  wk1-[][]↑′ : wk1 t [ n ][ u ]↑ ≡ wk[ n ]′ t
  wk1-[][]↑′ {t} {n} {u} =
    wk1 t [ n ][ u ]↑  ≡⟨ wk1-[][]↑ n ⟩
    wk[ n ] t          ≡⟨ wk[]≡wk[]′ ⟩
    wk[ n ]′ t         ∎

opaque

  -- A lemma related to t [ 1+ n ][ var x0 ]↑.

  [1+][0]↑ : t [ 1+ n ][ var x0 ]↑ ≡ wk (lift (stepn id n)) t
  [1+][0]↑ {t} {n} =
    t [ 1+ n ][ var x0 ]↑                             ≡⟨ [][]↑≡ t ⟩
    wk (lift (stepn id (1+ n))) t [ var x0 ]₀         ≡⟨ subst-wk t ⟩
    t [ sgSubst (var x0) ₛ• lift (stepn id (1+ n)) ]  ≡⟨ (flip substVar-to-subst t λ where
                                                            x0     → refl
                                                            (_ +1) → refl) ⟩
    t [ toSubst (lift (stepn id n)) ]                 ≡˘⟨ wk≡subst _ _ ⟩
    wk (lift (stepn id n)) t                          ∎

opaque

  -- The result of t [ var x0 ]↑ is equal to t.

  [0]↑ : t [ var x0 ]↑ ≡ t
  [0]↑ {t} =
    t [ var x0 ]↑   ≡⟨ [1+][0]↑ ⟩
    wk (lift id) t  ≡⟨ wk-lift-id _ ⟩
    t               ∎

------------------------------------------------------------------------
-- Some lemmas related to replace₂

opaque
  unfolding replace₂

  -- A lemma related to wk[_]′ and replace₂.

  wk[2+]′-[replace₂] :
    wk[ 2+ n ]′ t [ replace₂ u v ] ≡ wk[ 2+ n ]′ t
  wk[2+]′-[replace₂] {n} {t} {u} {v} =
    wk[ 2+ n ]′ t [ replace₂ u v ]         ≡⟨ subst-wk t ⟩
    t [ replace₂ u v ₛ• stepn id (2+ n) ]  ≡⟨⟩
    t [ toSubst (stepn id (2+ n)) ]        ≡˘⟨ wk≡subst _ _ ⟩
    wk[ 2+ n ]′ t                          ∎

opaque

  -- A lemma related to wk[_] and replace₂.

  wk[2+]-[replace₂] :
    wk[ 2+ n ] t [ replace₂ u v ] ≡ wk[ 2+ n ] t
  wk[2+]-[replace₂] {n} {t} {u} {v} =
    wk[ 2+ n ] t [ replace₂ u v ]   ≡⟨ PE.cong _[ _ ] $ wk[]≡wk[]′ {n = 2+ n} ⟩
    wk[ 2+ n ]′ t [ replace₂ u v ]  ≡⟨ wk[2+]′-[replace₂] ⟩
    wk[ 2+ n ]′ t                   ≡˘⟨ wk[]≡wk[]′ ⟩
    wk[ 2+ n ] t                    ∎

opaque
  unfolding replace₂

  -- A lemma related to _⇑[_] and replace₂.

  [replace₂]-[⇑] :
    (t : Term[ k ] (2+ m + n₂)) (σ : Subst n₁ n₂) →
    let σ⇑ = σ ⇑[ 2 + m ] in
    t [ replace₂ u v ] [ σ⇑ ] ≡
    t [ σ⇑ ] [ replace₂ (u [ σ⇑ ]) (v [ σ⇑ ]) ]
  [replace₂]-[⇑] {m} {u} {v} t σ =
    let σ⇑ = σ ⇑[ 2 + m ] in
    t [ replace₂ u v ] [ σ⇑ ]                    ≡⟨ substCompEq t ⟩
    t [ σ⇑ ₛ•ₛ replace₂ u v ]                    ≡⟨ (flip substVar-to-subst t λ where
                                                       x0        → PE.refl
                                                       (x0 +1)   → PE.refl
                                                       (_ +1 +1) → PE.sym $ wk[2+]-[replace₂] {n = 0}) ⟩
    t [ replace₂ (u [ σ⇑ ]) (v [ σ⇑ ]) ₛ•ₛ σ⇑ ]  ≡˘⟨ substCompEq t ⟩
    t [ σ⇑ ] [ replace₂ (u [ σ⇑ ]) (v [ σ⇑ ]) ]  ∎

opaque
  unfolding replace₂

  -- A lemma related to _[_,_]₁₀ and replace₂.

  [replace₂]-[,]₁₀ :
    (t : Term[ k ] (2+ n)) →
    t [ replace₂ u₁ u₂ ] [ v₁ , v₂ ]₁₀ ≡
    t [ u₁ [ v₁ , v₂ ]₁₀ , u₂ [ v₁ , v₂ ]₁₀ ]₁₀
  [replace₂]-[,]₁₀ t =
    trans (substCompEq t) $
    flip substVar-to-subst t λ where
      x0        → refl
      (x0 +1)   → refl
      (_ +1 +1) → refl

opaque
  unfolding replace₂

  -- A lemma related to _[_][_]↑ and replace₂.

  [2][]↑-[replace₂] :
    (t : Term[ k ] (1+ n)) →
    t [ 2 ][ u ]↑ [ replace₂ v₁ v₂ ] ≡
    t [ u [ replace₂ v₁ v₂ ] ]↑²
  [2][]↑-[replace₂] t =
    PE.trans (substCompEq t) $
    flip substVar-to-subst t λ where
      x0     → refl
      (_ +1) → refl

------------------------------------------------------------------------
-- Some lemmas related to numerals

-- The predicate Numeral is decidable

opaque

  isNumeral? : (t : Term n) → Dec (Numeral t)
  isNumeral? zero = yes zeroₙ
  isNumeral? (suc t) =
    case isNumeral? t of λ where
      (yes n) → yes (sucₙ n)
      (no ¬n) → no (λ { (sucₙ n) → ¬n n})
  isNumeral? (var x) = no (λ ())
  isNumeral? (defn α) = no (λ ())
  isNumeral? Level = no (λ ())
  isNumeral? zeroᵘ = no (λ ())
  isNumeral? (sucᵘ _) = no (λ ())
  isNumeral? (_ supᵘ _) = no (λ ())
  isNumeral? (U n) = no (λ ())
  isNumeral? (Lift _ _) = no λ ()
  isNumeral? (lift _) = no λ ()
  isNumeral? (lower _) = no λ ()
  isNumeral? ℕ = no λ ()
  isNumeral? Empty = no λ ()
  isNumeral? Unit! = no λ ()
  isNumeral? (ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _) = no λ ()
  isNumeral? (Id _ _ _) = no λ ()
  isNumeral? (lam _ _) = no λ ()
  isNumeral? (_ ∘ _) = no λ ()
  isNumeral? (prod! _ _) = no λ ()
  isNumeral? (fst _ _) = no λ ()
  isNumeral? (snd _ _) = no λ ()
  isNumeral? (prodrec _ _ _ _ _ _) = no λ ()
  isNumeral? (natrec _ _ _ _ _ _ _) = no λ ()
  isNumeral? star! = no λ ()
  isNumeral? (unitrec _ _ _ _ _) = no λ ()
  isNumeral? (emptyrec _ _ _) = no λ ()
  isNumeral? rfl = no λ ()
  isNumeral? (J _ _ _ _ _ _ _ _) = no λ ()
  isNumeral? (K _ _ _ _ _ _) = no λ ()
  isNumeral? ([]-cong! _ _ _ _ _) = no λ ()

opaque

  -- Being a numeral is preserved under weakening

  wk-numeral : Numeral t → Numeral (wk ρ t)
  wk-numeral zeroₙ = zeroₙ
  wk-numeral (sucₙ n) = sucₙ (wk-numeral n)

opaque

  -- Applying substitutions to numerals has no effect

  subst-numeral : Numeral t → t [ σ ] ≡ t
  subst-numeral zeroₙ = refl
  subst-numeral (sucₙ n) = cong suc (subst-numeral n)

opaque

  -- The term sucⁿ k is a Numeral

  sucⁿ-Numeral : ∀ k → Numeral (sucⁿ {n} k)
  sucⁿ-Numeral 0 = zeroₙ
  sucⁿ-Numeral (1+ k) = sucₙ (sucⁿ-Numeral k)

opaque

  -- If a term is a Numeral it is equal to sucⁿ k for some k.

  Numeral→sucⁿ : Numeral t → ∃ λ k → t ≡ sucⁿ k
  Numeral→sucⁿ zeroₙ = 0 , refl
  Numeral→sucⁿ (sucₙ n) =
    case (Numeral→sucⁿ n) of
      λ (k , t≡) →
    1+ k , cong suc t≡

opaque

  -- Applying a substitution to sucⁿ k has no effect

  subst-sucⁿ : ∀ k → sucⁿ k [ σ ] ≡ sucⁿ k
  subst-sucⁿ 0 = refl
  subst-sucⁿ (1+ k) = cong suc (subst-sucⁿ k)

opaque

  -- Applying a weakening to sucⁿ k has no effect

  wk-sucⁿ : ∀ k → wk ρ (sucⁿ k) ≡ sucⁿ k
  wk-sucⁿ 0 = refl
  wk-sucⁿ (1+ k) = cong suc (wk-sucⁿ k)

------------------------------------------------------------------------
-- Injectivity of constructors with respect to propositional equality

-- U is injective.

U-PE-injectivity : U l₁ PE.≡ U l₂ → l₁ PE.≡ l₂
U-PE-injectivity PE.refl = PE.refl

-- Lift is injective.

Lift-PE-injectivity :
  Lift l₁ A₁ PE.≡ Lift l₂ A₂ → l₁ PE.≡ l₂ × A₁ PE.≡ A₂
Lift-PE-injectivity PE.refl = PE.refl , PE.refl

-- The constructor Term[_].sucᵘ is injective.

sucᵘ-PE-injectivity : Term[_].sucᵘ t₁ PE.≡ sucᵘ t₂ → t₁ PE.≡ t₂
sucᵘ-PE-injectivity PE.refl = PE.refl

-- The constructor supᵘ is injective.

supᵘ-PE-injectivity : t₁ supᵘ u₁ PE.≡ t₂ supᵘ u₂ → t₁ PE.≡ t₂ × u₁ PE.≡ u₂
supᵘ-PE-injectivity PE.refl = PE.refl , PE.refl

-- The constructor Term[_].ωᵘ+ is injective.

ωᵘ+-PE-injectivity : Term[_].ωᵘ+ {n = n} m₁ PE.≡ ωᵘ+ m₂ → m₁ PE.≡ m₂
ωᵘ+-PE-injectivity PE.refl = PE.refl

-- The constructor Term[_].level is injective.

level-PE-injectivity : Term[_].level t₁ PE.≡ level t₂ → t₁ PE.≡ t₂
level-PE-injectivity PE.refl = PE.refl

-- BΠ is injective.

BΠ-PE-injectivity : BM BMΠ p₁ q₁ PE.≡ BM BMΠ p₂ q₂ → p₁ PE.≡ p₂ × q₁ PE.≡ q₂ -- Cannot use BΠ here because of #5054
BΠ-PE-injectivity PE.refl = PE.refl , PE.refl

-- BΣ is injective.

BΣ-PE-injectivity :
  BM (BMΣ s₁) p₁ q₁ PE.≡ BM (BMΣ s₂) p₂ q₂ → p₁ PE.≡ p₂ × q₁ PE.≡ q₂ × s₁ PE.≡ s₂ -- As above, for BΣ
BΣ-PE-injectivity PE.refl = PE.refl , PE.refl , PE.refl

-- The constructor Term[_].var is injective.

var-PE-injectivity : Term[_].var {n = n} x₁ PE.≡ var x₂ → x₁ PE.≡ x₂
var-PE-injectivity PE.refl = PE.refl

-- The constructor Term[_].defn is injective.

defn-PE-injectivity : Term[_].defn {n = n} α PE.≡ defn β → α PE.≡ β
defn-PE-injectivity PE.refl = PE.refl

-- ΠΣ⟨_⟩_,_▷_▹_ is injective.

ΠΣ-PE-injectivity :
  ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ PE.≡ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ →
  b₁ PE.≡ b₂ × p₁ PE.≡ p₂ × q₁ PE.≡ q₂ × A₁ PE.≡ A₂ × B₁ PE.≡ B₂
ΠΣ-PE-injectivity PE.refl =
  PE.refl , PE.refl , PE.refl , PE.refl , PE.refl

-- ⟦_⟧_▷_▹_ is injective.

B-PE-injectivity :
  ∀ W₁ W₂ → ⟦ W₁ ⟧ A₁ ▹ B₁ PE.≡ ⟦ W₂ ⟧ A₂ ▹ B₂ →
  A₁ PE.≡ A₂ × B₁ PE.≡ B₂ × W₁ PE.≡ W₂
B-PE-injectivity (BM _ _ _) (BM _ _ _) PE.refl =
  PE.refl , PE.refl , PE.refl

-- The constructor _∘⟨_⟩_ is injective.

∘-PE-injectivity :
  t₁ ∘⟨ p₁ ⟩ u₁ PE.≡ t₂ ∘⟨ p₂ ⟩ u₂ →
  p₁ PE.≡ p₂ × t₁ PE.≡ t₂ × u₁ PE.≡ u₂
∘-PE-injectivity PE.refl = PE.refl , PE.refl , PE.refl

-- The constructor lam is injective.

lam-PE-injectivity :
  lam p₁ t₁ PE.≡ lam p₂ t₂ →
  p₁ PE.≡ p₂ × t₁ PE.≡ t₂
lam-PE-injectivity PE.refl = PE.refl , PE.refl

-- The constructor prod is injective.

prod-PE-injectivity :
  prod s₁ p₁ t₁ u₁ PE.≡ prod s₂ p₂ t₂ u₂ →
  s₁ PE.≡ s₂ × p₁ PE.≡ p₂ × t₁ PE.≡ t₂ × u₁ PE.≡ u₂
prod-PE-injectivity PE.refl = PE.refl , PE.refl , PE.refl , PE.refl

-- The constructor prodrec is injective.

prodrec-PE-injectivity :
  prodrec r₁ p₁ q₁ A₁ t₁ u₁ PE.≡ prodrec r₂ p₂ q₂ A₂ t₂ u₂ →
  r₁ PE.≡ r₂ × p₁ PE.≡ p₂ × q₁ PE.≡ q₂ × A₁ PE.≡ A₂ × t₁ PE.≡ t₂ ×
  u₁ PE.≡ u₂
prodrec-PE-injectivity PE.refl =
  PE.refl , PE.refl , PE.refl , PE.refl , PE.refl , PE.refl

-- The constructor emptyrec is injective.

emptyrec-PE-injectivity :
  emptyrec p₁ A₁ t₁ PE.≡ emptyrec p₂ A₂ t₂ →
  p₁ PE.≡ p₂ × A₁ PE.≡ A₂ × t₁ PE.≡ t₂
emptyrec-PE-injectivity PE.refl = PE.refl , PE.refl , PE.refl

-- The constructor Unit is injective.

Unit-PE-injectivity :
  _≡_ {A = Term n} (Unit s₁) (Unit s₂) →
  s₁ ≡ s₂
Unit-PE-injectivity refl = refl

-- The constructor star is injective.

star-PE-injectivity :
  _≡_ {A = Term n} (star s₁) (star s₂) → s₁ PE.≡ s₂
star-PE-injectivity PE.refl = PE.refl

-- The constructor unitrec is injective.

unitrec-PE-injectivity :
  unitrec p₁ q₁ A₁ t₁ u₁ PE.≡ unitrec p₂ q₂ A₂ t₂ u₂ →
  p₁ PE.≡ p₂ × q₁ PE.≡ q₂ × A₁ PE.≡ A₂ × t₁ PE.≡ t₂ ×
  u₁ PE.≡ u₂
unitrec-PE-injectivity PE.refl =
  PE.refl , PE.refl , PE.refl , PE.refl , PE.refl

-- The constructor suc is injective.

suc-PE-injectivity : suc t₁ PE.≡ suc t₂ → t₁ PE.≡ t₂
suc-PE-injectivity PE.refl = PE.refl

opaque

  -- The function sucⁿ is injective.

  sucⁿ-PE-injectivity : sucⁿ {n = n} n₁ ≡ sucⁿ n₂ → n₁ ≡ n₂
  sucⁿ-PE-injectivity {n₁ = 0}    {n₂ = 0}    _  = refl
  sucⁿ-PE-injectivity {n₁ = 0}    {n₂ = 1+ _} ()
  sucⁿ-PE-injectivity {n₁ = 1+ _} {n₂ = 0}    ()
  sucⁿ-PE-injectivity {n₁ = 1+ _} {n₂ = 1+ _} eq =
    cong 1+ (sucⁿ-PE-injectivity (suc-PE-injectivity eq))

-- The constructor natrec is injective.

natrec-PE-injectivity :
  natrec p₁ q₁ r₁ A₁ t₁ u₁ v₁ PE.≡ natrec p₂ q₂ r₂ A₂ t₂ u₂ v₂ →
  p₁ PE.≡ p₂ × q₁ PE.≡ q₂ × r₁ PE.≡ r₂ × A₁ PE.≡ A₂ × t₁ PE.≡ t₂ ×
  u₁ PE.≡ u₂ × v₁ PE.≡ v₂
natrec-PE-injectivity PE.refl =
  PE.refl , PE.refl , PE.refl , PE.refl , PE.refl , PE.refl , PE.refl

-- Id is injective.

Id-PE-injectivity :
  Id A₁ t₁ u₁ PE.≡ Id A₂ t₂ u₂ →
  A₁ PE.≡ A₂ × t₁ PE.≡ t₂ × u₁ PE.≡ u₂
Id-PE-injectivity PE.refl = PE.refl , PE.refl , PE.refl

-- J is injective.

J-PE-injectivity :
  J p₁ q₁ A₁ t₁ B₁ u₁ v₁ w₁ PE.≡ J p₂ q₂ A₂ t₂ B₂ u₂ v₂ w₂ →
  p₁ PE.≡ p₂ × q₁ PE.≡ q₂ × A₁ PE.≡ A₂ × t₁ PE.≡ t₂ × B₁ PE.≡ B₂ ×
  u₁ PE.≡ u₂ × v₁ PE.≡ v₂ × w₁ PE.≡ w₂
J-PE-injectivity PE.refl =
  PE.refl , PE.refl , PE.refl , PE.refl , PE.refl , PE.refl ,
  PE.refl , PE.refl

-- K is injective.

K-PE-injectivity :
  K p₁ A₁ t₁ B₁ u₁ v₁ PE.≡ K p₂ A₂ t₂ B₂ u₂ v₂ →
  p₁ PE.≡ p₂ × A₁ PE.≡ A₂ × t₁ PE.≡ t₂ × B₁ PE.≡ B₂ × u₁ PE.≡ u₂ ×
  v₁ PE.≡ v₂
K-PE-injectivity PE.refl =
  PE.refl , PE.refl , PE.refl , PE.refl , PE.refl , PE.refl

-- []-cong is injective.

[]-cong-PE-injectivity :
  []-cong s₁ l₁ A₁ t₁ u₁ v₁ PE.≡ []-cong s₂ l₂ A₂ t₂ u₂ v₂ →
  s₁ PE.≡ s₂ × l₁ PE.≡ l₂ × A₁ PE.≡ A₂ × t₁ PE.≡ t₂ × u₁ PE.≡ u₂ ×
  v₁ PE.≡ v₂
[]-cong-PE-injectivity PE.refl =
  PE.refl , PE.refl , PE.refl , PE.refl , PE.refl , PE.refl

------------------------------------------------------------------------
-- Properties related to inlining of definitions

opaque
  unfolding inline-Con

  -- If A or-empty Γ holds, then A or-empty inline-Con ξ Γ holds.

  or-empty-inline-Con :
    {A : Set a} ⦃ ok : A or-empty Γ ⦄ →
    A or-empty inline-Con ξ Γ
  or-empty-inline-Con ⦃ ok = ε ⦄                 = ε
  or-empty-inline-Con ⦃ ok = possibly-nonempty ⦄ = possibly-nonempty

opaque
  unfolding inline-Conᵈ

  -- If A or-empty Γ holds, then A or-empty inline-Conᵈ ∇ Γ holds.

  or-empty-inline-Conᵈ :
    {A : Set a} ⦃ ok : A or-empty Γ ⦄ →
    A or-empty inline-Conᵈ ∇ Γ
  or-empty-inline-Conᵈ = or-empty-inline-Con

opaque
  unfolding inline-Nat

  -- The function inline-Nat (id eq) is pointwise equal to defn.

  inline-Nat-id :
    {eq : m ≡ n} →
    inline-Nat (id eq) α ≡ defn α
  inline-Nat-id {m} {α} {eq = refl} with m ≤? α
  … | no _    = refl
  … | yes m≤α with α <′? m
  …   | no _    = refl
  …   | yes α<m = ⊥-elim (n≮n _ (≤-trans (<′⇒< α<m) m≤α))

opaque
  unfolding inline

  -- The function inline (id eq) is pointwise equal to the identity
  -- function.

  inline-id : (t : Term[ k ] n) → inline (id eq) t ≡ t
  inline-id (var _) =
    refl
  inline-id {eq} (defn _) =
    PE.cong (wk _) (inline-Nat-id {eq = eq})
  inline-id Level =
    refl
  inline-id zeroᵘ =
    refl
  inline-id (sucᵘ t) =
    cong sucᵘ (inline-id t)
  inline-id (t supᵘ u) =
    cong₂ _supᵘ_ (inline-id t) (inline-id u)
  inline-id (ωᵘ+ _) =
    refl
  inline-id (level t) =
    cong level (inline-id t)
  inline-id (U l) =
    cong U (inline-id l)
  inline-id (Lift l A) =
    cong₂ Lift (inline-id l) (inline-id A)
  inline-id (lift t) =
    cong lift (inline-id t)
  inline-id (lower t) =
    cong lower (inline-id t)
  inline-id Empty =
    refl
  inline-id (emptyrec p A t) =
    cong₂ (emptyrec _) (inline-id A) (inline-id t)
  inline-id (Unit _) =
    refl
  inline-id (star _) =
    refl
  inline-id (unitrec _ _ A t u) =
    cong₃ (unitrec _ _) (inline-id A) (inline-id t) (inline-id u)
  inline-id (ΠΣ⟨ _ ⟩ _ , _ ▷ A ▹ B) =
    cong₂ (ΠΣ⟨ _ ⟩ _ , _ ▷_▹_) (inline-id A) (inline-id B)
  inline-id (lam p t) =
    cong (lam _) (inline-id t)
  inline-id (t ∘⟨ p ⟩ u) =
    cong₂ (_∘⟨ _ ⟩_) (inline-id t) (inline-id u)
  inline-id (prod s p t u) =
    cong₂ (prod _ _) (inline-id t) (inline-id u)
  inline-id (fst p t) =
    cong (fst _) (inline-id t)
  inline-id (snd p t) =
    cong (snd _) (inline-id t)
  inline-id (prodrec r p q A t u) =
    cong₃ (prodrec _ _ _) (inline-id A) (inline-id t) (inline-id u)
  inline-id ℕ =
    refl
  inline-id zero =
    refl
  inline-id (suc t) =
    cong suc (inline-id t)
  inline-id (natrec p q r A t u v) =
    cong₄ (natrec _ _ _) (inline-id A) (inline-id t) (inline-id u)
      (inline-id v)
  inline-id (Id A t u) =
    cong₃ Id (inline-id A) (inline-id t) (inline-id u)
  inline-id rfl =
    refl
  inline-id (J p q A t B u v w) =
    cong₆ (J _ _) (inline-id A) (inline-id t) (inline-id B)
      (inline-id u) (inline-id v) (inline-id w)
  inline-id (K p A t B u v) =
    cong₅ (K _) (inline-id A) (inline-id t) (inline-id B) (inline-id u)
      (inline-id v)
  inline-id ([]-cong _ l A t u v) =
    cong₅ ([]-cong _) (inline-id l) (inline-id A) (inline-id t)
      (inline-id u) (inline-id v)

opaque
  unfolding inline-Con

  -- The function inline-Con {m₂ = n} idᵉ is pointwise equal to the
  -- identity function.

  inline-Con-id :
    (Γ : Con Term m) → inline-Con {m₂ = n} idᵉ Γ ≡ Γ
  inline-Con-id ε       = refl
  inline-Con-id (_ ∙ _) = cong₂ _∙_ (inline-Con-id _) (inline-id _)

opaque
  unfolding inline

  -- The function inline ξ commutes with wk ρ.

  wk-inline : (t : Term[ k ] n) → wk ρ (inline ξ t) ≡ inline ξ (wk ρ t)
  wk-inline (var _) =
    refl
  wk-inline (defn _) =
    wk₀-comp _ _
  wk-inline Level =
    refl
  wk-inline zeroᵘ =
    refl
  wk-inline (sucᵘ t) =
    cong sucᵘ (wk-inline t)
  wk-inline (t supᵘ u) =
    cong₂ _supᵘ_ (wk-inline t) (wk-inline u)
  wk-inline (ωᵘ+ _) =
    refl
  wk-inline (level t) =
    cong level (wk-inline t)
  wk-inline (U l) =
    cong U (wk-inline l)
  wk-inline (Lift l A) =
    cong₂ Lift (wk-inline l) (wk-inline A)
  wk-inline (lift t) =
    cong lift (wk-inline t)
  wk-inline (lower t) =
    cong lower (wk-inline t)
  wk-inline Empty =
    refl
  wk-inline (emptyrec p A t) =
    cong₂ (emptyrec _) (wk-inline A) (wk-inline t)
  wk-inline (Unit _) =
    refl
  wk-inline (star _) =
    refl
  wk-inline (unitrec _ _ A t u) =
    cong₃ (unitrec _ _) (wk-inline A) (wk-inline t) (wk-inline u)
  wk-inline (ΠΣ⟨ _ ⟩ _ , _ ▷ A ▹ B) =
    cong₂ (ΠΣ⟨ _ ⟩ _ , _ ▷_▹_) (wk-inline A) (wk-inline B)
  wk-inline (lam p t) =
    cong (lam _) (wk-inline t)
  wk-inline (t ∘⟨ p ⟩ u) =
    cong₂ (_∘⟨ _ ⟩_) (wk-inline t) (wk-inline u)
  wk-inline (prod s p t u) =
    cong₂ (prod _ _) (wk-inline t) (wk-inline u)
  wk-inline (fst p t) =
    cong (fst _) (wk-inline t)
  wk-inline (snd p t) =
    cong (snd _) (wk-inline t)
  wk-inline (prodrec r p q A t u) =
    cong₃ (prodrec _ _ _) (wk-inline A) (wk-inline t) (wk-inline u)
  wk-inline ℕ =
    refl
  wk-inline zero =
    refl
  wk-inline (suc t) =
    cong suc (wk-inline t)
  wk-inline (natrec p q r A t u v) =
    cong₄ (natrec _ _ _) (wk-inline A) (wk-inline t) (wk-inline u)
      (wk-inline v)
  wk-inline (Id A t u) =
    cong₃ Id (wk-inline A) (wk-inline t) (wk-inline u)
  wk-inline rfl =
    refl
  wk-inline (J p q A t B u v w) =
    cong₆ (J _ _) (wk-inline A) (wk-inline t) (wk-inline B)
      (wk-inline u) (wk-inline v) (wk-inline w)
  wk-inline (K p A t B u v) =
    cong₅ (K _) (wk-inline A) (wk-inline t) (wk-inline B) (wk-inline u)
      (wk-inline v)
  wk-inline ([]-cong _ l A t u v) =
    cong₅ ([]-cong _) (wk-inline l) (wk-inline A) (wk-inline t)
      (wk-inline u) (wk-inline v)

opaque
  unfolding inline inline-Subst

  -- The function inline-Subst commutes (in a certain sense) with _⇑.

  inline-Subst-⇑ :
    (x : Fin (1+ n)) →
    inline-Subst ξ (σ ⇑) x ≡ (inline-Subst ξ σ ⇑) x
  inline-Subst-⇑ x0             = refl
  inline-Subst-⇑ {ξ} {σ} (x +1) =
    inline ξ (wk1 (σ x))  ≡˘⟨ wk-inline (σ _) ⟩
    wk1 (inline ξ (σ x))  ∎

opaque

  -- The function inline-Subst commutes (in a certain sense) with
  -- _⇑[_].

  inline-Subst-⇑[] :
    ∀ m (x : Fin (m + n)) →
    inline-Subst ξ (σ ⇑[ m ]) x ≡ (inline-Subst ξ σ ⇑[ m ]) x
  inline-Subst-⇑[]         0      _ = refl
  inline-Subst-⇑[] {ξ} {σ} (1+ m) x =
    inline-Subst ξ (σ ⇑[ m ] ⇑) x    ≡⟨ inline-Subst-⇑ x ⟩
    (inline-Subst ξ (σ ⇑[ m ]) ⇑) x  ≡⟨ substVar-lift (inline-Subst-⇑[] m) x ⟩
    (inline-Subst ξ σ ⇑[ m ] ⇑) x    ∎

opaque
  unfolding inline-Subst

  -- The function inline-Subst commutes (in a certain sense) with
  -- consSubst.

  inline-Subst-consSubst :
    (x : Fin (1+ n)) →
    inline-Subst ξ (consSubst σ t) x ≡
    consSubst (inline-Subst ξ σ) (inline ξ t) x
  inline-Subst-consSubst x0     = refl
  inline-Subst-consSubst (_ +1) = refl

opaque
  unfolding inline inline-Subst

  -- The function inline-Subst commutes (in a certain sense) with
  -- idSubst.

  inline-Subst-idSubst :
    (x : Fin n) →
    inline-Subst ξ idSubst x ≡ idSubst x
  inline-Subst-idSubst _ = refl

opaque

  -- The function inline-Subst commutes (in a certain sense) with
  -- sgSubst.

  inline-Subst-sgSubst :
    (x : Fin (1+ n)) →
    inline-Subst ξ (sgSubst t) x ≡
    sgSubst (inline ξ t) x
  inline-Subst-sgSubst {ξ} {t} x =
    inline-Subst ξ (consSubst idSubst t) x             ≡⟨ inline-Subst-consSubst x ⟩
    consSubst (inline-Subst ξ idSubst) (inline ξ t) x  ≡⟨ consSubst-cong refl inline-Subst-idSubst x ⟩
    consSubst idSubst (inline ξ t) x                   ∎

opaque
  unfolding inline-Subst

  -- The function inline-Subst commutes (in a certain sense) with
  -- wk1Subst.

  inline-Subst-wk1Subst :
    (x : Fin (1+ n)) →
    inline-Subst ξ (wk1Subst σ) x ≡
    wk1Subst (inline-Subst ξ σ) x
  inline-Subst-wk1Subst {σ} _ = sym $ wk-inline (σ _)

opaque
  unfolding inline-Subst

  -- The function inline-Subst commutes (in a certain sense) with
  -- wkSubst.

  inline-Subst-wkSubst :
    ∀ k (x : Fin n) →
    inline-Subst ξ (wkSubst k σ) x ≡
    wkSubst k (inline-Subst ξ σ) x
  inline-Subst-wkSubst 0 _ =
    refl
  inline-Subst-wkSubst {ξ} {σ} (1+ k) x =
    inline ξ (wk1 (wkSubst k σ x))        ≡˘⟨ wk-inline (wkSubst k _ _) ⟩
    wk1 (inline-Subst ξ (wkSubst k σ) x)  ≡⟨ cong wk1 $ inline-Subst-wkSubst k _ ⟩
    wk1 (wkSubst k (inline-Subst ξ σ) x)  ∎

opaque
 unfolding inline inline-Subst
 mutual

  -- The function inline ξ commutes (in a certain sense) with _[_].

  inline-[] :
    (t : Term[ k ] n) →
    inline ξ (t [ σ ]) ≡ inline ξ t [ inline-Subst ξ σ ]
  inline-[] (var _) =
    refl
  inline-[] (defn _) =
    sym wk-wk₀-[]≡
  inline-[] Level =
    refl
  inline-[] zeroᵘ =
    refl
  inline-[] (sucᵘ t) =
    cong sucᵘ (inline-[] t)
  inline-[] (t supᵘ u) =
    cong₂ _supᵘ_ (inline-[] t) (inline-[] u)
  inline-[] (ωᵘ+ _) =
    refl
  inline-[] (level t) =
    cong level (inline-[] t)
  inline-[] (U l) =
    cong U (inline-[] l)
  inline-[] (Lift l A) =
    cong₂ Lift (inline-[] l) (inline-[] A)
  inline-[] (lift t) =
    cong lift (inline-[] t)
  inline-[] (lower t) =
    cong lower (inline-[] t)
  inline-[] Empty =
    refl
  inline-[] (emptyrec _ A t) =
    cong₂ (emptyrec _) (inline-[] A) (inline-[] t)
  inline-[] (Unit _) =
    refl
  inline-[] (star _) =
    refl
  inline-[] (unitrec _ _ A t u) =
    cong₃ (unitrec _ _) (inline-[⇑] 1 A) (inline-[] t) (inline-[] u)
  inline-[] (ΠΣ⟨ _ ⟩ _ , _ ▷ A ▹ B) =
    cong₂ (ΠΣ⟨ _ ⟩ _ , _ ▷_▹_) (inline-[] A) (inline-[⇑] 1 B)
  inline-[] (lam _ t) =
    cong (lam _) (inline-[⇑] 1 t)
  inline-[] (t ∘⟨ _ ⟩ u) =
    cong₂ (_∘⟨ _ ⟩_) (inline-[] t) (inline-[] u)
  inline-[] (prod _ _ t u) =
    cong₂ (prod _ _) (inline-[] t) (inline-[] u)
  inline-[] (fst _ t) =
    cong (fst _) (inline-[] t)
  inline-[] (snd _ t) =
    cong (snd _) (inline-[] t)
  inline-[] (prodrec _ _ _ A t u) =
    cong₃ (prodrec _ _ _) (inline-[⇑] 1 A) (inline-[] t)
      (inline-[⇑] 2 u)
  inline-[] ℕ =
    refl
  inline-[] zero =
    refl
  inline-[] (suc t) =
    cong suc (inline-[] t)
  inline-[] (natrec _ _ _ A t u v) =
    cong₄ (natrec _ _ _) (inline-[⇑] 1 A) (inline-[] t) (inline-[⇑] 2 u)
      (inline-[] v)
  inline-[] (Id A t u) =
    cong₃ Id (inline-[] A) (inline-[] t) (inline-[] u)
  inline-[] rfl =
    refl
  inline-[] (J _ _ A t B u v w) =
    cong₆ (J _ _) (inline-[] A) (inline-[] t) (inline-[⇑] 2 B)
      (inline-[] u) (inline-[] v) (inline-[] w)
  inline-[] (K _ A t B u v) =
    cong₅ (K _) (inline-[] A) (inline-[] t) (inline-[⇑] 1 B)
      (inline-[] u) (inline-[] v)
  inline-[] ([]-cong _ l A t u v) =
    cong₅ ([]-cong _) (inline-[] l) (inline-[] A) (inline-[] t)
      (inline-[] u) (inline-[] v)

  -- A variant of inline-[].

  inline-[⇑] :
    ∀ m (t : Term[ k ] (m + n)) →
    inline ξ (t [ σ ⇑[ m ] ]) ≡
    inline ξ t [ inline-Subst ξ σ ⇑[ m ] ]
  inline-[⇑] {ξ} {σ} m t =
    inline ξ (t [ σ ⇑[ m ] ])                 ≡⟨ inline-[] t ⟩
    inline ξ t [ inline-Subst ξ (σ ⇑[ m ]) ]  ≡⟨ substVar-to-subst (inline-Subst-⇑[] m) (inline _ t) ⟩
    inline ξ t [ inline-Subst ξ σ ⇑[ m ] ]    ∎

opaque

  -- A variant of inline-[].

  inline-[]₀ :
    (t : Term[ k ] (1+ n)) →
    inline ξ (t [ u ]₀) ≡ inline ξ t [ inline ξ u ]₀
  inline-[]₀ {ξ} {u} t =
    inline ξ (t [ u ]₀)                        ≡⟨ inline-[] t ⟩
    inline ξ t [ inline-Subst ξ (sgSubst u) ]  ≡⟨ substVar-to-subst inline-Subst-sgSubst (inline _ t) ⟩
    inline ξ t [ inline ξ u ]₀                 ∎

opaque

  -- A variant of inline-[].

  inline-[]₁₀ :
    (t : Term[ k ] (2+ n)) →
    inline ξ (t [ u , v ]₁₀) ≡
    inline ξ t [ inline ξ u , inline ξ v ]₁₀
  inline-[]₁₀ {ξ} {u} {v} t =
    inline ξ (t [ u , v ]₁₀)                                 ≡⟨ inline-[] t ⟩
    inline ξ t [ inline-Subst ξ (consSubst (sgSubst u) v) ]  ≡⟨ (flip substVar-to-subst (inline _ t) λ x →
                                                                 trans (inline-Subst-consSubst x) $
                                                                 consSubst-cong refl inline-Subst-sgSubst x) ⟩
    inline ξ t [ inline ξ u , inline ξ v ]₁₀                 ∎

opaque

  -- A variant of inline-[].

  inline-[][]↑ :
    (t : Term[ k ] (1+ m)) →
    inline ξ (t [ n ][ u ]↑) ≡ inline ξ t [ n ][ inline ξ u ]↑
  inline-[][]↑ {ξ} {n} {u} t =
    inline ξ (t [ n ][ u ]↑)                                         ≡⟨ inline-[] t ⟩
    inline ξ t [ inline-Subst ξ (consSubst (wkSubst n idSubst) u) ]  ≡⟨ (flip substVar-to-subst (inline _ t) λ x →
                                                                         trans (inline-Subst-consSubst x) $
                                                                         flip (consSubst-cong refl) x $ λ x →
                                                                         trans (inline-Subst-wkSubst n x) $
                                                                         wkSubst-cong inline-Subst-idSubst x) ⟩
    inline ξ t [ n ][ inline ξ u ]↑                                  ∎

opaque
  unfolding inline-Nat

  -- If α is in scope with respect to ξ, then inline-Nat ξ α is equal
  -- to an application of inline-< ξ.

  <-inline-Nat :
    {ξ : DExt (Term 0) n m}
    {m≤α : m ≤ α} {α<n : α <′ n} →
    inline-Nat ξ α ≡ inline-< ξ m≤α α<n
  <-inline-Nat {n} {m} {α} {ξ} {m≤α} {α<n} with m ≤? α
  … | no m≰α = ⊥-elim (m≰α m≤α)
  … | yes _  with α <′? n
  …   | no α≮n = ⊥-elim (α≮n α<n)
  …   | yes _  =
    cong₂ (inline-< ξ) ≤-propositional <′-propositional

opaque
  unfolding inline

  -- Inlining does not affect level literals.

  inline-Level-literal :
    Level-literal t → inline ξ t ≡ t
  inline-Level-literal zeroᵘ        = PE.refl
  inline-Level-literal (sucᵘ t-lit) =
    cong sucᵘ (inline-Level-literal t-lit)
  inline-Level-literal ωᵘ+ =
    refl
  inline-Level-literal (level t-lit) =
    cong level (inline-Level-literal t-lit)

opaque

  -- If t is a level literal, then inline ξ t is also a level literal.

  Level-literal-inline :
    Level-literal t → Level-literal (inline ξ t)
  Level-literal-inline t-lit =
    PE.subst Level-literal (PE.sym $ inline-Level-literal t-lit) t-lit

------------------------------------------------------------------------
-- Properties related to inlining and glassification

opaque
 unfolding inline glassifyᵉ
 mutual

  -- The result of inline-< is not affected by glassification.

  inline-<-glassifyᵉ :
    (ξ : DExt (Term 0) n m) (m≤α : m ≤ α) (α<n : α <′ n) →
    inline-< (glassifyᵉ ξ) m≤α α<n ≡ inline-< ξ m≤α α<n
  inline-<-glassifyᵉ idᵉ m≤α α<n =
    ⊥-elim (n≮n _ (≤-trans (<′⇒< α<n) m≤α))
  inline-<-glassifyᵉ (step _ _ _ t) _ (≤′-reflexive _) =
    inline-glassifyᵉ t
  inline-<-glassifyᵉ (step ξ _ _ _) m≤α (≤′-step α<n) =
    inline-<-glassifyᵉ ξ m≤α α<n

  -- The result of inline-Nat is not affected by glassification.

  inline-Nat-glassifyᵉ :
    (ξ : DExt (Term 0) n m) →
    inline-Nat (glassifyᵉ ξ) α ≡ inline-Nat ξ α
  inline-Nat-glassifyᵉ {n} {m} {α} ξ with m ≤? α
  … | no _    = refl
  … | yes m≤α with α <′? n
  …   | no _    = refl
  …   | yes α<n = inline-<-glassifyᵉ ξ m≤α α<n

  -- The result of inline is not affected by glassification.

  inline-glassifyᵉ :
    (t : Term[ k ] n) → inline (glassifyᵉ ξ) t ≡ inline ξ t
  inline-glassifyᵉ (var _) =
    refl
  inline-glassifyᵉ {ξ} (defn _) =
    cong (wk _) (inline-Nat-glassifyᵉ ξ)
  inline-glassifyᵉ Level =
    refl
  inline-glassifyᵉ zeroᵘ =
    refl
  inline-glassifyᵉ (sucᵘ t) =
    cong sucᵘ (inline-glassifyᵉ t)
  inline-glassifyᵉ (t supᵘ u) =
    cong₂ _supᵘ_ (inline-glassifyᵉ t) (inline-glassifyᵉ u)
  inline-glassifyᵉ (ωᵘ+ _) =
    refl
  inline-glassifyᵉ (level t) =
    cong level (inline-glassifyᵉ t)
  inline-glassifyᵉ (U l) =
    cong U (inline-glassifyᵉ l)
  inline-glassifyᵉ (Lift l A) =
    cong₂ Lift (inline-glassifyᵉ l) (inline-glassifyᵉ A)
  inline-glassifyᵉ (lift t) =
    cong lift (inline-glassifyᵉ t)
  inline-glassifyᵉ (lower t) =
    cong lower (inline-glassifyᵉ t)
  inline-glassifyᵉ Empty =
    refl
  inline-glassifyᵉ (emptyrec p A t) =
    cong₂ (emptyrec _) (inline-glassifyᵉ A) (inline-glassifyᵉ t)
  inline-glassifyᵉ (Unit _) =
    refl
  inline-glassifyᵉ (star _) =
    refl
  inline-glassifyᵉ (unitrec _ _ A t u) =
    cong₃ (unitrec _ _) (inline-glassifyᵉ A) (inline-glassifyᵉ t)
      (inline-glassifyᵉ u)
  inline-glassifyᵉ (ΠΣ⟨ _ ⟩ _ , _ ▷ A ▹ B) =
    cong₂ (ΠΣ⟨ _ ⟩ _ , _ ▷_▹_) (inline-glassifyᵉ A) (inline-glassifyᵉ B)
  inline-glassifyᵉ (lam p t) =
    cong (lam _) (inline-glassifyᵉ t)
  inline-glassifyᵉ (t ∘⟨ p ⟩ u) =
    cong₂ (_∘⟨ _ ⟩_) (inline-glassifyᵉ t) (inline-glassifyᵉ u)
  inline-glassifyᵉ (prod s p t u) =
    cong₂ (prod _ _) (inline-glassifyᵉ t) (inline-glassifyᵉ u)
  inline-glassifyᵉ (fst p t) =
    cong (fst _) (inline-glassifyᵉ t)
  inline-glassifyᵉ (snd p t) =
    cong (snd _) (inline-glassifyᵉ t)
  inline-glassifyᵉ (prodrec r p q A t u) =
    cong₃ (prodrec _ _ _) (inline-glassifyᵉ A) (inline-glassifyᵉ t)
      (inline-glassifyᵉ u)
  inline-glassifyᵉ ℕ =
    refl
  inline-glassifyᵉ zero =
    refl
  inline-glassifyᵉ (suc t) =
    cong suc (inline-glassifyᵉ t)
  inline-glassifyᵉ (natrec p q r A t u v) =
    cong₄ (natrec _ _ _) (inline-glassifyᵉ A) (inline-glassifyᵉ t)
      (inline-glassifyᵉ u) (inline-glassifyᵉ v)
  inline-glassifyᵉ (Id A t u) =
    cong₃ Id (inline-glassifyᵉ A) (inline-glassifyᵉ t)
      (inline-glassifyᵉ u)
  inline-glassifyᵉ rfl =
    refl
  inline-glassifyᵉ (J p q A t B u v w) =
    cong₆ (J _ _) (inline-glassifyᵉ A) (inline-glassifyᵉ t)
      (inline-glassifyᵉ B) (inline-glassifyᵉ u) (inline-glassifyᵉ v)
      (inline-glassifyᵉ w)
  inline-glassifyᵉ (K p A t B u v) =
    cong₅ (K _) (inline-glassifyᵉ A) (inline-glassifyᵉ t)
      (inline-glassifyᵉ B) (inline-glassifyᵉ u) (inline-glassifyᵉ v)
  inline-glassifyᵉ ([]-cong _ l A t u v) =
    cong₅ ([]-cong _) (inline-glassifyᵉ l) (inline-glassifyᵉ A)
      (inline-glassifyᵉ t) (inline-glassifyᵉ u) (inline-glassifyᵉ v)

opaque
  unfolding inlineᵈ

  -- A variant of inline-glassifyᵉ.

  inlineᵈ-glassify : inlineᵈ (glassify ∇) t ≡ inlineᵈ ∇ t
  inlineᵈ-glassify {∇} {t} =
    inline (as-DExt (glassify ∇)) t   ≡˘⟨ cong (flip inline t) glassifyᵉ-as-DExt ⟩
    inline (glassifyᵉ (as-DExt ∇)) t  ≡⟨ inline-glassifyᵉ t ⟩
    inline (as-DExt ∇) t              ∎

opaque
  unfolding inline-Con

  -- The result of inline-Con is not affected by glassification.

  inline-Con-glassifyᵉ :
    (Γ : Con Term n) → inline-Con (glassifyᵉ ξ) Γ ≡ inline-Con ξ Γ
  inline-Con-glassifyᵉ ε       = refl
  inline-Con-glassifyᵉ (Γ ∙ A) =
    cong₂ _∙_ (inline-Con-glassifyᵉ _) (inline-glassifyᵉ A)

opaque
  unfolding inline-Conᵈ

  -- A variant of inline-Con-glassifyᵉ.

  inline-Conᵈ-glassify : inline-Conᵈ (glassify ∇) Γ ≡ inline-Conᵈ ∇ Γ
  inline-Conᵈ-glassify {∇} {Γ} =
    inline-Con (as-DExt (glassify ∇)) Γ   ≡˘⟨ cong (flip inline-Con _) glassifyᵉ-as-DExt ⟩
    inline-Con (glassifyᵉ (as-DExt ∇)) Γ  ≡⟨ inline-Con-glassifyᵉ _ ⟩
    inline-Con (as-DExt ∇) Γ              ∎

------------------------------------------------------------------------
-- Properties related to ⟨_≔_⟩ and ⟨_≔_⟩↑

opaque

  -- A lemma relating ⟨_≔_⟩ and ⟨_≔_⟩↑.

  ⟨≔⟩≡⟨≔⟩↑ :
    (y : Fin n) →
    wk (step-at x) (⟨ x ≔ t ⟩ y) ≡ ⟨ x ≔ wk (step-at′ x) t ⟩↑ y
  ⟨≔⟩≡⟨≔⟩↑ {x = x0} x0 =
    refl
  ⟨≔⟩≡⟨≔⟩↑ {x = x0} (_ +1) =
    refl
  ⟨≔⟩≡⟨≔⟩↑ {x = _+1 {n = 0}    ()}
  ⟨≔⟩≡⟨≔⟩↑ {x = _+1 {n = 1+ _} _}  x0 =
    refl
  ⟨≔⟩≡⟨≔⟩↑ {x = _+1 {n = 1+ _} x} {t} (y +1) =
    wk (lift (step-at x)) (wk1 (⟨ x ≔ t ⟩ y))  ≡˘⟨ wk1-wk≡lift-wk1 _ _ ⟩
    wk1 (wk (step-at x) (⟨ x ≔ t ⟩ y))         ≡⟨ cong wk1 $ ⟨≔⟩≡⟨≔⟩↑ y ⟩
    wk1 (⟨ x ≔ wk (step-at′ x) t ⟩↑ y)         ∎

------------------------------------------------------------------------
-- A view for variables

-- A view of terms as variables or anything else.

data Is-var? {n} : Term n → Set a where
  var     : ∀ x → Is-var? (var x)
  not-var : (∀ {x} → ¬ t ≡ var x) → Is-var? t

opaque

  -- The Is-var? view is "decidable".

  is-var? : (t : Term n) → Is-var? t
  is-var? (var x)                 = var x
  is-var? (defn _)                = not-var (λ ())
  is-var? Level                   = not-var (λ ())
  is-var? zeroᵘ                   = not-var (λ ())
  is-var? (sucᵘ _)                = not-var (λ ())
  is-var? (_ supᵘ _)              = not-var (λ ())
  is-var? (U _)                   = not-var (λ ())
  is-var? (Lift _ _)              = not-var (λ ())
  is-var? (lift _)                = not-var (λ ())
  is-var? (lower _)               = not-var (λ ())
  is-var? Empty                   = not-var (λ ())
  is-var? (emptyrec _ _ _)        = not-var (λ ())
  is-var? (Unit _)                = not-var (λ ())
  is-var? (star _)                = not-var (λ ())
  is-var? (unitrec _ _ _ _ _)     = not-var (λ ())
  is-var? (ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _) = not-var (λ ())
  is-var? (lam _ _)               = not-var (λ ())
  is-var? (_ ∘⟨ _ ⟩ _)            = not-var (λ ())
  is-var? (prod _ _ _ _)          = not-var (λ ())
  is-var? (fst _ _)               = not-var (λ ())
  is-var? (snd _ _)               = not-var (λ ())
  is-var? (prodrec _ _ _ _ _ _)   = not-var (λ ())
  is-var? ℕ                       = not-var (λ ())
  is-var? zero                    = not-var (λ ())
  is-var? (suc _)                 = not-var (λ ())
  is-var? (natrec _ _ _ _ _ _ _)  = not-var (λ ())
  is-var? (Id _ _ _)              = not-var (λ ())
  is-var? rfl                     = not-var (λ ())
  is-var? (J _ _ _ _ _ _ _ _)     = not-var (λ ())
  is-var? (K _ _ _ _ _ _)         = not-var (λ ())
  is-var? ([]-cong _ _ _ _ _ _)   = not-var (λ ())

------------------------------------------------------------------------
-- Some lemmas related to DCon/DExt

opaque
  unfolding _ᵈ•_

  -- The function _ᵈ•_ is injective for contexts/context extensions of
  -- equal length.

  ᵈ•-PE-injectivity :
    {∇₁ : DCon (Term 0) m} {ξ₁ : DExt (Term 0) n m}
    {∇₂ : DCon (Term 0) m} {ξ₂ : DExt (Term 0) n m} →
    ∇₁ ᵈ• ξ₁ ≡ ∇₂ ᵈ• ξ₂ →
    ∇₁ ≡ ∇₂ × ξ₁ ≡ ξ₂
  ᵈ•-PE-injectivity {ξ₁ = idᵉ} {∇₂} {ξ₂ = id eq} refl =
    subst (λ eq → ∇₂ ᵈ• id eq ≡ ∇₂ × idᵉ ≡ id eq) Nat-set
      (refl , refl)
  ᵈ•-PE-injectivity {ξ₁ = idᵉ} {ξ₂ = step ξ₂ _ _ _} _ =
    ⊥-elim $ n≮n _ (DExt→≤ ξ₂)
  ᵈ•-PE-injectivity {ξ₁ = step ξ₁ _ _ _} {ξ₂ = idᵉ} _ =
    ⊥-elim $ n≮n _ (DExt→≤ ξ₁)
  ᵈ•-PE-injectivity {ξ₁ = step _ _ _ _} {ξ₂ = step _ _ _ _} eq =
    case ∙-PE-injectivity eq of λ {
      (eq , refl , refl , refl) →
    Σ.map idᶠ (cong (λ ξ → step ξ _ _ _)) (ᵈ•-PE-injectivity eq) }

opaque

  -- The function map-Cons idᶠ is pointwise equal to the identity
  -- function.

  map-Cons-id : map-Cons idᶠ Δ ≡ Δ
  map-Cons-id = cong₂ _»_ map-DCon-id map-Con-id

opaque

  -- The function map-Cons preserves pointwise equality.

  map-Cons-cong :
    {f g : ∀ {n} → Term n → Term n} →
    (∀ {n} (x : Term n) → f x ≡ g x) → map-Cons f Δ ≡ map-Cons g Δ
  map-Cons-cong f≡g = cong₂ _»_ (map-DCon-cong f≡g) (map-Con-cong f≡g)

------------------------------------------------------------------------
-- Some lemmas related to Level-literal

opaque

  -- It is decidable whether two level literals are equal.

  infix 4 _≟L_

  _≟L_ :
    Level-literal t₁ → Level-literal t₂ →
    Dec (t₁ ≡ t₂)
  zeroᵘ   ≟L zeroᵘ   = yes refl
  zeroᵘ   ≟L sucᵘ _  = no (λ ())
  sucᵘ _  ≟L zeroᵘ   = no (λ ())
  sucᵘ t₁ ≟L sucᵘ t₂ =
    Dec-map (cong sucᵘ , sucᵘ-PE-injectivity) (t₁ ≟L t₂)
  ωᵘ+ {m = m₁} ≟L ωᵘ+ {m = m₂} =
    Dec-map (cong ωᵘ+ , ωᵘ+-PE-injectivity) (m₁ Nat.≟ m₂)
  ωᵘ+      ≟L level _  = no (λ ())
  level _  ≟L ωᵘ+      = no (λ ())
  level t₁ ≟L level t₂ =
    Dec-map (cong level , level-PE-injectivity) (t₁ ≟L t₂)

opaque

  -- Level-literal is propositional.

  Level-literal-propositional : Is-proposition (Level-literal t)
  Level-literal-propositional {x = zeroᵘ}  {y = zeroᵘ}  = refl
  Level-literal-propositional {x = sucᵘ _} {y = sucᵘ _} =
    cong sucᵘ Level-literal-propositional
  Level-literal-propositional {x = ωᵘ+}     {y = ωᵘ+}     = refl
  Level-literal-propositional {x = level _} {y = level _} =
    cong level Level-literal-propositional

opaque
  unfolding size-of-Level ↓ᵘ_

  -- If t-lit : Level-literal t for some t : Term n, then
  -- ↓ᵘ (size-of-Level t-lit) is equal to t.

  ↓ᵘ-size-of-Level :
    {t : Term n} {t-lit : Level-literal t} →
    ↓ᵘ (size-of-Level t-lit) ≡ t
  ↓ᵘ-size-of-Level {t-lit = zeroᵘ}  = refl
  ↓ᵘ-size-of-Level {t-lit = sucᵘ t} =
    cong sucᵘ (↓ᵘ-size-of-Level {t-lit = t})

opaque
  unfolding ↓ᵘ_

  -- An alternative characterisation of Level-literal for terms (not
  -- levels).

  Level-literal⇔ :
    {t : Term n} →
    Level-literal t ⇔ ∃ λ n → t ≡ ↓ᵘ n
  Level-literal⇔ =
    (λ t-lit → size-of-Level t-lit , sym (↓ᵘ-size-of-Level)) , from
    where
    from : (∃ λ n → t ≡ ↓ᵘ n) → Level-literal t
    from (0    , refl) = zeroᵘ
    from (1+ n , refl) = sucᵘ (from (n , refl))

opaque

  -- The term ↓ᵘ n is a level literal.

  Level-literal-↓ᵘ : Level-literal {n = n} (↓ᵘ m)
  Level-literal-↓ᵘ = Level-literal⇔ .proj₂ (_ , refl)

opaque

  -- The level level t is a level literal if and only if t is.

  Level-literal-level-⇔ : Level-literal (level t) ⇔ Level-literal t
  Level-literal-level-⇔ =
    (λ { (level t-lit) → t-lit }) , level

opaque
  unfolding Level-literal→Universe-level

  -- The result of Level-literal→Universe-level is necessarily
  -- strictly less than ωᵘ·2.

  Level-literal→Universe-level<ᵘωᵘ·2 :
    {l-lit : Level-literal l} →
    Level-literal→Universe-level l-lit <ᵘ ωᵘ·2
  Level-literal→Universe-level<ᵘωᵘ·2 {l-lit = ωᵘ+}     = ωᵘ+<ᵘωᵘ·2
  Level-literal→Universe-level<ᵘωᵘ·2 {l-lit = level _} = 0ᵘ+<ᵘωᵘ·2

------------------------------------------------------------------------
-- Some lemmas related to 1ᵘ+, 1ᵘ+ⁿ and ↓ᵘ_

opaque

  -- Weakening commutes with 1ᵘ+.

  wk-1ᵘ+ : {l : Term[ k ] n} → wk ρ (1ᵘ+ l) ≡ 1ᵘ+ (wk ρ l)
  wk-1ᵘ+ {k = tm}                = refl
  wk-1ᵘ+ {k = lvl} {l = ωᵘ+ _}   = refl
  wk-1ᵘ+ {k = lvl} {l = level _} = refl

opaque

  -- Substitution commutes with 1ᵘ+.

  1ᵘ+-[] : (l : Term[ k ] n) → 1ᵘ+ l [ σ ] ≡ 1ᵘ+ (l [ σ ])
  1ᵘ+-[] {k = tm}  _         = refl
  1ᵘ+-[] {k = lvl} (ωᵘ+ _)   = refl
  1ᵘ+-[] {k = lvl} (level _) = refl

opaque

  -- A substitution lemma for 1ᵘ+ⁿ.

  1ᵘ+ⁿ-[] : ∀ n → 1ᵘ+ⁿ n t [ σ ] ≡ 1ᵘ+ⁿ n (t [ σ ])
  1ᵘ+ⁿ-[]         0      = refl
  1ᵘ+ⁿ-[] {t} {σ} (1+ n) =
    1ᵘ+ (1ᵘ+ⁿ n t) [ σ ]    ≡⟨ 1ᵘ+-[] (1ᵘ+ⁿ n t) ⟩
    1ᵘ+ (1ᵘ+ⁿ n t [ σ ])    ≡⟨ cong 1ᵘ+ (1ᵘ+ⁿ-[] n) ⟩
    1ᵘ+ (1ᵘ+ⁿ n (t [ σ ]))  ∎

opaque

  -- A weakening lemma for 1ᵘ+ⁿ.

  wk-1ᵘ+ⁿ : ∀ n → wk ρ (1ᵘ+ⁿ n t) ≡ 1ᵘ+ⁿ n (wk ρ t)
  wk-1ᵘ+ⁿ {ρ} {t} n =
    wk ρ (1ᵘ+ⁿ n t)           ≡⟨ wk≡subst _ _ ⟩
    1ᵘ+ⁿ n t [ toSubst ρ ]    ≡⟨ 1ᵘ+ⁿ-[] n ⟩
    1ᵘ+ⁿ n (t [ toSubst ρ ])  ≡˘⟨ cong (1ᵘ+ⁿ n) $ wk≡subst _ _ ⟩
    1ᵘ+ⁿ n (wk ρ t)           ∎

opaque
  unfolding ↓ᵘ_

  -- A substitution lemma for ↓ᵘ_.

  ↓ᵘ-[] : (↓ᵘ n) [ σ ] ≡ ↓ᵘ n
  ↓ᵘ-[] {n} = 1ᵘ+ⁿ-[] n

opaque

  -- A weakening lemma for ↓ᵘ_.

  wk-↓ᵘ : wk ρ (↓ᵘ n) ≡ ↓ᵘ n
  wk-↓ᵘ {ρ} {n} =
    wk ρ (↓ᵘ n)           ≡⟨ wk≡subst _ _ ⟩
    (↓ᵘ n) [ toSubst ρ ]  ≡⟨ ↓ᵘ-[] ⟩
    ↓ᵘ n                  ∎

opaque

  -- 1ᵘ+ⁿ n commutes with level.

  1ᵘ+ⁿ-level≡ : ∀ n → 1ᵘ+ⁿ n (level t) ≡ level (1ᵘ+ⁿ n t)
  1ᵘ+ⁿ-level≡ 0      = refl
  1ᵘ+ⁿ-level≡ (1+ n) = cong 1ᵘ+ (1ᵘ+ⁿ-level≡ n)

opaque

  -- The level 1ᵘ+ l is a level literal if and only if l is.

  Level-literal-1ᵘ+-⇔ :
    {l : Term[ k ] n} →
    Level-literal (1ᵘ+ l) ⇔ Level-literal l
  Level-literal-1ᵘ+-⇔ {k = tm} =
    (λ { (sucᵘ t) → t }) , sucᵘ
  Level-literal-1ᵘ+-⇔ {l = ωᵘ+ _} =
    (λ _ → ωᵘ+) , (λ _ → ωᵘ+)
  Level-literal-1ᵘ+-⇔ {l = level _} =
    (λ { (level (sucᵘ t)) → level t }) ,
    (λ { (level t) → level (sucᵘ t) })

opaque

  -- The level 1ᵘ+ l is infinite if and only if l is.

  Infinite-1ᵘ+-⇔ : Infinite (1ᵘ+ l) ⇔ Infinite l
  Infinite-1ᵘ+-⇔ = to _ , (λ { ωᵘ+ → ωᵘ+ })
    where
    to : (l : Term[ k ] n) → Infinite (1ᵘ+ l) → Infinite l
    to {k = tm} _         ()
    to          (ωᵘ+ _)   _  = ωᵘ+
    to          (level _) ()

opaque
  unfolding inline

  -- Inlining commutes with 1ᵘ+.

  inline-1ᵘ+ : (l : Lvl n) → inline ξ (1ᵘ+ l) ≡ 1ᵘ+ (inline ξ l)
  inline-1ᵘ+ (ωᵘ+ _)   = refl
  inline-1ᵘ+ (level _) = refl

------------------------------------------------------------------------
-- More lemmas related to Level-literal

opaque

  -- If t is a level literal, then t [ σ₁ ] ≡ t [ σ₂ ] holds.

  Level-literal→[]≡[] :
    {t : Term[ k ] n} → Level-literal t → t [ σ₁ ] ≡ t [ σ₂ ]
  Level-literal→[]≡[] {k = tm} {σ₁} {σ₂} {t} t-lit =
    let n , eq = Level-literal⇔ .proj₁ t-lit in
    t [ σ₁ ]       ≡⟨ cong _[ _ ] eq ⟩
    (↓ᵘ n) [ σ₁ ]  ≡⟨ ↓ᵘ-[] ⟩
    ↓ᵘ n           ≡˘⟨ ↓ᵘ-[] ⟩
    (↓ᵘ n) [ σ₂ ]  ≡˘⟨ cong _[ _ ] eq ⟩
    t [ σ₂ ]       ∎
  Level-literal→[]≡[] {k = lvl} ωᵘ+           = refl
  Level-literal→[]≡[] {k = lvl} (level t-lit) =
    cong level (Level-literal→[]≡[] t-lit)

opaque

  -- If t is a level literal, then t [ σ ] is also a level literal.

  Level-literal-[] :
    {t : Term[ k ] n} → Level-literal t → Level-literal (t [ σ ])
  Level-literal-[] {k = tm} {σ} {t} =
    Level-literal t           ⇔⟨ Level-literal⇔ ⟩→
    (∃ λ n → t ≡ ↓ᵘ n)        →⟨ Σ.map idᶠ (λ { refl → ↓ᵘ-[] }) ⟩
    (∃ λ n → t [ σ ] ≡ ↓ᵘ n)  ⇔˘⟨ Level-literal⇔ ⟩→
    Level-literal (t [ σ ])   □
  Level-literal-[] {k = lvl} ωᵘ+           = ωᵘ+
  Level-literal-[] {k = lvl} (level t-lit) =
    level (Level-literal-[] t-lit)

opaque

  -- The term t is a level literal if and only if wk ρ t is.

  wk-Level-literal : Level-literal t ⇔ Level-literal (wk ρ t)
  wk-Level-literal = to , flip from refl
    where
    to : Level-literal t → Level-literal (wk ρ t)
    to = subst Level-literal (sym $ wk≡subst _ _) ∘→ Level-literal-[]

    from : Level-literal u → wk ρ t ≡ u → Level-literal t
    from zeroᵘ eq =
      case wk-zeroᵘ eq of λ {
        refl →
      zeroᵘ }
    from (sucᵘ u-lit) eq =
      case wk-sucᵘ eq of λ {
        (_ , refl , refl) →
      sucᵘ (from u-lit refl) }
    from ωᵘ+ eq rewrite wk-ωᵘ+ eq =
      ωᵘ+
    from (level u-lit) eq with wk-level eq
    … | _ , refl , eq =
      level (from u-lit eq)

opaque
  unfolding _supᵘₗ′_

  -- A "computation rule" for _supᵘₗ′_.

  supᵘₗ′≡↓ᵘ⊔ :
    (t₁-lit : Level-literal t₁) (t₂-lit : Level-literal t₂) →
    t₁ supᵘₗ′ t₂ ≡
    ↓ᵘ (size-of-Level t₁-lit ⊔ size-of-Level t₂-lit)
  supᵘₗ′≡↓ᵘ⊔ {t₁} {t₂} t₁-lit t₂-lit
    with Level-literal? t₁ ×-dec Level-literal? t₂
  … | yes _ =
    cong₂ (λ t₁ t₂ → ↓ᵘ (size-of-Level t₁ ⊔ size-of-Level t₂))
      Level-literal-propositional Level-literal-propositional
  … | no not-both = ⊥-elim (not-both (t₁-lit , t₂-lit))

opaque
  unfolding _supᵘₗ′_

  -- Another "computation rule" for _supᵘₗ′_.

  supᵘₗ′≡supᵘ :
    ¬ (Level-literal t₁ × Level-literal t₂) →
    t₁ supᵘₗ′ t₂ ≡ t₁ supᵘ t₂
  supᵘₗ′≡supᵘ {t₁} {t₂} not-both
    with Level-literal? t₁ ×-dec Level-literal? t₂
  … | yes (t₁-lit , t₂-lit) = ⊥-elim (not-both (t₁-lit , t₂-lit))
  … | no _                  = refl

opaque
  unfolding _supᵘₗ′_

  -- The level t₁ supᵘₗ′ t₂ is a level literal if and only if t₁ and
  -- t₂ are.

  Level-literal-supᵘₗ′⇔ :
    Level-literal (t₁ supᵘₗ′ t₂) ⇔
    (Level-literal t₁ × Level-literal t₂)
  Level-literal-supᵘₗ′⇔ =
    to ,
    (λ (t₁-lit , t₂-lit) →
       subst Level-literal (sym $ supᵘₗ′≡↓ᵘ⊔ t₁-lit t₂-lit)
         Level-literal-↓ᵘ)
    where
    to :
      Level-literal (t₁ supᵘₗ′ t₂) →
      Level-literal t₁ × Level-literal t₂
    to {t₁} {t₂} supᵘₗ′-lit
      with Level-literal? t₁ ×-dec Level-literal? t₂
    … | yes (t₁-lit , t₂-lit) = t₁-lit , t₂-lit
    … | no _                  = case supᵘₗ′-lit of λ ()

opaque

  -- Inlining commutes with _supᵘₗ′_ for terms that are level
  -- literals.

  inline-supᵘₗ′ :
    Level-literal t₁ → Level-literal t₂ →
    inline ξ (t₁ supᵘₗ′ t₂) PE.≡ inline ξ t₁ supᵘₗ′ inline ξ t₂
  inline-supᵘₗ′ {t₁} {t₂} {ξ} t₁-lit t₂-lit =
    inline ξ (t₁ supᵘₗ′ t₂)         ≡⟨ inline-Level-literal (Level-literal-supᵘₗ′⇔ .proj₂ (t₁-lit , t₂-lit)) ⟩
    t₁ supᵘₗ′ t₂                    ≡˘⟨ cong₂ _supᵘₗ′_ (inline-Level-literal t₁-lit) (inline-Level-literal t₂-lit) ⟩
    inline ξ t₁ supᵘₗ′ inline ξ t₂  ∎

opaque
  unfolding Level-literal⇔ size-of-Level

  -- A lemma related to size-of-Level.

  size-of-Level-Level-literal⇔ :
    {eq : t ≡ ↓ᵘ n} →
    size-of-Level (Level-literal⇔ .proj₂ (n , eq)) ≡ n
  size-of-Level-Level-literal⇔ {n = 0}    {eq = refl} = refl
  size-of-Level-Level-literal⇔ {n = 1+ _} {eq = refl} =
    cong 1+ size-of-Level-Level-literal⇔

opaque
  unfolding Level-literal-↓ᵘ

  -- A lemma relating size-of-Level and Level-literal-↓ᵘ.

  size-of-Level-Level-literal-↓ᵘ :
    size-of-Level (Level-literal-↓ᵘ {n = n} {m = m}) ≡ m
  size-of-Level-Level-literal-↓ᵘ = size-of-Level-Level-literal⇔

opaque
  unfolding Level-literal→Universe-level

  -- A simplification lemma for Level-literal→Universe-level.

  Level-literal→Universe-level-ωᵘ+ :
    {lit : Level-literal {n = n} (ωᵘ+ m)} →
    Level-literal→Universe-level lit ≡ ωᵘ+ m
  Level-literal→Universe-level-ωᵘ+ {lit = ωᵘ+} = refl

opaque
  unfolding Level-literal→Universe-level Level-literal-level-⇔

  -- A lemma relating Level-literal→Universe-level and size-of-Level.

  Level-literal→Universe-level-level :
    {lit : Level-literal (level t)} →
    Level-literal→Universe-level lit ≡
    0ᵘ+ (size-of-Level (Level-literal-level-⇔ .proj₁ lit))
  Level-literal→Universe-level-level {lit = level _} = refl

opaque
  unfolding Level-literal-[] Level-literal⇔

  -- The function size-of-Level is not affected by applications of
  -- Level-literal-[].

  size-of-Level-Level-literal-[] :
    {t-lit : Level-literal t} →
    size-of-Level (Level-literal-[] {σ = σ} t-lit) ≡
    size-of-Level t-lit
  size-of-Level-Level-literal-[] = size-of-Level-Level-literal⇔

opaque
  unfolding Level-literal→Universe-level Level-literal-[]

  -- The function Level-literal→Universe-level is not affected by
  -- applications of Level-literal-[].

  Level-literal→Universe-level-Level-literal-[] :
    {l-lit : Level-literal l} →
    Level-literal→Universe-level (Level-literal-[] {σ = σ} l-lit) ≡
    Level-literal→Universe-level l-lit
  Level-literal→Universe-level-Level-literal-[] {l-lit = ωᵘ+} =
    refl
  Level-literal→Universe-level-Level-literal-[] {l-lit = level _} =
    cong 0ᵘ+ size-of-Level-Level-literal-[]

opaque

  -- The function size-of-Level is not affected by applications of
  -- subst Level-literal.

  size-of-Level-subst :
    {eq : t₁ ≡ t₂} {t₁-lit : Level-literal t₁} →
    size-of-Level (subst Level-literal eq t₁-lit) ≡
    size-of-Level t₁-lit
  size-of-Level-subst {eq = refl} = refl

opaque

  -- The function Level-literal→Universe-level is not affected by
  -- applications of subst Level-literal.

  Level-literal→Universe-level-subst :
    {eq : l₁ ≡ l₂} {l₁-lit : Level-literal l₁} →
    Level-literal→Universe-level (subst Level-literal eq l₁-lit) ≡
    Level-literal→Universe-level l₁-lit
  Level-literal→Universe-level-subst {eq = refl} = refl

opaque
  unfolding wk-Level-literal

  -- The function size-of-Level is not affected by applications of the
  -- forward direction of wk-Level-literal.

  size-of-Level-wk-Level-literal :
    {t-lit : Level-literal t} →
    size-of-Level (wk-Level-literal {ρ = ρ} .proj₁ t-lit) ≡
    size-of-Level t-lit
  size-of-Level-wk-Level-literal {t} {ρ} {t-lit} =
    size-of-Level
      (subst Level-literal (sym $ wk≡subst _ _) $
       Level-literal-[] t-lit)                     ≡⟨ size-of-Level-subst ⟩

    size-of-Level (Level-literal-[] t-lit)         ≡⟨ size-of-Level-Level-literal-[] ⟩

    size-of-Level t-lit                            ∎

opaque
  unfolding wk-Level-literal

  -- The function Level-literal→Universe-level is not affected by
  -- applications of the forward direction of wk-Level-literal.

  Level-literal→Universe-level-wk-Level-literal :
    {t-lit : Level-literal t} →
    Level-literal→Universe-level
      (wk-Level-literal {ρ = ρ} .proj₁ t-lit) ≡
    Level-literal→Universe-level t-lit
  Level-literal→Universe-level-wk-Level-literal {t} {ρ} {t-lit} =
    Level-literal→Universe-level
      (subst Level-literal (sym $ wk≡subst _ _) $
       Level-literal-[] t-lit)                             ≡⟨ Level-literal→Universe-level-subst ⟩

    Level-literal→Universe-level (Level-literal-[] t-lit)  ≡⟨ Level-literal→Universe-level-Level-literal-[] ⟩

    Level-literal→Universe-level t-lit                     ∎

opaque
  unfolding Level-literal-supᵘₗ′⇔

  -- A lemma relating size-of-Level, Level-literal-supᵘₗ′⇔ and _⊔_.

  size-of-Level-Level-literal-supᵘₗ′⇔ :
    {t₁-lit : Level-literal t₁}
    {t₂-lit : Level-literal t₂} →
    size-of-Level (Level-literal-supᵘₗ′⇔ .proj₂ (t₁-lit , t₂-lit)) ≡
    size-of-Level t₁-lit ⊔ size-of-Level t₂-lit
  size-of-Level-Level-literal-supᵘₗ′⇔ {t₁-lit} {t₂-lit} =
    size-of-Level
      (PE.subst Level-literal (PE.sym (supᵘₗ′≡↓ᵘ⊔ t₁-lit t₂-lit))
         Level-literal-↓ᵘ)                                         ≡⟨ size-of-Level-subst ⟩

    size-of-Level
      (Level-literal-↓ᵘ
         {m = size-of-Level t₁-lit ⊔ size-of-Level t₂-lit})        ≡⟨ size-of-Level-Level-literal-↓ᵘ ⟩

    size-of-Level t₁-lit ⊔ size-of-Level t₂-lit                    ∎

opaque

  -- A substitution lemma for _supᵘₗ′_.

  supᵘₗ′-[] :
    Level-literal t₁ → Level-literal t₂ →
    t₁ supᵘₗ′ t₂ [ σ ] ≡ (t₁ [ σ ]) supᵘₗ′ (t₂ [ σ ])
  supᵘₗ′-[] {t₁} {t₂} {σ} t₁-lit t₂-lit =
    t₁ supᵘₗ′ t₂ [ σ ]                                        ≡⟨ cong _[ _ ] $ supᵘₗ′≡↓ᵘ⊔ _ _ ⟩

    (↓ᵘ (size-of-Level t₁-lit ⊔ size-of-Level t₂-lit)) [ σ ]  ≡⟨ ↓ᵘ-[] ⟩

    ↓ᵘ (size-of-Level t₁-lit ⊔ size-of-Level t₂-lit)          ≡˘⟨ cong₂ (λ t₁ t₂ → ↓ᵘ (t₁ ⊔ t₂))
                                                                    size-of-Level-Level-literal-[]
                                                                    size-of-Level-Level-literal-[] ⟩
    ↓ᵘ
      (size-of-Level (Level-literal-[] t₁-lit) ⊔
       size-of-Level (Level-literal-[] t₂-lit))               ≡˘⟨ supᵘₗ′≡↓ᵘ⊔ _ _ ⟩

    (t₁ [ σ ]) supᵘₗ′ (t₂ [ σ ])                              ∎

opaque
  unfolding _supᵘₗ′_

  -- A weakening lemma for _supᵘₗ′_.

  wk-supᵘₗ′ : wk ρ (t₁ supᵘₗ′ t₂) ≡ wk ρ t₁ supᵘₗ′ wk ρ t₂
  wk-supᵘₗ′ {ρ} {t₁} {t₂}
    with Level-literal? t₁ ×-dec Level-literal? t₂
  … | yes (t₁-lit , t₂-lit) =
    wk ρ (↓ᵘ (size-of-Level t₁-lit ⊔ size-of-Level t₂-lit))  ≡˘⟨ cong (wk _) $ supᵘₗ′≡↓ᵘ⊔ _ _ ⟩
    wk ρ (t₁ supᵘₗ′ t₂)                                      ≡⟨ wk≡subst _ _ ⟩
    t₁ supᵘₗ′ t₂ [ toSubst ρ ]                               ≡⟨ supᵘₗ′-[] t₁-lit t₂-lit ⟩
    (t₁ [ toSubst ρ ]) supᵘₗ′ (t₂ [ toSubst ρ ])             ≡˘⟨ cong₂ _supᵘₗ′_ (wk≡subst _ _) (wk≡subst _ _) ⟩
    wk ρ t₁ supᵘₗ′ wk ρ t₂                                   ∎
  … | no not-both =
    wk ρ t₁ supᵘ   wk ρ t₂  ≡˘⟨ supᵘₗ′≡supᵘ (not-both ∘→ Σ.map (wk-Level-literal .proj₂) (wk-Level-literal .proj₂)) ⟩
    wk ρ t₁ supᵘₗ′ wk ρ t₂  ∎

------------------------------------------------------------------------
-- Some lemmas related to Infinite

opaque

  -- The level wk ρ l is infinite if and only if l is.

  Infinite-wk-⇔ : Infinite (wk ρ l) ⇔ Infinite l
  Infinite-wk-⇔ = flip to refl , (λ { ωᵘ+ → ωᵘ+ })
    where
    to : Infinite l′ → wk ρ l ≡ l′ → Infinite l
    to ωᵘ+ eq rewrite wk-ωᵘ+ eq = ωᵘ+

opaque

  -- The level l [ σ ] is infinite if and only if l is.

  Infinite-[]-⇔ : Infinite (l [ σ ]) ⇔ Infinite l
  Infinite-[]-⇔ = flip to refl , (λ { ωᵘ+ → ωᵘ+ })
    where
    to : Infinite l′ → l [ σ ] ≡ l′ → Infinite l
    to {l} ωᵘ+ eq rewrite subst-ωᵘ+ {l = l} eq = ωᵘ+

opaque

  -- If l is infinite, then l is a level literal.

  Infinite→Level-literal : Infinite l → Level-literal l
  Infinite→Level-literal ωᵘ+ = ωᵘ+
