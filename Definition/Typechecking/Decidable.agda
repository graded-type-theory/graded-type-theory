{-# OPTIONS --without-K --safe #-}

open import Tools.Relation

module Definition.Typechecking.Decidable {a ℓ} (M″ : DecSetoid a ℓ) where

open DecSetoid M″ using (_≟_; _≈_) renaming (Carrier to M; setoid to M′; refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)

open import Definition.Conversion.FullReduction M′
open import Definition.Typechecking M′
open import Definition.Typechecking.Inversion M′
open import Definition.Typechecking.Soundness M′
open import Definition.Typechecking.Completeness M′
open import Definition.Typechecking.Deterministic M′
open import Definition.Typed M′
open import Definition.Typed.Properties M′
open import Definition.Typed.Weakening M′ as W
open import Definition.Typed.Consequences.Inequality M′
open import Definition.Typed.Consequences.Injectivity M′
open import Definition.Typed.Consequences.Inversion M′
open import Definition.Typed.Consequences.Reduction M′
open import Definition.Typed.Consequences.Syntactic M′
open import Definition.Typed.Consequences.Substitution M′
open import Definition.Typed.Decidable.Equality M″
open import Definition.Untyped M renaming (_∷_ to _∷∷_) hiding (U≢B; ℕ≢B; B≢ne)
import Definition.Untyped M as U

open import Tools.Fin
open import Tools.Nat hiding (_≟_)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Nullary

open import Definition.Typed.EqRelInstance M′
open import Definition.LogicalRelation M′
open import Definition.LogicalRelation.Properties.Escape M′
open import Definition.LogicalRelation.Fundamental.Reducibility M′

private
  variable
    n : Nat
    Γ : Con Term n
    t u A B : Term n
    p q r : M

dec⇉-var : (x : Fin n) → ∃ λ A → x ∷ A ∈ Γ
dec⇉-var {Γ = Γ ∙ A} x0 = _ , here
dec⇉-var {Γ = Γ ∙ B} (x +1) =
  let A , x∷A∈Γ = dec⇉-var x
  in  _ , there x∷A∈Γ

isB′ : ∀ {l} → Γ ⊩⟨ l ⟩ A → Dec (∃₃ λ F G W → (Γ ⊢ F) × (Γ ∙ F ⊢ G) × Γ ⊢ A ⇒* (⟦ W ⟧ F ▹ G))
isB′ (Uᵣ′ l′ l< ⊢Γ) = no (λ {(F , G , W , ⊢F , ⊢G , U⇒W) → U≢B W (subset* U⇒W)})
isB′ (ℕᵣ x) = no (λ {(F , G , W , ⊢F , ⊢G , A⇒W) → ℕ≢B W (trans (sym (subset* (red x))) (subset* A⇒W))})
isB′ (Emptyᵣ x) = no (λ {(F , G , W , ⊢F , ⊢G , A⇒W) → Empty≢Bⱼ W (trans (sym (subset* (red x))) (subset* A⇒W))})
isB′ (Unitᵣ x) = no (λ {(F , G , W , ⊢F , ⊢G , A⇒W) → Unit≢Bⱼ W (trans (sym (subset* (red x))) (subset* A⇒W))})
isB′ (ne′ K D neK K≡K) = no (λ {(F , G , W , ⊢F , ⊢G , A⇒W) → B≢ne W neK (trans (sym (subset* A⇒W)) (subset* (red D)))})
isB′ (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext) = yes (F , G , W , ⊢F , ⊢G , red D)
isB′ (emb 0<1 [A]) = isB′ [A]

isB : Γ ⊢ A → Dec (∃₃ λ F G W → (Γ ⊢ F) × (Γ ∙ F ⊢ G) × Γ ⊢ A ⇒* (⟦ W ⟧ F ▹ G))
isB ⊢A = isB′ (reducible ⊢A)

isΠ : Γ ⊢ A → Dec (∃₄ λ F G p q → (Γ ⊢ F) × (Γ ∙ F ⊢ G) × Γ ⊢ A ⇒* (Π p , q ▷ F ▹ G))
isΠ ⊢A with isB ⊢A
... | yes (F , G , BΠ p q , ⊢F , ⊢G , A⇒Π) = yes (F , G , p , q , ⊢F , ⊢G , A⇒Π)
... | yes (F , G , BΣ p x , ⊢F , ⊢G , A⇒Σ) = no (λ {(F′ , G′ , p′ , q′ , ⊢F , ⊢G , A⇒Π) → Π≢Σ (trans (sym (subset* A⇒Π)) (subset* A⇒Σ))})
... | no ¬isB = no (λ {(F′ , G′ , p′ , q′ , ⊢F , ⊢G , A⇒Π) → ¬isB (F′ , G′ , BΠ p′ q′ , ⊢F , ⊢G , A⇒Π)})

isΣ : Γ ⊢ A → Dec (∃₄ λ F G m q → (Γ ⊢ F) × (Γ ∙ F ⊢ G) × Γ ⊢ A ⇒* (Σ⟨ m ⟩ q ▷ F ▹ G))
isΣ ⊢A with isB ⊢A
... | yes (F , G , BΣ q m , ⊢F , ⊢G , A⇒Σ) = yes (F , G , m , q , ⊢F , ⊢G , A⇒Σ)
... | yes (F , G , BΠ p q , ⊢F , ⊢G , A⇒Π) = no (λ {(F′ , G′ , p′ , q′ , ⊢F , ⊢G , A⇒Σ) → Π≢Σ (trans (sym (subset* A⇒Π)) (subset* A⇒Σ))})
... | no ¬isB = no (λ {(F′ , G′ , m , q′ , ⊢F , ⊢G , A⇒Π) → ¬isB (F′ , G′ , BΣ q′ m , ⊢F , ⊢G , A⇒Π)})

isΣₚ : Γ ⊢ A → Dec (∃₃ λ F G q → (Γ ⊢ F) × (Γ ∙ F ⊢ G) × Γ ⊢ A ⇒* (Σₚ q ▷ F ▹ G))
isΣₚ ⊢A with isΣ ⊢A
... | yes (F , G , Σₚ , q , ⊢F , ⊢G , A⇒Σ) = yes (F , G , q , ⊢F , ⊢G , A⇒Σ)
... | yes (F , G , Σᵣ , q , ⊢F , ⊢G , A⇒Σ) = no (λ {(F′ , G′ , q′ , ⊢F′ , ⊢G′ , A⇒Σ′) → Σₚ≢Σᵣ (trans (sym (subset* A⇒Σ′)) (subset* A⇒Σ))})
... | no ¬isΣ = no (λ {(F′ , G′ , q′ , ⊢F′ , ⊢G′ , A⇒Σ′) → ¬isΣ (F′ , G′ , Σₚ , q′ , ⊢F′ , ⊢G′ , A⇒Σ′)})

isΣᵣ : Γ ⊢ A → Dec (∃₃ λ F G q → (Γ ⊢ F) × (Γ ∙ F ⊢ G) × Γ ⊢ A ⇒* (Σᵣ q ▷ F ▹ G))
isΣᵣ ⊢A with isΣ ⊢A
... | yes (F , G , Σₚ , q , ⊢F , ⊢G , A⇒Σ) = no (λ {(F′ , G′ , q′ , ⊢F′ , ⊢G′ , A⇒Σ′) → Σₚ≢Σᵣ (trans (sym (subset* A⇒Σ)) (subset* A⇒Σ′))})
... | yes (F , G , Σᵣ , q , ⊢F , ⊢G , A⇒Σ) = yes (F , G , q , ⊢F , ⊢G , A⇒Σ)
... | no ¬isΣ = no (λ {(F′ , G′ , q′ , ⊢F′ , ⊢G′ , A⇒Σ′) → ¬isΣ (F′ , G′ , Σᵣ , q′ , ⊢F′ , ⊢G′ , A⇒Σ′)})


mutual

  dec⇉-app : ⊢ Γ → NfNeutral t → Nf u → Dec (∃ λ A → Γ ⊢ t ∘ p ▷ u ⇉ A)
  dec⇉-app ⊢Γ t u with dec⇉ ⊢Γ t
  dec⇉-app ⊢Γ t u | yes (A , t⇉A) with isΠ (proj₁ (soundness⇉ ⊢Γ t⇉A))
  dec⇉-app {p = p′} ⊢Γ t u | yes (A , t⇉A) | yes (F , G , p , q , ⊢F , ⊢G , A⇒ΠFG) with dec⇇ ⊢Γ u ⊢F | p ≟ p′
  dec⇉-app {p = p′} ⊢Γ t u | yes (A , t⇉A) | yes (F , G , p , q , ⊢F , ⊢G , A⇒ΠFG)
                           | yes u⇇F | yes p≈p′ = yes (_ , (appᵢ t⇉A (A⇒ΠFG , Πₙ) u⇇F p≈p′))
  dec⇉-app {p = p′} ⊢Γ t u | yes (A , t⇉A) | yes (F , G , p , q , ⊢F , ⊢G , A⇒ΠFG)
                           | yes u⇇F | no p≉p′ =
    no (λ { (_ , appᵢ x x₁ x₂ x₃) →
      let A≡A′ = deterministic⇉ t⇉A x
          A↘ΠF′G′ = PE.subst (λ A → _ ⊢ A ↘ _) (PE.sym A≡A′) x₁
          ΠFG≡ΠF′G′ = whrDet* (A⇒ΠFG , Πₙ) A↘ΠF′G′
          _ , _ , W≡W′ = B-PE-injectivity BΠ! BΠ! ΠFG≡ΠF′G′
          p≡p″ , _ = BΠ-PE-injectivity W≡W′
      in  p≉p′ (PE.subst (λ p → p ≈ _) (PE.sym p≡p″) x₃)})
  dec⇉-app {p = p′} ⊢Γ t u | yes (A , t⇉A) | yes (F , G , p , q , ⊢F , ⊢G , A⇒ΠFG)
                           | no ¬u⇇F | _ =
    no (λ { (_ , appᵢ x x₁ x₂ x₃) →
      let A≡A′ = deterministic⇉ t⇉A x
          A↘ΠF′G′ = PE.subst (λ A → _ ⊢ A ↘ _) (PE.sym A≡A′) x₁
          ΠFG≡ΠF′G′ = whrDet* (A⇒ΠFG , Πₙ) A↘ΠF′G′
          F≡F′ , _ , _ = B-PE-injectivity BΠ! BΠ! ΠFG≡ΠF′G′
      in  ¬u⇇F (PE.subst (λ F → _ ⊢ _ ⇇ F) (PE.sym F≡F′) x₂)})
  dec⇉-app ⊢Γ t u | yes (A , t⇉A) | no ¬A⇒ΠFG = no (λ { (_ , appᵢ x x₁ x₂ x₃) →
    let A≡A′ = deterministic⇉ t⇉A x
        A⇒ΠFG = PE.subst (λ A → _ ⊢ A ↘ _) (PE.sym A≡A′) x₁
        _ , ⊢ΠFG = syntacticRed (proj₁ x₁)
        ⊢F , ⊢G = syntacticΠ ⊢ΠFG
    in  ¬A⇒ΠFG (_ , _ , _ , _ , ⊢F , ⊢G , proj₁ A⇒ΠFG)})
  dec⇉-app ⊢Γ t u | no ¬t⇉A = no (λ { (_ , appᵢ x x₁ x₂ x₃) → ¬t⇉A (_ , x)})

  dec⇉-natrec′ : ∀ {A z s n C} → ⊢ Γ → Nf z → Nf s → Γ ⊢ n ⇉ C → Γ ∙ ℕ ⊢ A → Γ ∙ ℕ ⊢ A ⇇Type → Dec (∃ λ B → Γ ⊢ natrec p r A z s n ⇉ B)
  dec⇉-natrec′ ⊢Γ z s n⇉C ⊢A A⇇Type with dec⇇ ⊢Γ z (substType ⊢A (zeroⱼ ⊢Γ)) | decEq (proj₁ (soundness⇉ ⊢Γ n⇉C)) (ℕⱼ ⊢Γ)
  dec⇉-natrec′ ⊢Γ z s n⇉C ⊢A A⇇Type | yes z⇇A₀ | yes C≡ℕ
    with dec⇇ (⊢Γ ∙ ℕⱼ ⊢Γ ∙ ⊢A) s (W.wk (step id) (⊢Γ ∙ ℕⱼ ⊢Γ ∙ ⊢A) (subst↑Type ⊢A (sucⱼ (var (⊢Γ ∙ ℕⱼ ⊢Γ) here))))
  dec⇉-natrec′ ⊢Γ z s n⇉C ⊢A A⇇Type | yes z⇇A₀ | yes C≡ℕ | yes s⇇A₊ = yes (_ , natrecᵢ A⇇Type z⇇A₀ s⇇A₊ (infᶜ n⇉C C≡ℕ))
  dec⇉-natrec′ ⊢Γ z s n⇉C ⊢A A⇇Type | yes z⇇A₀ | yes C≡ℕ | no ¬s⇇A₊ = no (λ { (_ , natrecᵢ x x₁ x₂ x₃) → ¬s⇇A₊ x₂})
  dec⇉-natrec′ ⊢Γ z s n⇉C ⊢A A⇇Type | yes z⇇A₀ | no C≢ℕ =
    no λ { (_ , natrecᵢ x x₁ x₂ (infᶜ x₃ x₄)) → C≢ℕ (PE.subst (λ C → _ ⊢ C ≡ ℕ) (deterministic⇉ x₃ n⇉C) x₄)}
  dec⇉-natrec′ ⊢Γ z s n⇉C ⊢A A⇇Type | no ¬z⇇A₀ | _ = no (λ { (_ , natrecᵢ x x₁ x₂ x₃) → ¬z⇇A₀ x₁})

  dec⇉-natrec : ∀ {A z s n} → ⊢ Γ → Nf A → Nf z → Nf s → NfNeutral n → Dec (∃ λ B → Γ ⊢ natrec p r A z s n ⇉ B)
  dec⇉-natrec ⊢Γ A z s n with dec⇉ ⊢Γ n | dec⇇Type (⊢Γ ∙ ℕⱼ ⊢Γ) A
  dec⇉-natrec ⊢Γ A z s n | yes (B , n⇉B) | yes A⇇Type = dec⇉-natrec′ ⊢Γ z s n⇉B (soundness⇇Type (⊢Γ ∙ ℕⱼ ⊢Γ) A⇇Type) A⇇Type
  dec⇉-natrec ⊢Γ A z s n | yes (B , n⇉B) | no ¬A⇇Type = no (λ { (_ , natrecᵢ x x₁ x₂ x₃) → ¬A⇇Type x})
  dec⇉-natrec ⊢Γ A z s n | no ¬n⇇A | _ = no (λ { (_ , natrecᵢ x x₁ x₂ (infᶜ x₃ x₄)) → ¬n⇇A (_ , x₃)})


  dec⇉-prodrec : ⊢ Γ → Nf A → NfNeutral t → Nf u → Dec (∃ λ B → Γ ⊢ prodrec p A t u ⇉ B)
  dec⇉-prodrec ⊢Γ A t u with dec⇉ ⊢Γ t
  dec⇉-prodrec ⊢Γ A t u | yes (B , t⇉B) with isΣᵣ (proj₁ (soundness⇉ ⊢Γ t⇉B))
  dec⇉-prodrec ⊢Γ A t u | yes (B , t⇉B) | yes (F , G , q , ⊢F , ⊢G , B⇒ΣFG)
    with dec⇇Type (⊢Γ ∙ (Σⱼ ⊢F ▹ ⊢G)) A
  dec⇉-prodrec ⊢Γ A t u | yes (B , t⇉B) | yes (F , G , q , ⊢F , ⊢G , B⇒ΣFG)
                        | yes A⇇Type with dec⇇ (⊢Γ ∙ ⊢F ∙ ⊢G) u (subst↑²Type (soundness⇇Type (⊢Γ ∙ proj₂ (syntacticRed B⇒ΣFG)) A⇇Type))
  dec⇉-prodrec ⊢Γ A t u | yes (B , t⇉B) | yes (F , G , q , ⊢F , ⊢G , B⇒ΣFG)
                        | yes A⇇Type | yes u⇇A₊ = yes (_ , prodrecᵢ A⇇Type t⇉B (B⇒ΣFG , Σₙ) u⇇A₊)
  dec⇉-prodrec ⊢Γ A t u | yes (B , t⇉B) | yes (F , G , q , ⊢F , ⊢G , B⇒ΣFG)
                        | yes A⇇Type | no ¬u⇇A₊ = no λ { (_ , prodrecᵢ x x₁ x₂ x₃) →
    let B≡B′ = deterministic⇉ t⇉B x₁
        Σ≡Σ′ = whrDet* (PE.subst (λ B → _ ⊢ B ↘ _) B≡B′ (B⇒ΣFG , Σₙ)) x₂
        F≡F′ , G≡G′ , _ = B-PE-injectivity BΣ! BΣ! Σ≡Σ′
    in  ¬u⇇A₊ (PE.subst₂ (λ F G → (_ ∙ F ∙ G) ⊢ _ ⇇ _) (PE.sym F≡F′) (PE.sym G≡G′) x₃)}
  dec⇉-prodrec {Γ = Γ} {A = A′} ⊢Γ A t u | yes (B , t⇉B) | yes (F , G , q , ⊢F , ⊢G , B⇒ΣFG)
                        | no ¬A⇇Type = no (λ { (_ , prodrecᵢ x x₁ x₂ x₃) →
    let B≡B′ = deterministic⇉ t⇉B x₁
        Σ≡Σ′ = whrDet* (PE.subst (λ B → _ ⊢ B ↘ _) B≡B′ (B⇒ΣFG , Σₙ)) x₂
    in  ¬A⇇Type (PE.subst (λ Σ → Γ ∙ Σ ⊢ A′ ⇇Type) (PE.sym Σ≡Σ′) x)})
  dec⇉-prodrec ⊢Γ A t u | yes (B , t⇉B) | no ¬isΣᵣ = no λ { (_ , prodrecᵢ x x₁ x₂ x₃) →
    let B′≡B = deterministic⇉ x₁ t⇉B
        _ , ⊢Σ = syntacticRed (proj₁ x₂)
        ⊢F , ⊢G = syntacticΣ ⊢Σ
    in  ¬isΣᵣ (_ , _ , _ , ⊢F , ⊢G , PE.subst (λ B → _ ⊢ B ⇒* _) B′≡B (proj₁ x₂))}
  dec⇉-prodrec ⊢Γ A t u | no ¬t⇉B = no λ { (_ , prodrecᵢ x x₁ x₂ x₃) → ¬t⇉B (_ , x₁)}

  -- Decidability of checking that a term is a type

  dec⇇Type : ⊢ Γ → Nf A → Dec (Γ ⊢ A ⇇Type)
  dec⇇Type ⊢Γ Uₙ = yes Uᵢ
  dec⇇Type ⊢Γ (Πₙ F G) with dec⇇Type ⊢Γ F
  ... | yes F⇇Type with dec⇇Type (⊢Γ ∙ soundness⇇Type ⊢Γ F⇇Type) G
  ... | yes G⇇Type = yes (Πᵢ F⇇Type G⇇Type)
  ... | no ¬G⇇Type = no (λ { (Πᵢ x x₁) → ¬G⇇Type x₁ ; (univᵢ (infᶜ (Πᵢ x x₂) x₁)) → ¬G⇇Type (univᵢ x₂)})
  dec⇇Type ⊢Γ (Πₙ F G) | no ¬F⇇Type = no (λ { (Πᵢ x x₁) → ¬F⇇Type x ; (univᵢ (infᶜ (Πᵢ x x₂) x₁)) → ¬F⇇Type (univᵢ x)})
  dec⇇Type ⊢Γ (Σₙ F G) with dec⇇Type ⊢Γ F
  ... | yes F⇇Type with dec⇇Type (⊢Γ ∙ soundness⇇Type ⊢Γ F⇇Type) G
  ... | yes G⇇Type = yes (Σᵢ F⇇Type G⇇Type)
  ... | no ¬G⇇Type = no (λ { (Σᵢ x x₁) → ¬G⇇Type x₁ ; (univᵢ (infᶜ (Σᵢ x x₂) x₁)) → ¬G⇇Type (univᵢ x₂)})
  dec⇇Type ⊢Γ (Σₙ F G) | no ¬F⇇Type = no (λ { (Σᵢ x x₁) → ¬F⇇Type x ; (univᵢ (infᶜ (Σᵢ x x₂) x₁)) → ¬F⇇Type (univᵢ x)})
  dec⇇Type ⊢Γ ℕₙ = yes ℕᵢ
  dec⇇Type ⊢Γ Emptyₙ = yes Emptyᵢ
  dec⇇Type ⊢Γ Unitₙ = yes Unitᵢ
  dec⇇Type ⊢Γ (lamₙ t) = no (λ { (univᵢ (lamᶜ x x₁ x₂)) → U.U≢B BΠ! (whnfRed* (proj₁ x) Uₙ)})
  dec⇇Type ⊢Γ (prodₙ t u) = no (λ { (univᵢ (prodᶜ x x₁ x₂)) → U.U≢B BΣ! (whnfRed* (proj₁ x) Uₙ)})
  dec⇇Type ⊢Γ zeroₙ = no (λ { (univᵢ (infᶜ zeroᵢ x₁)) → U≢ℕ (sym x₁)})
  dec⇇Type ⊢Γ (sucₙ t) = no (λ { (univᵢ (infᶜ (sucᵢ x) x₁)) → U≢ℕ (sym x₁)})
  dec⇇Type ⊢Γ starₙ = no (λ { (univᵢ (infᶜ starᵢ x₁)) → U≢Unitⱼ (sym x₁)})
  dec⇇Type ⊢Γ (ne x) with dec⇉ ⊢Γ x
  ... | yes (A , t⇉A) with decEq (proj₁ (soundness⇉ ⊢Γ t⇉A)) (Uⱼ ⊢Γ)
  ... | yes A≡U = yes (univᵢ (infᶜ t⇉A A≡U))
  ... | no A≢U = no (λ { (univᵢ (infᶜ x x₁)) → A≢U (PE.subst (λ A → _ ⊢ A ≡ _) (deterministic⇉ x t⇉A) x₁)})
  dec⇇Type ⊢Γ (ne x) | no ¬t⇉A = no (λ { (univᵢ (infᶜ x x₁)) → ¬t⇉A (_ , x)})

  -- Decidability of algorithmic type inference

  dec⇉ : ⊢ Γ → NfNeutral t → Dec (∃ λ A → Γ ⊢ t ⇉ A)
  dec⇉ ⊢Γ (var x) = yes (_ , varᵢ (proj₂ (dec⇉-var x)))
  dec⇉ ⊢Γ (∘ₙ {q = p} t u) = dec⇉-app ⊢Γ t u
  dec⇉ ⊢Γ (fstₙ t) with dec⇉ ⊢Γ t
  ... | yes (A , t⇉A) with isΣₚ (proj₁ (soundness⇉ ⊢Γ t⇉A))
  ... | yes (F , G , q , ⊢F , ⊢G , A⇒ΣFG) = yes (_ , fstᵢ t⇉A (A⇒ΣFG , Σₙ))
  ... | no ¬A⇒ΣFG = no (λ { (_ , fstᵢ x x₁) →
    let A≡A′ = deterministic⇉ t⇉A x
        A⇒ΣFG = PE.subst (λ A → _ ⊢ A ↘ _) (PE.sym A≡A′) x₁
        _ , ⊢ΣFG = syntacticRed (proj₁ x₁)
        ⊢F , ⊢G = syntacticΣ ⊢ΣFG
    in  ¬A⇒ΣFG (_ , _ , _ , ⊢F , ⊢G , proj₁ A⇒ΣFG)})
  dec⇉ ⊢Γ (fstₙ t) | no ¬t⇉A = no (λ { (_ , fstᵢ x x₁) → ¬t⇉A (_ , x)})
  dec⇉ ⊢Γ (sndₙ t) with dec⇉ ⊢Γ t
  ... | yes (A , t⇉A) with isΣₚ (proj₁ (soundness⇉ ⊢Γ t⇉A))
  ... | yes (F , G , q , ⊢F , ⊢G , A⇒ΣFG) = yes (_ , sndᵢ t⇉A (A⇒ΣFG , Σₙ))
  ... | no ¬A⇒ΣFG = no (λ { (_ , sndᵢ x x₁) →
    let A≡A′ = deterministic⇉ t⇉A x
        A⇒ΣFG = PE.subst (λ A → _ ⊢ A ↘ _) (PE.sym A≡A′) x₁
        _ , ⊢ΣFG = syntacticRed (proj₁ x₁)
        ⊢F , ⊢G = syntacticΣ ⊢ΣFG
    in  ¬A⇒ΣFG (_ , _ , _ , ⊢F , ⊢G , proj₁ A⇒ΣFG)})
  dec⇉ ⊢Γ (sndₙ t) | no ¬t⇉A = no (λ { (_ , sndᵢ x x₁) → ¬t⇉A (_ , x)})
  dec⇉ ⊢Γ (natrecₙ A z s n) = dec⇉-natrec ⊢Γ A z s n
  dec⇉ ⊢Γ (prodrecₙ A t u) = dec⇉-prodrec ⊢Γ A t u
  dec⇉ ⊢Γ (Emptyrecₙ A t) with dec⇉ ⊢Γ t
  ... | yes (B , t⇉B) with decEq (proj₁ (soundness⇉ ⊢Γ t⇉B)) (Emptyⱼ ⊢Γ) | dec⇇Type ⊢Γ A
  ... | yes B≡Empty | yes A⇇Type = yes (_ , Emptyrecᵢ A⇇Type (infᶜ t⇉B B≡Empty))
  ... | yes B≡Empty | no ¬A⇇Type = no (λ { (_ , Emptyrecᵢ x x₁) → ¬A⇇Type x})
  ... | no B≢Empty | _ = no (λ { (_ , Emptyrecᵢ x (infᶜ x₁ x₂)) → B≢Empty (PE.subst (λ B → _ ⊢ B ≡ Empty) (deterministic⇉ x₁ t⇉B) x₂)})
  dec⇉ ⊢Γ (Emptyrecₙ A t) | no ¬t⇉B = no (λ { (_ , Emptyrecᵢ x (infᶜ x₁ x₂)) → ¬t⇉B ((_ , x₁))})

  -- Decidability of algorithmic type checking

  dec⇇ : ⊢ Γ → Nf t → Γ ⊢ A → Dec (Γ ⊢ t ⇇ A)
  dec⇇ ⊢Γ Uₙ ⊢A = no (λ { (infᶜ () x₁)})
  dec⇇ ⊢Γ (Πₙ F G) ⊢A with dec⇇ ⊢Γ F (Uⱼ ⊢Γ)
  ... | yes F⇇U with dec⇇ (⊢Γ ∙ univ (soundness⇇ ⊢Γ (Uⱼ ⊢Γ) F⇇U)) G (Uⱼ (⊢Γ ∙ univ (soundness⇇ ⊢Γ (Uⱼ ⊢Γ) F⇇U)))
  ... | yes G⇇U with decEq (Uⱼ ⊢Γ) ⊢A
  ... | yes U≡A = yes (infᶜ (Πᵢ F⇇U G⇇U) U≡A)
  ... | no U≢A = no (λ { (infᶜ (Πᵢ x x₂) x₁) → U≢A x₁})
  dec⇇ ⊢Γ (Πₙ F G) ⊢A | yes F⇇U | no ¬G⇇U = no (λ { (infᶜ (Πᵢ x x₂) x₁) → ¬G⇇U x₂})
  dec⇇ ⊢Γ (Πₙ F G) ⊢A | no ¬F⇇U = no (λ { (infᶜ (Πᵢ x x₂) x₁) → ¬F⇇U x})
  dec⇇ ⊢Γ (Σₙ F G) ⊢A with dec⇇ ⊢Γ F (Uⱼ ⊢Γ)
  ... | yes F⇇U with dec⇇ (⊢Γ ∙ univ (soundness⇇ ⊢Γ (Uⱼ ⊢Γ) F⇇U)) G (Uⱼ (⊢Γ ∙ univ (soundness⇇ ⊢Γ (Uⱼ ⊢Γ) F⇇U)))
  ... | yes G⇇U with decEq (Uⱼ ⊢Γ) ⊢A
  ... | yes U≡A = yes (infᶜ (Σᵢ F⇇U G⇇U) U≡A)
  ... | no U≢A = no (λ { (infᶜ (Σᵢ x x₂) x₁) → U≢A x₁})
  dec⇇ ⊢Γ (Σₙ F G) ⊢A | yes F⇇U | no ¬G⇇U = no (λ { (infᶜ (Σᵢ x x₂) x₁) → ¬G⇇U x₂})
  dec⇇ ⊢Γ (Σₙ F G) ⊢A | no ¬F⇇U = no (λ { (infᶜ (Σᵢ x x₂) x₁) → ¬F⇇U x})
  dec⇇ ⊢Γ ℕₙ ⊢A with decEq (Uⱼ ⊢Γ) ⊢A
  ... | yes U≡A = yes (infᶜ ℕᵢ U≡A)
  ... | no U≢A = no (λ { (infᶜ ℕᵢ x₁) → U≢A x₁})
  dec⇇ ⊢Γ Emptyₙ ⊢A with decEq (Uⱼ ⊢Γ) ⊢A
  ... | yes U≡A = yes (infᶜ Emptyᵢ U≡A)
  ... | no U≢A = no (λ { (infᶜ Emptyᵢ x₁) → U≢A x₁})
  dec⇇ ⊢Γ Unitₙ ⊢A with decEq (Uⱼ ⊢Γ) ⊢A
  ... | yes U≡A = yes (infᶜ Unitᵢ U≡A)
  ... | no U≢A = no (λ { (infᶜ Unitᵢ x₁) → U≢A x₁})
  dec⇇ ⊢Γ (lamₙ {q = p} t) ⊢A with isΠ ⊢A
  ... | yes (F , G , p′ , q , ⊢F , ⊢G , A⇒ΠFG) with dec⇇ (⊢Γ ∙ ⊢F) t ⊢G | p ≟ p′
  ... | yes t⇇G | yes p≈p′ = yes (lamᶜ (A⇒ΠFG , Πₙ) t⇇G (≈-sym p≈p′))
  ... | yes t⇇G | no p≉p′ = no (λ { (lamᶜ x x₁ x₂) →
    let Π≡Π′ = trans (sym (subset* A⇒ΠFG)) (subset* (proj₁ x))
        _ , _ , p′≈p″ , _ = injectivity Π≡Π′
    in  p≉p′ (≈-trans (≈-sym x₂) (≈-sym p′≈p″))})
  ... | no ¬t⇇G | _ = no (λ { (lamᶜ x x₁ x₂) →
    let Π≡Π′ = whrDet* (A⇒ΠFG , Πₙ) x
        F≡F′ , G≡G′ , _ = B-PE-injectivity BΠ! BΠ! Π≡Π′
    in  ¬t⇇G (PE.subst₂ (λ F G → (_ ∙ F) ⊢ _ ⇇ G) (PE.sym F≡F′) (PE.sym G≡G′) x₁)})
  dec⇇ ⊢Γ (lamₙ t) ⊢A | no ¬isΠ = no (λ { (lamᶜ x x₁ x₂) →
    let _ , ⊢ΠFG = syntacticRed (proj₁ x)
        ⊢F , ⊢G = syntacticΠ ⊢ΠFG
    in  ¬isΠ (_ , _ , _ , _ , ⊢F , ⊢G , proj₁ x)})
  dec⇇ ⊢Γ (prodₙ t u) ⊢A with isΣ ⊢A
  ... | yes (F , G , m , q , ⊢F , ⊢G , A⇒ΣFG) with dec⇇ ⊢Γ t ⊢F
  ... | yes t⇇F with dec⇇ ⊢Γ u (substType ⊢G (soundness⇇ ⊢Γ ⊢F t⇇F))
  ... | yes u⇇Gt = yes (prodᶜ (A⇒ΣFG , Σₙ) t⇇F u⇇Gt)
  ... | no ¬u⇇Gt = no (λ { (prodᶜ x x₁ x₂) →
    let Σ≡Σ′ = whrDet* (A⇒ΣFG , Σₙ) x
        F≡F′ , G≡G′ , _ = B-PE-injectivity BΣ! BΣ! Σ≡Σ′
    in  ¬u⇇Gt (PE.subst (λ G → _ ⊢ _ ⇇ (G [ _ ])) (PE.sym G≡G′) x₂)})
  dec⇇ ⊢Γ (prodₙ t u) ⊢A | yes (F , G , m , q , ⊢F , ⊢G , A⇒ΣFG) | no ¬t⇇F = no λ { (prodᶜ x x₁ x₂) →
    let Σ≡Σ′ = whrDet* (A⇒ΣFG , Σₙ) x
        F≡F′ , G≡G′ , _ = B-PE-injectivity BΣ! BΣ! Σ≡Σ′
    in  ¬t⇇F (PE.subst (λ F → _ ⊢ _ ⇇ F) (PE.sym F≡F′) x₁)}
  dec⇇ ⊢Γ (prodₙ t u) ⊢A | no ¬isΣ = no (λ { (prodᶜ x x₁ x₂) →
    let _ , ⊢ΣFG = syntacticRed (proj₁ x)
        ⊢F , ⊢G = syntacticΣ ⊢ΣFG
    in  ¬isΣ (_ , _ , _ , _ , ⊢F , ⊢G , proj₁ x)})
  dec⇇ ⊢Γ zeroₙ ⊢A with decEq (ℕⱼ ⊢Γ) ⊢A
  ... | yes ℕ≡A = yes (infᶜ zeroᵢ ℕ≡A)
  ... | no ℕ≢A = no (λ { (infᶜ zeroᵢ x₁) → ℕ≢A x₁})
  dec⇇ ⊢Γ (sucₙ t) ⊢A with dec⇇ ⊢Γ t (ℕⱼ ⊢Γ)
  ... | yes t⇇ℕ with decEq (ℕⱼ ⊢Γ) ⊢A
  ... | yes ℕ≡A = yes (infᶜ (sucᵢ t⇇ℕ) ℕ≡A)
  ... | no ℕ≢A = no (λ { (infᶜ (sucᵢ x) x₁) → ℕ≢A x₁})
  dec⇇ ⊢Γ (sucₙ t) ⊢A | no ¬t⇇ℕ = no λ { (infᶜ (sucᵢ x) x₁) → ¬t⇇ℕ x}
  dec⇇ ⊢Γ starₙ ⊢A with decEq (Unitⱼ ⊢Γ) ⊢A
  ... | yes Unit≡A = yes (infᶜ starᵢ Unit≡A)
  ... | no Unit≢A = no (λ { (infᶜ starᵢ x₁) → Unit≢A x₁})
  dec⇇ ⊢Γ (ne x) ⊢A with dec⇉ ⊢Γ x
  ... | yes (B , t⇉B) with decEq (proj₁ (soundness⇉ ⊢Γ t⇉B)) ⊢A
  ... | yes B≡A = yes (infᶜ t⇉B B≡A)
  ... | no B≢A = no (λ { (infᶜ x x₁) →
    let B≡A′ = deterministic⇉ t⇉B x
    in  B≢A (PE.subst (λ x → _ ⊢ x ≡ _) (PE.sym B≡A′) x₁)})
  dec⇇ ⊢Γ (ne x) ⊢A | no ¬t⇉B = no (λ { (infᶜ x x₁) → ¬t⇉B (_ , x)})
