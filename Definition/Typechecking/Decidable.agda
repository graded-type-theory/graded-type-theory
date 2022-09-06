{-# OPTIONS --without-K --safe #-}

open import Tools.Relation

module Definition.Typechecking.Decidable {a ℓ} (M″ : DecSetoid a ℓ) where

open DecSetoid M″ using (_≟_; _≈_) renaming (Carrier to M; setoid to M′; refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)

open import Definition.Typechecking M′
open import Definition.Typechecking.Soundness M′
open import Definition.Typechecking.Deterministic M′
open import Definition.Typed M′
open import Definition.Typed.Properties M′
open import Definition.Typed.Weakening M′ as W
open import Definition.Typed.Consequences.Inequality M′
open import Definition.Typed.Consequences.Syntactic M′
open import Definition.Typed.Consequences.Substitution M′
open import Definition.Typed.Decidable.Equality M″
open import Definition.Typed.Decidable.Reduction M″
open import Definition.Untyped M
import Definition.Untyped M as U

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Nullary

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

dec⇇-var : (x : Fin n) → Γ ⊢ A → Dec (Γ ⊢ var x ⇇ A)
dec⇇-var x ⊢A with dec⇉-var x
... | B , x∷B∈Γ with decEq (syntacticVar x∷B∈Γ (wf ⊢A)) ⊢A
... | yes B≡A = yes (infᶜ (varᵢ x∷B∈Γ) B≡A)
... | no B≢A = no λ { (infᶜ (varᵢ x) x₁) → B≢A (PE.subst (λ x → _ ⊢ x ≡ _) (det∈ x x∷B∈Γ) x₁)}

mutual

  -- Decidability of terms being inferable

  dec-Inferable : (t : Term n) → Dec (Inferable t)
  dec-Inferable (var x) = yes varᵢ
  dec-Inferable (gen Ukind []) = yes Uᵢ
  dec-Inferable (gen (Pikind p q) (F ∷ G ∷ []))
    with dec-Checkable F | dec-Checkable G
  ... | yes F′ | yes G′ = yes (Πᵢ F′ G′)
  ... | yes F′ | no ¬G′ = no λ { (Πᵢ x x₁) → ¬G′ x₁}
  ... | no ¬F′ | _      = no λ { (Πᵢ x x₁) → ¬F′ x}
  dec-Inferable (gen (Lamkind p) (t ∷ [])) = no λ {()}
  dec-Inferable (gen (Appkind p) (t ∷ u ∷ []))
    with dec-Inferable t | dec-Checkable u
  ... | yes t′ | yes u′ = yes (∘ᵢ t′ u′)
  ... | yes t′ | no ¬u′ = no λ { (∘ᵢ x x₁) → ¬u′ x₁}
  ... | no ¬t′ | _      = no λ { (∘ᵢ x x₁) → ¬t′ x}
  dec-Inferable (gen (Sigmakind q x) (F ∷ G ∷ []))
    with dec-Checkable F | dec-Checkable G
  ... | yes F′ | yes G′ = yes (Σᵢ F′ G′)
  ... | yes F′ | no ¬G′ = no λ { (Σᵢ x x₁) → ¬G′ x₁}
  ... | no ¬F′ | _      = no λ { (Σᵢ x x₁) → ¬F′ x}
  dec-Inferable (gen Prodkind (t ∷ u ∷ [])) = no λ {()}
  dec-Inferable (gen Fstkind (t ∷ []))
    with dec-Inferable t
  ... | yes t′ = yes (fstᵢ t′)
  ... | no ¬t′ = no λ { (fstᵢ x) → ¬t′ x}
  dec-Inferable (gen Sndkind (t ∷ []))
    with dec-Inferable t
  ... | yes t′ = yes (sndᵢ t′)
  ... | no ¬t′ = no λ { (sndᵢ x) → ¬t′ x}
  dec-Inferable (gen (Prodreckind p) (A ∷ t ∷ u ∷ []))
    with dec-Checkable A | dec-Inferable t | dec-Checkable u
  ... | yes A′ | yes t′ | yes u′ = yes (prodrecᵢ A′ t′ u′)
  ... | yes A′ | yes t′ | no ¬u′ = no λ { (prodrecᵢ x x₁ x₂) → ¬u′ x₂}
  ... | yes A′ | no ¬t′ | _      = no λ { (prodrecᵢ x x₁ x₂) → ¬t′ x₁}
  ... | no ¬A′ | _ | _           = no λ { (prodrecᵢ x x₁ x₂) → ¬A′ x}
  dec-Inferable (gen Natkind []) = yes ℕᵢ
  dec-Inferable (gen Zerokind []) = yes zeroᵢ
  dec-Inferable (gen Suckind (t ∷ []))
    with dec-Checkable t
  ... | yes t′ = yes (sucᵢ t′)
  ... | no ¬t′ = no λ { (sucᵢ x) → ¬t′ x}
  dec-Inferable (gen (Natreckind p q) (A ∷ z ∷ s ∷ n ∷ []))
    with dec-Checkable A | dec-Checkable z | dec-Checkable s | dec-Checkable n
  ... | yes A′ | yes z′ | yes s′ | yes n′ = yes (natrecᵢ A′ z′ s′ n′)
  ... | yes A′ | yes z′ | yes s′ | no ¬n′ = no λ { (natrecᵢ x x₁ x₂ x₃) → ¬n′ x₃}
  ... | yes A′ | yes z′ | no ¬s′ | _      = no λ { (natrecᵢ x x₁ x₂ x₃) → ¬s′ x₂}
  ... | yes A′ | no ¬z′ | _ | _           = no λ { (natrecᵢ x x₁ x₂ x₃) → ¬z′ x₁}
  ... | no ¬A′ | _ | _ | _                = no λ { (natrecᵢ x x₁ x₂ x₃) → ¬A′ x}
  dec-Inferable (gen Unitkind []) = yes Unitᵢ
  dec-Inferable (gen Starkind []) = yes starᵢ
  dec-Inferable (gen Emptykind []) = yes Emptyᵢ
  dec-Inferable (gen (Emptyreckind p) (A ∷ t ∷ []))
    with dec-Checkable A | dec-Checkable t
  ... | yes A′ | yes t′ = yes (Emptyrecᵢ A′ t′)
  ... | yes A′ | no ¬t′ = no λ { (Emptyrecᵢ x x₁) → ¬t′ x₁}
  ... | no ¬A′ | _      = no λ { (Emptyrecᵢ x x₁) → ¬A′ x}

  -- Decidability of terms being checkable

  dec-Checkable : (t : Term n) → Dec (Checkable t)
  dec-Checkable (var x) = yes (infᶜ varᵢ)
  dec-Checkable (gen Ukind []) = yes (infᶜ Uᵢ)
  dec-Checkable (gen (Pikind p q) (F ∷ G ∷ []))
    with dec-Checkable F | dec-Checkable G
  ... | yes F′ | yes G′ = yes (infᶜ (Πᵢ F′ G′))
  ... | yes F′ | no ¬G′ = no λ { (infᶜ (Πᵢ x x₁)) → ¬G′ x₁}
  ... | no ¬F′ | _      = no λ { (infᶜ (Πᵢ x x₁)) → ¬F′ x}
  dec-Checkable (gen (Lamkind p) (t ∷ []))
    with dec-Checkable t
  ... | yes t′ = yes (lamᶜ t′)
  ... | no ¬t′ = no λ { (lamᶜ x) → ¬t′ x}
  dec-Checkable (gen (Appkind p) (t ∷ u ∷ []))
    with dec-Inferable t | dec-Checkable u
  ... | yes t′ | yes u′ = yes (infᶜ (∘ᵢ t′ u′))
  ... | yes t′ | no ¬u′ = no λ { (infᶜ (∘ᵢ x x₁)) → ¬u′ x₁}
  ... | no ¬t′ | _      = no λ { (infᶜ (∘ᵢ x x₁)) → ¬t′ x}
  dec-Checkable (gen (Sigmakind q x) (F ∷ G ∷ []))
    with dec-Checkable F | dec-Checkable G
  ... | yes F′ | yes G′ = yes (infᶜ (Σᵢ F′ G′))
  ... | yes F′ | no ¬G′ = no λ { (infᶜ (Σᵢ x x₁)) → ¬G′ x₁}
  ... | no ¬F′ | _      = no λ { (infᶜ (Σᵢ x x₁)) → ¬F′ x}
  dec-Checkable (gen Prodkind (t ∷ u ∷ []))
    with dec-Checkable t | dec-Checkable u
  ... | yes t′ | yes u′ = yes (prodᶜ t′ u′)
  ... | yes t′ | no ¬u′ = no λ { (prodᶜ x x₁) → ¬u′ x₁}
  ... | no ¬t′ | _      = no λ { (prodᶜ x x₁) → ¬t′ x}
  dec-Checkable (gen Fstkind (t ∷ []))
    with dec-Inferable t
  ... | yes t′ = yes (infᶜ (fstᵢ t′))
  ... | no ¬t′ = no λ { (infᶜ (fstᵢ x)) → ¬t′ x}
  dec-Checkable (gen Sndkind (t ∷ []))
    with dec-Inferable t
  ... | yes t′ = yes (infᶜ (sndᵢ t′))
  ... | no ¬t′ = no λ { (infᶜ (sndᵢ x)) → ¬t′ x}
  dec-Checkable (gen (Prodreckind p) (A ∷ t ∷ u ∷ []))
    with dec-Checkable A | dec-Inferable t | dec-Checkable u
  ... | yes A′ | yes t′ | yes u′ = yes (infᶜ (prodrecᵢ A′ t′ u′))
  ... | yes A′ | yes t′ | no ¬u′ = no λ { (infᶜ (prodrecᵢ x x₁ x₂)) → ¬u′ x₂}
  ... | yes A′ | no ¬t′ | _      = no λ { (infᶜ (prodrecᵢ x x₁ x₂)) → ¬t′ x₁}
  ... | no ¬A′ | _ | _           = no λ { (infᶜ (prodrecᵢ x x₁ x₂)) → ¬A′ x}
  dec-Checkable (gen Natkind []) = yes (infᶜ ℕᵢ)
  dec-Checkable (gen Zerokind []) = yes (infᶜ zeroᵢ)
  dec-Checkable (gen Suckind (t ∷ []))
    with dec-Checkable t
  ... | yes t′ = yes (infᶜ (sucᵢ t′))
  ... | no ¬t′ = no λ { (infᶜ (sucᵢ x)) → ¬t′ x}
  dec-Checkable (gen (Natreckind p q) (A ∷ z ∷ s ∷ n ∷ []))
    with dec-Checkable A | dec-Checkable z | dec-Checkable s | dec-Checkable n
  ... | yes A′ | yes z′ | yes s′ | yes n′ = yes (infᶜ (natrecᵢ A′ z′ s′ n′))
  ... | yes A′ | yes z′ | yes s′ | no ¬n′ = no λ { (infᶜ (natrecᵢ x x₁ x₂ x₃)) → ¬n′ x₃}
  ... | yes A′ | yes z′ | no ¬s′ | _      = no λ { (infᶜ (natrecᵢ x x₁ x₂ x₃)) → ¬s′ x₂}
  ... | yes A′ | no ¬z′ | _ | _           = no λ { (infᶜ (natrecᵢ x x₁ x₂ x₃)) → ¬z′ x₁}
  ... | no ¬A′ | _ | _ | _                = no λ { (infᶜ (natrecᵢ x x₁ x₂ x₃)) → ¬A′ x}
  dec-Checkable (gen Unitkind []) = yes (infᶜ Unitᵢ)
  dec-Checkable (gen Starkind []) = yes (infᶜ starᵢ)
  dec-Checkable (gen Emptykind []) = yes (infᶜ Emptyᵢ)
  dec-Checkable (gen (Emptyreckind p) (A ∷ t ∷ []))
    with dec-Checkable A | dec-Checkable t
  ... | yes A′ | yes t′ = yes (infᶜ (Emptyrecᵢ A′ t′))
  ... | yes A′ | no ¬t′ = no λ { (infᶜ (Emptyrecᵢ x x₁)) → ¬t′ x₁}
  ... | no ¬A′ | _      = no λ { (infᶜ (Emptyrecᵢ x x₁)) → ¬A′ x}


mutual

  dec⇉-app : ⊢ Γ → Inferable t → Checkable u → Dec (∃ λ A → Γ ⊢ t ∘ p ▷ u ⇉ A)
  dec⇉-app {p = p′} ⊢Γ t u with dec⇉ ⊢Γ t
  ... | no ¬t⇉A = no λ { (_ , appᵢ x x₁ x₂ x₃) → ¬t⇉A (_ , x)}
  ... | yes (A , t⇉A) with isΠ (proj₁ (soundness⇉ ⊢Γ t⇉A))
  ... | no ¬isΠ = no λ { (_ , appᵢ x x₁ x₂ x₃) →
    let A≡A′ = deterministic⇉ x t⇉A
        _ , ⊢Π = syntacticRed (proj₁ x₁)
        ⊢F , ⊢G = syntacticΠ ⊢Π
    in  ¬isΠ (_ , _ , _ , _ , ⊢F , ⊢G , PE.subst (λ x → _ ⊢ x ⇒* _) A≡A′ (proj₁ x₁))}
  ... | yes (F , G , p , q  , ⊢F , ⊢G , A⇒Π) with dec⇇ ⊢Γ u ⊢F
  ... | no ¬u⇇F = no λ { (_ , appᵢ x x₁ x₂ x₃) →
    let A≡A′ = deterministic⇉ t⇉A x
        Π≡Π′ = whrDet* x₁ (PE.subst (λ x → _ ⊢ x ⇒* _) A≡A′ A⇒Π , Πₙ)
        F≡F′ , _ = B-PE-injectivity BΠ! BΠ! Π≡Π′
    in  ¬u⇇F (PE.subst (λ x → _ ⊢ _ ⇇ x) F≡F′ x₂)}
  ... | yes u⇇F with p ≟ p′
  ... | no p≉p′ = no λ { (_ , appᵢ x x₁ x₂ x₃) →
    let A≡A′ = deterministic⇉ t⇉A x
        Π≡Π′ = whrDet* x₁ (PE.subst (λ x → _ ⊢ x ⇒* _) A≡A′ A⇒Π , Πₙ)
        F≡F′ , G≡G′ , W≡W′ = B-PE-injectivity BΠ! BΠ! Π≡Π′
        p≡p′ , _ = BΠ-PE-injectivity W≡W′
    in  p≉p′ (PE.subst (λ x → x ≈ _) p≡p′ x₃)}
  ... | yes p≈p′ = yes (_ , (appᵢ t⇉A (A⇒Π , Πₙ) u⇇F p≈p′))

  dec⇉-fst : ⊢ Γ → Inferable t → Dec (∃ λ A → Γ ⊢ fst t ⇉ A)
  dec⇉-fst ⊢Γ t with dec⇉ ⊢Γ t
  ... | no ¬t⇉A = no λ { (_ , fstᵢ x x₁) → ¬t⇉A (_ , x)}
  ... | yes (A , t⇉A) with isΣₚ (proj₁ (soundness⇉ ⊢Γ t⇉A))
  ... | no ¬isΣ = no λ { (_ , fstᵢ x x₁) →
    let A≡A′ = deterministic⇉ x t⇉A
        _ , ⊢Σ = syntacticRed (proj₁ x₁)
        ⊢F , ⊢G = syntacticΣ ⊢Σ
    in  ¬isΣ (_ , _ , _ , ⊢F , ⊢G , PE.subst (λ x → _ ⊢ x ⇒* _) A≡A′ (proj₁ x₁))}
  ... | yes (F , G , q , ⊢F , ⊢G , A⇒Σ) = yes (F , fstᵢ t⇉A (A⇒Σ , Σₙ))

  dec⇉-snd : ⊢ Γ → Inferable t → Dec (∃ λ A → Γ ⊢ snd t ⇉ A)
  dec⇉-snd ⊢Γ t with dec⇉ ⊢Γ t
  ... | no ¬t⇉A = no λ { (_ , sndᵢ x x₁) → ¬t⇉A (_ , x)}
  ... | yes (A , t⇉A) with isΣₚ (proj₁ (soundness⇉ ⊢Γ t⇉A))
  ... | no ¬isΣ = no λ { (_ , sndᵢ x x₁) →
    let A≡A′ = deterministic⇉ x t⇉A
        _ , ⊢Σ = syntacticRed (proj₁ x₁)
        ⊢F , ⊢G = syntacticΣ ⊢Σ
    in  ¬isΣ (_ , _ , _ , ⊢F , ⊢G , PE.subst (λ x → _ ⊢ x ⇒* _) A≡A′ (proj₁ x₁))}
  ... | yes (F , G , q , ⊢F , ⊢G , A⇒Σ) = yes (G [ _ ] , sndᵢ t⇉A (A⇒Σ , Σₙ))

  dec⇉-natrec′ : ∀ {A z s n} → ⊢ Γ → Checkable z → Checkable s → Γ ⊢ n ⇇ ℕ → Γ ∙ ℕ ⊢ A
               → Γ ∙ ℕ ⊢ A ⇇Type → Dec (∃ λ B → Γ ⊢ natrec p r A z s n ⇉ B)
  dec⇉-natrec′ ⊢Γ z s n⇇ℕ ⊢A A⇇Type with dec⇇ ⊢Γ z (substType ⊢A (zeroⱼ ⊢Γ))
      | dec⇇ (⊢Γ ∙ ℕⱼ ⊢Γ ∙ ⊢A) s (W.wk (step id) (⊢Γ ∙ ℕⱼ ⊢Γ ∙ ⊢A) (subst↑Type ⊢A (sucⱼ (var (⊢Γ ∙ ℕⱼ ⊢Γ) here))))
  ... | yes z⇇A₀ | yes s⇇A₊ = yes (_ , natrecᵢ A⇇Type z⇇A₀ s⇇A₊ n⇇ℕ)
  ... | yes z⇇A₀ | no ¬s⇇A₊ = no λ { (_ , natrecᵢ x x₁ x₂ x₃) → ¬s⇇A₊ x₂}
  ... | no ¬z⇇A₀ | _ = no λ { (_ , natrecᵢ x x₁ x₂ x₃) → ¬z⇇A₀ x₁}

  dec⇉-natrec : ∀ {A z s n} → ⊢ Γ → Checkable A → Checkable z → Checkable s → Checkable n → Dec (∃ λ B → Γ ⊢ natrec p r A z s n ⇉ B)
  dec⇉-natrec ⊢Γ A z s n with dec⇇ ⊢Γ n (ℕⱼ ⊢Γ) | dec⇇Type (⊢Γ ∙ ℕⱼ ⊢Γ) A
  ... | yes n⇇ℕ | yes A⇇Type = dec⇉-natrec′ ⊢Γ z s n⇇ℕ (soundness⇇Type (⊢Γ ∙ ℕⱼ ⊢Γ) A⇇Type) A⇇Type
  ... | yes n⇇ℕ | no ¬A⇇Type = no λ { (_ , natrecᵢ x x₁ x₂ x₃) → ¬A⇇Type x}
  ... | no ¬n⇇ℕ | _ = no λ { (_ , natrecᵢ x x₁ x₂ x₃) → ¬n⇇ℕ x₃}

  dec⇉-prodrec : ⊢ Γ → Checkable A → Inferable t → Checkable u → Dec (∃ λ B → Γ ⊢ prodrec p A t u ⇉ B)
  dec⇉-prodrec ⊢Γ A t u with dec⇉ ⊢Γ t
  ... | no ¬t⇉B = no λ { (_ , prodrecᵢ x x₁ x₂ x₃) → ¬t⇉B (_ , x₁)}
  ... | yes (B , t⇉B) with isΣᵣ (proj₁ (soundness⇉ ⊢Γ t⇉B))
  ... | no ¬isΣ = no λ { (_ , prodrecᵢ x x₁ x₂ x₃) →
    let B≡B′ = deterministic⇉ x₁ t⇉B
        _ , ⊢Σ = syntacticRed (proj₁ x₂)
        ⊢F , ⊢G = syntacticΣ ⊢Σ
    in  ¬isΣ (_ , _ , _ , ⊢F , ⊢G , PE.subst (λ x → _ ⊢ x ⇒* _) B≡B′ (proj₁ x₂))}
  ... | yes (F , G , q , ⊢F , ⊢G , B⇒Σ) with dec⇇Type (⊢Γ ∙ (Σⱼ ⊢F ▹ ⊢G)) A
  ... | no ¬A⇇Type = no λ { (_ , prodrecᵢ x x₁ x₂ x₃) →
    let B≡B′ = deterministic⇉ t⇉B x₁
        Σ≡Σ′ = whrDet* x₂ (PE.subst (λ x → _ ⊢ x ⇒* _) B≡B′ B⇒Σ , Σₙ)
        F≡F′ , G≡G′ , W≡W′ = B-PE-injectivity BΣ! BΣ! Σ≡Σ′
        q≡q′ , _ = BΣ-PE-injectivity W≡W′
    in  ¬A⇇Type (PE.subst₃ (λ x y z → _ ∙ (Σ x ▷ y ▹ z) ⊢ _ ⇇Type) q≡q′ F≡F′ G≡G′ x)}
  ... | yes A⇇Type with dec⇇ (⊢Γ ∙ ⊢F ∙ ⊢G) u (subst↑²Type (soundness⇇Type (⊢Γ ∙ (Σⱼ ⊢F ▹ ⊢G)) A⇇Type))
  ... | no ¬u⇇A₊ = no λ { (_ , prodrecᵢ x x₁ x₂ x₃) →
    let B≡B′ = deterministic⇉ t⇉B x₁
        Σ≡Σ′ = whrDet* x₂ (PE.subst (λ x → _ ⊢ x ⇒* _) B≡B′ B⇒Σ , Σₙ)
        F≡F′ , G≡G′ , W≡W′ = B-PE-injectivity BΣ! BΣ! Σ≡Σ′
    in  ¬u⇇A₊ (PE.subst₂ (λ x y → _ ∙ x ∙ y ⊢ _ ⇇ _) F≡F′ G≡G′ x₃)}
  ... | yes u⇇A₊ = yes (_ , prodrecᵢ A⇇Type t⇉B (B⇒Σ , Σₙ) u⇇A₊)

  dec⇉-Emptyrec : ⊢ Γ → Checkable A → Checkable t → Dec (∃ λ B → Γ ⊢ Emptyrec p A t ⇉ B)
  dec⇉-Emptyrec ⊢Γ A t with dec⇇Type ⊢Γ A | dec⇇ ⊢Γ t (Emptyⱼ ⊢Γ)
  ... | yes A⇇Type | yes t⇇Empty = yes (_ , Emptyrecᵢ A⇇Type t⇇Empty)
  ... | yes A⇇Type | no ¬t⇇Empty = no λ { (_ , Emptyrecᵢ x x₁) → ¬t⇇Empty x₁}
  ... | no ¬A⇇Type | _ = no λ { (_ , Emptyrecᵢ x x₁) → ¬A⇇Type x}

  -- Decidability of checking that a term is a type

  dec⇉Type : ⊢ Γ → Inferable A → Dec (Γ ⊢ A ⇇Type)
  dec⇉Type ⊢Γ Uᵢ = yes Uᶜ
  dec⇉Type ⊢Γ (Πᵢ F G) with dec⇇Type ⊢Γ F
  ... | yes F⇇Type with dec⇇Type (⊢Γ ∙ soundness⇇Type ⊢Γ F⇇Type) G
  ... | yes G⇇Type = yes (Πᶜ F⇇Type G⇇Type)
  ... | no ¬G⇇Type = no λ { (Πᶜ x x₁) → ¬G⇇Type x₁ ; (univᶜ (infᶜ (Πᵢ x x₂) x₁)) → ¬G⇇Type (univᶜ x₂)}
  dec⇉Type ⊢Γ (Πᵢ F G) | no ¬F⇇Type = no λ { (Πᶜ x x₁) → ¬F⇇Type x ; (univᶜ (infᶜ (Πᵢ x x₂) x₁)) → ¬F⇇Type (univᶜ x)}
  dec⇉Type ⊢Γ (Σᵢ F G) with dec⇇Type ⊢Γ F
  ... | yes F⇇Type with dec⇇Type (⊢Γ ∙ soundness⇇Type ⊢Γ F⇇Type) G
  ... | yes G⇇Type = yes (Σᶜ F⇇Type G⇇Type)
  ... | no ¬G⇇Type = no λ { (Σᶜ x x₁) → ¬G⇇Type x₁ ; (univᶜ (infᶜ (Σᵢ x x₂) x₁)) → ¬G⇇Type (univᶜ x₂)}
  dec⇉Type ⊢Γ (Σᵢ F G) | no ¬F⇇Type = no λ { (Σᶜ x x₁) → ¬F⇇Type x ; (univᶜ (infᶜ (Σᵢ x x₂) x₁)) → ¬F⇇Type (univᶜ x)}
  dec⇉Type ⊢Γ (varᵢ {x = x}) with dec⇇-var x (Uⱼ ⊢Γ)
  ... | yes x⇇U = yes (univᶜ x⇇U)
  ... | no ¬x⇇U = no λ { (univᶜ x) → ¬x⇇U x}
  dec⇉Type ⊢Γ (∘ᵢ t u) with dec⇉-app ⊢Γ t u
  ... | no ¬tu⇉A = no λ { (univᶜ (infᶜ x x₁)) → ¬tu⇉A (_ , x)}
  ... | yes (A , tu⇉A) with decEq (proj₁ (soundness⇉ ⊢Γ tu⇉A)) (Uⱼ ⊢Γ)
  ... | no A≢U = no λ { (univᶜ (infᶜ x x₁)) →
    let A≡A′ = deterministic⇉ x tu⇉A
    in  A≢U (PE.subst (λ x → _ ⊢ x ≡ U) A≡A′ x₁)}
  ... | yes A≡U = yes (univᶜ (infᶜ tu⇉A A≡U))
  dec⇉Type ⊢Γ (fstᵢ t) with dec⇉-fst ⊢Γ t
  ... | no ¬t₁⇉A = no λ { (univᶜ (infᶜ x x₁)) → ¬t₁⇉A (_ , x)}
  ... | yes (A , t₁⇉A) with decEq (proj₁ (soundness⇉ ⊢Γ t₁⇉A)) (Uⱼ ⊢Γ)
  ... | no A≢U = no λ { (univᶜ (infᶜ x x₁)) →
    let A≡A′ = deterministic⇉ x t₁⇉A
    in  A≢U (PE.subst (λ x → _ ⊢ x ≡ U) A≡A′ x₁)}
  ... | yes A≡U = yes (univᶜ (infᶜ t₁⇉A A≡U))
  dec⇉Type ⊢Γ (sndᵢ t) with dec⇉-snd ⊢Γ t
  ... | no ¬t₂⇉A = no λ { (univᶜ (infᶜ x x₁)) → ¬t₂⇉A (_ , x)}
  ... | yes (A , t₂⇉A) with decEq (proj₁ (soundness⇉ ⊢Γ t₂⇉A)) (Uⱼ ⊢Γ)
  ... | no A≢U = no λ { (univᶜ (infᶜ x x₁)) →
    let A≡A′ = deterministic⇉ x t₂⇉A
    in  A≢U (PE.subst (λ x → _ ⊢ x ≡ U) A≡A′ x₁)}
  ... | yes A≡U = yes (univᶜ (infᶜ t₂⇉A A≡U))
  dec⇉Type ⊢Γ (prodrecᵢ A t u) with dec⇉-prodrec ⊢Γ A t u
  ... | no ¬pr⇉B = no λ { (univᶜ (infᶜ x x₁)) → ¬pr⇉B (_ , x)}
  ... | yes (B , pr⇉B) with decEq (proj₁ (soundness⇉ ⊢Γ pr⇉B)) (Uⱼ ⊢Γ)
  ... | no B≢U = no λ { (univᶜ (infᶜ x x₁)) →
    let B≡B′ = deterministic⇉ x pr⇉B
    in  B≢U (PE.subst (λ x → _ ⊢ x ≡ U) B≡B′ x₁)}
  ... | yes B≡U = yes (univᶜ (infᶜ pr⇉B B≡U))
  dec⇉Type ⊢Γ ℕᵢ = yes ℕᶜ
  dec⇉Type ⊢Γ zeroᵢ = no λ { (univᶜ (infᶜ zeroᵢ x₁)) → U≢ℕ (sym x₁)}
  dec⇉Type ⊢Γ (sucᵢ x) = no λ { (univᶜ (infᶜ (sucᵢ x) x₁)) → U≢ℕ (sym x₁)}
  dec⇉Type ⊢Γ (natrecᵢ A z s n) with dec⇉-natrec ⊢Γ A z s n
  ... | no ¬nr⇉B = no λ { (univᶜ (infᶜ x x₁)) → ¬nr⇉B (_ , x)}
  ... | yes (B , nr⇉B) with decEq (proj₁ (soundness⇉ ⊢Γ nr⇉B)) (Uⱼ ⊢Γ)
  ... | no B≢U = no λ { (univᶜ (infᶜ x x₁)) →
    let B≡B′ = deterministic⇉ x nr⇉B
    in  B≢U (PE.subst (λ x → _ ⊢ x ≡ U) B≡B′ x₁)}
  ... | yes B≡U = yes (univᶜ (infᶜ nr⇉B B≡U))
  dec⇉Type ⊢Γ Unitᵢ = yes Unitᶜ
  dec⇉Type ⊢Γ starᵢ = no λ { (univᶜ (infᶜ starᵢ x₁)) → U≢Unitⱼ (sym x₁)}
  dec⇉Type ⊢Γ Emptyᵢ = yes Emptyᶜ
  dec⇉Type ⊢Γ (Emptyrecᵢ A t) with dec⇉-Emptyrec ⊢Γ A t
  ... | no ¬er⇉B = no λ { (univᶜ (infᶜ x x₁)) → ¬er⇉B (_ , x)}
  ... | yes (B , er⇉B) with decEq (proj₁ (soundness⇉ ⊢Γ er⇉B)) (Uⱼ ⊢Γ)
  ... | no B≢U = no λ { (univᶜ (infᶜ x x₁)) →
    let B≡B′ = deterministic⇉ x er⇉B
    in  B≢U (PE.subst (λ x → _ ⊢ x ≡ U) B≡B′ x₁)}
  ... | yes B≡U = yes (univᶜ (infᶜ er⇉B B≡U))

  dec⇇Type : ⊢ Γ → Checkable A → Dec (Γ ⊢ A ⇇Type)
  dec⇇Type ⊢Γ (lamᶜ t) = no λ { (univᶜ (lamᶜ x x₁ x₂)) → U.U≢B BΠ! (whnfRed* (proj₁ x) Uₙ)}
  dec⇇Type ⊢Γ (prodᶜ t u) = no λ { (univᶜ (prodᶜ x x₁ x₂)) → U.U≢B BΣ! (whnfRed* (proj₁ x) Uₙ)}
  dec⇇Type ⊢Γ (infᶜ x) = dec⇉Type ⊢Γ x

  -- Decidability of algorithmic type inference

  dec⇉ : ⊢ Γ → Inferable t → Dec (∃ λ A → Γ ⊢ t ⇉ A)
  dec⇉ ⊢Γ Uᵢ = no (λ { (A , ())})
  dec⇉ ⊢Γ (Πᵢ F G) with dec⇇ ⊢Γ F (Uⱼ ⊢Γ)
  ... | no ¬F⇇U = no λ { (_ , Πᵢ x x₁) → ¬F⇇U x}
  ... | yes F⇇U with dec⇇ (⊢Γ ∙ univ (soundness⇇ ⊢Γ F⇇U)) G (Uⱼ (⊢Γ ∙ univ (soundness⇇ ⊢Γ F⇇U)))
  ... | no ¬G⇇U = no λ { (_ , Πᵢ x x₁) → ¬G⇇U x₁}
  ... | yes G⇇U = yes (U , Πᵢ F⇇U G⇇U)
  dec⇉ ⊢Γ (Σᵢ F G) with dec⇇ ⊢Γ F (Uⱼ ⊢Γ)
  ... | no ¬F⇇U = no λ { (_ , Σᵢ x x₁) → ¬F⇇U x}
  ... | yes F⇇U with dec⇇ (⊢Γ ∙ univ (soundness⇇ ⊢Γ F⇇U)) G (Uⱼ (⊢Γ ∙ univ (soundness⇇ ⊢Γ F⇇U)))
  ... | no ¬G⇇U = no λ { (_ , Σᵢ x x₁) → ¬G⇇U x₁}
  ... | yes G⇇U = yes (U , Σᵢ F⇇U G⇇U)
  dec⇉ ⊢Γ varᵢ = yes (_ , varᵢ (proj₂ (dec⇉-var _)))
  dec⇉ ⊢Γ (∘ᵢ t u) = dec⇉-app ⊢Γ t u
  dec⇉ ⊢Γ (fstᵢ t) = dec⇉-fst ⊢Γ t
  dec⇉ ⊢Γ (sndᵢ t) = dec⇉-snd ⊢Γ t
  dec⇉ ⊢Γ (prodrecᵢ A t u) = dec⇉-prodrec ⊢Γ A t u
  dec⇉ ⊢Γ ℕᵢ = yes (U , ℕᵢ)
  dec⇉ ⊢Γ zeroᵢ = yes (ℕ , zeroᵢ)
  dec⇉ ⊢Γ (sucᵢ t) with dec⇇ ⊢Γ t (ℕⱼ ⊢Γ)
  ... | no ¬t⇇ℕ = no λ { (_ , sucᵢ x) → ¬t⇇ℕ x}
  ... | yes t⇇ℕ = yes (ℕ , sucᵢ t⇇ℕ)
  dec⇉ ⊢Γ (natrecᵢ A z s n) = dec⇉-natrec ⊢Γ A z s n
  dec⇉ ⊢Γ Unitᵢ = yes (U , Unitᵢ)
  dec⇉ ⊢Γ starᵢ = yes (Unit , starᵢ)
  dec⇉ ⊢Γ Emptyᵢ = yes (U , Emptyᵢ)
  dec⇉ ⊢Γ (Emptyrecᵢ A t) = dec⇉-Emptyrec ⊢Γ A t

  -- Decidability of algorithmic type checking

  dec⇇ : ⊢ Γ → Checkable t → Γ ⊢ A → Dec (Γ ⊢ t ⇇ A)
  dec⇇ ⊢Γ (lamᶜ {p = p′} t) ⊢A with isΠ ⊢A
  ... | no ¬isΠ = no λ { (lamᶜ x x₁ x₂) →
    let _ , ⊢Π = syntacticRed (proj₁ x)
        ⊢F , ⊢G = syntacticΠ ⊢Π
    in  ¬isΠ (_ , _ , _ , _ , ⊢F , ⊢G , proj₁ x)}
  ... | yes (F , G , p , q , ⊢F , ⊢G , A⇒Π) with dec⇇ (⊢Γ ∙ ⊢F) t ⊢G
  ... | no ¬t⇇G = no λ { (lamᶜ x x₁ x₂) →
    let Π≡Π′ = whrDet* x (A⇒Π , Πₙ)
        F≡F′ , G≡G′ , _ = B-PE-injectivity BΠ! BΠ! Π≡Π′
    in  ¬t⇇G (PE.subst₂ (λ x y → _ ∙ x ⊢ _ ⇇ y) F≡F′ G≡G′ x₁)}
  ... | yes t⇇G with p ≟ p′
  ... | no p≉p′ = no λ { (lamᶜ x x₁ x₂) →
    let Π≡Π′ = whrDet* x (A⇒Π , Πₙ)
        F≡F′ , G≡G′ , W≡W′ = B-PE-injectivity BΠ! BΠ! Π≡Π′
        p≡p′ , _ = BΠ-PE-injectivity W≡W′
    in  p≉p′ (PE.subst (λ x → x ≈ _) p≡p′ x₂)}
  ... | yes p≈p′ = yes (lamᶜ (A⇒Π , Πₙ) t⇇G p≈p′)
  dec⇇ ⊢Γ (prodᶜ t u) ⊢A with isΣ ⊢A
  ... | no ¬isΣ = no λ { (prodᶜ x x₁ x₂) →
    let _ , ⊢Σ = syntacticRed (proj₁ x)
        ⊢F , ⊢G = syntacticΣ ⊢Σ
    in  ¬isΣ (_ , _ , _ , _ , ⊢F , ⊢G , proj₁ x)}
  ... | yes (F , G , q , m , ⊢F , ⊢G , A⇒Σ) with dec⇇ ⊢Γ t ⊢F
  ... | no ¬t⇇F = no λ { (prodᶜ x x₁ x₂) →
    let Σ≡Σ′ = whrDet* x (A⇒Σ , Σₙ)
        F≡F′ , G≡G′ , _ = B-PE-injectivity BΣ! BΣ! Σ≡Σ′
    in  ¬t⇇F (PE.subst (λ x → _ ⊢ _ ⇇ x) F≡F′ x₁)}
  ... | yes t⇇F with dec⇇ ⊢Γ u (substType ⊢G (soundness⇇ ⊢Γ t⇇F))
  ... | no ¬u⇇Gₜ = no λ { (prodᶜ x x₁ x₂) →
    let Σ≡Σ′ = whrDet* x (A⇒Σ , Σₙ)
        F≡F′ , G≡G′ , _ = B-PE-injectivity BΣ! BΣ! Σ≡Σ′
    in  ¬u⇇Gₜ (PE.subst (λ x → _ ⊢ _ ⇇ x [ _ ]) G≡G′ x₂)}
  ... | yes u⇇Gₜ = yes (prodᶜ (A⇒Σ , Σₙ) t⇇F u⇇Gₜ)
  dec⇇ ⊢Γ (infᶜ t) ⊢A with dec⇉ ⊢Γ t
  ... | no ¬t⇉B = no λ { (infᶜ x x₁) → ¬t⇉B (_ , x)}
  ... | yes (B , t⇉B) with decEq (proj₁ (soundness⇉ ⊢Γ t⇉B)) ⊢A
  ... | no B≢A = no λ { (infᶜ x x₁) →
    let B≡B′ = deterministic⇉ x t⇉B
    in  B≢A (PE.subst (λ x → _ ⊢ x ≡ _) B≡B′ x₁)}
  ... | yes B≡A = yes (infᶜ t⇉B B≡A)
