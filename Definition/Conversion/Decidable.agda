------------------------------------------------------------------------
-- The algorithmic equality is decidable.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality
import Tools.PropositionalEquality as PE
open import Tools.Relation

module Definition.Conversion.Decidable
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  (_≟_ : Decidable (PE._≡_ {A = M}))
  where

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Conversion R
open import Definition.Conversion.Inversion R
open import Definition.Conversion.Whnf R
open import Definition.Conversion.Soundness R
open import Definition.Conversion.Symmetry R
open import Definition.Conversion.Transitivity R
open import Definition.Conversion.Stability R
open import Definition.Conversion.Conversion R
open import Definition.Typed.Consequences.DerivedRules.Identity R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Consequences.Substitution R
open import Definition.Typed.Consequences.Stability R
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Reduction R
open import Definition.Typed.Consequences.Equality R
open import Definition.Typed.Consequences.Inequality R as IE
open import Definition.Typed.Consequences.NeTypeEq R
open import Definition.Typed.Consequences.DerivedRules.Nat R

open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
open import Tools.Empty
open import Tools.Sum using (inj₁; inj₂)

private
  variable
    ℓ : Nat
    Γ Δ : Con Term ℓ
    B F G k k′ l l′ : Term ℓ
    p p′ p₁ p₂ q q′ r r′ : M


-- Algorithmic equality of variables infers propositional equality.
strongVarEq : ∀ {m n A} → Γ ⊢ var n ~ var m ↑ A → n PE.≡ m
strongVarEq (var-refl x x≡y) = x≡y

-- Helper function for decidability of applications.
dec~↑-app : ∀ {k k₁ l l₁ F F₁ G G₁ B}
          → Γ ⊢ k ∷ Π p , q ▷ F ▹ G
          → Γ ⊢ k₁ ∷ Π p , q ▷ F₁ ▹ G₁
          → Γ ⊢ k ~ k₁ ↓ B
          → p PE.≡ p′
          → Dec (Γ ⊢ l [conv↑] l₁ ∷ F)
          → Dec (∃ λ A → Γ ⊢ k ∘⟨ p ⟩ l ~ k₁ ∘⟨ p′ ⟩ l₁ ↑ A)
dec~↑-app k k₁ k~k₁ PE.refl (yes p) =
  let whnfA , neK , neL = ne~↓ k~k₁
      ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓ k~k₁)
      ΠFG₁≡A = neTypeEq neK k ⊢k
  in
  case Π≡A ΠFG₁≡A whnfA of λ {
    (H , E , A≡ΠHE) →
  case injectivity (PE.subst (λ x → _ ⊢ _ ≡ x) A≡ΠHE ΠFG₁≡A) of λ {
    (F≡H , G₁≡E , _ , _) →
  yes (E [ _ ] , app-cong (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) A≡ΠHE k~k₁)
                   (convConvTerm p F≡H)) }}
dec~↑-app k₂ k₃ k~k₁ _ (no ¬p) =
  no (λ { (_ , app-cong x x₁) →
      let whnfA , neK , neL = ne~↓ x
          ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓ x)
          ΠFG≡ΠF₂G₂ = neTypeEq neK k₂ ⊢k
          F≡F₂ , G≡G₂ , _ = injectivity ΠFG≡ΠF₂G₂
      in  ¬p (convConvTerm x₁ (sym F≡F₂)) })

-- Helper function for decidability for neutrals of natural number type.
decConv↓Term-ℕ-ins : ∀ {t u t′}
                    → Γ ⊢ t [conv↓] u ∷ ℕ
                    → Γ ⊢ t ~ t′ ↓ ℕ
                    → Γ ⊢ t ~ u ↓ ℕ
decConv↓Term-ℕ-ins (ℕ-ins x) t~t = x
decConv↓Term-ℕ-ins (ne-ins x x₁ () x₃) t~t
decConv↓Term-ℕ-ins (zero-refl x) ([~] _ _ ())
decConv↓Term-ℕ-ins (suc-cong x) ([~] _ _ ())

-- Helper function for decidability for neutrals of empty type.
decConv↓Term-Empty-ins : ∀ {t u t′}
                    → Γ ⊢ t [conv↓] u ∷ Empty
                    → Γ ⊢ t ~ t′ ↓ Empty
                    → Γ ⊢ t ~ u ↓ Empty
decConv↓Term-Empty-ins (Empty-ins x) t~t = x
decConv↓Term-Empty-ins (ne-ins x x₁ () x₃) t~t

-- Helper function for decidability for neutrals of Sigm type.
decConv↓Term-Σʷ-ins : ∀ {t t′ u F G H E}
                    → Γ ⊢ t [conv↓] u ∷ Σʷ p , q ▷ F ▹ G
                    → Γ ⊢ t ~ t′ ↓ Σʷ p′ , q′ ▷ H ▹ E
                    → ∃ λ B → Γ ⊢ t ~ u ↓ B
decConv↓Term-Σʷ-ins (Σʷ-ins x x₁ x₂) t~t = _ , x₂
decConv↓Term-Σʷ-ins (prod-cong _ _ _ _ _) ()
decConv↓Term-Σʷ-ins (ne-ins x x₁ () x₃) t~t

-- Helper function for decidability for impossibility of terms not being equal
-- as neutrals when they are equal as terms and the first is a neutral.
decConv↓Term-ℕ : ∀ {t u t′}
                → Γ ⊢ t [conv↓] u ∷ ℕ
                → Γ ⊢ t ~ t′ ↓ ℕ
                → ¬ (Γ ⊢ t ~ u ↓ ℕ)
                → ⊥
decConv↓Term-ℕ (ℕ-ins x) t~t ¬u~u = ¬u~u x
decConv↓Term-ℕ (ne-ins x x₁ () x₃) t~t ¬u~u
decConv↓Term-ℕ (zero-refl x) ([~] _ _ ()) ¬u~u
decConv↓Term-ℕ (suc-cong x) ([~] _ _ ()) ¬u~u

decConv↓Term-Σʷ : ∀ {t u t′ F G F′ G′}
                → Γ ⊢ t [conv↓] u ∷ Σʷ p , q ▷ F ▹ G
                → Γ ⊢ t ~ t′ ↓ Σʷ p′ , q′ ▷ F′ ▹ G′
                → (∀ {B} → ¬ (Γ ⊢ t ~ u ↓ B))
                → ⊥
decConv↓Term-Σʷ (Σʷ-ins x x₁ x₂) t~t ¬u~u = ¬u~u x₂
decConv↓Term-Σʷ (prod-cong _ _ _ _ _) ()
decConv↓Term-Σʷ (ne-ins x x₁ () x₃) t~t ¬u~u

-- Helper function for extensional equality of Unit.
decConv↓Term-Unit : ∀ {t t′}
              → Γ ⊢ t [conv↓] starʷ ∷ Unitʷ
              → Γ ⊢ t ~ t′ ↓ Unitʷ
              → Unitʷ-η
decConv↓Term-Unit (Unitʷ-ins _ ()) ([~] _ _ _)
decConv↓Term-Unit (η-unit _ _ _ _ (inj₁ ())) ([~] _ _ _)
decConv↓Term-Unit (η-unit _ _ _ _ (inj₂ η)) ([~] _ _ _) = η
decConv↓Term-Unit (ne-ins x x₁ () x₃) ([~] _ _ k~l)
decConv↓Term-Unit (starʷ-refl _ _ _) ()

-- Helper function for Σ-η.
decConv↓Term-Σ-η : ∀ {t u F G}
                  → Γ ⊢ t ∷ Σ p , q ▷ F ▹ G
                  → Γ ⊢ u ∷ Σ p , q ▷ F ▹ G
                  → Product t
                  → Product u
                  → Γ ⊢ fst p t [conv↑] fst p u ∷ F
                  → Dec (Γ ⊢ snd p t [conv↑] snd p u ∷ G [ fst p t ]₀)
                  → Dec (Γ ⊢ t [conv↓] u ∷ Σ p , q ▷ F ▹ G)
decConv↓Term-Σ-η ⊢t ⊢u tProd uProd fstConv (yes Q) =
  yes (Σ-η ⊢t ⊢u tProd uProd fstConv Q)
decConv↓Term-Σ-η ⊢t ⊢u tProd uProd fstConv (no ¬Q) =
  no (λ {(Σ-η _ _ _ _ _ Q) → ¬Q Q})

-- Helper function for prodrec
dec~↑-prodrec :
  ∀ {F G C E t t′ u v F′ G′ q″} →
  Dec (Γ ∙ (Σʷ p , q ▷ F ▹ G) ⊢ C [conv↑] E) →
  (Γ ∙ (Σʷ p , q ▷ F ▹ G) ⊢ C ≡ E →
    Dec (Γ ∙ F ∙ G ⊢ u [conv↑] v ∷
      C [ prodʷ p (var x1) (var x0) ]↑²)) →
  Γ ⊢ t ~ t′ ↓ Σʷ p , q ▷ F′ ▹ G′ →
  Γ ⊢ Σʷ p , q ▷ F ▹ G ≡ Σʷ p , q ▷ F′ ▹ G′ →
  p PE.≡ p′ →
  q′ PE.≡ q″ →
  r PE.≡ r′ →
  Dec (∃ λ B → Γ ⊢ prodrec r p q′ C t u ~ prodrec r′ p′ q″ E t′ v ↑ B)
dec~↑-prodrec (yes C<>E) u<?>v t~t′ ⊢Σ≡Σ′ p≡p′ q≡q′ r≡r′ =
  case u<?>v (soundnessConv↑ C<>E) of λ where
    (yes u<>v) → case p≡p′ of λ where
      PE.refl → case q≡q′ of λ where
        PE.refl → case r≡r′ of λ where
          PE.refl → case reflConEq (wfEq ⊢Σ≡Σ′) of λ ⊢Γ≡Γ →
                    case stabilityConv↑ (⊢Γ≡Γ ∙ ⊢Σ≡Σ′) C<>E of λ C<>E′ →
                    case Σ-injectivity ⊢Σ≡Σ′ of λ (⊢F≡F′ , ⊢G≡G′ , _) →
                    case stabilityConv↑Term (⊢Γ≡Γ ∙ ⊢F≡F′ ∙ ⊢G≡G′) u<>v of λ u<>v′ →
                      yes (_ , prodrec-cong C<>E′ t~t′ u<>v′)
    (no ¬u<>v) → no λ where
      (_ , prodrec-cong x x₁ x₂) →
        case syntacticEqTerm (soundness~↓ t~t′) of λ (_ , ⊢t , _) →
        case syntacticEqTerm (soundness~↓ x₁)   of λ (_ , ⊢t₁ , _) →
        case ne~↓ t~t′ of λ (_ , neT , _) →
        case neTypeEq neT ⊢t₁ ⊢t of λ ⊢Σ″≡Σ′ →
        case reflConEq (wfEq ⊢Σ″≡Σ′) of λ ⊢Γ≡Γ →
        case Σ-injectivity (trans ⊢Σ″≡Σ′ (sym ⊢Σ≡Σ′)) of λ (⊢F″≡F , ⊢G″≡G , _) →
          ¬u<>v (stabilityConv↑Term (⊢Γ≡Γ ∙ ⊢F″≡F ∙ ⊢G″≡G) x₂)
dec~↑-prodrec (no ¬C<>E) u<?>v t~t′ ⊢Σ≡Σ′ _ _ _ =  no λ where
      (_ , prodrec-cong x x₁ x₂) →
        case syntacticEqTerm (soundness~↓ t~t′) of λ (_ , ⊢t , _) →
        case syntacticEqTerm (soundness~↓ x₁)   of λ (_ , ⊢t₁ , _) →
        case ne~↓ t~t′ of λ (_ , neT , _) →
        case neTypeEq neT ⊢t₁ ⊢t of λ ⊢Σ″≡Σ′ →
        case reflConEq (wfEq ⊢Σ″≡Σ′) of λ ⊢Γ≡Γ →
          ¬C<>E (stabilityConv↑ (⊢Γ≡Γ ∙ trans ⊢Σ″≡Σ′ (sym ⊢Σ≡Σ′)) x)

dec~↑-var : ∀ {k k′ A}
          → (x : Fin _)
          → Γ ⊢ k ~ k′ ↑ A
          → Dec (∃ λ B → Γ ⊢ var x ~ k ↑ B)
dec~↑-var x (var-refl {x = y} x₁ x₂) with x ≟ⱽ y
... | yes PE.refl = yes (_ , var-refl x₁ PE.refl)
... | no ¬p = no λ { (_ , var-refl x x₁) → ¬p x₁}
dec~↑-var x (app-cong _ _) = no λ { (_ , ())}
dec~↑-var x (fst-cong _) = no λ { (_ , ())}
dec~↑-var x (snd-cong _) = no λ { (_ , ())}
dec~↑-var x (natrec-cong _ _ _ _) = no λ { (_ , ())}
dec~↑-var x (prodrec-cong _ _ _) = no λ { (_ , ())}
dec~↑-var x (emptyrec-cong _ _) = no λ { (_ , ())}
dec~↑-var x (unitrec-cong _ _ _ _) = no λ { (_ , ())}
dec~↑-var _ (J-cong _ _ _ _ _ _ _) = no λ { (_ , ()) }
dec~↑-var _ (K-cong _ _ _ _ _ _ _) = no λ { (_ , ()) }
dec~↑-var _ ([]-cong-cong _ _ _ _ _ _) = no λ { (_ , ()) }

dec~↑-app′ : ∀ {k l l′ a A F G}
          → Γ ⊢ l ~ l′ ↑ A
          → (∀ {l l′ B} → Γ ⊢ l ~ l′ ↓ B → Dec (∃ λ C → Γ ⊢ k ~ l ↓ C))
          → (∀ {F′ u u′} → Γ ⊢ F ≡ F′ → Γ ⊢ u [conv↑] u′ ∷ F′
                           → Dec (Γ ⊢ a [conv↑] u ∷ F))
          → Γ ⊢ k ∷ Π p , q ▷ F ▹ G
          → p PE.≡ p₁
          → Dec (∃ λ C → Γ ⊢ k ∘⟨ p₁ ⟩ a ~ l ↑ C)
dec~↑-app′ (app-cong x x₁) dec dec′ ⊢l₁ p≡p₁ with dec x
... | no ¬p = no λ{ (_ , app-cong x x₁) → ¬p (_ , x)}
dec~↑-app′ (app-cong x x₁) _ dec′ ⊢l₁ PE.refl | yes (C , k~l) =
  let whnfA , neK , neL = ne~↓ k~l
      ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓ k~l)
      _ , ⊢l₂ , _ = syntacticEqTerm (soundness~↓ x)
      ΠFG≡A = neTypeEq neK ⊢l₁ ⊢k
      ΠF′G′≡A = neTypeEq neL ⊢l₂ ⊢l
  in
  case injectivity (trans ΠFG≡A (sym ΠF′G′≡A)) of λ {
    (F≡F′ , G≡G′ , PE.refl , _) →
  case conv ⊢l₂ (trans ΠF′G′≡A (sym ΠFG≡A)) of λ {
    ⊢l₂′ →
  dec~↑-app ⊢l₁ ⊢l₂′ k~l PE.refl (dec′ F≡F′ x₁) }}
dec~↑-app′ (var-refl x x₁) _ _ _ _ = no λ { (_ , ())}
dec~↑-app′ (fst-cong x) _ _ _ _ = no λ { (_ , ())}
dec~↑-app′ (snd-cong x) _ _ _ _ = no λ { (_ , ())}
dec~↑-app′ (natrec-cong x x₁ x₂ x₃) _ _ _ _ = no λ { (_ , ())}
dec~↑-app′ (prodrec-cong x x₁ x₂) _ _ _ _ = no λ { (_ , ())}
dec~↑-app′ (emptyrec-cong x x₁) _ _ _ _ = no λ { (_ , ())}
dec~↑-app′ (unitrec-cong _ _ _ _) _ _ _ _ = no λ { (_ , ())}
dec~↑-app′ (J-cong _ _ _ _ _ _ _) _ _ _ _ = no λ { (_ , ()) }
dec~↑-app′ (K-cong _ _ _ _ _ _ _) _ _ _ _ = no λ { (_ , ()) }
dec~↑-app′ ([]-cong-cong _ _ _ _ _ _) _ _ _ _ = no λ { (_ , ()) }

dec~↑-fst :
  Γ ⊢ k ~ k′ ↓ Σˢ p , q ▷ F ▹ G →
  (∀ {l l′ B} → Γ ⊢ l ~ l′ ↓ B → Dec (∃ λ A → Γ ⊢ k ~ l ↓ A)) →
  Γ ⊢ l ~ l′ ↑ B →
  Dec (∃ λ A → Γ ⊢ fst p k ~ l ↑ A)
dec~↑-fst k~k dec (fst-cong l~l) with dec l~l
... | yes (A , k~l) =
  case ne~↓ k~l of λ (whnfA , neK , neL) →
  case syntacticEqTerm (soundness~↓ k~l) of λ (⊢A , ⊢k , ⊢l) →
  case syntacticEqTerm (soundness~↓ k~k) of λ (_ , ⊢k₁ , _) →
  case syntacticEqTerm (soundness~↓ l~l) of λ (_ , ⊢l₁ , _) →
  case neTypeEq neK ⊢k₁ ⊢k of λ ΣFG≡A →
  case neTypeEq neL ⊢l₁ ⊢l of λ ΣF′G′≡A →
  case Σ≡A ΣFG≡A whnfA of λ where
    (F , _ , PE.refl) →
      case Σ-injectivity ΣF′G′≡A of λ where
        (_ , _ , PE.refl , _ , _) →
          yes (F , fst-cong k~l)
... | no ¬p = no (λ { (_ , fst-cong x) → ¬p (_ , x) })
dec~↑-fst _ _ (var-refl _ _)             = no λ { (_ , ()) }
dec~↑-fst _ _ (app-cong _ _)             = no λ { (_ , ()) }
dec~↑-fst _ _ (snd-cong _)               = no λ { (_ , ()) }
dec~↑-fst _ _ (natrec-cong _ _ _ _)      = no λ { (_ , ()) }
dec~↑-fst _ _ (prodrec-cong _ _ _)       = no λ { (_ , ()) }
dec~↑-fst _ _ (emptyrec-cong _ _)        = no λ { (_ , ()) }
dec~↑-fst _ _ (unitrec-cong _ _ _ _)     = no λ { (_ , ()) }
dec~↑-fst _ _ (J-cong _ _ _ _ _ _ _)     = no λ { (_ , ()) }
dec~↑-fst _ _ (K-cong _ _ _ _ _ _ _)     = no λ { (_ , ()) }
dec~↑-fst _ _ ([]-cong-cong _ _ _ _ _ _) = no λ { (_ , ()) }

dec~↑-snd :
  Γ ⊢ k ~ k′ ↓ Σˢ p , q ▷ F ▹ G →
  (∀ {l l′ B} → Γ ⊢ l ~ l′ ↓ B → Dec (∃ λ A → Γ ⊢ k ~ l ↓ A)) →
  Γ ⊢ l ~ l′ ↑ B →
  Dec (∃ λ A → Γ ⊢ snd p k ~ l ↑ A)
dec~↑-snd {k = k} k~k dec (snd-cong l~l) with dec l~l
... | yes (A , k~l) =
  case ne~↓ k~l of λ (whnfA , neK , neL) →
  case syntacticEqTerm (soundness~↓ k~l) of λ (⊢A , ⊢k , ⊢l) →
  case syntacticEqTerm (soundness~↓ k~k) of λ (_ , ⊢k₁ , _) →
  case syntacticEqTerm (soundness~↓ l~l) of λ (_ , ⊢l₁ , _) →
  case neTypeEq neK ⊢k₁ ⊢k of λ ΣFG≡A →
  case neTypeEq neL ⊢l₁ ⊢l of λ ΣF′G′≡A →
  case Σ≡A ΣFG≡A whnfA of λ where
    (_ , G , PE.refl) →
      case Σ-injectivity ΣF′G′≡A of λ where
        (_ , _ , PE.refl , _ , _) →
          yes (G [ fst _ k ]₀ , snd-cong k~l)
... | no ¬p = no (λ { (_ , snd-cong x₂) → ¬p (_ , x₂) })
dec~↑-snd _ _ (var-refl _ _)             = no λ { (_ , ()) }
dec~↑-snd _ _ (app-cong _ _)             = no λ { (_ , ()) }
dec~↑-snd _ _ (fst-cong _)               = no λ { (_ , ()) }
dec~↑-snd _ _ (natrec-cong _ _ _ _)      = no λ { (_ , ()) }
dec~↑-snd _ _ (prodrec-cong _ _ _)       = no λ { (_ , ()) }
dec~↑-snd _ _ (emptyrec-cong _ _)        = no λ { (_ , ()) }
dec~↑-snd _ _ (unitrec-cong _ _ _ _)     = no λ { (_ , ()) }
dec~↑-snd _ _ (J-cong _ _ _ _ _ _ _)     = no λ { (_ , ()) }
dec~↑-snd _ _ (K-cong _ _ _ _ _ _ _)     = no λ { (_ , ()) }
dec~↑-snd _ _ ([]-cong-cong _ _ _ _ _ _) = no λ { (_ , ()) }

dec~↑-natrec : ∀ {l l′ A C z s n}
             → Γ ⊢ l ~ l′ ↑ A
             → ⊢ Γ
             → (∀ {C′ C″} → Γ ∙ ℕ ⊢ C′ [conv↑] C″ → Dec (Γ ∙ ℕ ⊢ C [conv↑] C′))
             → (∀ {t t′ C′} → Γ ⊢ C [ zero ]₀ ≡ C′ → Γ ⊢ t [conv↑] t′ ∷ C′ → Dec (Γ ⊢ z [conv↑] t ∷ C [ zero ]₀))
             → (∀ {t t′ C′} → Γ ∙ ℕ ∙ C ⊢ C [ suc (var x1) ]↑² ≡ C′ → Γ ∙ ℕ ∙ C ⊢ t [conv↑] t′ ∷ C′
                            → Dec (Γ ∙ ℕ ∙ C ⊢ s [conv↑] t ∷ C [ suc (var x1) ]↑²))
             → (∀ {t t′ C′} → Γ ⊢ t ~ t′ ↓ C′ → Dec (∃ λ B → Γ ⊢ n ~ t ↓ B))
             → Dec (∃ λ B → Γ ⊢ natrec p q r C z s n ~ l ↑ B)
dec~↑-natrec {p = p} {q = q} {r = r}
  (natrec-cong {p = p′} {q = q′} {r = r′} x x₁ x₂ x₃)
  ⊢Γ decC decZ decS decN
  with decC x | decN x₃ | p ≟ p′ | q ≟ q′ | r ≟ r′
... | _ | _ | _ | _ | no r≢r′ = no λ {(_ , natrec-cong _ _ _ _) → r≢r′ PE.refl}
... | _ | _ | _ | no q≢q′ | _ = no λ {(_ , natrec-cong _ _ _ _) → q≢q′ PE.refl}
... | _ | _ | no p≢p′ | _ | _ = no λ {(_ , natrec-cong _ _ _ _) → p≢p′ PE.refl}
... | _ | no ¬P | _ | _ | _ = no λ {(_ , natrec-cong _ _ _ x) → ¬P (_ , x)}
... | no ¬P | _ | _ | _ | _ = no λ {(_ , natrec-cong x _ _ _) → ¬P x}
... | yes C<>C′ | yes (B , n~n′) | yes _ | yes _ | yes _
  with decZ (substTypeEq (soundnessConv↑ C<>C′) (refl (zeroⱼ ⊢Γ))) x₁
     | decS (sucCong (soundnessConv↑ C<>C′))
            (stabilityConv↑Term ((reflConEq (⊢Γ ∙ ℕⱼ ⊢Γ)) ∙ (sym (soundnessConv↑ C<>C′))) x₂)
... | _ | no ¬P = no λ {(_ , natrec-cong _ _ x _) → ¬P x}
... | no ¬P | _ = no λ {(_ , natrec-cong _ x _ _) → ¬P x}
dec~↑-natrec (natrec-cong _ _ _ x₃) _ _ _ _ _
  | yes C<>C′ | yes (B , n~n′) | yes PE.refl | yes PE.refl | yes PE.refl
  | yes z<>z′ | yes s<>s′ =
  let whnfA , neN , neN′ = ne~↓ n~n′
      ⊢A , ⊢n , ⊢n′ = syntacticEqTerm (soundness~↓ n~n′)
      _ , ⊢n′∷ℕ , _ = syntacticEqTerm (soundness~↓ x₃)
      ⊢ℕ≡A = neTypeEq neN′ ⊢n′∷ℕ ⊢n′
      A≡ℕ = ℕ≡A ⊢ℕ≡A whnfA
      n~n″ = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) A≡ℕ n~n′
  in  yes (_ , natrec-cong C<>C′ z<>z′ s<>s′ n~n″)
dec~↑-natrec (var-refl _ _) _ _ _ _ _             = no λ {(_ , ())}
dec~↑-natrec (app-cong _ _) _ _ _ _ _             = no λ {(_ , ())}
dec~↑-natrec (fst-cong _) _ _ _ _ _               = no λ {(_ , ())}
dec~↑-natrec (snd-cong _) _ _ _ _ _               = no λ {(_ , ())}
dec~↑-natrec (prodrec-cong _ _ _) _ _ _ _ _       = no λ {(_ , ())}
dec~↑-natrec (emptyrec-cong _ _) _ _ _ _ _        = no λ {(_ , ())}
dec~↑-natrec (unitrec-cong _ _ _ _) _ _ _ _ _     = no λ {(_ , ())}
dec~↑-natrec (J-cong _ _ _ _ _ _ _) _ _ _ _ _     = no λ {(_ , ())}
dec~↑-natrec (K-cong _ _ _ _ _ _ _) _ _ _ _ _     = no λ {(_ , ())}
dec~↑-natrec ([]-cong-cong _ _ _ _ _ _) _ _ _ _ _ = no λ {(_ , ())}

mutual
  -- Decidability of algorithmic equality of neutrals.
  dec~↑ : ∀ {k l R T k′ l′}
        → Γ ⊢ k ~ k′ ↑ R → Γ ⊢ l ~ l′ ↑ T
        → Dec (∃ λ A → Γ ⊢ k ~ l ↑ A)
  dec~↑ (var-refl x x₁) y = dec~↑-var _ y
  dec~↑ (app-cong x x₁) y =
    dec~↑-app′ y (dec~↓ x) (λ F≡F′ → decConv↑TermConv F≡F′ x₁)
      (proj₁ (proj₂ (syntacticEqTerm (soundness~↓ x)))) PE.refl
  dec~↑ (fst-cong k~k) l~l =
    dec~↑-fst k~k (dec~↓ k~k) l~l
  dec~↑ (snd-cong k~k) l~l =
    dec~↑-snd k~k (dec~↓ k~k) l~l
  dec~↑ (natrec-cong x x₁ x₂ x₃) y =
    dec~↑-natrec y (wfEqTerm (soundness~↑ y)) (decConv↑ x)
                 (λ z → decConv↑TermConv z x₁)
                 (λ z → decConv↑TermConv z x₂) (dec~↓ x₃)

  dec~↑ (unitrec-cong {p = p} {q = q} x x₁ x₂ no-η)
        (unitrec-cong {p = p′} {q = q′} x₃ x₄ x₅ _) =
    case dec~↓ x₁ x₄ of λ where
      (no ¬p) → no λ{ (_ , unitrec-cong x x₁ x₂ _) → ¬p (_ , x₁)}
      (yes (A , k~k′)) → case (decConv↑ x x₃) of λ where
        (no ¬p) → no λ{ (_ , unitrec-cong x x₁ x₂ _) → ¬p x}
        (yes F<>F′) →
          let F≡F′ = soundnessConv↑ F<>F′
              k≡l = soundness~↓ x₁
              ⊢Unit , ⊢k , _ = syntacticEqTerm k≡l
              ok = inversion-Unit ⊢Unit
              ⊢Γ = wf ⊢Unit
              F₊≡F′₊ = substTypeEq F≡F′ (refl (starⱼ ⊢Γ ok))
              _ , ⊢k′ , _ = syntacticEqTerm (soundness~↓ k~k′)
              whA , neK , _ = ne~↓ k~k′
              A≡Unit = neTypeEq neK ⊢k ⊢k′
              k~k″ = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x)
                              (Unit≡A A≡Unit whA)
                              k~k′
          in  case (decConv↑Term x₂ (convConv↑Term (reflConEq ⊢Γ) (sym F₊≡F′₊) x₅)) of λ where
            (no ¬p) → no λ{ (_ , unitrec-cong x x₁ x₂ _) → ¬p x₂}
            (yes u<>u′) → case p ≟ p′ of λ where
              (no p≉p′) →
                no λ { (_ , unitrec-cong x x₁ x₂ _) → p≉p′ PE.refl }
              (yes p≈p′) → case q ≟ q′ of λ where
                (no q≉q′) →
                  no λ { (_ , unitrec-cong x x₁ x₂ _) → q≉q′ PE.refl }
                (yes PE.refl) → case p≈p′ of λ where
                  PE.refl → yes (_ , unitrec-cong F<>F′ k~k″ u<>u′ no-η)

  dec~↑
    (prodrec-cong {p = p}  {r = r}  {q′ = q}  x  x₁ x₂)
    (prodrec-cong {p = p′} {r = r′} {q′ = q′} x₃ x₄ x₅)
    with dec~↓ x₁ x₄ | r ≟ r′ | p ≟ p′ | q ≟ q′
  ... | yes (B , t~t′) | yes PE.refl | yes PE.refl | yes PE.refl =
    case ne~↓ t~t′ of λ (whnfB , neT , neT′) →
    case syntacticEqTerm (soundness~↓ t~t′) of λ (⊢B , ⊢t , ⊢t′) →
    case syntacticEqTerm (soundness~↓ x₁) of λ (⊢Σ , ⊢t₁ , ⊢w) →
    case syntacticEqTerm (soundness~↓ x₄) of λ (⊢Σ′ , ⊢t′₁ , ⊢w′) →
    case neTypeEq neT ⊢t ⊢t₁ of λ ⊢B≡Σ →
    case neTypeEq neT′ ⊢t′ ⊢t′₁ of λ ⊢B≡Σ′ →
    case Σ≡A (sym ⊢B≡Σ) whnfB of λ where
      (_ , _ , PE.refl) →
        case trans (sym ⊢B≡Σ′) ⊢B≡Σ of λ ⊢Σ′≡Σ →
        case Σ-injectivity ⊢Σ′≡Σ of λ where
          (⊢F′≡F , ⊢G′≡G , _ , PE.refl , _) → case Σ-injectivity ⊢B≡Σ′ of  λ where
            (⊢F′≡F″ , _ , _ , _ , _) →
              case reflConEq (wf ⊢B) of λ ⊢Γ≡Γ →
                dec~↑-prodrec
                  (decConv↑ x (stabilityConv↑ (⊢Γ≡Γ ∙ ⊢Σ′≡Σ) x₃))
                  (λ C≡C′ → decConv↑TermConv
                     (subst↑²TypeEq-prod C≡C′ (⊢∷ΠΣ→ΠΣ-allowed ⊢t₁))
                     x₂
                     (stabilityConv↑Term (⊢Γ≡Γ ∙ ⊢F′≡F ∙ ⊢G′≡G) x₅))
                  t~t′ (sym ⊢B≡Σ) PE.refl PE.refl PE.refl
  ... | no ¬P | _ | _ | _ =
    no (λ { (_ , prodrec-cong _ x _) → ¬P (_ , x) })
  ... | _ | no ¬r≡r′ | _ | _ =
    no (λ { (_ , prodrec-cong _ _ _) → ¬r≡r′ PE.refl })
  ... | _ | _ | no ¬p≡p′ | _ =
    no (λ { (_ , prodrec-cong _ _ _) → ¬p≡p′ PE.refl })
  ... | _ | _ | _ | no ¬q≡q′ =
    no (λ { (_ , prodrec-cong _ _ _) → ¬q≡q′ PE.refl })
  dec~↑ (prodrec-cong _ _ _) (var-refl _ _) = no λ { (_ , ()) }
  dec~↑ (prodrec-cong _ _ _) (app-cong _ _) = no λ { (_ , ()) }
  dec~↑ (prodrec-cong _ _ _) (fst-cong _) = no λ { (_ , ()) }
  dec~↑ (prodrec-cong _ _ _) (snd-cong _) = no λ { (_ , ()) }
  dec~↑ (prodrec-cong _ _ _) (natrec-cong _ _ _ _) = no λ { (_ , ()) }
  dec~↑ (prodrec-cong _ _ _) (emptyrec-cong _ _) = no λ { (_ , ()) }
  dec~↑ (prodrec-cong _ _ _) (unitrec-cong _ _ _ _) = no λ{(_ , ())}
  dec~↑ (prodrec-cong _ _ _) (J-cong _ _ _ _ _ _ _) = no λ { (_ , ()) }
  dec~↑ (prodrec-cong _ _ _) (K-cong _ _ _ _ _ _ _) = no λ { (_ , ()) }
  dec~↑ (prodrec-cong _ _ _) ([]-cong-cong _ _ _ _ _ _) =
    no λ { (_ , ()) }

  dec~↑ (emptyrec-cong {p = p′} x x₁) (emptyrec-cong {p = p″} x₄ x₅)
        with decConv↑ x x₄ | dec~↓ x₁ x₅ | p′ ≟ p″
  ... | yes p | yes (A , k~l) | yes PE.refl =
    let whnfA , neK , neL = ne~↓ k~l
        ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓ k~l)
        _ , ⊢l∷Empty , _ = syntacticEqTerm (soundness~↓ x₁)
        ⊢Empty≡A = neTypeEq neK ⊢l∷Empty ⊢k
        A≡Empty = Empty≡A ⊢Empty≡A whnfA
        k~l′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) A≡Empty k~l
    in  yes (_ , emptyrec-cong p k~l′)
  ... | yes p | yes (A , k~l) | no ¬p′≡p″ =
    no (λ { (_ , emptyrec-cong _ _) → ¬p′≡p″ PE.refl })
  ... | yes p | no ¬p | _ =
    no (λ { (_ , emptyrec-cong _ b) → ¬p (_ , b) })
  ... | no ¬p | r | _ = no (λ { (_ , emptyrec-cong a _) → ¬p a })
  dec~↑ (emptyrec-cong _ _) (var-refl _ _) = no (λ { (_ , ()) })
  dec~↑ (emptyrec-cong _ _) (fst-cong _) = no (λ { (_ , ()) })
  dec~↑ (emptyrec-cong _ _) (snd-cong _) = no (λ { (_ , ()) })
  dec~↑ (emptyrec-cong _ _) (app-cong _ _) = no (λ { (_ , ()) })
  dec~↑ (emptyrec-cong _ _) (natrec-cong _ _ _ _) = no (λ { (_ , ()) })
  dec~↑ (emptyrec-cong _ _) (prodrec-cong _ _ _) = no λ{(_ , ())}
  dec~↑ (emptyrec-cong _ _) (unitrec-cong _ _ _ _) = no λ{(_ , ())}
  dec~↑ (emptyrec-cong _ _) (J-cong _ _ _ _ _ _ _) = no λ { (_ , ()) }
  dec~↑ (emptyrec-cong _ _) (K-cong _ _ _ _ _ _ _) = no λ { (_ , ()) }
  dec~↑ (emptyrec-cong _ _) ([]-cong-cong _ _ _ _ _ _) =
    no λ { (_ , ()) }
  dec~↑ (unitrec-cong _ _ _ _) (var-refl _ _) = no λ{(_ , ())}
  dec~↑ (unitrec-cong _ _ _ _) (app-cong _ _) = no λ{(_ , ())}
  dec~↑ (unitrec-cong _ _ _ _) (fst-cong _) = no λ{(_ , ())}
  dec~↑ (unitrec-cong _ _ _ _) (snd-cong _) = no λ{(_ , ())}
  dec~↑ (unitrec-cong _ _ _ _) (natrec-cong _ _ _ _) = no λ{(_ , ())}
  dec~↑ (unitrec-cong _ _ _ _) (prodrec-cong _ _ _) = no λ{(_ , ())}
  dec~↑ (unitrec-cong _ _ _ _) (emptyrec-cong _ _) = no λ{(_ , ())}
  dec~↑ (unitrec-cong _ _ _ _) (J-cong _ _ _ _ _ _ _) = no λ { (_ , ()) }
  dec~↑ (unitrec-cong _ _ _ _) (K-cong _ _ _ _ _ _ _) = no λ { (_ , ()) }
  dec~↑ (unitrec-cong _ _ _ _) ([]-cong-cong _ _ _ _ _ _) =
    no λ { (_ , ()) }
  dec~↑
    (J-cong {p = p₁} {q = q₁} A₁≡A₃ t₁≡t₃ B₁≡B₃ u₁≡u₃ v₁≡v₃ w₁~w₃
       C₁≡Id-t₁-v₁)
    (J-cong {p = p₂} {q = q₂} A₂≡A₄ t₂≡t₄ B₂≡B₄ u₂≡u₄ v₂≡v₄ w₂~w₄ _) =
    case p₁ ≟ p₂ of λ {
      (no p₁≢p₂) → no $
        p₁≢p₂ ∘→ proj₁ ∘→ proj₂ ∘→ J-cong⁻¹ ∘→ proj₂
    ; (yes PE.refl) →
    case q₁ ≟ q₂ of λ {
      (no q₁≢q₂) → no $
        q₁≢q₂ ∘→ proj₁ ∘→ proj₂ ∘→ proj₂ ∘→ J-cong⁻¹ ∘→ proj₂
    ; (yes PE.refl) →
    case decConv↑ A₁≡A₃ A₂≡A₄ of λ {
      (no A₁≢A₂) → no $
        A₁≢A₂ ∘→ proj₁ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ J-cong⁻¹ ∘→ proj₂
    ; (yes A₁≡A₂) →
    case soundnessConv↑ A₁≡A₂ of λ {
      ⊢A₁≡A₂ →
    case decConv↑TermConv ⊢A₁≡A₂ t₁≡t₃ t₂≡t₄ of λ {
      (no t₁≢t₂) → no $
        t₁≢t₂ ∘→ proj₁ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→
        J-cong⁻¹ ∘→ proj₂
    ; (yes t₁≡t₂) →
    case soundnessConv↑Term t₁≡t₂ of λ {
      ⊢t₁≡t₂ →
    case decConv↑′ (J-motive-context-cong′ ⊢A₁≡A₂ ⊢t₁≡t₂)
           B₁≡B₃ B₂≡B₄ of λ {
      (no B₁≢B₂) → no $
        B₁≢B₂ ∘→ proj₁ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→
        J-cong⁻¹ ∘→ proj₂
    ; (yes B₁≡B₂) →
    case decConv↑TermConv
           (J-motive-rfl-cong (soundnessConv↑ B₁≡B₂) ⊢t₁≡t₂)
           u₁≡u₃ u₂≡u₄ of λ {
      (no u₁≢u₂) → no $
        u₁≢u₂ ∘→ proj₁ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→
        proj₂ ∘→ J-cong⁻¹ ∘→ proj₂
    ; (yes u₁≡u₂) →
    case decConv↑TermConv ⊢A₁≡A₂ v₁≡v₃ v₂≡v₄ of λ {
      (no v₁≢v₂) → no $
        v₁≢v₂ ∘→ proj₁ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→
        proj₂ ∘→ proj₂ ∘→ J-cong⁻¹ ∘→ proj₂
    ; (yes v₁≡v₂) →
    case dec~↓ w₁~w₃ w₂~w₄ of λ {
      (no ¬w₁~w₂) → no $
        ¬w₁~w₂ ∘→ (_ ,_) ∘→ proj₁ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→
        proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ J-cong⁻¹ ∘→ proj₂
    ; (yes (_ , w₁~w₂)) →
    case neTypeEq (ne~↓ w₁~w₂ .proj₂ .proj₁)
           (syntacticEqTerm (soundness~↓ w₁~w₃) .proj₂ .proj₁)
           (syntacticEqTerm (soundness~↓ w₁~w₂) .proj₂ .proj₁) of λ {
      C₁≡D →
    yes
      ( _
      , J-cong A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁~w₂
          (trans (sym C₁≡D) C₁≡Id-t₁-v₁)
      ) }}}}}}}}}}}
  dec~↑ (J-cong _ _ _ _ _ _ _) (var-refl _ _) = no (λ { (_ , ()) })
  dec~↑ (J-cong _ _ _ _ _ _ _) (fst-cong _) = no (λ { (_ , ()) })
  dec~↑ (J-cong _ _ _ _ _ _ _) (snd-cong _) = no (λ { (_ , ()) })
  dec~↑ (J-cong _ _ _ _ _ _ _) (app-cong _ _) = no (λ { (_ , ()) })
  dec~↑ (J-cong _ _ _ _ _ _ _) (natrec-cong _ _ _ _) = no (λ { (_ , ()) })
  dec~↑ (J-cong _ _ _ _ _ _ _) (prodrec-cong _ _ _) = no λ{(_ , ())}
  dec~↑ (J-cong _ _ _ _ _ _ _) (emptyrec-cong _ _) = no λ { (_ , ()) }
  dec~↑ (J-cong _ _ _ _ _ _ _) (unitrec-cong _ _ _ _) = no λ { (_ , ()) }
  dec~↑ (J-cong _ _ _ _ _ _ _) (K-cong _ _ _ _ _ _ _) = no λ { (_ , ()) }
  dec~↑ (J-cong _ _ _ _ _ _ _) ([]-cong-cong _ _ _ _ _ _) = no λ { (_ , ()) }

  dec~↑ (K-cong {p = p₁} A₁≡A₃ t₁≡t₃ B₁≡B₃ u₁≡u₃ v₁~v₃ C₁≡Id-t₁-t₁ ok)
     (K-cong {p = p₂} A₂≡A₄ t₂≡t₄ B₂≡B₄ u₂≡u₄ v₂~v₄ _ _) =
    case p₁ ≟ p₂ of λ {
      (no p₁≢p₂) → no $
        p₁≢p₂ ∘→ proj₁ ∘→ proj₂ ∘→ K-cong⁻¹ ∘→ proj₂
    ; (yes PE.refl) →
    case decConv↑ A₁≡A₃ A₂≡A₄ of λ {
      (no A₁≢A₂) → no $
        A₁≢A₂ ∘→ proj₁ ∘→ proj₂ ∘→ proj₂ ∘→ K-cong⁻¹ ∘→ proj₂
    ; (yes A₁≡A₂) →
    case soundnessConv↑ A₁≡A₂ of λ {
      ⊢A₁≡A₂ →
    case decConv↑TermConv ⊢A₁≡A₂ t₁≡t₃ t₂≡t₄ of λ {
      (no t₁≢t₂) → no $
        t₁≢t₂ ∘→ proj₁ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ K-cong⁻¹ ∘→ proj₂
    ; (yes t₁≡t₂) →
    case decConv↑′
           (K-motive-context-cong′ ⊢A₁≡A₂ (soundnessConv↑Term t₁≡t₂))
           B₁≡B₃ B₂≡B₄ of λ {
      (no B₁≢B₂) → no $
        B₁≢B₂ ∘→ proj₁ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→
        K-cong⁻¹ ∘→ proj₂
    ; (yes B₁≡B₂) →
    case decConv↑TermConv (K-motive-rfl-cong (soundnessConv↑ B₁≡B₂))
           u₁≡u₃ u₂≡u₄ of λ {
      (no u₁≢u₂) → no $
        u₁≢u₂ ∘→ proj₁ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→
        K-cong⁻¹ ∘→ proj₂
    ; (yes u₁≡u₂) →
    case dec~↓ v₁~v₃ v₂~v₄ of λ {
      (no ¬v₁~v₂) → no $
        ¬v₁~v₂ ∘→ (_ ,_) ∘→ proj₁ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→
        proj₂ ∘→ proj₂ ∘→ K-cong⁻¹ ∘→ proj₂
    ; (yes (_ , v₁~v₂)) →
    case neTypeEq (ne~↓ v₁~v₂ .proj₂ .proj₁)
           (syntacticEqTerm (soundness~↓ v₁~v₃) .proj₂ .proj₁)
           (syntacticEqTerm (soundness~↓ v₁~v₂) .proj₂ .proj₁) of λ {
      C₁≡D →
    yes
      ( _
      , K-cong A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁~v₂
          (trans (sym C₁≡D) C₁≡Id-t₁-t₁) ok
      ) }}}}}}}}
  dec~↑ (K-cong _ _ _ _ _ _ _) (var-refl _ _) = no (λ { (_ , ()) })
  dec~↑ (K-cong _ _ _ _ _ _ _) (fst-cong _) = no (λ { (_ , ()) })
  dec~↑ (K-cong _ _ _ _ _ _ _) (snd-cong _) = no (λ { (_ , ()) })
  dec~↑ (K-cong _ _ _ _ _ _ _) (app-cong _ _) = no (λ { (_ , ()) })
  dec~↑ (K-cong _ _ _ _ _ _ _) (natrec-cong _ _ _ _) = no (λ { (_ , ()) })
  dec~↑ (K-cong _ _ _ _ _ _ _) (prodrec-cong _ _ _) = no λ{(_ , ())}
  dec~↑ (K-cong _ _ _ _ _ _ _) (emptyrec-cong _ _) = no λ { (_ , ()) }
  dec~↑ (K-cong _ _ _ _ _ _ _) (unitrec-cong _ _ _ _) = no λ { (_ , ()) }
  dec~↑ (K-cong _ _ _ _ _ _ _) (J-cong _ _ _ _ _ _ _) = no λ { (_ , ()) }
  dec~↑ (K-cong _ _ _ _ _ _ _) ([]-cong-cong _ _ _ _ _ _) = no λ { (_ , ()) }

  dec~↑ ([]-cong-cong {s = s} A₁≡A₃ t₁≡t₃ u₁≡u₃ v₁~v₃ B₁≡Id-t₁-u₁ ok)
     ([]-cong-cong {s = s′} A₂≡A₄ t₂≡t₄ u₂≡u₄ v₂~v₄ _ _) =
    case decConv↑ A₁≡A₃ A₂≡A₄ of λ where
      (no A₁≢A₂) → no λ where
        (_ , []-cong-cong A₁≡A₂ _ _ _ _ _) → A₁≢A₂ A₁≡A₂
      (yes A₁≡A₂) → case decConv↑TermConv (soundnessConv↑ A₁≡A₂)
                           t₁≡t₃ t₂≡t₄ of λ where
        (no t₁≢t₂) → no λ where
          (_ , []-cong-cong _ t₁≡t₂ _ _ _ _) → t₁≢t₂ t₁≡t₂
        (yes t₁≡t₂) → case decConv↑TermConv (soundnessConv↑ A₁≡A₂)
                             u₁≡u₃ u₂≡u₄ of λ where
          (no u₁≢u₂) → no λ where
            (_ , []-cong-cong _ _ u₁≡u₂ _ _ _) → u₁≢u₂ u₁≡u₂
          (yes u₁≡u₂) → case dec~↓ v₁~v₃ v₂~v₄ of λ where
            (no ¬v₁~v₂) → no λ where
              (_ , []-cong-cong _ _ _ v₁~v₂ _ _) → ¬v₁~v₂ (_ , v₁~v₂)
            (yes (_ , v₁~v₂)) →
              case neTypeEq (ne~↓ v₁~v₂ .proj₂ .proj₁)
                     (syntacticEqTerm (soundness~↓ v₁~v₃) .proj₂ .proj₁)
                     (syntacticEqTerm (soundness~↓ v₁~v₂)
                        .proj₂ .proj₁) of λ {
                B₁≡C → case decStrength s s′ of λ where
                  (yes PE.refl) → yes
                    ( _
                    , []-cong-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁~v₂
                        (trans (sym B₁≡C) B₁≡Id-t₁-u₁) ok
                    )
                  (no s≢s) → no λ where
                    (_ , []-cong-cong _ _ _ _ _ _) → s≢s PE.refl }
  dec~↑ ([]-cong-cong _ _ _ _ _ _) (var-refl _ _) = no (λ { (_ , ()) })
  dec~↑ ([]-cong-cong _ _ _ _ _ _) (fst-cong _) = no (λ { (_ , ()) })
  dec~↑ ([]-cong-cong _ _ _ _ _ _) (snd-cong _) = no (λ { (_ , ()) })
  dec~↑ ([]-cong-cong _ _ _ _ _ _) (app-cong _ _) = no (λ { (_ , ()) })
  dec~↑ ([]-cong-cong _ _ _ _ _ _) (natrec-cong _ _ _ _) = no (λ { (_ , ()) })
  dec~↑ ([]-cong-cong _ _ _ _ _ _) (prodrec-cong _ _ _) = no λ{(_ , ())}
  dec~↑ ([]-cong-cong _ _ _ _ _ _) (emptyrec-cong _ _) = no λ { (_ , ()) }
  dec~↑ ([]-cong-cong _ _ _ _ _ _) (unitrec-cong _ _ _ _) = no λ { (_ , ()) }
  dec~↑ ([]-cong-cong _ _ _ _ _ _) (J-cong _ _ _ _ _ _ _) = no λ { (_ , ()) }
  dec~↑ ([]-cong-cong _ _ _ _ _ _) (K-cong _ _ _ _ _ _ _) = no λ { (_ , ()) }

  dec~↑′ : ∀ {k l R T}
        → ⊢ Γ ≡ Δ
        → Γ ⊢ k ~ k ↑ R → Δ ⊢ l ~ l ↑ T
        → Dec (∃ λ A → Γ ⊢ k ~ l ↑ A)
  dec~↑′ Γ≡Δ k~k l~l = dec~↑ k~k (stability~↑ (symConEq Γ≡Δ) l~l)

  -- Decidability of algorithmic equality of neutrals with types in WHNF.
  dec~↓ : ∀ {k l R T k′ l′}
        → Γ ⊢ k ~ k′ ↓ R → Γ ⊢ l ~ l′ ↓ T
        → Dec (∃ λ A → Γ ⊢ k ~ l ↓ A)
  dec~↓ ([~] _ _ k~l) ([~] _ _ k~l₁) with dec~↑ k~l k~l₁
  dec~↓ ([~] _ _ k~l) ([~] _ _ k~l₁) | yes (B , k~l₂) =
    let ⊢B , _ , _ = syntacticEqTerm (soundness~↑ k~l₂)
        C , whnfC , D′ = whNorm ⊢B
    in  yes (C , [~] B (red D′ , whnfC) k~l₂)
  dec~↓ ([~] _ _ k~l) ([~] _ _ k~l₁) | no ¬p =
    no (λ { (_ , [~] A₃ _ k~l₂) → ¬p (A₃ , k~l₂) })

  -- Decidability of algorithmic equality of types.
  decConv↑ : ∀ {A B A′ B′}
           → Γ ⊢ A [conv↑] A′ → Γ ⊢ B [conv↑] B′
           → Dec (Γ ⊢ A [conv↑] B)
  decConv↑ ([↑] A′ B′ D D′ A′<>B′)
               ([↑] A″ B″ D₁ D″ A′<>B″)
           with decConv↓ A′<>B′ A′<>B″
  decConv↑ ([↑] A′ B′ D D′ A′<>B′)
               ([↑] A″ B″ D₁ D″ A′<>B″) | yes p =
    yes ([↑] A′ A″ D D₁ p)
  decConv↑ ([↑] A′ B′ D D′ A′<>B′)
               ([↑] A″ B″ D₁ D″ A′<>B″) | no ¬p =
    no (λ { ([↑] A‴ B‴ D₂ D‴ A′<>B‴) →
        let A‴≡B′ = whrDet* D₂ D
            B‴≡B″ = whrDet* D‴ D₁
        in  ¬p (PE.subst₂ (λ x y → _ ⊢ x [conv↓] y) A‴≡B′ B‴≡B″ A′<>B‴) })

  decConv↑′ : ∀ {A B A′ B′}
            → ⊢ Γ ≡ Δ
            → Γ ⊢ A [conv↑] A′ → Δ ⊢ B [conv↑] B′
            → Dec (Γ ⊢ A [conv↑] B)
  decConv↑′ Γ≡Δ A B = decConv↑ A (stabilityConv↑ (symConEq Γ≡Δ) B)

  -- Decidability of algorithmic equality of types in WHNF.
  decConv↓ : ∀ {A B A′ B′}
           → Γ ⊢ A [conv↓] A′ → Γ ⊢ B [conv↓] B′
           → Dec (Γ ⊢ A [conv↓] B)
  -- True cases
  decConv↓ (U-refl x) (U-refl x₁) = yes (U-refl x)
  decConv↓ (ℕ-refl x) (ℕ-refl x₁) = yes (ℕ-refl x)
  decConv↓ (Empty-refl x) (Empty-refl x₁) = yes (Empty-refl x)

  -- Inspective cases
  decConv↓ (Unit-refl {s = s} x ok) (Unit-refl {s = s′} _ _) =
    case decStrength s s′ of λ where
    (yes PE.refl) → yes (Unit-refl x ok)
    (no s≢s′) → no (λ { (Unit-refl x x₁) → s≢s′ PE.refl})
  decConv↓ (ne x) (ne x₁) with dec~↓ x x₁
  decConv↓ (ne x) (ne x₁) | yes (A , k~l) =
    let whnfA , neK , neL = ne~↓ k~l
        ⊢A , ⊢k , _ = syntacticEqTerm (soundness~↓ k~l)
        _ , ⊢k∷U , _ = syntacticEqTerm (soundness~↓ x)
        ⊢U≡A = neTypeEq neK ⊢k∷U ⊢k
        A≡U = U≡A ⊢U≡A
        k~l′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) A≡U k~l
    in  yes (ne k~l′)
  decConv↓ (ne x) (ne x₁) | no ¬p = no (λ x₂ → ¬p (U , (decConv↓-ne x₂ x)))

  decConv↓
    (ΠΣ-cong {b = b₁} {p = p′} {q = q′} x x₁ x₂ ok)
    (ΠΣ-cong {b = b₂} {p = p″} {q = q″} x₃ x₄ x₅ _)
           with decConv↑ x₁ x₄
  ... | yes p
    with decConv↑′ (reflConEq (wf x) ∙ soundnessConv↑ p) x₂ x₅
       | p′ ≟ p″ | q′ ≟ q″ | decBinderMode b₁ b₂
  ... | yes p₁ | yes PE.refl | yes PE.refl | yes PE.refl =
    yes (ΠΣ-cong x p p₁ ok)
  ... | no ¬p | _ | _ | _ =
    no (λ { (ne ([~] _ _ ())); (ΠΣ-cong _ _ p _) → ¬p p })
  ... | _ | no ¬p′≡p″ | _ | _ =
    no (λ { (ne ([~] _ _ ())); (ΠΣ-cong _ _ _ _) → ¬p′≡p″ PE.refl })
  ... | _ | _ | no ¬q′≡q″ | _ =
    no (λ { (ne ([~] _ _ ())); (ΠΣ-cong _ _ _ _) → ¬q′≡q″ PE.refl })
  ... | _ | _ | _ | no b₁≢b₂ =
    no λ { (ne ([~] _ _ ())); (ΠΣ-cong _ _ _ _) → b₁≢b₂ PE.refl }
  decConv↓ (ΠΣ-cong _ _ _ _) (ΠΣ-cong _ _ _ _) | no ¬p =
    no (λ { (ne ([~] _ _ ())) ; (ΠΣ-cong _ p _ _) → ¬p p })

  decConv↓ (Id-cong A₁≡A₃ t₁≡t₃ u₁≡u₃) (Id-cong A₂≡A₄ t₂≡t₄ u₂≡u₄) =
    case decConv↑ A₁≡A₃ A₂≡A₄ of λ where
      (no A₁≢A₂) → no λ where
        (ne ([~] _ _ ()))
        (Id-cong A₁≡A₂ _ _) → A₁≢A₂ A₁≡A₂
      (yes A₁≡A₂) → case decConv↑TermConv (soundnessConv↑ A₁≡A₂)
                           t₁≡t₃ t₂≡t₄ of λ where
        (no t₁≢t₂) → no λ where
          (ne ([~] _ _ ()))
          (Id-cong _ t₁≡t₂ _) → t₁≢t₂ t₁≡t₂
        (yes t₁≡t₂) → case decConv↑TermConv (soundnessConv↑ A₁≡A₂)
                             u₁≡u₃ u₂≡u₄ of λ where
          (no u₁≢u₂) → no λ where
            (ne ([~] _ _ ()))
            (Id-cong _ _ u₁≡u₂) → u₁≢u₂ u₁≡u₂
          (yes u₁≡u₂) → yes (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂)

  -- False cases
  decConv↓ (U-refl x) (ℕ-refl x₁) = no (λ { (ne ([~] _ _ ())) })
  decConv↓ (U-refl x) (Empty-refl x₁) = no (λ { (ne ([~] _ _ ())) })
  decConv↓ (U-refl _) (Unit-refl _ _) = no (λ { (ne ([~] _ _ ())) })
  decConv↓ (U-refl x) (ne x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓ x₁
               in  ⊥-elim (IE.U≢ne neK (soundnessConv↓ x₂)))
  decConv↓ (U-refl _) (ΠΣ-cong _ _ _ _) = no (λ { (ne ([~] _ _ ())) })
  decConv↓ (U-refl _) (Id-cong _ _ _) = no (λ { (ne ([~] _ _ ())) })
  decConv↓ (ℕ-refl x) (U-refl x₁) = no (λ { (ne ([~] _ _ ())) })
  decConv↓ (ℕ-refl x) (Empty-refl x₁) = no (λ { (ne ([~] _ _ ())) })
  decConv↓ (ℕ-refl _) (Unit-refl _ _) = no (λ { (ne ([~] _ _ ())) })
  decConv↓ (ℕ-refl x) (ne x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓ x₁
               in  ⊥-elim (IE.ℕ≢ne neK (soundnessConv↓ x₂)))
  decConv↓ (ℕ-refl _) (ΠΣ-cong _ _ _ _) = no (λ { (ne ([~] _ _ ())) })
  decConv↓ (ℕ-refl _) (Id-cong _ _ _) = no (λ { (ne ([~] _ _ ())) })
  decConv↓ (Empty-refl x) (U-refl x₁) = no (λ { (ne ([~] _ _ ())) })
  decConv↓ (Empty-refl x) (ℕ-refl x₁) = no (λ { (ne ([~] _ _ ())) })
  decConv↓ (Empty-refl _) (Unit-refl _ _) = no (λ { (ne ([~] _ _ ())) })
  decConv↓ (Empty-refl x) (ne x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓ x₁
               in  ⊥-elim (IE.Empty≢neⱼ neK (soundnessConv↓ x₂)))
  decConv↓ (Empty-refl _) (ΠΣ-cong _ _ _ _) = no (λ { (ne ([~] _ _ ())) })
  decConv↓ (Empty-refl _) (Id-cong _ _ _) = no (λ { (ne ([~] _ _ ())) })
  decConv↓ (Unit-refl _ _) (U-refl _) = no (λ { (ne ([~] _ _ ())) })
  decConv↓ (Unit-refl _ _) (ℕ-refl _) = no (λ { (ne ([~] _ _ ())) })
  decConv↓ (Unit-refl _ _) (Empty-refl _) = no (λ { (ne ([~] _ _ ())) })
  decConv↓ (Unit-refl _ _) (ne x) =
    no (λ y → let _ , neK , _ = ne~↓ x
              in  ⊥-elim (IE.Unit≢neⱼ neK (soundnessConv↓ y)))
  decConv↓ (Unit-refl _ _) (ΠΣ-cong _ _ _ _) = no (λ { (ne ([~] _ _ ())) })
  decConv↓ (Unit-refl _ _) (Id-cong _ _ _) = no (λ { (ne ([~] _ _ ())) })
  decConv↓ (ne x) (U-refl x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓ x
               in  ⊥-elim (IE.U≢ne neK (sym (soundnessConv↓ x₂))))
  decConv↓ (ne x) (ℕ-refl x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓ x
               in  ⊥-elim (IE.ℕ≢ne neK (sym (soundnessConv↓ x₂))))
  decConv↓ (ne x) (Empty-refl x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓ x
               in  ⊥-elim (IE.Empty≢neⱼ neK (sym (soundnessConv↓ x₂))))
  decConv↓ (ne x) (Unit-refl _ _) =
    no (λ y → let whnfA , neK , neL = ne~↓ x
              in  ⊥-elim (IE.Unit≢neⱼ neK (sym (soundnessConv↓ y))))
  decConv↓ (ne x) (ΠΣ-cong _ _ _ _) =
    no (λ y → let whnfA , neK , neL = ne~↓ x
              in  ⊥-elim (IE.ΠΣ≢ne neK (sym (soundnessConv↓ y))))
  decConv↓ (ne A~A′) (Id-cong _ _ _) =
    no λ A≡B →
    ⊥-elim $
    IE.Id≢ne (ne~↓ A~A′ .proj₂ .proj₁) (sym (soundnessConv↓ A≡B))
  decConv↓ (ΠΣ-cong _ _ _ _) (U-refl _) = no (λ { (ne ([~] _ _ ())) })
  decConv↓ (ΠΣ-cong _ _ _ _) (ℕ-refl _) = no (λ { (ne ([~] _ _ ())) })
  decConv↓ (ΠΣ-cong _ _ _ _) (Empty-refl _) = no (λ { (ne ([~] _ _ ())) })
  decConv↓ (ΠΣ-cong _ _ _ _) (Unit-refl _ _) = no (λ { (ne ([~] _ _ ())) })
  decConv↓ (ΠΣ-cong _ _ _ _) (ne x) =
    no (λ y → let whnfA , neK , neL = ne~↓ x
              in  ⊥-elim (IE.ΠΣ≢ne neK (soundnessConv↓ y)))
  decConv↓ (ΠΣ-cong _ _ _ _) (Id-cong _ _ _) = no (λ { (ne ([~] _ _ ())) })
  decConv↓ (Id-cong _ _ _) (U-refl _) = no (λ { (ne ([~] _ _ ())) })
  decConv↓ (Id-cong _ _ _) (ℕ-refl _) = no (λ { (ne ([~] _ _ ())) })
  decConv↓ (Id-cong _ _ _) (Empty-refl _) = no (λ { (ne ([~] _ _ ())) })
  decConv↓ (Id-cong _ _ _) (Unit-refl _ _) = no (λ { (ne ([~] _ _ ())) })
  decConv↓ (Id-cong _ _ _) (ne B~B′) =
    no λ A≡B →
    ⊥-elim $
    IE.Id≢ne (ne~↓ B~B′ .proj₂ .proj₁) (soundnessConv↓ A≡B)
  decConv↓ (Id-cong _ _ _) (ΠΣ-cong _ _ _ _) = no (λ { (ne ([~] _ _ ())) })

  -- Helper function for decidability of neutral types.
  decConv↓-ne : ∀ {A B A′}
              → Γ ⊢ A [conv↓] B
              → Γ ⊢ A ~ A′ ↓ U
              → Γ ⊢ A ~ B ↓ U
  decConv↓-ne (U-refl x) ()
  decConv↓-ne (ℕ-refl x) ()
  decConv↓-ne (Empty-refl x) ()
  decConv↓-ne (ne x) A~A = x
  decConv↓-ne (ΠΣ-cong _ _ _ _) ([~] _ _ ())
  decConv↓-ne (Unit-refl _ _) ()
  decConv↓-ne (Id-cong _ _ _) ([~] _ _ ())

  -- Decidability of algorithmic equality of terms.
  decConv↑Term : ∀ {t u A t′ u′}
               → Γ ⊢ t [conv↑] t′ ∷ A → Γ ⊢ u [conv↑] u′ ∷ A
               → Dec (Γ ⊢ t [conv↑] u ∷ A)
  decConv↑Term ([↑]ₜ B t′ u′ D d d′ t<>u)
               ([↑]ₜ B₁ t″ u″ D₁ d₁ d″ t<>u₁)
               rewrite whrDet* D D₁
                 with decConv↓Term t<>u t<>u₁
  decConv↑Term ([↑]ₜ B t′ u′ D d d′ t<>u)
               ([↑]ₜ B₁ t″ u″ D₁ d₁ d″ t<>u₁)
               | yes p = yes ([↑]ₜ B₁ t′ t″ D₁ d d₁ p)
  decConv↑Term ([↑]ₜ B t′ u′ D d d′ t<>u)
               ([↑]ₜ B₁ t″ u″ D₁ d₁ d″ t<>u₁)
               | no ¬p =
    no (λ { ([↑]ₜ B₂ t‴ u‴ D₂ d₂ d‴ t<>u₂) →
        let B₂≡B₁ = whrDet* D₂ D₁
            t‴≡u′ = whrDet*Term d₂
                      (PE.subst (_⊢_↘_∷_ _ _ _) (PE.sym B₂≡B₁) d)
            u‴≡u″ = whrDet*Term d‴
                      (PE.subst (_⊢_↘_∷_ _ _ _) (PE.sym B₂≡B₁) d₁)
        in  ¬p (PE.subst₃ (λ x y z → _ ⊢ x [conv↓] y ∷ z)
                          t‴≡u′ u‴≡u″ B₂≡B₁ t<>u₂)})

  decConv↑Term′ : ∀ {t u A}
                → ⊢ Γ ≡ Δ
                → Γ ⊢ t [conv↑] t ∷ A → Δ ⊢ u [conv↑] u ∷ A
                → Dec (Γ ⊢ t [conv↑] u ∷ A)
  decConv↑Term′ Γ≡Δ t u = decConv↑Term t (stabilityConv↑Term (symConEq Γ≡Δ) u)

  -- Decidability of algorithmic equality of terms in WHNF.
  decConv↓Term : ∀ {t u A t′ u′}
               → Γ ⊢ t [conv↓] t′ ∷ A → Γ ⊢ u [conv↓] u′ ∷ A
               → Dec (Γ ⊢ t [conv↓] u ∷ A)
  -- True cases
  decConv↓Term (zero-refl x) (zero-refl x₁) = yes (zero-refl x)
  decConv↓Term (starʷ-refl x x₁ no-η) (starʷ-refl _ _ _) =
    yes (starʷ-refl x x₁ no-η)
  decConv↓Term (starʷ-refl _ _ _) (η-unit _ _ _ _ (inj₁ ()))
  decConv↓Term (starʷ-refl _ _ no-η) (η-unit _ _ _ _ (inj₂ η)) =
    ⊥-elim (no-η η)
  decConv↓Term (η-unit ⊢t _ tUnit _ ok) (η-unit ⊢u _ uUnit _ _) =
    yes (η-unit ⊢t ⊢u tUnit uUnit ok)
  decConv↓Term (η-unit _ _ _ _ (inj₁ ())) (starʷ-refl _ _ _)
  decConv↓Term (η-unit _ _ _ _ (inj₂ η)) (starʷ-refl _ _ no-η) =
    ⊥-elim (no-η η)
  decConv↓Term ⊢rfl≡rfl@(rfl-refl _) (rfl-refl _) = yes ⊢rfl≡rfl

  -- Inspective cases
  decConv↓Term (ℕ-ins x) (ℕ-ins x₁) with dec~↓ x x₁
  decConv↓Term (ℕ-ins x) (ℕ-ins x₁) | yes (A , k~l) =
    let whnfA , neK , neL = ne~↓ k~l
        ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓ k~l)
        _ , ⊢l∷ℕ , _ = syntacticEqTerm (soundness~↓ x)
        ⊢ℕ≡A = neTypeEq neK ⊢l∷ℕ ⊢k
        A≡ℕ = ℕ≡A ⊢ℕ≡A whnfA
        k~l′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) A≡ℕ k~l
    in  yes (ℕ-ins k~l′)
  decConv↓Term (ℕ-ins x) (ℕ-ins x₁) | no ¬p =
    no (λ x₂ → ¬p (ℕ , decConv↓Term-ℕ-ins x₂ x))
  decConv↓Term (Empty-ins x) (Empty-ins x₁) with dec~↓ x x₁
  decConv↓Term (Empty-ins x) (Empty-ins x₁) | yes (A , k~l) =
    let whnfA , neK , neL = ne~↓ k~l
        ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓ k~l)
        _ , ⊢l∷Empty , _ = syntacticEqTerm (soundness~↓ x)
        ⊢Empty≡A = neTypeEq neK ⊢l∷Empty ⊢k
        A≡Empty = Empty≡A ⊢Empty≡A whnfA
        k~l′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) A≡Empty k~l
    in  yes (Empty-ins k~l′)
  decConv↓Term (Empty-ins x) (Empty-ins x₁) | no ¬p =
    no (λ x₂ → ¬p (Empty , decConv↓Term-Empty-ins x₂ x))
  decConv↓Term (Unitʷ-ins no-η t~t′) (Unitʷ-ins _ u~u′)
    with dec~↓ t~t′ u~u′
  ... | yes (A , t~u) =
    case ne~↓ t~u of λ
      (A-whnf , t-ne , _) →
    yes $
    Unitʷ-ins no-η $
    PE.subst (_⊢_~_↓_ _ _ _)
      (Unit≡A
         (neTypeEq t-ne
            (syntacticEqTerm (soundness~↓ t~t′) .proj₂ .proj₁)
            (syntacticEqTerm (soundness~↓ t~u) .proj₂ .proj₁))
         A-whnf)
      t~u
  ... | no ¬t~u =
    case Unitʷ-η? of λ where
      (no no-η) → no λ where
        (Unitʷ-ins _ t~u)          → ¬t~u (_ , t~u)
        (η-unit _ _ _ _ (inj₁ ()))
        (η-unit _ _ _ _ (inj₂ η))  → no-η η
      (yes η) → yes $
        η-unit
          (syntacticEqTerm (soundness~↓ t~t′) .proj₂ .proj₁)
          (syntacticEqTerm (soundness~↓ u~u′) .proj₂ .proj₁)
          (ne (ne~↓ t~t′ .proj₂ .proj₁))
          (ne (ne~↓ u~u′ .proj₂ .proj₁))
          (inj₂ η)
  decConv↓Term (Σʷ-ins x x₁ x₂) (Σʷ-ins x₃ x₄ x₅) with dec~↓ x₂ x₅
  ... | yes (B , t~u) =
    let ⊢B , ⊢t , ⊢u = syntacticEqTerm (soundness~↓ t~u)
        whnfB , neT , _ = ne~↓ t~u
        Σ≡B = neTypeEq neT x ⊢t
        _ , _ , B≡Σ′ = Σ≡A Σ≡B whnfB
    in  yes (Σʷ-ins x x₃ (PE.subst (λ x →  _ ⊢ _ ~ _ ↓ x) B≡Σ′ t~u))
  ... | no ¬p = no (λ x₆ → ¬p (decConv↓Term-Σʷ-ins x₆ x₂))
  decConv↓Term (ne-ins x x₁ x₂ x₃) (ne-ins x₄ x₅ x₆ x₇)
               with dec~↓ x₃ x₇
  decConv↓Term (ne-ins x x₁ x₂ x₃) (ne-ins x₄ x₅ x₆ x₇) | yes (A , k~l) =
    yes (ne-ins x x₄ x₆ k~l)
  decConv↓Term (ne-ins x x₁ x₂ x₃) (ne-ins x₄ x₅ x₆ x₇) | no ¬p =
    no (λ x₈ → ¬p (inv-[conv↓]∷-ne x₆ x₈))
  decConv↓Term (univ x x₁ x₂) (univ x₃ x₄ x₅)
               with decConv↓  x₂ x₅
  decConv↓Term (univ x x₁ x₂) (univ x₃ x₄ x₅) | yes p =
    yes (univ x x₃ p)
  decConv↓Term (univ x x₁ x₂) (univ x₃ x₄ x₅) | no ¬p =
    no (λ { (ne-ins x₆ x₇ () x₉)
          ; (univ x₆ x₇ x₈) → ¬p x₈ })
  decConv↓Term (suc-cong x) (suc-cong x₁) with decConv↑Term  x x₁
  decConv↓Term (suc-cong x) (suc-cong x₁) | yes p =
    yes (suc-cong p)
  decConv↓Term (suc-cong x) (suc-cong x₁) | no ¬p =
    no (λ { (ℕ-ins ([~] _ _ ()))
          ; (ne-ins x₂ x₃ () x₅)
          ; (suc-cong x₂) → ¬p x₂ })
  decConv↓Term (Σ-η ⊢t _ tProd _ fstConvT sndConvT)
               (Σ-η ⊢u _ uProd _ fstConvU sndConvU)
               with decConv↑Term fstConvT fstConvU
  ... | yes P = let ⊢F , ⊢G = syntacticΣ (syntacticTerm ⊢t)
                    fstt≡fstu = soundnessConv↑Term P
                    Gfstt≡Gfstu = substTypeEq (refl ⊢G) fstt≡fstu
                    sndConv = decConv↑TermConv Gfstt≡Gfstu sndConvT sndConvU
                in  decConv↓Term-Σ-η ⊢t ⊢u tProd uProd P sndConv
  ... | no ¬P = no (λ { (Σ-η _ _ _ _ P _) → ¬P P } )
  decConv↓Term (prod-cong x x₁ x₂ x₃ ok) (prod-cong x₄ x₅ x₆ x₇ _)
    with decConv↑Term x₂ x₆
  ... | no ¬P = no λ eq → case prod-cong⁻¹ eq of λ
    (_ , _ , _ , _ , t , _) → ¬P t
  ... | yes P with decConv↑TermConv (substTypeEq (refl x₁) (soundnessConv↑Term P)) x₃ x₇
  ... | yes Q = yes (prod-cong x x₁ P Q ok)
  ... | no ¬Q = no λ eq → case prod-cong⁻¹ eq of λ
    (_ , _ , _ , _ , _ , u , _) → ¬Q u
  decConv↓Term (η-eq {p = p} {f = t} x₁ x₂ x₃ x₄ x₅) (η-eq {f = u} x₇ x₈ x₉ x₁₀ x₁₁)
    with decConv↑Term x₅ x₁₁
  ... | yes P =
    let ⊢F , ⊢G = syntacticΠ (syntacticTerm x₁)
        G≡G = refl ⊢G
    in
    yes (η-eq x₁ x₇ x₃ x₉ $
         transConv↑Term G≡G x₅
           (transConv↑Term G≡G (symConvTerm x₅)
           (transConv↑Term G≡G P
           (transConv↑Term G≡G x₁₁
           (symConvTerm x₁₁)))))
  ... | no ¬P = no (λ { (ne-ins x₁₂ x₁₃ () x₁₅)
                      ; (η-eq x₁₃ x₁₄ x₁₅ x₁₆ x₁₇) → ¬P x₁₇ })
  decConv↓Term (Id-ins ⊢v₁ v₁~v₃) (Id-ins ⊢v₂ v₂~v₄) =
    case dec~↓ v₁~v₃ v₂~v₄ of λ where
      (no ¬v₁~v₂) → no λ where
        (Id-ins _ v₁~v₂)  → ¬v₁~v₂ (_ , v₁~v₂)
        (rfl-refl _)      → case v₂~v₄ of λ { ([~] _ _ ()) }
        (ne-ins _ _ () _)
      (yes (_ , v₁~v₂)) →
        case ne~↓ v₁~v₂ of λ {
          (B-whnf , v₁-ne , _) →
        case neTypeEq v₁-ne
               (syntacticEqTerm (soundness~↓ v₁~v₃) .proj₂ .proj₁)
               (syntacticEqTerm (soundness~↓ v₁~v₂)
                  .proj₂ .proj₁) of λ {
          Id≡B →
        case Id≡Whnf Id≡B B-whnf of λ {
          (_ , _ , _ , PE.refl) →
        yes (Id-ins ⊢v₁ v₁~v₂) }}}

  -- False cases
  decConv↓Term  (ℕ-ins x) (zero-refl x₁) =
    no (λ x₂ → decConv↓Term-ℕ x₂ x λ { ([~] _ _ ()) })
  decConv↓Term  (ℕ-ins x) (suc-cong x₁) =
    no (λ x₂ → decConv↓Term-ℕ x₂ x (λ { ([~] _ _ ()) }))
  decConv↓Term  (zero-refl x) (ℕ-ins x₁) =
    no (λ x₂ → decConv↓Term-ℕ (symConv↓Term′ x₂) x₁ (λ { ([~] _ _ ()) }))
  decConv↓Term  (zero-refl x) (suc-cong x₁) =
    no (λ { (ℕ-ins ([~] _ _ ())) ; (ne-ins x₂ x₃ () x₅) })
  decConv↓Term  (suc-cong x) (ℕ-ins x₁) =
    no (λ x₂ → decConv↓Term-ℕ (symConv↓Term′ x₂) x₁ (λ { ([~] _ _ ()) }))
  decConv↓Term  (suc-cong x) (zero-refl x₁) =
    no (λ { (ℕ-ins ([~] _ _ ())) ; (ne-ins x₂ x₃ () x₅) })
  decConv↓Term (Unitʷ-ins no-η _) (η-unit _ _ _ _ (inj₂ η)) =
    ⊥-elim (no-η η)
  decConv↓Term (η-unit _ _ _ _ (inj₂ η)) (Unitʷ-ins no-η _) =
    ⊥-elim (no-η η)
  decConv↓Term (Σʷ-ins x x₁ x₂) (prod-cong x₃ x₄ x₅ x₆ _) =
    no λ x₇ → decConv↓Term-Σʷ x₇ x₂ (λ{ ()})
  decConv↓Term (prod-cong x x₁ x₂ x₃ _) (Σʷ-ins x₄ x₅ x₆) =
    no (λ x₇ → decConv↓Term-Σʷ (symConv↓Term′ x₇) x₆ (λ{ ()}))
  decConv↓Term (starʷ-refl _ _ no-η) (Unitʷ-ins _ u~) =
    no λ ≡u → no-η (decConv↓Term-Unit (symConv↓Term′ ≡u) u~)
  decConv↓Term (Unitʷ-ins _ t~) (starʷ-refl _ _ no-η) =
    no λ t≡ → no-η (decConv↓Term-Unit t≡ t~)
  decConv↓Term (Id-ins _ v₁~v₃) (rfl-refl _) =
    no λ where
      (Id-ins _ ~rfl)   → case ne~↓ ~rfl  .proj₂ .proj₂ of λ ()
      (rfl-refl _)      → case ne~↓ v₁~v₃ .proj₂ .proj₁ of λ ()
      (ne-ins _ _ () _)
  decConv↓Term (rfl-refl _) (Id-ins _ v₂~v₄) =
    no λ where
      (Id-ins _ rfl~)   → case ne~↓ rfl~  .proj₂ .proj₁ of λ ()
      (rfl-refl _)      → case ne~↓ v₂~v₄ .proj₂ .proj₁ of λ ()
      (ne-ins _ _ () _)

  -- Impossible cases
  decConv↓Term (ℕ-ins x) (ne-ins x₁ x₂ () x₄)
  decConv↓Term (Empty-ins x) (ne-ins x₁ x₂ () x₄)
  decConv↓Term (Σʷ-ins x x₁ x₂) (ne-ins x₃ x₄ () x₆)
  decConv↓Term (ne-ins x x₁ () x₃) (ℕ-ins x₄)
  decConv↓Term (ne-ins x x₁ () x₃) (Empty-ins x₄)
  decConv↓Term (ne-ins _ _ () _) (Unitʷ-ins _ _)
  decConv↓Term (ne-ins x x₁ () x₃) (Σʷ-ins x₄ x₅ x₆)
  decConv↓Term (ne-ins x x₁ () x₃) (univ x₄ x₅ x₆)
  decConv↓Term (ne-ins x x₁ () x₃) (zero-refl x₄)
  decConv↓Term (ne-ins x x₁ () x₃) (suc-cong x₄)
  decConv↓Term (ne-ins x x₁ () x₃) (prod-cong x₄ x₅ x₆ x₇ _)
  decConv↓Term (ne-ins x x₁ () x₃) (η-eq x₄ x₅ x₆ x₇ x₈)
  decConv↓Term (ne-ins x x₁ () x₃) (Σ-η x₄ x₅ x₆ x₇ x₈ x₉)
  decConv↓Term (ne-ins x x₁ () x₃) (η-unit _ _ _ _ _)
  decConv↓Term (ne-ins _ _ () _) (Id-ins _ _)
  decConv↓Term (ne-ins _ _ () _) (rfl-refl _)
  decConv↓Term (univ x x₁ x₂) (ne-ins x₃ x₄ () x₆)
  decConv↓Term (zero-refl x) (ne-ins x₁ x₂ () x₄)
  decConv↓Term (rfl-refl _) (ne-ins _ _ () _)
  decConv↓Term (suc-cong x) (ne-ins x₁ x₂ () x₄)
  decConv↓Term (prod-cong x x₁ x₂ x₃ _) (ne-ins x₄ x₅ () x₇)
  decConv↓Term (η-eq x x₁ x₂ x₃ x₄) (ne-ins x₅ x₆ () x₈)
  decConv↓Term (Σ-η x x₁ x₂ x₃ x₄ x₅) (ne-ins x₆ x₇ () x₉)
  decConv↓Term (Id-ins _ _) (ne-ins _ _ () _)
  decConv↓Term (Unitʷ-ins _ _) (η-unit _ _ _ _ (inj₁ ()))
  decConv↓Term (Unitʷ-ins _ _) (ne-ins _ _ () _)
  decConv↓Term (ne-ins x x₁ () x₃) (starʷ-refl _ _ _)
  decConv↓Term (starʷ-refl _ _ _) (ne-ins x₂ x₃ () x₅)
  decConv↓Term (η-unit _ _ _ _ (inj₁ ())) (Unitʷ-ins _ _)
  decConv↓Term (η-unit _ _ _ _ _) (ne-ins x₄ x₅ () x₇)

  -- Decidability of algorithmic equality of terms of equal types.
  decConv↑TermConv : ∀ {t u A B t′ u′}
                → Γ ⊢ A ≡ B
                → Γ ⊢ t [conv↑] t′ ∷ A
                → Γ ⊢ u [conv↑] u′ ∷ B
                → Dec (Γ ⊢ t [conv↑] u ∷ A)
  decConv↑TermConv A≡B t u =
    decConv↑Term t (convConvTerm u (sym A≡B))
