{-# OPTIONS --without-K --safe #-}

open import Tools.Relation

module Definition.Conversion.Decidable {a ℓ′} (M″ : DecSetoid a ℓ′) where

open DecSetoid M″ using (_≈_; _≟_) renaming (Carrier to M; setoid to M′; sym to ≈-sym; trans to ≈-trans; refl to ≈-refl)

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed M′
open import Definition.Typed.Properties M′
open import Definition.Conversion M′
open import Definition.Conversion.Whnf M′
open import Definition.Conversion.Soundness M′
open import Definition.Conversion.Symmetry M′
open import Definition.Conversion.Transitivity M′
open import Definition.Conversion.Stability M′
open import Definition.Conversion.Conversion M′
open import Definition.Typed.Consequences.Syntactic M′
open import Definition.Typed.Consequences.Substitution M′
open import Definition.Typed.Consequences.Injectivity M′
open import Definition.Typed.Consequences.Reduction M′
open import Definition.Typed.Consequences.Equality M′
open import Definition.Typed.Consequences.Inequality M′ as IE
open import Definition.Typed.Consequences.NeTypeEq M′
open import Definition.Typed.Consequences.SucCong M′

open import Tools.Fin
open import Tools.Nat hiding (_≟_)
open import Tools.Product
open import Tools.Empty
open import Tools.Nullary
import Tools.PropositionalEquality as PE

private
  variable
    ℓ : Nat
    Γ Δ : Con Term ℓ
    p p₁ p₂ q : M


-- Algorithmic equality of variables infers propositional equality.
strongVarEq : ∀ {m n A} → Γ ⊢ var n ~ var m ↑ A → n PE.≡ m
strongVarEq (var-refl x x≡y) = x≡y

-- Helper function for decidability of applications.
dec~↑-app : ∀ {k k₁ l l₁ F F₁ G G₁ B}
          → Γ ⊢ k ∷ Π p , q ▷ F ▹ G
          → Γ ⊢ k₁ ∷ Π p , q ▷ F₁ ▹ G₁
          → Γ ⊢ k ~ k₁ ↓ B
          → p ≈ p₁
          → p ≈ p₂
          → Dec (Γ ⊢ l [conv↑] l₁ ∷ F)
          → Dec (∃ λ A → Γ ⊢ k ∘ p₁ ▷ l ~ k₁ ∘ p₂ ▷ l₁ ↑ A)
dec~↑-app k k₁ k~k₁ p₃≈p₁ p₃≈p₂ (yes p) =
  let whnfA , neK , neL = ne~↓ k~k₁
      ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓ k~k₁)
      ΠFG₁≡A = neTypeEq neK k ⊢k
      p′ , q′ , H , E , A≡ΠHE = Π≡A ΠFG₁≡A whnfA
      F≡H , G₁≡E , p₃≈p′ , q≈q′ = injectivity (PE.subst (λ x → _ ⊢ _ ≡ x) A≡ΠHE ΠFG₁≡A)
  in  yes (E [ _ ] , app-cong (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) A≡ΠHE k~k₁)
                              (convConvTerm p F≡H)
                              (≈-trans (≈-sym p₃≈p′) p₃≈p₁) (≈-trans (≈-sym p₃≈p′) p₃≈p₂))
dec~↑-app k₂ k₃ k~k₁ p≈p₁ p≈p₂ (no ¬p) =
  no (λ { (_ , app-cong x x₁ x₂ x₃) →
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
decConv↓Term-ℕ-ins (zero-refl x) ([~] A D whnfB ())
decConv↓Term-ℕ-ins (suc-cong x) ([~] A D whnfB ())

-- Helper function for decidability for neutrals of empty type.
decConv↓Term-Empty-ins : ∀ {t u t′}
                    → Γ ⊢ t [conv↓] u ∷ Empty
                    → Γ ⊢ t ~ t′ ↓ Empty
                    → Γ ⊢ t ~ u ↓ Empty
decConv↓Term-Empty-ins (Empty-ins x) t~t = x
decConv↓Term-Empty-ins (ne-ins x x₁ () x₃) t~t

-- Helper function for decidability for neutrals of a neutral type.
decConv↓Term-ne-ins : ∀ {t u A}
                    → Neutral A
                    → Γ ⊢ t [conv↓] u ∷ A
                    → ∃ λ B → Γ ⊢ t ~ u ↓ B
decConv↓Term-ne-ins () (ℕ-ins x)
decConv↓Term-ne-ins () (Empty-ins x)
decConv↓Term-ne-ins neA (ne-ins x x₁ x₂ x₃) = _ , x₃
decConv↓Term-ne-ins () (univ x x₁ x₂)
decConv↓Term-ne-ins () (zero-refl x)
decConv↓Term-ne-ins () (suc-cong x)
decConv↓Term-ne-ins () (η-eq x₁ x₂ x₃ x₄ x₅)

-- Helper function for decidability for impossibility of terms not being equal
-- as neutrals when they are equal as terms and the first is a neutral.
decConv↓Term-ℕ : ∀ {t u t′}
                → Γ ⊢ t [conv↓] u ∷ ℕ
                → Γ ⊢ t ~ t′ ↓ ℕ
                → ¬ (Γ ⊢ t ~ u ↓ ℕ)
                → ⊥
decConv↓Term-ℕ (ℕ-ins x) t~t ¬u~u = ¬u~u x
decConv↓Term-ℕ (ne-ins x x₁ () x₃) t~t ¬u~u
decConv↓Term-ℕ (zero-refl x) ([~] A D whnfB ()) ¬u~u
decConv↓Term-ℕ (suc-cong x) ([~] A D whnfB ()) ¬u~u

-- Helper function for extensional equality of Unit.
decConv↓Term-Unit : ∀ {t u t′ u′}
              → Γ ⊢ t [conv↓] t′ ∷ Unit → Γ ⊢ u [conv↓] u′ ∷ Unit
              → Dec (Γ ⊢ t [conv↓] u ∷ Unit)
decConv↓Term-Unit tConv uConv =
  let t≡t = soundnessConv↓Term tConv
      u≡u = soundnessConv↓Term uConv
      _ , [t] , _ = syntacticEqTerm t≡t
      _ , [u] , _ = syntacticEqTerm u≡u
      _ , tWhnf , _ = whnfConv↓Term tConv
      _ , uWhnf , _ = whnfConv↓Term uConv
  in  yes (η-unit [t] [u] tWhnf uWhnf)

-- Helper function for Σ-η.
decConv↓Term-Σ-η : ∀ {t u q F G}
                  → Γ ⊢ t ∷ Σ q ▷ F ▹ G
                  → Γ ⊢ u ∷ Σ q ▷ F ▹ G
                  → Product t
                  → Product u
                  → Γ ⊢ fst t [conv↑] fst u ∷ F
                  → Dec (Γ ⊢ snd t [conv↑] snd u ∷ G [ fst t ])
                  → Dec (Γ ⊢ t [conv↓] u ∷ Σ q ▷ F ▹ G)
decConv↓Term-Σ-η ⊢t ⊢u tProd uProd fstConv (yes Q) =
  yes (Σ-η ⊢t ⊢u tProd uProd fstConv Q)
decConv↓Term-Σ-η ⊢t ⊢u tProd uProd fstConv (no ¬Q) =
  no (λ {(Σ-η _ _ _ _ _ Q) → ¬Q Q})



mutual
  -- Decidability of algorithmic equality of neutrals.
  dec~↑ : ∀ {k l R T k′ l′}
        → Γ ⊢ k ~ k′ ↑ R → Γ ⊢ l ~ l′ ↑ T
        → Dec (∃ λ A → Γ ⊢ k ~ l ↑ A)
  dec~↑ (var-refl {n} x₂ x≡y) (var-refl {m} x₃ x≡y₁) with n ≟ⱽ m
  ... | yes PE.refl = yes (_ , (var-refl x₂ PE.refl))
  ... | no ¬p = no (λ { (A , k~l) → ¬p (strongVarEq k~l) })
  dec~↑ (var-refl x₁ x≡y) (app-cong x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑ (var-refl x₁ x≡y) (fst-cong x₂) = no (λ { (_ , ()) })
  dec~↑ (var-refl x₁ x≡y) (snd-cong x₂) = no (λ { (_ , ()) })
  dec~↑ (var-refl x₁ x≡y) (natrec-cong x₂ x₃ x₄ x₅ x₆ x₇) = no (λ { (_ , ()) })
  dec~↑ (var-refl x₁ x≡y) (Emptyrec-cong x₂ x₃ x₄) = no (λ { (_ , ()) })

  dec~↑ (app-cong x x₁ p₃≈p₁ p₃≈p₁′) (app-cong x₂ x₃ p≈p₂ p≈p₂′)
        with dec~↓ x x₂
  ... | yes (A , k~l) =
    let whnfA , neK , neL = ne~↓ k~l
        ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓ k~l)
        _ , ⊢l₁ , _ = syntacticEqTerm (soundness~↓ x)
        _ , ⊢l₂ , _ = syntacticEqTerm (soundness~↓ x₂)
        ΠFG≡A = neTypeEq neK ⊢l₁ ⊢k
        ΠF′G′≡A = neTypeEq neL ⊢l₂ ⊢l
        F≡F′ , G≡G′ , p₃≈p , q≈q′ = injectivity (trans ΠFG≡A (sym ΠF′G′≡A))
        ⊢l₂′ = conv ⊢l₂ (trans ΠF′G′≡A (sym ΠFG≡A))
    in  dec~↑-app ⊢l₁ ⊢l₂′ k~l p₃≈p₁ (≈-trans p₃≈p p≈p₂) (decConv↑TermConv F≡F′ x₁ x₃)
  ... | no ¬p = no (λ { (_ , app-cong x₄ x₅ x₆ x₇) → ¬p (_ , x₄) })
  dec~↑ (app-cong x₁ x₂ _ _) (var-refl x₃ x≡y) = no (λ { (_ , ()) })
  dec~↑ (app-cong x x₁ _ _) (fst-cong x₂) = no (λ { (_ , ()) })
  dec~↑ (app-cong x x₁ _ _) (snd-cong x₂) = no (λ { (_ , ()) })
  dec~↑ (app-cong x x₁ _ _) (natrec-cong x₂ x₃ x₄ x₅ _ _) = no (λ { (_ , ()) })
  dec~↑ (app-cong x x₁ _ _) (Emptyrec-cong x₂ x₃ _) = no (λ { (_ , ()) })

  dec~↑ (fst-cong {k} k~k) (fst-cong {l} l~l) with dec~↓ k~k l~l
  ... | yes (A , k~l) =
    let whnfA , neK , neL = ne~↓ k~l
        ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓ k~l)
        _ , ⊢k₁ , _ = syntacticEqTerm (soundness~↓ k~k)
        ΣFG≡A = neTypeEq neK ⊢k₁ ⊢k
        q , F , G , A≡ΣFG = Σ≡A ΣFG≡A whnfA
    in  yes (F , fst-cong (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x)
                          A≡ΣFG
                          k~l))
  ... | no ¬p = no (λ { (_ , fst-cong x₂) → ¬p (_ , x₂) })
  dec~↑ (fst-cong x) (var-refl x₁ x₂) = no (λ { (_ , ()) })
  dec~↑ (fst-cong x) (app-cong x₁ x₂ _ _) = no (λ { (_ , ()) })
  dec~↑ (fst-cong x) (snd-cong x₁) = no (λ { (_ , ()) })
  dec~↑ (fst-cong x) (natrec-cong x₁ x₂ x₃ x₄ _ _) = no (λ { (_ , ()) })
  dec~↑ (fst-cong x) (Emptyrec-cong x₁ x₂ _) = no (λ { (_ , ()) })

  dec~↑ (snd-cong {k} k~k) (snd-cong {l} l~l) with dec~↓ k~k l~l
  ... | yes (A , k~l) =
    let whnfA , neK , neL = ne~↓ k~l
        ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓ k~l)
        _ , ⊢k₁ , _ = syntacticEqTerm (soundness~↓ k~k)
        ΣFG≡A = neTypeEq neK ⊢k₁ ⊢k
        q , F , G , A≡ΣFG = Σ≡A ΣFG≡A whnfA
    in  yes (G [ fst k ] , snd-cong (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x)
                                    A≡ΣFG
                                    k~l))
  ... | no ¬p = no (λ { (_ , snd-cong x₂) → ¬p (_ , x₂) })
  dec~↑ (snd-cong x) (var-refl x₁ x₂) = no (λ { (_ , ()) })
  dec~↑ (snd-cong x) (app-cong x₁ x₂ _ _) = no (λ { (_ , ()) })
  dec~↑ (snd-cong x) (fst-cong x₁) = no (λ { (_ , ()) })
  dec~↑ (snd-cong x) (natrec-cong x₁ x₂ x₃ x₄ _ _) = no (λ { (_ , ()) })
  dec~↑ (snd-cong x) (Emptyrec-cong x₁ x₂ _) = no (λ { (_ , ()) })
  dec~↑ (natrec-cong {p = p′} {r = r′} x x₁ x₂ x₃ _ _) (natrec-cong {p = p″} {r = r″} x₄ x₅ x₆ x₇ _ _) with decConv↑ x x₄
  ... | yes p with decConv↑TermConv
                     (substTypeEq (soundnessConv↑ p)
                                  (refl (zeroⱼ (wfEqTerm (soundness~↓ x₃))))) x₁ x₅
                 | decConv↑TermConv (sucCong (soundnessConv↑ p)) x₂
                                    (stabilityConv↑Term (reflConEq (wfEq (soundnessConv↑ x)) ∙ sym (soundnessConv↑ p)) x₆)
                 | dec~↓ x₃ x₇
                 | p′ ≟ p″
                 | r′ ≟ r″
  ... | yes p₁ | yes p₂ | yes (A , k~l) | yes p′≈p″ | yes r′≈r″ =
    let whnfA , neK , neL = ne~↓ k~l
        ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓ k~l)
        _ , ⊢l∷ℕ , _ = syntacticEqTerm (soundness~↓ x₃)
        ⊢ℕ≡A = neTypeEq neK ⊢l∷ℕ ⊢k
        A≡ℕ = ℕ≡A ⊢ℕ≡A whnfA
        k~l′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) A≡ℕ k~l
    in  yes (_ , (natrec-cong p p₁ p₂ k~l′ p′≈p″ r′≈r″))
  ... | yes p₁ | yes p₂ | yes (A , k~l) | yes p′≈p″ | no ¬r′≈r″ =
    no (λ { (_ , natrec-cong x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃) → ¬r′≈r″ x₁₃ })
  ... | yes p₁ | yes p₂ | yes (A , k~l) | no ¬p′≈p″ | _ =
    no (λ { (_ , natrec-cong x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃) → ¬p′≈p″ x₁₂ })
  ... | yes p₁ | yes p₂ | no ¬p | _ | _ =
    no (λ { (_ , natrec-cong x₈ x₉ x₁₀ x₁₁ _ _) → ¬p (_ , x₁₁) })
  ... | yes p₁ | no ¬p | r | _ | _ =
    no (λ { (_ , natrec-cong x₈ x₉ x₁₀ x₁₁ _ _) → ¬p x₁₀ })
  ... | no ¬p | w | r | _ | _ =
    no (λ { (_ , natrec-cong x₈ x₉ x₁₀ x₁₁ _ _) → ¬p x₉ })
  dec~↑ (natrec-cong x x₁ x₂ x₃ _ _) (natrec-cong x₄ x₅ x₆ x₇ _ _)
    | no ¬p = no (λ { (_ , natrec-cong x₈ x₉ x₁₀ x₁₁ _ _) → ¬p x₈})
  dec~↑ (natrec-cong _ _ _ _ _ _) (var-refl _ _) = no (λ { (_ , ()) })
  dec~↑ (natrec-cong _ _ _ _ _ _) (fst-cong _) = no (λ { (_ , ()) })
  dec~↑ (natrec-cong _ _ _ _ _ _) (snd-cong _) = no (λ { (_ , ()) })
  dec~↑ (natrec-cong _ _ _ _ _ _) (app-cong _ _ _ _) = no (λ { (_ , ()) })
  dec~↑ (natrec-cong _ _ _ _ _ _) (Emptyrec-cong _ _ _) = no (λ { (_ , ()) })

  dec~↑ (Emptyrec-cong {p = p′} x x₁ eq) (Emptyrec-cong {p = p″} x₄ x₅ eq′)
        with decConv↑ x x₄ | dec~↓ x₁ x₅ | p′ ≟ p″
  ... | yes p | yes (A , k~l) | yes p′≈p″ =
    let whnfA , neK , neL = ne~↓ k~l
        ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓ k~l)
        _ , ⊢l∷Empty , _ = syntacticEqTerm (soundness~↓ x₁)
        ⊢Empty≡A = neTypeEq neK ⊢l∷Empty ⊢k
        A≡Empty = Empty≡A ⊢Empty≡A whnfA
        k~l′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) A≡Empty k~l
    in  yes (_ , Emptyrec-cong p k~l′ p′≈p″)
  ... | yes p | yes (A , k~l) | no ¬p′≈p″ = no (λ { (_ , Emptyrec-cong a b p′≈p″) → ¬p′≈p″ p′≈p″ })
  ... | yes p | no ¬p | _ = no (λ { (_ , Emptyrec-cong a b _) → ¬p (_ , b) })
  ... | no ¬p | r | _ = no (λ { (_ , Emptyrec-cong a b _) → ¬p a })
  dec~↑ (Emptyrec-cong _ _ _) (var-refl _ _) = no (λ { (_ , ()) })
  dec~↑ (Emptyrec-cong _ _ _) (fst-cong _) = no (λ { (_ , ()) })
  dec~↑ (Emptyrec-cong _ _ _) (snd-cong _) = no (λ { (_ , ()) })
  dec~↑ (Emptyrec-cong _ _ _) (app-cong _ _ _ _) = no (λ { (_ , ()) })
  dec~↑ (Emptyrec-cong _ _ _) (natrec-cong _ _ _ _ _ _) = no (λ { (_ , ()) })

  dec~↑′ : ∀ {k l R T}
        → ⊢ Γ ≡ Δ
        → Γ ⊢ k ~ k ↑ R → Δ ⊢ l ~ l ↑ T
        → Dec (∃ λ A → Γ ⊢ k ~ l ↑ A)
  dec~↑′ Γ≡Δ k~k l~l = dec~↑ k~k (stability~↑ (symConEq Γ≡Δ) l~l)

  -- Decidability of algorithmic equality of neutrals with types in WHNF.
  dec~↓ : ∀ {k l R T k′ l′}
        → Γ ⊢ k ~ k′ ↓ R → Γ ⊢ l ~ l′ ↓ T
        → Dec (∃ λ A → Γ ⊢ k ~ l ↓ A)
  dec~↓ ([~] A D whnfB k~l) ([~] A₁ D₁ whnfB₁ k~l₁) with dec~↑ k~l k~l₁
  dec~↓ ([~] A D whnfB k~l) ([~] A₁ D₁ whnfB₁ k~l₁) | yes (B , k~l₂) =
    let ⊢B , _ , _ = syntacticEqTerm (soundness~↑ k~l₂)
        C , whnfC , D′ = whNorm ⊢B
    in  yes (C , [~] B (red D′) whnfC k~l₂)
  dec~↓ ([~] A D whnfB k~l) ([~] A₁ D₁ whnfB₁ k~l₁) | no ¬p =
    no (λ { (A₂ , [~] A₃ D₂ whnfB₂ k~l₂) → ¬p (A₃ , k~l₂) })

  -- Decidability of algorithmic equality of types.
  decConv↑ : ∀ {A B A′ B′}
           → Γ ⊢ A [conv↑] A′ → Γ ⊢ B [conv↑] B′
           → Dec (Γ ⊢ A [conv↑] B)
  decConv↑ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′)
               ([↑] A″ B″ D₁ D″ whnfA″ whnfB″ A′<>B″)
           with decConv↓ A′<>B′ A′<>B″
  decConv↑ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′)
               ([↑] A″ B″ D₁ D″ whnfA″ whnfB″ A′<>B″) | yes p =
    yes ([↑] A′ A″ D D₁ whnfA′ whnfA″ p)
  decConv↑ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′)
               ([↑] A″ B″ D₁ D″ whnfA″ whnfB″ A′<>B″) | no ¬p =
    no (λ { ([↑] A‴ B‴ D₂ D‴ whnfA‴ whnfB‴ A′<>B‴) →
        let A‴≡B′ = whrDet* (D₂ , whnfA‴) (D , whnfA′)
            B‴≡B″ = whrDet* (D‴ , whnfB‴) (D₁ , whnfA″)
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
  decConv↓ (Unit-refl x) (Unit-refl x₁) = yes (Unit-refl x)

  -- Inspective cases
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

  decConv↓ (Π-cong {p = p′} {q = q′} x x₁ x₂ eq₁ eq₂) (Π-cong {p = p″} {q = q″} x₃ x₄ x₅ eq₃ eq₄)
           with decConv↑ x₁ x₄
  ... | yes p with decConv↑′ (reflConEq (wf x) ∙ soundnessConv↑ p) x₂ x₅ | p′ ≟ p″ | q′ ≟ q″
  ... | yes p₁ | yes p′≈p″ | yes q′≈q″ = yes (Π-cong x p p₁ p′≈p″ q′≈q″)
  ... | yes p₁ | yes p′≈p″ | no ¬q′≈q″ = no (λ { (ne ([~] A D whnfB ())) ; (Π-cong x₆ x₇ x₈ x₉ x₁₀) → ¬q′≈q″ x₁₀ })
  ... | yes p₁ | no ¬p′≈p″ | _ = no (λ { (ne ([~] A D whnfB ())) ; (Π-cong x₆ x₇ x₈ x₉ x₁₀) → ¬p′≈p″ x₉ })
  ... | no ¬p | _ | _ = no (λ { (ne ([~] A D whnfB ())) ; (Π-cong x₆ x₇ x₈ _ _) → ¬p x₈ })
  decConv↓ (Π-cong x x₁ x₂ _ _) (Π-cong x₃ x₄ x₅ _ _) | no ¬p =
    no (λ { (ne ([~] A D whnfB ())) ; (Π-cong x₆ x₇ x₈ _ _) → ¬p x₇ })

  decConv↓ (Σ-cong {q = q} x x₁ x₂ eq) (Σ-cong {q = q′} x₃ x₄ x₅ eq′)
           with decConv↑ x₁ x₄
  ... | yes p with decConv↑′ (reflConEq (wf x) ∙ soundnessConv↑ p) x₂ x₅ | q ≟ q′
  ... | yes p₁ | yes q≈q′ = yes (Σ-cong x p p₁ q≈q′)
  ... | yes p₁ | no ¬q≈q′ = no (λ { (ne ([~] A D whnfB ())) ; (Σ-cong x₆ x₇ x₈ x₉) → ¬q≈q′ x₉ })
  ... | no ¬p | _ = no (λ { (ne ([~] A D whnfB ())) ; (Σ-cong x₆ x₇ x₈ _) → ¬p x₈ })
  decConv↓ (Σ-cong x x₁ x₂ _) (Σ-cong x₃ x₄ x₅ _) | no ¬p =
    no (λ { (ne ([~] A D whnfB ())) ; (Σ-cong x₆ x₇ x₈ _) → ¬p x₇ })

  -- False cases
  decConv↓ (U-refl x) (ℕ-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (U-refl x) (Empty-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (U-refl x) (Unit-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (U-refl x) (ne x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓ x₁
               in  ⊥-elim (IE.U≢ne neK (soundnessConv↓ x₂)))
  decConv↓ (U-refl x) (Π-cong x₁ x₂ x₃ _ _) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (U-refl x) (Σ-cong x₁ x₂ x₃ _) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (ℕ-refl x) (U-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (ℕ-refl x) (Empty-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (ℕ-refl x) (Unit-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (ℕ-refl x) (ne x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓ x₁
               in  ⊥-elim (IE.ℕ≢ne neK (soundnessConv↓ x₂)))
  decConv↓ (ℕ-refl x) (Π-cong x₁ x₂ x₃ _ _) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (ℕ-refl x) (Σ-cong x₁ x₂ x₃ _) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Empty-refl x) (U-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Empty-refl x) (ℕ-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Empty-refl x) (Unit-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Empty-refl x) (ne x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓ x₁
               in  ⊥-elim (IE.Empty≢neⱼ neK (soundnessConv↓ x₂)))
  decConv↓ (Empty-refl x) (Π-cong x₁ x₂ x₃ _ _) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Empty-refl x) (Σ-cong x₁ x₂ x₃ _) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Unit-refl x) (U-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Unit-refl x) (ℕ-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Unit-refl x) (Empty-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Unit-refl x) (ne x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓ x₁
               in  ⊥-elim (IE.Unit≢neⱼ neK (soundnessConv↓ x₂)))
  decConv↓ (Unit-refl x) (Π-cong x₁ x₂ x₃ _ _) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Unit-refl x) (Σ-cong x₁ x₂ x₃ _) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (ne x) (U-refl x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓ x
               in  ⊥-elim (IE.U≢ne neK (sym (soundnessConv↓ x₂))))
  decConv↓ (ne x) (ℕ-refl x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓ x
               in  ⊥-elim (IE.ℕ≢ne neK (sym (soundnessConv↓ x₂))))
  decConv↓ (ne x) (Empty-refl x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓ x
               in  ⊥-elim (IE.Empty≢neⱼ neK (sym (soundnessConv↓ x₂))))
  decConv↓ (ne x) (Unit-refl x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓ x
               in  ⊥-elim (IE.Unit≢neⱼ neK (sym (soundnessConv↓ x₂))))
  decConv↓ (ne x) (Π-cong x₁ x₂ x₃ _ _) =
    no (λ x₄ → let whnfA , neK , neL = ne~↓ x
               in  ⊥-elim (IE.Π≢ne neK (sym (soundnessConv↓ x₄))))
  decConv↓ (ne x) (Σ-cong x₁ x₂ x₃ _) =
    no (λ x₄ → let whnfA , neK , neL = ne~↓ x
               in  ⊥-elim (IE.Σ≢ne neK (sym (soundnessConv↓ x₄))))
  decConv↓ (Π-cong x x₁ x₂ _ _) (U-refl x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Π-cong x x₁ x₂ _ _) (ℕ-refl x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Π-cong x x₁ x₂ _ _) (Empty-refl x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Π-cong x x₁ x₂ _ _) (Unit-refl x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Π-cong x x₁ x₂ _ _) (Σ-cong x₃ x₄ x₅ _) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Π-cong x x₁ x₂ _ _) (ne x₃) =
    no (λ x₄ → let whnfA , neK , neL = ne~↓ x₃
               in  ⊥-elim (IE.Π≢ne neK (soundnessConv↓ x₄)))
  decConv↓ (Σ-cong x x₁ x₂ _) (U-refl x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Σ-cong x x₁ x₂ _) (ℕ-refl x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Σ-cong x x₁ x₂ _) (Empty-refl x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Σ-cong x x₁ x₂ _) (Unit-refl x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Σ-cong x x₁ x₂ _) (Π-cong x₃ x₄ x₅ _ _) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ (Σ-cong x x₁ x₂ _) (ne x₃) =
    no (λ x₄ → let whnfA , neK , neL = ne~↓ x₃
               in  ⊥-elim (IE.Σ≢ne neK (soundnessConv↓ x₄)))

  -- Helper function for decidability of neutral types.
  decConv↓-ne : ∀ {A B A′}
              → Γ ⊢ A [conv↓] B
              → Γ ⊢ A ~ A′ ↓ U
              → Γ ⊢ A ~ B ↓ U
  decConv↓-ne (U-refl x) ()
  decConv↓-ne (ℕ-refl x) ()
  decConv↓-ne (Empty-refl x) ()
  decConv↓-ne (ne x) A~A = x
  decConv↓-ne (Π-cong x x₁ x₂ _ _) ([~] A D whnfB ())

  -- Decidability of algorithmic equality of terms.
  decConv↑Term : ∀ {t u A t′ u′}
               → Γ ⊢ t [conv↑] t′ ∷ A → Γ ⊢ u [conv↑] u′ ∷ A
               → Dec (Γ ⊢ t [conv↑] u ∷ A)
  decConv↑Term ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u)
               ([↑]ₜ B₁ t″ u″ D₁ d₁ d″ whnfB₁ whnft″ whnfu″ t<>u₁)
               rewrite whrDet* (D , whnfB) (D₁ , whnfB₁)
                 with decConv↓Term t<>u t<>u₁
  decConv↑Term ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u)
               ([↑]ₜ B₁ t″ u″ D₁ d₁ d″ whnfB₁ whnft″ whnfu″ t<>u₁)
               | yes p = yes ([↑]ₜ B₁ t′ t″ D₁ d d₁ whnfB₁ whnft′ whnft″ p)
  decConv↑Term ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u)
               ([↑]ₜ B₁ t″ u″ D₁ d₁ d″ whnfB₁ whnft″ whnfu″ t<>u₁)
               | no ¬p =
    no (λ { ([↑]ₜ B₂ t‴ u‴ D₂ d₂ d‴ whnfB₂ whnft‴ whnfu‴ t<>u₂) →
        let B₂≡B₁ = whrDet* (D₂ , whnfB₂) (D₁ , whnfB₁)
            t‴≡u′ = whrDet*Term (d₂ , whnft‴)
                                (PE.subst (λ x → _ ⊢ _ ⇒* _ ∷ x) (PE.sym B₂≡B₁) d , whnft′)
            u‴≡u″ = whrDet*Term (d‴ , whnfu‴)
                                (PE.subst (λ x → _ ⊢ _ ⇒* _ ∷ x) (PE.sym B₂≡B₁) d₁ , whnft″)
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
  decConv↓Term (Unit-ins t~t) uConv = decConv↓Term-Unit (Unit-ins t~t) uConv
  decConv↓Term (η-unit [t] _ tUnit _) uConv =
    decConv↓Term-Unit (η-unit [t] [t] tUnit tUnit) uConv

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
  decConv↓Term (ne-ins x x₁ x₂ x₃) (ne-ins x₄ x₅ x₆ x₇)
               with dec~↓ x₃ x₇
  decConv↓Term (ne-ins x x₁ x₂ x₃) (ne-ins x₄ x₅ x₆ x₇) | yes (A , k~l) =
    yes (ne-ins x x₄ x₆ k~l)
  decConv↓Term (ne-ins x x₁ x₂ x₃) (ne-ins x₄ x₅ x₆ x₇) | no ¬p =
    no (λ x₈ → ¬p (decConv↓Term-ne-ins x₆ x₈))
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
    no (λ { (ℕ-ins ([~] A D whnfB ()))
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
  decConv↓Term (η-eq {p = p} {f = t} x₁ x₂ x₃ x₄ x₅) (η-eq {f = u} x₇ x₈ x₉ x₁₀ x₁₁)
    with decConv↑Term (x₅ ≈-refl ≈-refl) (x₁₁ ≈-refl ≈-refl)
  ... | yes P = yes (η-eq x₁ x₇ x₃ x₉ (λ x x₆ →
    let ⊢F , ⊢G = syntacticΠ (syntacticTerm x₁)
        G≡G = refl ⊢G
    in  transConv↑Term G≡G (x₅ x ≈-refl)
                       (transConv↑Term G≡G (symConvTerm (x₅ ≈-refl ≈-refl))
                       (transConv↑Term G≡G P
                       (transConv↑Term G≡G (x₁₁ ≈-refl x₆)
                       (symConvTerm (x₁₁ x₆ x₆)))))))
  ... | no ¬P = no (λ { (ne-ins x₁₂ x₁₃ () x₁₅)
                      ; (η-eq x₁₃ x₁₄ x₁₅ x₁₆ x₁₇) → ¬P (x₁₇ ≈-refl ≈-refl) })

  -- False cases
  decConv↓Term  (ℕ-ins x) (zero-refl x₁) =
    no (λ x₂ → decConv↓Term-ℕ x₂ x λ { ([~] A D whnfB ()) })
  decConv↓Term  (ℕ-ins x) (suc-cong x₁) =
    no (λ x₂ → decConv↓Term-ℕ x₂ x (λ { ([~] A D whnfB ()) }))
  decConv↓Term  (zero-refl x) (ℕ-ins x₁) =
    no (λ x₂ → decConv↓Term-ℕ (symConv↓Term′ x₂) x₁ (λ { ([~] A D whnfB ()) }))
  decConv↓Term  (zero-refl x) (suc-cong x₁) =
    no (λ { (ℕ-ins ([~] A D whnfB ())) ; (ne-ins x₂ x₃ () x₅) })
  decConv↓Term  (suc-cong x) (ℕ-ins x₁) =
    no (λ x₂ → decConv↓Term-ℕ (symConv↓Term′ x₂) x₁ (λ { ([~] A D whnfB ()) }))
  decConv↓Term  (suc-cong x) (zero-refl x₁) =
    no (λ { (ℕ-ins ([~] A D whnfB ())) ; (ne-ins x₂ x₃ () x₅) })

  -- Decidability of algorithmic equality of terms of equal types.
  decConv↑TermConv : ∀ {t u A B t′ u′}
                → Γ ⊢ A ≡ B
                → Γ ⊢ t [conv↑] t′ ∷ A
                → Γ ⊢ u [conv↑] u′ ∷ B
                → Dec (Γ ⊢ t [conv↑] u ∷ A)
  decConv↑TermConv A≡B t u =
    decConv↑Term t (convConvTerm u (sym A≡B))
