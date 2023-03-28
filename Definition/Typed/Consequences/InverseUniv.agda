module Definition.Typed.Consequences.InverseUniv
  {a} (M : Set a) where

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed M
open import Definition.Typed.Consequences.Syntactic M

open import Tools.Nat
import Tools.Sum as Sum
open import Tools.Sum using (_⊎_; inj₁; inj₂)
open import Tools.Product
open import Tools.Empty
open import Tools.Nullary

private
  variable
    n : Nat
    Γ : Con Term n
    A F H : Term n
    G E : Term (1+ n)
    p p′ q q′ : M
    b : BinderMode

-- Proposition for terms if they contain a U.
data UFull : Term n → Set a where
  ∃U   : UFull {n} U
  ∃ΠΣ₁ : UFull F → UFull (ΠΣ⟨ b ⟩ p , q ▷ F ▹ G)
  ∃ΠΣ₂ : UFull G → UFull (ΠΣ⟨ b ⟩ p , q ▷ F ▹ G)

-- Terms cannot contain U.
noU : ∀ {t A} → Γ ⊢ t ∷ A → ¬ (UFull t)
noU (ℕⱼ x) ()
noU (Emptyⱼ x) ()
noU (ΠΣⱼ t ▹ t₁) (∃ΠΣ₁ ufull) = noU t ufull
noU (ΠΣⱼ t ▹ t₁) (∃ΠΣ₂ ufull) = noU t₁ ufull
noU (var x₁ x₂) ()
noU (lamⱼ x t₁) ()
noU (t ∘ⱼ t₁) ()
noU (zeroⱼ x) ()
noU (sucⱼ t) ()
noU (natrecⱼ x t t₁ t₂) ()
noU (Emptyrecⱼ x t) ()
noU (conv t₁ x) ufull = noU t₁ ufull

-- Neutrals cannot contain U.
noUNe : Neutral A → ¬ (UFull A)
noUNe (var n) ()
noUNe (∘ₙ neA) ()
noUNe (natrecₙ neA) ()
noUNe (Emptyrecₙ neA) ()

-- Helper function where if at least one Π-type does not contain U,
-- one of F and H will not contain U and one of G and E will not contain U.
pilem :
  (¬ UFull (ΠΣ⟨ b ⟩ p , q ▷ F ▹ G)) ⊎
    (¬ UFull (ΠΣ⟨ b ⟩ p′ , q′ ▷ H ▹ E)) →
  (¬ UFull F) ⊎ (¬ UFull H) × (¬ UFull G) ⊎ (¬ UFull E)
pilem (inj₁ x) = inj₁ (λ x₁ → x (∃ΠΣ₁ x₁)) , inj₁ (λ x₁ → x (∃ΠΣ₂ x₁))
pilem (inj₂ x) = inj₂ (λ x₁ → x (∃ΠΣ₁ x₁)) , inj₂ (λ x₁ → x (∃ΠΣ₂ x₁))

-- If type A does not contain U, then A can be a term of type U.
inverseUniv : ∀ {A} → ¬ (UFull A) → Γ ⊢ A → Γ ⊢ A ∷ U
inverseUniv q (ℕⱼ x) = ℕⱼ x
inverseUniv q (Emptyⱼ x) = Emptyⱼ x
inverseUniv q (Unitⱼ x) = Unitⱼ x
inverseUniv q (Uⱼ x) = ⊥-elim (q ∃U)
inverseUniv q (ΠΣⱼ A ▹ A₁) =
  ΠΣⱼ inverseUniv (λ x → q (∃ΠΣ₁ x)) A ▹
      inverseUniv (λ x → q (∃ΠΣ₂ x)) A₁
inverseUniv q (univ x) = x

-- If A is a neutral type, then A can be a term of U.
inverseUnivNe : ∀ {A} → Neutral A → Γ ⊢ A → Γ ⊢ A ∷ U
inverseUnivNe neA ⊢A = inverseUniv (noUNe neA) ⊢A

-- Helper function where if at least one type does not contain U, then the
-- equality of types can be an equality of term of type U.
inverseUnivEq′ : ∀ {A B} → (¬ (UFull A)) ⊎ (¬ (UFull B)) → Γ ⊢ A ≡ B → Γ ⊢ A ≡ B ∷ U
inverseUnivEq′ q (univ x) = x
inverseUnivEq′ q (refl x) = refl (inverseUniv (Sum.id q) x)
inverseUnivEq′ q (sym A≡B) = sym (inverseUnivEq′ (Sum.sym q) A≡B)
inverseUnivEq′ (inj₁ x) (trans A≡B A≡B₁) =
  let w = inverseUnivEq′ (inj₁ x) A≡B
      _ , _ , t = syntacticEqTerm w
      y = noU t
  in  trans w (inverseUnivEq′ (inj₁ y) A≡B₁)
inverseUnivEq′ (inj₂ x) (trans A≡B A≡B₁) =
  let w = inverseUnivEq′ (inj₂ x) A≡B₁
      _ , t , _ = syntacticEqTerm w
      y = noU t
  in  trans (inverseUnivEq′ (inj₂ y) A≡B) w
inverseUnivEq′ q (ΠΣ-cong x A≡B A≡B₁) =
  let w , e = pilem q
  in  ΠΣ-cong x (inverseUnivEq′ w A≡B) (inverseUnivEq′ e A≡B₁)

-- If A is a term of U, then the equality of types is an equality of terms of type U.
inverseUnivEq : ∀ {A B} → Γ ⊢ A ∷ U → Γ ⊢ A ≡ B → Γ ⊢ A ≡ B ∷ U
inverseUnivEq A A≡B = inverseUnivEq′ (inj₁ (noU A)) A≡B
