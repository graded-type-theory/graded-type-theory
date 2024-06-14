------------------------------------------------------------------------
-- Equality lemmata.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.Equality
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.RedSteps R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Fundamental.Reducibility R
open import Definition.LogicalRelation.Substitution.Introductions R

open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE

private
  variable
    n         : Nat
    Γ         : Con Term n
    A B C t u : Term _
    b         : BinderMode
    p q       : M
    s         : Strength

opaque

  -- If A is judgmentally equal to U, then A is propositionally equal
  -- to U.

  U≡A : Γ ⊢ U ≡ A → A PE.≡ U
  U≡A = proj₂ ∘→ proj₂ ∘→ ⊩U≡⇔ .proj₁ ∘→ reducible-⊩≡

opaque

  -- If the WHNF A is judgmentally equal to ℕ, then A is
  -- propositionally equal to ℕ.

  ℕ≡A : Γ ⊢ ℕ ≡ A → Whnf A → A PE.≡ ℕ
  ℕ≡A {Γ} {A} ℕ≡A A-whnf =
                $⟨ ℕ≡A ⟩
    Γ ⊢ ℕ ≡ A   →⟨ ⊩ℕ≡⇔ .proj₁ ∘→ reducible-⊩≡ ⟩
    Γ ⊩ℕ ℕ ≡ A  ≡⟨ PE.refl ⟩→
    Γ ⊢ A ⇒* ℕ  →⟨ flip whnfRed* A-whnf ⟩
    A PE.≡ ℕ    □

opaque

  -- If the WHNF A is judgmentally equal to Empty, then A is
  -- propositionally equal to Empty.

  Empty≡A : Γ ⊢ Empty ≡ A → Whnf A → A PE.≡ Empty
  Empty≡A {Γ} {A} Empty≡A A-whnf =
                        $⟨ Empty≡A ⟩
    Γ ⊢ Empty ≡ A       →⟨ ⊩Empty≡⇔ .proj₁ ∘→ reducible-⊩≡ ⟩
    Γ ⊩Empty Empty ≡ A  ≡⟨ PE.refl ⟩→
    Γ ⊢ A ⇒* Empty      →⟨ flip whnfRed* A-whnf ⟩
    A PE.≡ Empty        □

opaque

  -- If the WHNF A is judgmentally equal to Unit s, then A is
  -- propositionally equal to Unit s.

  Unit≡A : Γ ⊢ Unit s ≡ A → Whnf A → A PE.≡ Unit s
  Unit≡A {Γ} {s} {A} Unit≡A A-whnf =
                         $⟨ Unit≡A ⟩
    Γ ⊢ Unit s ≡ A       →⟨ reducible-⊩≡ ⟩
    Γ ⊩⟨ ¹ ⟩ Unit s ≡ A  →⟨ proj₂ ∘→ proj₂ ∘→ ⊩Unit≡⇔ .proj₁ ⟩
    Γ ⊢ A ⇒* Unit s      →⟨ flip whnfRed* A-whnf ⟩
    A PE.≡ Unit s        □

opaque

  -- If the neutral term B is judgmentally equal to the WHNF A, then A
  -- is neutral.

  ne≡A : Neutral B → Γ ⊢ B ≡ A → Whnf A → Neutral A
  ne≡A {B} {Γ} {A} B-ne B≡A A-whnf =  $⟨ B≡A ⟩
    Γ ⊢ B ≡ A                         →⟨ reducible-⊩≡ ⟩
    Γ ⊩⟨ ¹ ⟩ B ≡ A                    →⟨ Σ.map idᶠ (Σ.map idᶠ (proj₁ ∘→ proj₂)) ∘→ proj₂ ∘→ ⊩ne≡⇔ B-ne .proj₁ ⟩
    (∃ λ C → Neutral C × Γ ⊢ A ⇒* C)  →⟨ (λ (_ , C-ne , A⇒*C) →
                                            PE.subst Neutral (PE.sym $ whnfRed* A⇒*C A-whnf) C-ne) ⟩
    Neutral A                         □

opaque

  -- If a WHNF C is definitionally equal to ΠΣ⟨ b ⟩ p , q ▷ A ▹ B, then
  -- C has the shape ΠΣ⟨ b ⟩ p , q ▷ _ ▹ _.

  ΠΣ≡Whnf :
    Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ≡ C → Whnf C →
    ∃₂ λ A′ B′ → C PE.≡ ΠΣ⟨ b ⟩ p , q ▷ A′ ▹ B′
  ΠΣ≡Whnf {Γ} {b} {p} {q} {A} {B} {C} ΠΣ≡C C-whnf =    $⟨ ΠΣ≡C ⟩
    Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ≡ C                      →⟨ reducible-⊩≡ ⟩
    Γ ⊩⟨ ¹ ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ≡ C                 →⟨ Σ.map idᶠ (Σ.map idᶠ proj₁) ∘→ proj₂ ∘→ proj₂ ∘→ ⊩ΠΣ≡⇔ .proj₁ ⟩
    (∃₂ λ A′ B′ → Γ ⊢ C :⇒*: ΠΣ⟨ b ⟩ p , q ▷ A′ ▹ B′)  →⟨ Σ.map idᶠ $ Σ.map idᶠ (flip whnfRed* C-whnf ∘→ red) ⟩
    (∃₂ λ A′ B′ → C PE.≡ ΠΣ⟨ b ⟩ p , q ▷ A′ ▹ B′)      □

opaque

  -- If a WHNF A is definitionally equal to Π p , q ▷ B ▹ C, then A
  -- has the shape Π p , q ▷ _ ▹ _.

  Π≡A :
    Γ ⊢ Π p , q ▷ B ▹ C ≡ A → Whnf A →
    ∃₂ λ B′ C′ → A PE.≡ Π p , q ▷ B′ ▹ C′
  Π≡A = ΠΣ≡Whnf

opaque

  -- If a WHNF A is definitionally equal to Σ⟨ s ⟩ p , q ▷ B ▹ C, then
  -- A has the shape Σ⟨ s ⟩ p , q ▷ _ ▹ _.

  Σ≡A :
    Γ ⊢ Σ⟨ s ⟩ p , q ▷ B ▹ C ≡ A → Whnf A →
    ∃₂ λ B′ C′ → A PE.≡ Σ⟨ s ⟩ p , q ▷ B′ ▹ C′
  Σ≡A = ΠΣ≡Whnf

opaque

  -- If the WHNF B is judgmentally equal to Id A t u, then there are
  -- A′, t′ and u′ such that B is propositionally equal to
  -- Id A′ t′ u′.

  Id≡Whnf :
    Γ ⊢ Id A t u ≡ B → Whnf B →
    ∃₃ λ A′ t′ u′ → B PE.≡ Id A′ t′ u′
  Id≡Whnf {Γ} {A} {t} {u} {B} Id≡B B-whnf =   $⟨ Id≡B ⟩
    Γ ⊢ Id A t u ≡ B                          →⟨ reducible-⊩≡ ⟩
    Γ ⊩⟨ ¹ ⟩ Id A t u ≡ B                     →⟨ Σ.map idᶠ (Σ.map idᶠ (Σ.map idᶠ proj₁)) ∘→ proj₂ ∘→ ⊩Id≡⇔ .proj₁ ⟩
    (∃₃ λ A′ t′ u′ → Γ ⊢ B :⇒*: Id A′ t′ u′)  →⟨ Σ.map idᶠ $ Σ.map idᶠ $ Σ.map idᶠ (flip whnfRed* B-whnf ∘→ red) ⟩
    (∃₃ λ A′ t′ u′ → B PE.≡ Id A′ t′ u′)      □

opaque

  -- If t is definitionally equal to rfl, then t reduces to rfl.

  rfl-norm : Γ ⊢ t ≡ rfl ∷ A → Γ ⊢ t ⇒* rfl ∷ A
  rfl-norm t≡rfl =
    case inversion-rfl (syntacticEqTerm t≡rfl .proj₂ .proj₂) of λ
      (_ , _ , _ , _ , A≡Id) →
    case ⊩≡∷Id⇔ .proj₁ $ reducible-⊩≡∷ $ conv t≡rfl A≡Id of λ
      (t′ , _ , t⇒*u , rfl⇒*v , _ , _ , u∼v) →
    case whnfRed*Term (redₜ rfl⇒*v) rflₙ of λ {
      PE.refl →
    case u∼v of λ where
      (rfl₌ _) →
        conv* (redₜ t⇒*u) (sym A≡Id)
      (ne _ () _) }

opaque

  -- If the WHNF t is judgmentally equal to rfl, then t is
  -- propositionally equal to rfl.

  whnf≡rfl : Γ ⊢ t ≡ rfl ∷ A → Whnf t → t PE.≡ rfl
  whnf≡rfl = whnfRed*Term ∘→ rfl-norm
