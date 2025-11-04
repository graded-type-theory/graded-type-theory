------------------------------------------------------------------------
-- Lists defined using vectors
------------------------------------------------------------------------

-- Typing rules for the term formers defined in this module can be
-- found in Definition.Typed.Properties.Admissible.List and usage
-- rules can be found in Graded.Derived.List

import Graded.Modality
import Definition.Untyped
open import Tools.Bool

module Definition.Untyped.List
  {ℓ} {M : Set ℓ}
  (open Graded.Modality M)
  (open Definition.Untyped M)
  (𝕄 : Modality)
  -- The grade of the "heads" and grade of the length component
  (pₕ pₗ : M)
  where

-- Use vectors defined using weak Unit and Σ-types.
import Definition.Untyped.Vec 𝕄 𝕨 pₕ as V

open import Definition.Untyped.Properties M

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.PropositionalEquality
open import Tools.Reasoning.PropositionalEquality

open Modality 𝕄

private variable
  n : Nat
  A P k h t nl cs xs : Term _
  l : Universe-level
  σ : Subst _ _
  ρ : Wk _ _
  p₁ p₂ q r₁ r₂ : M

opaque

  -- The type of lists as a term former
  -- Lists are encoded as a tuple where the first component
  -- represents the length (assigned grade pₗ) and the second
  -- is a vector (of that length).

  List : Universe-level → (A : Term n) → Term n
  List l A = Σʷ pₗ , 𝟙 ▷ ℕ ▹ V.Vec′ l (wk1 A) (var x0)

opaque
  unfolding List

  -- Unfolding of List

  List≡ : List l A ≡ Σʷ pₗ , 𝟙 ▷ ℕ ▹ V.Vec′ l (wk1 A) (var x0)
  List≡ = refl

opaque
  unfolding List

  -- Applying a weakening to List

  List-wk : wk ρ (List l A) ≡ List l (wk ρ A)
  List-wk {ρ} {A}  =
    cong (Σʷ pₗ , 𝟙 ▷ ℕ ▹_)
      (trans V.Vec′-wk
        (cong (λ x → V.Vec′ _ x _) $ begin
          wk (lift ρ) (wk1 A)  ≡⟨ wk-comp (lift ρ) (step id) A ⟩
          wk (step (ρ • id)) A ≡⟨ cong (λ x → wk (step x) A) •-id ⟩
          wk (step ρ) A        ≡˘⟨ wk-comp (step id) ρ A ⟩
          wk1 (wk ρ A)         ∎))

opaque
  unfolding List

  -- Applying a substitution to List

  List-subst : (List l A) [ σ ] ≡ List l (A [ σ ])
  List-subst {l} {A} {σ} =
    cong (Σʷ pₗ , 𝟙 ▷ ℕ ▹_) $ begin
      V.Vec′ l (wk1 A) (var x0) [ σ ⇑ ] ≡⟨ V.Vec′-subst ⟩
      V.Vec′ l (wk1 A [ σ ⇑ ]) (var x0) ≡⟨ cong (λ x → V.Vec′ l x _) (wk1-liftSubst A) ⟩
      V.Vec′ l (wk1 (A [ σ ])) (var x0) ∎

opaque

  -- The empty list as a term former

  nil : Universe-level → (A : Term n) → Term n
  nil l A = prodʷ pₗ zero (V.nil′ l A)

opaque
  unfolding nil

  -- unfolding of nil

  nil≡ : nil l A ≡ prodʷ pₗ zero (V.nil′ l A)
  nil≡ = refl

opaque

  -- cons as a term former

  cons : (l : Universe-level) (A h t : Term n) → Term n
  cons l A h t =
    prodrec 𝟙 pₗ 𝟘 (wk1 (List l A)) t
      (prodʷ pₗ (suc (var x1)) (V.cons′ (wk₂ A) (var x1) (wk₂ h) (var x0)))

opaque
  unfolding cons

  -- unfolding of cons

  cons≡ :
    cons l A h t ≡
    prodrec 𝟙 pₗ 𝟘 (wk1 (List l A)) t
      (prodʷ pₗ (suc (var x1)) (V.cons′ (wk₂ A) (var x1) (wk₂ h) (var x0)))
  cons≡ = refl

opaque

  -- Applying a substition to cons

  cons-subst : cons l A h t [ σ ] ≡ cons l (A [ σ ]) (h [ σ ]) (t [ σ ])
  cons-subst {l} {A} {h} {t} {σ} = begin
    cons l A h t [ σ ]
        ≡⟨ cong (_[ σ ]) cons≡ ⟩
    prodrec 𝟙 pₗ 𝟘 (wk1 (List l A)) t
      (prodʷ pₗ (suc (var x1)) (V.cons′ (wk₂ A) (var x1) (wk₂ h) (var x0))) [ σ ]
        ≡⟨ cong (λ x → prodrec 𝟙 pₗ 𝟘 _ _ (prodʷ pₗ _ x)) V.cons′-subst ⟩
    prodrec 𝟙 pₗ 𝟘 (wk1 (List l A) [ σ ⇑ ]) (t [ σ ])
      (prodʷ pₗ (suc (var x1)) (V.cons′ (wk₂ A [ σ ⇑[ 2 ] ]) (var x1) (wk₂ h [ σ ⇑[ 2 ] ]) (var x0)))
        ≡⟨ cong₃ (λ x y z → prodrec 𝟙 pₗ 𝟘 x _ (prodʷ pₗ _ (V.cons′ y _ z _)))
            (wk1-liftSubst (List l A)) (wk[]′-[⇑] A) (wk[]′-[⇑] h) ⟩
    prodrec 𝟙 pₗ 𝟘 (wk1 (List l A [ σ ])) (t [ σ ])
      (prodʷ pₗ (suc (var x1)) (V.cons′ (wk₂ (A [ σ ])) (var x1) (wk₂ (h [ σ ])) (var x0)))
      ≡⟨ cong (λ x → prodrec 𝟙 pₗ 𝟘 (wk1 x) _ _) List-subst ⟩
    prodrec 𝟙 pₗ 𝟘 (wk1 (List l (A [ σ ]))) (t [ σ ])
      (prodʷ pₗ (suc (var x1)) (V.cons′ (wk₂ (A [ σ ])) (var x1) (wk₂ (h [ σ ])) (var x0))) ≡˘⟨ cons≡ ⟩
    cons l (A [ σ ]) (h [ σ ]) (t [ σ ]) ∎

opaque

  -- The eliminator for lists as a term former
  --
  -- The grades can be interpreted as follows:
  -- r₁ represents the total uses of the list
  -- r₂ represents the total uses of the vector component of the list
  -- p₁ represents the uses of the tail in cs
  -- p₂ represents the uses of the uses of the recursive call in cs
  -- q represents the uses of the list in the motive
  -- See also Graded.Derived.List.▸listrec′

  listrec :
    ∀ {n} →
    Universe-level →
    (r₁ r₂ p₁ p₂ q : M)
    (A : Term n)
    (P : Term (1+ n))
    (nl : Term n)
    (cs : Term (3+ n))
    (xs : Term n) → Term n
  listrec l r₁ r₂ p₁ p₂ q A P nl cs xs =
    prodrec r₁ pₗ q P xs
      (V.vecrec′ l (p₁ · pₗ) p₂ r₂ (q · pₗ) q
        (wk₂ A) (P [ 4 ][ prodʷ pₗ (var x1) (var x0) ]↑) (wk₂ nl)
        (cs [ consSubst (consSubst (consSubst (wkSubst 6 idSubst)
               (var x2)) (prodʷ pₗ (var x3) (var x1))) (var x0) ])
        (var x1) (var x0))

opaque
  unfolding listrec

  -- Unfolding listrec

  listrec≡ :
    listrec l r₁ r₂ p₁ p₂ q A P nl cs xs ≡
    prodrec r₁ pₗ q P xs
      (V.vecrec′ l (p₁ · pₗ) p₂ r₂ (q · pₗ) q
        (wk₂ A) (P [ 4 ][ prodʷ pₗ (var x1) (var x0) ]↑) (wk₂ nl)
        (cs [ consSubst (consSubst (consSubst (wkSubst 6 idSubst)
               (var x2)) (prodʷ pₗ (var x3) (var x1))) (var x0) ])
        (var x1) (var x0))
  listrec≡ = refl
