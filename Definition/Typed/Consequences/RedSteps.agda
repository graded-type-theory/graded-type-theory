------------------------------------------------------------------------
-- Substitution theorems for reduction closures.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.RedSteps
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Typed R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.Properties R
open import Definition.Typed.RedSteps R
open import Definition.Typed.Consequences.DerivedRules R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Substitution R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.LogicalRelation.Fundamental R
open import Definition.LogicalRelation.Fundamental.Reducibility R
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Properties R
import Definition.LogicalRelation.Substitution.Introductions R as I

open import Tools.Function
open import Tools.Nat
open import Tools.Fin
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation

private
  variable
    n : Nat
    Γ : Con Term n
    A B C t t′ t₁ t₂ u v v₁ v₂ w₁ w₂ : Term n
    p q q′ r : M

opaque

  -- A variant of snd-subst for _⊢_⇒*_∷_.

  snd-subst* :
    Γ ⊢ t ⇒* u ∷ Σˢ p , q ▷ A ▹ B →
    Γ ⊢ snd p t ⇒* snd p u ∷ B [ fst p t ]₀
  snd-subst* t⇒*u =
    case inversion-ΠΣ $ syntacticTerm $ redFirst*Term t⇒*u of λ
      (_ , ⊢B , _) →
    case t⇒*u of λ where
      (id ⊢t)      → id (sndⱼ′ ⊢t)
      (t⇒v ⇨ v⇨*u) →
        snd-subst′ t⇒v ⇨
        conv* (snd-subst* v⇨*u)
          (substTypeEq (refl ⊢B) (sym (fst-cong′ (subsetTerm t⇒v))))

opaque
  unfolding _⊩ᵛ⟨_⟩_ _⊩⟨_⟩_∷_

  -- A variant of natrec-subst for _⊢_⇒*_∷_.

  natrec-subst* :
    Γ ∙ ℕ ⊢ A →
    Γ ⊢ t ∷ A [ zero ]₀ →
    Γ ∙ ℕ ∙ A ⊢ u ∷ A [ suc (var x1) ]↑² →
    Γ ⊢ v₁ ⇒* v₂ ∷ ℕ →
    Γ ⊢ natrec p q r A t u v₁ ⇒* natrec p q r A t u v₂ ∷ A [ v₁ ]₀
  natrec-subst* ⊢A ⊢t ⊢u v₁⇒*v₂ =
    I.natrec-subst* (fundamental ⊢A) ⊢t ⊢u v₁⇒*v₂
      (reducibleTerm (syntacticRedTerm v₁⇒*v₂ .proj₂ .proj₂))

opaque

  -- A variant of prodrec-subst for _⊢_⇒*_∷_.

  prodrec-subst* :
    Γ ∙ Σʷ p , q ▷ A ▹ B ⊢ C →
    Γ ⊢ t₁ ⇒* t₂ ∷ Σʷ p , q ▷ A ▹ B →
    Γ ∙ A ∙ B ⊢ u ∷ C [ prodʷ p (var x1) (var x0) ]↑² →
    Γ ⊢ prodrec r p q′ C t₁ u ⇒* prodrec r p q′ C t₂ u ∷ C [ t₁ ]₀
  prodrec-subst* ⊢C t₁⇒*t₂ ⊢u =
    case t₁⇒*t₂ of λ where
      (id ⊢t₁)         → id (prodrecⱼ′ ⊢C ⊢t₁ ⊢u)
      (t₁⇒t₃ ⇨ t₃⇒*t₂) →
        prodrec-subst′ ⊢C ⊢u t₁⇒t₃ ⇨
        conv* (prodrec-subst* ⊢C t₃⇒*t₂ ⊢u)
          (substTypeEq (refl ⊢C) (sym (subsetTerm t₁⇒t₃)))

-- Unitrec substitution of reduction closures

unitrec-subst* :
  Γ ⊢ t ⇒* t′ ∷ Unitʷ →
  Γ ∙ Unitʷ ⊢ A →
  Γ ⊢ u ∷ A [ starʷ ]₀ →
  ¬ Unitʷ-η →
  Γ ⊢ unitrec p q A t u ⇒* unitrec p q A t′ u ∷ A [ t ]₀
unitrec-subst* (id x) ⊢A ⊢u _ =
  id (unitrecⱼ ⊢A x ⊢u (⊢∷Unit→Unit-allowed x))
unitrec-subst* (x ⇨ d) ⊢A ⊢u not-ok =
  unitrec-subst ⊢A ⊢u x ok not-ok ⇨
  conv* (unitrec-subst* d ⊢A ⊢u not-ok)
        (substTypeEq (refl ⊢A) (sym (subsetTerm x)))
  where
  ok = ⊢∷Unit→Unit-allowed (redFirstTerm x)

opaque
  unfolding _⊩ᵛ⟨_⟩_ _⊩⟨_⟩_∷_

  -- A variant of K-subst for _⊢_⇒*_∷_.

  K-subst* :
    Γ ∙ Id A t t ⊢ B →
    Γ ⊢ u ∷ B [ rfl ]₀ →
    Γ ⊢ v₁ ⇒* v₂ ∷ Id A t t →
    K-allowed →
    Γ ⊢ K p A t B u v₁ ⇒* K p A t B u v₂ ∷ B [ v₁ ]₀
  K-subst* ⊢B ⊢u v₁⇒*v₂ ok =
    I.K-subst* (fundamental ⊢B) ⊢u v₁⇒*v₂
      (reducibleTerm (syntacticRedTerm v₁⇒*v₂ .proj₂ .proj₂)) ok

opaque
  unfolding _⊩ᵛ⟨_⟩_ _⊩⟨_⟩_∷_

  -- A variant of J-subst for _⊢_⇒*_∷_.

  J-subst* :
    Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
    Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
    Γ ⊢ w₁ ⇒* w₂ ∷ Id A t v →
    Γ ⊢ J p q A t B u v w₁ ⇒* J p q A t B u v w₂ ∷ B [ v , w₁ ]₁₀
  J-subst* ⊢B ⊢u w₁⇒*w₂ =
    case syntacticRedTerm w₁⇒*w₂ of λ
      (⊢Id , _ , ⊢w₂) →
    I.J-subst* (fundamental ⊢B) ⊢u
      (reducibleTerm (inversion-Id ⊢Id .proj₂ .proj₂)) w₁⇒*w₂
      (reducibleTerm ⊢w₂)
