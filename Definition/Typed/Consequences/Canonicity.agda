------------------------------------------------------------------------
-- Canonicity theorems for natural numbers and the empty type
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.Canonicity
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant

open import Definition.Typed R
open import Definition.Typed.Consequences.Inequality R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Syntactic R
open import Definition.Typed.Well-formed R
open import Definition.Typed.EqRelInstance R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Substitution.Introductions R
open import Definition.LogicalRelation.Fundamental.Reducibility R
open import Definition.LogicalRelation.Unary R

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Relation

private
  variable
    n       : Nat
    x       : Fin _
    A t u v : Term _
    Γ       : Con _ _

opaque

  -- Canonicity for natural numbers.

  canonicity : ε ⊢ t ∷ ℕ → ∃ λ n → ε ⊢ t ≡ sucᵏ n ∷ ℕ
  canonicity {t} =
    ε ⊢ t ∷ ℕ                     →⟨ ⊩∷ℕ⇔ .proj₁ ∘→ proj₂ ∘→ reducible-⊩∷ ⦃ inc = ε ⦄ ⟩
    ε ⊩ℕ t ∷ℕ                     →⟨ lemma ⟩
    (∃ λ n → ε ⊢ t ≡ sucᵏ n ∷ ℕ)  □
    where
    lemma : ε ⊩ℕ u ∷ℕ → ∃ λ n → ε ⊢ u ≡ sucᵏ n ∷ ℕ
    lemma (ℕₜ v u⇒*v _ ⊩v) =
      Σ.map idᶠ (trans (subset*Term u⇒*v))
        (case ⊩v of λ where
           (ne (neNfₜ _ u-ne _)) → ⊥-elim $ noClosedNe u-ne
           zeroᵣ                 → 0 , refl (zeroⱼ ε)
           (sucᵣ ⊩u)             → Σ.map 1+ suc-cong (lemma ⊩u))

-- Only-levels Γ holds if Γ is a context that only contains
-- assumptions where the type is (syntactically) Level.

data Only-levels : Con Term n → Set a where
  ε       : Only-levels ε
  _∙Level : Only-levels Γ → Only-levels (Γ ∙ Level)

opaque

  -- If x ∷ A ∈ Γ and Γ only contains level assumptions, then A is
  -- equal to Level.

  Only-level→∈→≡Level : Only-levels Γ → x ∷ A ∈ Γ → A PE.≡ Level
  Only-level→∈→≡Level ε             ()
  Only-level→∈→≡Level (_ ∙Level)    here       = PE.refl
  Only-level→∈→≡Level (only ∙Level) (there x∈) =
    PE.cong wk1 $ Only-level→∈→≡Level only x∈

opaque

  -- If the neutral term t has type A with respect to a context Γ that
  -- only contains level assumptions, then A is definitionally equal
  -- to Level, and t is a variable (assuming that equality reflection
  -- is not allowed).

  Only-level→Neutral→≡Level :
    ⦃ ok : No-equality-reflection ⦄ →
    Only-levels Γ → Γ ⊢ t ∷ A → Neutral t →
    Γ ⊢ A ≡ Level × ∃ λ x → t PE.≡ var x
  Only-level→Neutral→≡Level only ⊢x (var x) =
    let _ , x∈ , A≡ = inversion-var ⊢x in
    PE.subst (_⊢_≡_ _ _) (Only-level→∈→≡Level only x∈) A≡ , _ , PE.refl
  Only-level→Neutral→≡Level only ⊢lower (lowerₙ t-ne) =
    let _ , _ , ⊢t , A≡ = inversion-lower ⊢lower
        Lift≡Level , _  = Only-level→Neutral→≡Level only ⊢t t-ne
    in
    ⊥-elim $ Lift≢Level ⦃ ok = possibly-nonempty ⦄ Lift≡Level
  Only-level→Neutral→≡Level only ⊢app (∘ₙ t-ne) =
    let _ , _ , _ , ⊢t , _ , A≡ = inversion-app ⊢app
        Π≡Level , _             = Only-level→Neutral→≡Level only ⊢t t-ne
    in
    ⊥-elim $ Level≢ΠΣⱼ ⦃ ok = possibly-nonempty ⦄ (sym Π≡Level)
  Only-level→Neutral→≡Level only ⊢fst (fstₙ t-ne) =
    let _ , _ , _ , _ , _ , ⊢t , A≡ = inversion-fst ⊢fst
        Σ≡Level , _                 =
          Only-level→Neutral→≡Level only ⊢t t-ne
    in
    ⊥-elim $ Level≢ΠΣⱼ ⦃ ok = possibly-nonempty ⦄ (sym Σ≡Level)
  Only-level→Neutral→≡Level only ⊢snd (sndₙ t-ne) =
    let _ , _ , _ , _ , _ , ⊢t , A≡ = inversion-snd ⊢snd
        Σ≡Level , _                 =
          Only-level→Neutral→≡Level only ⊢t t-ne
    in
    ⊥-elim $ Level≢ΠΣⱼ ⦃ ok = possibly-nonempty ⦄ (sym Σ≡Level)
  Only-level→Neutral→≡Level only ⊢nr (natrecₙ t-ne) =
    let _ , _ , _ , ⊢t , A≡ = inversion-natrec ⊢nr
        ℕ≡Level , _         = Only-level→Neutral→≡Level only ⊢t t-ne
    in
    ⊥-elim $ Level≢ℕ ⦃ ok = possibly-nonempty ⦄ (sym ℕ≡Level)
  Only-level→Neutral→≡Level only ⊢pr (prodrecₙ t-ne) =
    let _ , _ , _ , _ , _ , _ , ⊢t , _ , A≡ = inversion-prodrec ⊢pr
        Σ≡Level , _                         =
          Only-level→Neutral→≡Level only ⊢t t-ne
    in
    ⊥-elim $ Level≢ΠΣⱼ ⦃ ok = possibly-nonempty ⦄ (sym Σ≡Level)
  Only-level→Neutral→≡Level only ⊢er (emptyrecₙ t-ne) =
    let _ , ⊢t , A≡     = inversion-emptyrec ⊢er
        Empty≡Level , _ = Only-level→Neutral→≡Level only ⊢t t-ne
    in
    ⊥-elim $ Level≢Empty ⦃ ok = possibly-nonempty ⦄ (sym Empty≡Level)
  Only-level→Neutral→≡Level only ⊢ur (unitrecₙ _ t-ne) =
    let _ , ⊢t , _ , A≡ = inversion-unitrec ⊢ur
        Unit≡Level , _  = Only-level→Neutral→≡Level only ⊢t t-ne
    in
    ⊥-elim $ Level≢Unitⱼ ⦃ ok = possibly-nonempty ⦄ (sym Unit≡Level)
  Only-level→Neutral→≡Level only ⊢J (Jₙ t-ne) =
    let _ , _ , _ , _ , _ , ⊢t , A≡ = inversion-J ⊢J
        Id≡Level , _                =
          Only-level→Neutral→≡Level only ⊢t t-ne
    in
    ⊥-elim $ Level≢Id ⦃ ok = possibly-nonempty ⦄ (sym Id≡Level)
  Only-level→Neutral→≡Level only ⊢K (Kₙ t-ne) =
    let _ , _ , _ , _ , ⊢t , _ , A≡ = inversion-K ⊢K
        Id≡Level , _                =
          Only-level→Neutral→≡Level only ⊢t t-ne
    in
    ⊥-elim $ Level≢Id ⦃ ok = possibly-nonempty ⦄ (sym Id≡Level)
  Only-level→Neutral→≡Level only ⊢bc ([]-congₙ t-ne) =
    let _ , _ , _ , ⊢t , _ , A≡ = inversion-[]-cong ⊢bc
        Id≡Level , _            = Only-level→Neutral→≡Level only ⊢t t-ne
    in
    ⊥-elim $ Level≢Id ⦃ ok = possibly-nonempty ⦄ (sym Id≡Level)

opaque

  -- Canonicity for natural numbers for contexts Γ that satisfy
  -- Only-levels Γ (under the assumption that equality reflection is
  -- not allowed).
  --
  -- This lemma is similar to a conjecture in "Type Theory with
  -- Explicit Universe Polymorphism" by Bezem, Coquand, Dybjer and
  -- Escardó.

  canonicity-with-level-assumptions :
    ⦃ ok : No-equality-reflection ⦄ →
    Only-levels Γ → Γ ⊢ t ∷ ℕ → ∃ λ n → Γ ⊢ t ≡ sucᵏ n ∷ ℕ
  canonicity-with-level-assumptions {Γ} only ⊢t =
    lemma $ ⊩∷ℕ⇔ .proj₁ $
    reducible-⊩∷ ⦃ inc = possibly-nonempty ⦄ ⊢t .proj₂
    where
    lemma : Γ ⊩ℕ u ∷ℕ → ∃ λ n → Γ ⊢ u ≡ sucᵏ n ∷ ℕ
    lemma (ℕₜ v u⇒*v _ ⊩v) =
      Σ.map idᶠ (trans (subset*Term u⇒*v))
        (case ⊩v of λ where
           zeroᵣ                   → 0 , refl (zeroⱼ (wfTerm ⊢t))
           (sucᵣ ⊩u)               → Σ.map 1+ suc-cong (lemma ⊩u)
           (ne (neNfₜ _ u-ne u≡u)) →
             let _ , ⊢u , _ = wf-⊢≡∷ u≡u in
             ⊥-elim $ Level≢ℕ ⦃ ok = possibly-nonempty ⦄ $ _⊢_≡_.sym $
             Only-level→Neutral→≡Level only ⊢u u-ne .proj₁)

opaque

  -- Canonicity for the empty type.

  ¬Empty : ¬ ε ⊢ t ∷ Empty
  ¬Empty {t} =
    ε ⊢ t ∷ Empty      →⟨ ⊩∷Empty⇔ .proj₁ ∘→ proj₂ ∘→ reducible-⊩∷ ⦃ inc = ε ⦄ ⟩
    ε ⊩Empty t ∷Empty  →⟨ (λ { (Emptyₜ _ _ _ (ne (neNfₜ _ u-ne _))) →
                               noClosedNe u-ne }) ⟩
    ⊥                  □

opaque

  -- Every closed equality proof reduces to rfl.

  ε⊢⇒*rfl∷Id : ε ⊢ v ∷ Id A t u → ε ⊢ v ⇒* rfl ∷ Id A t u
  ε⊢⇒*rfl∷Id ⊢v =
    case ⊩∷Id⇔ .proj₁ $ reducible-⊩∷ ⦃ inc = ε ⦄ ⊢v .proj₂ of λ
      (_ , v⇒*w , _ , _ , rest) →
    case rest of λ where
      (rflᵣ _)      → v⇒*w
      (ne _ w-ne _) → ⊥-elim $ noClosedNe w-ne

opaque

  -- If Id A t u is inhabited in the empty context, then t is
  -- definitionally equal to u at type A.

  ε⊢∷Id→ε⊢≡∷ : ε ⊢ v ∷ Id A t u → ε ⊢ t ≡ u ∷ A
  ε⊢∷Id→ε⊢≡∷ {v} {A} {t} {u} =
    ε ⊢ v ∷ Id A t u         →⟨ ε⊢⇒*rfl∷Id ⟩
    ε ⊢ v ⇒* rfl ∷ Id A t u  →⟨ proj₂ ∘→ proj₂ ∘→ syntacticEqTerm ∘→ subset*Term ⟩
    ε ⊢ rfl ∷ Id A t u       →⟨ inversion-rfl-Id ⦃ ok = ε ⦄ ⟩
    ε ⊢ t ≡ u ∷ A            □
