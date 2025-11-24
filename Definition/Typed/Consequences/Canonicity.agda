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
open import Tools.Sum as ⊎

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

-- Only-Level-or-U Γ holds if Γ is a context that only contains
-- assumptions where the type is (syntactically) Level or U t for some
-- t.

data Only-Level-or-U : Con Term n → Set a where
  ε       : Only-Level-or-U ε
  _∙Level : Only-Level-or-U Γ → Only-Level-or-U (Γ ∙ Level)
  _∙U     : Only-Level-or-U Γ → Only-Level-or-U (Γ ∙ U t)

opaque

  -- If x ∷ A ∈ Γ and Γ satisfies Only-Level-or-U, then A is equal to
  -- either Level or U t (for some t).

  Only-Level-or-U→∈→≡Level⊎≡U :
    Only-Level-or-U Γ → x ∷ A ∈ Γ → A PE.≡ Level ⊎ ∃ λ t → A PE.≡ U t
  Only-Level-or-U→∈→≡Level⊎≡U ε          ()
  Only-Level-or-U→∈→≡Level⊎≡U (_ ∙Level) here =
    inj₁ PE.refl
  Only-Level-or-U→∈→≡Level⊎≡U (_ ∙U) here =
    inj₂ (_ , PE.refl)
  Only-Level-or-U→∈→≡Level⊎≡U (only ∙Level) (there x∈) =
    ⊎.map (PE.cong wk1) (Σ.map _ (PE.cong wk1)) $
    Only-Level-or-U→∈→≡Level⊎≡U only x∈
  Only-Level-or-U→∈→≡Level⊎≡U (only ∙U) (there x∈) =
    ⊎.map (PE.cong wk1) (Σ.map _ (PE.cong wk1)) $
    Only-Level-or-U→∈→≡Level⊎≡U only x∈

opaque

  -- If the neutral term t has type A with respect to a context Γ that
  -- only contains level or universe assumptions, then A is
  -- definitionally equal to Level or some universe, and t is a
  -- variable (assuming that equality reflection is not allowed).

  Only-Level-or-U→Neutral→≡Level⊎≡U :
    ⦃ ok : No-equality-reflection ⦄ →
    Only-Level-or-U Γ → Γ ⊢ t ∷ A → Neutral t →
    (Γ ⊢ A ≡ Level ⊎ ∃ λ u → Γ ⊢ A ≡ U u) × ∃ λ x → t PE.≡ var x
  Only-Level-or-U→Neutral→≡Level⊎≡U only ⊢x (var x) =
    let _ , x∈ , A≡ = inversion-var ⊢x in
    ⊎.map (flip (PE.subst (_⊢_≡_ _ _)) A≡)
      (Σ.map idᶠ (flip (PE.subst (_⊢_≡_ _ _)) A≡))
      (Only-Level-or-U→∈→≡Level⊎≡U only x∈) ,
    _ , PE.refl
  Only-Level-or-U→Neutral→≡Level⊎≡U only ⊢lower (lowerₙ t-ne) =
    let _ , _ , ⊢t , A≡ = inversion-lower ⊢lower
        Lift≡ , _       =
          Only-Level-or-U→Neutral→≡Level⊎≡U only ⊢t t-ne
    in
    case Lift≡ of λ where
      (inj₁ ≡Level) →
        ⊥-elim $ Lift≢Level ⦃ ok = possibly-nonempty ⦄ ≡Level
      (inj₂ (_ , ≡U)) →
        ⊥-elim $ U≢Liftⱼ ⦃ ok = possibly-nonempty ⦄ (sym ≡U)
  Only-Level-or-U→Neutral→≡Level⊎≡U only ⊢app (∘ₙ t-ne) =
    let _ , _ , _ , ⊢t , _ , A≡ = inversion-app ⊢app
        Π≡ , _                  =
          Only-Level-or-U→Neutral→≡Level⊎≡U only ⊢t t-ne
    in
    case Π≡ of λ where
      (inj₁ ≡Level) →
        ⊥-elim $ Level≢ΠΣⱼ ⦃ ok = possibly-nonempty ⦄ (sym ≡Level)
      (inj₂ (_ , ≡U)) →
        ⊥-elim $ U≢ΠΣⱼ ⦃ ok = possibly-nonempty ⦄ (sym ≡U)
  Only-Level-or-U→Neutral→≡Level⊎≡U only ⊢fst (fstₙ t-ne) =
    let _ , _ , _ , _ , _ , ⊢t , A≡ = inversion-fst ⊢fst
        Σ≡ , _                      =
          Only-Level-or-U→Neutral→≡Level⊎≡U only ⊢t t-ne
    in
    case Σ≡ of λ where
      (inj₁ ≡Level) →
        ⊥-elim $ Level≢ΠΣⱼ ⦃ ok = possibly-nonempty ⦄ (sym ≡Level)
      (inj₂ (_ , ≡U)) →
        ⊥-elim $ U≢ΠΣⱼ ⦃ ok = possibly-nonempty ⦄ (sym ≡U)
  Only-Level-or-U→Neutral→≡Level⊎≡U only ⊢snd (sndₙ t-ne) =
    let _ , _ , _ , _ , _ , ⊢t , A≡ = inversion-snd ⊢snd
        Σ≡ , _                      =
          Only-Level-or-U→Neutral→≡Level⊎≡U only ⊢t t-ne
    in
    case Σ≡ of λ where
      (inj₁ ≡Level) →
        ⊥-elim $ Level≢ΠΣⱼ ⦃ ok = possibly-nonempty ⦄ (sym ≡Level)
      (inj₂ (_ , ≡U)) →
        ⊥-elim $ U≢ΠΣⱼ ⦃ ok = possibly-nonempty ⦄ (sym ≡U)
  Only-Level-or-U→Neutral→≡Level⊎≡U only ⊢nr (natrecₙ t-ne) =
    let _ , _ , _ , ⊢t , A≡ = inversion-natrec ⊢nr
        ℕ≡ , _              =
          Only-Level-or-U→Neutral→≡Level⊎≡U only ⊢t t-ne
    in
    case ℕ≡ of λ where
      (inj₁ ≡Level) →
        ⊥-elim $ Level≢ℕ ⦃ ok = possibly-nonempty ⦄ (sym ≡Level)
      (inj₂ (_ , ≡U)) →
        ⊥-elim $ U≢ℕ ⦃ ok = possibly-nonempty ⦄ (sym ≡U)
  Only-Level-or-U→Neutral→≡Level⊎≡U only ⊢pr (prodrecₙ t-ne) =
    let _ , _ , _ , _ , _ , _ , ⊢t , _ , A≡ = inversion-prodrec ⊢pr
        Σ≡ , _                              =
          Only-Level-or-U→Neutral→≡Level⊎≡U only ⊢t t-ne
    in
    case Σ≡ of λ where
      (inj₁ ≡Level) →
        ⊥-elim $ Level≢ΠΣⱼ ⦃ ok = possibly-nonempty ⦄ (sym ≡Level)
      (inj₂ (_ , ≡U)) →
        ⊥-elim $ U≢ΠΣⱼ ⦃ ok = possibly-nonempty ⦄ (sym ≡U)
  Only-Level-or-U→Neutral→≡Level⊎≡U only ⊢er (emptyrecₙ t-ne) =
    let _ , ⊢t , A≡ = inversion-emptyrec ⊢er
        Empty≡ , _  = Only-Level-or-U→Neutral→≡Level⊎≡U only ⊢t t-ne
    in
    case Empty≡ of λ where
      (inj₁ ≡Level) →
        ⊥-elim $ Level≢Empty ⦃ ok = possibly-nonempty ⦄ (sym ≡Level)
      (inj₂ (_ , ≡U)) →
        ⊥-elim $ U≢Emptyⱼ ⦃ ok = possibly-nonempty ⦄ (sym ≡U)
  Only-Level-or-U→Neutral→≡Level⊎≡U only ⊢ur (unitrecₙ _ t-ne) =
    let _ , ⊢t , _ , A≡ = inversion-unitrec ⊢ur
        Unit≡ , _       = Only-Level-or-U→Neutral→≡Level⊎≡U only ⊢t t-ne
    in
    case Unit≡ of λ where
      (inj₁ ≡Level) →
        ⊥-elim $ Level≢Unitⱼ ⦃ ok = possibly-nonempty ⦄ (sym ≡Level)
      (inj₂ (_ , ≡U)) →
        ⊥-elim $ U≢Unitⱼ ⦃ ok = possibly-nonempty ⦄ (sym ≡U)
  Only-Level-or-U→Neutral→≡Level⊎≡U only ⊢J (Jₙ t-ne) =
    let _ , _ , _ , _ , _ , ⊢t , A≡ = inversion-J ⊢J
        Id≡ , _                     =
          Only-Level-or-U→Neutral→≡Level⊎≡U only ⊢t t-ne
    in
    case Id≡ of λ where
      (inj₁ ≡Level) →
        ⊥-elim $ Level≢Id ⦃ ok = possibly-nonempty ⦄ (sym ≡Level)
      (inj₂ (_ , ≡U)) →
        ⊥-elim $ Id≢U ⦃ ok = possibly-nonempty ⦄ ≡U
  Only-Level-or-U→Neutral→≡Level⊎≡U only ⊢K (Kₙ t-ne) =
    let _ , _ , _ , _ , ⊢t , _ , A≡ = inversion-K ⊢K
        Id≡ , _                     =
          Only-Level-or-U→Neutral→≡Level⊎≡U only ⊢t t-ne
    in
    case Id≡ of λ where
      (inj₁ ≡Level) →
        ⊥-elim $ Level≢Id ⦃ ok = possibly-nonempty ⦄ (sym ≡Level)
      (inj₂ (_ , ≡U)) →
        ⊥-elim $ Id≢U ⦃ ok = possibly-nonempty ⦄ ≡U
  Only-Level-or-U→Neutral→≡Level⊎≡U only ⊢bc ([]-congₙ t-ne) =
    let _ , _ , _ , _ , ⊢t , _ , A≡ = inversion-[]-cong ⊢bc
        Id≡ , _                     =
          Only-Level-or-U→Neutral→≡Level⊎≡U only ⊢t t-ne
    in
    case Id≡ of λ where
      (inj₁ ≡Level) →
        ⊥-elim $ Level≢Id ⦃ ok = possibly-nonempty ⦄ (sym ≡Level)
      (inj₂ (_ , ≡U)) →
        ⊥-elim $ Id≢U ⦃ ok = possibly-nonempty ⦄ ≡U

opaque

  -- Canonicity for natural numbers for contexts Γ that satisfy
  -- Only-Level-or-U Γ (under the assumption that equality reflection
  -- is not allowed).
  --
  -- This lemma is similar to a conjecture in "Type Theory with
  -- Explicit Universe Polymorphism" by Bezem, Coquand, Dybjer and
  -- Escardó (that conjecture restricts the contexts to only contain
  -- level variables).

  canonicity-Only-Level-or-U :
    ⦃ ok : No-equality-reflection ⦄ →
    Only-Level-or-U Γ → Γ ⊢ t ∷ ℕ → ∃ λ n → Γ ⊢ t ≡ sucᵏ n ∷ ℕ
  canonicity-Only-Level-or-U {Γ} only ⊢t =
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
             case Only-Level-or-U→Neutral→≡Level⊎≡U only ⊢u u-ne
                    .proj₁ of λ where
               (inj₁ ≡Level) →
                 ⊥-elim $ Level≢ℕ ⦃ ok = possibly-nonempty ⦄ $
                 sym ≡Level
               (inj₂ (_ , ≡U)) →
                 ⊥-elim $ U≢ℕ ⦃ ok = possibly-nonempty ⦄ (sym ≡U))

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
