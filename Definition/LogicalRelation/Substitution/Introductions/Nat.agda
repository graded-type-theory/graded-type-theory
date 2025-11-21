------------------------------------------------------------------------
-- Validity for natural numbers
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Nat
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  ⦃ eqrel : EqRelSet R ⦄
  where

open EqRelSet eqrel
open Type-restrictions R

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R
import Definition.LogicalRelation.Hidden.Restricted R as R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Introductions.Level R
open import
  Definition.LogicalRelation.Substitution.Introductions.Universe R
open import Definition.LogicalRelation.Unary R

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Reduction R
import Definition.Typed.Stability R as S
open import Definition.Typed.Substitution R
open import Definition.Typed.Weakening.Definition R
open import Definition.Typed.Well-formed R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Neutral.Atomic M type-variant
open import Definition.Untyped.Properties M
open import Definition.Untyped.Whnf M type-variant

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PropositionalEquality

private variable
  ∇                                 : DCon (Term 0) _
  Δ Η                               : Con Term _
  Γ                                 : Cons _ _
  A A₁ A₂ B t t₁ t₂ u u₁ u₂ v v₁ v₂ : Term _
  σ₁ σ₂                             : Subst _ _
  l l′ l″ l‴                        : Universe-level
  p q r                             : M

------------------------------------------------------------------------
-- Characterisation lemmas

opaque

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩ℕ⇔ : Γ ⊩⟨ l ⟩ ℕ ⇔ ⊢ Γ
  ⊩ℕ⇔ =
      (λ ⊩ℕ →
        case ℕ-view ⊩ℕ of λ {
          (ℕᵣ ℕ⇒*ℕ) →
        wfEq (subset* ℕ⇒*ℕ) })
    , (λ ⊢Γ → ℕᵣ (id (⊢ℕ ⊢Γ)))

opaque

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩ℕ∷U⇔ : Γ ⊩⟨ ωᵘ ⟩ ℕ ∷ U zeroᵘ ⇔ ⊢ Γ
  ⊩ℕ∷U⇔ =
      (λ ⊩ℕ →
         case ⊩∷U⇔ .proj₁ ⊩ℕ of λ
           (_ , _ , _ , _ , ℕ⇒* , _) →
         wfEqTerm (subset*Term ℕ⇒*))
    , (λ ⊢Γ →
         ⊩∷U⇔ .proj₂
           ( ⊩zeroᵘ ⊢Γ , <ᵘ-ωᵘ , ⊩ℕ⇔ .proj₂ ⊢Γ
           , (_ , id (ℕⱼ ⊢Γ) , ℕₙ , ≅ₜ-ℕrefl ⊢Γ)
           ))

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩ℕ≡⇔ : Γ ⊩⟨ l ⟩ ℕ ≡ A ⇔ Γ ⊩ℕ ℕ ≡ A
  ⊩ℕ≡⇔ =
      (λ (⊩ℕ , _ , ℕ≡A) →
         case ℕ-view ⊩ℕ of λ {
           (ℕᵣ _) →
         ℕ≡A })
    , (λ ℕ≡A →
         case id (⊢ℕ (wfEq (subset* ℕ≡A))) of λ
           ℕ⇒*ℕ →
         let ⊩ℕ = ℕᵣ ℕ⇒*ℕ in
           ⊩ℕ
         , (redSubst* ℕ≡A ⊩ℕ) .proj₁
         , ℕ≡A)

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩ℕ≡ℕ∷U⇔ : Γ ⊩⟨ ωᵘ ⟩ ℕ ≡ ℕ ∷ U zeroᵘ ⇔ ⊢ Γ
  ⊩ℕ≡ℕ∷U⇔ =
      (λ ℕ≡ℕ →
         case ⊩≡∷U⇔ .proj₁ ℕ≡ℕ of λ
           (_ , _ , _ , _ , _ , ℕ⇒* , _) →
         wfEqTerm (subset*Term ℕ⇒*))
    , (λ ⊢Γ →
         case id (ℕⱼ ⊢Γ) of λ
           ℕ⇒*ℕ →
         ⊩≡∷U⇔ .proj₂
           ( ⊩zeroᵘ ⊢Γ , <ᵘ-ωᵘ , ⊩ℕ≡⇔ .proj₂ (id (⊢ℕ ⊢Γ))
           , (_ , _ , ℕ⇒*ℕ , ℕ⇒*ℕ , ℕₙ , ℕₙ , ≅ₜ-ℕrefl ⊢Γ)
           ))

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷ℕ⇔ : Γ ⊩⟨ l ⟩ t ≡ u ∷ ℕ ⇔ Γ ⊩ℕ t ≡ u ∷ℕ
  ⊩≡∷ℕ⇔ =
      (λ (⊩ℕ , t≡u) →
         case ℕ-view ⊩ℕ of λ {
           (ℕᵣ _) →
         t≡u })
    , (λ t≡u →
         ℕᵣ (id (⊢ℕ (wfEqTerm (subset*Term (_⊩ℕ_≡_∷ℕ.d t≡u))))) , t≡u)

opaque

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷ℕ⇔ : Γ ⊩⟨ l ⟩ t ∷ ℕ ⇔ Γ ⊩ℕ t ∷ℕ
  ⊩∷ℕ⇔ {Γ} {l} {t} =
    Γ ⊩⟨ l ⟩ t ∷ ℕ      ⇔⟨ ⊩∷⇔⊩≡∷ ⟩
    Γ ⊩⟨ l ⟩ t ≡ t ∷ ℕ  ⇔⟨ ⊩≡∷ℕ⇔ ⟩
    Γ ⊩ℕ t ≡ t ∷ℕ       ⇔˘⟨ ⊩ℕ∷ℕ⇔⊩ℕ≡∷ℕ ⟩
    Γ ⊩ℕ t ∷ℕ           □⇔

opaque

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩zero∷ℕ⇔ : Γ ⊩⟨ l ⟩ zero ∷ ℕ ⇔ ⊢ Γ
  ⊩zero∷ℕ⇔ =
      wfTerm ∘→ escape-⊩∷
    , (λ ⊢Γ →
         ⊩∷ℕ⇔ .proj₂ $
         ℕₜ _ (id (zeroⱼ ⊢Γ)) (≅ₜ-zerorefl ⊢Γ) zeroᵣ)

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩zero≡zero∷ℕ⇔ : Γ ⊩⟨ l ⟩ zero ≡ zero ∷ ℕ ⇔ ⊢ Γ
  ⊩zero≡zero∷ℕ⇔ {Γ} {l} =
    Γ ⊩⟨ l ⟩ zero ≡ zero ∷ ℕ  ⇔˘⟨ ⊩∷⇔⊩≡∷ ⟩
    Γ ⊩⟨ l ⟩ zero ∷ ℕ         ⇔⟨ ⊩zero∷ℕ⇔ ⟩
    ⊢ Γ                       □⇔

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩suc≡suc∷ℕ⇔ :
    Γ ⊩⟨ l ⟩ suc t ≡ suc u ∷ ℕ ⇔
    Γ ⊩⟨ l ⟩ t ≡ u ∷ ℕ
  ⊩suc≡suc∷ℕ⇔ {Γ} {l} {t} {u} =
    Γ ⊩⟨ l ⟩ suc t ≡ suc u ∷ ℕ  ⇔⟨ ⊩≡∷ℕ⇔ ⟩
    Γ ⊩ℕ suc t ≡ suc u ∷ℕ       ⇔⟨ lemma₁ , lemma₂ ⟩
    Γ ⊩ℕ t ≡ u ∷ℕ               ⇔˘⟨ ⊩≡∷ℕ⇔ ⟩
    Γ ⊩⟨ l ⟩ t ≡ u ∷ ℕ          □⇔
    where
    lemma₀ : [Natural]-prop Γ (suc t) (suc u) → Γ ⊩ℕ t ≡ u ∷ℕ
    lemma₀ (sucᵣ t≡u)                  = t≡u
    lemma₀ (ne (neNfₜ₌ (ne () _) _ _))

    lemma₁ : Γ ⊩ℕ suc t ≡ suc u ∷ℕ → Γ ⊩ℕ t ≡ u ∷ℕ
    lemma₁ (ℕₜ₌ _ _ suc-t⇒*t′ suc-u⇒*u′ _ t′≡u′) =
      case whnfRed*Term suc-t⇒*t′ sucₙ of λ {
        PE.refl →
      case whnfRed*Term suc-u⇒*u′ sucₙ of λ {
        PE.refl →
      lemma₀ t′≡u′}}

    lemma₂ : Γ ⊩ℕ t ≡ u ∷ℕ → Γ ⊩ℕ suc t ≡ suc u ∷ℕ
    lemma₂
      t≡u@(ℕₜ₌ _ _ t⇒*t′ u⇒*u′ t′≅u′ t′≡u′) =
      let t′-ok , u′-ok = split t′≡u′ in
      ℕₜ₌ _ _ (id (sucⱼ (redFirst*Term t⇒*t′)))
        (id (sucⱼ (redFirst*Term u⇒*u′)))
        (≅-suc-cong $
         ≅ₜ-red (id (⊢ℕ (wfEqTerm (≅ₜ-eq t′≅u′))) , ℕₙ)
           (t⇒*t′ , naturalWhnf t′-ok) (u⇒*u′ , naturalWhnf u′-ok)
           t′≅u′)
        (sucᵣ t≡u)

opaque

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩suc∷ℕ⇔ :
    Γ ⊩⟨ l ⟩ suc t ∷ ℕ ⇔
    Γ ⊩⟨ l ⟩ t ∷ ℕ
  ⊩suc∷ℕ⇔ {Γ} {l} {t} =
    Γ ⊩⟨ l ⟩ suc t ∷ ℕ          ⇔⟨ ⊩∷⇔⊩≡∷ ⟩
    Γ ⊩⟨ l ⟩ suc t ≡ suc t ∷ ℕ  ⇔⟨ ⊩suc≡suc∷ℕ⇔ ⟩
    Γ ⊩⟨ l ⟩ t ≡ t ∷ ℕ          ⇔˘⟨ ⊩∷⇔⊩≡∷ ⟩
    Γ ⊩⟨ l ⟩ t ∷ ℕ              □⇔

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩zero≡suc∷ℕ⇔ : Γ ⊩⟨ l ⟩ zero ≡ suc t ∷ ℕ ⇔ ⊥
  ⊩zero≡suc∷ℕ⇔ =
      (λ zero≡suc →
         case ⊩≡∷ℕ⇔ .proj₁ zero≡suc of λ {
           (ℕₜ₌ _ _ zero⇒* suc⇒* _ rest) →
         case whnfRed*Term zero⇒* zeroₙ of λ {
           PE.refl →
         case whnfRed*Term suc⇒* sucₙ of λ {
           PE.refl →
         case rest of λ where
           (ne (neNfₜ₌ (ne () _) _ _)) }}})
    , ⊥-elim

------------------------------------------------------------------------
-- ℕ

opaque

  -- Validity of ℕ, seen as a type former.

  ℕᵛ : ⊩ᵛ Γ → Γ ⊩ᵛ⟨ l ⟩ ℕ
  ℕᵛ {Γ} {l} ⊩Γ =
    ⊩ᵛ⇔ʰ .proj₂
      ( ⊩Γ
      , λ {_} {∇′} ξ⊇ {_} {Δ} {σ₁} {σ₂} →
          ∇′ » Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ .vars  →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩
          ∇′ »⊢ Δ                      →⟨ ⊢ℕ ⟩
          (∇′ » Δ ⊢ ℕ)                 →⟨ id ⟩
          ∇′ » Δ ⊢ ℕ ⇒* ℕ              ⇔˘⟨ ⊩ℕ≡⇔ ⟩→
          ∇′ » Δ ⊩⟨ l ⟩ ℕ ≡ ℕ          □
      )

opaque

  -- Validity of ℕ, seen as a term former.

  ℕᵗᵛ : ⊩ᵛ Γ → Γ ⊩ᵛ⟨ ωᵘ ⟩ ℕ ∷ U zeroᵘ
  ℕᵗᵛ {Γ} ⊩Γ =
    ⊩ᵛ∷⇔ʰ .proj₂
      ( ⊩ᵛU (zeroᵘᵛ′ ⊩Γ)
      , λ {_} {∇′} ξ⊇ {_} {Δ} {σ₁} {σ₂} →
          ∇′ » Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ .vars     →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩
          ∇′ »⊢ Δ                         ⇔˘⟨ ⊩ℕ≡ℕ∷U⇔ ⟩→
          ∇′ » Δ ⊩⟨ ωᵘ ⟩ ℕ ≡ ℕ ∷ U zeroᵘ  □
      )

------------------------------------------------------------------------
-- The constructors zero and suc

opaque

  -- Reducibility of zero.

  ⊩zero :
    ⊢ Γ →
    Γ ⊩⟨ l ⟩ zero ∷ ℕ
  ⊩zero = ⊩zero∷ℕ⇔ .proj₂

opaque

  -- Validity of zero.

  zeroᵛ :
    ⊩ᵛ Γ →
    Γ ⊩ᵛ⟨ l ⟩ zero ∷ ℕ
  zeroᵛ {Γ} {l} ⊩Γ =
    ⊩ᵛ∷⇔ʰ .proj₂
      ( ℕᵛ ⊩Γ
      , λ {_} {∇′} ξ⊇ {_} {Δ} {σ₁} {σ₂} →
          ∇′ » Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ .vars    →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩
          ∇′ »⊢ Δ                        ⇔˘⟨ ⊩zero≡zero∷ℕ⇔ ⟩→
          ∇′ » Δ ⊩⟨ l ⟩ zero ≡ zero ∷ ℕ  □
      )

opaque

  -- Reducibility of suc.

  ⊩suc :
    Γ ⊩⟨ l ⟩ t ∷ ℕ →
    Γ ⊩⟨ l ⟩ suc t ∷ ℕ
  ⊩suc = ⊩suc∷ℕ⇔ .proj₂

opaque

  -- Reducibility of equality between applications of suc.

  ⊩suc≡suc :
    Γ ⊩⟨ l ⟩ t ≡ u ∷ ℕ →
    Γ ⊩⟨ l ⟩ suc t ≡ suc u ∷ ℕ
  ⊩suc≡suc = ⊩suc≡suc∷ℕ⇔ .proj₂

opaque

  -- Validity of equality preservation for suc.

  suc-congᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ ℕ →
    Γ ⊩ᵛ⟨ l ⟩ suc t ≡ suc u ∷ ℕ
  suc-congᵛ t≡u =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( ℕᵛ (wf-⊩ᵛ $ wf-⊩ᵛ∷ $ wf-⊩ᵛ≡∷ t≡u .proj₁)
      , λ ξ⊇ → ⊩suc≡suc ∘→ R.⊩≡∷→ ∘→ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (defn-wk-⊩ᵛ≡∷ ξ⊇ t≡u)
      )

opaque

  -- Validity of suc.

  sucᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ ℕ →
    Γ ⊩ᵛ⟨ l ⟩ suc t ∷ ℕ
  sucᵛ ⊩t =
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ $
    suc-congᵛ (refl-⊩ᵛ≡∷ ⊩t)

------------------------------------------------------------------------
-- The eliminator natrec

private opaque

  -- A lemma used to prove ⊩natrec≡natrec.

  ⊩natrec≡natrec′ :
    Γ »∙ ℕ ⊢ A₁ ≅ A₂ →
    (∀ {v₁ v₂} →
     Γ ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ ℕ →
     Γ ⊩⟨ l ⟩ A₁ [ v₁ ]₀ ≡ A₁ [ v₂ ]₀) →
    (∀ {v₁ v₂} →
     Γ ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ ℕ →
     Γ ⊩⟨ l ⟩ A₂ [ v₁ ]₀ ≡ A₂ [ v₂ ]₀) →
    (∀ {v₁ v₂} →
     Γ ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ ℕ →
     Γ ⊩⟨ l ⟩ A₁ [ v₁ ]₀ ≡ A₂ [ v₂ ]₀) →
    Γ ⊢ t₁ ∷ A₁ [ zero ]₀ →
    Γ ⊢ t₂ ∷ A₂ [ zero ]₀ →
    Γ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ A₁ [ zero ]₀ →
    Γ »∙ ℕ »∙ A₁ ⊢ u₁ ≅ u₂ ∷ A₁ [ suc (var x1) ]↑² →
    (∀ {v₁ v₂ w₁ w₂} →
     Γ ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ ℕ →
     Γ ⊩⟨ l ⟩ w₁ ≡ w₂ ∷ A₁ [ v₁ ]₀ →
     Γ ⊩⟨ l ⟩ u₁ [ v₁ , w₁ ]₁₀ ≡ u₂ [ v₂ , w₂ ]₁₀ ∷ A₁ [ suc v₁ ]₀) →
    Γ ⊩ℕ v₁ ≡ v₂ ∷ℕ →
    Γ ⊩⟨ l ⟩ natrec p q r A₁ t₁ u₁ v₁ ≡
      natrec p q r A₂ t₂ u₂ v₂ ∷ A₁ [ v₁ ]₀
  ⊩natrec≡natrec′
    {A₁} {A₂} {l} {t₁} {t₂} {u₁} {u₂} {v₁} {v₂} {p} {q} {r}
    A₁≅A₂ A₁≡A₁ A₂≡A₂ A₁≡A₂ ⊢t₁ ⊢t₂ t₁≡t₂ u₁≅u₂ u₁≡u₂
    ⊩ℕ-v₁≡v₂@(ℕₜ₌ v₁′ v₂′ v₁⇒*v₁′ v₂⇒*v₂′ v₁′≅v₂′ v₁′∼v₂′) =
    let ⊢A₁≡A₂        = ≅-eq A₁≅A₂
        _ , ⊢u₁ , ⊢u₂ = wf-⊢≡∷ (≅ₜ-eq u₁≅u₂)
        ⊢u₂           =
          S.stabilityTerm (S.refl-∙ ⊢A₁≡A₂)
            (conv ⊢u₂ $
             subst-⊢≡ ⊢A₁≡A₂ $ refl-⊢ˢʷ≡∷ $
             ⊢ˢʷ∷-[][]↑ (sucⱼ (var₁ (wf-⊢≡ ⊢A₁≡A₂ .proj₁))))
    in

    -- Some definitions related to v₁ and v₂.
    case ⊩≡∷ℕ⇔ {l = l} .proj₂ ⊩ℕ-v₁≡v₂ of λ
      v₁≡v₂ →
    case wf-⊩≡∷ v₁≡v₂ of λ
      (⊩v₁ , ⊩v₂) →

    -- Some definitions related to v₁′ and v₂′.
    case ⊩∷-⇒* v₁⇒*v₁′ ⊩v₁ of λ
      v₁≡v₁′ →
    case ⊩∷-⇒* v₂⇒*v₂′ ⊩v₂ of λ
      v₂≡v₂′ →
    case
      v₁′  ≡˘⟨ v₁≡v₁′ ⟩⊩∷
      v₁   ≡⟨ v₁≡v₂ ⟩⊩∷
      v₂   ≡⟨ v₂≡v₂′ ⟩⊩∷∎
      v₂′  ∎
    of λ
      v₁′≡v₂′ →
    case A₁≡A₂ v₁′≡v₂′ of λ
      A₁[v₁′]≡A₂[v₂′] →
    case ≅-eq $ escape-⊩≡ A₁[v₁′]≡A₂[v₂′] of λ
      ⊢A₁[v₁′]≡A₂[v₂′] →

    -- The two applications of natrec are equal if applications of
    -- natrec to v₁′ and v₂′ are equal.
    case
      (λ (hyp : _ ⊩⟨ l ⟩ _ ≡ _ ∷ _) →
         natrec p q r A₁ t₁ u₁ v₁ ∷ A₁ [ v₁ ]₀    ⇒*⟨ natrec-subst* ⊢t₁ ⊢u₁ v₁⇒*v₁′ ⟩⊩∷∷
                                                    ⟨ A₁≡A₁ v₁≡v₁′ ⟩⊩∷
         natrec p q r A₁ t₁ u₁ v₁′ ∷ A₁ [ v₁′ ]₀  ≡⟨ hyp ⟩⊩∷∷⇐*
                                                   ⟨ ⊢A₁[v₁′]≡A₂[v₂′] ⟩⇒
                                   ∷ A₂ [ v₂′ ]₀  ˘⟨ ≅-eq $ escape-⊩≡ $ A₂≡A₂ v₂≡v₂′ ⟩⇐
         natrec p q r A₂ t₂ u₂ v₂′ ∷ A₂ [ v₂ ]₀   ⇐*⟨ natrec-subst* ⊢t₂ ⊢u₂ v₂⇒*v₂′ ⟩∎∷
         natrec p q r A₂ t₂ u₂ v₂                 ∎)
    of λ
      lemma →

    lemma
      (case v₁′∼v₂′ of λ where
         -- If v₁′ and v₂′ are equal neutral terms, then one can
         -- conclude by using the fact that the applications of natrec
         -- to v₁′ and v₂′ are equal neutral terms.
         (ne (neNfₜ₌ v₁′-ne v₂′-ne v₁′~v₂′)) →
           neutral-⊩≡∷ (wf-⊩≡ A₁[v₁′]≡A₂[v₂′] .proj₁)
             (natrecₙᵃ v₁′-ne) (natrecₙᵃ v₂′-ne) $
           ~-natrec A₁≅A₂ (escape-⊩≡∷ t₁≡t₂) u₁≅u₂ v₁′~v₂′

         -- If v₁′ and v₂′ are both zero, then one can conclude by
         -- using the rule natrec-zero and the fact that t₁ is equal
         -- to t₂.
         zeroᵣ →
           natrec p q r A₁ t₁ u₁ zero  ⇒⟨ natrec-zero ⊢t₁ ⊢u₁ ⟩⊩∷
           t₁ ∷ A₁ [ zero ]₀           ≡⟨ t₁≡t₂ ⟩⊩∷∷⇐*
                                        ⟨ ⊢A₁[v₁′]≡A₂[v₂′] ⟩⇒
           t₂ ∷ A₂ [ zero ]₀           ⇐⟨ natrec-zero ⊢t₂ ⊢u₂ ⟩∎∷
           natrec p q r A₂ t₂ u₂ zero  ∎

         -- If v₁′ and v₂′ are applications of suc to equal terms,
         -- then one can conclude by using the rule natrec-suc and an
         -- inductive hypothesis.
         (sucᵣ {n = v₁″} {n′ = v₂″} ⊩ℕ-v₁″≡v₂″) →
           case ⊩≡∷ℕ⇔ .proj₂ ⊩ℕ-v₁″≡v₂″ of λ
             v₁″≡v₂″ →
           case wf-⊩≡∷ v₁″≡v₂″ of λ
             (⊩v₁″ , ⊩v₂″) →

           natrec p q r A₁ t₁ u₁ (suc v₁″)                             ⇒⟨ natrec-suc ⊢t₁ ⊢u₁ (escape-⊩∷ ⊩v₁″) ⟩⊩∷
           u₁ [ v₁″ , natrec p q r A₁ t₁ u₁ v₁″ ]₁₀ ∷ A₁ [ suc v₁″ ]₀  ≡⟨ u₁≡u₂ v₁″≡v₂″ $
                                                                          ⊩natrec≡natrec′ A₁≅A₂ A₁≡A₁ A₂≡A₂ A₁≡A₂ ⊢t₁ ⊢t₂ t₁≡t₂
                                                                            u₁≅u₂ u₁≡u₂ ⊩ℕ-v₁″≡v₂″ ⟩⊩∷∷⇐*
                                                                        ⟨ ⊢A₁[v₁′]≡A₂[v₂′] ⟩⇒
           u₂ [ v₂″ , natrec p q r A₂ t₂ u₂ v₂″ ]₁₀ ∷ A₂ [ suc v₂″ ]₀  ⇐⟨ natrec-suc ⊢t₂ ⊢u₂ (escape-⊩∷ ⊩v₂″)
                                                                        ⟩∎∷
           natrec p q r A₂ t₂ u₂ (suc v₂″)                             ∎)

opaque

  -- Reducibility of equality between applications of natrec.

  ⊩natrec≡natrec :
    ∇ » Δ ∙ ℕ ⊢ A₁ ≡ A₂ →
    ∇ » Δ ∙ ℕ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ →
    ∇ » Δ ⊩ᵛ⟨ l′ ⟩ t₁ ≡ t₂ ∷ A₁ [ zero ]₀ →
    ∇ » Δ ∙ ℕ ∙ A₁ ⊢ u₁ ≡ u₂ ∷ A₁ [ suc (var x1) ]↑² →
    ∇ » Δ ∙ ℕ ∙ A₁ ⊩ᵛ⟨ l″ ⟩ u₁ ≡ u₂ ∷ A₁ [ suc (var x1) ]↑² →
    ∇ » Δ ⊩ᵛ⟨ l‴ ⟩ v₁ ≡ v₂ ∷ ℕ →
    ⦃ inc : Var-included or-empty Η ⦄ →
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
    ∇ » Η ⊩⟨ l ⟩ natrec p q r A₁ t₁ u₁ v₁ [ σ₁ ] ≡
      natrec p q r A₂ t₂ u₂ v₂ [ σ₂ ] ∷ A₁ [ v₁ ]₀ [ σ₁ ]
  ⊩natrec≡natrec
    {A₁} {A₂} {l} {σ₁} ⊢A₁≡A₂ A₁≡A₂ t₁≡t₂ ⊢u₁≡u₂ u₁≡u₂ v₁≡v₂ σ₁≡σ₂ =
    case wf-⊩ᵛ≡ A₁≡A₂ of λ
      (⊩A₁ , ⊩A₂) →
    case wf-⊩ᵛ≡∷ t₁≡t₂ of λ
      (_ , ⊩t₂) →
    case conv-⊩ᵛ∷
           (⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ[]₀≡[]₀ A₁≡A₂ $
            refl-⊩ᵛ≡∷ $ zeroᵛ {l = l} $ wf-⊩ᵛ (wf-⊩ᵛ∷ ⊩t₂))
           ⊩t₂ of λ
      ⊩t₂ →
    case wf-⊩ˢ≡∷ σ₁≡σ₂ of λ
      (⊩σ₁ , ⊩σ₂) →
    case escape-⊩ˢ≡∷ σ₁≡σ₂ of λ
      (_ , ⊢σ₁≡σ₂) →
    case PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (singleSubstLift A₁ _) $
         R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t₁≡t₂ σ₁≡σ₂ of λ
      t₁[σ₁]≡t₂[σ₂] →
    PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (PE.sym $ singleSubstLift A₁ _) $
    ⊩natrec≡natrec′
      (with-inc-⊢≅ (subst-⊢≡-⇑ ⊢A₁≡A₂ ⊢σ₁≡σ₂) $
       R.escape-⊩≡ ⦃ inc = included ⦄ (⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑]≡[⇑] A₁≡A₂ σ₁≡σ₂))
      (R.⊩≡→ ∘→
       ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩A₁) (refl-⊩ˢ≡∷ ⊩σ₁) ∘→
       R.→⊩≡∷)
      (R.⊩≡→ ∘→
       ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩A₂) (refl-⊩ˢ≡∷ ⊩σ₂) ∘→
       R.→⊩≡∷)
      (R.⊩≡→ ∘→ ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ A₁≡A₂ σ₁≡σ₂ ∘→ R.→⊩≡∷)
      (escape-⊩∷ $ wf-⊩≡∷ t₁[σ₁]≡t₂[σ₂] .proj₁)
      (PE.subst (_⊢_∷_ _ _) (singleSubstLift A₂ _) $
       R.escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t₂ ⊩σ₂)
      (level-⊩≡∷
         (wf-⊩≡
            (R.⊩≡→ $
             ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ A₁≡A₂ σ₁≡σ₂ $ R.→⊩≡∷ $
             refl-⊩≡∷ $ ⊩zero {l = l} $ escape-⊩ˢ∷ ⊩σ₁ .proj₁)
            .proj₁)
         t₁[σ₁]≡t₂[σ₂])
      (with-inc-⊢≅∷
         (PE.subst (_⊢_≡_∷_ _ _ _) ([][]↑-commutes A₁) $
          subst-⊢≡∷-⇑ ⊢u₁≡u₂ ⊢σ₁≡σ₂)
         (PE.subst (_⊢_≅_∷_ _ _ _) (natrecSucCase _ A₁) $
          R.escape-⊩≡∷ ⦃ inc = included ⦄ $
          ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑⇑]≡[⇑⇑]∷ u₁≡u₂ σ₁≡σ₂))
      (λ {v₁ = v₁} {v₂ = _} {w₁ = w₁} v₁≡v₂ w₁≡w₂ →
         level-⊩≡∷
           (wf-⊩≡
              (R.⊩≡→ $ ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ A₁≡A₂ σ₁≡σ₂ $
               R.→⊩≡∷ $ ⊩suc≡suc v₁≡v₂)
              .proj₁) $
         PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _)
           (A₁ [ suc (var x1) ]↑² [ σ₁ ⇑ ⇑ ] [ v₁ , w₁ ]₁₀  ≡⟨ PE.cong _[ _ , _ ]₁₀ $ natrecSucCase _ A₁ ⟩
            A₁ [ σ₁ ⇑ ] [ suc (var x1) ]↑² [ v₁ , w₁ ]₁₀    ≡˘⟨ substComp↑² (A₁ [ _ ]) _ ⟩
            A₁ [ σ₁ ⇑ ] [ suc v₁ ]₀                         ∎) $
         R.⊩≡∷→ $
         ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀∷ u₁≡u₂ σ₁≡σ₂
           (R.→⊩≡∷ v₁≡v₂) (R.→⊩≡∷ w₁≡w₂))
      (⊩≡∷ℕ⇔ .proj₁ $ R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ v₁≡v₂ σ₁≡σ₂)
    where
    open Tools.Reasoning.PropositionalEquality

opaque

  -- Validity of equality preservation for natrec.

  natrec-congᵛ :
    Γ »∙ ℕ ⊢ A₁ ≡ A₂ →
    Γ »∙ ℕ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ l′ ⟩ t₁ ≡ t₂ ∷ A₁ [ zero ]₀ →
    Γ »∙ ℕ »∙ A₁ ⊢ u₁ ≡ u₂ ∷ A₁ [ suc (var x1) ]↑² →
    Γ »∙ ℕ »∙ A₁ ⊩ᵛ⟨ l″ ⟩ u₁ ≡ u₂ ∷ A₁ [ suc (var x1) ]↑² →
    Γ ⊩ᵛ⟨ l‴ ⟩ v₁ ≡ v₂ ∷ ℕ →
    Γ ⊩ᵛ⟨ l ⟩ natrec p q r A₁ t₁ u₁ v₁ ≡ natrec p q r A₂ t₂ u₂ v₂ ∷
      A₁ [ v₁ ]₀
  natrec-congᵛ ⊢A₁≡A₂ A₁≡A₂ t₁≡t₂ ⊢u₁≡u₂ u₁≡u₂ v₁≡v₂ =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]₀ (wf-⊩ᵛ≡ A₁≡A₂ .proj₁) (wf-⊩ᵛ≡∷ v₁≡v₂ .proj₁)
      , λ ξ⊇ → ⊩natrec≡natrec (defn-wkEq ξ⊇ ⊢A₁≡A₂)
                              (defn-wk-⊩ᵛ≡ ξ⊇ A₁≡A₂)
                              (defn-wk-⊩ᵛ≡∷ ξ⊇ t₁≡t₂)
                              (defn-wkEqTerm ξ⊇ ⊢u₁≡u₂)
                              (defn-wk-⊩ᵛ≡∷ ξ⊇ u₁≡u₂)
                              (defn-wk-⊩ᵛ≡∷ ξ⊇ v₁≡v₂)
      )

opaque

  -- Validity of natrec.

  natrecᵛ :
    Γ »∙ ℕ ⊩ᵛ⟨ l ⟩ A →
    Γ ⊩ᵛ⟨ l′ ⟩ t ∷ A [ zero ]₀ →
    Γ »∙ ℕ »∙ A ⊢ u ∷ A [ suc (var x1) ]↑² →
    Γ »∙ ℕ »∙ A ⊩ᵛ⟨ l″ ⟩ u ∷ A [ suc (var x1) ]↑² →
    Γ ⊩ᵛ⟨ l‴ ⟩ v ∷ ℕ →
    Γ ⊩ᵛ⟨ l ⟩ natrec p q r A t u v ∷ A [ v ]₀
  natrecᵛ ⊩A ⊩t ⊢u ⊩u ⊩v =
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ $
    natrec-congᵛ (refl (⊢∙→⊢ (wfTerm ⊢u))) (refl-⊩ᵛ≡ ⊩A) (refl-⊩ᵛ≡∷ ⊩t)
      (refl ⊢u) (refl-⊩ᵛ≡∷ ⊩u) (refl-⊩ᵛ≡∷ ⊩v)

opaque

  -- Validity of the equality rule called natrec-zero.

  natrec-zeroᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A [ zero ]₀ →
    Γ »∙ ℕ »∙ A ⊢ u ∷ A [ suc (var x1) ]↑² →
    Γ ⊩ᵛ⟨ l ⟩ natrec p q r A t u zero ≡ t ∷ A [ zero ]₀
  natrec-zeroᵛ {A} ⊩t ⊢u =
    ⊩ᵛ∷-⇐
      (λ ξ⊇ ⊩σ →
         PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ singleSubstLift A _) $
         natrec-zero
           (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) $
            R.escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ (defn-wk-⊩ᵛ∷ ξ⊇ ⊩t) ⊩σ)
           (PE.subst (_⊢_∷_ _ _) (natrecSucCase _ A) $
            subst-⊢∷-⇑ (defn-wkTerm ξ⊇ ⊢u) (escape-⊩ˢ∷ ⊩σ .proj₂)))
      ⊩t

opaque

  -- Validity of the equality rule called natrec-suc.

  natrec-sucᵛ :
    Γ »∙ ℕ ⊩ᵛ⟨ l′ ⟩ A →
    Γ ⊩ᵛ⟨ l″ ⟩ t ∷ A [ zero ]₀ →
    Γ »∙ ℕ »∙ A ⊢ u ∷ A [ suc (var x1) ]↑² →
    Γ »∙ ℕ »∙ A ⊩ᵛ⟨ l ⟩ u ∷ A [ suc (var x1) ]↑² →
    Γ ⊩ᵛ⟨ l‴ ⟩ v ∷ ℕ →
    Γ ⊩ᵛ⟨ l ⟩ natrec p q r A t u (suc v) ≡
      u [ v , natrec p q r A t u v ]₁₀ ∷ A [ suc v ]₀
  natrec-sucᵛ {A} {u} ⊩A ⊩t ⊢u ⊩u ⊩v =
    ⊩ᵛ∷-⇐
      (λ ξ⊇ ⊩σ →
         PE.subst₂ (_⊢_⇒_∷_ _ _) (PE.sym $ [,]-[]-commute u)
           (PE.sym $ singleSubstLift A _) $
         natrec-suc
           (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) $
            R.escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ (defn-wk-⊩ᵛ∷ ξ⊇ ⊩t) ⊩σ)
           (PE.subst (_⊢_∷_ _ _) (natrecSucCase _ A) $
            subst-⊢∷-⇑ (defn-wkTerm ξ⊇ ⊢u) (escape-⊩ˢ∷ ⊩σ .proj₂))
           (R.escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ (defn-wk-⊩ᵛ∷ ξ⊇ ⊩v) ⊩σ))
      (PE.subst (_⊩ᵛ⟨_⟩_∷_ _ _ _) (PE.sym $ substComp↑² A _) $
       ⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₁₀∷ ⊩u ⊩v (natrecᵛ ⊩A ⊩t ⊢u ⊩u ⊩v))
