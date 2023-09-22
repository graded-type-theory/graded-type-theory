------------------------------------------------------------------------
-- Validity for identity types
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Identity
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  ⦃ eqrel : EqRelSet R ⦄
  where

open EqRelSet eqrel
open Modality 𝕄
open Type-restrictions R

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Substitution R
import Definition.LogicalRelation.Substitution.Introductions.Erased R
  as Erased
open import
  Definition.LogicalRelation.Substitution.Introductions.Universe R
import Definition.LogicalRelation.Substitution.Irrelevance R as Irr
open import Definition.LogicalRelation.Substitution.Properties R
open import Definition.LogicalRelation.Substitution.Reflexivity R
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.RedSteps R
open import Definition.Untyped M as U
  hiding (_∷_; _[_]) renaming (_[_,_] to _[_,_]₁₀)
open import Definition.Untyped.Properties M

import Graded.Derived.Erased.Typed.Primitive R as ETP
open import Graded.Derived.Erased.Untyped 𝕄

open import Tools.Fin using (x0)
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  Γ Δ                                             : Con Term _
  A A₁ A₂ B B₁ B₂ t t₁ t₂ u u₁ u₂ v v₁ v₂ w w₁ w₂ : Term _
  l                                               : TypeLevel
  ⊩Γ                                              : ⊩ᵛ _
  m n                                             : Nat
  p q                                             : M

private

  -- Some definitions used in proofs below.

  module E (ok : []-cong-allowed) where

    open Erased ([]-cong→Erased ok) public hiding ([]-congᵛ)
    open ETP    ([]-cong→Erased ok) public

------------------------------------------------------------------------
-- Id

private

  -- Reducibility of Id, seen as a type former.

  ⊩Id′ :
    (⊩A : Γ ⊩⟨ l ⟩ A) →
    Γ ⊩⟨ l ⟩ t ∷ A / ⊩A →
    Γ ⊩⟨ l ⟩ u ∷ A / ⊩A →
    Γ ⊩′⟨ l ⟩Id Id A t u
  ⊩Id′ _  _  _  ._⊩ₗId_.Ty    = _
  ⊩Id′ _  _  _  ._⊩ₗId_.lhs   = _
  ⊩Id′ _  _  _  ._⊩ₗId_.rhs   = _
  ⊩Id′ ⊩A ⊩t ⊩u ._⊩ₗId_.⇒*Id  = idRed:*:
                                  (Idⱼ (escapeTerm ⊩A ⊩t)
                                     (escapeTerm ⊩A ⊩u))
  ⊩Id′ ⊩A _  _  ._⊩ₗId_.⊩Ty   = ⊩A
  ⊩Id′ _  ⊩t _  ._⊩ₗId_.⊩lhs  = ⊩t
  ⊩Id′ _  _  ⊩u ._⊩ₗId_.⊩rhs  = ⊩u

opaque

  -- Reducibility of Id, seen as a type former.

  ⊩Id :
    (⊩A : Γ ⊩⟨ l ⟩ A) →
    Γ ⊩⟨ l ⟩ t ∷ A / ⊩A →
    Γ ⊩⟨ l ⟩ u ∷ A / ⊩A →
    Γ ⊩⟨ l ⟩ Id A t u
  ⊩Id ⊩A ⊩t ⊩u = Idᵣ (⊩Id′ ⊩A ⊩t ⊩u)

opaque
  unfolding ⊩Id

  -- Preservation of well-formed equality for Id, seen as a type
  -- former.

  ⊩Id≡Id :
    {⊩A₁ : Γ ⊩⟨ l ⟩ A₁}
    {⊩t₁ : Γ ⊩⟨ l ⟩ t₁ ∷ A₁ / ⊩A₁} →
    Γ ⊢ t₂ ∷ A₂ →
    {⊩u₁ : Γ ⊩⟨ l ⟩ u₁ ∷ A₁ / ⊩A₁} →
    Γ ⊢ u₂ ∷ A₂ →
    Γ ⊩⟨ l ⟩ A₁ ≡ A₂ / ⊩A₁ →
    Γ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ A₁ / ⊩A₁ →
    Γ ⊩⟨ l ⟩ u₁ ≡ u₂ ∷ A₁ / ⊩A₁ →
    Γ ⊩⟨ l ⟩ Id A₁ t₁ u₁ ≡ Id A₂ t₂ u₂ / ⊩Id ⊩A₁ ⊩t₁ ⊩u₁
  ⊩Id≡Id {⊩A₁} {⊩t₁} ⊢t₂ {⊩u₁} ⊢u₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ =
    Id₌′ (idRed:*: (Idⱼ ⊢t₂ ⊢u₂)) A₁≡A₂ t₁≡t₂ u₁≡u₂

private

  -- Validity of Id, seen as a type former.

  Idᵛ′ :
    (⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ) →
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A / ⊩Γ / ⊩A →
    Γ ⊩ᵛ⟨ l ⟩ u ∷ A / ⊩Γ / ⊩A →
    Γ ⊩ᵛ⟨ l ⟩ Id A t u / ⊩Γ
  Idᵛ′ {⊩Γ} ⊩A ⊩t ⊩u = wrap λ ⊢Δ ⊩σ →
    let ⊩A₁ , A≡A = ⊩A .unwrap ⊢Δ ⊩σ in
    case ⊩t ⊢Δ ⊩σ of λ {
      (⊩t₁ , t≡t) →
    case ⊩u ⊢Δ ⊩σ of λ {
      (⊩u₁ , u≡u) →
    let ⊩Id = ⊩Id ⊩A₁ ⊩t₁ ⊩u₁ in
      ⊩Id
    , λ {_} ⊩σ′ σ≡σ′ →
        let ⊩A₂ , _ = ⊩A .unwrap ⊢Δ ⊩σ′ in
        case ⊩t ⊢Δ ⊩σ′ of λ {
          (⊩t₂ , _) →
        case ⊩u ⊢Δ ⊩σ′ of λ {
          (⊩u₂ , _) →
        case escapeTerm ⊩A₂ ⊩t₂ of λ {
          ⊢t₂ →
        case escapeTerm ⊩A₂ ⊩u₂ of λ {
          ⊢u₂ →
        case A≡A ⊩σ′ σ≡σ′ of λ {
          A≡A →
        case t≡t ⊩σ′ σ≡σ′ of λ {
          t≡t →
        case u≡u ⊩σ′ σ≡σ′ of λ {
          u≡u →
        ⊩Id≡Id ⊢t₂ ⊢u₂ A≡A t≡t u≡u }}}}}}}}}

opaque

  -- Validity of Id, seen as a type former.

  Idᵛ :
    (⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ) →
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A / ⊩Γ / ⊩A →
    Γ ⊩ᵛ⟨ l ⟩ u ∷ A / ⊩Γ / ⊩A →
    Γ ⊩ᵛ⟨ l ⟩ Id A t u / ⊩Γ
  Idᵛ = Idᵛ′

opaque

  -- Validity of Id, seen as a term former.

  Idᵗᵛ :
    ∀ t u →
    (⊩A : Γ ⊩ᵛ⟨ ¹ ⟩ A / ⊩Γ) →
    Γ ⊩ᵛ⟨ ¹ ⟩ A ∷ U / ⊩Γ / Uᵛ ⊩Γ →
    Γ ⊩ᵛ⟨ ¹ ⟩ t ∷ A / ⊩Γ / ⊩A →
    Γ ⊩ᵛ⟨ ¹ ⟩ u ∷ A / ⊩Γ / ⊩A →
    Γ ⊩ᵛ⟨ ¹ ⟩ Id A t u ∷ U / ⊩Γ / Uᵛ ⊩Γ
  Idᵗᵛ {⊩Γ} t u ⊩A ⊩A∷U ⊩t ⊩u ⊢Δ ⊩σ =
    let ⊩U  , _ = Uᵛ ⊩Γ .unwrap ⊢Δ ⊩σ
        ⊩A₁ , _ = ⊩A .unwrap ⊢Δ ⊩σ
    in
    case univᵛ ⊩Γ (Uᵛ ⊩Γ) ⊩A∷U of λ {
      ⊩A∷U₀ →
    case ⊩A∷U ⊢Δ ⊩σ of λ {
      (⊩A∷U₁ , A≡A∷U) →
    case ⊩t ⊢Δ ⊩σ of λ {
      (⊩t₁ , t≡t) →
    case ⊩u ⊢Δ ⊩σ of λ {
      (⊩u₁ , u≡u) →
    case escapeTerm ⊩U ⊩A∷U₁ of λ {
      ⊢A₁ →
    case escapeTerm ⊩A₁ ⊩t₁ of λ {
      ⊢t₁ →
    case escapeTerm ⊩A₁ ⊩u₁ of λ {
      ⊢u₁ →
    case reflSubst ⊩Γ ⊢Δ ⊩σ of λ {
      σ≡σ →
    case escapeTermEq ⊩U (A≡A∷U ⊩σ σ≡σ) of λ {
      A≅A₁ →
    case escapeTermEq ⊩A₁ (t≡t ⊩σ σ≡σ) of λ {
      t≅t₁ →
    case escapeTermEq ⊩A₁ (u≡u ⊩σ σ≡σ) of λ {
      u≅u₁ →
    case Idᵛ {t = t} {u = u} ⊩A∷U₀
           (Irr.irrelevanceTerm {t = t} ⊩Γ ⊩Γ ⊩A ⊩A∷U₀ ⊩t)
           (Irr.irrelevanceTerm {t = u} ⊩Γ ⊩Γ ⊩A ⊩A∷U₀ ⊩u) of λ {
      ⊩Id →
    case ⊩Id .unwrap ⊢Δ ⊩σ of λ {
      (⊩Id₁ , Id≡Id) →
      record
        { d     = idRedTerm:*: (Idⱼ ⊢A₁ ⊢t₁ ⊢u₁)
        ; typeA = Idₙ
        ; A≡A   = ≅ₜ-Id-cong A≅A₁ t≅t₁ u≅u₁
        ; [t]   = ⊩Id₁
        }
    , λ ⊩σ′ σ≡σ′ →
        let ⊩A₂ , _ = ⊩A .unwrap ⊢Δ ⊩σ′ in
        case ⊩A∷U ⊢Δ ⊩σ′ of λ {
          (⊩A∷U₂ , _) →
        case ⊩t ⊢Δ ⊩σ′ of λ {
          (⊩t₂ , _) →
        case ⊩u ⊢Δ ⊩σ′ of λ {
          (⊩u₂ , _) →
        case escapeTerm ⊩U ⊩A∷U₂ of λ {
          ⊢A₂ →
        case escapeTerm ⊩A₂ ⊩t₂ of λ {
          ⊢t₂ →
        case escapeTerm ⊩A₂ ⊩u₂ of λ {
          ⊢u₂ →
        case A≡A∷U ⊩σ′ σ≡σ′ of λ {
          A≡A∷U →
        case t≡t ⊩σ′ σ≡σ′ of λ {
          t≡t →
        case u≡u ⊩σ′ σ≡σ′ of λ {
          u≡u →
        case escapeTermEq ⊩U A≡A∷U of λ {
          A≅A₂ →
        case escapeTermEq ⊩A₁ t≡t of λ {
          t≅t₂ →
        case escapeTermEq ⊩A₁ u≡u of λ {
          u≅u₂ →
        case ⊩Id .unwrap ⊢Δ ⊩σ′ .proj₁ of λ {
          ⊩Id₂ →
        _ ⊩⟨ _ ⟩ _ ≡ _ ∷ _ / ⊩U ∋
        record
          { d     = idRedTerm:*: (Idⱼ ⊢A₁ ⊢t₁ ⊢u₁)
          ; d′    = idRedTerm:*: (Idⱼ ⊢A₂ ⊢t₂ ⊢u₂)
          ; typeA = Idₙ
          ; typeB = Idₙ
          ; A≡B   = ≅ₜ-Id-cong A≅A₂ t≅t₂ u≅u₂
          ; [t]   = ⊩Id₁
          ; [u]   = ⊩Id₂
          ; [t≡u] = Id≡Id ⊩σ′ σ≡σ′
          }
        }}}}}}}}}}}}}}}}}}}}}}}}}}

opaque
  unfolding Idᵛ

  -- Validity of equality preservation for Id, seen as a type former.

  Id-congᵛ :
    ∀ t₂ u₂ →
    {⊩A₁ : Γ ⊩ᵛ⟨ l ⟩ A₁ / ⊩Γ}
    (⊩A₂ : Γ ⊩ᵛ⟨ l ⟩ A₂ / ⊩Γ)
    {⊩t₁ : Γ ⊩ᵛ⟨ l ⟩ t₁ ∷ A₁ / ⊩Γ / ⊩A₁} →
    Γ ⊩ᵛ⟨ l ⟩ t₂ ∷ A₂ / ⊩Γ / ⊩A₂ →
    {⊩u₁ : Γ ⊩ᵛ⟨ l ⟩ u₁ ∷ A₁ / ⊩Γ / ⊩A₁} →
    Γ ⊩ᵛ⟨ l ⟩ u₂ ∷ A₂ / ⊩Γ / ⊩A₂ →
    Γ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ / ⊩Γ / ⊩A₁ →
    Γ ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ A₁ / ⊩Γ / ⊩A₁ →
    Γ ⊩ᵛ⟨ l ⟩ u₁ ≡ u₂ ∷ A₁ / ⊩Γ / ⊩A₁ →
    Γ ⊩ᵛ⟨ l ⟩ Id A₁ t₁ u₁ ≡ Id A₂ t₂ u₂ / ⊩Γ / Idᵛ ⊩A₁ ⊩t₁ ⊩u₁
  Id-congᵛ _ _ ⊩A₂ ⊩t₂ ⊩u₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ ⊢Δ ⊩σ =
    let ⊩A₂′ , _ = ⊩A₂ .unwrap ⊢Δ ⊩σ in
    case ⊩t₂ ⊢Δ ⊩σ of λ {
      (⊩t₂ , _) →
    case ⊩u₂ ⊢Δ ⊩σ of λ {
      (⊩u₂ , _) →
    case escapeTerm ⊩A₂′ ⊩t₂ of λ {
      ⊢t₂ →
    case escapeTerm ⊩A₂′ ⊩u₂ of λ {
      ⊢u₂ →
    case A₁≡A₂ ⊢Δ ⊩σ of λ {
      A₁≡A₂ →
    case t₁≡t₂ ⊢Δ ⊩σ of λ {
      t₁≡t₂ →
    case u₁≡u₂ ⊢Δ ⊩σ of λ {
      u₁≡u₂ →
    ⊩Id≡Id  ⊢t₂ ⊢u₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ }}}}}}}

opaque

  -- Validity of equality preservation for Id, seen as a term former.

  Id-congᵗᵛ :
    ∀ t₁ t₂ u₁ u₂ →
    (⊩A₁ : Γ ⊩ᵛ⟨ ¹ ⟩ A₁ / ⊩Γ)
    (⊩A₂ : Γ ⊩ᵛ⟨ ¹ ⟩ A₂ / ⊩Γ) →
    Γ ⊩ᵛ⟨ ¹ ⟩ A₁ ∷ U / ⊩Γ / Uᵛ ⊩Γ →
    Γ ⊩ᵛ⟨ ¹ ⟩ A₂ ∷ U / ⊩Γ / Uᵛ ⊩Γ →
    (⊩t₁ : Γ ⊩ᵛ⟨ ¹ ⟩ t₁ ∷ A₁ / ⊩Γ / ⊩A₁) →
    Γ ⊩ᵛ⟨ ¹ ⟩ t₂ ∷ A₂ / ⊩Γ / ⊩A₂ →
    (⊩u₁ : Γ ⊩ᵛ⟨ ¹ ⟩ u₁ ∷ A₁ / ⊩Γ / ⊩A₁) →
    Γ ⊩ᵛ⟨ ¹ ⟩ u₂ ∷ A₂ / ⊩Γ / ⊩A₂ →
    Γ ⊩ᵛ⟨ ¹ ⟩ A₁ ≡ A₂ ∷ U / ⊩Γ / Uᵛ ⊩Γ →
    Γ ⊩ᵛ⟨ ¹ ⟩ t₁ ≡ t₂ ∷ A₁ / ⊩Γ / ⊩A₁ →
    Γ ⊩ᵛ⟨ ¹ ⟩ u₁ ≡ u₂ ∷ A₁ / ⊩Γ / ⊩A₁ →
    Γ ⊩ᵛ⟨ ¹ ⟩ Id A₁ t₁ u₁ ≡ Id A₂ t₂ u₂ ∷ U / ⊩Γ / Uᵛ ⊩Γ
  Id-congᵗᵛ
    {A₁} {⊩Γ} {A₂}
    t₁ t₂ u₁ u₂ ⊩A₁ ⊩A₂ ⊩A₁∷U ⊩A₂∷U ⊩t₁ ⊩t₂ ⊩u₁ ⊩u₂ A₁≡A₂∷U t₁≡t₂ u₁≡u₂
    ⊢Δ ⊩σ =
    let ⊩U  , _  = Uᵛ ⊩Γ .unwrap ⊢Δ ⊩σ
        ⊩A₁′ , _ = ⊩A₁ .unwrap ⊢Δ ⊩σ
        ⊩A₂′ , _ = ⊩A₂ .unwrap ⊢Δ ⊩σ
    in
    case ⊩A₁∷U ⊢Δ ⊩σ of λ {
      (⊩A₁∷U′ , _) →
    case ⊩A₂∷U ⊢Δ ⊩σ of λ {
      (⊩A₂∷U′ , _) →
    case ⊩t₁ ⊢Δ ⊩σ of λ {
      (⊩t₁′ , _) →
    case ⊩t₂ ⊢Δ ⊩σ of λ {
      (⊩t₂′ , _) →
    case ⊩u₁ ⊢Δ ⊩σ of λ {
      (⊩u₁′ , _) →
    case ⊩u₂ ⊢Δ ⊩σ of λ {
      (⊩u₂′ , _) →
    case escapeTerm ⊩U ⊩A₁∷U′ of λ {
      ⊢A₁ →
    case escapeTerm ⊩U ⊩A₂∷U′ of λ {
      ⊢A₂ →
    case escapeTerm ⊩A₁′ ⊩t₁′ of λ {
      ⊢t₁ →
    case escapeTerm ⊩A₂′ ⊩t₂′ of λ {
      ⊢t₂ →
    case escapeTerm ⊩A₁′ ⊩u₁′ of λ {
      ⊢u₁ →
    case escapeTerm ⊩A₂′ ⊩u₂′ of λ {
      ⊢u₂ →
    case A₁≡A₂∷U ⊢Δ ⊩σ of λ {
      A₁≡A₂∷U′ →
    case t₁≡t₂ ⊢Δ ⊩σ of λ {
      t₁≡t₂′ →
    case u₁≡u₂ ⊢Δ ⊩σ of λ {
      u₁≡u₂′ →
    case escapeTermEq ⊩U A₁≡A₂∷U′ of λ {
      A₁≅A₂ →
    case escapeTermEq ⊩A₁′ t₁≡t₂′ of λ {
      t₁≅t₂ →
    case escapeTermEq ⊩A₁′ u₁≡u₂′ of λ {
      u₁≅u₂ →
    case univᵛ {A = A₁} {l′ = ⁰} ⊩Γ (Uᵛ ⊩Γ) ⊩A₁∷U of λ {
      ⊩A₁₀ →
    case univᵛ {A = A₂} {l′ = ⁰} ⊩Γ (Uᵛ ⊩Γ) ⊩A₂∷U of λ {
      ⊩A₂₀ →
    case (λ {k Δ σ} →
            Irr.irrelevanceTerm {t = t₁} ⊩Γ ⊩Γ ⊩A₁ ⊩A₁₀ ⊩t₁
              {k = k} {Δ = Δ} {σ = σ}) of λ {
      ⊩t₁₀ →
    case (λ {k Δ σ} →
            Irr.irrelevanceTerm {t = t₂} ⊩Γ ⊩Γ ⊩A₂ ⊩A₂₀ ⊩t₂
              {k = k} {Δ = Δ} {σ = σ}) of λ {
      ⊩t₂₀ →
    case (λ {k Δ σ} →
            Irr.irrelevanceTerm {t = u₁} ⊩Γ ⊩Γ ⊩A₁ ⊩A₁₀ ⊩u₁
              {k = k} {Δ = Δ} {σ = σ}) of λ {
      ⊩u₁₀ →
    case (λ {k Δ σ} →
            Irr.irrelevanceTerm {t = u₂} ⊩Γ ⊩Γ ⊩A₂ ⊩A₂₀ ⊩u₂
              {k = k} {Δ = Δ} {σ = σ}) of λ {
      ⊩u₂₀ →
    case (λ {k Δ σ} →
            univEqᵛ {B = A₂} ⊩Γ (Uᵛ ⊩Γ) ⊩A₁₀ A₁≡A₂∷U
              {k = k} {Δ = Δ} {σ = σ}) of λ {
      A₁≡A₂₀ →
    case (λ {k Δ σ} →
            Irr.irrelevanceEqTerm {t = t₁} {u = t₂} ⊩Γ ⊩Γ ⊩A₁ ⊩A₁₀ t₁≡t₂
              {k = k} {Δ = Δ} {σ = σ}) of λ {
      t₁≡t₂₀ →
    case (λ {k Δ σ} →
            Irr.irrelevanceEqTerm {t = u₁} {u = u₂} ⊩Γ ⊩Γ ⊩A₁ ⊩A₁₀ u₁≡u₂
              {k = k} {Δ = Δ} {σ = σ}) of λ {
      u₁≡u₂₀ →
    _ ⊩⟨ _ ⟩ _ ≡ _ ∷ _ / ⊩U ∋
    record
      { d     = idRedTerm:*: (Idⱼ ⊢A₁ ⊢t₁ ⊢u₁)
      ; d′    = idRedTerm:*: (Idⱼ ⊢A₂ ⊢t₂ ⊢u₂)
      ; typeA = Idₙ
      ; typeB = Idₙ
      ; A≡B   = ≅ₜ-Id-cong A₁≅A₂ t₁≅t₂ u₁≅u₂
      ; [t]   = Idᵛ {t = t₁} {u = u₁} ⊩A₁₀ ⊩t₁₀ ⊩u₁₀
                  .unwrap ⊢Δ ⊩σ .proj₁
      ; [u]   = Idᵛ {t = t₂} {u = u₂} ⊩A₂₀ ⊩t₂₀ ⊩u₂₀
                  .unwrap ⊢Δ ⊩σ .proj₁
      ; [t≡u] = Id-congᵛ t₂ u₂ ⊩A₂₀ ⊩t₂₀ ⊩u₂₀
                  A₁≡A₂₀ t₁≡t₂₀ u₁≡u₂₀ ⊢Δ ⊩σ
      } }}}}}}}}}}}}}}}}}}}}}}}}}}}

------------------------------------------------------------------------
-- The term rfl

opaque
  unfolding ⊩Id

  -- Reducibility of reflexivity.

  ⊩rfl′ :
    {⊩A : Γ ⊩⟨ l ⟩ A}
    {⊩t : Γ ⊩⟨ l ⟩ t ∷ A / ⊩A}
    {⊩u : Γ ⊩⟨ l ⟩ u ∷ A / ⊩A} →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A / ⊩A →
    Γ ⊩⟨ l ⟩ rfl ∷ Id A t u / ⊩Id ⊩A ⊩t ⊩u
  ⊩rfl′ {⊩A} {⊩t} {⊩u} t≡u =
    case escapeTerm ⊩A ⊩t of λ {
      ⊢t →
      rfl
    , idRedTerm:*:
        (conv (rflⱼ ⊢t)
           (Id-cong
              (≅-eq (escapeEq ⊩A (reflEq ⊩A)))
              (≅ₜ-eq (escapeTermEq ⊩A (reflEqTerm ⊩A ⊩t)))
              (≅ₜ-eq (escapeTermEq ⊩A t≡u))))
    , rflₙ
    , t≡u }

opaque

  -- Reducibility of reflexivity.

  ⊩rfl :
    {⊩A : Γ ⊩⟨ l ⟩ A}
    {⊩t : Γ ⊩⟨ l ⟩ t ∷ A / ⊩A} →
    Γ ⊩⟨ l ⟩ rfl ∷ Id A t t / ⊩Id ⊩A ⊩t ⊩t
  ⊩rfl {⊩A} {⊩t} = ⊩rfl′ (reflEqTerm ⊩A ⊩t)

opaque
  unfolding ⊩rfl′

  -- Reducibility of equality between rfl and rfl.

  ⊩rfl≡rfl :
    {⊩A : Γ ⊩⟨ l ⟩ A}
    {⊩t : Γ ⊩⟨ l ⟩ t ∷ A / ⊩A}
    {⊩u : Γ ⊩⟨ l ⟩ u ∷ A / ⊩A} →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A / ⊩A →
    Γ ⊩⟨ l ⟩ rfl ≡ rfl ∷ Id A t u / ⊩Id ⊩A ⊩t ⊩u
  ⊩rfl≡rfl {⊩A} {⊩t} {⊩u} t≡u =
    let ⊩rfl = ⊩rfl′ {⊩A = ⊩A} {⊩t = ⊩t} {⊩u = ⊩u} t≡u in
    ⊩Id≡∷ ⊩rfl ⊩rfl _

opaque
  unfolding Idᵛ ⊩rfl ⊩rfl′

  -- Validity of reflexivity.

  rflᵛ :
    {⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ}
    {⊩t : Γ ⊩ᵛ⟨ l ⟩ t ∷ A / ⊩Γ / ⊩A} →
    Γ ⊩ᵛ⟨ l ⟩ rfl ∷ Id A t t / ⊩Γ / Idᵛ ⊩A ⊩t ⊩t
  rflᵛ {⊩t} _ ⊩σ =
    let ⊩rfl = ⊩rfl {⊩t = ⊩t _ ⊩σ .proj₁} in
      ⊩rfl
    , λ _ _ → ⊩Id≡∷ ⊩rfl ⊩rfl _

opaque

  -- Validity of equality for rfl.

  rfl-congᵛ :
    {⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ}
    {⊩t : Γ ⊩ᵛ⟨ l ⟩ t ∷ A / ⊩Γ / ⊩A} →
    Γ ⊩ᵛ⟨ l ⟩ rfl ≡ rfl ∷ Id A t t / ⊩Γ / Idᵛ ⊩A ⊩t ⊩t
  rfl-congᵛ _ ⊩σ = rflᵛ _ ⊩σ .proj₂ ⊩σ (reflSubst _ _ ⊩σ)

------------------------------------------------------------------------
-- []-cong

private opaque

  -- A lemma used to implement []-congᵛ and []-cong-congᵛ.

  []-cong-cong′ :
    (ok : []-cong-allowed) →
    let open E ok in
    {⊩A₁ : Γ ⊩⟨ l ⟩ A₁}
    (⊩A₂ : Γ ⊩⟨ l ⟩ A₂) →
    Γ ⊩⟨ l ⟩ A₁ ≡ A₂ / ⊩A₁ →
    Γ ⊩⟨ l ⟩ t₁ ∷ A₁ / ⊩A₁ →
    Γ ⊩⟨ l ⟩ t₂ ∷ A₂ / ⊩A₂ →
    Γ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ A₁ / ⊩A₁ →
    Γ ⊩⟨ l ⟩ u₁ ∷ A₁ / ⊩A₁ →
    Γ ⊩⟨ l ⟩ u₂ ∷ A₂ / ⊩A₂ →
    Γ ⊩⟨ l ⟩ u₁ ≡ u₂ ∷ A₁ / ⊩A₁ →
    (⊩Id : Γ ⊩′⟨ l ⟩Id Id A₁ t₁ u₁)
    (Ty≡ : _⊩ₗId_.Ty ⊩Id PE.≡ A₁) →
    PE.subst (_ ⊩⟨ _ ⟩_) Ty≡ (_⊩ₗId_.⊩Ty ⊩Id) PE.≡ ⊩A₁ →
    _⊩ₗId_.lhs ⊩Id PE.≡ t₁ →
    _⊩ₗId_.rhs ⊩Id PE.≡ u₁ →
    (⊩Id-[]-[] : Γ ⊩′⟨ l ⟩Id Id (Erased A₁) [ t₁ ] [ u₁ ])
    (Ty≡ : _⊩ₗId_.Ty ⊩Id-[]-[] PE.≡ Erased A₁) →
    PE.subst (_ ⊩⟨ _ ⟩_) Ty≡ (_⊩ₗId_.⊩Ty ⊩Id-[]-[]) PE.≡ ⊩Erased ⊩A₁ →
    _⊩ₗId_.lhs ⊩Id-[]-[] PE.≡ [ t₁ ] →
    _⊩ₗId_.rhs ⊩Id-[]-[] PE.≡ [ u₁ ] →
    Γ ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ Id A₁ t₁ u₁ / Idᵣ ⊩Id →
    Γ ⊩⟨ l ⟩ []-cong A₁ t₁ u₁ v₁ ≡ []-cong A₂ t₂ u₂ v₂ ∷
      Id (Erased A₁) [ t₁ ] [ u₁ ] / Idᵣ ⊩Id-[]-[]
  []-cong-cong′
    {A₁} {A₂} {t₁} {t₂} {u₁} {u₂} ok
    {⊩A₁} ⊩A₂ ⊩A₁≡A₂ ⊩t₁ ⊩t₂ ⊩t₁≡t₂ ⊩u₁ ⊩u₂ ⊩u₁≡u₂ ⊩Id
    PE.refl PE.refl PE.refl PE.refl _ PE.refl PE.refl PE.refl PE.refl
    ⊩v₁≡v₂ =
      case escape ⊩A₁ of λ {
        ⊢A₁ →
      case escape ⊩A₂ of λ {
        ⊢A₂ →
      case escapeTerm ⊩A₁ ⊩t₁ of λ {
        ⊢t₁ →
      case escapeTerm ⊩A₁ ⊩u₁ of λ {
        ⊢u₁ →
      case escapeTerm ⊩A₂ ⊩t₂ of λ {
        ⊢t₂ →
      case escapeTerm ⊩A₂ ⊩u₂ of λ {
        ⊢u₂ →
      case escapeEq ⊩A₁ ⊩A₁≡A₂ of λ {
        A₁≅A₂ →
      case escapeTermEq ⊩A₁ ⊩t₁≡t₂ of λ {
        t₁≅t₂ →
      case escapeTermEq ⊩A₁ ⊩u₁≡u₂ of λ {
        u₁≅u₂ →
      case ≅-eq A₁≅A₂ of λ {
        ⊢A₁≡A₂ →
      case ≅ₜ-eq t₁≅t₂ of λ {
        ⊢t₁≡t₂ →
      case ≅ₜ-eq u₁≅u₂ of λ {
        ⊢u₁≡u₂ →
      case _⊢_≡_.Id-cong ⊢A₁≡A₂ ⊢t₁≡t₂ ⊢u₁≡u₂ of λ {
        ⊢Id-t₁-u₁≡Id-t₂-u₂ →
      case _⊢_≡_.Id-cong
             (Erased-cong ⊢A₁ ⊢A₁≡A₂)
             ([]-cong′ ⊢A₁ ⊢t₁≡t₂)
             ([]-cong′ ⊢A₁ ⊢u₁≡u₂) of λ {
        ⊢Id[t₁][u₁]≡Id[t₂][u₂] →
      case ⊩v₁≡v₂ of λ {
        ⊩v₁≡v₂@(v₁′ , v₂′ , v₁⇒*v₁′ , v₂⇒*v₂′ , _) →
      let (⊩v₁ , ⊩v₂ , _) = ⊩Id≡∷⁻¹ ⊩Id ⊩v₁≡v₂ in
      case escapeTerm (Idᵣ ⊩Id) ⊩v₁ of λ {
        ⊢v₁ →
      case escapeTerm (Idᵣ ⊩Id) ⊩v₂ of λ {
        ⊢v₂ →
      case ⊩Id≡∷-view-inhabited ⊩Id ⊩v₁≡v₂ of λ where
        (ne v₁′-n v₂′-n v₁′~v₂′) →
            []-cong A₁ t₁ u₁ v₁′
          , []-cong A₂ t₂ u₂ v₂′
          , []-cong-subst:*: ⊢A₁ ⊢t₁ ⊢u₁ v₁⇒*v₁′ ok
          , convRed:*:
              ([]-cong-subst:*: ⊢A₂ ⊢t₂ ⊢u₂
                 (convRed:*: v₂⇒*v₂′ ⊢Id-t₁-u₁≡Id-t₂-u₂) ok)
              (sym ⊢Id[t₁][u₁]≡Id[t₂][u₂])
          , ne ([]-congₙ v₁′-n)
          , ne ([]-congₙ v₂′-n)
          , ~-[]-cong A₁≅A₂ t₁≅t₂ u₁≅u₂ v₁′~v₂′ ok
        (rfl₌ ⊩t₁≡u₁) →
          case ⊩[]≡[] ⊩A₁ ⊩t₁ ⊩u₁ ⊩t₁≡u₁ of λ {
            ⊩[t₁]≡[u₁] →
          case ≅ₜ-eq (escapeTermEq ⊩A₁ ⊩t₁≡u₁) of λ {
            ⊢t₁≡u₁ →
          case _⊢_≡_.Id-cong (refl (Erasedⱼ ⊢A₁)) (refl ([]ⱼ ⊢A₁ ⊢t₁))
                 ([]-cong′ ⊢A₁ ⊢t₁≡u₁) of λ {
            ⊢Id[t₁][t₁]≡Id[t₁][u₁] →
          case _⊢_∷_.conv (rflⱼ ([]ⱼ ⊢A₁ ⊢t₁))
                 ⊢Id[t₁][t₁]≡Id[t₁][u₁] of λ {
            ⊢rfl →
            rfl
          , rfl
          , record
              { ⊢t = []-congⱼ ⊢t₁ ⊢u₁ ⊢v₁ ok
              ; ⊢u = ⊢rfl
              ; d  = []-cong-subst* ⊢A₁ ⊢t₁ ⊢u₁ (redₜ v₁⇒*v₁′) ok ⇨∷*
                     ([]-cong-β ⊢A₁ ⊢t₁ ⊢u₁ ⊢t₁≡u₁ ok ⇨
                      id ⊢rfl)
              }
          , record
              { ⊢t = conv
                       ([]-congⱼ ⊢t₂ ⊢u₂ (conv ⊢v₂ ⊢Id-t₁-u₁≡Id-t₂-u₂)
                          ok)
                       (sym ⊢Id[t₁][u₁]≡Id[t₂][u₂])
              ; ⊢u = ⊢rfl
              ; d  = conv*
                       ([]-cong-subst* ⊢A₂ ⊢t₂ ⊢u₂
                          (conv* (redₜ v₂⇒*v₂′) ⊢Id-t₁-u₁≡Id-t₂-u₂) ok)
                       (sym ⊢Id[t₁][u₁]≡Id[t₂][u₂]) ⇨∷*
                     (conv
                        ([]-cong-β ⊢A₂ ⊢t₂ ⊢u₂
                           (conv
                              (trans (sym ⊢t₁≡t₂)
                                 (trans ⊢t₁≡u₁ ⊢u₁≡u₂))
                              ⊢A₁≡A₂)
                           ok)
                        (sym ⊢Id[t₁][u₁]≡Id[t₂][u₂]) ⇨
                      id ⊢rfl)
              }
          , rflₙ
          , rflₙ
          , ⊩[t₁]≡[u₁] }}}}}}}}}}}}}}}}}}}}}
    where
    open E ok

opaque
  unfolding Idᵛ ⊩Id Erased.Erasedᵛ Erased.⊩Erased

  -- Validity of []-cong.

  []-congᵛ :
    {ok : []-cong-allowed} →
    let open E ok in
    {⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ}
    {⊩t : Γ ⊩ᵛ⟨ l ⟩ t ∷ A / ⊩Γ / ⊩A}
    {⊩u : Γ ⊩ᵛ⟨ l ⟩ u ∷ A / ⊩Γ / ⊩A} →
    ∀ v →
    Γ ⊩ᵛ⟨ l ⟩ v ∷ Id A t u / ⊩Γ / Idᵛ ⊩A ⊩t ⊩u →
    Γ ⊩ᵛ⟨ l ⟩ []-cong A t u v ∷ Id (Erased A) [ t ] [ u ] / ⊩Γ /
      Idᵛ (Erasedᵛ ⊩A) ([]ᵛ t ⊩t) ([]ᵛ u ⊩u)
  []-congᵛ
    {Γ} {l} {A} {⊩Γ} {t} {u} {ok} {⊩A} {⊩t} {⊩u} v ⊩v {Δ} {σ} ⊢Δ ⊩σ =
    lemma₁ , lemma₂
    where
    open E ok

    ⊩Id-[t]-[u] : Δ ⊩⟨ l ⟩ Id (Erased A) [ t ] [ u ] U.[ σ ]
    ⊩Id-[t]-[u] =
      Idᵛ {t = [ t ]} {u = [ u ]}
        (Erasedᵛ ⊩A) ([]ᵛ {⊩A = ⊩A} t ⊩t) ([]ᵛ {⊩A = ⊩A} u ⊩u)
        .unwrap ⊢Δ ⊩σ .proj₁

    lemma₁ :
      Δ ⊩⟨ l ⟩ []-cong A t u v U.[ σ ] ∷
        Id (Erased A) [ t ] [ u ] U.[ σ ] / ⊩Id-[t]-[u]
    lemma₁ =
      case reflᵛ _ ⊩A ⊢Δ ⊩σ of λ {
        ⊩A≡A →
      case reflᵗᵛ {t = t} _ ⊩A ⊩t ⊢Δ ⊩σ of λ {
        ⊩t≡t →
      case reflᵗᵛ {t = u} _ ⊩A ⊩u ⊢Δ ⊩σ of λ {
        ⊩u≡u →
      let ⊩Id , _ = Idᵛ {t = t} {u = u} ⊩A ⊩t ⊩u .unwrap ⊢Δ ⊩σ
          ⊩A  , _ = ⊩A .unwrap ⊢Δ ⊩σ
      in
      case ⊩t ⊢Δ ⊩σ .proj₁ of λ {
        ⊩t →
      case ⊩u ⊢Δ ⊩σ .proj₁ of λ {
        ⊩u →
      case escape ⊩A of λ {
        ⊢A →
      case escapeTerm ⊩A ⊩t of λ {
        ⊢t →
      case escapeTerm ⊩A ⊩u of λ {
        ⊢u →
      case escapeEq ⊩A ⊩A≡A of λ {
        A≅A →
      case escapeTermEq ⊩A ⊩t≡t of λ {
        t≅t →
      case escapeTermEq ⊩A ⊩u≡u of λ {
        u≅u →
      case ⊩v ⊢Δ ⊩σ .proj₁ of λ where
        (v′ , v⇒*v′ , ne v′-n , v′~v′) →
            []-cong (A U.[ σ ]) (t U.[ σ ]) (u U.[ σ ]) v′
          , []-cong-subst:*: ⊢A ⊢t ⊢u v⇒*v′ ok
          , ne ([]-congₙ v′-n)
          , ~-[]-cong A≅A t≅t u≅u v′~v′ ok
        ⊩v@(.rfl , v⇒*rfl , rflₙ , ⊩t≡u) →
          case escapeTerm ⊩Id ⊩v of λ {
            ⊢v →
          case ≅ₜ-eq (escapeTermEq ⊩A ⊩t≡u) of λ {
            ⊢t≡u →
          case _⊢_≡_.Id-cong (refl (Erasedⱼ ⊢A)) (refl ([]ⱼ ⊢A ⊢t))
                 ([]-cong′ ⊢A ⊢t≡u) of λ {
            ⊢Id[t][t]≡Id[t][u] →
          case _⊢_∷_.conv (rflⱼ ([]ⱼ ⊢A ⊢t)) ⊢Id[t][t]≡Id[t][u] of λ {
            ⊢rfl →
              rfl
            , record
                 { ⊢t = []-congⱼ ⊢t ⊢u ⊢v ok
                 ; ⊢u = ⊢rfl
                 ; d  = []-cong-subst* ⊢A ⊢t ⊢u (redₜ v⇒*rfl) ok ⇨∷*
                        ([]-cong-β ⊢A ⊢t ⊢u ⊢t≡u ok ⇨
                         id ⊢rfl)
                 }
            , rflₙ
            , ⊩[]≡[] ⊩A ⊩t ⊩u ⊩t≡u }}}}}}}}}}}}}}}

    lemma₂ :
      ∀ {σ′} →
      Δ ⊩ˢ σ′ ∷ Γ / ⊩Γ / ⊢Δ →
      Δ ⊩ˢ σ ≡ σ′ ∷ Γ / ⊩Γ / ⊢Δ / ⊩σ →
      Δ ⊩⟨ l ⟩ []-cong A t u v U.[ σ ] ≡ []-cong A t u v U.[ σ′ ] ∷
        Id (Erased A) [ t ] [ u ] U.[ σ ] / ⊩Id-[t]-[u]
    lemma₂ {σ′} ⊩σ′ σ≡σ′ =
      let ⊩A₁ , _ = ⊩A .unwrap ⊢Δ ⊩σ in
      case ⊩t ⊢Δ ⊩σ .proj₁ of λ {
        ⊩t₁ →
      case ⊩u ⊢Δ ⊩σ .proj₁ of λ {
        ⊩u₁ →
      irrelevanceEqTerm
        (⊩Id (⊩Erased ⊩A₁) (⊩[] {⊩A = ⊩A₁} ⊩t₁) (⊩[] {⊩A = ⊩A₁} ⊩u₁))
        ⊩Id-[t]-[u] $
      []-cong-cong′
        ok
        (⊩A .unwrap ⊢Δ ⊩σ′ .proj₁)
        (⊩A .unwrap ⊢Δ ⊩σ  .proj₂ ⊩σ′ σ≡σ′)
        ⊩t₁
        (⊩t ⊢Δ ⊩σ′ .proj₁)
        (⊩t ⊢Δ ⊩σ  .proj₂ ⊩σ′ σ≡σ′)
        ⊩u₁
        (⊩u ⊢Δ ⊩σ′ .proj₁)
        (⊩u ⊢Δ ⊩σ  .proj₂ ⊩σ′ σ≡σ′)
        (⊩Id′ ⊩A₁ ⊩t₁ ⊩u₁)
        PE.refl
        PE.refl
        PE.refl
        PE.refl
        (⊩Id′ (⊩Erased ⊩A₁) (⊩[] {⊩A = ⊩A₁} ⊩t₁) (⊩[] {⊩A = ⊩A₁} ⊩u₁))
        PE.refl
        PE.refl
        PE.refl
        PE.refl
        (⊩v ⊢Δ ⊩σ .proj₂ ⊩σ′ σ≡σ′) }}

opaque
  unfolding rflᵛ []-congᵛ

  -- Validity of the []-cong β rule.

  []-cong-βᵛ :
    {ok : []-cong-allowed} →
    let open E ok in
    {⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ}
    {⊩t : Γ ⊩ᵛ⟨ l ⟩ t ∷ A / ⊩Γ / ⊩A} →
    Γ ⊩ᵛ⟨ l ⟩ []-cong A t t rfl ≡ rfl ∷
      Id (Erased A) [ t ] [ t ] / ⊩Γ /
      Idᵛ (Erasedᵛ ⊩A) ([]ᵛ t ⊩t) ([]ᵛ t ⊩t)
  []-cong-βᵛ {t} {ok} {⊩A} {⊩t} ⊢Δ ⊩σ =
    ⊩Id≡∷
      ([]-congᵛ {t = t} {u = t} {ok = ok} {⊩A = ⊩A} {⊩t = ⊩t} {⊩u = ⊩t}
         rfl
         (rflᵛ {t = t} {⊩A = ⊩A} {⊩t = ⊩t})
         ⊢Δ ⊩σ .proj₁)
      (rflᵛ {t = [ t ]} {⊩A = Erasedᵛ ⊩A} {⊩t = []ᵛ {⊩A = ⊩A} t ⊩t}
         ⊢Δ ⊩σ .proj₁)
      _
    where
    open E ok

opaque
  unfolding Idᵛ ⊩Id

  -- Validity of equality preservation for []-cong.

  []-cong-congᵛ :
    {ok : []-cong-allowed} →
    let open E ok in
    {⊩A₁ : Γ ⊩ᵛ⟨ l ⟩ A₁ / ⊩Γ}
    {⊩t₁ : Γ ⊩ᵛ⟨ l ⟩ t₁ ∷ A₁ / ⊩Γ / ⊩A₁}
    {⊩u₁ : Γ ⊩ᵛ⟨ l ⟩ u₁ ∷ A₁ / ⊩Γ / ⊩A₁} →
    ∀ t₂ u₂ v₁ v₂ →
    (⊩A₂ : Γ ⊩ᵛ⟨ l ⟩ A₂ / ⊩Γ) →
    Γ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ / ⊩Γ / ⊩A₁ →
    Γ ⊩ᵛ⟨ l ⟩ t₂ ∷ A₂ / ⊩Γ / ⊩A₂ →
    Γ ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ A₁ / ⊩Γ / ⊩A₁ →
    Γ ⊩ᵛ⟨ l ⟩ u₂ ∷ A₂ / ⊩Γ / ⊩A₂ →
    Γ ⊩ᵛ⟨ l ⟩ u₁ ≡ u₂ ∷ A₁ / ⊩Γ / ⊩A₁ →
    Γ ⊩ᵛ⟨ l ⟩ v₁ ≡ v₂ ∷ Id A₁ t₁ u₁ / ⊩Γ / Idᵛ ⊩A₁ ⊩t₁ ⊩u₁ →
    Γ ⊩ᵛ⟨ l ⟩ []-cong A₁ t₁ u₁ v₁ ≡ []-cong A₂ t₂ u₂ v₂ ∷
      Id (Erased A₁) [ t₁ ] [ u₁ ] / ⊩Γ /
      Idᵛ (Erasedᵛ ⊩A₁) ([]ᵛ t₁ ⊩t₁) ([]ᵛ u₁ ⊩u₁)
  []-cong-congᵛ
    {A₁} {t₁} {u₁} {A₂} {ok} {⊩A₁} {⊩t₁} {⊩u₁}
    t₂ u₂ _ _ ⊩A₂ ⊩A₁≡A₂ ⊩t₂ ⊩t₁≡t₂ ⊩u₂ ⊩u₁≡u₂ ⊩v₁≡v₂ {σ} ⊢Δ ⊩σ =
    let ⊩A₁′ , _ = ⊩A₁ .unwrap ⊢Δ ⊩σ in
    case ⊩t₁ ⊢Δ ⊩σ .proj₁ of λ {
      ⊩t₁′ →
    case ⊩u₁ ⊢Δ ⊩σ .proj₁ of λ {
      ⊩u₁′ →
    irrelevanceEqTerm
      (⊩Id (⊩Erased ⊩A₁′) (⊩[] ⊩t₁′) (⊩[] ⊩u₁′))
      (Idᵛ {t = [ t₁ ]} {u = [ u₁ ]}
         (Erasedᵛ ⊩A₁) ([]ᵛ t₁ ⊩t₁) ([]ᵛ u₁ ⊩u₁)
         .unwrap ⊢Δ ⊩σ .proj₁) $
    []-cong-cong′
      _
      (⊩A₂ .unwrap ⊢Δ ⊩σ .proj₁)
      (⊩A₁≡A₂ ⊢Δ ⊩σ)
      ⊩t₁′
      (⊩t₂ ⊢Δ ⊩σ .proj₁)
      (⊩t₁≡t₂ ⊢Δ ⊩σ)
      ⊩u₁′
      (⊩u₂ ⊢Δ ⊩σ .proj₁)
      (⊩u₁≡u₂ ⊢Δ ⊩σ)
      (⊩Id′ ⊩A₁′ ⊩t₁′ ⊩u₁′)
      PE.refl
      PE.refl
      PE.refl
      PE.refl
      (⊩Id′ (⊩Erased ⊩A₁′) (⊩[] ⊩t₁′) (⊩[] ⊩u₁′))
      PE.refl
      PE.refl
      PE.refl
      PE.refl
      (⊩v₁≡v₂ ⊢Δ ⊩σ) }}
    where
    open E ok

------------------------------------------------------------------------
-- The K rule

opaque

  -- A variant of K-subst for _⊢_⇒*_∷_.

  K-subst* :
    Γ ⊢ A →
    Γ ⊢ t ∷ A →
    Γ ∙ Id A t t ⊢ B →
    Γ ⊢ u ∷ B [ rfl ]₀ →
    Γ ⊢ v₁ ⇒* v₂ ∷ Id A t t →
    (⊩Id : Γ ⊩⟨ l ⟩ Id A t t) →
    Γ ⊩⟨ l ⟩ v₂ ∷ Id A t t / ⊩Id →
    (∀ {v₁ v₂} →
     Γ ⊩⟨ l ⟩ v₁ ∷ Id A t t / ⊩Id →
     Γ ⊩⟨ l ⟩ v₂ ∷ Id A t t / ⊩Id →
     Γ ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ Id A t t / ⊩Id →
     Γ ⊢ B [ v₁ ]₀ ≡ B [ v₂ ]₀) →
    K-allowed →
    Γ ⊢ K p A t B u v₁ ⇒* K p A t B u v₂ ∷ B [ v₁ ]₀
  K-subst* ⊢A ⊢t ⊢B ⊢u v₁⇒*v₂ ⊩Id ⊩v₂ B≡B ok =
    case v₁⇒*v₂ of λ where
      (id ⊢v₁)         → id (Kⱼ ⊢t ⊢B ⊢u ⊢v₁ ok)
      (v₁⇒v₃ ⇨ v₃⇒*v₂) →
        case redSubst*Term v₃⇒*v₂ ⊩Id ⊩v₂ of λ {
          (⊩v₃ , _) →
        case redSubstTerm v₁⇒v₃ ⊩Id ⊩v₃ of λ {
          (⊩v₁ , ⊩v₁≡v₃) →
        K-subst ⊢A ⊢t ⊢B ⊢u v₁⇒v₃ ok ⇨
        conv* (K-subst* ⊢A ⊢t ⊢B ⊢u v₃⇒*v₂ ⊩Id ⊩v₂ B≡B ok)
          (sym (B≡B ⊩v₁ ⊩v₃ ⊩v₁≡v₃)) }}

private opaque
  unfolding ⊩Id

  -- Reducibility for K.

  ⊩K :
    {σ : Subst n m}
    {⊢Δ : ⊢ Δ}
    {⊩σ : Δ ⊩ˢ σ ∷ Γ / ⊩Γ / ⊢Δ} →
    K-allowed →
    (⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ)
    {⊩t : Γ ⊩ᵛ⟨ l ⟩ t ∷ A / ⊩Γ / ⊩A}
    (⊩B : Γ ∙ Id A t t ⊩ᵛ⟨ l ⟩ B / ⊩Γ ∙ Idᵛ′ ⊩A ⊩t ⊩t) →
    (⊩B[σ,rfl] : Δ ⊩⟨ l ⟩ B U.[ consSubst σ rfl ]) →
    Δ ⊩⟨ l ⟩ u ∷ B U.[ consSubst σ rfl ] / ⊩B[σ,rfl] →
    let ⊩A , _ = ⊩A .unwrap ⊢Δ ⊩σ
        ⊩t , _ = ⊩t         ⊢Δ ⊩σ
    in
    {⊩v : Δ ⊩⟨ l ⟩ v ∷ Id A t t U.[ σ ] / ⊩Id ⊩A ⊩t ⊩t} →
    Δ ⊩⟨ l ⟩
      K p (A U.[ σ ]) (t U.[ σ ]) (B U.[ liftSubst σ ]) u v ∷
      B U.[ consSubst σ v ] / ⊩B .unwrap ⊢Δ (⊩σ , ⊩v) .proj₁
  ⊩K
    {A} {t} {B} {u} {v} {σ} {⊢Δ} {⊩σ}
    ok ⊩A {⊩t} ⊩B ⊩B[σ,rfl] ⊩u {⊩v = ⊩v@(v′ , v⇒*v′ , _)} =
    let ⊩B′  , _ = ⊩B .unwrap {σ = consSubst _ _} _ (_ , ⊩v)
        ⊩B″  , _ = ⊩B .unwrap {σ = liftSubst _} _
                     (liftSubstS _ _ (Idᵛ′ {t = t} {u = t} ⊩A ⊩t ⊩t) ⊩σ)
        ⊩Id′ , _ = Idᵛ {t = t} {u = t} ⊩A ⊩t ⊩t .unwrap ⊢Δ ⊩σ
        ⊩A   , _ = ⊩A .unwrap ⊢Δ ⊩σ
        ⊩t   , _ = ⊩t ⊢Δ ⊩σ
        ⊩Id      = ⊩Id ⊩A ⊩t ⊩t
    in
    case PE.subst (_⊢_∷_ _ _) (PE.sym $ singleSubstComp _ _ B) $
         escapeTerm ⊩B[σ,rfl] ⊩u of λ {
      ⊢u →
    case escape ⊩A of λ {
      ⊢A →
    case escapeTerm ⊩A ⊩t of λ {
      ⊢t →
    case escape ⊩B″ of λ {
      ⊢B →
    case ⊩Id∷-view-inhabited ⊩v of λ where
      (ne v′-n v′~v′) →
        case ⊢u-redₜ v⇒*v′ of λ {
          ⊢v′ →
        case v′ , idRedTerm:*: ⊢v′ , ne v′-n , v′~v′ of λ {
          ⊩v′ →
        case redSubst*Term (redₜ v⇒*v′) ⊩Id ⊩v′ .proj₂ of λ {
          ⊩v≡v′ →
        case PE.subst (_⊢_≡_ _ _)
               (singleSubstComp _ _ B)
               (sym (⊩ᵛ→≡→⊢[⇑][]₀≡[⇑][]₀ ⊩B ⊩v ⊩v′ ⊩v≡v′)) of λ {
          ⊢B[⇑σ][v′]₀≡B[σ,v] →
        redSubst*Term
          {t = K _ (A U.[ σ ]) (t U.[ σ ]) (B U.[ liftSubst σ ]) u v}
          {u = K _ (A U.[ σ ]) (t U.[ σ ]) (B U.[ liftSubst σ ]) u v′}
          (PE.subst (_⊢_⇒*_∷_ _ _ _)
             (singleSubstComp _ _ B)
             (K-subst* ⊢A ⊢t ⊢B ⊢u (redₜ v⇒*v′) ⊩Id ⊩v′
                (⊩ᵛ→≡→⊢[⇑][]₀≡[⇑][]₀ ⊩B) ok))
          ⊩B′
          (neuTerm ⊩B′ (Kₙ v′-n)
             (conv (Kⱼ ⊢t ⊢B ⊢u ⊢v′ ok) ⊢B[⇑σ][v′]₀≡B[σ,v]) $
           flip ~-conv ⊢B[⇑σ][v′]₀≡B[σ,v] $
           ~-K
             (escapeEq ⊩A (reflEq ⊩A))
             ⊢t
             (escapeTermEq ⊩A (reflEqTerm ⊩A ⊩t))
             (escapeEq ⊩B″ (reflEq ⊩B″))
             (PE.subst (_ ⊢ _ ≅ _ ∷_)
                (PE.sym $ singleSubstComp _ _ B)
                (escapeTermEq ⊩B[σ,rfl] (reflEqTerm ⊩B[σ,rfl] ⊩u)))
             v′~v′
             ok)
          .proj₁ }}}}
      (rflᵣ ⊩t≡t) →
        case irrelevanceTerm ⊩Id′ ⊩Id (rflᵛ _ ⊩σ .proj₁) of λ {
          ⊩rfl →
        case redSubst*Term (redₜ v⇒*v′) ⊩Id ⊩rfl .proj₂ of λ {
          ⊩v≡rfl →
        case ⊩ᵛ→≡→⊢[⇑][]₀≡[⇑][]₀ ⊩B ⊩rfl ⊩v
               (symEqTerm ⊩Id ⊩v≡rfl) of λ {
          B[⇑σ][rfl]₀≡B[⇑σ][v]₀ →
        redSubst*Term
          {t = K _ (A U.[ σ ]) (t U.[ σ ]) (B U.[ liftSubst σ ]) u v}
          {u = u}
          (PE.subst (_⊢_⇒*_∷_ _ _ _)
             (singleSubstComp _ _ B)
             (K-subst* ⊢A ⊢t ⊢B ⊢u (redₜ v⇒*v′) ⊩Id ⊩rfl
                (⊩ᵛ→≡→⊢[⇑][]₀≡[⇑][]₀ ⊩B) ok ⇨∷*
              (conv (K-β ⊢t ⊢B ⊢u ok) B[⇑σ][rfl]₀≡B[⇑σ][v]₀ ⇨
               id (conv ⊢u B[⇑σ][rfl]₀≡B[⇑σ][v]₀))))
          ⊩B′
          (convTerm₂ ⊩B′ ⊩B[σ,rfl]
             (⊩B .unwrap _ _ .proj₂
                (_ , ⊩rfl) (reflSubst _ _ _ , ⊩v≡rfl))
             ⊩u)
          .proj₁ }}}}}}}

private opaque
  unfolding ⊩Id

  -- An equality lemma for K.

  ⊩K≡K :
    {⊩A₁ : Γ ⊩⟨ l ⟩ A₁}
    {⊩A₂ : Γ ⊩⟨ l ⟩ A₂}
    {⊩t₁ : Γ ⊩⟨ l ⟩ t₁ ∷ A₁ / ⊩A₁}
    {⊩t₂ : Γ ⊩⟨ l ⟩ t₂ ∷ A₂ / ⊩A₂} →
    let ⊩Id₁ = ⊩Id ⊩A₁ ⊩t₁ ⊩t₁
        ⊩Id₂ = ⊩Id ⊩A₂ ⊩t₂ ⊩t₂
    in
    K-allowed →
    Γ ⊩⟨ l ⟩ A₁ ≡ A₂ / ⊩A₁ →
    Γ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ A₁ / ⊩A₁ →
    (⊩B₁ : Γ ∙ Id A₁ t₁ t₁ ⊩⟨ l ⟩ B₁) →
    Γ ∙ Id A₂ t₂ t₂ ⊩⟨ l ⟩ B₂ →
    (⊩B₁[rfl] : Γ ⊩⟨ l ⟩ B₁ [ rfl ]₀)
    (⊩B₂[rfl] : Γ ⊩⟨ l ⟩ B₂ [ rfl ]₀)
    (⊩B₁[v₁] : Γ ⊩⟨ l ⟩ B₁ [ v₁ ]₀) →
    Γ ⊩⟨ l ⟩ B₂ [ v₂ ]₀ →
    (∀ {v₂} →
     Γ ⊩⟨ l ⟩ v₂ ∷ Id A₁ t₁ t₁ / ⊩Id₁ →
     Γ ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ Id A₁ t₁ t₁ / ⊩Id₁ →
     Γ ⊩⟨ l ⟩ B₁ [ v₁ ]₀ ≡ B₁ [ v₂ ]₀ / ⊩B₁[v₁]) →
    (∀ {v₁ v₂} →
     Γ ⊩⟨ l ⟩ v₁ ∷ Id A₁ t₁ t₁ / ⊩Id₁ →
     Γ ⊩⟨ l ⟩ v₂ ∷ Id A₁ t₁ t₁ / ⊩Id₁ →
     Γ ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ Id A₁ t₁ t₁ / ⊩Id₁ →
     Γ ⊢ B₁ [ v₁ ]₀ ≡ B₁ [ v₂ ]₀) →
    (∀ {v₁ v₂} →
     Γ ⊩⟨ l ⟩ v₁ ∷ Id A₂ t₂ t₂ / ⊩Id₂ →
     Γ ⊩⟨ l ⟩ v₂ ∷ Id A₂ t₂ t₂ / ⊩Id₂ →
     Γ ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ Id A₂ t₂ t₂ / ⊩Id₂ →
     Γ ⊢ B₂ [ v₁ ]₀ ≡ B₂ [ v₂ ]₀) →
    Γ ∙ Id A₁ t₁ t₁ ⊩⟨ l ⟩ B₁ ≡ B₂ / ⊩B₁ →
    Γ ⊩⟨ l ⟩ B₁ [ rfl ]₀ ≡ B₂ [ rfl ]₀ / ⊩B₁[rfl] →
    (∀ {v₂} →
     Γ ⊩⟨ l ⟩ v₂ ∷ Id A₂ t₂ t₂ / ⊩Id₂ →
     Γ ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ Id A₁ t₁ t₁ / ⊩Id₁ →
     Γ ⊩⟨ l ⟩ B₁ [ v₁ ]₀ ≡ B₂ [ v₂ ]₀ / ⊩B₁[v₁]) →
    (∀ {v₁ v₂} →
     Γ ⊩⟨ l ⟩ v₁ ∷ Id A₁ t₁ t₁ / ⊩Id₁ →
     Γ ⊩⟨ l ⟩ v₂ ∷ Id A₂ t₂ t₂ / ⊩Id₂ →
     Γ ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ Id A₁ t₁ t₁ / ⊩Id₁ →
     Γ ⊢ B₁ [ v₁ ]₀ ≡ B₂ [ v₂ ]₀) →
    Γ ⊩⟨ l ⟩ u₁ ∷ B₁ [ rfl ]₀ / ⊩B₁[rfl] →
    Γ ⊩⟨ l ⟩ u₂ ∷ B₂ [ rfl ]₀ / ⊩B₂[rfl] →
    Γ ⊩⟨ l ⟩ u₁ ≡ u₂ ∷ B₁ [ rfl ]₀ / ⊩B₁[rfl] →
    Γ ⊩⟨ l ⟩ v₁ ∷ Id A₁ t₁ t₁ / ⊩Id₁ →
    Γ ⊩⟨ l ⟩ v₂ ∷ Id A₂ t₂ t₂ / ⊩Id₂ →
    Γ ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ Id A₁ t₁ t₁ / ⊩Id₁ →
    Γ ⊩⟨ l ⟩ K p A₁ t₁ B₁ u₁ v₁ ≡ K p A₂ t₂ B₂ u₂ v₂ ∷ B₁ [ v₁ ]₀ /
      ⊩B₁[v₁]
  ⊩K≡K
    {A₁} {A₂} {t₁} {t₂} {B₁} {B₂} {v₁} {v₂} {u₁} {u₂}
    {⊩A₁} {⊩A₂} {⊩t₁} {⊩t₂} ok ⊩A₁≡A₂ ⊩t₁≡t₂
    ⊩B₁ ⊩B₂ ⊩B₁[rfl] ⊩B₂[rfl] ⊩B₁[v₁] ⊩B₂[v₂]
    ⊩B₁[v₁]≡B₁[] ⊢B₁[]≡B₁[] ⊢B₂[]≡B₂[]
    ⊩B₁≡B₂ ⊩B₁[rfl]≡B₂[rfl] ⊩B₁[v₁]≡B₂[] ⊢B₁[]≡B₂[]
    ⊩u₁ ⊩u₂ ⊩u₁≡u₂ ⊩v₁ ⊩v₂
    ⊩v₁≡v₂@(v₁′ , v₂′ , v₁⇒*v₁′ , v₂⇒*v₂′ , _) =
    let ⊩Id₁′ = ⊩Id′ ⊩A₁ ⊩t₁ ⊩t₁
        ⊩Id₁  = Idᵣ ⊩Id₁′
        ⊩Id₂  = ⊩Id ⊩A₂ ⊩t₂ ⊩t₂
    in
    case escape ⊩A₁ of λ {
      ⊢A₁ →
    case escape ⊩A₂ of λ {
      ⊢A₂ →
    case escapeEq ⊩A₁ ⊩A₁≡A₂ of λ {
      A₁≅A₂ →
    case escapeTerm ⊩A₁ ⊩t₁ of λ {
      ⊢t₁ →
    case escapeTerm ⊩A₂ ⊩t₂ of λ {
      ⊢t₂ →
    case escapeTermEq ⊩A₁ ⊩t₁≡t₂ of λ {
      t₁≅t₂ →
    case escape ⊩B₁ of λ {
      ⊢B₁ →
    case escape ⊩B₂ of λ {
      ⊢B₂ →
    case escapeTerm ⊩B₁[rfl] ⊩u₁ of λ {
      ⊢u₁ →
    case escapeTerm ⊩B₂[rfl] ⊩u₂ of λ {
      ⊢u₂ →
    case ⊩Id≡Id ⊢t₂ ⊢t₂ ⊩A₁≡A₂ ⊩t₁≡t₂ ⊩t₁≡t₂ of λ {
      ⊩Id₁≡Id₂ →
    case ≅-eq (escapeEq ⊩Id₁ ⊩Id₁≡Id₂) of λ {
      ⊢Id₁≡Id₂ →
    case convRed:*: v₂⇒*v₂′ ⊢Id₁≡Id₂ of λ {
      v₂⇒*v₂′ →
    case ⊢u-redₜ v₁⇒*v₁′ of λ {
      ⊢v₁′ →
    case ⊢u-redₜ v₂⇒*v₂′ of λ {
      ⊢v₂′ →
    case ⊩Id≡∷-view-inhabited ⊩Id₁′ ⊩v₁≡v₂ of λ where
      (ne v₁′-n v₂′-n v₁′~v₂′) →
        let ⊩v₁′≡v₂′ =
                v₁′ , v₂′
              , idRedTerm:*: ⊢v₁′
              , convRed:*: (idRedTerm:*: ⊢v₂′) (sym ⊢Id₁≡Id₂)
              , ne v₁′-n , ne v₂′-n
              , v₁′~v₂′
            ⊩v₁′ , ⊩v₂′ , _ = ⊩Id≡∷⁻¹ ⊩Id₁′ ⊩v₁′≡v₂′
        in
        case convTerm₁ ⊩Id₁ ⊩Id₂ ⊩Id₁≡Id₂ ⊩v₂′ of λ {
          ⊩v₂′ →
        case redSubst*Term (redₜ v₁⇒*v₁′) ⊩Id₁ ⊩v₁′ .proj₂ of λ {
          ⊩v₁≡v₁′ →
        case redSubst*Term (redₜ v₂⇒*v₂′) ⊩Id₂ ⊩v₂′ .proj₂ of λ {
          ⊩v₂≡v₂′ →
        case ⊢B₁[]≡B₁[] ⊩v₁′ ⊩v₁ (symEqTerm ⊩Id₁ ⊩v₁≡v₁′) of λ {
          ⊢B₁[v₁′]≡B₁[v₁] →
        case ⊢B₂[]≡B₂[] ⊩v₂′ ⊩v₂ (symEqTerm ⊩Id₂ ⊩v₂≡v₂′) of λ {
          ⊢B₂[v₂′]≡B₂[v₂] →
        transEqTerm ⊩B₁[v₁]
          (redSubst*Term
             {A = B₁ [ v₁ ]₀}
             {t = K _ A₁ t₁ B₁ u₁ v₁}
             {u = K _ A₁ t₁ B₁ u₁ v₁′}
             (K-subst* ⊢A₁ ⊢t₁ ⊢B₁ ⊢u₁ (redₜ v₁⇒*v₁′) ⊩Id₁ ⊩v₁′
                ⊢B₁[]≡B₁[] ok)
             ⊩B₁[v₁]
             (neuTerm
                ⊩B₁[v₁]
                (Kₙ v₁′-n)
                (conv (Kⱼ ⊢t₁ ⊢B₁ ⊢u₁ ⊢v₁′ ok) ⊢B₁[v₁′]≡B₁[v₁])
                (~-conv
                   (~-K
                      (escapeEq ⊩A₁ (reflEq ⊩A₁))
                      ⊢t₁
                      (escapeTermEq ⊩A₁ (reflEqTerm ⊩A₁ ⊩t₁))
                      (escapeEq ⊩B₁ (reflEq ⊩B₁))
                      (escapeTermEq ⊩B₁[rfl] (reflEqTerm ⊩B₁[rfl] ⊩u₁))
                      (⊩v₁′ .proj₂ .proj₂ .proj₂)
                      ok)
                   ⊢B₁[v₁′]≡B₁[v₁]))
             .proj₂) $
        transEqTerm ⊩B₁[v₁]
          (neuEqTerm ⊩B₁[v₁] (Kₙ v₁′-n) (Kₙ v₂′-n)
             (conv (Kⱼ ⊢t₁ ⊢B₁ ⊢u₁ ⊢v₁′ ok) ⊢B₁[v₁′]≡B₁[v₁])
             (conv (Kⱼ ⊢t₂ ⊢B₂ ⊢u₂ ⊢v₂′ ok)
                (trans (sym (⊢B₁[]≡B₂[] ⊩v₁′ ⊩v₂′ ⊩v₁′≡v₂′))
                   ⊢B₁[v₁′]≡B₁[v₁]))
             (~-conv
                (~-K A₁≅A₂ ⊢t₁ t₁≅t₂
                   (escapeEq ⊩B₁ ⊩B₁≡B₂)
                   (escapeTermEq ⊩B₁[rfl] ⊩u₁≡u₂)
                   v₁′~v₂′ ok)
                ⊢B₁[v₁′]≡B₁[v₁])) $
        convEqTerm₂ ⊩B₁[v₁] ⊩B₂[v₂] (⊩B₁[v₁]≡B₂[] ⊩v₂ ⊩v₁≡v₂) $
        symEqTerm ⊩B₂[v₂] $
        redSubst*Term
          {A = B₂ [ v₂ ]₀}
          {t = K _ A₂ t₂ B₂ u₂ v₂}
          {u = K _ A₂ t₂ B₂ u₂ v₂′}
          (K-subst* ⊢A₂ ⊢t₂ ⊢B₂ ⊢u₂ (redₜ v₂⇒*v₂′) ⊩Id₂ ⊩v₂′
             ⊢B₂[]≡B₂[] ok)
          ⊩B₂[v₂]
          (neuTerm
             ⊩B₂[v₂]
             (Kₙ v₂′-n)
             (conv (Kⱼ ⊢t₂ ⊢B₂ ⊢u₂ ⊢v₂′ ok) ⊢B₂[v₂′]≡B₂[v₂])
             (~-conv
                (~-K
                   (escapeEq ⊩A₂ (reflEq ⊩A₂))
                   ⊢t₂
                   (escapeTermEq ⊩A₂ (reflEqTerm ⊩A₂ ⊩t₂))
                   (escapeEq ⊩B₂ (reflEq ⊩B₂))
                   (escapeTermEq ⊩B₂[rfl] (reflEqTerm ⊩B₂[rfl] ⊩u₂))
                   (~-conv (~-trans (~-sym v₁′~v₂′) v₁′~v₂′) ⊢Id₁≡Id₂)
                   ok)
                ⊢B₂[v₂′]≡B₂[v₂]))
          .proj₂ }}}}}
      (rfl₌ lhs≡rhs) →
        case redSubst*Term (redₜ v₁⇒*v₁′) ⊩Id₁ ⊩rfl .proj₂ of λ {
          ⊩v₁≡rfl →
        case redSubst*Term (redₜ v₂⇒*v₂′) ⊩Id₂ ⊩rfl .proj₂ of λ {
          ⊩v₂≡rfl →
        case symEq ⊩B₁[v₁] ⊩B₁[rfl] $
             ⊩B₁[v₁]≡B₁[] ⊩rfl ⊩v₁≡rfl of λ {
          ⊩B₁[rfl]≡B₁[v₁] →
        case ≅-eq (escapeEq ⊩B₁[rfl] ⊩B₁[rfl]≡B₁[v₁]) of λ {
          ⊢B₁[rfl]≡B₁[v₁] →
        convEqTerm₁ ⊩B₁[rfl] ⊩B₁[v₁] ⊩B₁[rfl]≡B₁[v₁] $
        transEqTerm ⊩B₁[rfl]
          (redSubst*Term
             {A = B₁ [ rfl ]₀}
             {t = K _ A₁ t₁ B₁ u₁ v₁}
             {u = u₁}
             (conv*
                (K-subst* ⊢A₁ ⊢t₁ ⊢B₁ ⊢u₁ (redₜ v₁⇒*v₁′) ⊩Id₁ ⊩rfl
                   ⊢B₁[]≡B₁[] ok)
                (sym ⊢B₁[rfl]≡B₁[v₁]) ⇨∷*
              (K-β ⊢t₁ ⊢B₁ ⊢u₁ ok ⇨
               id ⊢u₁))
             ⊩B₁[rfl]
             ⊩u₁
             .proj₂) $
        transEqTerm ⊩B₁[rfl] ⊩u₁≡u₂ $
        convEqTerm₂ ⊩B₁[rfl] ⊩B₂[rfl] ⊩B₁[rfl]≡B₂[rfl] $
        symEqTerm ⊩B₂[rfl] $
        redSubst*Term
          {A = B₂ [ rfl ]₀}
          {t = K _ A₂ t₂ B₂ u₂ v₂}
          {u = u₂}
          (conv*
             (K-subst* ⊢A₂ ⊢t₂ ⊢B₂ ⊢u₂ (redₜ v₂⇒*v₂′) ⊩Id₂ ⊩rfl
                ⊢B₂[]≡B₂[] ok)
             (⊢B₂[]≡B₂[] ⊩v₂ ⊩rfl ⊩v₂≡rfl) ⇨∷*
           (K-β ⊢t₂ ⊢B₂ ⊢u₂ ok ⇨
            id ⊢u₂))
          ⊩B₂[rfl]
          ⊩u₂
          .proj₂ }}}}}}}}}}}}}}}}}}}

opaque
  unfolding Idᵛ

  -- Validity for K.

  Kᵛ :
    ∀ u →
    K-allowed →
    {⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ}
    {⊩t : Γ ⊩ᵛ⟨ l ⟩ t ∷ A / ⊩Γ / ⊩A} →
    Γ ∙ Id A t t ⊩ᵛ⟨ l ⟩ B / ⊩Γ ∙ Idᵛ ⊩A ⊩t ⊩t →
    (⊩B[rfl] : Γ ⊩ᵛ⟨ l ⟩ B [ rfl ]₀ / ⊩Γ) →
    Γ ⊩ᵛ⟨ l ⟩ u ∷ B [ rfl ]₀ / ⊩Γ / ⊩B[rfl] →
    Γ ⊩ᵛ⟨ l ⟩ v ∷ Id A t t / ⊩Γ / Idᵛ ⊩A ⊩t ⊩t →
    (⊩B[v] : Γ ⊩ᵛ⟨ l ⟩ B [ v ]₀ / ⊩Γ) →
    Γ ⊩ᵛ⟨ l ⟩ K p A t B u v ∷ B [ v ]₀ / ⊩Γ / ⊩B[v]
  Kᵛ {A} {t} {B} {v} u ok {⊩A} {⊩t} ⊩B ⊩B[rfl] ⊩u ⊩v ⊩B[v] {σ} ⊢Δ ⊩σ =
    let ⊩B[v][σ] , _ = ⊩B[v] .unwrap _ ⊩σ in
    case ⊩B .unwrap _
           (_ , rflᵛ {t = t} {⊩A = ⊩A} {⊩t = ⊩t} _ ⊩σ .proj₁) of λ {
      (⊩B[σ,rfl] , _) →
      irrelevanceTerm′
        (substConsId B)
        (⊩B .unwrap _ (_ , ⊩v ⊢Δ ⊩σ .proj₁) .proj₁)
        ⊩B[v][σ]
        (⊩K ok ⊩A ⊩B ⊩B[σ,rfl]
           (irrelevanceTerm′
              (PE.sym (substConsId B))
              (⊩B[rfl] .unwrap _ ⊩σ .proj₁)
              ⊩B[σ,rfl]
              (⊩u _ ⊩σ .proj₁)))
    , λ {σ′} ⊩σ′ ⊩σ≡σ′ →
        let ⊩Id             = Idᵛ {t = t} {u = t} ⊩A ⊩t ⊩t
            ⊩B[rfl][σ]  , _ = ⊩B[rfl] .unwrap _ ⊩σ
            ⊩B[rfl][σ′] , _ = ⊩B[rfl] .unwrap _ ⊩σ′
            ⊩v[σ]       , _ = ⊩v _ ⊩σ
        in
        case irrelevance′ (PE.sym (singleSubstComp _ _ B))
               ⊩B[σ,rfl] of λ {
          ⊩B[⇑σ][rfl] →
        case irrelevance′ (PE.sym (singleSubstComp _ _ B)) $
             ⊩B .unwrap _
               (_ , rflᵛ {t = t} {⊩A = ⊩A} {⊩t = ⊩t} _ ⊩σ′ .proj₁)
               .proj₁ of λ {
          ⊩B[⇑σ′][rfl] →
        case irrelevance′ (PE.sym (singleSubstComp _ _ B)) $
             ⊩B .unwrap _ (_ , ⊩v _ ⊩σ .proj₁) .proj₁ of λ {
          ⊩B[⇑σ][v[σ]] →
        case (λ {σ} → rflᵛ {t = t} {⊩A = ⊩A} {⊩t = ⊩t} {σ = σ}) of λ {
          ⊩rfl →
        irrelevanceEqTerm′
          (PE.sym (singleSubstLift B _)) ⊩B[⇑σ][v[σ]] ⊩B[v][σ] $
        ⊩K≡K
          {A₁ = A U.[ σ ]}
          {A₂ = A U.[ σ′ ]}
          {t₁ = t U.[ σ ]}
          {t₂ = t U.[ σ′ ]}
          {B₁ = B U.[ liftSubst σ ]}
          {B₂ = B U.[ liftSubst σ′ ]}
          {v₁ = v U.[ σ ]}
          {v₂ = v U.[ σ′ ]}
          {u₁ = u U.[ σ ]}
          {u₂ = u U.[ σ′ ]}
          ok
          (⊩A .unwrap _ _ .proj₂ ⊩σ′ ⊩σ≡σ′)
          (⊩t _ _ .proj₂ ⊩σ′ ⊩σ≡σ′)
          (⊩B .unwrap _ (liftSubstS _ _ ⊩Id ⊩σ)  .proj₁)
          (⊩B .unwrap _ (liftSubstS _ _ ⊩Id ⊩σ′) .proj₁)
          ⊩B[⇑σ][rfl]
          ⊩B[⇑σ′][rfl]
          ⊩B[⇑σ][v[σ]]
          (irrelevance′ (PE.sym (singleSubstComp _ _ B)) $
           ⊩B .unwrap _ (_ , ⊩v _ ⊩σ′ .proj₁) .proj₁)
          (⊩ᵛ→≡→≡→⊩[⇑][]₀≡[⇑][]₀
             ⊩B ⊩B[⇑σ][v[σ]] (reflSubst _ _ ⊩σ) ⊩v[σ])
          (⊩ᵛ→≡→⊢[⇑][]₀≡[⇑][]₀ ⊩B)
          (⊩ᵛ→≡→⊢[⇑][]₀≡[⇑][]₀ ⊩B)
          (⊩ᵛ→≡→⊩[⇑]≡[⇑] ⊩B ⊩σ′ ⊩σ≡σ′)
          (⊩ᵛ→≡→≡→⊩[⇑][]₀≡[⇑][]₀
             ⊩B ⊩B[⇑σ][rfl] ⊩σ≡σ′
             (⊩rfl _ ⊩σ  .proj₁)
             (⊩rfl _ ⊩σ′ .proj₁)
             (⊩rfl _ _   .proj₂ ⊩σ′ ⊩σ≡σ′))
          (⊩ᵛ→≡→≡→⊩[⇑][]₀≡[⇑][]₀ ⊩B ⊩B[⇑σ][v[σ]] ⊩σ≡σ′ ⊩v[σ])
          (⊩ᵛ→≡→≡→⊢[⇑][]₀≡[⇑][]₀ ⊩B ⊩σ≡σ′)
          (irrelevanceTerm′
             (singleSubstLift B _) ⊩B[rfl][σ] ⊩B[⇑σ][rfl]
             (⊩u _ ⊩σ .proj₁))
          (irrelevanceTerm′
             (singleSubstLift B _) ⊩B[rfl][σ′] ⊩B[⇑σ′][rfl]
             (⊩u _ ⊩σ′ .proj₁))
          (irrelevanceEqTerm′
             (singleSubstLift B _) ⊩B[rfl][σ] ⊩B[⇑σ][rfl]
             (⊩u _ _ .proj₂ ⊩σ′ ⊩σ≡σ′))
          ⊩v[σ]
          (⊩v _ ⊩σ′ .proj₁)
          (⊩v _ _   .proj₂ ⊩σ′ ⊩σ≡σ′) }}}}}

opaque

  -- Validity of the K β rule.

  K-βᵛ :
    ∀ u →
    K-allowed →
    {⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ}
    {⊩t : Γ ⊩ᵛ⟨ l ⟩ t ∷ A / ⊩Γ / ⊩A} →
    Γ ∙ Id A t t ⊩ᵛ⟨ l ⟩ B / ⊩Γ ∙ Idᵛ ⊩A ⊩t ⊩t →
    (⊩B[rfl] : Γ ⊩ᵛ⟨ l ⟩ B [ rfl ]₀ / ⊩Γ) →
    Γ ⊩ᵛ⟨ l ⟩ u ∷ B [ rfl ]₀ / ⊩Γ / ⊩B[rfl] →
    Γ ⊩ᵛ⟨ l ⟩ K p A t B u rfl ≡ u ∷ B [ rfl ]₀ / ⊩Γ / ⊩B[rfl]
  K-βᵛ {B} _ ok {⊩A} {⊩t} ⊩B ⊩B[rfl] ⊩u _ ⊩σ =
    let ⊩B[rfl][σ] = ⊩B[rfl] .unwrap _ ⊩σ .proj₁ in
    case ⊩u _ ⊩σ .proj₁ of λ {
      ⊩u[σ] →
    redSubstTerm
      (PE.subst (_ ⊢ K _ _ _ (B U.[ _ ]) _ _ ⇒ _ ∷_)
         (PE.sym (singleSubstLift B _))
         (K-β
            (escapeTerm (⊩A .unwrap _ ⊩σ .proj₁) (⊩t _ ⊩σ .proj₁))
            (escape
               (⊩B .unwrap _ (liftSubstS _ _ (Idᵛ ⊩A ⊩t ⊩t) ⊩σ) .proj₁))
            (PE.subst (_ ⊢ _ ∷_) (singleSubstLift B _)
               (escapeTerm ⊩B[rfl][σ] ⊩u[σ]))
            ok))
      ⊩B[rfl][σ]
      ⊩u[σ]
      .proj₂ }

opaque
  unfolding Idᵛ

  -- Validity of equality preservation for K.

  K-congᵛ :
    {⊩A₁ : Γ ⊩ᵛ⟨ l ⟩ A₁ / ⊩Γ}
    {⊩A₂ : Γ ⊩ᵛ⟨ l ⟩ A₂ / ⊩Γ}
    {⊩t₁ : Γ ⊩ᵛ⟨ l ⟩ t₁ ∷ A₁ / ⊩Γ / ⊩A₁} →
    {⊩t₂ : Γ ⊩ᵛ⟨ l ⟩ t₂ ∷ A₂ / ⊩Γ / ⊩A₂} →
    let ⊩Id₁ = Idᵛ ⊩A₁ ⊩t₁ ⊩t₁
        ⊩Id₂ = Idᵛ ⊩A₂ ⊩t₂ ⊩t₂
    in
    K-allowed →
    ∀ u₁ u₂ v₂ →
    Γ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ / ⊩Γ / ⊩A₁ →
    Γ ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ A₁ / ⊩Γ / ⊩A₁ →
    (⊩B₁ : Γ ∙ Id A₁ t₁ t₁ ⊩ᵛ⟨ l ⟩ B₁ / ⊩Γ ∙ ⊩Id₁) →
    Γ ∙ Id A₂ t₂ t₂ ⊩ᵛ⟨ l ⟩ B₂ / ⊩Γ ∙ ⊩Id₂ →
    Γ ∙ Id A₁ t₁ t₁ ⊩ᵛ⟨ l ⟩ B₁ ≡ B₂ / ⊩Γ ∙ ⊩Id₁ / ⊩B₁ →
    (⊩B₁[rfl] : Γ ⊩ᵛ⟨ l ⟩ B₁ [ rfl ]₀ / ⊩Γ)
    (⊩B₂[rfl] : Γ ⊩ᵛ⟨ l ⟩ B₂ [ rfl ]₀ / ⊩Γ) →
    Γ ⊩ᵛ⟨ l ⟩ u₁ ∷ B₁ [ rfl ]₀ / ⊩Γ / ⊩B₁[rfl] →
    Γ ⊩ᵛ⟨ l ⟩ u₂ ∷ B₂ [ rfl ]₀ / ⊩Γ / ⊩B₂[rfl] →
    Γ ⊩ᵛ⟨ l ⟩ u₁ ≡ u₂ ∷ B₁ [ rfl ]₀ / ⊩Γ / ⊩B₁[rfl] →
    Γ ⊩ᵛ⟨ l ⟩ v₁ ∷ Id A₁ t₁ t₁ / ⊩Γ / ⊩Id₁ →
    Γ ⊩ᵛ⟨ l ⟩ v₂ ∷ Id A₂ t₂ t₂ / ⊩Γ / ⊩Id₂ →
    Γ ⊩ᵛ⟨ l ⟩ v₁ ≡ v₂ ∷ Id A₁ t₁ t₁ / ⊩Γ / ⊩Id₁ →
    (⊩B₁[v₁] : Γ ⊩ᵛ⟨ l ⟩ B₁ [ v₁ ]₀ / ⊩Γ) →
    Γ ⊩ᵛ⟨ l ⟩ K p A₁ t₁ B₁ u₁ v₁ ≡ K p A₂ t₂ B₂ u₂ v₂ ∷ B₁ [ v₁ ]₀ /
      ⊩Γ / ⊩B₁[v₁]
  K-congᵛ
    {A₁} {A₂} {t₁} {t₂} {B₁} {B₂} {v₁} {⊩A₁} {⊩A₂} {⊩t₁} {⊩t₂}
    ok u₁ u₂ v₂
    ⊩A₁≡A₂ ⊩t₁≡t₂ ⊩B₁ ⊩B₂ ⊩B₁≡B₂ ⊩B₁[rfl] ⊩B₂[rfl]
    ⊩u₁ ⊩u₂ ⊩u₁≡u₂ ⊩v₁ ⊩v₂ ⊩v₁≡v₂ ⊩B₁[v₁]
    {σ} _ ⊩σ =
    let ⊩B₁[v₁][σ]  , _ = ⊩B₁[v₁]  .unwrap _ ⊩σ
        ⊩B₁[rfl][σ] , _ = ⊩B₁[rfl] .unwrap _ ⊩σ
        ⊩B₂[rfl][σ] , _ = ⊩B₂[rfl] .unwrap _ ⊩σ
    in
    case liftSubstS _ _ (Idᵛ {t = t₁} {u = t₁} ⊩A₁ ⊩t₁ ⊩t₁) ⊩σ of λ {
      ⊩liftSubst-σ₁ →
    case liftSubstS _ _ (Idᵛ {t = t₂} {u = t₂} ⊩A₂ ⊩t₂ ⊩t₂) ⊩σ of λ {
      ⊩liftSubst-σ₂ →
    case irrelevance′ (singleSubstLift B₁ _) ⊩B₁[v₁][σ] of λ {
      ⊩B₁[⇑σ][v₁[σ]] →
    case irrelevance′ (PE.sym (singleSubstComp _ _ B₂))
           (⊩B₂ .unwrap _ (⊩σ , ⊩v₂ _ ⊩σ .proj₁) .proj₁) of λ {
      ⊩B₂[⇑σ][v₂[σ]] →
    case irrelevance′ (singleSubstLift B₁ _) ⊩B₁[rfl][σ] of λ {
      ⊩B₁[⇑σ][rfl] →
    case irrelevance′ (singleSubstLift B₂ _) ⊩B₂[rfl][σ] of λ {
      ⊩B₂[⇑σ][rfl] →
    case escapeTerm (⊩A₂ .unwrap _ ⊩σ .proj₁) (⊩t₂ _ ⊩σ .proj₁) of λ {
      ⊢t₂[σ] →
    case ⊩Id≡Id ⊢t₂[σ] ⊢t₂[σ]
           (⊩A₁≡A₂ _ ⊩σ) (⊩t₁≡t₂ _ ⊩σ) (⊩t₁≡t₂ _ ⊩σ) of λ {
      ⊩Id₁≡Id₂ →
    irrelevanceEqTerm′
      (PE.sym (singleSubstLift B₁ _)) ⊩B₁[⇑σ][v₁[σ]] ⊩B₁[v₁][σ] $
    ⊩K≡K
      {A₁ = A₁ U.[ σ ]}
      {A₂ = A₂ U.[ σ ]}
      {t₁ = t₁ U.[ σ ]}
      {t₂ = t₂ U.[ σ ]}
      {B₁ = B₁ U.[ liftSubst σ ]}
      {B₂ = B₂ U.[ liftSubst σ ]}
      {v₁ = v₁ U.[ σ ]}
      {v₂ = v₂ U.[ σ ]}
      {u₁ = u₁ U.[ σ ]}
      {u₂ = u₂ U.[ σ ]}
      ok
      (⊩A₁≡A₂ _ ⊩σ)
      (⊩t₁≡t₂ _ ⊩σ)
      (⊩B₁ .unwrap _ ⊩liftSubst-σ₁ .proj₁)
      (⊩B₂ .unwrap _ ⊩liftSubst-σ₂ .proj₁)
      ⊩B₁[⇑σ][rfl]
      ⊩B₂[⇑σ][rfl]
      ⊩B₁[⇑σ][v₁[σ]]
      ⊩B₂[⇑σ][v₂[σ]]
      (⊩ᵛ→≡→≡→⊩[⇑][]₀≡[⇑][]₀
         ⊩B₁ ⊩B₁[⇑σ][v₁[σ]] (reflSubst _ _ ⊩σ) (⊩v₁ _ ⊩σ .proj₁))
      (⊩ᵛ→≡→⊢[⇑][]₀≡[⇑][]₀ ⊩B₁)
      (⊩ᵛ→≡→⊢[⇑][]₀≡[⇑][]₀ ⊩B₂)
      (⊩B₁≡B₂ _ ⊩liftSubst-σ₁)
      (⊩ᵛ≡→≡→≡→⊩[⇑][]₀≡[⇑][]₀
         ⊩B₁ ⊩B₂ ⊩B₁≡B₂ ⊩B₁[⇑σ][rfl] ⊩σ ⊩Id₁≡Id₂
         (rflᵛ {t = t₁} {⊩A = ⊩A₁} {⊩t = ⊩t₁} _ ⊩σ .proj₁)
         (rflᵛ {t = t₂} {⊩A = ⊩A₂} {⊩t = ⊩t₂} _ ⊩σ .proj₁)
         (rfl-congᵛ {t = t₁} {⊩A = ⊩A₁} {⊩t = ⊩t₁} _ ⊩σ))
      (⊩ᵛ≡→≡→≡→⊩[⇑][]₀≡[⇑][]₀
         ⊩B₁ ⊩B₂ ⊩B₁≡B₂ ⊩B₁[⇑σ][v₁[σ]] ⊩σ ⊩Id₁≡Id₂ (⊩v₁ _ ⊩σ .proj₁))
      (⊩ᵛ≡→≡→≡→⊢[⇑][]₀≡[⇑][]₀ ⊩B₁ ⊩B₂ ⊩B₁≡B₂ ⊩σ ⊩Id₁≡Id₂)
      (irrelevanceTerm′
         (singleSubstLift B₁ _) ⊩B₁[rfl][σ] ⊩B₁[⇑σ][rfl]
         (⊩u₁ _ ⊩σ .proj₁))
      (irrelevanceTerm′
         (singleSubstLift B₂ _) ⊩B₂[rfl][σ] ⊩B₂[⇑σ][rfl]
         (⊩u₂ _ ⊩σ .proj₁))
      (irrelevanceEqTerm′
         (singleSubstLift B₁ _) ⊩B₁[rfl][σ] ⊩B₁[⇑σ][rfl]
         (⊩u₁≡u₂ _ ⊩σ))
      (⊩v₁ _ ⊩σ .proj₁)
      (⊩v₂ _ ⊩σ .proj₁)
      (⊩v₁≡v₂ _ ⊩σ) }}}}}}}}

------------------------------------------------------------------------
-- The J rule

opaque

  -- A variant of J-subst for _⊢_⇒*_∷_.

  J-subst* :
    Γ ⊢ A →
    Γ ⊢ t ∷ A →
    Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B →
    Γ ⊢ u ∷ B [ t , rfl ]₁₀ →
    Γ ⊢ v ∷ A →
    Γ ⊢ w₁ ⇒* w₂ ∷ Id A t v →
    (⊩Id : Γ ⊩⟨ l ⟩ Id A t v) →
    Γ ⊩⟨ l ⟩ w₂ ∷ Id A t v / ⊩Id →
    (∀ {w₁ w₂} →
     Γ ⊩⟨ l ⟩ w₁ ∷ Id A t v / ⊩Id →
     Γ ⊩⟨ l ⟩ w₂ ∷ Id A t v / ⊩Id →
     Γ ⊩⟨ l ⟩ w₁ ≡ w₂ ∷ Id A t v / ⊩Id →
     Γ ⊢ B [ v , w₁ ]₁₀ ≡ B [ v , w₂ ]₁₀) →
    Γ ⊢ J p q A t B u v w₁ ⇒* J p q A t B u v w₂ ∷ B [ v , w₁ ]₁₀
  J-subst* ⊢A ⊢t ⊢B ⊢u ⊢v w₁⇒*w₂ ⊩Id ⊩w₂ B≡B =
    case w₁⇒*w₂ of λ where
      (id ⊢w₁)         → id (Jⱼ ⊢A ⊢t ⊢B ⊢u ⊢v ⊢w₁)
      (w₁⇒w₃ ⇨ w₃⇒*w₂) →
        case redSubst*Term w₃⇒*w₂ ⊩Id ⊩w₂ of λ {
          (⊩w₃ , _) →
        case redSubstTerm w₁⇒w₃ ⊩Id ⊩w₃ of λ {
          (⊩w₁ , ⊩w₁≡w₃) →
        J-subst ⊢A ⊢t ⊢B ⊢u ⊢v w₁⇒w₃ ⇨
        conv* (J-subst* ⊢A ⊢t ⊢B ⊢u ⊢v w₃⇒*w₂ ⊩Id ⊩w₂ B≡B)
          (sym (B≡B ⊩w₁ ⊩w₃ ⊩w₁≡w₃)) }}

private opaque
  unfolding ⊩Id

  -- Reducibility for J.

  ⊩J :
    {⊩A : Γ ⊩⟨ l ⟩ A}
    {⊩t : Γ ⊩⟨ l ⟩ t ∷ A / ⊩A}
    {⊩v : Γ ⊩⟨ l ⟩ v ∷ A / ⊩A} →
    let ⊩Id = ⊩Id ⊩A ⊩t ⊩v in
    Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊩⟨ l ⟩ B →
    (⊩B[t,rfl] : Γ ⊩⟨ l ⟩ B [ t , rfl ]₁₀)
    (⊩B[v,w] : Γ ⊩⟨ l ⟩ B [ v , w ]₁₀) →
    (∀ {w w′} →
     Γ ⊩⟨ l ⟩ w ∷ Id A t v / ⊩Id →
     Γ ⊩⟨ l ⟩ w′ ∷ Id A t v / ⊩Id →
     Γ ⊩⟨ l ⟩ w ≡ w′ ∷ Id A t v / ⊩Id →
     Γ ⊢ B [ v , w ]₁₀ ≡ B [ v , w′ ]₁₀) →
    (∀ {w} →
     Γ ⊩⟨ l ⟩ t ≡ v ∷ A / ⊩A →
     Γ ⊩⟨ l ⟩ w ∷ Id A t v / ⊩Id →
     Γ ⊩⟨ l ⟩ rfl ≡ w ∷ Id A t v / ⊩Id →
     Γ ⊩⟨ l ⟩ B [ t , rfl ]₁₀ ≡ B [ v , w ]₁₀ / ⊩B[t,rfl]) →
    Γ ⊩⟨ l ⟩ u ∷ B [ t , rfl ]₁₀ / ⊩B[t,rfl] →
    Γ ⊩⟨ l ⟩ w ∷ Id A t v / ⊩Id →
    Γ ⊩⟨ l ⟩ J p q A t B u v w ∷ B [ v , w ]₁₀ / ⊩B[v,w]
  ⊩J
    {A} {t} {v} {B} {w} {u} {⊩A} {⊩t} {⊩v}
    ⊩B ⊩B[t,rfl] ⊩B[v,w] ⊢B[v,]≡B[v,] ⊩B[t,rfl]≡B[v,]
    ⊩u ⊩w@(w′ , w⇒*w′ , _) =
    let ⊩Id = ⊩Id ⊩A ⊩t ⊩v in
    case escape ⊩A of λ {
      ⊢A →
    case escapeTerm ⊩A ⊩t of λ {
      ⊢t →
    case escape ⊩B of λ {
      ⊢B →
    case escapeTerm ⊩B[t,rfl] ⊩u of λ {
      ⊢u →
    case escapeTerm ⊩A ⊩v of λ {
      ⊢v →
    case ⊩Id∷-view-inhabited ⊩w of λ where
      (ne w′-n w′~w′) →
        case ⊢u-redₜ w⇒*w′ of λ {
          ⊢w′ →
        case w′ , idRedTerm:*: ⊢w′ , ne w′-n , w′~w′ of λ {
          ⊩w′ →
        case redSubst*Term (redₜ w⇒*w′) ⊩Id ⊩w′ .proj₂ of λ {
          ⊩w≡w′ →
        case sym (⊢B[v,]≡B[v,] ⊩w ⊩w′ ⊩w≡w′) of λ {
          ⊢B[v,w′]≡B[v,w] →
        redSubst*Term
          {t = J _ _ A t B u v w}
          {u = J _ _ A t B u v w′}
          (J-subst* ⊢A ⊢t ⊢B ⊢u ⊢v (redₜ w⇒*w′) ⊩Id ⊩w′ ⊢B[v,]≡B[v,])
          ⊩B[v,w]
          (neuTerm ⊩B[v,w] (Jₙ w′-n)
             (conv (Jⱼ ⊢A ⊢t ⊢B ⊢u ⊢v ⊢w′) ⊢B[v,w′]≡B[v,w])
             (~-conv
                (~-J ⊢A
                   (escapeEq ⊩A (reflEq ⊩A))
                   ⊢t
                   (escapeTermEq ⊩A (reflEqTerm ⊩A ⊩t))
                   (escapeEq ⊩B (reflEq ⊩B))
                   (escapeTermEq ⊩B[t,rfl] (reflEqTerm ⊩B[t,rfl] ⊩u))
                   (escapeTermEq ⊩A (reflEqTerm ⊩A ⊩v))
                   w′~w′)
                ⊢B[v,w′]≡B[v,w]))
          .proj₁ }}}}
      (rflᵣ ⊩t≡v) →
        case ≅ₜ-eq (escapeTermEq ⊩A ⊩t≡v) of λ {
          ⊢t≡v →
        case   rfl , rfl
             , idRedTerm:*:
                 (conv (rflⱼ ⊢t) (Id-cong (refl ⊢A) (refl ⊢t) ⊢t≡v))
             , w⇒*w′
             , rflₙ , rflₙ
             , ⊩t≡v of λ {
          ⊩rfl≡w →
        case ⊩B[t,rfl]≡B[v,] ⊩t≡v ⊩w ⊩rfl≡w of λ {
          ⊩B[t,rfl]≡B[v,w] →
        case ≅-eq $ escapeEq ⊩B[t,rfl] ⊩B[t,rfl]≡B[v,w] of λ {
          ⊢B[t,rfl]≡B[v,w] →
        case ≅-eq $ escapeEq ⊩B[t,rfl] $
             ⊩B[t,rfl]≡B[v,] ⊩t≡v (⊩rfl′ ⊩t≡v)
               (⊩rfl≡rfl {⊩A = ⊩A} {⊩t = ⊩t} {⊩u = ⊩v} ⊩t≡v) of λ {
          ⊢B[t,rfl]≡B[v,rfl] →
        redSubst*Term
          {t = J _ _ A t B u v w}
          {u = u}
          (J-subst* ⊢A ⊢t ⊢B ⊢u ⊢v (redₜ w⇒*w′) ⊩Id (⊩rfl′ ⊩t≡v)
             ⊢B[v,]≡B[v,] ⇨∷*
           (conv (J-β ⊢A ⊢t ⊢v ⊢t≡v ⊢B ⊢B[t,rfl]≡B[v,rfl] ⊢u)
              ⊢B[t,rfl]≡B[v,w] ⇨
            id (conv ⊢u ⊢B[t,rfl]≡B[v,w])))
          ⊩B[v,w]
          (convTerm₂ ⊩B[v,w] ⊩B[t,rfl]
             (symEq ⊩B[t,rfl] ⊩B[v,w] ⊩B[t,rfl]≡B[v,w])
             ⊩u)
          .proj₁ }}}}}}}}}}

private opaque
  unfolding ⊩Id

  -- An equality lemma for J.

  ⊩J≡J :
    {⊩A₁ : Γ ⊩⟨ l ⟩ A₁}
    {⊩A₂ : Γ ⊩⟨ l ⟩ A₂}
    {⊩t₁ : Γ ⊩⟨ l ⟩ t₁ ∷ A₁ / ⊩A₁}
    {⊩t₂ : Γ ⊩⟨ l ⟩ t₂ ∷ A₂ / ⊩A₂}
    {⊩v₁ : Γ ⊩⟨ l ⟩ v₁ ∷ A₁ / ⊩A₁}
    {⊩v₂ : Γ ⊩⟨ l ⟩ v₂ ∷ A₂ / ⊩A₂} →
    let ⊩Id₁ = ⊩Id ⊩A₁ ⊩t₁ ⊩v₁
        ⊩Id₂ = ⊩Id ⊩A₂ ⊩t₂ ⊩v₂
    in
    Γ ⊩⟨ l ⟩ A₁ ≡ A₂ / ⊩A₁ →
    Γ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ A₁ / ⊩A₁ →
    Γ ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ A₁ / ⊩A₁ →
    (⊩B₁ : Γ ∙ A₁ ∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊩⟨ l ⟩ B₁) →
    Γ ∙ A₂ ∙ Id (wk1 A₂) (wk1 t₂) (var x0) ⊩⟨ l ⟩ B₂ →
    (⊩B₁[t₁,rfl] : Γ ⊩⟨ l ⟩ B₁ [ t₁ , rfl ]₁₀)
    (⊩B₂[t₂,rfl] : Γ ⊩⟨ l ⟩ B₂ [ t₂ , rfl ]₁₀)
    (⊩B₁[v₁,w₁] : Γ ⊩⟨ l ⟩ B₁ [ v₁ , w₁ ]₁₀) →
    Γ ⊩⟨ l ⟩ B₂ [ v₂ , w₂ ]₁₀ →
    (∀ {w w′} →
     Γ ⊩⟨ l ⟩ w ∷ Id A₁ t₁ v₁ / ⊩Id₁ →
     Γ ⊩⟨ l ⟩ w′ ∷ Id A₁ t₁ v₁ / ⊩Id₁ →
     Γ ⊩⟨ l ⟩ w ≡ w′ ∷ Id A₁ t₁ v₁ / ⊩Id₁ →
     Γ ⊢ B₁ [ v₁ , w ]₁₀ ≡ B₁ [ v₁ , w′ ]₁₀) →
    (∀ {w} →
     Γ ⊩⟨ l ⟩ t₁ ≡ v₁ ∷ A₁ / ⊩A₁ →
     Γ ⊩⟨ l ⟩ w ∷ Id A₁ t₁ v₁ / ⊩Id₁ →
     Γ ⊩⟨ l ⟩ rfl ≡ w ∷ Id A₁ t₁ v₁ / ⊩Id₁ →
     Γ ⊩⟨ l ⟩ B₁ [ t₁ , rfl ]₁₀ ≡ B₁ [ v₁ , w ]₁₀ / ⊩B₁[t₁,rfl]) →
    (∀ {w w′} →
     Γ ⊩⟨ l ⟩ w ∷ Id A₂ t₂ v₂ / ⊩Id₂ →
     Γ ⊩⟨ l ⟩ w′ ∷ Id A₂ t₂ v₂ / ⊩Id₂ →
     Γ ⊩⟨ l ⟩ w ≡ w′ ∷ Id A₂ t₂ v₂ / ⊩Id₂ →
     Γ ⊢ B₂ [ v₂ , w ]₁₀ ≡ B₂ [ v₂ , w′ ]₁₀) →
    Γ ∙ A₁ ∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊩⟨ l ⟩ B₁ ≡ B₂ / ⊩B₁ →
    Γ ⊩⟨ l ⟩ B₁ [ t₁ , rfl ]₁₀ ≡ B₂ [ t₂ , rfl ]₁₀ / ⊩B₁[t₁,rfl] →
    (∀ {w₂} →
     Γ ⊩⟨ l ⟩ w₂ ∷ Id A₂ t₂ v₂ / ⊩Id₂ →
     Γ ⊩⟨ l ⟩ w₁ ≡ w₂ ∷ Id A₁ t₁ v₁ / ⊩Id₁ →
     Γ ⊩⟨ l ⟩ B₁ [ v₁ , w₁ ]₁₀ ≡ B₂ [ v₂ , w₂ ]₁₀ / ⊩B₁[v₁,w₁]) →
    Γ ⊩⟨ l ⟩ u₁ ∷ B₁ [ t₁ , rfl ]₁₀ / ⊩B₁[t₁,rfl] →
    Γ ⊩⟨ l ⟩ u₂ ∷ B₂ [ t₂ , rfl ]₁₀ / ⊩B₂[t₂,rfl] →
    Γ ⊩⟨ l ⟩ u₁ ≡ u₂ ∷ B₁ [ t₁ , rfl ]₁₀ / ⊩B₁[t₁,rfl] →
    Γ ⊩⟨ l ⟩ w₁ ∷ Id A₁ t₁ v₁ / ⊩Id₁ →
    Γ ⊩⟨ l ⟩ w₂ ∷ Id A₂ t₂ v₂ / ⊩Id₂ →
    Γ ⊩⟨ l ⟩ w₁ ≡ w₂ ∷ Id A₁ t₁ v₁ / ⊩Id₁ →
    Γ ⊩⟨ l ⟩ J p q A₁ t₁ B₁ u₁ v₁ w₁ ≡ J p q A₂ t₂ B₂ u₂ v₂ w₂ ∷
      B₁ [ v₁ , w₁ ]₁₀ / ⊩B₁[v₁,w₁]
  ⊩J≡J
    {A₁} {A₂} {t₁} {t₂} {v₁} {v₂} {B₁} {B₂} {w₁} {w₂} {u₁} {u₂}
    {⊩A₁} {⊩A₂} {⊩t₁} {⊩t₂} {⊩v₁} {⊩v₂} ⊩A₁≡A₂ ⊩t₁≡t₂ ⊩v₁≡v₂
    ⊩B₁ ⊩B₂ ⊩B₁[t₁,rfl] ⊩B₂[t₂,rfl] ⊩B₁[v₁,w₁] ⊩B₂[v₂,w₂]
    ⊢B₁[v₁,]≡B₁[v₁,] ⊩B₁[t₁,rfl]≡B₁[v₁,] ⊢B₂[v₂,]≡B₂[v₂,]
    ⊩B₁≡B₂ ⊩B₁[t₁,rfl]≡B₂[t₂,rfl] ⊩B₁[v₁,w₁]≡B₂[v₂,]
    ⊩u₁ ⊩u₂ ⊩u₁≡u₂ ⊩w₁ ⊩w₂ ⊩w₁≡w₂@(w₁′ , w₂′ , w₁⇒*w₁′ , w₂⇒*w₂′ , _) =
    let ⊩Id₁′ = ⊩Id′ ⊩A₁ ⊩t₁ ⊩v₁
        ⊩Id₁  = Idᵣ ⊩Id₁′
        ⊩Id₂  = ⊩Id ⊩A₂ ⊩t₂ ⊩v₂
    in
    case escape ⊩A₁ of λ {
      ⊢A₁ →
    case escape ⊩A₂ of λ {
      ⊢A₂ →
    case escapeTerm ⊩A₁ ⊩t₁ of λ {
      ⊢t₁ →
    case escapeTerm ⊩A₂ ⊩t₂ of λ {
      ⊢t₂ →
    case escape ⊩B₁ of λ {
      ⊢B₁ →
    case escape ⊩B₂ of λ {
      ⊢B₂ →
    case escapeTerm ⊩B₁[t₁,rfl] ⊩u₁ of λ {
      ⊢u₁ →
    case escapeTerm ⊩B₂[t₂,rfl] ⊩u₂ of λ {
      ⊢u₂ →
    case escapeTerm ⊩A₁ ⊩v₁ of λ {
      ⊢v₁ →
    case escapeTerm ⊩A₂ ⊩v₂ of λ {
      ⊢v₂ →
    case ⊩Id≡Id ⊢t₂ ⊢v₂ ⊩A₁≡A₂ ⊩t₁≡t₂ ⊩v₁≡v₂ of λ {
      ⊩Id₁≡Id₂ →
    case ≅-eq (escapeEq ⊩Id₁ ⊩Id₁≡Id₂) of λ {
      ⊢Id₁≡Id₂ →
    case convRed:*: w₂⇒*w₂′ ⊢Id₁≡Id₂ of λ {
      w₂⇒*w₂′ →
    case ⊢u-redₜ w₁⇒*w₁′ of λ {
      ⊢w₁′ →
    case ⊢u-redₜ w₂⇒*w₂′ of λ {
      ⊢w₂′ →
    case ⊩Id≡∷-view-inhabited ⊩Id₁′ ⊩w₁≡w₂ of λ where
      (ne w₁′-n w₂′-n w₁′~w₂′) →
        let ⊩w₁′≡w₂′ =
                w₁′ , w₂′
              , idRedTerm:*: ⊢w₁′
              , convRed:*: (idRedTerm:*: ⊢w₂′) (sym ⊢Id₁≡Id₂)
              , ne w₁′-n , ne w₂′-n
              , w₁′~w₂′
            ⊩w₁′ , ⊩w₂′ , _ = ⊩Id≡∷⁻¹ ⊩Id₁′ ⊩w₁′≡w₂′
        in
        case convTerm₁ ⊩Id₁ ⊩Id₂ ⊩Id₁≡Id₂ ⊩w₂′ of λ {
          ⊩w₂′ →
        case redSubst*Term (redₜ w₁⇒*w₁′) ⊩Id₁ ⊩w₁′ .proj₂ of λ {
          ⊩w₁≡w₁′ →
        case redSubst*Term (redₜ w₂⇒*w₂′) ⊩Id₂ ⊩w₂′ .proj₂ of λ {
          ⊩w₂≡w₂′ →
        case ⊢B₁[v₁,]≡B₁[v₁,] ⊩w₁′ ⊩w₁ (symEqTerm ⊩Id₁ ⊩w₁≡w₁′) of λ {
          ⊢B₁[v₁,w₁′]≡B₁[v₁,w₁] →
        case ⊢B₂[v₂,]≡B₂[v₂,] ⊩w₂′ ⊩w₂ (symEqTerm ⊩Id₂ ⊩w₂≡w₂′) of λ {
          ⊢B₂[v₂,w₂′]≡B₂[v₂,w₂] →
        case conv (Jⱼ ⊢A₁ ⊢t₁ ⊢B₁ ⊢u₁ ⊢v₁ ⊢w₁′)
               ⊢B₁[v₁,w₁′]≡B₁[v₁,w₁] of λ {
          ⊢J₁ →
        case Jⱼ ⊢A₂ ⊢t₂ ⊢B₂ ⊢u₂ ⊢v₂ ⊢w₂′ of λ {
          ⊢J₂ →
        transEqTerm ⊩B₁[v₁,w₁]
          (redSubst*Term
             {A = B₁ [ v₁ , w₁ ]₁₀}
             {t = J _ _ A₁ t₁ B₁ u₁ v₁ w₁}
             {u = J _ _ A₁ t₁ B₁ u₁ v₁ w₁′}
             (J-subst* ⊢A₁ ⊢t₁ ⊢B₁ ⊢u₁ ⊢v₁ (redₜ w₁⇒*w₁′) ⊩Id₁ ⊩w₁′
                ⊢B₁[v₁,]≡B₁[v₁,])
             ⊩B₁[v₁,w₁]
             (neuTerm ⊩B₁[v₁,w₁] (Jₙ w₁′-n) ⊢J₁
                (~-conv
                   (~-J ⊢A₁ (escapeEq ⊩A₁ (reflEq ⊩A₁)) ⊢t₁
                      (escapeTermEq ⊩A₁ (reflEqTerm ⊩A₁ ⊩t₁))
                      (escapeEq ⊩B₁ (reflEq ⊩B₁))
                      (escapeTermEq ⊩B₁[t₁,rfl]
                         (reflEqTerm ⊩B₁[t₁,rfl] ⊩u₁))
                      (escapeTermEq ⊩A₁ (reflEqTerm ⊩A₁ ⊩v₁))
                      (⊩w₁′ .proj₂ .proj₂ .proj₂))
                   ⊢B₁[v₁,w₁′]≡B₁[v₁,w₁]))
             .proj₂) $
        transEqTerm ⊩B₁[v₁,w₁]
          (neuEqTerm ⊩B₁[v₁,w₁] (Jₙ w₁′-n) (Jₙ w₂′-n) ⊢J₁
             (conv ⊢J₂
                (_⊢_≡_.sym $ ≅-eq $ escapeEq ⊩B₁[v₁,w₁] $
                 ⊩B₁[v₁,w₁]≡B₂[v₂,] ⊩w₂′ $
                 transEqTerm ⊩Id₁ ⊩w₁≡w₁′ ⊩w₁′≡w₂′))
             (~-conv
                (~-J ⊢A₁ (escapeEq ⊩A₁ ⊩A₁≡A₂) ⊢t₁
                   (escapeTermEq ⊩A₁ ⊩t₁≡t₂)
                   (escapeEq ⊩B₁ ⊩B₁≡B₂)
                   (escapeTermEq ⊩B₁[t₁,rfl] ⊩u₁≡u₂)
                   (escapeTermEq ⊩A₁ ⊩v₁≡v₂)
                   w₁′~w₂′)
                ⊢B₁[v₁,w₁′]≡B₁[v₁,w₁])) $
        convEqTerm₂
          ⊩B₁[v₁,w₁] ⊩B₂[v₂,w₂] (⊩B₁[v₁,w₁]≡B₂[v₂,] ⊩w₂ ⊩w₁≡w₂) $
        symEqTerm ⊩B₂[v₂,w₂] $
        redSubst*Term
          {A = B₂ [ v₂ , w₂ ]₁₀}
          {t = J _ _ A₂ t₂ B₂ u₂ v₂ w₂}
          {u = J _ _ A₂ t₂ B₂ u₂ v₂ w₂′}
          (J-subst* ⊢A₂ ⊢t₂ ⊢B₂ ⊢u₂ ⊢v₂ (redₜ w₂⇒*w₂′) ⊩Id₂ ⊩w₂′
             ⊢B₂[v₂,]≡B₂[v₂,])
          ⊩B₂[v₂,w₂]
          (neuTerm ⊩B₂[v₂,w₂] (Jₙ w₂′-n)
             (conv ⊢J₂ ⊢B₂[v₂,w₂′]≡B₂[v₂,w₂])
             (~-conv
                (~-J ⊢A₂ (escapeEq ⊩A₂ (reflEq ⊩A₂)) ⊢t₂
                   (escapeTermEq ⊩A₂ (reflEqTerm ⊩A₂ ⊩t₂))
                   (escapeEq ⊩B₂ (reflEq ⊩B₂))
                   (escapeTermEq ⊩B₂[t₂,rfl]
                      (reflEqTerm ⊩B₂[t₂,rfl] ⊩u₂))
                   (escapeTermEq ⊩A₂ (reflEqTerm ⊩A₂ ⊩v₂))
                   (~-conv (~-trans (~-sym w₁′~w₂′) w₁′~w₂′) ⊢Id₁≡Id₂))
                ⊢B₂[v₂,w₂′]≡B₂[v₂,w₂]))
          .proj₂ }}}}}}}
      (rfl₌ ⊩t₁≡v₁) →
        case convEqTerm₁ ⊩A₁ ⊩A₂ ⊩A₁≡A₂ $
             transEqTerm ⊩A₁ (symEqTerm ⊩A₁ ⊩t₁≡t₂)
               (transEqTerm ⊩A₁ ⊩t₁≡v₁ ⊩v₁≡v₂) of λ {
          ⊩t₂≡v₂ →
        case redSubst*Term
               (redₜ w₁⇒*w₁′) ⊩Id₁ (⊩rfl′ ⊩t₁≡v₁) .proj₂ of λ {
          ⊩w₁≡rfl →
        case redSubst*Term
               (redₜ w₂⇒*w₂′) ⊩Id₂ (⊩rfl′ ⊩t₂≡v₂) .proj₂ of λ {
          ⊩w₂≡rfl →
        case ⊩B₁[t₁,rfl]≡B₁[v₁,]
               ⊩t₁≡v₁ ⊩w₁ (symEqTerm ⊩Id₁ ⊩w₁≡rfl) of λ {
          ⊩B₁[t₁,rfl]≡B₁[v₁,w₁] →
        case _⊢_≡_.trans
               (≅-eq $ escapeEq ⊩B₂[t₂,rfl] $
                symEq ⊩B₁[t₁,rfl] ⊩B₂[t₂,rfl] ⊩B₁[t₁,rfl]≡B₂[t₂,rfl]) $
             _⊢_≡_.trans
               (≅-eq $ escapeEq ⊩B₁[t₁,rfl] $
                ⊩B₁[t₁,rfl]≡B₁[v₁,] ⊩t₁≡v₁ ⊩w₁ $
                symEqTerm ⊩Id₁ ⊩w₁≡rfl) $
             ≅-eq $ escapeEq ⊩B₁[v₁,w₁] $
             ⊩B₁[v₁,w₁]≡B₂[v₂,] (⊩rfl′ ⊩t₂≡v₂) ⊩w₁≡rfl of λ {
          ⊢B₂[t₂,rfl]≡B₂[v₂,rfl] →
        convEqTerm₁ ⊩B₁[t₁,rfl] ⊩B₁[v₁,w₁] ⊩B₁[t₁,rfl]≡B₁[v₁,w₁] $
        transEqTerm ⊩B₁[t₁,rfl]
          (redSubst*Term
             {A = B₁ [ t₁ , rfl ]₁₀}
             {t = J _ _ A₁ t₁ B₁ u₁ v₁ w₁}
             {u = u₁}
             (conv*
                (J-subst* ⊢A₁ ⊢t₁ ⊢B₁ ⊢u₁ ⊢v₁ (redₜ w₁⇒*w₁′) ⊩Id₁
                   (⊩rfl′ ⊩t₁≡v₁) ⊢B₁[v₁,]≡B₁[v₁,])
                (_⊢_≡_.sym $ ≅-eq $
                 escapeEq ⊩B₁[t₁,rfl] ⊩B₁[t₁,rfl]≡B₁[v₁,w₁]) ⇨∷*
              (J-β ⊢A₁ ⊢t₁ ⊢v₁ (≅ₜ-eq (escapeTermEq ⊩A₁ ⊩t₁≡v₁)) ⊢B₁
                 (≅-eq $ escapeEq ⊩B₁[t₁,rfl] $
                  ⊩B₁[t₁,rfl]≡B₁[v₁,] ⊩t₁≡v₁ (⊩rfl′ ⊩t₁≡v₁) $
                  ⊩rfl≡rfl {⊩A = ⊩A₁} {⊩t = ⊩t₁} {⊩u = ⊩v₁} ⊩t₁≡v₁)
                 ⊢u₁ ⇨
               id ⊢u₁))
             ⊩B₁[t₁,rfl]
             ⊩u₁
             .proj₂) $
        transEqTerm ⊩B₁[t₁,rfl] ⊩u₁≡u₂ $
        convEqTerm₂ ⊩B₁[t₁,rfl] ⊩B₂[t₂,rfl] ⊩B₁[t₁,rfl]≡B₂[t₂,rfl] $
        symEqTerm ⊩B₂[t₂,rfl] $
        redSubst*Term
          {A = B₂ [ t₂ , rfl ]₁₀}
          {t = J _ _ A₂ t₂ B₂ u₂ v₂ w₂}
          {u = u₂}
          (conv*
             (J-subst* ⊢A₂ ⊢t₂ ⊢B₂ ⊢u₂ ⊢v₂ (redₜ w₂⇒*w₂′) ⊩Id₂
                (⊩rfl′ ⊩t₂≡v₂) ⊢B₂[v₂,]≡B₂[v₂,])
             (trans (⊢B₂[v₂,]≡B₂[v₂,] ⊩w₂ (⊩rfl′ ⊩t₂≡v₂) ⊩w₂≡rfl)
                (sym ⊢B₂[t₂,rfl]≡B₂[v₂,rfl])) ⇨∷*
           (J-β ⊢A₂ ⊢t₂ ⊢v₂ (≅ₜ-eq (escapeTermEq ⊩A₂ ⊩t₂≡v₂)) ⊢B₂
              ⊢B₂[t₂,rfl]≡B₂[v₂,rfl] ⊢u₂ ⇨
            id ⊢u₂))
          ⊩B₂[t₂,rfl]
          ⊩u₂
          .proj₂ }}}}}}}}}}}}}}}}}}}}

opaque
  unfolding Idᵛ

  -- Validity for J.

  Jᵛ :
    {⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ}
    {⊩t : Γ ⊩ᵛ⟨ l ⟩ t ∷ A / ⊩Γ / ⊩A}
    {⊩v : Γ ⊩ᵛ⟨ l ⟩ v ∷ A / ⊩Γ / ⊩A}
    {⊩Id : Γ ∙ A ⊩ᵛ⟨ l ⟩ Id (wk1 A) (wk1 t) (var x0) / ⊩Γ ∙ ⊩A} →
    ∀ u →
    Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊩ᵛ⟨ l ⟩ B / ⊩Γ ∙ ⊩A ∙ ⊩Id →
    (⊩B[t,rfl] : Γ ⊩ᵛ⟨ l ⟩ B [ t , rfl ]₁₀ / ⊩Γ)
    (⊩B[v,w] : Γ ⊩ᵛ⟨ l ⟩ B [ v , w ]₁₀ / ⊩Γ) →
    Γ ⊩ᵛ⟨ l ⟩ u ∷ B [ t , rfl ]₁₀ / ⊩Γ / ⊩B[t,rfl] →
    Γ ⊩ᵛ⟨ l ⟩ w ∷ Id A t v / ⊩Γ / Idᵛ ⊩A ⊩t ⊩v →
    Γ ⊩ᵛ⟨ l ⟩ J p q A t B u v w ∷ B [ v , w ]₁₀ / ⊩Γ / ⊩B[v,w]
  Jᵛ
    {l} {A} {t} {v} {B} {w} {⊩A} {⊩t} {⊩v} {⊩Id = ⊩Id′}
    u ⊩B ⊩B[t,rfl] ⊩B[v,w] ⊩u ⊩w {Δ} {σ} _ ⊩σ =
      let ⊩A[σ]        , _ = ⊩A .unwrap _ ⊩σ
          ⊩t[σ]        , _ = ⊩t _ ⊩σ
          ⊩B[⇑⇑σ]′     , _ = ⊩B .unwrap
                               {σ = liftSubstn σ 2}
                               _
                               (liftSubstS _ _ ⊩Id′ $
                                liftSubstS _ _ ⊩A ⊩σ)
          ⊩B[t,rfl][σ] , _ = ⊩B[t,rfl] .unwrap _ ⊩σ
          ⊩B[v,w][σ]   , _ = ⊩B[v,w] .unwrap _ ⊩σ
          ⊩Id′[σ,t[σ]] , _ = ⊩Id′ .unwrap
                               {σ = consSubst σ (t U.[ σ ])}
                               _ (⊩σ , ⊩t[σ])
          ⊩Id′[σ,v[σ]] , _ = ⊩Id′ .unwrap
                               {σ = consSubst σ (v U.[ σ ])}
                               _ (⊩σ , ⊩v _ ⊩σ .proj₁)
          ⊩Id-t[σ]-v[σ]    = ⊩Id ⊩A[σ] ⊩t[σ] (⊩v _ ⊩σ .proj₁)
      in
      case escapeTerm ⊩A[σ] ⊩t[σ] of λ {
        ⊢t[σ] →
      case irrelevance′ ([,]-[]-commute B) ⊩B[t,rfl][σ] of λ {
        ⊩B[⇑⇑σ][t[σ],rfl] →
      case irrelevance′ ([,]-[]-commute B) ⊩B[v,w][σ] of λ {
        ⊩B[⇑⇑σ][v[σ],w[σ]] →
      case PE.sym $
           PE.cong₂ (λ A t′ → Id A t′ (t U.[ σ ]))
             (wk1-tail A) (wk1-tail t) of λ {
        Id-t[σ]-t[σ]≡Id-wk1-t[σ,t[σ]]-t[σ] →
      case PE.sym $
           PE.cong₂ (λ A t′ → Id A t′ (v U.[ σ ]))
             (wk1-tail A) (wk1-tail t) of λ {
        Id-t[σ]-v[σ]≡Id-wk1-t[σ,v[σ]]-v[σ] →
      case PE.subst
             (λ Id →
                Δ ∙ A U.[ σ ] ∙ Id ⊩⟨ l ⟩
                B U.[ liftSubst (liftSubst σ) ])
             (Id-wk1-wk1-0[⇑]≡ A t)
             ⊩B[⇑⇑σ]′ of λ {
        ⊩B[⇑⇑σ] →
      case (λ w w′ ⊩w ⊩w′
              (⊩w≡w′ : _ ⊩⟨ _ ⟩ w ≡ w′ ∷ _ / ⊩Id-t[σ]-v[σ]) →
              ⊩ᵛ→≡→⊢[⇑⇑][,]≡[⇑⇑][,]
                ⊩B
                (irrelevanceTerm′
                   Id-t[σ]-v[σ]≡Id-wk1-t[σ,v[σ]]-v[σ]
                   ⊩Id-t[σ]-v[σ] ⊩Id′[σ,v[σ]] ⊩w)
                (irrelevanceTerm′
                   Id-t[σ]-v[σ]≡Id-wk1-t[σ,v[σ]]-v[σ]
                   ⊩Id-t[σ]-v[σ] ⊩Id′[σ,v[σ]] ⊩w′)
                (irrelevanceEqTerm′
                   Id-t[σ]-v[σ]≡Id-wk1-t[σ,v[σ]]-v[σ]
                   ⊩Id-t[σ]-v[σ] ⊩Id′[σ,v[σ]] ⊩w≡w′)) of λ {
        ⊢B[⇑⇑σ][v[σ],]≡B[⇑⇑σ][v[σ],] →
      case (λ w ⊩t[σ]≡v[σ]
              (⊩w : _ ⊩⟨ _ ⟩ w ∷ _ / ⊩Id-t[σ]-v[σ]) ⊩rfl≡w →
              case ⊩Id≡Id
                     (PE.subst₂ (_ ⊢_∷_)
                        (PE.sym (wk1-tail t))
                        (PE.sym (wk1-tail A))
                        ⊢t[σ])
                     (PE.subst (_ ⊢ _ ∷_) (PE.sym (wk1-tail A)) ⊢t[σ])
                     (irrelevanceEqR′ (PE.sym (wk1-tail A))
                        ⊩A[σ] (reflEq ⊩A[σ]))
                     (PE.subst (_ ⊩⟨ _ ⟩ t U.[ _ ] ≡_∷ _ / ⊩A[σ])
                        (PE.sym (wk1-tail t))
                        (reflEqTerm ⊩A[σ] ⊩t[σ]))
                     (symEqTerm ⊩A[σ] ⊩t[σ]≡v[σ]) of λ {
                ⊩Id-t[σ]-v[σ]≡Id-wk1-t[σ,t[σ]]-t[σ] →
              ⊩ᵛ→≡→≡→⊩[⇑⇑][,]≡[⇑⇑][,]
                ⊩B ⊩B[⇑⇑σ][t[σ],rfl] ⊩t[σ]≡v[σ]
                (convTerm₁
                   ⊩Id-t[σ]-v[σ] ⊩Id′[σ,t[σ]]
                   ⊩Id-t[σ]-v[σ]≡Id-wk1-t[σ,t[σ]]-t[σ]
                   (⊩rfl′ ⊩t[σ]≡v[σ]))
                (irrelevanceTerm′
                   Id-t[σ]-v[σ]≡Id-wk1-t[σ,v[σ]]-v[σ]
                   ⊩Id-t[σ]-v[σ] ⊩Id′[σ,v[σ]] ⊩w)
                (convEqTerm₁
                   ⊩Id-t[σ]-v[σ] ⊩Id′[σ,t[σ]]
                   ⊩Id-t[σ]-v[σ]≡Id-wk1-t[σ,t[σ]]-t[σ]
                   ⊩rfl≡w) }) of λ {
        ⊩B[⇑⇑σ][t[σ],rfl]≡B[⇑⇑σ][v[σ],] →
      case irrelevanceTerm′
             ([,]-[]-commute B) ⊩B[t,rfl][σ] ⊩B[⇑⇑σ][t[σ],rfl] $
           ⊩u _ ⊩σ .proj₁ of λ {
        ⊩u[σ] →
      irrelevanceTerm′ (PE.sym ([,]-[]-commute B))
        ⊩B[⇑⇑σ][v[σ],w[σ]] ⊩B[v,w][σ]
        (⊩J
           {A = A U.[ σ ]}
           {t = t U.[ σ ]}
           {v = v U.[ σ ]}
           {B = B U.[ liftSubstn σ 2 ]}
           {w = w U.[ σ ]}
           {u = u U.[ σ ]}
           ⊩B[⇑⇑σ]
           ⊩B[⇑⇑σ][t[σ],rfl]
           ⊩B[⇑⇑σ][v[σ],w[σ]]
           (λ {w = w} {w′ = w′} → ⊢B[⇑⇑σ][v[σ],]≡B[⇑⇑σ][v[σ],] w w′)
           (λ {w = w} → ⊩B[⇑⇑σ][t[σ],rfl]≡B[⇑⇑σ][v[σ],] w)
           ⊩u[σ]
           (⊩w _ ⊩σ .proj₁))
    , λ {σ′} ⊩σ′ ⊩σ≡σ′ →
        let ⊩A[σ′]         , _ = ⊩A .unwrap _ ⊩σ′
            ⊩t[σ′]         , _ = ⊩t _ ⊩σ′
            ⊩B[t,rfl][σ′]  , _ = ⊩B[t,rfl] .unwrap _ ⊩σ′
            ⊩B[v,w][σ′]    , _ = ⊩B[v,w] .unwrap _ ⊩σ′
            ⊩Id′[σ′,t[σ′]] , _ = ⊩Id′ .unwrap
                                   {σ = consSubst σ′ (t U.[ σ′ ])}
                                   _ (⊩σ′ , ⊩t[σ′])
            ⊩Id′[σ′,v[σ′]] , _ = ⊩Id′ .unwrap
                                   {σ = consSubst σ′ (v U.[ σ′ ])}
                                   _ (⊩σ′ , ⊩v _ ⊩σ′ .proj₁)
            ⊩Id-t[σ′]-v[σ′]    = ⊩Id ⊩A[σ′] ⊩t[σ′] (⊩v _ ⊩σ′ .proj₁)
        in
        case irrelevance′ ([,]-[]-commute B) ⊩B[t,rfl][σ′] of λ {
          ⊩B[⇑⇑σ′][t[σ′],rfl] →
        case irrelevance′ ([,]-[]-commute B) ⊩B[v,w][σ′] of λ {
          ⊩B[⇑⇑σ′][v[σ′],w[σ′]] →
        case PE.sym $
             PE.cong₂ (λ A t′ → Id A t′ (t U.[ σ′ ]))
               (wk1-tail A) (wk1-tail t) of λ {
          Id-t[σ′]-t[σ′]≡Id-wk1-t[σ′,t[σ′]]-t[σ′] →
        case PE.sym $
             PE.cong₂ (λ A t′ → Id A t′ (v U.[ σ′ ]))
               (wk1-tail A) (wk1-tail t) of λ {
          Id-t[σ′]-v[σ′]≡Id-wk1-t[σ′,v[σ′]]-v[σ′] →
        case irrelevanceEqR′
               Id-t[σ′]-v[σ′]≡Id-wk1-t[σ′,v[σ′]]-v[σ′]
               ⊩Id-t[σ′]-v[σ′] $
             reflEq ⊩Id-t[σ′]-v[σ′] of λ {
          ⊩Id-t[σ′]-v[σ′]≡Id-wk1-t[σ′,v[σ′]]-v[σ′] →
        case ⊩t _ _ .proj₂ ⊩σ′ ⊩σ≡σ′ of λ {
          ⊩t[σ]≡t[σ′] →
        case ⊩v _ _ .proj₂ ⊩σ′ ⊩σ≡σ′ of λ {
          ⊩v[σ]≡v[σ′] →
        irrelevanceEqTerm′
          (PE.sym ([,]-[]-commute B)) ⊩B[⇑⇑σ][v[σ],w[σ]] ⊩B[v,w][σ] $
        ⊩J≡J
          {A₁ = A U.[ σ ]}
          {A₂ = A U.[ σ′ ]}
          {t₁ = t U.[ σ ]}
          {t₂ = t U.[ σ′ ]}
          {v₁ = v U.[ σ ]}
          {v₂ = v U.[ σ′ ]}
          {B₁ = B U.[ liftSubstn σ 2 ]}
          {B₂ = B U.[ liftSubstn σ′ 2 ]}
          {w₁ = w U.[ σ ]}
          {w₂ = w U.[ σ′ ]}
          {u₁ = u U.[ σ ]}
          {u₂ = u U.[ σ′ ]}
          (⊩A .unwrap _ _ .proj₂ ⊩σ′ ⊩σ≡σ′)
          ⊩t[σ]≡t[σ′]
          ⊩v[σ]≡v[σ′]
          ⊩B[⇑⇑σ]
          (PE.subst
             (λ Id →
                Δ ∙ A U.[ σ′ ] ∙ Id ⊩⟨ l ⟩
                B U.[ liftSubst (liftSubst σ′) ])
             (Id-wk1-wk1-0[⇑]≡ A t) $
           ⊩B .unwrap _ (liftSubstS _ _ ⊩Id′ (liftSubstS _ _ ⊩A ⊩σ′))
             .proj₁)
          ⊩B[⇑⇑σ][t[σ],rfl]
          ⊩B[⇑⇑σ′][t[σ′],rfl]
          ⊩B[⇑⇑σ][v[σ],w[σ]]
          ⊩B[⇑⇑σ′][v[σ′],w[σ′]]
          (λ {w = w} {w′ = w′} → ⊢B[⇑⇑σ][v[σ],]≡B[⇑⇑σ][v[σ],] w w′)
          (λ {w = w} → ⊩B[⇑⇑σ][t[σ],rfl]≡B[⇑⇑σ][v[σ],] w)
          (λ ⊩w ⊩w′ ⊩w≡w′ →
             ⊩ᵛ→≡→⊢[⇑⇑][,]≡[⇑⇑][,] ⊩B
               (convTerm₁
                  ⊩Id-t[σ′]-v[σ′] ⊩Id′[σ′,v[σ′]]
                  ⊩Id-t[σ′]-v[σ′]≡Id-wk1-t[σ′,v[σ′]]-v[σ′]
                  ⊩w)
               (irrelevanceTerm′
                  Id-t[σ′]-v[σ′]≡Id-wk1-t[σ′,v[σ′]]-v[σ′]
                  ⊩Id-t[σ′]-v[σ′] ⊩Id′[σ′,v[σ′]] ⊩w′)
               (convEqTerm₁
                  ⊩Id-t[σ′]-v[σ′] ⊩Id′[σ′,v[σ′]]
                  ⊩Id-t[σ′]-v[σ′]≡Id-wk1-t[σ′,v[σ′]]-v[σ′]
                  ⊩w≡w′))
          (irrelevanceEq‴ PE.refl PE.refl
             (PE.cong (λ Id → Δ ∙ A U.[ σ ] ∙ Id) $
              Id-wk1-wk1-0[⇑]≡ A t)
             ⊩B[⇑⇑σ]′ ⊩B[⇑⇑σ] $
           ⊩B .unwrap {σ = liftSubstn σ 2}
             _ (liftSubstS _ _ ⊩Id′ (liftSubstS {σ = σ} _ _ ⊩A ⊩σ))
             .proj₂ {σ′ = liftSubstn σ′ 2}
             (liftSubstS″ ⊩Id′ ⊩σ′ ⊩σ≡σ′)
             (liftSubstSEq {σ′ = liftSubst σ′} _ _ ⊩Id′
                (liftSubstS _ _ ⊩A ⊩σ)
                (liftSubstSEq _ _ ⊩A ⊩σ ⊩σ≡σ′)))
          (⊩ᵛ→≡→≡→≡→⊩[⇑⇑][,]≡[⇑⇑][,]
             ⊩B ⊩B[⇑⇑σ][t[σ],rfl] ⊩σ≡σ′ ⊩t[σ]≡t[σ′]
             (irrelevanceTerm′
                Id-t[σ]-t[σ]≡Id-wk1-t[σ,t[σ]]-t[σ]
                (⊩Id ⊩A[σ] ⊩t[σ] ⊩t[σ])
                ⊩Id′[σ,t[σ]] ⊩rfl)
             (irrelevanceTerm′
                Id-t[σ′]-t[σ′]≡Id-wk1-t[σ′,t[σ′]]-t[σ′]
                (⊩Id ⊩A[σ′] ⊩t[σ′] ⊩t[σ′])
                ⊩Id′[σ′,t[σ′]] ⊩rfl)
             (irrelevanceEqTerm′
                Id-t[σ]-t[σ]≡Id-wk1-t[σ,t[σ]]-t[σ]
                (⊩Id ⊩A[σ] ⊩t[σ] ⊩t[σ])
                ⊩Id′[σ,t[σ]]
                (⊩rfl≡rfl (reflEqTerm ⊩A[σ] ⊩t[σ]))))
          (λ ⊩w₂ ⊩w₁≡w₂ →
             ⊩ᵛ→≡→≡→≡→⊩[⇑⇑][,]≡[⇑⇑][,]
               ⊩B ⊩B[⇑⇑σ][v[σ],w[σ]] ⊩σ≡σ′ ⊩v[σ]≡v[σ′]
               (irrelevanceTerm′
                  Id-t[σ]-v[σ]≡Id-wk1-t[σ,v[σ]]-v[σ]
                  ⊩Id-t[σ]-v[σ] ⊩Id′[σ,v[σ]]
                  (⊩w _ ⊩σ .proj₁))
               (irrelevanceTerm′
                  Id-t[σ′]-v[σ′]≡Id-wk1-t[σ′,v[σ′]]-v[σ′]
                  ⊩Id-t[σ′]-v[σ′] ⊩Id′[σ′,v[σ′]]
                  ⊩w₂)
               (irrelevanceEqTerm′
                  Id-t[σ]-v[σ]≡Id-wk1-t[σ,v[σ]]-v[σ]
                  ⊩Id-t[σ]-v[σ] ⊩Id′[σ,v[σ]] ⊩w₁≡w₂))
          ⊩u[σ]
          (irrelevanceTerm′
             ([,]-[]-commute B) ⊩B[t,rfl][σ′] ⊩B[⇑⇑σ′][t[σ′],rfl] $
           ⊩u _ ⊩σ′ .proj₁)
          (irrelevanceEqTerm′
             ([,]-[]-commute B) ⊩B[t,rfl][σ] ⊩B[⇑⇑σ][t[σ],rfl] $
           ⊩u _ _ .proj₂ ⊩σ′ ⊩σ≡σ′)
          (⊩w _ ⊩σ .proj₁)
          (⊩w _ ⊩σ′ .proj₁)
          (⊩w _ _ .proj₂ ⊩σ′ ⊩σ≡σ′) }}}}}}}}}}}}}}}}

opaque

  -- Validity of the J β rule.

  J-βᵛ :
    {⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ}
    {⊩Id : Γ ∙ A ⊩ᵛ⟨ l ⟩ Id (wk1 A) (wk1 t) (var x0) / ⊩Γ ∙ ⊩A} →
    ∀ u →
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A / ⊩Γ / ⊩A →
    Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊩ᵛ⟨ l ⟩ B / ⊩Γ ∙ ⊩A ∙ ⊩Id →
    (⊩B[t,rfl] : Γ ⊩ᵛ⟨ l ⟩ B [ t , rfl ]₁₀ / ⊩Γ) →
    Γ ⊩ᵛ⟨ l ⟩ u ∷ B [ t , rfl ]₁₀ / ⊩Γ / ⊩B[t,rfl] →
    Γ ⊩ᵛ⟨ l ⟩ J p q A t B u t rfl ≡ u ∷ B [ t , rfl ]₁₀ / ⊩Γ / ⊩B[t,rfl]
  J-βᵛ {A} {t} {B} {⊩A} {⊩Id = ⊩Id′} _ ⊩t ⊩B ⊩B[t,rfl] ⊩u {Δ} {σ} _ ⊩σ =
    let ⊩A[σ]        , _ = ⊩A .unwrap _ ⊩σ
        ⊩B[t,rfl][σ] , _ = ⊩B[t,rfl] .unwrap _ ⊩σ
    in
    case ⊩t _ ⊩σ .proj₁ of λ {
      ⊩t[σ] →
    case escapeTerm ⊩A[σ] ⊩t[σ] of λ {
      ⊢t[σ] →
    case irrelevanceTerm′
           (PE.cong₂ (λ A t′ → Id A t′ (t U.[ _ ]))
              (PE.sym (wk1-tail {σ = consSubst _ _} A))
              (PE.sym (wk1-tail t)))
           (⊩Id ⊩A[σ] ⊩t[σ] ⊩t[σ])
           (⊩Id′ .unwrap _ (_ , ⊩t[σ]) .proj₁)
           ⊩rfl of λ {
      ⊩rfl →
    case ⊩u _ ⊩σ .proj₁ of λ {
      ⊩u[σ] →
    redSubstTerm
      (PE.subst (_ ⊢ J _ _ _ _ (B U.[ _ ]) _ _ _ ⇒ _ ∷_)
         (PE.sym ([,]-[]-commute B))
         (J-β (escape ⊩A[σ]) ⊢t[σ] ⊢t[σ] (refl ⊢t[σ])
            (PE.subst
               (λ Id →
                  Δ ∙ A U.[ σ ] ∙ Id ⊢
                  B U.[ liftSubst (liftSubst σ) ])
               (Id-wk1-wk1-0[⇑]≡ A t) $
             escape $
             ⊩B .unwrap
               _ (liftSubstS _ _ ⊩Id′ (liftSubstS _ _ ⊩A ⊩σ)) .proj₁)
            (⊩ᵛ→⊢[⇑⇑][,]≡[⇑⇑][,] ⊩B ⊩rfl)
            (PE.subst (_ ⊢ _ ∷_)
               (PE.sym (PE.sym ([,]-[]-commute B)))
               (escapeTerm ⊩B[t,rfl][σ] ⊩u[σ]))))
      ⊩B[t,rfl][σ]
      ⊩u[σ]
      .proj₂ }}}}

opaque
  unfolding Idᵛ

  -- Validity of equality preservation for J.

  J-congᵛ :
    {⊩A₁ : Γ ⊩ᵛ⟨ l ⟩ A₁ / ⊩Γ}
    {⊩A₂ : Γ ⊩ᵛ⟨ l ⟩ A₂ / ⊩Γ}
    {⊩t₁ : Γ ⊩ᵛ⟨ l ⟩ t₁ ∷ A₁ / ⊩Γ / ⊩A₁}
    {⊩t₂ : Γ ⊩ᵛ⟨ l ⟩ t₂ ∷ A₂ / ⊩Γ / ⊩A₂}
    {⊩v₁ : Γ ⊩ᵛ⟨ l ⟩ v₁ ∷ A₁ / ⊩Γ / ⊩A₁}
    {⊩v₂ : Γ ⊩ᵛ⟨ l ⟩ v₂ ∷ A₂ / ⊩Γ / ⊩A₂}
    {⊩Id₁ : Γ ∙ A₁ ⊩ᵛ⟨ l ⟩ Id (wk1 A₁) (wk1 t₁) (var x0) / ⊩Γ ∙ ⊩A₁}
    {⊩Id₂ : Γ ∙ A₂ ⊩ᵛ⟨ l ⟩ Id (wk1 A₂) (wk1 t₂) (var x0) / ⊩Γ ∙ ⊩A₂} →
    ∀ u₁ u₂ w₂ →
    Γ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ / ⊩Γ / ⊩A₁ →
    Γ ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ A₁ / ⊩Γ / ⊩A₁ →
    (⊩B₁ : Γ ∙ A₁ ∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊩ᵛ⟨ l ⟩ B₁ /
             ⊩Γ ∙ ⊩A₁ ∙ ⊩Id₁) →
    Γ ∙ A₂ ∙ Id (wk1 A₂) (wk1 t₂) (var x0) ⊩ᵛ⟨ l ⟩ B₂ /
      ⊩Γ ∙ ⊩A₂ ∙ ⊩Id₂ →
    Γ ∙ A₁ ∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊩ᵛ⟨ l ⟩ B₁ ≡ B₂ /
      ⊩Γ ∙ ⊩A₁ ∙ ⊩Id₁ / ⊩B₁ →
    (⊩B₁[t₁,rfl] : Γ ⊩ᵛ⟨ l ⟩ B₁ [ t₁ , rfl ]₁₀ / ⊩Γ)
    (⊩B₂[t₂,rfl] : Γ ⊩ᵛ⟨ l ⟩ B₂ [ t₂ , rfl ]₁₀ / ⊩Γ)
    (⊩B₁[v₁,w₁] : Γ ⊩ᵛ⟨ l ⟩ B₁ [ v₁ , w₁ ]₁₀ / ⊩Γ) →
    Γ ⊩ᵛ⟨ l ⟩ u₁ ∷ B₁ [ t₁ , rfl ]₁₀ / ⊩Γ / ⊩B₁[t₁,rfl] →
    Γ ⊩ᵛ⟨ l ⟩ u₂ ∷ B₂ [ t₂ , rfl ]₁₀ / ⊩Γ / ⊩B₂[t₂,rfl] →
    Γ ⊩ᵛ⟨ l ⟩ u₁ ≡ u₂ ∷ B₁ [ t₁ , rfl ]₁₀ / ⊩Γ / ⊩B₁[t₁,rfl] →
    Γ ⊩ᵛ⟨ l ⟩ v₁ ≡ v₂ ∷ A₁ / ⊩Γ / ⊩A₁ →
    Γ ⊩ᵛ⟨ l ⟩ w₁ ∷ Id A₁ t₁ v₁ / ⊩Γ / Idᵛ ⊩A₁ ⊩t₁ ⊩v₁ →
    Γ ⊩ᵛ⟨ l ⟩ w₂ ∷ Id A₂ t₂ v₂ / ⊩Γ / Idᵛ ⊩A₂ ⊩t₂ ⊩v₂ →
    Γ ⊩ᵛ⟨ l ⟩ w₁ ≡ w₂ ∷ Id A₁ t₁ v₁ / ⊩Γ / Idᵛ ⊩A₁ ⊩t₁ ⊩v₁ →
    Γ ⊩ᵛ⟨ l ⟩ J p q A₁ t₁ B₁ u₁ v₁ w₁ ≡ J p q A₂ t₂ B₂ u₂ v₂ w₂ ∷
      B₁ [ v₁ , w₁ ]₁₀ / ⊩Γ / ⊩B₁[v₁,w₁]
  J-congᵛ
    {l} {A₁} {A₂} {t₁} {t₂} {v₁} {v₂} {B₁} {B₂} {w₁}
    {⊩A₁} {⊩A₂} {⊩t₁} {⊩t₂} {⊩v₁} {⊩v₂} {⊩Id₁} {⊩Id₂}
    u₁ u₂ w₂
    ⊩A₁≡A₂ ⊩t₁≡t₂ ⊩B₁ ⊩B₂ ⊩B₁≡B₂ ⊩B₁[t₁,rfl] ⊩B₂[t₂,rfl] ⊩B₁[v₁,w₁]
    ⊩u₁ ⊩u₂ ⊩u₁≡u₂ ⊩v₁≡v₂ ⊩w₁ ⊩w₂ ⊩w₁≡w₂ {Δ} {σ} _ ⊩σ =
    let ⊩A₁[σ]         , _ = ⊩A₁ .unwrap _ ⊩σ
        ⊩A₂[σ]         , _ = ⊩A₂ .unwrap _ ⊩σ
        ⊩B₁[⇑⇑σ]′      , _ = ⊩B₁ .unwrap
                               {σ = liftSubstn σ 2}
                               _
                               (liftSubstS _ _ ⊩Id₁ $
                                liftSubstS _ _ ⊩A₁ ⊩σ)
        ⊩B₂[⇑⇑σ]′      , _ = ⊩B₂ .unwrap
                               {σ = liftSubstn σ 2}
                               _
                               (liftSubstS _ _ ⊩Id₂ $
                                liftSubstS _ _ ⊩A₂ ⊩σ)
        ⊩B₁[t₁,rfl][σ] , _ = ⊩B₁[t₁,rfl] .unwrap _ ⊩σ
        ⊩B₂[t₂,rfl][σ] , _ = ⊩B₂[t₂,rfl] .unwrap _ ⊩σ
        ⊩B₁[v₁,w₁][σ]  , _ = ⊩B₁[v₁,w₁] .unwrap _ ⊩σ
        ⊩Id₁[σ,t₁[σ]]  , _ = ⊩Id₁ .unwrap
                               {σ = consSubst σ (t₁ U.[ σ ])}
                               _ (⊩σ , ⊩t₁ _ ⊩σ .proj₁)
        ⊩Id₂[σ,t₂[σ]]  , _ = ⊩Id₂ .unwrap
                               {σ = consSubst σ (t₂ U.[ σ ])}
                               _ (⊩σ , ⊩t₂ _ ⊩σ .proj₁)
        ⊩Id₁[σ,v₁[σ]]  , _ = ⊩Id₁ .unwrap
                               {σ = consSubst σ (v₁ U.[ σ ])}
                               _ (⊩σ , ⊩v₁ _ ⊩σ .proj₁)
        ⊩Id₂[σ,v₂[σ]]  , _ = ⊩Id₂ .unwrap
                               {σ = consSubst σ (v₂ U.[ σ ])}
                               _ (⊩σ , ⊩v₂ _ ⊩σ .proj₁)

        ⊩Id-t₁[σ]-v₁[σ] =
          ⊩Id ⊩A₁[σ] (⊩t₁ _ ⊩σ .proj₁) (⊩v₁ _ ⊩σ .proj₁)
        ⊩Id-t₂[σ]-v₂[σ] =
          ⊩Id ⊩A₂[σ] (⊩t₂ _ ⊩σ .proj₁) (⊩v₂ _ ⊩σ .proj₁)

        ⊩t₂[σ]′ =
          convTerm₂ ⊩A₁[σ] ⊩A₂[σ] (⊩A₁≡A₂ _ ⊩σ) (⊩t₂ _ ⊩σ .proj₁)
        ⊩v₂[σ]′ =
          convTerm₂ ⊩A₁[σ] ⊩A₂[σ] (⊩A₁≡A₂ _ ⊩σ) (⊩v₂ _ ⊩σ .proj₁)
    in
    case PE.subst
           (λ Id →
              Δ ∙ A₁ U.[ σ ] ∙ Id ⊩⟨ l ⟩
              B₁ U.[ liftSubst (liftSubst σ) ])
           (Id-wk1-wk1-0[⇑]≡ A₁ t₁)
           ⊩B₁[⇑⇑σ]′ of λ {
      ⊩B₁[⇑⇑σ] →
    case irrelevance′ ([,]-[]-commute B₁) ⊩B₁[t₁,rfl][σ] of λ {
      ⊩B₁[⇑⇑σ][t₁[σ],rfl] →
    case irrelevance′ ([,]-[]-commute B₂) ⊩B₂[t₂,rfl][σ] of λ {
      ⊩B₂[⇑⇑σ][t₂[σ],rfl] →
    case irrelevance′ ([,]-[]-commute B₁) ⊩B₁[v₁,w₁][σ] of λ {
      ⊩B₁[⇑⇑σ][v₁[σ],w₁[σ]] →
    case (λ A t v →
            PE.sym $
            PE.cong₂ (λ A t → Id A t (v U.[ σ ]))
              (wk1-tail {σ = consSubst σ (v U.[ σ ])} A)
              (wk1-tail {σ = consSubst σ (v U.[ σ ])} t)) of λ {
      Id-[σ]-[σ]≡Id-wk1-[σ,[σ]]-[σ] →
    case escapeTerm ⊩A₁[σ] (⊩t₁ _ ⊩σ .proj₁) of λ {
      ⊢t₁[σ] →
    case escapeTerm ⊩A₂[σ] (⊩t₂ _ ⊩σ .proj₁) of λ {
      ⊢t₂[σ] →
    case irrelevanceEqR′
           (Id-[σ]-[σ]≡Id-wk1-[σ,[σ]]-[σ] A₂ t₂ v₂)
           ⊩Id-t₂[σ]-v₂[σ] $
         reflEq ⊩Id-t₂[σ]-v₂[σ] of λ {
      ⊩Id-t₂[σ]-v₂[σ]≡Id-wk1-t₂[σ,v₂[σ]]-v₂[σ] →
    irrelevanceEqTerm′ (PE.sym ([,]-[]-commute B₁))
      ⊩B₁[⇑⇑σ][v₁[σ],w₁[σ]] ⊩B₁[v₁,w₁][σ] $
    ⊩J≡J
      {A₁ = A₁ U.[ σ ]}
      {A₂ = A₂ U.[ σ ]}
      {t₁ = t₁ U.[ σ ]}
      {t₂ = t₂ U.[ σ ]}
      {v₁ = v₁ U.[ σ ]}
      {v₂ = v₂ U.[ σ ]}
      {B₁ = B₁ U.[ liftSubstn σ 2 ]}
      {B₂ = B₂ U.[ liftSubstn σ 2 ]}
      {w₁ = w₁ U.[ σ ]}
      {w₂ = w₂ U.[ σ ]}
      {u₁ = u₁ U.[ σ ]}
      {u₂ = u₂ U.[ σ ]}
      (⊩A₁≡A₂ _ ⊩σ)
      (⊩t₁≡t₂ _ ⊩σ)
      (⊩v₁≡v₂ _ ⊩σ)
      ⊩B₁[⇑⇑σ]
      (PE.subst
         (λ Id →
            Δ ∙ A₂ U.[ σ ] ∙ Id ⊩⟨ l ⟩ B₂ U.[ liftSubst (liftSubst σ) ])
         (Id-wk1-wk1-0[⇑]≡ A₂ t₂) $
       ⊩B₂ .unwrap _ (liftSubstS _ _ ⊩Id₂ (liftSubstS _ _ ⊩A₂ ⊩σ))
         .proj₁)
      ⊩B₁[⇑⇑σ][t₁[σ],rfl]
      ⊩B₂[⇑⇑σ][t₂[σ],rfl]
      ⊩B₁[⇑⇑σ][v₁[σ],w₁[σ]]
      (irrelevance′ (PE.sym (doubleSubstComp B₂ _ _ _)) $
       ⊩B₂ .unwrap
         {σ = consSubst (consSubst σ (v₂ U.[ σ ])) (w₂ U.[ σ ])} _
         ( (⊩σ , ⊩v₂ _ ⊩σ .proj₁)
         , irrelevanceTerm′
             (Id-[σ]-[σ]≡Id-wk1-[σ,[σ]]-[σ] A₂ t₂ v₂)
             ⊩Id-t₂[σ]-v₂[σ] ⊩Id₂[σ,v₂[σ]] (⊩w₂ _ ⊩σ .proj₁)
         )
         .proj₁)
      (λ ⊩w ⊩w′ ⊩w≡w′ →
         ⊩ᵛ→≡→⊢[⇑⇑][,]≡[⇑⇑][,]
           ⊩B₁
           (irrelevanceTerm′
              (Id-[σ]-[σ]≡Id-wk1-[σ,[σ]]-[σ] A₁ t₁ v₁)
              ⊩Id-t₁[σ]-v₁[σ] ⊩Id₁[σ,v₁[σ]] ⊩w)
           (irrelevanceTerm′
              (Id-[σ]-[σ]≡Id-wk1-[σ,[σ]]-[σ] A₁ t₁ v₁)
              ⊩Id-t₁[σ]-v₁[σ] ⊩Id₁[σ,v₁[σ]] ⊩w′)
           (irrelevanceEqTerm′
              (Id-[σ]-[σ]≡Id-wk1-[σ,[σ]]-[σ] A₁ t₁ v₁)
              ⊩Id-t₁[σ]-v₁[σ] ⊩Id₁[σ,v₁[σ]] ⊩w≡w′))
      (λ ⊩t₁[σ]≡v₁[σ] ⊩w ⊩rfl≡w →
         case ⊩Id≡Id
                (PE.subst₂ (_ ⊢_∷_)
                   (PE.sym (wk1-tail t₁))
                   (PE.sym (wk1-tail A₁))
                   ⊢t₁[σ])
                (PE.subst (_ ⊢ _ ∷_)
                   (PE.sym (wk1-tail A₁))
                   ⊢t₁[σ])
                (irrelevanceEqR′ (PE.sym (wk1-tail A₁))
                   ⊩A₁[σ] (reflEq ⊩A₁[σ]))
                (PE.subst (_ ⊩⟨ _ ⟩ t₁ U.[ _ ] ≡_∷ _ / ⊩A₁[σ])
                   (PE.sym (wk1-tail t₁))
                   (reflEqTerm ⊩A₁[σ] (⊩t₁ _ ⊩σ .proj₁)))
                (symEqTerm ⊩A₁[σ] ⊩t₁[σ]≡v₁[σ]) of λ {
           ⊩Id-t₁[σ]-v₁[σ]≡Id-wk1-t₁[σ,t₁[σ]]-t₁[σ] →
         ⊩ᵛ→≡→≡→⊩[⇑⇑][,]≡[⇑⇑][,]
           ⊩B₁ ⊩B₁[⇑⇑σ][t₁[σ],rfl] ⊩t₁[σ]≡v₁[σ]
           (convTerm₁
              ⊩Id-t₁[σ]-v₁[σ] ⊩Id₁[σ,t₁[σ]]
              ⊩Id-t₁[σ]-v₁[σ]≡Id-wk1-t₁[σ,t₁[σ]]-t₁[σ]
              (⊩rfl′ ⊩t₁[σ]≡v₁[σ]))
           (irrelevanceTerm′
              (Id-[σ]-[σ]≡Id-wk1-[σ,[σ]]-[σ] A₁ t₁ v₁)
              ⊩Id-t₁[σ]-v₁[σ] ⊩Id₁[σ,v₁[σ]] ⊩w)
           (convEqTerm₁
              ⊩Id-t₁[σ]-v₁[σ] ⊩Id₁[σ,t₁[σ]]
              ⊩Id-t₁[σ]-v₁[σ]≡Id-wk1-t₁[σ,t₁[σ]]-t₁[σ]
              ⊩rfl≡w) })
      (λ ⊩w ⊩w′ ⊩w≡w′ →
         ⊩ᵛ→≡→⊢[⇑⇑][,]≡[⇑⇑][,] ⊩B₂
           (convTerm₁
              ⊩Id-t₂[σ]-v₂[σ] ⊩Id₂[σ,v₂[σ]]
              ⊩Id-t₂[σ]-v₂[σ]≡Id-wk1-t₂[σ,v₂[σ]]-v₂[σ]
              ⊩w)
           (irrelevanceTerm′
              (Id-[σ]-[σ]≡Id-wk1-[σ,[σ]]-[σ] A₂ t₂ v₂)
              ⊩Id-t₂[σ]-v₂[σ] ⊩Id₂[σ,v₂[σ]] ⊩w′)
           (convEqTerm₁
              ⊩Id-t₂[σ]-v₂[σ] ⊩Id₂[σ,v₂[σ]]
              ⊩Id-t₂[σ]-v₂[σ]≡Id-wk1-t₂[σ,v₂[σ]]-v₂[σ]
              ⊩w≡w′))
      (irrelevanceEq‴ PE.refl PE.refl
         (PE.cong (λ Id → Δ ∙ A₁ U.[ σ ] ∙ Id) $
          Id-wk1-wk1-0[⇑]≡ A₁ t₁)
         ⊩B₁[⇑⇑σ]′ ⊩B₁[⇑⇑σ] $
       ⊩B₁≡B₂ _ (liftSubstS _ _ ⊩Id₁ (liftSubstS _ _ ⊩A₁ ⊩σ)))
      (⊩ᵛ→≡→≡→≡→≡→≡→⊩[⇑⇑][,]≡[⇑⇑][,]
         (⊩A₁≡A₂ _ ⊩σ)
         (irrelevanceEq″
            (Id-[σ]-[σ]≡Id-wk1-[σ,[σ]]-[σ] A₁ t₁ t₂)
            (Id-[σ]-[σ]≡Id-wk1-[σ,[σ]]-[σ] A₂ t₂ t₂)
            (⊩Id ⊩A₁[σ] (⊩t₁ _ ⊩σ .proj₁) ⊩t₂[σ]′)
            (⊩Id₁ .unwrap _ (⊩σ , ⊩t₂[σ]′) .proj₁) $
          ⊩Id≡Id ⊢t₂[σ] ⊢t₂[σ] (⊩A₁≡A₂ _ ⊩σ) (⊩t₁≡t₂ _ ⊩σ)
            (reflEqTerm ⊩A₁[σ] ⊩t₂[σ]′))
         ⊩B₁ ⊩B₂ ⊩B₁≡B₂ ⊩B₁[⇑⇑σ][t₁[σ],rfl]
         (⊩t₁≡t₂ _ ⊩σ)
         (irrelevanceTerm′
            (Id-[σ]-[σ]≡Id-wk1-[σ,[σ]]-[σ] A₁ t₁ t₁)
            (⊩Id ⊩A₁[σ] (⊩t₁ _ ⊩σ .proj₁) (⊩t₁ _ ⊩σ .proj₁))
            ⊩Id₁[σ,t₁[σ]] ⊩rfl)
         (irrelevanceTerm′
            (Id-[σ]-[σ]≡Id-wk1-[σ,[σ]]-[σ] A₂ t₂ t₂)
            (⊩Id ⊩A₂[σ] (⊩t₂ _ ⊩σ .proj₁) (⊩t₂ _ ⊩σ .proj₁))
            ⊩Id₂[σ,t₂[σ]] ⊩rfl)
         (irrelevanceEqTerm′
            (Id-[σ]-[σ]≡Id-wk1-[σ,[σ]]-[σ] A₁ t₁ t₁)
            (⊩Id ⊩A₁[σ] (⊩t₁ _ ⊩σ .proj₁) (⊩t₁ _ ⊩σ .proj₁))
            ⊩Id₁[σ,t₁[σ]]
            (⊩rfl≡rfl (reflEqTerm ⊩A₁[σ] (⊩t₁ _ ⊩σ .proj₁)))))
      (λ ⊩w₂ ⊩w₁≡w₂ →
         ⊩ᵛ→≡→≡→≡→≡→≡→⊩[⇑⇑][,]≡[⇑⇑][,]
           (⊩A₁≡A₂ _ ⊩σ)
           (irrelevanceEq″
              (Id-[σ]-[σ]≡Id-wk1-[σ,[σ]]-[σ] A₁ t₁ v₂)
              (Id-[σ]-[σ]≡Id-wk1-[σ,[σ]]-[σ] A₂ t₂ v₂)
              (⊩Id ⊩A₁[σ] (⊩t₁ _ ⊩σ .proj₁) ⊩v₂[σ]′)
              (⊩Id₁ .unwrap _ (⊩σ , ⊩v₂[σ]′) .proj₁) $
          ⊩Id≡Id ⊢t₂[σ] (escapeTerm ⊩A₂[σ] (⊩v₂ _ ⊩σ .proj₁))
            (⊩A₁≡A₂ _ ⊩σ) (⊩t₁≡t₂ _ ⊩σ) (reflEqTerm ⊩A₁[σ] ⊩v₂[σ]′))
           ⊩B₁ ⊩B₂ ⊩B₁≡B₂ ⊩B₁[⇑⇑σ][v₁[σ],w₁[σ]]
           (⊩v₁≡v₂ _ ⊩σ)
           (irrelevanceTerm′
              (Id-[σ]-[σ]≡Id-wk1-[σ,[σ]]-[σ] A₁ t₁ v₁)
              (⊩Id ⊩A₁[σ] (⊩t₁ _ ⊩σ .proj₁) (⊩v₁ _ ⊩σ .proj₁))
              ⊩Id₁[σ,v₁[σ]] (⊩w₁ _ ⊩σ .proj₁))
           (irrelevanceTerm′
              (Id-[σ]-[σ]≡Id-wk1-[σ,[σ]]-[σ] A₂ t₂ v₂)
              (⊩Id ⊩A₂[σ] (⊩t₂ _ ⊩σ .proj₁) (⊩v₂ _ ⊩σ .proj₁))
              ⊩Id₂[σ,v₂[σ]] ⊩w₂)
           (irrelevanceEqTerm′
              (Id-[σ]-[σ]≡Id-wk1-[σ,[σ]]-[σ] A₁ t₁ v₁)
              (⊩Id ⊩A₁[σ] (⊩t₁ _ ⊩σ .proj₁) (⊩v₁ _ ⊩σ .proj₁))
              ⊩Id₁[σ,v₁[σ]] ⊩w₁≡w₂))
      (irrelevanceTerm′ ([,]-[]-commute B₁)
         ⊩B₁[t₁,rfl][σ] ⊩B₁[⇑⇑σ][t₁[σ],rfl]
         (⊩u₁ _ ⊩σ .proj₁))
      (irrelevanceTerm′ ([,]-[]-commute B₂)
         ⊩B₂[t₂,rfl][σ] ⊩B₂[⇑⇑σ][t₂[σ],rfl]
         (⊩u₂ _ ⊩σ .proj₁))
      (irrelevanceEqTerm′ ([,]-[]-commute B₁)
         ⊩B₁[t₁,rfl][σ] ⊩B₁[⇑⇑σ][t₁[σ],rfl]
         (⊩u₁≡u₂ _ ⊩σ))
      (⊩w₁ _ ⊩σ .proj₁)
      (⊩w₂ _ ⊩σ .proj₁)
      (⊩w₁≡w₂ _ ⊩σ) }}}}}}}}
