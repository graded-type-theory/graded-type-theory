------------------------------------------------------------------------
-- The quantity translation functions preserve various things related
-- to typing (given certain assumptions)
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Modality.Morphism
open import Graded.Modality.Morphism.Type-restrictions
open import Definition.Typed.Restrictions
open import Tools.Bool

module Definition.Typed.QuantityTranslation
  {a₁ a₂} {M₁ : Set a₁} {M₂ : Set a₂}
  {𝕄₁ : Modality M₁} {𝕄₂ : Modality M₂}
  (R₁ : Type-restrictions 𝕄₁)
  (R₂ : Type-restrictions 𝕄₂)
  (transparent : Bool)
  (tr tr-Σ : M₁ → M₂)
  (m : Is-morphism 𝕄₁ 𝕄₂ tr)
  (m-Σ : Is-Σ-morphism 𝕄₁ 𝕄₂ tr tr-Σ)
  (pres : Are-preserving-type-restrictions transparent R₁ R₂ tr tr-Σ)
  where

open Is-morphism m
open Is-Σ-morphism m-Σ
open Are-preserving-type-restrictions pres

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum using (inj₁; inj₂)

open import Definition.Typed
open import Definition.Typed.Inversion R₁
import Definition.Typed.Properties
import Definition.Typed.Substitution
open import Definition.Untyped
import Definition.Untyped.Allowed-literal
import Definition.Untyped.Erased
open import Definition.Untyped.QuantityTranslation transparent tr tr-Σ
open import Definition.Untyped.Quotient
import Definition.Untyped.Sup

open Modality-lemmas 𝕄₁ 𝕄₂

private
  module A₁  = Definition.Untyped.Allowed-literal R₁
  module A₂  = Definition.Untyped.Allowed-literal R₂
  module E₁  = Definition.Untyped.Erased 𝕄₁
  module E₂  = Definition.Untyped.Erased 𝕄₂
  module R₁  = Type-restrictions R₁
  module R₂  = Type-restrictions R₂
  module T₁  = Definition.Typed R₁
  module T₂  = Definition.Typed R₂
  module P₁  = Definition.Typed.Properties R₁
  module P₂  = Definition.Typed.Properties R₂
  module S₁  = Definition.Typed.Substitution R₁
  module S₂  = Definition.Typed.Substitution R₂
  module U₁  = Definition.Untyped M₁
  module U₂  = Definition.Untyped M₂
  module US₁ = Definition.Untyped.Sup R₁
  module US₂ = Definition.Untyped.Sup R₂

private variable
  n             : Nat
  x             : Fin _
  ∇ ∇′          : DCon _ _
  Δ             : Con _ _
  Γ             : Cons _ _ _
  A B t t₁ t₂ u : Term _ _
  l l₁ l₂       : Lvl _ _
  k             : Term-kind
  σ σ′          : Subst _ _ _
  p q           : M₁
  s             : Strength
  o             : Opacity _
  φ φ₁ φ₂       : Unfolding _

opaque

  -- Translation preserves Allowed-literal.

  tr-Term-Allowed-literal :
    R₁.Allowed-literal l → R₂.Allowed-literal (tr-Term l)
  tr-Term-Allowed-literal {l = ωᵘ+ m} =
    R₁.Allowed-literal (U₁.ωᵘ+ m)            ⇔⟨ A₁.Allowed-literal-ωᵘ+-⇔ ⟩→
    R₁.Omega-plus-allowed                    →⟨ Omega-plus-preserved ⟩
    R₂.Omega-plus-allowed                    ⇔˘⟨ A₂.Allowed-literal-ωᵘ+-⇔ ⟩→
    R₂.Allowed-literal (tr-Term (U₁.ωᵘ+ m))  □
  tr-Term-Allowed-literal {l = level t} =
    R₁.Allowed-literal (U₁.level t)                    ⇔⟨ A₁.Allowed-literal-level-⇔ ⟩→
    U₁.Level-literal t × ¬ R₁.Level-allowed            ⇔⟨ tr-Level-literal ×-cong-⇔ Level-allowed⇔ →-cong-⇔ id⇔ ⟩→
    U₂.Level-literal (tr-Term t) × ¬ R₂.Level-allowed  ⇔˘⟨ A₂.Allowed-literal-level-⇔ ⟩→
    R₂.Allowed-literal (U₂.level (tr-Term t))          □

opaque
  unfolding Definition.Untyped.Sup._supᵘₗ_

  -- The function tr-Term commutes with _supᵘₗ_.

  tr-Term-supᵘₗ :
    {l₁ l₂ : U₁.Term[ k ] n} →
    tr-Term l₁ US₂.supᵘₗ tr-Term l₂ PE.≡
    tr-Term (l₁ US₁.supᵘₗ l₂)
  tr-Term-supᵘₗ {l₁ = ωᵘ+ _}   {l₂ = ωᵘ+ _}   = PE.refl
  tr-Term-supᵘₗ {l₁ = ωᵘ+ _}   {l₂ = level _} = PE.refl
  tr-Term-supᵘₗ {l₁ = level _} {l₂ = ωᵘ+ _}   = PE.refl
  tr-Term-supᵘₗ {l₁ = level _} {l₂ = level _} =
    PE.cong level tr-Term-supᵘₗ
  tr-Term-supᵘₗ {k = tm} {l₁ = t₁} {l₂ = t₂}
    with R₁.Level-allowed? | R₂.Level-allowed?
  … | yes ok₁ | yes ok₂ =
    tr-Term t₁ US₂.supᵘₗ tr-Term t₂  ≡⟨ US₂.supᵘₗ≡supᵘ-tm ok₂ ⟩
    tr-Term t₁ supᵘ tr-Term t₂       ≡⟨⟩
    tr-Term (t₁ supᵘ t₂)             ≡˘⟨ PE.cong tr-Term $ US₁.supᵘₗ≡supᵘ-tm ok₁ ⟩
    tr-Term (t₁ US₁.supᵘₗ t₂)        ∎
  … | yes ok  | no not-ok =
    ⊥-elim (not-ok (Level-allowed⇔ .proj₁ ok))
  … | no not-ok | yes ok =
    ⊥-elim (not-ok (Level-allowed⇔ .proj₂ ok))
  … | no not-ok₁ | no not-ok₂ =
    tr-Term t₁ US₂.supᵘₗ tr-Term t₂  ≡⟨ US₂.supᵘₗ≡supᵘₗ′-tm not-ok₂ ⟩
    tr-Term t₁ U₂.supᵘₗ′ tr-Term t₂  ≡⟨ tr-Term-supᵘₗ′ ⟩
    tr-Term (t₁ U₁.supᵘₗ′ t₂)        ≡˘⟨ PE.cong tr-Term $ US₁.supᵘₗ≡supᵘₗ′-tm not-ok₁ ⟩
    tr-Term (t₁ US₁.supᵘₗ t₂)        ∎

opaque
  unfolding Definition.Untyped.Erased.Erased

  -- If []-cong is allowed (in the source modality), then tr-Term
  -- commutes with Erased.

  tr-Term-Erased :
    R₁.[]-cong-allowed s →
    E₂.Erased s (tr-Term l) (tr-Term A) PE.≡ tr-Term (E₁.Erased s l A)
  tr-Term-Erased {s} ok =
    PE.cong₄ Σ⟨ s ⟩_,_▷_▹_
      (PE.sym $ tr-Σ-𝟘-≡ (R₁.[]-cong→¬Trivial ok))
      (PE.sym $ tr-𝟘-≡ (R₁.[]-cong→¬Trivial ok))
      PE.refl
      (PE.cong (flip Lift _) tr-Term-wk)

opaque
  unfolding Definition.Untyped.Erased.[_]

  -- If []-cong is allowed (in the source modality), then tr-Term
  -- commutes with [_].

  tr-Term-[]′ :
    R₁.[]-cong-allowed s →
    E₂.[_] s (tr-Term t) PE.≡ tr-Term (E₁.[_] s t)
  tr-Term-[]′ ok =
    PE.sym $ PE.cong (λ p → prod _ p _ _) $
    tr-Σ-𝟘-≡ (R₁.[]-cong→¬Trivial ok)

opaque

  -- A combination of the previous two lemmas.

  tr-Term-Id-Erased-[]-[] :
    R₁.[]-cong-allowed s →
    Id (E₂.Erased s (tr-Term l) (tr-Term A)) (E₂.[_] s (tr-Term t))
      (E₂.[_] s (tr-Term u)) PE.≡
    tr-Term (Id (E₁.Erased s l A) (E₁.[_] s t) (E₁.[_] s u))
  tr-Term-Id-Erased-[]-[] ok =
    PE.cong₃ Id (tr-Term-Erased ok) (tr-Term-[]′ ok)
      (tr-Term-[]′ ok)

-- Preservation of _∷_∈_.

tr-∷∈ : x T₁.∷ A ∈ Δ → x T₂.∷ tr-Term A ∈ tr-Con Δ
tr-∷∈ here =
  PE.subst (_ T₂.∷_∈ _ ∙ tr-Term _) tr-Term-wk here
tr-∷∈ (there x) =
  PE.subst (_ T₂.∷_∈ _ ∙ tr-Term _) tr-Term-wk (there (tr-∷∈ x))

opaque
  unfolding Definition.Typed._⊔ᵒᵗ_

  -- Preservation for _⊔ᵒᵗ_.

  tr-⊔ᵒᵗ : φ₁ T₁.⊔ᵒᵗ φ₂ PE.≡ φ₁ T₂.⊔ᵒᵗ φ₂
  tr-⊔ᵒᵗ rewrite unfolding-mode-preserved = PE.refl

opaque
  unfolding Definition.Typed.Trans

  -- If definitions are not made transparent, then translation
  -- commutes with Trans φ.

  tr-Trans-not-transparent :
    ¬ T transparent →
    tr-DCon (T₁.Trans φ ∇) PE.≡ T₂.Trans φ (tr-DCon ∇)
  tr-Trans-not-transparent {∇ = ε} _ =
    PE.refl
  tr-Trans-not-transparent {∇ = _ ∙⟨ tra ⟩!} not-trp =
    PE.cong U₂._∙! (tr-Trans-not-transparent not-trp)
  tr-Trans-not-transparent
    {φ = φ ⁰} {∇ = ∇ ∙⟨ opa φ′ ⟩[ t ∷ A ]} not-trp =
    tr-DCon (T₁.Trans φ ∇)
      U₂.∙⟨ tr-Opacity (U₂.opa φ′) ⟩[ tr-Term t ∷ tr-Term A ]  ≡⟨ PE.cong U₂._∙! (tr-Trans-not-transparent not-trp) ⟩

    T₂.Trans φ (tr-DCon ∇)
      U₂.∙⟨ tr-Opacity (U₂.opa φ′) ⟩[ tr-Term t ∷ tr-Term A ]  ≡⟨ PE.cong (U₂._∙⟨_⟩! _) $
                                                                  tr-Opacity-not-transparent not-trp ⟩
    T₂.Trans φ (tr-DCon ∇)
      U₂.∙⟨ U₂.opa φ′ ⟩[ tr-Term t ∷ tr-Term A ]               ≡⟨⟩

    T₂.Trans (φ ⁰)
      (tr-DCon ∇ U₂.∙⟨ U₂.opa φ′ ⟩[ tr-Term t ∷ tr-Term A ])   ≡˘⟨ PE.cong (T₂.Trans _ ∘→ U₂._∙⟨_⟩! _) $
                                                                   tr-Opacity-not-transparent not-trp ⟩
    T₂.Trans (φ ⁰)
      (tr-DCon ∇ U₂.∙⟨ tr-Opacity (U₂.opa φ′) ⟩[
         tr-Term t ∷ tr-Term A ])                              ∎
  tr-Trans-not-transparent
    {φ = φ ¹} {∇ = ∇ ∙⟨ opa φ′ ⟩[ t ∷ A ]} not-trp =
    tr-DCon (T₁.Trans (φ T₁.⊔ᵒᵗ φ′) ∇)
      U₂.∙⟨ U₂.tra ⟩[ tr-Term t ∷ tr-Term A ]                 ≡⟨ PE.cong U₂._∙! (tr-Trans-not-transparent not-trp) ⟩

    T₂.Trans (φ T₁.⊔ᵒᵗ φ′) (tr-DCon ∇)
      U₂.∙⟨ U₂.tra ⟩[ tr-Term t ∷ tr-Term A ]                 ≡⟨ PE.cong (U₂._∙! ∘→ flip T₂.Trans _) tr-⊔ᵒᵗ ⟩

    T₂.Trans (φ T₂.⊔ᵒᵗ φ′) (tr-DCon ∇)
      U₂.∙⟨ U₂.tra ⟩[ tr-Term t ∷ tr-Term A ]                 ≡⟨⟩

    T₂.Trans (φ ¹)
      (tr-DCon ∇ U₂.∙⟨ U₂.opa φ′ ⟩[ tr-Term t ∷ tr-Term A ])  ≡˘⟨ PE.cong (T₂.Trans _ ∘→ U₂._∙⟨_⟩! _) $
                                                                  tr-Opacity-not-transparent not-trp ⟩
    T₂.Trans (φ ¹)
      (tr-DCon ∇ U₂.∙⟨ tr-Opacity (U₂.opa φ′) ⟩[
         tr-Term t ∷ tr-Term A ])                             ∎

opaque
  unfolding Definition.Typed.Trans

  -- If definitions are made transparent, then transparentisation is

  tr-Trans-transparent :
    T transparent →
    tr-DCon (T₁.Trans φ ∇) PE.≡ tr-DCon ∇
  tr-Trans-transparent {∇ = ε} _ =
    PE.refl
  tr-Trans-transparent {∇ = _ ∙⟨ tra ⟩!} trp =
    PE.cong U₂._∙! (tr-Trans-transparent trp)
  tr-Trans-transparent {φ = _ ⁰} {∇ = _ ∙⟨ opa _ ⟩!} trp =
    PE.cong U₂._∙! (tr-Trans-transparent trp)
  tr-Trans-transparent {φ = _ ¹} {∇ = _ ∙⟨ opa _ ⟩!} trp =
    PE.cong₂ U₂._∙⟨_⟩! (tr-Trans-transparent trp)
      (PE.sym (tr-Opacity-transparent trp))

mutual

  -- Preservation of »_.

  tr-» : T₁.» ∇ → T₂.» tr-DCon ∇
  tr-» ε                 = ε
  tr-» ∙ᵗ[ t ]           = ∙ᵗ[ tr-⊢∷ t ]
  tr-» ∙ᵒ⟨ ok ⟩[ t ∷ A ] with T? transparent
  … | yes trp =
    PE.subst T₂.»_
      (PE.cong₃ (_∙⟨_⟩[_∷_] _)
         (PE.cong (if_then _ else _) (PE.sym (T-true .proj₁ trp)))
         PE.refl PE.refl)
      ∙ᵗ[ PE.subst₃ T₂._⊢_∷_
            (PE.cong (_» _) (tr-Trans-transparent trp))
            PE.refl PE.refl $
          tr-⊢∷ t ]
  … | no not-trp =
    PE.subst T₂.»_
      (PE.cong₃ (_∙⟨_⟩[_∷_] _)
         (PE.cong (if_then _ else _) (PE.sym (¬-T .proj₁ not-trp)))
         PE.refl PE.refl) $
    ∙ᵒ⟨ Opacity-preserved not-trp ok
    ⟩[ PE.subst₃ T₂._⊢_∷_
         (PE.cong (_» _) (tr-Trans-not-transparent not-trp))
         PE.refl PE.refl $
       tr-⊢∷ t
    ∷ tr-⊢′ A
    ]

  -- Preservation of ⊢_.

  tr-⊢ : T₁.⊢ Γ → T₂.⊢ tr-Cons Γ
  tr-⊢ (ε ∇) = ε (tr-» ∇)
  tr-⊢ (∙ A) = ∙ tr-⊢′ A

  -- Preservation of _⊢_.

  tr-⊢′ : Γ T₁.⊢ A → tr-Cons Γ T₂.⊢ tr-Term A
  tr-⊢′ (Levelⱼ ok Γ) =
    P₂.Levelⱼ′
      (Level-allowed⇔ .proj₁ (R₁.Level-allowed⇔⊎ .proj₂ (inj₂ ok)))
      (tr-⊢ Γ)
  tr-⊢′ (Liftⱼ l A) =
    Liftⱼ (tr-⊢∷L l) (tr-⊢′ A)
  tr-⊢′ (ΠΣⱼ P ok) =
    ΠΣⱼ (tr-⊢′ P) (ΠΣ-preserved ok)
  tr-⊢′ (Idⱼ _ t u) =
    P₂.Idⱼ′ (tr-⊢∷ t) (tr-⊢∷ u)
  tr-⊢′ (univ A) =
    univ (tr-⊢∷ A)
  tr-⊢′ (Quot ok ⊢B) =
    Quot (Quot-preserved ok)
      (PE.subst (flip T₂._⊢_ _) tr-Cons-Quot-rel-Cons $
       tr-⊢′ ⊢B)

  -- Preservation of _⊢_∷_.

  tr-⊢∷ : Γ T₁.⊢ t ∷ A → tr-Cons Γ T₂.⊢ tr-Term t ∷ tr-Term A
  tr-⊢∷ (defn Γ α PE.refl) =
    defn (tr-⊢ Γ) (tr-↦ α) (PE.sym tr-Term-wk)
  tr-⊢∷ (Levelⱼ Γ ok) =
    Levelⱼ (tr-⊢ Γ) (Level-is-small-preserved ok)
  tr-⊢∷ (zeroᵘⱼ ok Γ) =
    zeroᵘⱼ (Level-allowed⇔ .proj₁ ok) (tr-⊢ Γ)
  tr-⊢∷ (sucᵘⱼ t) =
    sucᵘⱼ (tr-⊢∷ t)
  tr-⊢∷ (supᵘⱼ t u) =
    supᵘⱼ (tr-⊢∷ t) (tr-⊢∷ u)
  tr-⊢∷ (Liftⱼ t u A) =
    PE.subst (T₂._⊢_∷_ _ _) (PE.cong U tr-Term-supᵘₗ) $
    Liftⱼ (tr-⊢∷L t) (tr-⊢∷L u) (tr-⊢∷ A)
  tr-⊢∷ (liftⱼ t A u) =
    liftⱼ (tr-⊢∷L t) (tr-⊢′ A) (tr-⊢∷ u)
  tr-⊢∷ (lowerⱼ t) =
    lowerⱼ (tr-⊢∷ t)
  tr-⊢∷ (Uⱼ l) =
    PE.subst (T₂._⊢_∷_ _ _) (PE.cong U (PE.sym tr-Term-1ᵘ+)) $
    Uⱼ (tr-⊢∷L l)
  tr-⊢∷ (ΠΣⱼ {l = l} ⊢l A P ok) =
    ΠΣⱼ (tr-⊢∷L ⊢l) (tr-⊢∷ A)
      (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-wk {t = U l})) (tr-⊢∷ P))
      (ΠΣ-preserved ok)
  tr-⊢∷ (ℕⱼ Γ) =
    ℕⱼ (tr-⊢ Γ)
  tr-⊢∷ (Emptyⱼ Γ) =
    Emptyⱼ (tr-⊢ Γ)
  tr-⊢∷ (Unitⱼ Γ ok) =
    Unitⱼ (tr-⊢ Γ) (Unit-preserved ok)
  tr-⊢∷ (var Γ x) =
    var (tr-⊢ Γ) (tr-∷∈ x)
  tr-⊢∷ (lamⱼ _ t ok) =
    P₂.lamⱼ′ (ΠΣ-preserved ok) (tr-⊢∷ t)
  tr-⊢∷ (_∘ⱼ_ {G = P} t u) =
    PE.subst (_ T₂.⊢ _ ∷_) (tr-Term-[] P) (tr-⊢∷ t ∘ⱼ tr-⊢∷ u)
  tr-⊢∷ (prodⱼ {G = P} ⊢P t u ok) =
    prodⱼ (tr-⊢′ ⊢P) (tr-⊢∷ t)
      (PE.subst (_ T₂.⊢ _ ∷_) (PE.sym (tr-Term-[] P)) (tr-⊢∷ u))
      (ΠΣ-preserved ok)
  tr-⊢∷ (fstⱼ P t) =
    fstⱼ (tr-⊢′ P) (tr-⊢∷ t)
  tr-⊢∷ (sndⱼ {G = P} ⊢P t) =
    PE.subst (_ T₂.⊢ _ ∷_) (tr-Term-[] P)
      (sndⱼ (tr-⊢′ ⊢P) (tr-⊢∷ t))
  tr-⊢∷ (prodrecⱼ {A = Q} ⊢Q t u) =
    PE.subst (T₂._⊢_∷_ _ _) (tr-Term-[] Q)
      (prodrecⱼ (tr-⊢′ ⊢Q) (tr-⊢∷ t)
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[]↑ Q)) (tr-⊢∷ u)))
  tr-⊢∷ (zeroⱼ Γ) =
    zeroⱼ (tr-⊢ Γ)
  tr-⊢∷ (sucⱼ t) =
    sucⱼ (tr-⊢∷ t)
  tr-⊢∷ (natrecⱼ {A = P} z s n) =
    PE.subst (T₂._⊢_∷_ _ _) (tr-Term-[] P)
      (natrecⱼ
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[] P)) (tr-⊢∷ z))
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[]↑ P))
            (tr-⊢∷ s))
         (tr-⊢∷ n))
  tr-⊢∷ (emptyrecⱼ A e) =
    emptyrecⱼ (tr-⊢′ A) (tr-⊢∷ e)
  tr-⊢∷ (starⱼ Γ ok) =
    starⱼ (tr-⊢ Γ) (Unit-preserved ok)
  tr-⊢∷ (unitrecⱼ {A = A} ⊢A t u) =
    PE.subst (T₂._⊢_∷_ _ _) (tr-Term-[] A)
      (unitrecⱼ (tr-⊢′ ⊢A) (tr-⊢∷ t)
        (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[] A)) (tr-⊢∷ u)))
  tr-⊢∷ (Idⱼ A t u) =
    Idⱼ (tr-⊢∷ A) (tr-⊢∷ t) (tr-⊢∷ u)
  tr-⊢∷ (rflⱼ t) =
    rflⱼ (tr-⊢∷ t)
  tr-⊢∷ (Jⱼ {B} _ ⊢B u _ w) =
    PE.subst (T₂._⊢_∷_ _ _) (tr-Term-[,] B) $
    P₂.Jⱼ′
      (PE.subst (flip T₂._⊢_ _)
         (PE.cong (_»_ _) $
          PE.cong (_∙_ _) $
          PE.cong₂ (λ A t → Id A t (var x0))
            (PE.sym tr-Term-wk)
            (PE.sym tr-Term-wk)) $
       tr-⊢′ ⊢B)
      (PE.subst (T₂._⊢_∷_ _ _) (PE.sym $ tr-Term-[,] B) $
       tr-⊢∷ u)
      (tr-⊢∷ w)
  tr-⊢∷ (Kⱼ {B} ⊢B u v ok) =
    PE.subst (T₂._⊢_∷_ _ _) (tr-Term-[] B) $
    Kⱼ (tr-⊢′ ⊢B)
      (PE.subst (T₂._⊢_∷_ _ _) (PE.sym $ tr-Term-[] B) $
       tr-⊢∷ u)
      (tr-⊢∷ v) (K-preserved ok)
  tr-⊢∷ ([]-congⱼ l _ _ _ v ok) =
    PE.subst (T₂._⊢_∷_ _ _) (tr-Term-Id-Erased-[]-[] ok) $
    P₂.[]-congⱼ′ ([]-cong-preserved ok) (tr-⊢∷L l) (tr-⊢∷ v)
  tr-⊢∷ (Quot {l} ok _ ⊢A ⊢B) =
    P₂.⊢Quot (Quot-preserved ok) (tr-⊢∷ ⊢A)
      (PE.subst₃ T₂._⊢_∷_ tr-Cons-Quot-rel-Cons PE.refl
         (PE.sym (tr-Term-wk {t = U l})) $
       tr-⊢∷ ⊢B)
  tr-⊢∷ (class ⊢Q ⊢t) =
    class (tr-⊢′ ⊢Q) (tr-⊢∷ ⊢t)
  tr-⊢∷ (resp {B} ⊢Q ⊢t ⊢u ⊢v) =
    resp (tr-⊢′ ⊢Q) (tr-⊢∷ ⊢t) (tr-⊢∷ ⊢u)
      (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[,] B)) $
       tr-⊢∷ ⊢v)
  tr-⊢∷ (set _ _ _ ⊢v ⊢w) =
    P₂.⊢set (tr-⊢∷ ⊢v) (tr-⊢∷ ⊢w)
  tr-⊢∷ (qrec {C} ⊢C ⊢t ⊢u ⊢v ⊢w) =
    let ok , _ = inversion-Is-set-Cons ⊢v in
    PE.subst (T₂._⊢_∷_ _ _) (tr-Term-[] C) $
    qrec (tr-⊢′ ⊢C)
      (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[]↑ C)) $
       tr-⊢∷ ⊢t)
      (PE.subst₃ T₂._⊢_∷_ tr-Cons-Resp-Cons PE.refl
         (tr-Term-Resp-type (Quot-allowed→tr-𝟘≡𝟘 ok) tr-ω) $
       tr-⊢∷ ⊢u)
      (PE.subst₃ T₂._⊢_∷_ tr-Cons-Is-set-Cons PE.refl
         tr-Term-Is-set-type $
       tr-⊢∷ ⊢v)
      (tr-⊢∷ ⊢w)
  tr-⊢∷ (conv t A≡B) =
    conv (tr-⊢∷ t) (tr-⊢≡ A≡B)

  -- Preservation of _⊢_∷Level.

  tr-⊢∷L : Γ T₁.⊢ l ∷Level → tr-Cons Γ T₂.⊢ tr-Term l ∷Level
  tr-⊢∷L (term ok ⊢l) =
    term (Level-allowed⇔ .proj₁ ok) (tr-⊢∷ ⊢l)
  tr-⊢∷L (literal ok ⊢Γ) =
    literal (tr-Term-Allowed-literal ok) (tr-⊢ ⊢Γ)

  -- Preservation of _⊢_≡_.

  tr-⊢≡ : Γ T₁.⊢ A ≡ B → tr-Cons Γ T₂.⊢ tr-Term A ≡ tr-Term B
  tr-⊢≡ (U-cong l₁≡l₂) =
    U-cong (tr-⊢≡∷ l₁≡l₂)
  tr-⊢≡ (Lift-cong l₁≡l₂ A≡B) =
    Lift-cong (tr-⊢≡∷L l₁≡l₂) (tr-⊢≡ A≡B)
  tr-⊢≡ (univ A≡B) =
    univ (tr-⊢≡∷ A≡B)
  tr-⊢≡ (refl A) =
    refl (tr-⊢′ A)
  tr-⊢≡ (sym A≡B) =
    sym (tr-⊢≡ A≡B)
  tr-⊢≡ (trans A≡B C≡D) =
    trans (tr-⊢≡ A≡B) (tr-⊢≡ C≡D)
  tr-⊢≡ (ΠΣ-cong {b} A≡B C≡D ok) =
    ΠΣ-cong (tr-⊢≡ A≡B) (tr-⊢≡ C≡D) (ΠΣ-preserved ok)
  tr-⊢≡ (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) =
    Id-cong (tr-⊢≡ A₁≡A₂) (tr-⊢≡∷ t₁≡t₂) (tr-⊢≡∷ u₁≡u₂)
  tr-⊢≡ (Quot-cong ok A₁≡A₂ B₁≡B₂) =
    Quot-cong (Quot-preserved ok) (tr-⊢≡ A₁≡A₂)
      (PE.subst₃ T₂._⊢_≡_ tr-Cons-Quot-rel-Cons PE.refl PE.refl $
       tr-⊢≡ B₁≡B₂)

  -- Preservation of _⊢_≡_∷_.

  tr-⊢≡∷ :
    Γ T₁.⊢ t ≡ u ∷ A → tr-Cons Γ T₂.⊢ tr-Term t ≡ tr-Term u ∷ tr-Term A
  tr-⊢≡∷ (refl t) =
    refl (tr-⊢∷ t)
  tr-⊢≡∷ (sym _ t≡u) =
    P₂.sym′ (tr-⊢≡∷ t≡u)
  tr-⊢≡∷ (trans t≡u u≡v) =
    trans (tr-⊢≡∷ t≡u) (tr-⊢≡∷ u≡v)
  tr-⊢≡∷ (conv t≡u A≡B) =
    conv (tr-⊢≡∷ t≡u) (tr-⊢≡ A≡B)
  tr-⊢≡∷ (δ-red Γ α PE.refl PE.refl) =
    δ-red (tr-⊢ Γ) (tr-↦∷ α) (PE.sym tr-Term-wk) (PE.sym tr-Term-wk)
  tr-⊢≡∷ (sucᵘ-cong t≡t') =
    sucᵘ-cong (tr-⊢≡∷ t≡t')
  tr-⊢≡∷ (supᵘ-cong t≡t' u≡u') =
    supᵘ-cong (tr-⊢≡∷ t≡t') (tr-⊢≡∷ u≡u')
  tr-⊢≡∷ (supᵘ-zeroˡ t) =
    supᵘ-zeroˡ (tr-⊢∷ t)
  tr-⊢≡∷ (supᵘ-sucᵘ t u) =
    supᵘ-sucᵘ (tr-⊢∷ t) (tr-⊢∷ u)
  tr-⊢≡∷ (supᵘ-assoc t u v) =
    supᵘ-assoc (tr-⊢∷ t) (tr-⊢∷ u) (tr-⊢∷ v)
  tr-⊢≡∷ (supᵘ-comm t u) =
    supᵘ-comm (tr-⊢∷ t) (tr-⊢∷ u)
  tr-⊢≡∷ (supᵘ-idem t) =
    supᵘ-idem (tr-⊢∷ t)
  tr-⊢≡∷ (supᵘ-sub t) =
    supᵘ-sub (tr-⊢∷ t)
  tr-⊢≡∷ (U-cong t≡u) =
    U-cong (tr-⊢≡∷ t≡u)
  tr-⊢≡∷ (Lift-cong _ _ u≡u' A≡B) =
    PE.subst (T₂._⊢_≡_∷_ _ _ _) (PE.cong U tr-Term-supᵘₗ) $
    P₂.Lift-cong′ (tr-⊢≡∷L u≡u') (tr-⊢≡∷ A≡B)
  tr-⊢≡∷ (lower-cong t≡u) =
    lower-cong (tr-⊢≡∷ t≡u)
  tr-⊢≡∷ (Lift-β A u) =
    Lift-β (tr-⊢′ A) (tr-⊢∷ u)
  tr-⊢≡∷ (Lift-η l A t u lt≡lu) =
    Lift-η (tr-⊢∷L l) (tr-⊢′ A) (tr-⊢∷ t) (tr-⊢∷ u) (tr-⊢≡∷ lt≡lu)
  tr-⊢≡∷ (ΠΣ-cong {l = l} ⊢l A≡B C≡D ok) =
    ΠΣ-cong (tr-⊢∷L ⊢l) (tr-⊢≡∷ A≡B)
      (PE.subst (T₂._⊢_≡_∷_ _ _ _) (PE.sym (tr-Term-wk {t = U l})) (tr-⊢≡∷ C≡D))
      (ΠΣ-preserved ok)
  tr-⊢≡∷ (app-cong {G = P} t≡u v≡w) =
    PE.subst (T₂._⊢_≡_∷_ _ _ _) (tr-Term-[] P)
      (app-cong (tr-⊢≡∷ t≡u) (tr-⊢≡∷ v≡w))
  tr-⊢≡∷ (β-red {B = P} {t} ⊢P ⊢t u PE.refl ok) =
    PE.subst₂ (T₂._⊢_≡_∷_ _ _)
      (tr-Term-[] t)
      (tr-Term-[] P)
      (β-red (tr-⊢′ ⊢P) (tr-⊢∷ ⊢t) (tr-⊢∷ u) PE.refl (ΠΣ-preserved ok))
  tr-⊢≡∷ {Γ} (η-eq {F = A} {G = P} _ t u t≡u _) =
    P₂.η-eq′ (tr-⊢∷ t) (tr-⊢∷ u)
      (PE.subst₃ (T₂._⊢_≡_∷_ _)
         (PE.sym (PE.cong (_∘⟨ _ ⟩ _ ) tr-Term-wk))
         (PE.sym (PE.cong (_∘⟨ _ ⟩ _ ) tr-Term-wk))
         PE.refl
         (tr-⊢≡∷ t≡u))
  tr-⊢≡∷ (fst-cong P t≡u) =
    fst-cong (tr-⊢′ P) (tr-⊢≡∷ t≡u)
  tr-⊢≡∷ (snd-cong {G = P} ⊢P t≡u) =
    PE.subst (T₂._⊢_≡_∷_ _ _ _) (tr-Term-[] P)
      (snd-cong (tr-⊢′ ⊢P) (tr-⊢≡∷ t≡u))
  tr-⊢≡∷ (prod-cong {G = P} {k = s} ⊢P t≡u v≡w ok) =
    prod-cong (tr-⊢′ ⊢P) (tr-⊢≡∷ t≡u)
      (PE.subst (T₂._⊢_≡_∷_ _ _ _) (PE.sym (tr-Term-[] P)) (tr-⊢≡∷ v≡w))
      (ΠΣ-preserved ok)
  tr-⊢≡∷ (Σ-β₁ {G = P} ⊢P t u PE.refl ok) =
    Σ-β₁ (tr-⊢′ ⊢P) (tr-⊢∷ t)
      (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[] P)) (tr-⊢∷ u))
      PE.refl (ΠΣ-preserved ok)
  tr-⊢≡∷ (Σ-β₂ {G = P} ⊢P t u PE.refl ok) =
    PE.subst (T₂._⊢_≡_∷_ _ _ _) (tr-Term-[] P)
      (Σ-β₂ (tr-⊢′ ⊢P) (tr-⊢∷ t)
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[] P)) (tr-⊢∷ u))
         PE.refl (ΠΣ-preserved ok))
  tr-⊢≡∷ (Σ-η {G = P} _ t u t₁≡u₁ t₂≡u₂ _) =
    P₂.Σ-η′ (tr-⊢∷ t) (tr-⊢∷ u) (tr-⊢≡∷ t₁≡u₁)
      (PE.subst (T₂._⊢_≡_∷_ _ _ _) (PE.sym (tr-Term-[] P))
         (tr-⊢≡∷ t₂≡u₂))
  tr-⊢≡∷ (prodrec-cong {A = Q} Q≡R t≡u v≡w) =
    PE.subst (T₂._⊢_≡_∷_ _ _ _) (tr-Term-[] Q)
      (prodrec-cong (tr-⊢≡ Q≡R) (tr-⊢≡∷ t≡u)
         (PE.subst (T₂._⊢_≡_∷_ _ _ _) (PE.sym (tr-Term-[]↑ Q))
            (tr-⊢≡∷ v≡w)))
  tr-⊢≡∷
    (prodrec-β {G = P} {A = Q} {u = v} ⊢Q t u ⊢v PE.refl) =
    PE.subst₂ (T₂._⊢_≡_∷_ _ _) (tr-Term-[,] v) (tr-Term-[] Q)
      (prodrec-β (tr-⊢′ ⊢Q) (tr-⊢∷ t)
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[] P)) (tr-⊢∷ u))
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[]↑ Q))
            (tr-⊢∷ ⊢v))
         PE.refl)
  tr-⊢≡∷ (suc-cong t≡u) =
    suc-cong (tr-⊢≡∷ t≡u)
  tr-⊢≡∷ (natrec-cong {A = P} P≡P′ z≡z′ s≡s′ n≡n′) =
    PE.subst (T₂._⊢_≡_∷_ _ _ _) (tr-Term-[] P)
      (natrec-cong (tr-⊢≡ P≡P′)
         (PE.subst (T₂._⊢_≡_∷_ _ _ _) (PE.sym (tr-Term-[] P))
            (tr-⊢≡∷ z≡z′))
         (PE.subst (T₂._⊢_≡_∷_ _ _ _) (PE.sym (tr-Term-[]↑ P))
            (tr-⊢≡∷ s≡s′))
         (tr-⊢≡∷ n≡n′))
  tr-⊢≡∷ (natrec-zero {A = P} z s) =
    PE.subst (T₂._⊢_≡_∷_ _ _ _)
      (tr-Term-[] P)
      (natrec-zero
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[] P)) (tr-⊢∷ z))
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[]↑ P)) (tr-⊢∷ s)))
  tr-⊢≡∷ (natrec-suc {A = P} {s} z ⊢s n) =
    PE.subst₂ (T₂._⊢_≡_∷_ _ _) (tr-Term-[,] s) (tr-Term-[] P)
      (natrec-suc
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[] P)) (tr-⊢∷ z))
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[]↑ P)) (tr-⊢∷ ⊢s))
         (tr-⊢∷ n))
  tr-⊢≡∷ (emptyrec-cong A≡B t≡u) =
    emptyrec-cong (tr-⊢≡ A≡B) (tr-⊢≡∷ t≡u)
  tr-⊢≡∷ (unitrec-cong {A = A} A≡A′ t≡t′ u≡u′ _) =
    PE.subst (T₂._⊢_≡_∷_ _ _ _) (tr-Term-[] A)
      (P₂.unitrec-cong′ (tr-⊢≡ A≡A′) (tr-⊢≡∷ t≡t′)
         (PE.subst (T₂._⊢_≡_∷_ _ _ _) (PE.sym (tr-Term-[] A))
            (tr-⊢≡∷ u≡u′)))
  tr-⊢≡∷ (unitrec-β {A} ⊢A u _) =
    PE.subst (T₂._⊢_≡_∷_ _ _ _) (tr-Term-[] A)
      (P₂.unitrec-β-≡ (tr-⊢′ ⊢A)
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[] A)) (tr-⊢∷ u)))
  tr-⊢≡∷ (unitrec-β-η {A} ⊢A t u ok) =
    PE.subst (T₂._⊢_≡_∷_ _ _ _) (tr-Term-[] A)
      (unitrec-β-η (tr-⊢′ ⊢A) (tr-⊢∷ t)
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[] A)) (tr-⊢∷ u))
         (Unitʷ-η-preserved ok))
  tr-⊢≡∷ (η-unit t u ok) =
    η-unit (tr-⊢∷ t) (tr-⊢∷ u) $
    case ok of λ where
       (inj₁ ok) → inj₁ ok
       (inj₂ ok) → inj₂ (Unitʷ-η-preserved ok)
  tr-⊢≡∷ (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) =
    Id-cong (tr-⊢≡∷ A₁≡A₂) (tr-⊢≡∷ t₁≡t₂) (tr-⊢≡∷ u₁≡u₂)
  tr-⊢≡∷ (J-cong {B₁} {B₂} A₁≡A₂ _ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁≡w₂) =
    PE.subst (T₂._⊢_≡_∷_ _ _ _) (tr-Term-[,] B₁) $
    P₂.J-cong′ (tr-⊢≡ A₁≡A₂) (tr-⊢≡∷ t₁≡t₂)
      (PE.subst₃ T₂._⊢_≡_
         (PE.cong (_»_ _) $
          PE.cong (_∙_ _) $
          PE.cong₂ (λ A t → Id A t (var x0))
            (PE.sym tr-Term-wk)
            (PE.sym tr-Term-wk))
         PE.refl PE.refl $
       tr-⊢≡ B₁≡B₂)
      (PE.subst (T₂._⊢_≡_∷_ _ _ _) (PE.sym $ tr-Term-[,] B₁) $
       tr-⊢≡∷ u₁≡u₂)
      (tr-⊢≡∷ v₁≡v₂) (tr-⊢≡∷ w₁≡w₂)
  tr-⊢≡∷ (K-cong {B₁} A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ ok) =
    PE.subst (T₂._⊢_≡_∷_ _ _ _) (tr-Term-[] B₁) $
    K-cong (tr-⊢≡ A₁≡A₂) (tr-⊢≡∷ t₁≡t₂) (tr-⊢≡ B₁≡B₂)
      (PE.subst (T₂._⊢_≡_∷_ _ _ _) (PE.sym $ tr-Term-[] B₁) $
       tr-⊢≡∷ u₁≡u₂)
      (tr-⊢≡∷ v₁≡v₂) (K-preserved ok)
  tr-⊢≡∷ ([]-cong-cong l₁≡l₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ ok) =
    PE.subst (T₂._⊢_≡_∷_ _ _ _) (tr-Term-Id-Erased-[]-[] ok) $
    []-cong-cong (tr-⊢≡∷L l₁≡l₂) (tr-⊢≡ A₁≡A₂) (tr-⊢≡∷ t₁≡t₂)
      (tr-⊢≡∷ u₁≡u₂) (tr-⊢≡∷ v₁≡v₂) ([]-cong-preserved ok)
  tr-⊢≡∷ (J-β {B} t ⊢B u PE.refl) =
    PE.subst (T₂._⊢_≡_∷_ _ _ _) (tr-Term-[,] B) $
    P₂.J-β-≡ (tr-⊢∷ t)
      (PE.subst (flip T₂._⊢_ _)
         (PE.cong (_»_ _) $
          PE.cong (_∙_ _) $
          PE.cong₂ (λ A t → Id A t (var x0))
            (PE.sym tr-Term-wk)
            (PE.sym tr-Term-wk)) $
       tr-⊢′ ⊢B)
      (PE.subst (T₂._⊢_∷_ _ _) (PE.sym $ tr-Term-[,] B) $
       tr-⊢∷ u)
  tr-⊢≡∷ (K-β {B} ⊢B u ok) =
    PE.subst (T₂._⊢_≡_∷_ _ _ _) (tr-Term-[] B) $
    K-β (tr-⊢′ ⊢B)
      (PE.subst (T₂._⊢_∷_ _ _) (PE.sym $ tr-Term-[] B) $
       tr-⊢∷ u)
      (K-preserved ok)
  tr-⊢≡∷ ([]-cong-β l t PE.refl ok) =
    PE.subst (T₂._⊢_≡_∷_ _ _ _) (tr-Term-Id-Erased-[]-[] ok) $
    []-cong-β (tr-⊢∷L l) (tr-⊢∷ t) PE.refl
      ([]-cong-preserved ok)
  tr-⊢≡∷ (equality-reflection ok _ v) =
    P₂.equality-reflection′ (Equality-reflection-preserved ok) (tr-⊢∷ v)
  tr-⊢≡∷ (Quot-cong {l} ok _ A₁≡A₂ B₁≡B₂) =
    P₂.Quot-cong′ (Quot-preserved ok) (tr-⊢≡∷ A₁≡A₂)
      (PE.subst₄ T₂._⊢_≡_∷_ tr-Cons-Quot-rel-Cons PE.refl PE.refl
         (PE.sym (tr-Term-wk {t = U l})) $
       tr-⊢≡∷ B₁≡B₂)
  tr-⊢≡∷ (class-cong ⊢Q t₁≡t₂) =
    class-cong (tr-⊢′ ⊢Q) (tr-⊢≡∷ t₁≡t₂)
  tr-⊢≡∷ (resp-cong {B₁} ok A₁≡A₂ B₁≡B₂ t₁≡t₂ u₁≡u₂ v₁≡v₂) =
    resp-cong (Quot-preserved ok) (tr-⊢≡ A₁≡A₂)
      (PE.subst₃ T₂._⊢_≡_ tr-Cons-Quot-rel-Cons PE.refl PE.refl $
       tr-⊢≡ B₁≡B₂)
      (tr-⊢≡∷ t₁≡t₂) (tr-⊢≡∷ u₁≡u₂)
      (PE.subst (T₂._⊢_≡_∷_ _ _ _) (PE.sym (tr-Term-[,] B₁)) $
       tr-⊢≡∷ v₁≡v₂)
  tr-⊢≡∷ (set-cong A₁≡A₂ B₁≡B₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ w₁≡w₂) =
    set-cong (tr-⊢≡ A₁≡A₂)
      (PE.subst₃ T₂._⊢_≡_ tr-Cons-Quot-rel-Cons PE.refl PE.refl $
       tr-⊢≡ B₁≡B₂)
      (tr-⊢≡∷ t₁≡t₂) (tr-⊢≡∷ u₁≡u₂) (tr-⊢≡∷ v₁≡v₂) (tr-⊢≡∷ w₁≡w₂)
  tr-⊢≡∷ (qrec-cong {C₁} C₁≡C₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ w₁≡w₂) =
    let ok , _ = inversion-Is-set-Cons v₁≡v₂ in
    PE.subst (T₂._⊢_≡_∷_ _ _ _) (tr-Term-[] C₁) $
    qrec-cong (tr-⊢≡ C₁≡C₂)
      (PE.subst (T₂._⊢_≡_∷_ _ _ _) (PE.sym (tr-Term-[]↑ C₁)) $
       tr-⊢≡∷ t₁≡t₂)
      (PE.subst₄ T₂._⊢_≡_∷_ tr-Cons-Resp-Cons PE.refl PE.refl
         (tr-Term-Resp-type (Quot-allowed→tr-𝟘≡𝟘 ok) tr-ω) $
       tr-⊢≡∷ u₁≡u₂)
      (PE.subst₄ T₂._⊢_≡_∷_ tr-Cons-Is-set-Cons PE.refl PE.refl
         tr-Term-Is-set-type $
       tr-⊢≡∷ v₁≡v₂)
      (tr-⊢≡∷ w₁≡w₂)
  tr-⊢≡∷ (qrec-β {C} {t} ⊢C ⊢t ⊢u ⊢v ⊢w) =
    let ok , _ = inversion-Is-set-Cons ⊢v in
    PE.subst₂ (T₂._⊢_≡_∷_ _ _) (tr-Term-[] t) (tr-Term-[] C) $
    qrec-β (tr-⊢′ ⊢C)
      (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[]↑ C)) $
       tr-⊢∷ ⊢t)
      (PE.subst₃ T₂._⊢_∷_ tr-Cons-Resp-Cons PE.refl
         (tr-Term-Resp-type (Quot-allowed→tr-𝟘≡𝟘 ok) tr-ω) $
       tr-⊢∷ ⊢u)
      (PE.subst₃ T₂._⊢_∷_ tr-Cons-Is-set-Cons PE.refl
         tr-Term-Is-set-type $
       tr-⊢∷ ⊢v)
      (tr-⊢∷ ⊢w)

  -- Preservation of _⊢_≡_∷Level.

  tr-⊢≡∷L :
    Γ T₁.⊢ l₁ ≡ l₂ ∷Level →
    tr-Cons Γ T₂.⊢ tr-Term l₁ ≡ tr-Term l₂ ∷Level
  tr-⊢≡∷L (term ok l₁≡l₂) =
    term (Level-allowed⇔ .proj₁ ok) (tr-⊢≡∷ l₁≡l₂)
  tr-⊢≡∷L (literal ok ⊢Γ) =
    literal (tr-Term-Allowed-literal ok) (tr-⊢ ⊢Γ)

-- Preservation of _⊢ˢ_∷_.

tr-⊢ˢ∷ : Γ S₁.⊢ˢ σ ∷ Δ → tr-Cons Γ S₂.⊢ˢ tr-Subst σ ∷ tr-Con Δ
tr-⊢ˢ∷ S₁.id                     = S₂.id
tr-⊢ˢ∷ (S₁._,_ {A} ⊢ˢtail ⊢head) =
  tr-⊢ˢ∷ ⊢ˢtail S₂.,
  PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-subst A)) (tr-⊢∷ ⊢head)

-- Preservation of _⊢ˢ_≡_∷_.

tr-⊢ˢ≡∷ :
  Γ S₁.⊢ˢ σ ≡ σ′ ∷ Δ →
  tr-Cons Γ S₂.⊢ˢ tr-Subst σ ≡ tr-Subst σ′ ∷ tr-Con Δ
tr-⊢ˢ≡∷ S₁.id                       = S₂.id
tr-⊢ˢ≡∷ (S₁._,_ {A} ⊢ˢtail≡ ⊢head≡) =
  tr-⊢ˢ≡∷ ⊢ˢtail≡ S₂.,
  PE.subst (T₂._⊢_≡_∷_ _ _ _) (PE.sym (tr-Term-subst A)) (tr-⊢≡∷ ⊢head≡)

opaque

  -- Preservation of _⊢ˢʷ_∷_.

  tr-⊢ˢʷ∷ : Γ S₁.⊢ˢʷ σ ∷ Δ → tr-Cons Γ S₂.⊢ˢʷ tr-Subst σ ∷ tr-Con Δ
  tr-⊢ˢʷ∷ = S₂.⊢ˢʷ∷⇔ .proj₂ ∘→ Σ.map tr-⊢ tr-⊢ˢ∷ ∘→ S₁.⊢ˢʷ∷⇔ .proj₁

opaque

  -- Preservation of _⊢ˢʷ_≡_∷_.

  tr-⊢ˢʷ≡∷ :
    Γ S₁.⊢ˢʷ σ ≡ σ′ ∷ Δ →
    tr-Cons Γ S₂.⊢ˢʷ tr-Subst σ ≡ tr-Subst σ′ ∷ tr-Con Δ
  tr-⊢ˢʷ≡∷ =
    S₂.⊢ˢʷ≡∷⇔ .proj₂ ∘→
    Σ.map tr-⊢ (Σ.map tr-⊢ˢ∷ (Σ.map tr-⊢ˢ∷ tr-⊢ˢ≡∷)) ∘→
    S₁.⊢ˢʷ≡∷⇔ .proj₁

-- The following results make use of another assumption.

module _
  (Unitʷ-η-reflected : R₂.Unitʷ-η → R₁.Unitʷ-η)
  where

  -- Preservation of _⊢_⇒_∷_.

  tr-⊢⇒∷ :
    Γ T₁.⊢ t ⇒ u ∷ A →
    tr-Cons Γ T₂.⊢ tr-Term t ⇒ tr-Term u ∷ tr-Term A
  tr-⊢⇒∷ (conv t⇒u A≡B) =
    conv (tr-⊢⇒∷ t⇒u) (tr-⊢≡ A≡B)
  tr-⊢⇒∷ (δ-red ⊢Γ α∈ PE.refl PE.refl) =
    δ-red (tr-⊢ ⊢Γ) (tr-↦∷ α∈) (PE.sym tr-Term-wk) (PE.sym tr-Term-wk)
  tr-⊢⇒∷ (supᵘ-substˡ t⇒t' u) =
    supᵘ-substˡ (tr-⊢⇒∷ t⇒t') (tr-⊢∷ u)
  tr-⊢⇒∷ (supᵘ-substʳ t u⇒u') =
    supᵘ-substʳ (tr-⊢∷ t) (tr-⊢⇒∷ u⇒u')
  tr-⊢⇒∷ (supᵘ-zeroˡ t) =
    supᵘ-zeroˡ (tr-⊢∷ t)
  tr-⊢⇒∷ (supᵘ-zeroʳ t) =
    supᵘ-zeroʳ (tr-⊢∷ t)
  tr-⊢⇒∷ (supᵘ-sucᵘ t u) =
    supᵘ-sucᵘ (tr-⊢∷ t) (tr-⊢∷ u)
  tr-⊢⇒∷ (lower-subst t⇒u) =
    lower-subst (tr-⊢⇒∷ t⇒u)
  tr-⊢⇒∷ (Lift-β A u) =
    Lift-β (tr-⊢′ A) (tr-⊢∷ u)
  tr-⊢⇒∷ (app-subst {B = P} t⇒u v) =
    PE.subst (T₂._⊢_⇒_∷_ _ _ _) (tr-Term-[] P)
      (app-subst (tr-⊢⇒∷ t⇒u) (tr-⊢∷ v))
  tr-⊢⇒∷ (β-red {B = P} {t} ⊢P ⊢t u PE.refl ok) =
    PE.subst₂ (T₂._⊢_⇒_∷_ _ _) (tr-Term-[] t) (tr-Term-[] P)
      (β-red (tr-⊢′ ⊢P) (tr-⊢∷ ⊢t) (tr-⊢∷ u) PE.refl (ΠΣ-preserved ok))
  tr-⊢⇒∷ (fst-subst P t⇒u) =
    fst-subst (tr-⊢′ P) (tr-⊢⇒∷ t⇒u)
  tr-⊢⇒∷ (snd-subst {G = P} ⊢P t⇒u) =
    PE.subst (T₂._⊢_⇒_∷_ _ _ _) (tr-Term-[] P)
      (snd-subst (tr-⊢′ ⊢P) (tr-⊢⇒∷ t⇒u))
  tr-⊢⇒∷ (Σ-β₁ {G = P} ⊢P t u PE.refl ok) =
    Σ-β₁ (tr-⊢′ ⊢P) (tr-⊢∷ t)
      (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[] P)) (tr-⊢∷ u))
      PE.refl (ΠΣ-preserved ok)
  tr-⊢⇒∷ (Σ-β₂ {G = P} ⊢P t u PE.refl ok) =
    PE.subst (T₂._⊢_⇒_∷_ _ _ _) (tr-Term-[] P)
      (Σ-β₂ (tr-⊢′ ⊢P) (tr-⊢∷ t)
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[] P)) (tr-⊢∷ u))
         PE.refl (ΠΣ-preserved ok))
  tr-⊢⇒∷ (prodrec-subst {A = Q} ⊢Q v t⇒u) =
    PE.subst (T₂._⊢_⇒_∷_ _ _ _) (tr-Term-[] Q)
      (prodrec-subst (tr-⊢′ ⊢Q)
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[]↑ Q)) (tr-⊢∷ v))
         (tr-⊢⇒∷ t⇒u))
  tr-⊢⇒∷ (prodrec-β {G = P} {A = Q} {u = v} ⊢Q t u ⊢v PE.refl) =
    PE.subst₂ (T₂._⊢_⇒_∷_ _ _) (tr-Term-[,] v) (tr-Term-[] Q)
      (prodrec-β (tr-⊢′ ⊢Q) (tr-⊢∷ t)
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[] P)) (tr-⊢∷ u))
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[]↑ Q)) (tr-⊢∷ ⊢v))
         PE.refl)
  tr-⊢⇒∷ (natrec-subst {A = P} z s n⇒n′) =
    PE.subst (T₂._⊢_⇒_∷_ _ _ _) (tr-Term-[] P)
      (natrec-subst
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[] P)) (tr-⊢∷ z))
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[]↑ P)) (tr-⊢∷ s))
         (tr-⊢⇒∷ n⇒n′))
  tr-⊢⇒∷ (natrec-zero {A = P} z s) =
    PE.subst (T₂._⊢_⇒_∷_ _ _ _)
      (tr-Term-[] P)
      (natrec-zero
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[] P)) (tr-⊢∷ z))
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[]↑ P)) (tr-⊢∷ s)))
  tr-⊢⇒∷ (natrec-suc {A = P} {s} z ⊢s n) =
    PE.subst₂ (T₂._⊢_⇒_∷_ _ _) (tr-Term-[,] s) (tr-Term-[] P)
      (natrec-suc
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[] P)) (tr-⊢∷ z))
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[]↑ P)) (tr-⊢∷ ⊢s))
         (tr-⊢∷ n))
  tr-⊢⇒∷ (emptyrec-subst A t⇒u) =
    emptyrec-subst (tr-⊢′ A) (tr-⊢⇒∷ t⇒u)
  tr-⊢⇒∷ (unitrec-subst {A} ⊢A u t⇒t′ ok) =
    PE.subst (T₂._⊢_⇒_∷_ _ _ _) (tr-Term-[] A)
      (unitrec-subst (tr-⊢′ ⊢A)
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[] A)) (tr-⊢∷ u))
         (tr-⊢⇒∷ t⇒t′) (ok ∘→ Unitʷ-η-reflected))
  tr-⊢⇒∷ (unitrec-β {A} ⊢A u _) =
    PE.subst (T₂._⊢_⇒_∷_ _ _ _) (tr-Term-[] A)
      (P₂.unitrec-β-⇒ (tr-⊢′ ⊢A)
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[] A)) (tr-⊢∷ u)))
  tr-⊢⇒∷ (unitrec-β-η {A} ⊢A t u ok) =
    PE.subst (T₂._⊢_⇒_∷_ _ _ _) (tr-Term-[] A)
      (unitrec-β-η (tr-⊢′ ⊢A) (tr-⊢∷ t)
         (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[] A)) (tr-⊢∷ u))
         (Unitʷ-η-preserved ok))
  tr-⊢⇒∷ (J-subst {B} _ ⊢B u _ w₁⇒w₂) =
    PE.subst (T₂._⊢_⇒_∷_ _ _ _) (tr-Term-[,] B) $
    P₂.J-subst′
      (PE.subst (flip T₂._⊢_ _)
         (PE.cong (_»_ _) $
          PE.cong (_∙_ _) $
          PE.cong₂ (λ A t → Id A t (var x0))
            (PE.sym tr-Term-wk)
            (PE.sym tr-Term-wk)) $
       tr-⊢′ ⊢B)
      (PE.subst (T₂._⊢_∷_ _ _) (PE.sym $ tr-Term-[,] B) $
       tr-⊢∷ u)
      (tr-⊢⇒∷ w₁⇒w₂)
  tr-⊢⇒∷ (K-subst {B} ⊢B u v₁⇒v₂ ok) =
    PE.subst (T₂._⊢_⇒_∷_ _ _ _) (tr-Term-[] B) $
    K-subst (tr-⊢′ ⊢B)
      (PE.subst (T₂._⊢_∷_ _ _) (PE.sym $ tr-Term-[] B) $
       tr-⊢∷ u)
      (tr-⊢⇒∷ v₁⇒v₂) (K-preserved ok)
  tr-⊢⇒∷ ([]-cong-subst l v₁⇒v₂ ok) =
    PE.subst (T₂._⊢_⇒_∷_ _ _ _) (tr-Term-Id-Erased-[]-[] ok) $
    []-cong-subst (tr-⊢∷L l) (tr-⊢⇒∷ v₁⇒v₂) ([]-cong-preserved ok)
  tr-⊢⇒∷ (J-β {B} _ _ t≡t′ ⊢B _ u) =
    PE.subst (T₂._⊢_⇒_∷_ _ _ _) (tr-Term-[,] B) $
    P₂.J-β-⇒ (tr-⊢≡∷ t≡t′)
      (PE.subst (flip T₂._⊢_ _)
         (PE.cong (_»_ _) $
          PE.cong (_∙_ _) $
          PE.cong₂ (λ A t → Id A t (var x0))
            (PE.sym tr-Term-wk)
            (PE.sym tr-Term-wk)) $
       tr-⊢′ ⊢B)
      (PE.subst (T₂._⊢_∷_ _ _) (PE.sym $ tr-Term-[,] B) $
       tr-⊢∷ u)
  tr-⊢⇒∷ (K-β {B} ⊢B u ok) =
    PE.subst (T₂._⊢_⇒_∷_ _ _ _) (tr-Term-[] B) $
    K-β (tr-⊢′ ⊢B)
      (PE.subst (T₂._⊢_∷_ _ _) (PE.sym $ tr-Term-[] B) $
       tr-⊢∷ u)
      (K-preserved ok)
  tr-⊢⇒∷ ([]-cong-β l t≡t′ ok) =
    PE.subst (T₂._⊢_⇒_∷_ _ _ _) (tr-Term-Id-Erased-[]-[] ok) $
    []-cong-β (tr-⊢∷L l) (tr-⊢≡∷ t≡t′) ([]-cong-preserved ok)
  tr-⊢⇒∷ (resp-η {B} ok ⊢Q ⊢t ⊢u ⊢v) =
    resp-η (Equality-reflection-preserved ok) (tr-⊢′ ⊢Q) (tr-⊢∷ ⊢t)
      (tr-⊢∷ ⊢u)
      (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[,] B)) $
       tr-⊢∷ ⊢v)
  tr-⊢⇒∷ (set-η ok ⊢t ⊢u ⊢v ⊢w) =
    set-η (Equality-reflection-preserved ok) (tr-⊢∷ ⊢t) (tr-⊢∷ ⊢u)
      (tr-⊢∷ ⊢v) (tr-⊢∷ ⊢w)
  tr-⊢⇒∷ (qrec-subst {C} ⊢C ⊢t ⊢u ⊢v w₁⇒w₂) =
    let ok , _ = inversion-Is-set-Cons ⊢v in
    PE.subst (T₂._⊢_⇒_∷_ _ _ _) (tr-Term-[] C) $
    qrec-subst (tr-⊢′ ⊢C)
      (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[]↑ C)) $
       tr-⊢∷ ⊢t)
      (PE.subst₃ T₂._⊢_∷_ tr-Cons-Resp-Cons PE.refl
         (tr-Term-Resp-type (Quot-allowed→tr-𝟘≡𝟘 ok) tr-ω) $
       tr-⊢∷ ⊢u)
      (PE.subst₃ T₂._⊢_∷_ tr-Cons-Is-set-Cons PE.refl
         tr-Term-Is-set-type $
       tr-⊢∷ ⊢v)
      (tr-⊢⇒∷ w₁⇒w₂)
  tr-⊢⇒∷ (qrec-β {C} {t} ⊢C ⊢t ⊢u ⊢v ⊢w) =
    let ok , _ = inversion-Is-set-Cons ⊢v in
    PE.subst₂ (T₂._⊢_⇒_∷_ _ _) (tr-Term-[] t) (tr-Term-[] C) $
    qrec-β (tr-⊢′ ⊢C)
      (PE.subst (T₂._⊢_∷_ _ _) (PE.sym (tr-Term-[]↑ C)) $
       tr-⊢∷ ⊢t)
      (PE.subst₃ T₂._⊢_∷_ tr-Cons-Resp-Cons PE.refl
         (tr-Term-Resp-type (Quot-allowed→tr-𝟘≡𝟘 ok) tr-ω) $
       tr-⊢∷ ⊢u)
      (PE.subst₃ T₂._⊢_∷_ tr-Cons-Is-set-Cons PE.refl
         tr-Term-Is-set-type $
       tr-⊢∷ ⊢v)
      (tr-⊢∷ ⊢w)

  -- Preservation of _⊢_⇒_.

  tr-⊢⇒ : Γ T₁.⊢ A ⇒ B → tr-Cons Γ T₂.⊢ tr-Term A ⇒ tr-Term B
  tr-⊢⇒ (univ A⇒B) = univ (tr-⊢⇒∷ A⇒B)

  -- Preservation of _⊢_⇒*_∷_.

  tr-⊢⇒*∷ :
    Γ T₁.⊢ t ⇒* u ∷ A →
    tr-Cons Γ T₂.⊢ tr-Term t ⇒* tr-Term u ∷ tr-Term A
  tr-⊢⇒*∷ (id t)       = id (tr-⊢∷ t)
  tr-⊢⇒*∷ (t⇒u ⇨ u⇒*v) = tr-⊢⇒∷ t⇒u ⇨ tr-⊢⇒*∷ u⇒*v

  -- Preservation of _⊢_⇒*_.

  tr-⊢⇒* : Γ T₁.⊢ A ⇒* B → tr-Cons Γ T₂.⊢ tr-Term A ⇒* tr-Term B
  tr-⊢⇒* (id A)       = id (tr-⊢′ A)
  tr-⊢⇒* (A⇒B ⇨ B⇒*C) = tr-⊢⇒ A⇒B ⇨ tr-⊢⇒* B⇒*C

  -- The following results make use of more assumptions.

  module _
    (not-transparent : ¬ T transparent)
    (Higher-quotient-constructors-neutral-preserved :
       R₁.Higher-quotient-constructors-neutral →
       R₂.Higher-quotient-constructors-neutral)
    where

    -- Preservation of _⊢_↘_.

    tr-⊢↘ : Γ T₁.⊢ A ↘ B → tr-Cons Γ T₂.⊢ tr-Term A ↘ tr-Term B
    tr-⊢↘ (A⇒*B , B) =
      tr-⊢⇒* A⇒*B ,
      tr-Whnf not-transparent
        Higher-quotient-constructors-neutral-preserved Unitʷ-η-reflected
        B

    -- Preservation of _⊢_↘_∷_.

    tr-⊢↘∷ :
      Γ T₁.⊢ t ↘ u ∷ A →
      tr-Cons Γ T₂.⊢ tr-Term t ↘ tr-Term u ∷ tr-Term A
    tr-⊢↘∷ (t⇒*u , u) =
      tr-⊢⇒*∷ t⇒*u ,
      tr-Whnf not-transparent
        Higher-quotient-constructors-neutral-preserved Unitʷ-η-reflected
        u
