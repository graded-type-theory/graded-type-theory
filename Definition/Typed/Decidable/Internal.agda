------------------------------------------------------------------------
-- A type-checker that is internal in the sense that it is intended to
-- be used to prove some of the formalisation's lemmas (not in the
-- sense that it is implemented inside the object theory)
------------------------------------------------------------------------

-- This type-checker should work even if the Type-restrictions record,
-- and perhaps also some other things, are variables. The type-checker
-- uses terms defined in Definition.Typed.Decidable.Internal.Term. See
-- Definition.Typed.Decidable.Internal.Examples for some examples of
-- how the type-checker can be used.

open import Definition.Typed.Restrictions
open import Graded.Modality
open import Graded.Mode

module Definition.Typed.Decidable.Internal
  {a a′} {M : Set a} {Mode : Set a′}
  {𝕄 : Modality M}
  (𝐌 : IsMode Mode 𝕄)
  (TR : Type-restrictions 𝕄)
  where

open Type-restrictions TR

open import Definition.Conversion.Consequences.InverseUniv TR

open import Definition.Typed TR hiding (Trans)
open import Definition.Typed.Consequences.Inequality TR
open import Definition.Typed.Consequences.Injectivity TR
open import Definition.Typed.Consequences.Inversion TR
open import Definition.Typed.Decidable.Internal.Constraint 𝐌 TR
open import Definition.Typed.Decidable.Internal.Context 𝐌 TR
open import Definition.Typed.Decidable.Internal.Equality 𝐌 TR
open import Definition.Typed.Decidable.Internal.Monad 𝐌 TR
open import Definition.Typed.Decidable.Internal.Substitution 𝐌 TR
open import Definition.Typed.Decidable.Internal.Term 𝐌 TR
open import Definition.Typed.Decidable.Internal.Tests 𝐌 TR
open import Definition.Typed.Decidable.Internal.Universe-level TR
open import Definition.Typed.Decidable.Internal.Weakening 𝐌 TR
open import Definition.Typed.Inversion TR
open import Definition.Typed.Properties.Admissible.Empty TR
open import Definition.Typed.Properties.Admissible.Equality TR
open import Definition.Typed.Properties.Admissible.Erased TR
open import Definition.Typed.Properties.Admissible.Identity TR
open import Definition.Typed.Properties.Admissible.Level TR
open import Definition.Typed.Properties.Admissible.Lift TR
open import Definition.Typed.Properties.Admissible.Nat TR
open import Definition.Typed.Properties.Admissible.Pi TR
open import Definition.Typed.Properties.Admissible.Sigma TR
open import Definition.Typed.Properties.Admissible.U TR
open import Definition.Typed.Properties.Admissible.Unit TR
open import Definition.Typed.Properties.Admissible.Var TR
open import Definition.Typed.Properties.Reduction TR
open import Definition.Typed.Properties.Transparentisation TR
open import Definition.Typed.Properties.Well-formed TR
import Definition.Typed.Reasoning.Level TR as LvlR
import Definition.Typed.Reasoning.Term TR as TmR
import Definition.Typed.Reasoning.Type TR as TyR
open import Definition.Typed.Stability TR
open import Definition.Typed.Substitution.Primitive TR
import Definition.Typed.Weakening TR as W
open import Definition.Typed.Well-formed TR

open import Definition.Untyped M as U
  using (Term-kind; Universe-level; _or-empty_; _»_; _≤ᵘ_)
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
import Definition.Untyped.Sup TR as S
open import Definition.Untyped.Whnf M type-variant

open U.Con
open U.Context-pair
open U.Opacity
open U.Strength
open Term-kind
open U.Wk
open _or-empty_

open import Tools.Bool
open import Tools.Empty
open import Tools.Fin
open import Tools.Function hiding (ext)
import Tools.Level as L
open import Tools.List as List using (List; All; module Any; _∈_; [])
open import Tools.Maybe as M using (Maybe; nothing; just)
open import Tools.Nat as N using (Nat; 1+)
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum as ⊎
open import Tools.Unit
import Tools.Vec as Vec

open Any using (Any)

private variable
  b b₁ b₂                              : Bool
  m n n₁ n₂ n₃                         : Nat
  c                                    : Constants
  γ                                    : Contexts _
  st                                   : Stack-trace _
  ∇                                    : DCon _ _
  Δ Δ′ Δ₁ Δ₂ Η₁ Η₂                     : Con _ _
  Γ Γ′                                 : Cons _ _ _
  x x₁ x₂                              : Meta-var _ _ _
  A A′ A₁ A₁′ A₂ A₂′ B
    l l′ l″ l₁ l₂ t t′ t₁ t₁′ t₂ t₂′ u : Term[ _ , _ ] _
  ℓ ℓ₁ ℓ₂                              : Universe-level⁻
  k                                    : Term-kind
  σ σ′ σ₁ σ₂                           : Subst _ _ _

------------------------------------------------------------------------
-- A lemma

private opaque

  -- A lemma used below.

  ⊢1,0 :
    ∀ {Γ : U.Cons m n} {A₁ A₂ p q} →
    Γ ⊢ U.Σʷ p , q ▷ A₁ ▹ A₂ →
    Γ U.»∙ A₁ U.»∙ A₂ ⊢ U.prod 𝕨 p (U.var x1) (U.var x0) ∷
      U.wk[ 2 ] (U.Σʷ p , q ▷ A₁ ▹ A₂)
  ⊢1,0 {A₂} ⊢Σ =
    let ⊢A₁ , ⊢A₂ , Σ-ok = inversion-ΠΣ ⊢Σ in
    prodⱼ
      (PE.subst (_⊢_ _) (PE.sym (wk-comp _ _ _)) $
       W.wk
         (PE.subst (flip (W._»_∷ʷ_⊇_ _ _) _)
            (PE.cong (_∙_ _) (PE.sym wk[]≡wk[]′)) $
          W.liftʷ W.⊇-drop $
          W.wk (W.ʷ⊇-drop (∙ ⊢A₂)) ⊢A₁)
         ⊢A₂)
      (var₁ ⊢A₂)
      (PE.subst (_⊢_∷_ _ _)
         (U.wk1 A₂                                                  ≡⟨ wk≡subst _ _ ⟩

          A₂ U.[ U.toSubst (step id) ]                              ≡⟨ (flip substVar-to-subst A₂ λ where
                                                                          x0     → PE.refl
                                                                          (_ +1) → PE.refl) ⟩
          A₂ U.[ U.sgSubst (U.var x1) U.ₛ• lift (step (step id)) ]  ≡˘⟨ subst-wk A₂ ⟩

          U.wk (lift (step (step id))) A₂ U.[ U.var x1 ]₀           ≡˘⟨ PE.cong U._[ _ ]₀ (wk-comp _ _ A₂) ⟩

          U.wk (lift (step id)) (U.wk (lift (step id)) A₂)
            U.[ U.var x1 ]₀                                         ∎) $
       var₀ ⊢A₂)
      Σ-ok

------------------------------------------------------------------------
-- "Normal" forms for levels

mutual

  -- "Normal" forms for levels. These "normal" forms are not
  -- necessarily unique. One could perhaps imagine sorting the lists,
  -- using some kind of lexicographic comparison of terms. However,
  -- the lists are expected to be short. Two normal forms are compared
  -- by
  -- * comparing the universe levels and
  -- * comparing every element in one list with all the elements in the
  --   other list.

  Lvlⁿ : Constants → Nat → Set a
  Lvlⁿ c n = Lvlⁿ′ c n × Universe-level⁻

  -- One component of the normal form type.
  --
  -- The levels are supposed to be atomic neutral levels
  -- (meta-variables are included in this category), but that is not
  -- enforced by the type.

  Lvlⁿ′ : Constants → Nat → Set a
  Lvlⁿ′ c n = List (Nat × Lvl c n)

private variable
  nf nf₁ nf₂ : Lvlⁿ _ _
  ns ns₁ ns₂ : Lvlⁿ′ _ _

opaque

  -- The semantics of a normal form.

  ⌜_⌝ⁿ′ : Lvlⁿ′ c n → Contexts c → U.Lvl n → U.Lvl n
  ⌜ ns ⌝ⁿ′ γ =
    flip (List.foldr (λ (n , l) → U.1ᵘ+ⁿ n (⌜ l ⌝ γ) S.supᵘₗ_)) ns

  -- The semantics of a normal form.

  ⌜_⌝ⁿ : Lvlⁿ c n → Contexts c → U.Lvl n
  ⌜ ns , ℓ ⌝ⁿ γ = ⌜ ns ⌝ⁿ′ γ ⌜ ℓ ⌝⁻

opaque

  -- Well-formed normal forms.

  infix 4 _⊢⌜_⌝ⁿ′_∷Level

  _⊢⌜_⌝ⁿ′_∷Level : U.Cons m n → Lvlⁿ′ c n → Contexts c → Set a
  Γ ⊢⌜ []                ⌝ⁿ′ _ ∷Level = L.Lift _ ⊤
  Γ ⊢⌜ (_ , l) List.∷ ns ⌝ⁿ′ γ ∷Level =
    Γ ⊢ ⌜ l ⌝ γ ∷Level × Γ ⊢⌜ ns ⌝ⁿ′ γ ∷Level

  -- Well-formed normal forms.

  infix 4 _⊢⌜_⌝ⁿ_∷Level

  _⊢⌜_⌝ⁿ_∷Level : U.Cons m n → Lvlⁿ c n → Contexts c → Set a
  Γ ⊢⌜ ns , ℓ ⌝ⁿ γ ∷Level =
    Γ ⊢⌜ ns ⌝ⁿ′ γ ∷Level × Γ ⊢ ⌜ ℓ ⌝⁻ ∷Level

opaque
  unfolding ⌜_⌝ⁿ _⊢⌜_⌝ⁿ_∷Level

  -- A well-formedness lemma for _⊢⌜_⌝ⁿ′_∷Level.

  wf-⊢⌜⌝ⁿ′∷L :
    ∀ {Γ : U.Cons m n} {l} →
    Γ ⊢⌜ ns ⌝ⁿ′ γ ∷Level →
    Γ ⊢ l ∷Level →
    Γ ⊢ ⌜ ns ⌝ⁿ′ γ l ∷Level
  wf-⊢⌜⌝ⁿ′∷L {ns = List.[]} _ ⊢l =
    ⊢l
  wf-⊢⌜⌝ⁿ′∷L {ns = (n , _) List.∷ _} (⊢l′ , ⊢ns) ⊢l =
    ⊢supᵘₗ (⊢1ᵘ+ⁿ n ⊢l′) (wf-⊢⌜⌝ⁿ′∷L ⊢ns ⊢l)

  -- A well-formedness lemma for _⊢⌜_⌝ⁿ_∷Level.

  wf-⊢⌜⌝ⁿ∷L :
    {Γ : U.Cons m n} →
    Γ ⊢⌜ nf ⌝ⁿ γ ∷Level → Γ ⊢ ⌜ nf ⌝ⁿ γ ∷Level
  wf-⊢⌜⌝ⁿ∷L (⊢ns , ⊢ℓ) = wf-⊢⌜⌝ⁿ′∷L ⊢ns ⊢ℓ

opaque
  unfolding ⌜_⌝ⁿ _⊢⌜_⌝ⁿ_∷Level S._supᵘₗ_

  -- A lemma related to ⌜_⌝ⁿ.

  ⌜⊔⌝ⁿ :
    ∀ {Γ : U.Cons m n} ns →
    Γ ⊢ ⌜ ℓ₁ ⌝⁻ ∷Level →
    Γ ⊢⌜ ns , ℓ₂ ⌝ⁿ γ ∷Level →
    Γ ⊢ ⌜ ns , ℓ₁ ⊔⁻ ℓ₂ ⌝ⁿ γ ≡ ⌜ ℓ₁ ⌝⁻ S.supᵘₗ ⌜ ns , ℓ₂ ⌝ⁿ γ ∷Level
  ⌜⊔⌝ⁿ List.[] ⊢ℓ₁ (_ , ⊢ℓ₂) =
    ⊢⌜⊔⁻⌝⁻≡ ⊢ℓ₁ ⊢ℓ₂
  ⌜⊔⌝ⁿ {ℓ₁} {ℓ₂} {γ} ((n , l) List.∷ ns) ⊢ℓ₁ ((⊢l , ⊢ns) , ⊢ℓ₂) =
    let ⊢ns,ℓ₂ = wf-⊢⌜⌝ⁿ′∷L ⊢ns ⊢ℓ₂
        ⊢n+l   = ⊢1ᵘ+ⁿ n ⊢l
    in
    U.1ᵘ+ⁿ n (⌜ l ⌝ γ) S.supᵘₗ ⌜ ns , ℓ₁ ⊔⁻ ℓ₂ ⌝ⁿ γ              ≡⟨ supᵘₗ-cong (refl-⊢≡∷L ⊢n+l) (⌜⊔⌝ⁿ ns ⊢ℓ₁ (⊢ns , ⊢ℓ₂)) ⟩⊢
    U.1ᵘ+ⁿ n (⌜ l ⌝ γ) S.supᵘₗ (⌜ ℓ₁ ⌝⁻ S.supᵘₗ ⌜ ns , ℓ₂ ⌝ⁿ γ)  ≡˘⟨ supᵘₗ-assoc ⊢n+l ⊢ℓ₁ ⊢ns,ℓ₂ ⟩⊢
    (U.1ᵘ+ⁿ n (⌜ l ⌝ γ) S.supᵘₗ ⌜ ℓ₁ ⌝⁻) S.supᵘₗ ⌜ ns , ℓ₂ ⌝ⁿ γ  ≡⟨ supᵘₗ-cong (supᵘₗ-comm ⊢n+l ⊢ℓ₁) (refl-⊢≡∷L ⊢ns,ℓ₂) ⟩⊢
    (⌜ ℓ₁ ⌝⁻ S.supᵘₗ U.1ᵘ+ⁿ n (⌜ l ⌝ γ)) S.supᵘₗ ⌜ ns , ℓ₂ ⌝ⁿ γ  ≡⟨ supᵘₗ-assoc ⊢ℓ₁ ⊢n+l ⊢ns,ℓ₂ ⟩⊢∎
    ⌜ ℓ₁ ⌝⁻ S.supᵘₗ (U.1ᵘ+ⁿ n (⌜ l ⌝ γ) S.supᵘₗ ⌜ ns , ℓ₂ ⌝ⁿ γ)  ∎
    where
    open LvlR

-- Below Γ γ nf₁ nf₂ means that nf₁ is bounded by nf₂.

Below : U.Cons m n → Contexts c → Lvlⁿ c n → Lvlⁿ c n → Set a
Below Γ γ (ns₁ , ℓ₁) (ns₂ , ℓ₂) =
  ℓ₁ ≤⁻ ℓ₂ ×
  All
    (λ (n₁ , l₁) →
       Any
         (λ (n₂ , l₂) →
            Γ ⊢ U.1ᵘ+ⁿ n₁ (⌜ l₁ ⌝ γ) ≤ₗ U.1ᵘ+ⁿ n₂ (⌜ l₂ ⌝ γ) ∷Level)
         ns₂)
    ns₁

private opaque
  unfolding ⌜_⌝ⁿ _⊢⌜_⌝ⁿ_∷Level S._supᵘₗ_

  -- A lemma used to prove Below→≤.

  Below→≤-lemma :
    ∀ {Γ : U.Cons m n} {l} →
    Γ ⊢ l ∷Level →
    Γ ⊢⌜ nf ⌝ⁿ γ ∷Level →
    Any (λ (n′ , l′) → Γ ⊢ l ≤ₗ U.1ᵘ+ⁿ n′ (⌜ l′ ⌝ γ) ∷Level)
      (nf .proj₁) →
    Γ ⊢ l ≤ₗ ⌜ nf ⌝ⁿ γ ∷Level
  Below→≤-lemma {nf = List.[] , _} _ _ ()
  Below→≤-lemma
    {nf = (n′ , l′) List.∷ ns , ℓ} {γ} {l}
    ⊢l ((⊢l′ , ⊢ns) , ⊢ℓ) (List.here l≤n′+l′) =
    let ⊢ns,ℓ = wf-⊢⌜⌝ⁿ∷L (⊢ns , ⊢ℓ) in
    ⊢≡∷L→⊢≤ₗ∷L ⊢l
      (l S.supᵘₗ (U.1ᵘ+ⁿ n′ (⌜ l′ ⌝ γ) S.supᵘₗ ⌜ ns , ℓ ⌝ⁿ γ)  ≡˘⟨ supᵘₗ-assoc ⊢l (⊢1ᵘ+ⁿ n′ ⊢l′) ⊢ns,ℓ ⟩⊢
       (l S.supᵘₗ U.1ᵘ+ⁿ n′ (⌜ l′ ⌝ γ)) S.supᵘₗ ⌜ ns , ℓ ⌝ⁿ γ  ≡⟨ supᵘₗ-cong (⊢≤ₗ∷L→⊢≡∷L l≤n′+l′) (refl-⊢≡∷L ⊢ns,ℓ) ⟩⊢∎
       U.1ᵘ+ⁿ n′ (⌜ l′ ⌝ γ) S.supᵘₗ ⌜ ns , ℓ ⌝ⁿ γ              ∎)
    where
    open LvlR
  Below→≤-lemma
    {nf = (n′ , l′) List.∷ ns , ℓ} {γ} {l}
    ⊢l ((⊢l′ , ⊢ns) , ⊢ℓ) (List.there below) =
    let ⊢ns,ℓ = wf-⊢⌜⌝ⁿ∷L (⊢ns , ⊢ℓ)
        ⊢n′+l′ = ⊢1ᵘ+ⁿ n′ ⊢l′
    in
    ⊢≡∷L→⊢≤ₗ∷L ⊢l
      (l S.supᵘₗ (U.1ᵘ+ⁿ n′ (⌜ l′ ⌝ γ) S.supᵘₗ ⌜ ns , ℓ ⌝ⁿ γ)  ≡˘⟨ supᵘₗ-assoc ⊢l ⊢n′+l′ ⊢ns,ℓ ⟩⊢
       (l S.supᵘₗ U.1ᵘ+ⁿ n′ (⌜ l′ ⌝ γ)) S.supᵘₗ ⌜ ns , ℓ ⌝ⁿ γ  ≡⟨ supᵘₗ-cong (supᵘₗ-comm ⊢l ⊢n′+l′) (refl-⊢≡∷L ⊢ns,ℓ) ⟩⊢
       (U.1ᵘ+ⁿ n′ (⌜ l′ ⌝ γ) S.supᵘₗ l) S.supᵘₗ ⌜ ns , ℓ ⌝ⁿ γ  ≡⟨ supᵘₗ-assoc ⊢n′+l′ ⊢l ⊢ns,ℓ ⟩⊢
       U.1ᵘ+ⁿ n′ (⌜ l′ ⌝ γ) S.supᵘₗ l S.supᵘₗ ⌜ ns , ℓ ⌝ⁿ γ    ≡⟨ supᵘₗ-cong (refl-⊢≡∷L ⊢n′+l′)
                                                                    (⊢≤ₗ∷L→⊢≡∷L (Below→≤-lemma ⊢l (⊢ns , ⊢ℓ) below)) ⟩⊢∎
       U.1ᵘ+ⁿ n′ (⌜ l′ ⌝ γ) S.supᵘₗ ⌜ ns , ℓ ⌝ⁿ γ              ∎)
       where
       open LvlR

opaque
  unfolding ⌜_⌝ⁿ _≤⁻_ _⊢⌜_⌝ⁿ_∷Level S._supᵘₗ_

  -- Below Γ γ nf₁ nf₂ implies that ⌜ nf₁ ⌝ⁿ γ is below ⌜ nf₂ ⌝ⁿ γ,
  -- given certain assumptions.

  Below→≤ :
    {Γ : U.Cons m n} →
    Γ ⊢⌜ nf₁ ⌝ⁿ γ ∷Level →
    Γ ⊢⌜ nf₂ ⌝ⁿ γ ∷Level →
    Below Γ γ nf₁ nf₂ →
    Γ ⊢ ⌜ nf₁ ⌝ⁿ γ ≤ₗ ⌜ nf₂ ⌝ⁿ γ ∷Level
  Below→≤
    {nf₁ = List.[] , _} {nf₂ = ns₂ , _}
    (_ , ⊢ns₁) ⊢ns₂ (ℓ₁≤ℓ₂ , List.[]) =
    ⊢≡∷L→⊢≤ₗ∷L ⊢ns₁ $
    PE.subst (_⊢_≡_∷Level _ _)
      (PE.cong (λ ℓ → ⌜ ns₂ , ℓ ⌝ⁿ _) ℓ₁≤ℓ₂) $
    sym-⊢≡∷L (⌜⊔⌝ⁿ ns₂ ⊢ns₁ ⊢ns₂)
  Below→≤
    {nf₁ = (n , l) List.∷ ns₁ , ℓ₁} {γ} {nf₂ = ns₂ , ℓ₂}
    ⊢n+l,ns₁,ℓ₁@((⊢l , ⊢ns₁) , ⊢ℓ₁) ⊢ns₂,ℓ₂
    (ℓ₁≤ℓ₂ , below₁ List.∷ below₂) =
    let ⊢n+l = ⊢1ᵘ+ⁿ n ⊢l in
    ⊢≡∷L→⊢≤ₗ∷L (wf-⊢⌜⌝ⁿ∷L {nf = (n , l) List.∷ _ , _} ⊢n+l,ns₁,ℓ₁)
      ((U.1ᵘ+ⁿ n (⌜ l ⌝ γ) S.supᵘₗ ⌜ ns₁ , ℓ₁ ⌝ⁿ γ)
         S.supᵘₗ
       ⌜ ns₂ , ℓ₂ ⌝ⁿ γ                               ≡⟨ supᵘₗ-assoc ⊢n+l (wf-⊢⌜⌝ⁿ∷L (⊢ns₁ , ⊢ℓ₁)) (wf-⊢⌜⌝ⁿ∷L ⊢ns₂,ℓ₂) ⟩⊢

       U.1ᵘ+ⁿ n (⌜ l ⌝ γ)
         S.supᵘₗ
       (⌜ ns₁ , ℓ₁ ⌝ⁿ γ S.supᵘₗ ⌜ ns₂ , ℓ₂ ⌝ⁿ γ)     ≡⟨ supᵘₗ-cong (refl-⊢≡∷L ⊢n+l) $ ⊢≤ₗ∷L→⊢≡∷L $
                                                        Below→≤ (⊢ns₁ , ⊢ℓ₁) ⊢ns₂,ℓ₂ (ℓ₁≤ℓ₂ , below₂) ⟩⊢

       U.1ᵘ+ⁿ n (⌜ l ⌝ γ) S.supᵘₗ ⌜ ns₂ , ℓ₂ ⌝ⁿ γ    ≡⟨ ⊢≤ₗ∷L→⊢≡∷L (Below→≤-lemma ⊢n+l ⊢ns₂,ℓ₂ below₁) ⟩⊢∎

       ⌜ ns₂ , ℓ₂ ⌝ⁿ γ                               ∎)
       where
       open LvlR

opaque

  -- If nf₁ is bounded by nf₂ and vice versa, then the two normal
  -- forms are equal, given certain assumptions.

  Below-antisymmetric :
    {Γ : U.Cons m n} →
    Γ ⊢⌜ nf₁ ⌝ⁿ γ ∷Level →
    Γ ⊢⌜ nf₂ ⌝ⁿ γ ∷Level →
    Below Γ γ nf₁ nf₂ →
    Below Γ γ nf₂ nf₁ →
    Γ ⊢ ⌜ nf₁ ⌝ⁿ γ ≡ ⌜ nf₂ ⌝ⁿ γ ∷Level
  Below-antisymmetric ⊢nf₁ ⊢nf₂ nf₁≤nf₂ nf₂≤nf₁ =
    antisym-⊢≤ₗ∷L (Below→≤ ⊢nf₁ ⊢nf₂ nf₁≤nf₂)
      (Below→≤ ⊢nf₂ ⊢nf₁ nf₂≤nf₁)

-- Turns atomic neutral levels (and other terms) into "normal" forms.

⌞_⌟ⁿ : Term[ c , k ] n → Lvlⁿ c n
⌞ l ⌟ⁿ = (0 , Term[]→Lvl l) List.∷ [] , 0ᵘ+ 0

opaque
  unfolding ⌜_⌝ⁿ ⌜_⌝⁻ _⊢⌜_⌝ⁿ_∷Level U.↓ᵘ_ S._supᵘₗ_

  -- The function ⌞_⌟ⁿ is correctly defined.

  ⌞⌟ⁿ-correct :
    {Γ : U.Cons m n} (l : Term[ c , k ] n) →
    Γ ⊢ ⌜ Term[]→Lvl l ⌝ γ ∷Level →
    Γ ⊢⌜ ⌞ l ⌟ⁿ ⌝ⁿ γ ∷Level ×
    Γ ⊢ ⌜ Term[]→Lvl l ⌝ γ ≡ ⌜ ⌞ l ⌟ⁿ ⌝ⁿ γ ∷Level
  ⌞⌟ⁿ-correct _ ⊢l =
    ((⊢l , _) , ⊢zeroᵘ (wf ⊢l)) ,
    sym-⊢≡∷L (supᵘₗ-zeroʳ ⊢l)

-- Zero.

zeroᵘⁿ : Lvlⁿ c n
zeroᵘⁿ = [] , 0ᵘ+ 0

opaque
  unfolding ⌜_⌝ⁿ ⌜_⌝⁻ _⊢⌜_⌝ⁿ_∷Level U.↓ᵘ_

  -- The normal form zeroᵘⁿ is correctly defined.

  zeroᵘⁿ-correct :
    {Γ : U.Cons m n} →
    ⊢ Γ →
    Γ ⊢⌜ zeroᵘⁿ ⌝ⁿ γ ∷Level ×
    Γ ⊢ U.zeroᵘₗ ≡ ⌜ zeroᵘⁿ ⌝ⁿ γ ∷Level
  zeroᵘⁿ-correct ⊢Γ =
    let ⊢0 = ⊢zeroᵘ ⊢Γ in
    (_ , ⊢0) ,
    refl-⊢≡∷L ⊢0

-- A successor operation for Lvlⁿ.

1ᵘ+ⁿ : Lvlⁿ c n → Lvlⁿ c n
1ᵘ+ⁿ = Σ.map (List.map (Σ.map 1+ idᶠ)) 1+⁻

opaque
  unfolding ⌜_⌝ⁿ _⊢⌜_⌝ⁿ_∷Level S._supᵘₗ_

  -- The function 1ᵘ+ⁿ is correctly defined.

  1ᵘ+ⁿ-correct :
    {Γ : U.Cons m n} →
    Γ ⊢⌜ nf ⌝ⁿ γ ∷Level →
    Γ ⊢⌜ 1ᵘ+ⁿ nf ⌝ⁿ γ ∷Level ×
    Γ ⊢ ⌜ 1ᵘ+ⁿ nf ⌝ⁿ γ ≡ U.1ᵘ+ (⌜ nf ⌝ⁿ γ) ∷Level
  1ᵘ+ⁿ-correct {nf = List.[] , _} (_ , ⊢ℓ) =
    let 1ᵘ+ℓ≡     = ⊢⌜1+⁻⌝⁻≡ ⊢ℓ
        ⊢1ᵘ+ℓ , _ = wf-⊢≡∷L 1ᵘ+ℓ≡
    in
    (_ , ⊢1ᵘ+ℓ) ,
    1ᵘ+ℓ≡
  1ᵘ+ⁿ-correct {nf = (n , l) List.∷ ns , ℓ} {γ} ((⊢l , ⊢ns) , ⊢ℓ) =
    let (⊢1+ns , ⊢1+ℓ) , ≡1ᵘ+-⌜ns,ℓ⌝ = 1ᵘ+ⁿ-correct (⊢ns , ⊢ℓ)
        ⊢n+l                         = ⊢1ᵘ+ⁿ n ⊢l
    in
    ((⊢l , ⊢1+ns) , ⊢1+ℓ) ,
    (U.1ᵘ+ⁿ (1+ n) (⌜ l ⌝ γ) S.supᵘₗ ⌜ 1ᵘ+ⁿ (ns , ℓ) ⌝ⁿ γ   ≡⟨ supᵘₗ-cong (refl-⊢≡∷L (⊢1ᵘ+ ⊢n+l)) ≡1ᵘ+-⌜ns,ℓ⌝ ⟩⊢
     U.1ᵘ+ⁿ (1+ n) (⌜ l ⌝ γ) S.supᵘₗ U.1ᵘ+ (⌜ ns , ℓ ⌝ⁿ γ)  ≡⟨ supᵘₗ-1ᵘ+ ⊢n+l (wf-⊢⌜⌝ⁿ∷L (⊢ns , ⊢ℓ)) ⟩⊢∎
     U.1ᵘ+ (U.1ᵘ+ⁿ n (⌜ l ⌝ γ) S.supᵘₗ ⌜ ns , ℓ ⌝ⁿ γ)       ∎)
    where
    open LvlR

-- Max for Lvlⁿ.

supᵘₗⁿ : Lvlⁿ c n → Lvlⁿ c n → Lvlⁿ c n
supᵘₗⁿ (ns₁ , ℓ₁) (ns₂ , ℓ₂) = ns₁ List.++ ns₂ , ℓ₁ ⊔⁻ ℓ₂

opaque
  unfolding ⌜_⌝ⁿ _⊢⌜_⌝ⁿ_∷Level S._supᵘₗ_

  -- The function supᵘₗⁿ is correctly defined.

  supᵘₗⁿ-correct :
    {Γ : U.Cons m n} →
    Γ ⊢⌜ nf₁ ⌝ⁿ γ ∷Level →
    Γ ⊢⌜ nf₂ ⌝ⁿ γ ∷Level →
    Γ ⊢⌜ supᵘₗⁿ nf₁ nf₂ ⌝ⁿ γ ∷Level ×
    Γ ⊢ ⌜ supᵘₗⁿ nf₁ nf₂ ⌝ⁿ γ ≡ ⌜ nf₁ ⌝ⁿ γ S.supᵘₗ ⌜ nf₂ ⌝ⁿ γ ∷Level
  supᵘₗⁿ-correct
    {nf₁ = List.[] , _} {nf₂ = ns₂ , _} (_ , ⊢ℓ₁) (⊢ns₂ , ⊢ℓ₂) =
    (⊢ns₂ , ⊢⌜⌝⁻ ⊢ℓ₁ ⊢ℓ₂) ,
    ⌜⊔⌝ⁿ ns₂ ⊢ℓ₁ (⊢ns₂ , ⊢ℓ₂)
  supᵘₗⁿ-correct
    {nf₁ = (n , l) List.∷ ns₁ , ℓ₁} {γ} {nf₂ = ns₂ , ℓ₂}
    ((⊢l , ⊢ns₁) , ⊢ℓ₁) ⊢ns₂,ℓ₂ =
    let (⊢ns₁++ns₂ , ⊢ℓ₁⊔ℓ₂) , ⌜supᵘₗⁿ⌝≡ = supᵘₗⁿ-correct (⊢ns₁ , ⊢ℓ₁)
                                             ⊢ns₂,ℓ₂
        ⊢n+l                             = ⊢1ᵘ+ⁿ n ⊢l
    in
    ((⊢l , ⊢ns₁++ns₂) , ⊢ℓ₁⊔ℓ₂) ,
    (U.1ᵘ+ⁿ n (⌜ l ⌝ γ) S.supᵘₗ ⌜ ns₁ List.++ ns₂ , ℓ₁ ⊔⁻ ℓ₂ ⌝ⁿ γ  ≡⟨ supᵘₗ-cong (refl-⊢≡∷L ⊢n+l) ⌜supᵘₗⁿ⌝≡ ⟩⊢
     U.1ᵘ+ⁿ n (⌜ l ⌝ γ)
       S.supᵘₗ
     (⌜ ns₁ , ℓ₁ ⌝ⁿ γ S.supᵘₗ ⌜ ns₂ , ℓ₂ ⌝ⁿ γ)                     ≡˘⟨ supᵘₗ-assoc ⊢n+l (wf-⊢⌜⌝ⁿ∷L (⊢ns₁ , ⊢ℓ₁)) (wf-⊢⌜⌝ⁿ∷L ⊢ns₂,ℓ₂) ⟩⊢∎

     (U.1ᵘ+ⁿ n (⌜ l ⌝ γ) S.supᵘₗ ⌜ ns₁ , ℓ₁ ⌝ⁿ γ)
       S.supᵘₗ
     ⌜ ns₂ , ℓ₂ ⌝ⁿ γ                                               ∎)
    where
    open LvlR

-- Omega plus something.

ωᵘ+ⁿ : Nat → Lvlⁿ c n
ωᵘ+ⁿ m = [] , ωᵘ+ m

opaque
  unfolding ⌜_⌝ⁿ ⌜_⌝⁻ _⊢⌜_⌝ⁿ_∷Level

  -- The function ωᵘ+ⁿ is correctly defined.

  ωᵘ+ⁿ-correct :
    {Γ : U.Cons n₁ n₂} →
    Omega-plus-allowed →
    ⊢ Γ →
    Γ ⊢⌜ ωᵘ+ⁿ m ⌝ⁿ γ ∷Level ×
    Γ ⊢ U.ωᵘ+ m ≡ ⌜ ωᵘ+ⁿ m ⌝ⁿ γ ∷Level
  ωᵘ+ⁿ-correct ω-ok ⊢Γ =
    let ⊢ω = ⊢ωᵘ+ ω-ok ⊢Γ in
    (_ , ⊢ω) ,
    refl-⊢≡∷L ⊢ω

------------------------------------------------------------------------
-- Reduction

mutual

  -- Reduction. This implementation is sound if equality reflection is
  -- not allowed or the variable context is empty.
  --
  -- Note that if the definition context's length is not a literal
  -- natural number, then the code can get stuck, due to the use of de
  -- Bruijn levels.

  red : Fuel → Cons c m n → Term c n → Check c (Term c n)
  red 0      _ _ = no-fuel
  red (1+ n) Γ t = register ([red] Γ t) do
    red′ n Γ t

  private

    -- A helper function.

    red′ : Fuel → Cons c m n → Term c n → Check c (Term c n)
    red′ _ _ (meta-var x σ) =
      return (meta-var x σ)
    red′ n Γ (weaken ρ t) =
      red n Γ (wk ρ t)
    red′ n Γ (subst t σ) =
      red n Γ (t [ σ ])
    red′ _ _ (var x) =
      return (var x)
    red′ n Γ (defn α) = do
      t , _ ← definition-of (Γ .defs) α
      t     ← red n (Γ .defs » ε) t
      return (wk U.wk₀ t)
    red′ _ _ Level =
      return Level
    red′ _ _ zeroᵘ =
      return zeroᵘ
    red′ _ _ (1ᵘ+ l) =
      return (1ᵘ+ l)
    red′ n Γ (l₁ supᵘₗ l₂) = do
      l₁ ← red n Γ l₁
      case level-con? l₁ of λ where
        nothing         → return (l₁ supᵘₗ l₂)
        (just zeroᵘ)    → red n Γ l₂
        (just (1ᵘ+ l₁)) → do
          l₂ ← red n Γ l₂
          case level-con? l₂ of λ where
            nothing           → return (1ᵘ+ l₁ supᵘₗ l₂)
            (just zeroᵘ)      → return (1ᵘ+ l₁)
            (just (1ᵘ+ l₂))   → return (1ᵘ+ (l₁ supᵘₗ l₂))
    red′ _ _ (U l) =
      return (U l)
    red′ _ _ (Lift l A) =
      return (Lift l A)
    red′ _ _ (lift l t) =
      return (lift l t)
    red′ n Γ (lower t) = do
      t ← red n Γ t
      case is-lift? t of λ where
        (just (_ , t , _)) → red n Γ t
        nothing            → return (lower t)
    red′ _ _ Empty =
      return Empty
    red′ n Γ (emptyrec p A t) = do
      t ← red n Γ t
      return (emptyrec p A t)
    red′ _ _ (Unit s) =
      return (Unit s)
    red′ _ _ (star s) =
      return (star s)
    red′ n Γ (unitrec p q A t₁ t₂) = do
      t₁ ← red n Γ t₁
      case is-star? t₁ of λ where
        (just _) → red n Γ t₂
        nothing  → return (unitrec p q A t₁ t₂)
    red′ _ _ (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ A₂) =
      return (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ A₂)
    red′ _ _ (lam p qA t) =
      return (lam p qA t)
    red′ n Γ (t₁ ∘⟨ p ⟩ t₂) = do
      t₁ ← red n Γ t₁
      case is-lam? t₁ of λ where
        (just (_ , _ , t₁′ , _)) → red n Γ (t₁′ [ sgSubst t₂ ])
        nothing                  → return (t₁ ∘⟨ p ⟩ t₂)
    red′ _ _ (prod s p qA₂ t₁ t₂) =
      return (prod s p qA₂ t₁ t₂)
    red′ n Γ (fst p t) = do
      t ← red n Γ t
      case is-prod? t of λ where
        (just (_ , _ , _ , t₁ , _)) → red n Γ t₁
        nothing                     → return (fst p t)
    red′ n Γ (snd p t) = do
      t ← red n Γ t
      case is-prod? t of λ where
        (just (_ , _ , _ , _ , t₂ , _)) → red n Γ t₂
        nothing                         → return (snd p t)
    red′ n Γ (prodrec r p q A t₁ t₂) = do
      t₁ ← red n Γ t₁
      case is-prod? t₁ of λ where
        (just (_ , _ , _ , t₁₁ , t₁₂ , _)) →
          red n Γ (subst t₂ (cons (sgSubst t₁₁) t₁₂))
        nothing →
          return (prodrec r p q A t₁ t₂)
    red′ _ _ ℕ =
      return ℕ
    red′ _ _ zero =
      return zero
    red′ _ _ (suc t) =
      return (suc t)
    red′ n Γ (natrec p q r A t₁ t₂ t₃) = do
      t₃ ← red n Γ t₃
      case is-zero-or-suc? t₃ of λ where
        (just (inj₁ _)) →
          red n Γ t₁
        (just (inj₂ (t₃′ , _))) →
          red n Γ
            (subst t₂ (cons (sgSubst t₃′) (natrec p q r A t₁ t₂ t₃′)))
        nothing →
          return (natrec p q r A t₁ t₂ t₃)
    red′ _ _ (Id A t₁ t₂) =
      return (Id A t₁ t₂)
    red′ _ _ (rfl t) =
      return (rfl t)
    red′ n Γ (J p q A₁ t₁ A₂ t₂ t₃ t₄) = do
      t₄ ← red n Γ t₄
      case is-rfl? t₄ of λ where
        (just _) → red n Γ t₂
        nothing  → return (J p q A₁ t₁ A₂ t₂ t₃ t₄)
    red′ n Γ (K p A₁ t₁ A₂ t₂ t₃) = do
      t₃ ← red n Γ t₃
      case is-rfl? t₃ of λ where
        (just _) → red n Γ t₂
        nothing  → return (K p A₁ t₁ A₂ t₂ t₃)
    red′ n Γ ([]-cong s l A t₁ t₂ t₃) = do
      t₃ ← red n Γ t₃
      case is-rfl? t₃ of λ where
        (just (t₃′ , _)) →
          return (rfl (box s l M.<$> (t₃′ M.<∣> just t₁)))
        nothing →
          return ([]-cong s l A t₁ t₂ t₃)

------------------------------------------------------------------------
-- Reduction (again) and type and equality checking

private

  -- A helper function used in the implementations of equal-sub and
  -- equal-sub′.

  equal-sub″ :
    ∀ k → Con c (k N.+ c .base-con-size) → Check c ⊤
  equal-sub″ 0 Γ = do
    is-base Γ
    return tt
  equal-sub″ (1+ k) Γ = do
    Γ , _ ← is-∙ Γ
    equal-sub″ k Γ

-- Removes top-level weaken and subst constructors.
--
-- For the meaning of the boolean in the result, see
-- really-remove-weaken-subst-sound. If the boolean argument is false,
-- then a certain check is not run and the returned boolean is always
-- false.

really-remove-weaken-subst :
  Fuel → Term[ c , k ] n → Bool → Check c (Term[ c , k ] n × Bool)
really-remove-weaken-subst 0 _ _ =
  no-fuel
really-remove-weaken-subst (1+ n) t run-check = do
  t , b ← remove-weaken-subst n t run-check
  case is-weaken-subst? t of λ where
    (no _)  → return (t , b)
    (yes _) → really-remove-weaken-subst n t run-check

-- Returns the context associated to the meta-variable.

context-of : Meta-var c k n → Check c (Con c n)
context-of x = do
  Μ ← ask
  return (Μ .metas .bindings x .proj₁)

-- Checks that the meta-variable refers to a term. In that case the
-- term's variable context and type are returned.

is-term : Meta-var c tm n → Check c (Con c n × Term c n)
is-term x = do
  Μ ← ask
  case Μ .metas .bindings x of λ where
    (_ , type _) →
      fail "Expected a term."
    (Δ , term _ A) → do
      return (Δ , A)

-- Checks that the two meta-variables are equal.

are-equal-meta-vars : (_ _ : Meta-var c k n) → Check c ⊤
are-equal-meta-vars x₁ x₂ = do
  Μ ← ask
  [ are-equal-meta-vars? (Μ .metas) x₁ x₂ ]with-message
    "Expected equal meta-variables."
  return tt
  where
  -- Note that this test does not match on the natural numbers. Those
  -- numbers might be meta-level variables.

  equal? :
    (p₁ p₂ :
     ∃ λ ((k , n) : Term-kind × Nat) →
       Meta-var c k n × Meta-var c k n) →
    Maybe (p₁ PE.≡ p₂)
  equal?
    {c}
    ((k₁ , n₁) , var x₁ eq₁₁ eq₂₁ , var y₁ _ _)
    ((k₂ , n₂) , var x₂ eq₁₂ eq₂₂ , var y₂ _ _) =
    (λ x₁≡x₂ y₁≡y₂ →
       let k₁≡k₂ =
             k₁                                     ≡˘⟨ eq₂₁ ⟩
             Vec.lookup (c .meta-con-term-kind) x₁  ≡⟨ PE.cong (Vec.lookup (c .meta-con-term-kind)) x₁≡x₂ ⟩
             Vec.lookup (c .meta-con-term-kind) x₂  ≡⟨ eq₂₂ ⟩
             k₂                                     ∎

           n₁≡n₂ =
             n₁                                ≡˘⟨ eq₁₁ ⟩
             Vec.lookup (c .meta-con-size) x₁  ≡⟨ PE.cong (Vec.lookup (c .meta-con-size)) x₁≡x₂ ⟩
             Vec.lookup (c .meta-con-size) x₂  ≡⟨ eq₁₂ ⟩
             n₂                                ∎
       in
       case k₁≡k₂ of λ {
         PE.refl →
       case n₁≡n₂ of λ {
         PE.refl →
       PE.cong₂ (λ x y → _ , x , y)
         (var-cong x₁≡x₂) (var-cong y₁≡y₂) }}) M.<$>
    M.dec⇒maybe (x₁ ≟ⱽ x₂) M.⊛ M.dec⇒maybe (y₁ ≟ⱽ y₂)

  are-equal-meta-vars? :
    (Μ : Meta-con c) (x₁ x₂ : Meta-var c k n) →
    Maybe
      (x₁ PE.≡ x₂ ⊎
       ((k , n) , x₁ , x₂) ∈ Μ .equalities ⊎
       ((k , n) , x₂ , x₁) ∈ Μ .equalities)
  are-equal-meta-vars? Μ x₁ x₂ =
    (inj₁ M.<$> x₁ ≟ᵐᵛ x₂) M.<∣>
    (inj₂ ∘→ inj₁ M.<$>
     List.member? equal? (_ , x₁ , x₂) (Μ .equalities)) M.<∣>
    (inj₂ ∘→ inj₂ M.<$>
     List.member? equal? (_ , x₂ , x₁) (Μ .equalities))

mutual

  -- A mutually recursive definition of reduction, type-checking and
  -- equality checking.
  --
  -- Inputs that are not checked (or for which a type is inferred) are
  -- assumed to be well-formed, unless otherwise noted.
  --
  -- Why is reduction defined mutually with type-checking? If equality
  -- reflection is possibly allowed, then the implementation of
  -- reduction makes use of type-checking to avoid uses of injectivity
  -- lemmas in the soundness proof.
  --
  -- Some of the procedures return terms that are possibly more
  -- annotated versions of the inputs. This approach was taken because
  -- it made it possible to omit some annotations.

  -- Checks that the meta-variable refers to a type. In that case the
  -- type's variable context is returned.

  is-type :
    Fuel → DCon c m → Meta-var c tm n → Check c (Con c n)
  is-type n ∇ x = do
    Μ ← ask
    case Μ .metas .bindings x of λ where
      (Δ , type _) →
        return Δ
      (Δ , term _ A) → do
        A ← red-ty n (∇ » Δ) A
        is-U A
        return Δ

  -- Checks that the meta-variable, with the substitution applied to
  -- it, refers to a level. In that case the level's context as well
  -- as a possibly more annotated version of the level is returned.
  --
  -- The substitution is not assumed to be well-formed.

  is-level :
    Fuel → Cons c m n₂ → Meta-var c k n₁ → Subst c n₂ n₁ →
    Check c (Con c n₁ × Term[ c , k ] n₂)
  is-level n (∇ » Γ) x σ = do
    γ ← ask
    case γ .metas .bindings x of λ where
      (_ , type _) →
        fail "Expected a level, found a type."
      (Δ , term _ A) → do
        σ ← check-sub n ∇ Γ σ Δ
        B ← red-ty n (∇ » Γ) (A [ σ ])
        is-Level B
        return (Δ , meta-var x σ)
      (Δ , level _) → do
        σ ← check-sub n ∇ Γ σ Δ
        return (Δ , meta-var x σ)

  -- Reduction for types.

  red-ty : Fuel → Cons c m n → Term c n → Check c (Term c n)
  red-ty 0      _ _ = no-fuel
  red-ty (1+ n) Γ A =
    register ([red-ty] Γ A)
      (if-no-equality-reflection (red n Γ A) do
         A , _ ← really-remove-weaken-subst n A false
         case is-type-constructor? A of λ where
           (just _) → return A
           nothing  → do
             B ← infer-red n Γ A
             is-U B
             red-tm n Γ A B)

  -- Reduction for a term with a given type.
  --
  -- Note that if the definition context's length is not a literal
  -- natural number, then the code can get stuck, due to the use of de
  -- Bruijn levels.

  red-tm : Fuel → Cons c m n → (t A : Term c n) → Check c (Term c n)
  red-tm 0      _ _ _ = no-fuel
  red-tm (1+ n) Γ t A =
    register ([red-tm] Γ t A)
      (if-no-equality-reflection (red n Γ t) (red-tm′ n Γ t A))

  private

    -- A helper function.

    red-tm′ : Fuel → Cons c m n → (t A : Term c n) → Check c (Term c n)
    red-tm′ _ _ (meta-var x σ) _ =
      return (meta-var x σ)
    red-tm′ n Γ (weaken ρ t) A =
      red-tm n Γ (wk ρ t) A
    red-tm′ n Γ (subst t σ) A =
      red-tm n Γ (t [ σ ]) A
    red-tm′ _ _ (var x) _ =
      return (var x)
    red-tm′ n Γ (defn α) _ = do
      t , B ← definition-of (Γ .defs) α
      t     ← red-tm n (Γ .defs » ε) t B
      return (wk U.wk₀ t)
    red-tm′ _ _ Level _ =
      return Level
    red-tm′ _ _ zeroᵘ _ =
      return zeroᵘ
    red-tm′ _ _ (1ᵘ+ l) _ =
      return (1ᵘ+ l)
    red-tm′ n Γ (l₁ supᵘₗ l₂) _ = do
      l₁ ← red-tm n Γ l₁ Level
      case level-con? l₁ of λ where
        nothing         → return (l₁ supᵘₗ l₂)
        (just zeroᵘ)    → red-tm n Γ l₂ Level
        (just (1ᵘ+ l₁)) → do
          l₂ ← red-tm n Γ l₂ Level
          case level-con? l₂ of λ where
            nothing         → return (1ᵘ+ l₁ supᵘₗ l₂)
            (just zeroᵘ)    → return (1ᵘ+ l₁)
            (just (1ᵘ+ l₂)) → return (1ᵘ+ (l₁ supᵘₗ l₂))
    red-tm′ _ _ (U l) _ =
      return (U l)
    red-tm′ _ _ (Lift l A) _ =
      return (Lift l A)
    red-tm′ _ _ (lift l t) _ =
      return (lift l t)
    red-tm′ n Γ (lower t) A = do
      B         ← infer-red n Γ t
      l , C , _ ← is-Lift B
      equal-ty n Γ A C
      t ← red-tm n Γ t (Lift l C)
      case is-lift? t of λ where
        nothing            → return (lower t)
        (just (_ , t , _)) → do
          t ← check n Γ t C
          red-tm n Γ t C
    red-tm′ _ _ Empty _ =
      return Empty
    red-tm′ n Γ (emptyrec p A t) _ = do
      t ← red-tm n Γ t Empty
      return (emptyrec p A t)
    red-tm′ _ _ (Unit s) _ =
      return (Unit s)
    red-tm′ _ _ (star s) _ =
      return (star s)
    red-tm′ n Γ (unitrec p q A t₁ t₂) _ = do
      t₁ ← red-tm n Γ t₁ (Unit 𝕨)
      case is-star-𝕨? t₁ of λ where
        (just _) → red-tm n Γ t₂ (subst A (sgSubst (star 𝕨)))
        nothing  → return (unitrec p q A t₁ t₂)
    red-tm′ _ _ (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ A₂) _ =
      return (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ A₂)
    red-tm′ _ _ (lam p qA t) _ =
      return (lam p qA t)
    red-tm′ n Γ (t₁ ∘⟨ p ⟩ t₂) A = do
      B               ← infer-red n Γ t₁
      q , B₁ , B₂ , _ ← is-ΠΣ BMΠ p B
      t₂              ← check n Γ t₂ B₁
      equal-ty n Γ A (subst B₂ (sgSubst t₂))
      t₁ ← red-tm n Γ t₁ (ΠΣ⟨ BMΠ ⟩ p , q ▷ B₁ ▹ B₂)
      case is-lam⟨ p ⟩? t₁ of λ where
        nothing              → return (t₁ ∘⟨ p ⟩ t₂)
        (just (_ , t₁′ , _)) → do
          t₁′ ← check n (Γ »∙ B₁) t₁′ B₂
          red-tm n Γ (t₁′ [ sgSubst t₂ ]) (subst B₂ (sgSubst t₂))
    red-tm′ _ _ (prod s p qA₂ t₁ t₂) _ =
      return (prod s p qA₂ t₁ t₂)
    red-tm′ n Γ (fst p t) A = do
      B               ← infer-red n Γ t
      q , B₁ , B₂ , _ ← is-ΠΣ (BMΣ 𝕤) p B
      equal-ty n Γ A B₁
      t ← red-tm n Γ t (ΠΣ⟨ BMΣ 𝕤 ⟩ p , q ▷ B₁ ▹ B₂)
      case is-prod⟨ 𝕤 , p ⟩? t of λ where
        nothing                  → return (fst p t)
        (just (_ , t₁ , t₂ , _)) → do
          t₁ ← check n Γ t₁ B₁
          check n Γ t₂ (subst B₂ (sgSubst t₁))
          red-tm n Γ t₁ B₁
    red-tm′ n Γ (snd p t) A = do
      B               ← infer-red n Γ t
      q , B₁ , B₂ , _ ← is-ΠΣ (BMΣ 𝕤) p B
      equal-ty n Γ A (subst B₂ (sgSubst (fst p t)))
      t ← red-tm n Γ t (ΠΣ⟨ BMΣ 𝕤 ⟩ p , q ▷ B₁ ▹ B₂)
      case is-prod⟨ 𝕤 , p ⟩? t of λ where
        nothing                  → return (snd p t)
        (just (_ , t₁ , t₂ , _)) → do
          t₁ ← check n Γ t₁ B₁
          t₂ ← check n Γ t₂ (subst B₂ (sgSubst t₁))
          red-tm n Γ t₂ (subst B₂ (sgSubst t₁))
    red-tm′ n Γ (prodrec r p q B t₁ t₂) A = do
      C                ← infer-red n Γ t₁
      q′ , C₁ , C₂ , _ ← is-ΠΣ (BMΣ 𝕨) p C
      B  ← check-type n (Γ »∙ Σʷ p , q′ ▷ C₁ ▹ C₂) B
      t₁ ← red-tm n Γ t₁ (Σʷ p , q′ ▷ C₁ ▹ C₂)
      equal-ty n Γ A (subst B (sgSubst t₁))
      t₂ ←
        check n (Γ »∙ C₁ »∙ C₂) t₂
          (Term[_,_].subst B $
           cons (wkSubst 2 id)
             (prod 𝕨 p (just (q′ , weaken (lift (U.stepn id 2)) C₂))
                (var x1) (var x0)))
      case is-prod⟨ 𝕨 , p ⟩? t₁ of λ where
        (just (_ , t₁₁ , t₁₂ , _)) → do
          t₁₁ ← check n Γ t₁₁ C₁
          t₁₂ ← check n Γ t₁₂ (subst C₂ (sgSubst t₁₁))
          red-tm n Γ (subst t₂ (cons (sgSubst t₁₁) t₁₂))
            (subst B (sgSubst (prod 𝕨 p (just (q′ , C₂)) t₁₁ t₁₂)))
        nothing →
          return (prodrec r p q B t₁ t₂)
    red-tm′ _ _ ℕ _ =
      return ℕ
    red-tm′ _ _ zero _ =
      return zero
    red-tm′ _ _ (suc t) _ =
      return (suc t)
    red-tm′ n Γ (natrec p q r A t₁ t₂ t₃) _ = do
      t₃ ← red-tm n Γ t₃ ℕ
      case is-zero-or-suc? t₃ of λ where
        (just (inj₁ _)) →
          red-tm n Γ t₁ (subst A (sgSubst zero))
        (just (inj₂ (t₃′ , _))) →
          red-tm n Γ
            (subst t₂ (cons (sgSubst t₃′) (natrec p q r A t₁ t₂ t₃′)))
            (subst A (sgSubst (suc t₃′)))
        nothing →
          return (natrec p q r A t₁ t₂ t₃)
    red-tm′ _ _ (Id A t₁ t₂) _ =
      return (Id A t₁ t₂)
    red-tm′ _ _ (rfl t) _ =
      return (rfl t)
    red-tm′ n Γ (J p q A₁ t₁ A₂ t₂ t₃ t₄) _ = do
      t₄ ← red-tm n Γ t₄ (Id A₁ t₁ t₃)
      case is-rfl? t₄ of λ where
        nothing  → return (J p q A₁ t₁ A₂ t₂ t₃ t₄)
        (just _) → do
          equal-tm n Γ t₁ t₃ A₁
          red-tm n Γ t₂ (subst A₂ (cons (sgSubst t₁) (rfl (just t₁))))
    red-tm′ n Γ (K p A₁ t₁ A₂ t₂ t₃) _ = do
      t₃ ← red-tm n Γ t₃ (Id A₁ t₁ t₁)
      case is-rfl? t₃ of λ where
        (just _) → red-tm n Γ t₂ (subst A₂ (sgSubst (rfl (just t₁))))
        nothing  → return (K p A₁ t₁ A₂ t₂ t₃)
    red-tm′ n Γ ([]-cong s l A t₁ t₂ t₃) _ = do
      t₃ ← red-tm n Γ t₃ (Id A t₁ t₂)
      case is-rfl? t₃ of λ where
        nothing          → return ([]-cong s l A t₁ t₂ t₃)
        (just (t₃′ , _)) → do
          equal-tm n Γ t₁ t₂ A
          return (rfl (box s l M.<$> (t₃′ M.<∣> just t₁)))

  -- A type-checker for types.
  --
  -- The returned type is a possibly more annotated version of the
  -- input.

  check-type : Fuel → Cons c m n → Term c n → Check c (Term c n)
  check-type 0 _ _ =
    no-fuel
  check-type (1+ n) Γ A = register ([check-type] Γ A) do
    A , _ ← really-remove-weaken-subst n A false
    check-type′ n Γ (is-type-constructor? A)

  private

    -- A helper function.

    check-type′ :
      {A : Term c n} →
      Fuel → Cons c m n → Maybe (Is-type-constructor A) →
      Check c (Term c n)
    check-type′ n Γ (just (meta-var x σ)) = do
      Δ ← is-type n (Γ .defs) x
      σ ← check-sub n (Γ .defs) (Γ .vars) σ Δ
      return (meta-var x σ)
    check-type′ _ _ (just Level) = do
      require⁰ level-allowed
      return Level
    check-type′ n Γ (just (U l)) = do
      l ← check-level n Γ l
      return (U l)
    check-type′ n Γ (just (Lift l A)) = do
      l ← check-level n Γ l
      A ← check-type n Γ A
      return (Lift l A)
    check-type′ _ _ (just Empty) =
      return Empty
    check-type′ _ _ (just (Unit s)) = do
      require⁺ (unit-allowed s)
      return (Unit s)
    check-type′ n Γ (just (ΠΣ b p q A₁ A₂)) = do
      A₁ ← check-type n Γ A₁
      A₂ ← check-type n (Γ »∙ A₁) A₂
      require⁺ (πσ-allowed b p q)
      return (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ A₂)
    check-type′ _ _ (just ℕ) =
      return ℕ
    check-type′ n Γ (just (Id A t₁ t₂)) = do
      A ← check-type n Γ A
      t₁ ← check n Γ t₁ A
      t₂ ← check n Γ t₂ A
      return (Id A t₁ t₂)
    check-type′ {A} n Γ nothing = do
      B ← infer-red n Γ A
      is-U B
      return A

  -- A type-checker for levels (either terms that stand for levels or
  -- syntactical levels).
  --
  -- The returned term is a possibly more annotated version of the
  -- input.
  --
  -- Note that if an application of a substitution σ to l₁ supᵘₗ l₂ is
  -- encountered, then the level is only accepted if Level is allowed
  -- or if σ, l₁ and l₂ satisfy a certain condition. The reason is
  -- that a term like
  -- subst (level (var x0) supᵘₗ level (var x0)) (sgSubst zeroᵘ) does
  -- not correspond to a level literal: its translation is, at the
  -- time of writing, U.zeroᵘₗ U.supᵘ U.zeroᵘₗ.

  check-level :
    Fuel → Cons c m n → Term[ c , k ] n → Check c (Term[ c , k ] n)
  check-level 0 _ _ =
    no-fuel
  check-level (1+ n) Γ l = register ([check-level] Γ l) do
    l , condition-satisfied ← really-remove-weaken-subst n l true
    check-level′ n Γ (is-perhaps-level? l) condition-satisfied

  private

    -- A helper function.

    check-level′ :
      {l : Term[ c , k ] n} →
      Fuel → Cons c m n → Maybe (Is-perhaps-level l) → Bool →
      Check c (Term[ c , k ] n)
    check-level′ n Γ (just (meta-var x σ)) _ =
      proj₂ <$> is-level n Γ x σ
    check-level′ _ _ (just zeroᵘ) _ =
      return zeroᵘ
    check-level′ n Γ (just (1ᵘ+ l)) _ =
      1ᵘ+ <$> check-level n Γ l
    check-level′ n Γ (just (l₁ supᵘₗ l₂)) condition-satisfied = do
      unless condition-satisfied (require⁰ level-allowed)
      _supᵘₗ_ <$> check-level n Γ l₁ ⊛ check-level n Γ l₂
    check-level′ _ _ (just (ωᵘ+ m)) _ = do
      require⁰ omega-plus-allowed
      return (ωᵘ+ m)
    check-level′ n Γ (just (level t)) _ =
      level <$> check-level n Γ t
    check-level′ {k = tm} {l} n Γ nothing _ = do
      require⁰ level-allowed
      check n Γ l Level
    check-level′ _ _ _ _ =
      -- This case should be impossible.
      fail "Internal error."

  -- A type-checker for terms.
  --
  -- The returned term is a possibly more annotated version of the
  -- input.

  check : Fuel → Cons c m n → Term c n → Term c n → Check c (Term c n)
  check 0 _ _ _ =
    no-fuel
  check (1+ n) Γ t A = register ([check] Γ t A) do
    t , _ ← really-remove-weaken-subst n t false
    case checkable? t of λ where
      nothing → do
        B ← infer n Γ t
        equal-ty n Γ B A
        return t
      (just t) → do
        A ← red-ty n Γ A
        check′ n Γ t A

  private

    -- A helper function.

    check′ :
      {t : Term c n} →
      Fuel → Cons c m n → Checkable t → Term c n → Check c (Term c n)
    check′ n Γ (lift t) A = do
      l , B , _ ← is-Lift A
      t ← check n Γ t B
      return (lift (just l) t)
    check′ n Γ (lam p t) A = do
      q , B₁ , B₂ , _ ← is-ΠΣ BMΠ p A
      t ← check n (Γ »∙ B₁) t B₂
      return (lam p (just (q , B₁)) t)
    check′ n Γ (prod s p t₁ t₂) A = do
      q , B₁ , B₂ , _ ← is-ΠΣ (BMΣ s) p A
      t₁              ← check n Γ t₁ B₁
      t₂              ← check n Γ t₂ (subst B₂ (sgSubst t₁))
      return (prod s p (just (q , B₂)) t₁ t₂)
    check′ n Γ rfl A = do
      B , t₁ , t₂ , _ ← is-Id A
      equal-tm n Γ t₁ t₂ B
      return (rfl (just t₁))

  -- Type inference.
  --
  -- The returned type is reduced.

  infer-red : Fuel → Cons c m n → Term c n → Check c (Term c n)
  infer-red n Γ t = do
    A ← infer n Γ t
    red-ty n Γ A

  -- Type inference.
  --
  -- The returned type is not guaranteed to be reduced.

  infer : Fuel → Cons c m n → Term c n → Check c (Term c n)
  infer 0 _ _ =
    no-fuel
  infer (1+ n) Γ t = register ([infer] Γ t) do
    t , _ ← really-remove-weaken-subst n t false
    inf   ← inferable t
    infer′ n Γ inf

  private

    -- A helper function.

    infer′ :
      {t : Term c n} →
      Fuel → Cons c m n → Inferable t → Check c (Term c n)
    infer′ n Γ (meta-var x σ) = do
      Δ , A ← is-term x
      σ     ← check-sub n (Γ .defs) (Γ .vars) σ Δ
      return (subst A σ)
    infer′ _ Γ (var x) =
      index (Γ .vars) x
    infer′ _ Γ (defn α) = do
      A ← type-of (Γ .defs) α
      return (weaken U.wk₀ A)
    infer′ _ _ Level = do
      require⁰ level-is-small
      return U₀
    infer′ _ _ zeroᵘ = do
      require⁰ level-allowed
      return Level
    infer′ n Γ (1ᵘ+ l) = do
      require⁰ level-allowed
      check n Γ l Level
      return Level
    infer′ n Γ (l₁ supᵘₗ l₂) = do
      require⁰ level-allowed
      check n Γ l₁ Level
      check n Γ l₂ Level
      return Level
    infer′ n Γ (U l) = do
      l ← check-level n Γ l
      return (U (1ᵘ+ l))
    infer′ n Γ (Lift l A) = do
      l₁ ← check-level n Γ l
      l₂ ← infer-U n Γ A
      return (U (l₁ supᵘₗ l₂))
    infer′ n Γ (lift l t) = do
      l ← check-level n Γ l
      A ← infer n Γ t
      return (Lift l A)
    infer′ n Γ (lower t) = do
      A         ← infer-red n Γ t
      _ , B , _ ← is-Lift A
      return B
    infer′ _ _ (Unit s) = do
      require⁺ (unit-allowed s)
      return U₀
    infer′ _ _ (star s) = do
      require⁺ (unit-allowed s)
      return (Unit s)
    infer′ n Γ (unitrec A t₁ t₂) = do
      A  ← check-type n (Γ »∙ Unit 𝕨) A
      t₁ ← check n Γ t₁ (Unit 𝕨)
      check n Γ t₂ (subst A (sgSubst (star 𝕨)))
      require⁺ (unit-allowed 𝕨)
      return (subst A (sgSubst t₁))
    infer′ _ _ Empty =
      return U₀
    infer′ n Γ (emptyrec A t) = do
      A ← check-type n Γ A
      check n Γ t Empty
      return A
    infer′ n Γ (ΠΣ b p q A₁ A₂) = do
      B₁    ← infer-red n Γ A₁
      l , _ ← is-U B₁
      check n (Γ »∙ A₁) A₂ (U (wk[ 1 ] l))
      require⁺ (πσ-allowed b p q)
      return (U l)
    infer′ n Γ (lam p q A₁ t) = do
      A₁ ← check-type n Γ A₁
      A₂ ← infer n (Γ »∙ A₁) t
      require⁺ (π-allowed p q)
      return (Π p , q ▷ A₁ ▹ A₂)
    infer′ n Γ (app t₁ p t₂) = do
      A               ← infer-red n Γ t₁
      _ , A₁ , A₂ , _ ← is-ΠΣ BMΠ p A
      t₂ ← check n Γ t₂ A₁
      return (subst A₂ (sgSubst t₂))
    infer′ n Γ (prod s p q A₂ t₁ t₂) = do
      A₁ ← infer n Γ t₁
      A₂ ← check-type n (Γ »∙ A₁) A₂
      check n Γ t₂ (subst A₂ (sgSubst t₁))
      require⁺ (σ-allowed s p q)
      return (ΠΣ⟨ BMΣ s ⟩ p , q ▷ A₁ ▹ A₂)
    infer′ n Γ (fst p t) = do
      A          ← infer-red n Γ t
      _ , A₁ , _ ← is-ΠΣ (BMΣ 𝕤) p A
      return A₁
    infer′ n Γ (snd p t) = do
      A              ← infer-red n Γ t
      _ , _ , A₂ , _ ← is-ΠΣ (BMΣ 𝕤) p A
      return (subst A₂ (sgSubst (fst p t)))
    infer′ n Γ (prodrec p A t₁ t₂) = do
      B               ← infer-red n Γ t₁
      q , B₁ , B₂ , _ ← is-ΠΣ (BMΣ 𝕨) p B
      A               ← check-type n (Γ »∙ Σʷ p , q ▷ B₁ ▹ B₂) A
      check n (Γ »∙ B₁ »∙ B₂) t₂
        (Term[_,_].subst A $
         cons (wkSubst 2 id)
           (prod 𝕨 p (just (q , weaken (lift (U.stepn id 2)) B₂))
              (var x1) (var x0)))
      return (subst A (sgSubst t₁))
    infer′ _ _ ℕ =
      return U₀
    infer′ _ _ zero =
      return ℕ
    infer′ n Γ (suc t) = do
      check n Γ t ℕ
      return ℕ
    infer′ n Γ (natrec A t₁ t₂ t₃) = do
      A ← check-type n (Γ »∙ ℕ) A
      check n Γ t₁ (subst A (sgSubst zero))
      check n (Γ »∙ ℕ »∙ A) t₂
        (subst A (cons (wkSubst 2 id) (suc (var x1))))
      t₃ ← check n Γ t₃ ℕ
      return (subst A (sgSubst t₃))
    infer′ n Γ (Id A t₁ t₂) = do
      B     ← infer-red n Γ A
      l , _ ← is-U B
      check n Γ t₁ A
      check n Γ t₂ A
      return (U l)
    infer′ n Γ (rfl t) = do
      A ← infer n Γ t
      return (Id A t t)
    infer′ n Γ (J A₁ t₁ A₂ t₂ t₃ t₄) = do
      A₁ ← check-type n Γ A₁
      t₁ ← check n Γ t₁ A₁
      A₂ ←
        check-type n (Γ »∙ A₁ »∙ Id (wk[ 1 ] A₁) (wk[ 1 ] t₁) (var x0))
          A₂
      check n Γ t₂ (subst A₂ (cons (sgSubst t₁) (rfl (just t₁))))
      t₃ ← check n Γ t₃ A₁
      t₄ ← check n Γ t₄ (Id A₁ t₁ t₃)
      return (subst A₂ (cons (sgSubst t₃) t₄))
    infer′ n Γ (K A₁ t₁ A₂ t₂ t₃) = do
      A₁ ← check-type n Γ A₁
      t₁ ← check n Γ t₁ A₁
      A₂ ← check-type n (Γ »∙ Id A₁ t₁ t₁) A₂
      check n Γ t₂ (subst A₂ (sgSubst (rfl (just t₁))))
      t₃ ← check n Γ t₃ (Id A₁ t₁ t₁)
      require⁰ k-allowed
      return (subst A₂ (sgSubst t₃))
    infer′ n Γ ([]-cong s l A t₁ t₂ t₃) = do
      l  ← check-level n Γ l
      A  ← check-type n Γ A
      t₁ ← check n Γ t₁ A
      t₂ ← check n Γ t₂ A
      check n Γ t₃ (Id A t₁ t₂)
      require⁺ (box-cong-allowed s)
      return (Id (Erased s l A) (box s l t₁) (box s l t₂))

  -- A variant of infer that checks that the inferred type is U l for
  -- some universe level l. The level is returned.

  infer-U : Fuel → Cons c m n → Term c n → Check c (Lvl c n)
  infer-U n Γ A = do
    B     ← infer-red n Γ A
    l , _ ← is-U B
    return l

  -- An equality checker for variable contexts.

  equal-con : Fuel → Cons c m n → Con c n → Check c ⊤
  equal-con n Γ Δ = do
    eq ← equal-con-constructors⁼ (Γ .vars) Δ
    equal-con′ n (Γ .defs) eq

  private

    -- A helper function.

    equal-con′ :
      {Δ₁ Δ₂ : Con c n} →
      Fuel → DCon c m → Equal-con-constructors⁼ Δ₁ Δ₂ → Check c ⊤
    equal-con′ _ _ (base _) =
      return tt
    equal-con′ _ _ ε =
      return tt
    equal-con′ n ∇ (ext Δ₁ A₁ Δ₂ A₂) = do
      equal-con n (∇ » Δ₁) Δ₂
      equal-ty n (∇ » Δ₁) A₁ A₂

  -- A type-checker for substitutions.
  --
  -- The returned substitution is a possibly more annotated version of
  -- the input.

  check-sub :
    Fuel → DCon c m → Con c n₂ → Subst c n₂ n₁ → Con c n₁ →
    Check c (Subst c n₂ n₁)
  check-sub n ∇ Δ₂ σ Δ₁ =
    register ([check-sub] ∇ Δ₂ σ Δ₁) (check-sub′ n ∇ Δ₂ σ Δ₁)

  private

    -- A helper function.

    check-sub′ :
      Fuel → DCon c m → Con c n₂ → Subst c n₂ n₁ → Con c n₁ →
      Check c (Subst c n₂ n₁)
    check-sub′ n ∇ Δ₂ id Δ₁ = do
      equal-con n (∇ » Δ₂) Δ₁
      return id
    check-sub′ n ∇ Δ₂ (wk1 σ) Δ₁ = do
      Δ₂ , _ ← is-∙ Δ₂
      σ      ← check-sub n ∇ Δ₂ σ Δ₁
      return (wk1 σ)
    check-sub′ n ∇ Δ₂ (σ ⇑) Δ₁ = do
      Δ₂ , A , _ ← is-∙ Δ₂
      Δ₁ , B , _ ← is-∙ Δ₁
      σ          ← check-sub n ∇ Δ₂ σ Δ₁
      equal-ty n (∇ » Δ₂) A (subst B σ)
      return (σ ⇑)
    check-sub′ n ∇ Δ₂ (cons σ t) Δ₁ = do
      Δ₁ , B , _ ← is-∙ Δ₁
      σ          ← check-sub n ∇ Δ₂ σ Δ₁
      t          ← check n (∇ » Δ₂) t (subst B σ)
      return (cons σ t)

  -- Are the two terms equal at the given type?

  equal-tm : Fuel → Cons c m n → (t₁ t₂ A : Term c n) → Check c ⊤
  equal-tm 0 _ _ _ _ =
    no-fuel
  equal-tm (1+ n) Γ t₁ t₂ A = register ([equal-tm] Γ t₁ t₂ A) do
    A  ← red-ty n Γ A
    t₁ ← red-tm n Γ t₁ A
    t₂ ← red-tm n Γ t₂ A
    equal-tm-red n Γ t₁ t₂ A

  -- Are the two reduced terms equal at the given reduced type?

  equal-tm-red : Fuel → Cons c m n → (t₁ t₂ A : Term c n) → Check c ⊤
  equal-tm-red n Γ t₁ t₂ A with is-type-constructorˡ? A
  … | just (meta-var _ _) =
    equal-ne-red n Γ t₁ t₂ A
  … | just Level =
    case equal-level-cons? t₁ t₂ of λ where
      (just zeroᵘ)       → return tt
      (just (1ᵘ+ l₁ l₂)) → equal-tm n Γ l₁ l₂ Level
      nothing            → equal-ne-red n Γ t₁ t₂ A
  … | just (U l) =
    if-no-equality-reflection (equal-ty-red n Γ t₁ t₂)
      (equal-ty-red-U n Γ t₁ t₂ l)
  … | just (Lift _ A) =
    equal-tm n Γ (lower t₁) (lower t₂) A
  … | just Empty =
    equal-ne-red n Γ t₁ t₂ A
  … | just (Unit s) =
    case s ≟ˢ 𝕤 of λ where
      (just _) → return tt
      nothing  →
        if-no-equality-reflection
          (case are-star? t₁ t₂ of λ where
             (just _) → return tt
             nothing  → equal-ne-red n Γ t₁ t₂ A)
          (case are-star⟨ s ⟩? t₁ t₂ of λ where
             (just _) → return tt
             nothing  → equal-ne-red n Γ t₁ t₂ A)
          catch
        require⁺ (unit-with-η s)
  … | just ℕ =
    case are-zero-or-suc? t₁ t₂ of λ where
      (just (inj₁ _))             → return tt
      (just (inj₂ (t₁ , t₂ , _))) → equal-tm n Γ t₁ t₂ ℕ
      nothing                     → equal-ne-red n Γ t₁ t₂ A
  … | just (ΠΣ BMΠ p _ A₁ A₂) =
    equal-tm n (Γ »∙ A₁) (wk[ 1 ] t₁ ∘⟨ p ⟩ var x0)
      (wk[ 1 ] t₂ ∘⟨ p ⟩ var x0) A₂
  … | just (ΠΣ (BMΣ s) p _ A₁ A₂) = do
    case s ≟ˢ 𝕤 of λ where
      (just _) → do
        equal-tm n Γ (fst p t₁) (fst p t₂) A₁
        equal-tm n Γ (snd p t₁) (snd p t₂)
          (subst A₂ (sgSubst (fst p t₁)))
      nothing →
        if-no-equality-reflection
          (case are-prod? t₁ t₂ of λ where
             (just (_ , _ , _ , t₁₁ , t₁₂ ,
                    _ , _ , _ , t₂₁ , t₂₂ , _)) → do
               equal-tm n Γ t₁₁ t₂₁ A₁
               equal-tm n Γ t₁₂ t₂₂ (subst A₂ (sgSubst t₁₁))
             nothing →
               equal-ne-red n Γ t₁ t₂ A)
          (case are-prod⟨ s , p ⟩? t₁ t₂ of λ where
             (just (_ , t₁₁ , t₁₂ , _ , t₂₁ , t₂₂ , _)) → do
               -- Here check-and-equal-tm is used instead of
               -- equal-tm to avoid uses of injectivity lemmas.
               t₁ ← check-and-equal-tm n Γ t₁₁ t₂₁ A₁
               check-and-equal-tm n Γ t₁₂ t₂₂ (subst A₂ (sgSubst t₁))
               return tt
             nothing →
               equal-ne-red n Γ t₁ t₂ A)
  … | just (Id _ _ _) =
    case are-rfl? t₁ t₂ of λ where
      (just _) → return tt
      nothing  → equal-ne-red n Γ t₁ t₂ A
  … | nothing =
    equal-ne-red n Γ t₁ t₂ A

  -- Are the two possibly neutral terms equal at the given type? The
  -- terms are not assumed to be well-typed (see equal-ne-inf below
  -- for some motivation).

  equal-ne : Fuel → (Γ : Cons c m n) (t₁ t₂ A : Term c n) → Check c ⊤
  equal-ne n Γ t₁ t₂ A = do
    A′ ← equal-ne-inf n Γ t₁ t₂
    equal-ty n Γ A′ A

  -- Are the two possibly neutral terms equal at the given reduced
  -- type? The terms are not assumed to be well-typed (see
  -- equal-ne-inf below for some motivation).

  equal-ne-red :
    Fuel → (Γ : Cons c m n) (t₁ t₂ A : Term c n) → Check c ⊤
  equal-ne-red n Γ t₁ t₂ A = do
    A′ ← equal-ne-inf-red n Γ t₁ t₂
    equal-ty-red n Γ A′ A

  -- Are the two possibly neutral terms equal? In that case an
  -- inferred, reduced type is returned. The terms are not assumed to
  -- be well-typed (see equal-ne-inf below for some motivation).

  equal-ne-inf-red :
    Fuel → (Γ : Cons c m n) (t₁ t₂ : Term c n) → Check c (Term c n)
  equal-ne-inf-red n Γ t₁ t₂ = do
    A ← equal-ne-inf n Γ t₁ t₂
    red-ty n Γ A

  -- Are the two possibly neutral terms equal? In that case an
  -- inferred type is returned.
  --
  -- The test fails for (equal) variables if no inferred type is
  -- produced because the variables point to the base context.
  --
  -- The terms are not assumed to be well-typed. Instead they are
  -- checked to be well-typed. For a variant of the code without these
  -- checks (also without the check in equal-ne), and without the case
  -- for meta-variables in equal-ne-inf, it should be possible to
  -- prove the following soundness result:
  --
  --   equal-ne-inf-sound :
  --     ⦃ ok : No-equality-reflection ⦄ →
  --     ∀ {B₁ B₂} n →
  --     OK (equal-ne-inf n Γ t₁ t₂) A γ st →
  --     Contexts-wf (Γ .defs) γ →
  --     ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ∷ B₁ →
  --     ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₂ ⌝ γ ∷ B₂ →
  --     (⌜ Γ ⌝ᶜ γ ⊢ B₁ ≡ ⌜ A ⌝ γ) ×
  --     (⌜ Γ ⌝ᶜ γ ⊢ B₂ ≡ ⌜ A ⌝ γ) ×
  --     ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ≡ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ
  --
  -- However, meta-variables might not have unique types. A
  -- meta-variable that refers to the term rfl could for instance have
  -- many different types. They are treated somewhat like neutral
  -- terms in this code, but after translation they might not be
  -- neutral.
  --
  -- Having extra checks could be detrimental to performance. A way to
  -- avoid this problem might be to replace meta-variables by opaque
  -- definitions, which are neutral. However, meta-variables can refer
  -- to open terms, and at the time of writing opaque definitions
  -- cannot. Furthermore the use of de Bruijn levels can be
  -- problematic if one wants to leave a prefix of the context
  -- unspecified.
  --
  -- One aspect of the present structure of the code is that the
  -- soundness proof equal-ne-inf-sound does not use injectivity
  -- lemmas, unlike the lemma mentioned above: those lemmas are
  -- restricted in a setting with equality reflection.

  equal-ne-inf :
    Fuel → (Γ : Cons c m n) (t₁ t₂ : Term c n) → Check c (Term c n)
  equal-ne-inf 0      _ _  _  = no-fuel
  equal-ne-inf (1+ n) Γ t₁ t₂ =
    register ([equal-ne-inf] Γ t₁ t₂) do
      eq ← are-equal-eliminators t₁ t₂
      equal-ne-inf′ n Γ eq

  private

    -- A helper function.

    equal-ne-inf′ :
      {t₁ t₂ : Term c n} →
      Fuel → Cons c m n → Are-equal-eliminators t₁ t₂ →
      Check c (Term c n)
    equal-ne-inf′ n Γ (meta-var x₁ σ₁ x₂ σ₂ _) = do
      Δ₁      ← context-of x₁
      Δ₂ , A  ← is-term x₂
      PE.refl ← equal-sub′ n false Γ σ₁ Δ₁ σ₂ Δ₂
      are-equal-meta-vars x₁ x₂
      return (subst A σ₁)
    equal-ne-inf′ _ Γ (var x _) =
      index (Γ .vars) x
    equal-ne-inf′ _ Γ (defn α _) = do
      A ← type-of (Γ .defs) α
      return (weaken U.wk₀ A)
    equal-ne-inf′ n Γ (sup l₁₁ l₂₁ l₁₂ l₂₂ _) = do
      check-and-equal-level n Γ (l₁₁ supᵘₗ l₂₁) (l₁₂ supᵘₗ l₂₂)
      require⁰ level-allowed
      return Level
    equal-ne-inf′ n Γ (lower t₁ t₂ _) = do
      A          ← equal-ne-inf-red n Γ t₁ t₂
      _ , B ,  _ ← is-Lift A
      return B
    equal-ne-inf′ n Γ (emptyrec A₁ t₁ A₂ t₂ _) = do
      A ← check-and-equal-ty n Γ A₁ A₂
      equal-ne-red n Γ t₁ t₂ Empty
      return A
    equal-ne-inf′ n Γ (unitrec A₁ t₁₁ t₁₂ A₂ t₂₁ t₂₂ _) = do
      A ← check-and-equal-ty n (Γ »∙ Unit 𝕨) A₁ A₂
      equal-ne-red n Γ t₁₁ t₂₁ (Unit 𝕨)
      check-and-equal-tm n Γ t₁₂ t₂₂ (subst A (sgSubst (star 𝕨)))
      require⁺ (unit-allowed 𝕨)
      return (subst A (sgSubst t₁₁))
    equal-ne-inf′ n Γ (app p t₁₁ t₁₂ t₂₁ t₂₂ _) = do
      A               ← equal-ne-inf-red n Γ t₁₁ t₂₁
      _ , A₁ , A₂ , _ ← is-ΠΣ BMΠ p A
      t₂              ← check-and-equal-tm n Γ t₁₂ t₂₂ A₁
      return (subst A₂ (sgSubst t₂))
    equal-ne-inf′ n Γ (fst p t₁′ t₂′ _) = do
      A          ← equal-ne-inf-red n Γ t₁′ t₂′
      _ , A₁ , _ ← is-ΠΣ (BMΣ 𝕤) p A
      return A₁
    equal-ne-inf′ n Γ (snd p t₁′ t₂′ _) = do
      A              ← equal-ne-inf-red n Γ t₁′ t₂′
      _ , _ , A₂ , _ ← is-ΠΣ (BMΣ 𝕤) p A
      return (subst A₂ (sgSubst (fst p t₁′)))
    equal-ne-inf′ n Γ (prodrec p A₁ t₁₁ t₁₂ A₂ t₂₁ t₂₂ _) = do
      B               ← equal-ne-inf-red n Γ t₁₁ t₂₁
      q , B₁ , B₂ , _ ← is-ΠΣ (BMΣ 𝕨) p B
      A ← check-and-equal-ty n (Γ »∙ Σʷ p , q ▷ B₁ ▹ B₂) A₁ A₂
      check-and-equal-tm n (Γ »∙ B₁ »∙ B₂) t₁₂ t₂₂
        (subst A
           (cons (wkSubst 2 id)
              (prod 𝕨 p (just (q , weaken (lift (U.stepn id 2)) B₂))
                 (var x1) (var x0))))
      return (subst A (sgSubst t₁₁))
    equal-ne-inf′ n Γ (natrec A₁ t₁₁ t₁₂ t₁₃ A₂ t₂₁ t₂₂ t₂₃ _) = do
      A ← check-and-equal-ty n (Γ »∙ ℕ) A₁ A₂
      check-and-equal-tm n Γ t₁₁ t₂₁ (subst A (sgSubst zero))
      check-and-equal-tm n (Γ »∙ ℕ »∙ A) t₁₂ t₂₂
        (subst A (cons (wkSubst 2 id) (suc (var x1))))
      equal-ne-red n Γ t₁₃ t₂₃ ℕ
      return (subst A (sgSubst t₁₃))
    equal-ne-inf′
      n Γ (J A₁₁ t₁₁ A₁₂ t₁₂ t₁₃ t₁₄ A₂₁ t₂₁ A₂₂ t₂₂ t₂₃ t₂₄ _) = do
      A₁ ← check-and-equal-ty n Γ A₁₁ A₂₁
      t₁ ← check-and-equal-tm n Γ t₁₁ t₂₁ A₁
      A₂ ←
        check-and-equal-ty n
          (Γ »∙ A₁ »∙ Id (wk[ 1 ] A₁) (wk[ 1 ] t₁) (var x0)) A₁₂ A₂₂
      check-and-equal-tm n Γ t₁₂ t₂₂
        (subst A₂ (cons (sgSubst t₁) (rfl (just t₁))))
      t₃ ← check-and-equal-tm n Γ t₁₃ t₂₃ A₁
      equal-ne-red n Γ t₁₄ t₂₄ (Id A₁ t₁ t₃)
      return (subst A₂ (cons (sgSubst t₃) t₁₄))
    equal-ne-inf′ n Γ (K A₁₁ t₁₁ A₁₂ t₁₂ t₁₃ A₂₁ t₂₁ A₂₂ t₂₂ t₂₃ _) = do
      A₁ ← check-and-equal-ty n Γ A₁₁ A₂₁
      t₁ ← check-and-equal-tm n Γ t₁₁ t₂₁ A₁
      A₂ ← check-and-equal-ty n (Γ »∙ Id A₁ t₁ t₁) A₁₂ A₂₂
      check-and-equal-tm n Γ t₁₂ t₂₂
        (subst A₂ (sgSubst (rfl (just t₁))))
      equal-ne-red n Γ t₁₃ t₂₃ (Id A₁ t₁ t₁)
      require⁰ k-allowed
      return (subst A₂ (sgSubst t₁₃))
    equal-ne-inf′
      n Γ ([]-cong s l₁ A₁ t₁₁ t₁₂ t₁₃ l₂ A₂ t₂₁ t₂₂ t₂₃ _) = do
      l  ← check-and-equal-level n Γ l₁ l₂
      A  ← check-and-equal-ty n Γ A₁ A₂
      t₁ ← check-and-equal-tm n Γ t₁₁ t₂₁ A
      t₂ ← check-and-equal-tm n Γ t₁₂ t₂₂ A
      equal-ne-red n Γ t₁₃ t₂₃ (Id A t₁ t₂)
      require⁺ (box-cong-allowed s)
      return (Id (Erased s l A) (box s l t₁) (box s l t₂))

  -- Are the two types equal?

  equal-ty : Fuel → (Γ : Cons c m n) (A₁ A₂ : Term c n) → Check c ⊤
  equal-ty 0 _ _ _ =
    no-fuel
  equal-ty (1+ n) Γ A₁ A₂ = register ([equal-ty] Γ A₁ A₂) do
    A₁ ← red-ty n Γ A₁
    A₂ ← red-ty n Γ A₂
    equal-ty-red n Γ A₁ A₂

  -- Are the two reduced types equal?

  equal-ty-red :
    Fuel → (Γ : Cons c m n) (A₁ A₂ : Term c n) → Check c ⊤
  equal-ty-red n Γ A₁ A₂ with are-equal-type-constructors? A₁ A₂
  … | just (meta-var x₁ σ₁ x₂ σ₂ _) = do
    Δ₁ ← context-of x₁
    Δ₂ ← is-type n (Γ .defs) x₂
    PE.refl ← equal-sub′ n false Γ σ₁ Δ₁ σ₂ Δ₂
    are-equal-meta-vars x₁ x₂
    return tt
  … | just (Level _) =
    return tt
  … | just (U l₁ l₂ _) =
    equal-level n Γ l₁ l₂
  … | just (Lift l₁ A₁ l₂ A₂ _) = do
    equal-level n Γ l₁ l₂
    equal-ty n Γ A₁ A₂
  … | just (Empty _) =
    return tt
  … | just (Unit _) =
    return tt
  … | just (ΠΣ A₁₁ A₁₂ A₂₁ A₂₂ _) = do
    equal-ty n Γ A₁₁ A₂₁
    equal-ty n (Γ »∙ A₁₁) A₁₂ A₂₂
  … | just (ℕ _) =
    return tt
  … | just (Id A₁ t₁₁ t₁₂ A₂ t₂₁ t₂₂ _) = do
    equal-ty n Γ A₁ A₂
    equal-tm n Γ t₁₁ t₂₁ A₁
    equal-tm n Γ t₁₂ t₂₂ A₁
  … | nothing = do
    B ← equal-ne-inf-red n Γ A₁ A₂
    is-U B
    return tt

  -- Are the two reduced terms of type U l equal?
  --
  -- If equality reflection is disallowed, then it suffices to check
  -- that the terms are equal as types.

  equal-ty-red-U :
    Fuel → (Γ : Cons c m n) (A₁ A₂ : Term c n) (l : Lvl c n) → Check c ⊤
  equal-ty-red-U {c} n Γ A₁ A₂ l with are-equal-type-constructors? A₁ A₂
  … | just (meta-var x₁ σ₁ x₂ σ₂ _) = do
    Δ₁      ← context-of x₁
    Δ₂ , A  ← is-term x₂
    PE.refl ← equal-sub′ n false Γ σ₁ Δ₁ σ₂ Δ₂
    are-equal-meta-vars x₁ x₂
    equal-ty n Γ (subst A σ₁) (U l)
  … | just (Level _) =
    return tt
  … | just (U l₁ l₂ _) =
    equal-level n Γ l₁ l₂
  … | just (Lift l₁ A₁ l₂ A₂ _) = do
    equal-level n Γ l₁ l₂
    l₃ ← infer-U n Γ A₁
    A₂ ← check n Γ A₂ (U l₃)
    equal-tm n Γ A₁ A₂ (U l₃)
    equal-level n Γ (l₃ supᵘₗ l₁) l
  … | just (Empty _) =
    return tt
  … | just (Unit _) =
    return tt
  … | just (ΠΣ A₁₁ A₁₂ A₂₁ A₂₂ _) = do
    A₁ ← check-and-equal-tm n Γ A₁₁ A₂₁ (U l)
    check-and-equal-tm n (Γ »∙ A₁) A₁₂ A₂₂ (U (wk[ 1 ] l))
    return tt
  … | just (ℕ _) =
    return tt
  … | just (Id A₁ t₁₁ t₁₂ A₂ t₂₁ t₂₂ _) = do
    equal-tm n Γ A₁ A₂ (U l)
    equal-tm n Γ t₁₁ t₂₁ A₁
    equal-tm n Γ t₁₂ t₂₂ A₁
  … | nothing = do
    B ← equal-ne-inf-red n Γ A₁ A₂
    equal-ty n Γ B (U l)
    return tt

  -- Are the two levels equal?

  equal-level :
    Fuel → (Γ : Cons c m n) (l₁ l₂ : Term[ c , k ] n) → Check c ⊤
  equal-level n Γ l₁ l₂ = do
    nf₁ , ℓ₁ ← normalise-level false n Γ l₁
    nf₂ , ℓ₂ ← normalise-level false n Γ l₂
    [ M.dec⇒maybe (ℓ₁ ≟⁻ ℓ₂) ]with-message
      "Expected equal universe levels."
    below n Γ nf₁ nf₂
    below n Γ nf₂ nf₁

  -- "Normalises" level expressions.
  --
  -- If the boolean is true, then the level is reduced.

  normalise-level :
    Bool → Fuel → Cons c m n → Term[ c , k ] n → Check c (Lvlⁿ c n)
  normalise-level _ 0 _ _ =
    no-fuel
  normalise-level reduced (1+ n) Γ l =
    register ([normalise-level] Γ l) do
      l , _ ← really-remove-weaken-subst n l false
      normalise-level′ reduced n Γ (is-perhaps-level? l)

  private

    -- A helper function.

    normalise-level′ :
      {l : Term[ c , k ] n} →
      Bool → Fuel → Cons c m n → Maybe (Is-perhaps-level l) →
      Check c (Lvlⁿ c n)
    normalise-level′ _ _ _ (just (meta-var x σ)) =
      return ⌞ meta-var x σ ⌟ⁿ
    normalise-level′ _ _ _ (just zeroᵘ) =
      return zeroᵘⁿ
    normalise-level′ _ n Γ (just (1ᵘ+ l)) =
      1ᵘ+ⁿ <$> normalise-level false n Γ l
    normalise-level′ _ _ _ (just (ωᵘ+ m)) =
      return (ωᵘ+ⁿ m)
    normalise-level′ _ n Γ (just (level t)) =
      normalise-level false n Γ t
    normalise-level′ {k = lvl} _ n Γ (just (l₁ supᵘₗ l₂)) = do
      -- There is no general inversion lemma for S._supᵘₗ_, see
      -- Definition.Typed.Consequences.Inversion.¬-inversion-supᵘₗ, so
      -- it is checked that l₁ and l₂ are well-formed levels.
      l₁ ← check-level n Γ l₁
      l₂ ← check-level n Γ l₂
      supᵘₗⁿ <$> normalise-level false n Γ l₁ ⊛
        normalise-level false n Γ l₂
    normalise-level′ {k = tm} _ n Γ (just (l₁ supᵘₗ l₂)) = do
      supᵘₗⁿ <$> normalise-level false n Γ l₁ ⊛
        normalise-level false n Γ l₂
    normalise-level′ {k = tm} {l} false n Γ nothing = do
      require⁰ level-allowed
      l ← red-tm n Γ l Level
      normalise-level true n Γ l
    normalise-level′ {l} _ _ _ nothing =
      return ⌞ l ⌟ⁿ

  -- Compares (parts of) "normal" forms.

  below : Fuel → Cons c m n → Lvlⁿ′ c n → Lvlⁿ′ c n → Check c ⊤
  below n Γ ns₁ ns₂ = all (λ l₁ → any (below′ n Γ l₁) ns₂) ns₁

  private

    -- Some helper functions.

    below′ :
      Fuel → Cons c m n → Nat × Lvl c n → Nat × Lvl c n → Check c ⊤
    below′ n Γ (n₁ , l₁) (n₂ , l₂) = do
      [ M.dec⇒maybe (n₁ N.≤? n₂) ]with-message
        "The number is too large."
      case are-meta-variables? l₁ l₂ of λ where
        -- The first case is included because the levels might not be
        -- applications of level, and furthermore Level might not be
        -- allowed.
        (just (_ , x₁ , σ₁ , _ , x₂ , σ₂ , _)) → do
          Δ₁      ← context-of x₁
          Δ₂ , _  ← is-level n Γ x₂ σ₂
          PE.refl ← equal-sub′ n true Γ σ₁ Δ₁ σ₂ Δ₂
          are-equal-meta-vars x₁ x₂
        nothing → case are-level? l₁ l₂ of λ where
          (just (t₁ , t₂ , _)) → do
            require⁰ level-allowed
            equal-tm n Γ t₁ t₂ Level
          nothing →
            fail "Expected two terms."

  -- An equality checker for substitutions. This variant, unlike
  -- equal-sub below, is supposed to work for (at least some)
  -- substitutions that are not already known to be well-formed. It
  -- does this by invoking the type-checker.
  --
  -- If the boolean is true, then the second substitution is known to
  -- be well-formed.
  --
  -- This procedure is used by equal-ty-red and equal-ne-inf in the
  -- cases for meta-variables. Note that, even though x, x[σ₁] and
  -- x[σ₂] are well-typed, it might not be the case that σ₁ and σ₂
  -- are. This procedure addresses this by checking if σ₁ and σ₂ are
  -- well-typed.
  --
  -- Another approach might be to use a dedicated type-system in which
  -- x[σ] is only well-typed if both x and σ are. That would however
  -- lead to a fair amount of code that is very similar to existing
  -- code (a type system, inversion lemmas, possibly well-formedness
  -- lemmas, and maybe other things). If the main type system already
  -- had (perhaps optional) support for explicit substitutions, then
  -- this approach might not be so bad, though.
  --
  -- Another complication addressed by this procedure is that if n is
  -- not known, then code that checks if x₁ : Fin n and x₂ : Fin n are
  -- equal can get stuck. For that reason this code takes two "source"
  -- variable contexts, and the substitutions are allowed to have
  -- different "source" indices. If the code succeeds, then a proof of
  -- equality between the indices is returned.
  --
  -- The test compares the "source" contexts:
  --
  -- * If they are both empty, then the substitutions are equal.
  --
  -- * If they are both the base context, then it is checked that both
  --   substitutions are equal to the same number of applications of
  --   wk1 to id. The base context's size might be a meta-level
  --   variable, so no attempt is made to handle the substitution
  --   constructors _⇑ and cons, for which the source size is
  --   1+ something.
  --
  -- * If they are both non-empty, then the tails of the substitutions
  --   are compared recursively. Furthermore it is checked that the
  --   heads are type-correct and equal (the test of type-correctness
  --   would not be required if the substitutions were known to be
  --   type-correct).
  --
  --   Note that the tail operation does not add new _⇑ or cons
  --   constructors to a substitution.

  equal-sub′ :
    Fuel → Bool → Cons c m n₃ → Subst c n₃ n₁ → Con c n₁ →
    Subst c n₃ n₂ → Con c n₂ → Check c (n₁ PE.≡ n₂)
  equal-sub′ n σ₂-ok Γ σ₁ Δ₁ σ₂ Δ₂ = do
    eq ← equal-con-constructors Δ₁ Δ₂
    case eq of λ where
      ε →
        return PE.refl
      (ext Δ₁ _ Δ₂ A) → do
        σ₁₊     ← return (tailₛ σ₁)
        PE.refl ← equal-sub′ n σ₂-ok Γ σ₁₊ Δ₁ (tailₛ σ₂) Δ₂
        if σ₂-ok
          then
            (do A[σ₁₊] ← return (subst A σ₁₊)
                σ₁₀    ← check n Γ (headₛ σ₁) A[σ₁₊]
                equal-tm n Γ σ₁₀ (headₛ σ₂) A[σ₁₊]
                return PE.refl)
          else
            (do check-and-equal-tm n Γ (headₛ σ₁) (headₛ σ₂)
                  (subst A σ₁₊)
                return PE.refl)
      base → do
        both k _ ← both-wk1-id σ₁ σ₂
        equal-sub″ k (Γ .vars)
        return PE.refl

  -- A procedure that checks two types and then checks that they are
  -- equal.
  --
  -- The returned type is a possibly more annotated version of the
  -- input.

  check-and-equal-ty :
    Fuel → Cons c m n → Term c n → Term c n → Check c (Term c n)
  check-and-equal-ty n Γ A₁ A₂ = do
    A₁ ← check-type n Γ A₁
    A₂ ← check-type n Γ A₂
    equal-ty n Γ A₁ A₂
    return A₁

  -- A procedure that checks two universe levels and then checks that
  -- they are equal.
  --
  -- The returned level is a possibly more annotated version of the
  -- input.

  check-and-equal-level :
    Fuel → Cons c m n → (l₁ l₂ : Term[ c , k ] n) →
    Check c (Term[ c , k ] n)
  check-and-equal-level n Γ l₁ l₂ = do
    l₁ ← check-level n Γ l₁
    l₂ ← check-level n Γ l₂
    equal-level n Γ l₁ l₂
    return l₁

  -- A procedure that checks two terms of type A and then checks that
  -- the terms are equal at type A. The type is assumed to be
  -- well-formed.
  --
  -- The returned term is a possibly more annotated version of the
  -- input.

  check-and-equal-tm :
    Fuel → Cons c m n → Term c n → Term c n → Term c n →
    Check c (Term c n)
  check-and-equal-tm n Γ t₁ t₂ A = do
    t₁ ← check n Γ t₁ A
    t₂ ← check n Γ t₂ A
    equal-tm n Γ t₁ t₂ A
    return t₁

-- A procedure that checks a type and a term of the given type.
--
-- The returned term and type are possibly more annotated versions of
-- the inputs.

check-type-and-term :
  Fuel → Cons c m n → Term c n → Term c n →
  Check c (Term c n × Term c n)
check-type-and-term n Γ t A = do
  A ← check-type n Γ A
  t ← check n Γ t A
  return (t , A)

-- A procedure that checks a type and two terms, and checks that the
-- two terms are equal.

check-and-equal-type-and-terms :
  Fuel → Cons c m n → Term c n → Term c n → Term c n → Check c ⊤
check-and-equal-type-and-terms n Γ t₁ t₂ A = do
  A ← check-type n Γ A
  check-and-equal-tm n Γ t₁ t₂ A
  return tt

-- An equality checker for substitutions. This variant, unlike
-- equal-sub′, is only supposed to work for substitutions that are
-- already known to be type-correct and that have equal indices.

equal-sub :
  Fuel → Cons c m n₂ → Subst c n₂ n₁ → Subst c n₂ n₁ → Con c n₁ →
  Check c ⊤
equal-sub _ _ _ _ ε =
  return tt
equal-sub n Γ σ₁ σ₂ (Δ ∙ B) = do
  equal-sub n Γ σ₁₊ (tailₛ σ₂) Δ
  equal-tm n Γ (headₛ σ₁) (headₛ σ₂) (subst B σ₁₊)
  where
  σ₁₊ = tailₛ σ₁
equal-sub _ Γ σ₁ σ₂ base = do
  both k _ ← both-wk1-id σ₁ σ₂
  equal-sub″ k (Γ .vars)

-- A procedure that checks a variable context.
--
-- The returned context is a possibly more annotated version of the
-- input.

check-con : Fuel → DCon c m → Con c n → Check c (Con c n)
check-con _ _ (base {b}) =
  return (base {b = b})
check-con _ _ ε =
  return ε
check-con n ∇ (Δ ∙ A) = do
  Δ ← check-con n ∇ Δ
  A ← check-type n (∇ » Δ) A
  return (Δ ∙ A)

-- A procedure that checks a definition context.
--
-- The unfolding mode is required to be transitive if any opaque
-- definition is encountered (or if base (opa something) is
-- encountered).
--
-- The meta-variable context is required to be empty if a context
-- extension is encountered. An alternative might be to check that
-- meta-variables that are used in a definition do not make use of
-- that definition or any later definitions.

check-dcon : Fuel → DCon c m → Check c ⊤
check-dcon _ (base nothing) =
  return tt
check-dcon _ (base (just _)) =
  require⁰ unfolding-mode-transitive
check-dcon _ ε =
  return tt
check-dcon {c} n (∇ ∙⟨ tra ⟩[ t ∷ A ]) = do
  check-meta-con-empty
  check-dcon n ∇
  check-type-and-term n (∇ » ε) t A
  return tt
check-dcon {c} n (∇ ∙⟨ opa o ⟩[ t ∷ A ]) = do
  check-meta-con-empty
  check-dcon n ∇
  check-type n (∇ » ε) A
  check n (Trans o ∇ » ε) t A
  require⁰ opacity-allowed
  require⁰ unfolding-mode-transitive

-- A procedure that checks a context pair.
--
-- The returned context pair is a possibly more annotated version of
-- the input.

check-cons : Fuel → Cons c m n → Check c (Cons c m n)
check-cons n (∇ » Γ) = do
  check-dcon n ∇
  Γ ← check-con n ∇ Γ
  return (∇ » Γ)

-- A procedure that checks a context pair, a type and a term.

check-cons-type-and-term :
  Fuel → Cons c m n → Term c n → Term c n → Check c ⊤
check-cons-type-and-term n Γ t A = do
  Γ ← check-cons n Γ
  check-type-and-term n Γ t A
  return tt

-- A procedure that checks a context pair, a type and two terms, and
-- checks that the two terms are equal.

check-and-equal-cons-type-and-terms :
  Fuel → Cons c m n → Term c n → Term c n → Term c n → Check c ⊤
check-and-equal-cons-type-and-terms n Γ t₁ t₂ A = do
  Γ ← check-cons n Γ
  check-and-equal-type-and-terms n Γ t₁ t₂ A

------------------------------------------------------------------------
-- Some observations

opaque

  -- If equality reflection is allowed, then red and red-tm can
  -- succeed in reducing a well-typed term without returning a WHNF.

  successful-reduction-without-WHNF :
    Equality-reflection →
    let n = 3 N.+ n
        Γ = record { defs = ε; vars = ε ∙ Empty }
        t = emptyrec ω ℕ zero
        u = t
        A = ℕ
    in
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ∷ ⌜ A ⌝ γ ×
    OK (red n Γ t) u γ st ×
    OK (red-tm n Γ t A) u γ st ×
    ¬ Whnf (⌜ Γ ⌝ᶜ γ .defs) (⌜ u ⌝ γ)
  successful-reduction-without-WHNF okᵉ =
    let ⊢Γ = ∙ ⊢Empty εε in
    emptyrecⱼ (⊢ℕ ⊢Γ)
      (_⊢_∷_.conv (zeroⱼ ⊢Γ) $
       univ (⊢∷Empty→⊢≡∷ okᵉ (var₀ (⊢Empty εε)) (ℕⱼ ⊢Γ) (Emptyⱼ ⊢Γ))) ,
    ok! ,
    OK-register
      (OK-if-no-equality-reflection ok! $
       OK->>= (OK-register (OK-if-no-equality-reflection ok! ok!))
         ok!) ,
    (λ { (ne (emptyrecₙ ())) })

opaque

  -- If weak unit types are allowed and Unitʷ-η holds, then the
  -- functions red and red-tm can return a term that is not a WHNF,
  -- and that is not the result of reducing the initial term.
  --
  -- This problem could presumably be averted by checking if Unitʷ-η
  -- holds or not, but that check might get stuck at compile-time: the
  -- idea is that red and red-tm should work even if the
  -- Type-restrictions record is a variable.

  successful-reduction-without-reduction-sequence :
    Unitʷ-allowed →
    Unitʷ-η →
    let n = 4 N.+ n
        Γ = emptyᶜ »∙ Unit 𝕨
        t = unitrec ω ω ℕ (unitrec ω ω (Unit 𝕨) (star 𝕨) (var x0)) zero
        u = unitrec ω ω ℕ (var x0) zero
        A = ℕ
    in
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ∷ ⌜ A ⌝ γ ×
    OK (red n Γ t) u γ st ×
    OK (red-tm n Γ t A) u γ st ×
    ¬ Whnf (⌜ Γ ⌝ᶜ γ .defs) (⌜ u ⌝ γ) ×
    ¬ ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ⇒* ⌜ u ⌝ γ ∷ ⌜ A ⌝ γ
  successful-reduction-without-reduction-sequence okᵘ η =
    let ⊢Unit′ = ⊢Unit εε okᵘ
        ⊢Unit″ = ⊢Unit (∙ ⊢Unit′) okᵘ
        ⊢ℕ     = ⊢ℕ (∙ ⊢Unit″)
        ⊢ur    = unitrecⱼ′ (⊢Unit (∙ ⊢Unit″) okᵘ) (starⱼ (∙ ⊢Unit′) okᵘ)
                   (var₀ ⊢Unit′)
        ⊢0     = zeroⱼ (∙ ⊢Unit′)
    in
    unitrecⱼ′ ⊢ℕ ⊢ur ⊢0 ,
    ok! ,
    OK-register
      (OK-if-no-equality-reflection ok! $
       OK->>=
         (OK-register $
          OK-if-no-equality-reflection ok! $
          OK->>=
            (OK-register (OK-if-no-equality-reflection ok! ok!))
            (OK-register (OK-if-no-equality-reflection ok! ok!)))
         ok!) ,
    (λ { (ne (unitrecₙ no-η _)) → no-η η }) ,
    (λ where
       (t⇒u ⇨ u⇒*v) →
         case whrDetTerm t⇒u (unitrec-β-η ⊢ℕ ⊢ur ⊢0 okᵘ η) of λ {
           PE.refl →
         case whnfRed*Term u⇒*v zeroₙ of λ () })

------------------------------------------------------------------------
-- Soundness proofs

opaque
 unfolding S._supᵘₗ_
 mutual

  -- Soundness for red for terms, under the assumption that equality
  -- reflection is not allowed (or that the variable context is
  -- empty).
  --
  -- It is not proved that the resulting term is a WHNF, or that the
  -- initial term reduces to the resulting term (only that the two
  -- terms are judgementally equal), see
  -- successful-reduction-without-reduction-sequence.

  red-sound-⊢∷ :
    ⦃ ok : No-equality-reflection or-empty (⌜ Γ ⌝ᶜ γ) .vars ⦄ →
    ∀ {A} n → OK (red n Γ t) u γ st →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ∷ A →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ≡ ⌜ u ⌝ γ ∷ A
  red-sound-⊢∷     0      not-ok
  red-sound-⊢∷ {t} (1+ n) eq     = red′-sound-⊢∷ n t (inv-register eq)

  private

    -- Soundness for red.

    red′-sound-⊢∷ :
      ⦃ ok : No-equality-reflection or-empty (⌜ Γ ⌝ᶜ γ) .vars ⦄ →
      ∀ {A} n t → OK (red′ n Γ t) u γ st →
      ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ∷ A →
      ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ≡ ⌜ u ⌝ γ ∷ A
    red′-sound-⊢∷ _ (meta-var _ _) ok! ⊢x =
      refl ⊢x
    red′-sound-⊢∷ {γ} {u} n (weaken ρ t) eq ⊢wk-ρ-t =
      let open TmR
          eq′ = PE.sym (⌜wk⌝ t)
      in
      U.wk ρ (⌜ t ⌝ γ)  ≡⟨ eq′ ⟩⊢≡
      ⌜ wk ρ t ⌝ γ      ≡⟨ red-sound-⊢∷ n eq $
                           PE.subst (flip (_⊢_∷_ _) _) eq′ ⊢wk-ρ-t ⟩⊢∎
      ⌜ u ⌝ γ           ∎
    red′-sound-⊢∷ {γ} {u} n (subst t σ) eq ⊢t[σ] =
      let open TmR
          eq′ = PE.sym (⌜[]⌝ t (term₂ ⊢t[σ]))
      in
      ⌜ t ⌝ γ U.[ ⌜ σ ⌝ˢ γ ]  ≡⟨ eq′ ⟩⊢≡
      ⌜ t [ σ ] ⌝ γ           ≡⟨ red-sound-⊢∷ n eq $
                                 PE.subst (flip (_⊢_∷_ _) _) eq′ ⊢t[σ] ⟩⊢∎
      ⌜ u ⌝ γ                 ∎
    red′-sound-⊢∷ _ (var _) ok! ⊢x =
      refl ⊢x
    red′-sound-⊢∷ {Γ} {γ} {u} {A} n (defn α) eq ⊢α
      using inv (t , _) eq₁ eq ← inv->>= eq
      with inv->>= eq
    … | inv t′ eq₂ ok! =
      let ⊢Γ               = wf ⊢α
          A′ , α↦A′ , A≡A′ = inversion-defn ⊢α
          α↦t∷A″ , A″≡A′   = Σ.map idᶠ (λ hyp → hyp α↦A′) $
                             definition-of-sound (Γ .defs) eq₁
                               (defn-wf ⊢Γ)

          open TmR
      in
               ∷ A               ⟨ A≡A′ ⟩≡∷
      U.defn α ∷ U.wk U.wk₀ A′  ≡⟨ _⊢_≡_∷_.conv (δ-red ⊢Γ α↦t∷A″ PE.refl PE.refl) $
                                   W.wk (W.wk₀∷ʷ⊇ ⊢Γ) A″≡A′ ⟩⊢∷
      U.wk U.wk₀ (⌜ t ⌝ γ)      ≡⟨ W.wk (W.wk₀∷ʷ⊇ ⊢Γ) $
                                   red-sound-⊢∷ ⦃ ok = ε ⦄ n eq₂ $
                                   conv (wf-↦∷∈ α↦t∷A″ (defn-wf ⊢Γ)) A″≡A′ ⟩⊢∎≡
      U.wk U.wk₀ (⌜ t′ ⌝ γ)     ≡˘⟨ ⌜wk⌝ t′ ⟩
      ⌜ wk U.wk₀ t′ ⌝ γ         ≡⟨⟩
      ⌜ u ⌝ γ                   ∎
    red′-sound-⊢∷ _ Level ok! ⊢Level =
      refl ⊢Level
    red′-sound-⊢∷ _ zeroᵘ ok! ⊢zeroᵘ =
      refl ⊢zeroᵘ
    red′-sound-⊢∷ _ (1ᵘ+ _) ok! ⊢1ᵘ+ =
      refl ⊢1ᵘ+
    red′-sound-⊢∷ {γ} {u} {A} n (l₁ supᵘₗ l₂) eq ⊢sup
      with inv->>= eq
    … | inv l₁′ eq₁ eq
      using ⊢l₁ , ⊢l₂ , A≡Level ← inversion-supᵘₗ-⊢∷ ⊢sup
          | okᴸ                 ← inversion-Level-⊢
                                    (wf-⊢≡ A≡Level .proj₂)
          | l₁≡l₁′              ← red-sound-⊢∷ n eq₁ ⊢l₁
          | l₁⊔l₂≡              ←
              ⊢≡∷Level→⊢≡∷Level okᴸ $
              supᵘₗ-cong (term-⊢≡∷ l₁≡l₁′) (refl-⊢≡∷L (term-⊢∷ ⊢l₂))
      with level-con? l₁′ | eq
    … | nothing | ok! =
      let open TmR in
                        ∷ A         ⟨ A≡Level ⟩≡∷
      ⌜ l₁ supᵘₗ l₂ ⌝ γ ∷ U.Level  ≡⟨ l₁⊔l₂≡ ⟩⊢∷∎≡
      ⌜ l₁′ supᵘₗ l₂ ⌝ γ           ≡⟨⟩
      ⌜ u ⌝ γ                      ∎
    … | just zeroᵘ | eq =
      let open TmR in
                        ∷ A         ⟨ A≡Level ⟩≡∷
      ⌜ l₁ supᵘₗ l₂ ⌝ γ ∷ U.Level  ≡⟨ l₁⊔l₂≡ ⟩⊢∷
      ⌜ zeroᵘ supᵘₗ l₂ ⌝ γ         ≡⟨ ⊢≡∷Level→⊢≡∷Level okᴸ $
                                      supᵘₗ-zeroˡ (term-⊢∷ ⊢l₂) ⟩⊢
      ⌜ l₂ ⌝ γ                     ≡⟨ red-sound-⊢∷ n eq ⊢l₂ ⟩⊢∎
      ⌜ u ⌝ γ                      ∎
    … | just (1ᵘ+ l₁″) | eq
      with inv->>= eq
    … | inv l₂′ eq₂ eq
      using _ , _ , ⊢l₁′ ← wf-⊢≡∷ l₁≡l₁′
          | l₂≡l₂′       ← red-sound-⊢∷ n eq₂ ⊢l₂
          | l₁′⊔l₂≡      ←
              ⊢≡∷Level→⊢≡∷Level okᴸ $
              supᵘₗ-cong (refl-⊢≡∷L (term-⊢∷ ⊢l₁′)) (term-⊢≡∷ l₂≡l₂′)
      with level-con? l₂′ | eq
    … | nothing | ok! =
      let open TmR in
                        ∷ A         ⟨ A≡Level ⟩≡∷
      ⌜ l₁ supᵘₗ l₂ ⌝ γ ∷ U.Level  ≡⟨ l₁⊔l₂≡ ⟩⊢∷
      ⌜ 1ᵘ+ l₁″ supᵘₗ l₂ ⌝ γ       ≡⟨ l₁′⊔l₂≡ ⟩⊢∎≡
      ⌜ 1ᵘ+ l₁″ supᵘₗ l₂′ ⌝ γ      ≡⟨⟩
      ⌜ u ⌝ γ                      ∎
    … | just zeroᵘ | ok! =
      let open TmR in
                        ∷ A         ⟨ A≡Level ⟩≡∷
      ⌜ l₁ supᵘₗ l₂ ⌝ γ ∷ U.Level  ≡⟨ l₁⊔l₂≡ ⟩⊢∷
      ⌜ 1ᵘ+ l₁″ supᵘₗ l₂ ⌝ γ       ≡⟨ l₁′⊔l₂≡ ⟩⊢
      ⌜ 1ᵘ+ l₁″ supᵘₗ zeroᵘ ⌝ γ    ≡⟨ ⊢≡∷Level→⊢≡∷Level okᴸ $
                                      supᵘₗ-zeroʳ (term-⊢∷ ⊢l₁′) ⟩⊢∎≡
      ⌜ 1ᵘ+ l₁″ ⌝ γ                ≡⟨⟩
      ⌜ u ⌝ γ                      ∎
    … | just (1ᵘ+ l₂″) | ok! =
      let ⊢l₁″ , _     = inversion-sucᵘ ⊢l₁′
          _ , _ , ⊢l₂′ = wf-⊢≡∷ l₂≡l₂′
          ⊢l₂″ , _     = inversion-sucᵘ ⊢l₂′

          open TmR
      in
                        ∷ A         ⟨ A≡Level ⟩≡∷
      ⌜ l₁ supᵘₗ l₂ ⌝ γ ∷ U.Level  ≡⟨ l₁⊔l₂≡ ⟩⊢∷
      ⌜ 1ᵘ+ l₁″ supᵘₗ l₂ ⌝ γ       ≡⟨ l₁′⊔l₂≡ ⟩⊢
      ⌜ 1ᵘ+ l₁″ supᵘₗ 1ᵘ+ l₂″ ⌝ γ  ≡⟨ ⊢≡∷Level→⊢≡∷Level okᴸ $
                                      supᵘₗ-1ᵘ+ (term-⊢∷ ⊢l₁″) (term-⊢∷ ⊢l₂″) ⟩⊢∎≡
      ⌜ 1ᵘ+ (l₁″ supᵘₗ l₂″) ⌝ γ    ≡⟨⟩
      ⌜ u ⌝ γ                      ∎
    red′-sound-⊢∷ _ (U _) ok! ⊢U =
      refl ⊢U
    red′-sound-⊢∷ _ (Lift _ _) ok! ⊢Lift =
      refl ⊢Lift
    red′-sound-⊢∷ _ (lift _ _) ok! ⊢lift =
      refl ⊢lift
    red′-sound-⊢∷ {γ} {u} {A} n (lower t) eq ⊢lower
      with inv->>= eq
    … | inv t′ eq₁ eq
      using _ , B , ⊢t , A≡B ← inversion-lower ⊢lower
          | lower-t≡lower-t′ ← lower-cong (red-sound-⊢∷ n eq₁ ⊢t)
      with is-lift? t′ | eq
    … | just (l , t″ , PE.refl) | eq₂ =
      let _ , _ , ⊢lift , B≡C =
            inversion-lower (wf-⊢≡∷ lower-t≡lower-t′ .proj₂ .proj₂)
          ⊢t″ =
            conv (inversion-lift-Lift ⊢lift) (sym B≡C)

          open TmR
      in
                              ∷ A   ⟨ A≡B ⟩≡∷
      ⌜ lower t           ⌝ γ ∷ B  ≡⟨ lower-t≡lower-t′ ⟩⊢∷
      ⌜ lower (lift l t″) ⌝ γ      ≡⟨ Lift-β′ ⊢t″ ⟩⊢
      ⌜ t″ ⌝ γ                     ≡⟨ red-sound-⊢∷ n eq₂ ⊢t″ ⟩⊢∎
      ⌜ u ⌝ γ                      ∎
    … | nothing | ok! =
      let open TmR in
                     ∷ A   ⟨ A≡B ⟩≡∷
      ⌜ lower t  ⌝ γ ∷ B  ≡⟨ lower-t≡lower-t′ ⟩⊢∷∎≡
      ⌜ lower t′ ⌝ γ      ≡⟨⟩
      ⌜ u ⌝ γ             ∎
    red′-sound-⊢∷ _ Empty ok! ⊢Empty =
      refl ⊢Empty
    red′-sound-⊢∷ n (emptyrec _ _ _) eq ⊢er
      with inv->>= eq
    … | inv _ eq ok! =
      let ⊢A , ⊢t , ≡A = inversion-emptyrec ⊢er in
      conv (emptyrec-cong (refl ⊢A) (red-sound-⊢∷ n eq ⊢t)) (sym ≡A)
    red′-sound-⊢∷ _ (Unit _) ok! ⊢Unit =
      refl ⊢Unit
    red′-sound-⊢∷ _ (star _) ok! ⊢star =
      refl ⊢star
    red′-sound-⊢∷ {γ} {u} {A} n (unitrec p q B t₁ t₂) eq ⊢ur
      with inv->>= eq
    … | inv t₁′ eq₁ eq₂
      using ⊢B , ⊢t₁ , ⊢t₂ , A≡ ← inversion-unitrec ⊢ur
          | t₁≡                 ← red-sound-⊢∷ n eq₁ ⊢t₁
          | ur≡                 ← unitrec-cong′ (refl ⊢B) t₁≡ (refl ⊢t₂)
      with is-star? t₁′ | eq₂
    … | just (s , ≡star) | eq₂ =
      let s≡𝕨 , _ =
            inversion-star-Unit $
            PE.subst (flip (_⊢_∷_ _) _) (PE.cong (flip ⌜_⌝ _) ≡star)
              (wf-⊢≡∷ t₁≡ .proj₂ .proj₂)
          ≡star =
            PE.trans (PE.cong (flip ⌜_⌝ _) ≡star) $
            PE.cong U.star s≡𝕨

          open TmR
      in
                                        ∷ A                          ⟨ A≡ ⟩≡∷
      ⌜ unitrec p q B t₁         t₂ ⌝ γ ∷ ⌜ B ⌝ γ U.[ ⌜ t₁ ⌝ γ ]₀   ≡⟨ ur≡ ⟩⊢∷
      ⌜ unitrec p q B t₁′        t₂ ⌝ γ                             ≡⟨ PE.cong (flip (U.unitrec _ _ _) _) ≡star ⟩⊢≡
                                                                     ⟨ subst-⊢≡₀ ⊢B t₁≡ ⟩≡
                                        ∷ ⌜ B ⌝ γ U.[ ⌜ t₁′ ⌝ γ ]₀   ⟨ PE.cong (⌜ B ⌝ _ U.[_]₀) ≡star ⟩≡∷≡
      ⌜ unitrec p q B (star 𝕨) t₂ ⌝ γ   ∷ ⌜ B ⌝ γ U.[ U.starʷ ]₀    ⇒⟨ unitrec-β-⇒ ⊢B ⊢t₂ ⟩⊢∷
      ⌜ t₂ ⌝ γ                                                      ≡⟨ red-sound-⊢∷ n eq₂ ⊢t₂ ⟩⊢∎
      ⌜ u ⌝ γ                                                       ∎
    … | nothing | ok! =
      let open TmR in
                                 ∷ A                         ⟨ A≡ ⟩≡∷
      ⌜ unitrec p q B t₁  t₂ ⌝ γ ∷ ⌜ B ⌝ γ U.[ ⌜ t₁ ⌝ γ ]₀  ≡⟨ ur≡ ⟩⊢∷∎≡
      ⌜ unitrec p q B t₁′ t₂ ⌝ γ                            ≡⟨⟩
      ⌜ u ⌝ γ                                               ∎
    red′-sound-⊢∷ _ (ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _) ok! ⊢ΠΣ =
      refl ⊢ΠΣ
    red′-sound-⊢∷ _ (lam _ _ _) ok! ⊢lam =
      refl ⊢lam
    red′-sound-⊢∷ {γ} {u} {A} n (t₁ ∘⟨ p ⟩ t₂) eq ⊢app
      with inv->>= eq
    … | inv t₁′ eq₁ eq₂
      using _ , C , _ , ⊢t₁ , ⊢t₂ , A≡ ← inversion-app ⊢app
          | t₁≡t₁′                     ← red-sound-⊢∷ n eq₁ ⊢t₁
          | _ , _ , ⊢t₁′               ← wf-⊢≡∷ t₁≡t₁′
          | t₁∘t₂≡t₁′∘t₂               ← app-cong t₁≡t₁′ (refl ⊢t₂)
      with is-lam? t₁′ | eq₂
    … | just (_ , qC , t₁″ , eq₃) | eq₂ =
      let C′ , ⊢t₁″ , C′≡C , p≡p′ , Π-ok =
            inversion-lam-Π $
            PE.subst (flip (_⊢_∷_ _) _) (PE.cong (flip ⌜_⌝ _) eq₃) ⊢t₁′
          ⌜t₁″⌝[]≡ =
            ⌜[]⌝ t₁″ (term₂ (subst-⊢₀ ⊢t₁″ ⊢t₂))

          open TmR
      in
                                   ∷ A                     ⟨ A≡ ⟩≡∷
      ⌜ t₁           ∘⟨ p ⟩ t₂ ⌝ γ ∷ C U.[ ⌜ t₂ ⌝ γ ]₀    ≡⟨ t₁∘t₂≡t₁′∘t₂ ⟩⊢∷
      ⌜ t₁′          ∘⟨ p ⟩ t₂ ⌝ γ                        ≡⟨ PE.cong (U._∘⟨ _ ⟩ _) $
                                                             PE.trans (PE.cong (flip ⌜_⌝ _) eq₃) $
                                                             PE.cong (flip U.lam _) (PE.sym p≡p′) ⟩⊢≡
                                                          ˘⟨ C′≡C (refl ⊢t₂) ⟩≡
      ⌜ lam p  qC t₁″ ∘⟨ p ⟩ t₂ ⌝ γ ∷ C′ U.[ ⌜ t₂ ⌝ γ ]₀  ⇒⟨ β-red-⇒ ⊢t₁″ ⊢t₂ Π-ok ⟩⊢∷
      ⌜ t₁″ ⌝ γ U.[ ⌜ t₂ ⌝ γ ]₀                           ≡˘⟨ ⌜t₁″⌝[]≡ ⟩⊢≡
      ⌜ t₁″ [ sgSubst t₂ ] ⌝ γ                            ≡⟨ red-sound-⊢∷ n eq₂ $
                                                             PE.subst (flip (_⊢_∷_ _) _) (PE.sym ⌜t₁″⌝[]≡) $
                                                             subst-⊢₀ ⊢t₁″ ⊢t₂ ⟩⊢∎
      ⌜ u ⌝ γ                                             ∎
    … | nothing | ok! =
      let open TmR in
                          ∷ A                   ⟨ A≡ ⟩≡∷
      ⌜ t₁  ∘⟨ p ⟩ t₂ ⌝ γ ∷ C U.[ ⌜ t₂ ⌝ γ ]₀  ≡⟨ t₁∘t₂≡t₁′∘t₂ ⟩⊢∷∎≡
      ⌜ t₁′ ∘⟨ p ⟩ t₂ ⌝ γ                      ≡⟨⟩
      ⌜ u ⌝ γ                                  ∎
    red′-sound-⊢∷ _ (prod _ _ _ _ _) ok! ⊢prod =
      refl ⊢prod
    red′-sound-⊢∷ {γ} {u} {A} n (fst p t) eq ⊢fst
      with inv->>= eq
    … | inv t′ eq₁ eq₂
      using B , _ , _ , _ , ⊢C , ⊢t , A≡ ← inversion-fst ⊢fst
          | t≡t′                         ← red-sound-⊢∷ n eq₁ ⊢t
      with is-prod? t′ | eq₂
    … | just (_ , _ , qC , t₁ , t₂ , eq₃) | eq₂ =
      let ⊢t₁ , ⊢t₂ , s≡𝕤 , p≡p′ , Σ-ok =
            inversion-prod-Σ $
            PE.subst (flip (_⊢_∷_ _) _) (PE.cong (flip ⌜_⌝ _) eq₃)
              (wf-⊢≡∷ t≡t′ .proj₂ .proj₂)

          open TmR
      in
                                      ∷ A   ⟨ A≡ ⟩≡∷
      ⌜ fst p t                   ⌝ γ ∷ B  ≡⟨ fst-cong′ t≡t′ ⟩⊢∷
      ⌜ fst p t′                  ⌝ γ      ≡⟨ PE.cong (U.fst _) $
                                              PE.trans (PE.cong (flip ⌜_⌝ _) eq₃) $
                                              PE.sym $ PE.cong₂ (λ s p → U.prod s p _ _) s≡𝕤 p≡p′ ⟩⊢≡
      ⌜ fst p (prod 𝕤 p qC t₁ t₂) ⌝ γ      ≡⟨ Σ-β₁-≡ ⊢C ⊢t₁ ⊢t₂ Σ-ok ⟩⊢
      ⌜ t₁ ⌝ γ                             ≡⟨ red-sound-⊢∷ n eq₂ ⊢t₁ ⟩⊢∎
      ⌜ u ⌝ γ                              ∎
    … | nothing | ok! =
      let open TmR in
                     ∷ A   ⟨ A≡ ⟩≡∷
      ⌜ fst p t  ⌝ γ ∷ B  ≡⟨ fst-cong′ t≡t′ ⟩⊢∷∎≡
      ⌜ fst p t′ ⌝ γ      ≡⟨⟩
      ⌜ u ⌝ γ             ∎
    red′-sound-⊢∷ {γ} {u} {A} n (snd p t) eq ⊢snd
      with inv->>= eq
    … | inv t′ eq₁ eq₂
      using _ , C , _ , _ , ⊢C , ⊢t , A≡ ← inversion-snd ⊢snd
          | t≡t′                         ← red-sound-⊢∷ n eq₁ ⊢t
      with is-prod? t′ | eq₂
    … | just (_ , _ , qC , t₁ , t₂ , eq₃) | eq₂ =
      let ⊢t₁ , ⊢t₂ , s≡𝕤 , p≡p′ , Σ-ok =
            inversion-prod-Σ $
            PE.subst (flip (_⊢_∷_ _) _) (PE.cong (flip ⌜_⌝ _) eq₃)
              (wf-⊢≡∷ t≡t′ .proj₂ .proj₂)
          ≡prod =
            PE.trans (PE.cong (flip ⌜_⌝ _) eq₃) $
            PE.sym $ PE.cong₂ (λ s p → U.prod s p _ _) s≡𝕤 p≡p′

          open TmR
      in
                                      ∷ A                         ⟨ A≡ ⟩≡∷
      ⌜ snd p t                   ⌝ γ ∷ C U.[ ⌜ fst p t  ⌝ γ ]₀  ≡⟨ snd-cong′ t≡t′ ⟩⊢∷
      ⌜ snd p t′                  ⌝ γ                            ≡⟨ PE.cong (U.snd _) ≡prod ⟩⊢≡
                                                                  ⟨ subst-⊢≡₀ ⊢C (fst-cong′ t≡t′) ⟩≡
                     ∷ C U.[ ⌜ fst p t′ ⌝ γ ]₀                    ⟨ PE.cong (C U.[_]₀ ∘→ U.fst _) ≡prod ⟩≡∷≡
                     ∷ C U.[ ⌜ fst p (prod 𝕤 p qC t₁ t₂) ⌝ γ ]₀   ⟨ subst-⊢≡₀ ⊢C (Σ-β₁-≡ ⊢C ⊢t₁ ⊢t₂ Σ-ok) ⟩≡∷
      ⌜ snd p (prod 𝕤 p qC t₁ t₂) ⌝ γ ∷ C U.[ ⌜ t₁ ⌝ γ ]₀        ≡⟨ Σ-β₂-≡ ⊢C ⊢t₁ ⊢t₂ Σ-ok ⟩⊢∷
      ⌜ t₂ ⌝ γ                                                   ≡⟨ red-sound-⊢∷ n eq₂ ⊢t₂ ⟩⊢∎
      ⌜ u ⌝ γ                                                    ∎
    … | nothing | ok! =
      let open TmR in
                     ∷ A                        ⟨ A≡ ⟩≡∷
      ⌜ snd p t  ⌝ γ ∷ C U.[ ⌜ fst p t ⌝ γ ]₀  ≡⟨ snd-cong′ t≡t′ ⟩⊢∷∎≡
      ⌜ snd p t′ ⌝ γ                           ≡⟨⟩
      ⌜ u ⌝ γ                                  ∎
    red′-sound-⊢∷ {γ} {u} {A} n (prodrec r p q D t₁ t₂) eq ⊢pr
      with inv->>= eq
    … | inv t₁′ eq₁ eq₂
      using _ , _ , _ , _ , _ ,
              ⊢D , ⊢t₁ , ⊢t₂ , A≡ ← inversion-prodrec ⊢pr
          | t₁≡t₁′                ← red-sound-⊢∷ n eq₁ ⊢t₁
      with is-prod? t₁′ | eq₂
    … | just (_ , _ , qC , t₁₁ , t₁₂ , eq₃) | eq₂ =
      let ⊢t₁₁ , ⊢t₁₂ , s≡𝕨 , p≡p′ , _ =
            inversion-prod-Σ $
            PE.subst (flip (_⊢_∷_ _) _) (PE.cong (flip ⌜_⌝ _) eq₃)
              (wf-⊢≡∷ t₁≡t₁′ .proj₂ .proj₂)
          ≡prod =
            PE.trans (PE.cong (flip ⌜_⌝ _) eq₃) $
            PE.sym $ PE.cong₂ (λ s p → U.prod s p _ _) s≡𝕨 p≡p′

          open TmR
      in
                                   ∷ A                          ⟨ A≡ ⟩≡∷
      ⌜ prodrec r p q D t₁ t₂ ⌝ γ  ∷ ⌜ D ⌝ γ U.[ ⌜ t₁  ⌝ γ ]₀  ≡⟨ prodrec-cong′ (refl ⊢D) t₁≡t₁′ (refl ⊢t₂) ⟩⊢∷
      ⌜ prodrec r p q D t₁′ t₂ ⌝ γ                             ≡⟨ PE.cong (flip (U.prodrec _ _ _ _) _) ≡prod ⟩⊢≡
                                                                ⟨ subst-⊢≡₀ ⊢D t₁≡t₁′ ⟩≡
                                   ∷ ⌜ D ⌝ γ U.[ ⌜ t₁′ ⌝ γ ]₀   ⟨ PE.cong (⌜ D ⌝ _ U.[_]₀) ≡prod ⟩≡∷≡
      ⌜ prodrec r p q D (prod 𝕨 p qC t₁₁ t₁₂) t₂ ⌝ γ ∷
        ⌜ D ⌝ γ U.[ ⌜ prod 𝕨 p qC t₁₁ t₁₂ ⌝ γ ]₀               ⇒⟨ prodrec-β-⇒ ⊢D ⊢t₁₁ ⊢t₁₂ ⊢t₂ ⟩⊢∷
      ⌜ subst t₂ (cons (sgSubst t₁₁) t₁₂) ⌝ γ                  ≡⟨ red-sound-⊢∷ n eq₂ $
                                                                  PE.subst (_⊢_∷_ _ _) ([1,0]↑²[,] (⌜ D ⌝ _)) $
                                                                  subst-⊢₁₀ ⊢t₂ ⊢t₁₁ ⊢t₁₂ ⟩⊢∎
      ⌜ u ⌝ γ                                                  ∎
    … | nothing | ok! =
      let open TmR in
                                   ∷ A                          ⟨ A≡ ⟩≡∷
      ⌜ prodrec r p q D t₁ t₂ ⌝ γ  ∷ ⌜ D ⌝ γ U.[ ⌜ t₁  ⌝ γ ]₀  ≡⟨ prodrec-cong′ (refl ⊢D) t₁≡t₁′ (refl ⊢t₂) ⟩⊢∷∎≡
      ⌜ prodrec r p q D t₁′ t₂ ⌝ γ                             ≡⟨⟩
      ⌜ u ⌝ γ                                                  ∎
    red′-sound-⊢∷ _ ℕ ok! ⊢ℕ =
      refl ⊢ℕ
    red′-sound-⊢∷ _ zero ok! ⊢zero =
      refl ⊢zero
    red′-sound-⊢∷ _ (suc _) ok! ⊢suc =
      refl ⊢suc
    red′-sound-⊢∷ {γ} {u} {A} n (natrec p q r B t₁ t₂ t₃) eq ⊢nr
      with inv->>= eq
    … | inv t₃′ eq₁ eq₂
      using ⊢B , ⊢t₁ , ⊢t₂ , ⊢t₃ , A≡ ← inversion-natrec ⊢nr
          | t₃≡t₃′                    ← red-sound-⊢∷ n eq₁ ⊢t₃
      with is-zero-or-suc? t₃′ | eq₂
    … | just (inj₁ eq₃) | eq₂ =
      let open TmR

          t₃≡0 =
            ⌜ t₃   ⌝ γ  ≡⟨ t₃≡t₃′ ⟩⊢∎≡
            ⌜ t₃′  ⌝ γ  ≡⟨ PE.cong (flip ⌜_⌝ _) eq₃ ⟩
            U.zero      ∎
      in
                                      ∷ A                         ⟨ A≡ ⟩≡∷
      ⌜ natrec p q r B t₁ t₂ t₃   ⌝ γ ∷ ⌜ B ⌝ γ U.[ ⌜ t₃ ⌝ γ ]₀  ≡⟨ natrec-cong (refl ⊢B) (refl ⊢t₁) (refl ⊢t₂) t₃≡0 ⟩⊢∷
                                                                  ⟨ subst-⊢≡₀ ⊢B t₃≡0 ⟩≡
      ⌜ natrec p q r B t₁ t₂ zero ⌝ γ ∷ ⌜ B ⌝ γ U.[ U.zero ]₀    ⇒⟨ natrec-zero ⊢t₁ ⊢t₂ ⟩⊢∷
      ⌜ t₁ ⌝ γ                                                   ≡⟨ red-sound-⊢∷ n eq₂ ⊢t₁ ⟩⊢∎
      ⌜ u ⌝ γ                                                    ∎
    … | just (inj₂ (t₃″ , eq₃)) | eq₂ =
      let open TmR

          t₃≡suc =
            ⌜ t₃      ⌝ γ  ≡⟨ t₃≡t₃′ ⟩⊢∎≡
            ⌜ t₃′     ⌝ γ  ≡⟨ PE.cong (flip ⌜_⌝ _) eq₃ ⟩
            ⌜ suc t₃″ ⌝ γ  ∎
          ⊢t₃″ , _ =
            inversion-suc (wf-⊢≡∷ t₃≡suc .proj₂ .proj₂)
      in
                                           ∷ A                         ⟨ A≡ ⟩≡∷
      ⌜ natrec p q r B t₁ t₂ t₃        ⌝ γ ∷ ⌜ B ⌝ γ U.[ ⌜ t₃ ⌝ γ ]₀  ≡⟨ natrec-cong (refl ⊢B) (refl ⊢t₁) (refl ⊢t₂) t₃≡suc ⟩⊢∷
                                                                       ⟨ subst-⊢≡₀ ⊢B t₃≡suc ⟩≡
      ⌜ natrec p q r B t₁ t₂ (suc t₃″) ⌝ γ ∷
        ⌜ B ⌝ γ U.[ ⌜ suc t₃″ ⌝ γ ]₀                                  ⇒⟨ natrec-suc ⊢t₁ ⊢t₂ ⊢t₃″ ⟩⊢∷
      ⌜ subst t₂ (cons (sgSubst t₃″) (natrec p q r B t₁ t₂ t₃″)) ⌝ γ  ≡⟨ red-sound-⊢∷ n eq₂ $
                                                                         PE.subst (_⊢_∷_ _ _) (PE.sym $ substComp↑² (⌜ B ⌝ _) _) $
                                                                         subst-⊢₁₀ ⊢t₂ ⊢t₃″ (natrecⱼ ⊢t₁ ⊢t₂ ⊢t₃″) ⟩⊢∎
      ⌜ u ⌝ γ                                                         ∎
    … | nothing | ok! =
      let open TmR in
                                     ∷ A                          ⟨ A≡ ⟩≡∷
      ⌜ natrec p q r B t₁ t₂ t₃  ⌝ γ ∷ ⌜ B ⌝ γ U.[ ⌜ t₃  ⌝ γ ]₀  ≡⟨ natrec-cong (refl ⊢B) (refl ⊢t₁) (refl ⊢t₂) t₃≡t₃′ ⟩⊢∷∎≡
      ⌜ natrec p q r B t₁ t₂ t₃′ ⌝ γ                             ≡⟨⟩
      ⌜ u ⌝ γ                                                    ∎
    red′-sound-⊢∷ _ (Id _ _ _) ok! ⊢Id =
      refl ⊢Id
    red′-sound-⊢∷ _ (rfl _) ok! ⊢rfl =
      refl ⊢rfl
    red′-sound-⊢∷ {γ} {u} {A} n (J p q B₁ t₁ B₂ t₂ t₃ t₄) eq ⊢J
      with inv->>= eq
    … | inv t₄′ eq₁ eq₂
      using ⊢B₁ , ⊢t₁ , ⊢B₂ , ⊢t₂ , ⊢t₃ , ⊢t₄ , A≡ ←
              inversion-J ⊢J
          | t₄≡t₄′ ←
              red-sound-⊢∷ n eq₁ ⊢t₄
      with is-rfl? t₄′ | eq₂
    … | just (t₁? , eq₃) | eq₂ =
      let open TmR

          t₄≡rfl =
            ⌜ t₄  ⌝ γ  ≡⟨ t₄≡t₄′ ⟩⊢∎≡
            ⌜ t₄′ ⌝ γ  ≡⟨ PE.cong (flip ⌜_⌝ _) eq₃ ⟩
            U.rfl      ∎

          t₁≡t₃ =
            inversion-rfl-Id (wf-⊢≡∷ t₄≡rfl .proj₂ .proj₂)
      in
                                    ∷ A        ⟨ A≡ ⟩≡∷
      ⌜ J p q B₁ t₁ B₂ t₂ t₃ t₄ ⌝ γ ∷
        ⌜ B₂ ⌝ γ U.[ ⌜ t₃ ⌝ γ , ⌜ t₄ ⌝ γ ]₁₀  ≡⟨ J-cong′ (refl ⊢B₁) (refl ⊢t₁) (refl ⊢B₂) (refl ⊢t₂) (refl ⊢t₃) t₄≡rfl ⟩⊢∷
                                               ⟨ subst-⊢≡₁₀ ⊢B₂ (sym′ t₁≡t₃) (PE.subst (_⊢_≡_∷_ _ _ _) ≡Id-wk1-wk1-0[]₀ t₄≡rfl) ⟩≡
      ⌜ J p q B₁ t₁ B₂ t₂ t₃ (rfl t₁?) ⌝ γ ∷
        ⌜ B₂ ⌝ γ U.[ ⌜ t₁ ⌝ γ , U.rfl ]₁₀     ⇒⟨ J-β-⇒ t₁≡t₃ ⊢B₂ ⊢t₂ ⟩⊢∷
      ⌜ t₂ ⌝ γ                                ≡⟨ red-sound-⊢∷ n eq₂ ⊢t₂ ⟩⊢∎
      ⌜ u ⌝ γ                                 ∎
    … | nothing | ok! =
      let open TmR in
                                    ∷ A        ⟨ A≡ ⟩≡∷
      ⌜ J p q B₁ t₁ B₂ t₂ t₃ t₄ ⌝ γ ∷
        ⌜ B₂ ⌝ γ U.[ ⌜ t₃ ⌝ γ , ⌜ t₄ ⌝ γ ]₁₀  ≡⟨ J-cong′ (refl ⊢B₁) (refl ⊢t₁) (refl ⊢B₂) (refl ⊢t₂) (refl ⊢t₃) t₄≡t₄′ ⟩⊢∷∎≡
      ⌜ J p q B₁ t₁ B₂ t₂ t₃ t₄′ ⌝ γ          ≡⟨⟩
      ⌜ u ⌝ γ                                 ∎
    red′-sound-⊢∷ {γ} {u} {A} n (K p B₁ t₁ B₂ t₂ t₃) eq ⊢K
      with inv->>= eq
    … | inv t₃′ eq₁ eq₂
      using ⊢B₁ , ⊢t₁ , ⊢B₂ , ⊢t₂ , ⊢t₃ , K-ok , A≡ ←
              inversion-K ⊢K
          | t₃≡t₃′ ←
              red-sound-⊢∷ n eq₁ ⊢t₃
      with is-rfl? t₃′ | eq₂
    … | just (t₁? , eq₃) | eq₂ =
      let open TmR

          t₃≡rfl =
            ⌜ t₃  ⌝ γ  ≡⟨ t₃≡t₃′ ⟩⊢∎≡
            ⌜ t₃′ ⌝ γ  ≡⟨ PE.cong (flip ⌜_⌝ _) eq₃ ⟩
            U.rfl      ∎
      in
                                      ∷ A                          ⟨ A≡ ⟩≡∷
      ⌜ K p B₁ t₁ B₂ t₂ t₃        ⌝ γ ∷ ⌜ B₂ ⌝ γ U.[ ⌜ t₃ ⌝ γ ]₀  ≡⟨ K-cong (refl ⊢B₁) (refl ⊢t₁) (refl ⊢B₂) (refl ⊢t₂) t₃≡rfl K-ok ⟩⊢∷
                                                                   ⟨ subst-⊢≡₀ ⊢B₂ t₃≡rfl ⟩≡
      ⌜ K p B₁ t₁ B₂ t₂ (rfl t₁?) ⌝ γ ∷ ⌜ B₂ ⌝ γ U.[ U.rfl ]₀     ⇒⟨ K-β ⊢B₂ ⊢t₂ K-ok ⟩⊢∷
      ⌜ t₂ ⌝ γ                                                    ≡⟨ red-sound-⊢∷ n eq₂ ⊢t₂ ⟩⊢∎
      ⌜ u ⌝ γ                                                     ∎
    … | nothing | ok! =
      let open TmR in
                                ∷ A                          ⟨ A≡ ⟩≡∷
      ⌜ K p B₁ t₁ B₂ t₂ t₃  ⌝ γ ∷ ⌜ B₂ ⌝ γ U.[ ⌜ t₃ ⌝ γ ]₀  ≡⟨ K-cong (refl ⊢B₁) (refl ⊢t₁) (refl ⊢B₂) (refl ⊢t₂) t₃≡t₃′ K-ok ⟩⊢∷∎≡
      ⌜ K p B₁ t₁ B₂ t₂ t₃′ ⌝ γ                             ≡⟨⟩
      ⌜ u ⌝ γ                                               ∎
    red′-sound-⊢∷ {γ} {u} {A} n ([]-cong s l B t₁ t₂ t₃) eq ⊢bc
      with inv->>= eq
    … | inv t₃′ eq₁ eq₂
      using ⊢l , ⊢B , ⊢t₁ , ⊢t₂ , ⊢t₃ , okᵇᶜ , A≡ ←
              inversion-[]-cong ⊢bc
          | t₃≡t₃′ ←
              red-sound-⊢∷ n eq₁ ⊢t₃
      with is-rfl? t₃′ | eq₂
    … | just (t₁? , eq₃) | ok! =
      let open TmR
          module E = Erased (⟦ s ⟧ˢ γ)

          t₃≡rfl =
            ⌜ t₃  ⌝ γ  ≡⟨ t₃≡t₃′ ⟩⊢∎≡
            ⌜ t₃′ ⌝ γ  ≡⟨ PE.cong (flip ⌜_⌝ _) eq₃ ⟩
            U.rfl      ∎

          t₁≡t₂ =
            inversion-rfl-Id (wf-⊢≡∷ t₃≡rfl .proj₂ .proj₂)
      in
                                   ∷ A        ⟨ A≡ ⟩≡∷
      ⌜ []-cong s l B t₁ t₂ t₃ ⌝ γ ∷
        U.Id (E.Erased (⌜ l ⌝ γ) (⌜ B ⌝ γ))
          E.[ ⌜ t₁ ⌝ γ ] E.[ ⌜ t₂ ⌝ γ ]      ≡⟨ []-cong-cong (refl-⊢≡∷L ⊢l) (refl ⊢B) (refl ⊢t₁) (refl ⊢t₂) t₃≡rfl okᵇᶜ ⟩⊢∷
      ⌜ []-cong s l B t₁ t₂ (rfl t₁?) ⌝ γ    ≡⟨ subsetTerm ([]-cong-β ⊢l t₁≡t₂ okᵇᶜ) ⟩⊢∎≡
      U.rfl                                  ≡⟨⟩
      ⌜ u ⌝ γ                                ∎
    … | nothing | ok! =
      let open TmR
          module E = Erased (⟦ s ⟧ˢ γ)
      in
                                   ∷ A        ⟨ A≡ ⟩≡∷
      ⌜ []-cong s l B t₁ t₂ t₃ ⌝ γ ∷
        U.Id (E.Erased (⌜ l ⌝ γ) (⌜ B ⌝ γ))
          E.[ ⌜ t₁ ⌝ γ ] E.[ ⌜ t₂ ⌝ γ ]      ≡⟨ []-cong-cong (refl-⊢≡∷L ⊢l) (refl ⊢B) (refl ⊢t₁) (refl ⊢t₂) t₃≡t₃′ okᵇᶜ ⟩⊢∷∎≡
      ⌜ []-cong s l B t₁ t₂ t₃′ ⌝ γ          ≡⟨⟩
      ⌜ u ⌝ γ                                ∎

opaque mutual

  -- Soundness for red for types.

  red-sound-⊢ :
    ⦃ ok : No-equality-reflection or-empty (⌜ Γ ⌝ᶜ γ) .vars ⦄ →
    ∀ n → OK (red n Γ A) B γ st →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A ⌝ γ ≡ ⌜ B ⌝ γ
  red-sound-⊢     0      not-ok
  red-sound-⊢ {A} (1+ n) eq     = red′-sound-⊢ n A (inv-register eq)

  private

    -- Soundness for red.

    red′-sound-⊢ :
      ⦃ ok : No-equality-reflection or-empty (⌜ Γ ⌝ᶜ γ) .vars ⦄ →
      ∀ n A → OK (red′ n Γ A) B γ st →
      ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A ⌝ γ →
      ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A ⌝ γ ≡ ⌜ B ⌝ γ
    red′-sound-⊢ _ (meta-var _ _) ok! ⊢x =
      refl ⊢x
    red′-sound-⊢ {γ} {B} n (weaken ρ A) eq ⊢wk-ρ-A =
      let open TyR
          eq′ = PE.sym (⌜wk⌝ A)
      in
      U.wk ρ (⌜ A ⌝ γ)  ≡⟨ eq′ ⟩⊢≡
      ⌜ wk ρ A ⌝ γ      ≡⟨ red-sound-⊢ n eq $
                           PE.subst (_⊢_ _) eq′ ⊢wk-ρ-A ⟩⊢∎
      ⌜ B ⌝ γ           ∎
    red′-sound-⊢ {γ} {B} n (subst A σ) eq ⊢A[σ] =
      let open TyR
          eq′ = PE.sym (⌜[]⌝ A (type₂ ⊢A[σ]))
      in
      ⌜ A ⌝ γ U.[ ⌜ σ ⌝ˢ γ ]  ≡⟨ eq′ ⟩⊢≡
      ⌜ A [ σ ] ⌝ γ           ≡⟨ red-sound-⊢ n eq $
                                 PE.subst (_⊢_ _) eq′ ⊢A[σ] ⟩⊢∎
      ⌜ B ⌝ γ                 ∎
    red′-sound-⊢ _ Level ok! ⊢Level =
      refl ⊢Level
    red′-sound-⊢ _ (_ supᵘₗ _) _ ⊢sup =
      let _ , _ , _ , U≡Level = inversion-supᵘₗ-⊢ ⊢sup in
      ⊥-elim (U≢Level U≡Level)
    red′-sound-⊢ _ (Lift _ _) ok! ⊢Lift =
      refl ⊢Lift
    red′-sound-⊢ _ (ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _) ok! ⊢ΠΣ =
      refl ⊢ΠΣ
    red′-sound-⊢ _ (Id _ _ _) ok! ⊢Id =
      refl ⊢Id
    red′-sound-⊢ n A eq (univ ⊢A) =
      univ (red′-sound-⊢∷ n A eq ⊢A)

private opaque

  -- Soundness for equal-sub″.

  equal-sub″-sound :
    ∀ {k} {Δ : Con c (k N.+ c .base-con-size)} (∇ : DCon c m) →
    OK (equal-sub″ k Δ) tt γ st →
    ⊢ ⌜ ∇ » Δ ⌝ᶜ γ →
    ⌜ ∇ » Δ ⌝ᶜ γ ⊢ˢʷ ⌜ wkSubst k id ⌝ˢ γ ∷ γ .⌜base⌝ .vars
  equal-sub″-sound {k = 0} _ eq ⊢base
    with inv->>= eq
  … | inv (_ , PE.refl) _ ok! =
    ⊢ˢʷ∷-idSubst ⊢base
  equal-sub″-sound {k = 1+ _} ∇ eq ⊢Γ
    with inv->>= eq
  … | inv (_ , _ , PE.refl) _ eq =
    let ⊢A = ⊢∙→⊢ ⊢Γ in
    ⊢ˢʷ∷-wk1Subst ⊢A (equal-sub″-sound ∇ eq (wf ⊢A))

opaque

  -- Soundness for really-remove-weaken-subst.

  really-remove-weaken-subst-sound :
    ∀ n →
    OK (really-remove-weaken-subst n t b₁) (u , b₂) γ st →
    Remove-weaken-subst-assumption b₂ γ t u →
    ⌜ t ⌝ γ PE.≡ ⌜ u ⌝ γ
  really-remove-weaken-subst-sound             0      not-ok
  really-remove-weaken-subst-sound {t} {u} {γ} (1+ n) eq     ass
    with inv->>= eq
  … | inv (t′ , _) eq₁ eq₂
    using t≡t′ ← remove-weaken-subst-sound {γ′ = γ} eq₁
    with is-weaken-subst? t′ | eq₂
  … | no _ | ok! =
    t≡t′ ass
  … | yes ws | eq₂ =
    let t≡t′ = t≡t′ (not-supᵘₗ (Is-weaken-subst→Not-supᵘₗ ws)) in
    ⌜ t ⌝ γ   ≡⟨ t≡t′ ⟩
    ⌜ t′ ⌝ γ  ≡⟨ really-remove-weaken-subst-sound n eq₂ $
                 cast-Remove-weaken-subst-assumption t≡t′ ass ⟩
    ⌜ u ⌝ γ  ∎

-- A type used to state is-term-sound and
-- are-equal-meta-vars-sound-tm.

data Is-term (A : Term c n) (γ : Contexts c) (Γ : Cons c m n)
       (x : Meta-var c tm n) : Set a where
  term : ∀ {t} → γ .metas .bindings x PE.≡ (Γ .vars , term t A) →
         Is-term A γ Γ x

opaque

  -- Soundness for is-term.

  is-term-sound :
    {x : Meta-var c tm n} →
    OK (is-term x) (Δ , A) γ st →
    Contexts-wf ∇ γ →
    Is-term A γ (∇ » Δ) x ×
    ⌜ ∇ ⌝ᶜᵈ γ » ⌜ Δ ⌝ᶜᵛ γ ⊢ ⌜ x ⌝ᵐ γ ∷ ⌜ A ⌝ γ
  is-term-sound {γ} {x} eq ⊢γ
    with inv->>= eq
  … | inv _ ok! eq
    with γ .metas .bindings x in γx≡ | ⊢γ .metas-wf .bindings-wf x | eq
  … | _ , type _   | _  | not-ok
  … | _ , term _ _ | ⊢t | ok!    = term γx≡ , ⊢t

opaque

  -- Soundness for are-equal-meta-vars for terms.

  are-equal-meta-vars-sound-tm :
    OK (are-equal-meta-vars x₁ x₂) tt γ st →
    Contexts-wf (Γ .defs) γ →
    Is-term A γ Γ x₂ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ x₂ ⌝ᵐ γ ∷ ⌜ A ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ x₁ ⌝ᵐ γ ≡ ⌜ x₂ ⌝ᵐ γ ∷ ⌜ A ⌝ γ
  are-equal-meta-vars-sound-tm eq _ _ _
    with inv->>= eq
  … | inv _ ok! eq
    with inv->>= eq
  are-equal-meta-vars-sound-tm _ _ _ ⊢x₂
    | _ | inv (inj₁ PE.refl) _ _ =
    refl ⊢x₂
  are-equal-meta-vars-sound-tm {x₁} {x₂} {γ} _ ⊢γ (term _) _
    | _ | inv (inj₂ (inj₁ ∈eqs)) _ _
    with γ .metas .bindings x₁ | γ .metas .bindings x₂
       | List.lookup (⊢γ .metas-wf .equalities-wf) ∈eqs
  are-equal-meta-vars-sound-tm _ _ (term ()) _
    | _ | _ | _ | _ | _ , type _
  are-equal-meta-vars-sound-tm _ _ (term PE.refl) _
    | _ | _ | _ | _ | Δ₁≡Δ₂ , term A₁≡A t₁≡t₂ =
    stability Δ₁≡Δ₂ (conv t₁≡t₂ A₁≡A)
  are-equal-meta-vars-sound-tm {x₁} {x₂} {γ} _ ⊢γ (term _) _
    | _ | inv (inj₂ (inj₂ ∈eqs)) _ _
    with γ .metas .bindings x₁ | γ .metas .bindings x₂
       | List.lookup (⊢γ .metas-wf .equalities-wf) ∈eqs
  are-equal-meta-vars-sound-tm _ _ (term ()) _
    | _ | _ | _ | _ | _ , type _
  are-equal-meta-vars-sound-tm _ _ (term PE.refl) _
    | _ | _ | _ | _ | _ , term _ t₁≡t₂ =
    sym′ t₁≡t₂

-- A type used to state are-equal-meta-vars-sound-level and
-- is-level-sound.

data Is-level
       (σ : Subst c n₂ n₁) (γ : Contexts c) (Γ : Cons c m n₂)
       (Δ : Con c n₁) : Meta-var c k n₁ → Set a where
  level : ∀ {l} → γ .metas .bindings x PE.≡ (Δ , level l) →
          Is-level σ γ Γ Δ x
  term  : ∀ {t A} → γ .metas .bindings x PE.≡ (Δ , term t A) →
          ⌜ Γ .defs » Δ ⌝ᶜ γ ⊢ ⌜ A ⌝ γ →
          ⌜ Γ ⌝ᶜ γ ⊢ ⌜ subst A σ ⌝ γ ≡ U.Level →
          Is-level σ γ Γ Δ x

opaque

  -- Soundness for are-equal-meta-vars for levels.

  are-equal-meta-vars-sound-level :
    ∀ σ₁ →
    OK (are-equal-meta-vars x₁ x₂) tt γ st →
    Contexts-wf (Γ .defs) γ →
    Is-level σ₂ γ Γ Δ x₂ →
    ⌜ Γ ⌝ᶜ γ ⊢ˢʷ ⌜ σ₁ ⌝ˢ γ ≡ ⌜ σ₂ ⌝ˢ γ ∷ ⌜ Δ ⌝ᶜᵛ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ meta-var x₁ σ₁ ⌝ γ ≡ ⌜ meta-var x₂ σ₂ ⌝ γ ∷Level
  are-equal-meta-vars-sound-level {x₁} {x₂} {γ} {σ₂} σ₁ eq _ _ _
    rewrite ⌜meta-var⌝ {γ = γ} {x = x₁} σ₁
          | ⌜meta-var⌝ {γ = γ} {x = x₂} σ₂
    with inv->>= eq
  … | inv _ ok! eq
    with inv->>= eq
  are-equal-meta-vars-sound-level {x₂} {γ} _ _ ⊢γ (level _) _
    | _ | inv (inj₁ PE.refl) _ _
    with γ .metas .bindings x₂ | ⊢γ .metas-wf .bindings-wf x₂
  are-equal-meta-vars-sound-level _ _ _ (level PE.refl) σ₁≡σ₂
    | _ | _ | _ , level _ | ⊢l =
    subst-⊢≡∷L (refl-⊢≡∷L ⊢l) σ₁≡σ₂
  are-equal-meta-vars-sound-level {x₁} {x₂} {γ} _ _ ⊢γ (level _) _
    | _ | inv (inj₂ (inj₁ ∈eqs)) _ _
    with γ .metas .bindings x₁ | γ .metas .bindings x₂
       | List.lookup (⊢γ .metas-wf .equalities-wf) ∈eqs
  are-equal-meta-vars-sound-level _ _ _ (level PE.refl) σ₁≡σ₂
    | _ | _ | _ | _ | Η₁≡Η₂ , level l₁≡l₂ =
    subst-⊢≡∷L (stability Η₁≡Η₂ l₁≡l₂) σ₁≡σ₂
  are-equal-meta-vars-sound-level {x₁} {x₂} {γ} _ _ ⊢γ (level _) _
    | _ | inv (inj₂ (inj₂ ∈eqs)) _ _
    with γ .metas .bindings x₁ | γ .metas .bindings x₂
       | List.lookup (⊢γ .metas-wf .equalities-wf) ∈eqs
  are-equal-meta-vars-sound-level _ _ _ (level PE.refl) σ₁≡σ₂
    | _ | _ | _ | _ | _ , level l₁≡l₂ =
    subst-⊢≡∷L (sym-⊢≡∷L l₁≡l₂) σ₁≡σ₂

-- A type used to state are-equal-meta-vars-sound-ty and
-- is-type-sound.

data Is-type (γ : Contexts c) (Γ : Cons c m n) (x : Meta-var c tm n) :
       Set a where
  type : ∀ {A} → γ .metas .bindings x PE.≡ (Γ .vars , type A) →
         Is-type γ Γ x
  term : ∀ {t l} → γ .metas .bindings x PE.≡ (Γ .vars , term t A) →
         ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A ⌝ γ ≡ U.U l →
         Is-type γ Γ x

opaque

  -- Soundness for are-equal-meta-vars for types.

  are-equal-meta-vars-sound-ty :
    OK (are-equal-meta-vars x₁ x₂) tt γ st →
    Contexts-wf (Γ .defs) γ →
    Is-type γ Γ x₂ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ x₂ ⌝ᵐ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ x₁ ⌝ᵐ γ ≡ ⌜ x₂ ⌝ᵐ γ
  are-equal-meta-vars-sound-ty eq _ _ _
    with inv->>= eq
  … | inv _ ok! eq
    with inv->>= eq
  are-equal-meta-vars-sound-ty _ _ _ ⊢x₂
    | _ | inv (inj₁ PE.refl) _ _ =
    refl ⊢x₂
  are-equal-meta-vars-sound-ty {x₁} {x₂} {γ} _ ⊢γ (type _) _
    | _ | inv (inj₂ (inj₁ ∈eqs)) _ _
    with γ .metas .bindings x₁ | γ .metas .bindings x₂
       | List.lookup (⊢γ .metas-wf .equalities-wf) ∈eqs
  are-equal-meta-vars-sound-ty _ _ (type PE.refl) _
    | _ | _ | _ | _ | Δ₁≡Δ₂ , type A₁≡A₂ =
    stability Δ₁≡Δ₂ A₁≡A₂
  are-equal-meta-vars-sound-ty _ _ (type ()) _
    | _ | _ | _ | _ | _ , term _ _
  are-equal-meta-vars-sound-ty {x₁} {x₂} {γ} _ ⊢γ (term _ _) _
    | _ | inv (inj₂ (inj₁ ∈eqs)) _ _
    with γ .metas .bindings x₁ | γ .metas .bindings x₂
       | List.lookup (⊢γ .metas-wf .equalities-wf) ∈eqs
  are-equal-meta-vars-sound-ty _ _ (term () _) _
    | _ | _ | _ | _ | _ , type _
  are-equal-meta-vars-sound-ty _ _ (term PE.refl A₂≡U) _
    | _ | _ | _ | _ | Δ₁≡Δ₂ , term A₁≡A₂ t₁≡t₂ =
    univ (conv (stability Δ₁≡Δ₂ (conv t₁≡t₂ A₁≡A₂)) A₂≡U)
  are-equal-meta-vars-sound-ty {x₁} {x₂} {γ} _ ⊢γ (type _) _
    | _ | inv (inj₂ (inj₂ ∈eqs)) _ _
    with γ .metas .bindings x₁ | γ .metas .bindings x₂
       | List.lookup (⊢γ .metas-wf .equalities-wf) ∈eqs
  are-equal-meta-vars-sound-ty _ _ (type PE.refl) _
    | _ | _ | _ | _ | _ , type A₁≡A₂ =
    sym A₁≡A₂
  are-equal-meta-vars-sound-ty _ _ (type ()) _
    | _ | _ | _ | _ | _ , term _ _
  are-equal-meta-vars-sound-ty {x₁} {x₂} {γ} _ ⊢γ (term _ _) _
    | _ | inv (inj₂ (inj₂ ∈eqs)) _ _
    with γ .metas .bindings x₁ | γ .metas .bindings x₂
       | List.lookup (⊢γ .metas-wf .equalities-wf) ∈eqs
  are-equal-meta-vars-sound-ty _ _ (term () _) _
    | _ | _ | _ | _ | _ , type _
  are-equal-meta-vars-sound-ty _ _ (term PE.refl A₁≡U) _
    | _ | _ | _ | _ | _ , term _ t₁≡t₂ =
    sym (univ (conv t₁≡t₂ A₁≡U))

private

  -- The code used to contain a mutual block that was 2422 lines long.
  -- The option --no-occurrence-analysis was used to speed things up,
  -- but the termination checker still took quite some time to check
  -- that block.
  --
  -- Now the code uses a different structure: Some properties are
  -- proved by induction on the structure of fuel. Those properties
  -- are collected in the record type P n, where n is an amount of
  -- fuel. Other properties are proved first, under the assumption
  -- that the properties in P n hold for some n. Then the properties
  -- in P (1+ n) are proved under the assumption that the properties
  -- in P n hold, and finally the properties in P 0 are proved and the
  -- recursive knot is tied.

  record P (n : Fuel) : Set (L.lsuc a) where
    no-eta-equality
    field
      -- Soundness for red-ty.

      red-ty-sound :
        OK (red-ty n Γ A) B γ st →
        Contexts-wf (Γ .defs) γ →
        ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A ⌝ γ →
        ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A ⌝ γ ≡ ⌜ B ⌝ γ

      -- Soundness for red-tm.
      --
      -- It is not proved that the resulting term is a WHNF, or that
      -- the initial term reduces to the resulting term (only that the
      -- two terms are judgementally equal), see
      -- successful-reduction-without-reduction-sequence.

      red-tm-sound :
        OK (red-tm n Γ t A) u γ st →
        Contexts-wf (Γ .defs) γ →
        ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ∷ ⌜ A ⌝ γ →
        ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ≡ ⌜ u ⌝ γ ∷ ⌜ A ⌝ γ

      -- Soundness for check-type.

      check-type-sound :
        OK (check-type n Γ A) A′ γ st →
        Contexts-wf (Γ .defs) γ →
        ⊢ ⌜ Γ ⌝ᶜ γ →
        ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A ⌝ γ ≡ ⌜ A′ ⌝ γ

      -- Soundness for check-level.

      check-level-sound :
        OK (check-level n Γ l) l′ γ st →
        Contexts-wf (Γ .defs) γ →
        ⊢ ⌜ Γ ⌝ᶜ γ →
        ⌜ Γ ⌝ᶜ γ ⊢ ⌜ Term[]→Lvl l ⌝ γ ≡ ⌜ Term[]→Lvl l′ ⌝ γ ∷Level

      -- Soundness for check.

      check-sound :
        OK (check n Γ t A) t′ γ st →
        Contexts-wf (Γ .defs) γ →
        ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A ⌝ γ →
        ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ≡ ⌜ t′ ⌝ γ ∷ ⌜ A ⌝ γ

      -- Soundness for infer.

      infer-sound :
        OK (infer n Γ t) A γ st →
        Contexts-wf (Γ .defs) γ →
        ⊢ ⌜ Γ ⌝ᶜ γ →
        ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ∷ ⌜ A ⌝ γ

      -- Soundness for equal-ty.

      equal-ty-sound :
        OK (equal-ty n Γ A₁ A₂) tt γ st →
        Contexts-wf (Γ .defs) γ →
        ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A₁ ⌝ γ →
        ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A₂ ⌝ γ →
        ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A₁ ⌝ γ ≡ ⌜ A₂ ⌝ γ

      -- Soundness for equal-tm.

      equal-tm-sound :
        OK (equal-tm n Γ t₁ t₂ A) tt γ st →
        Contexts-wf (Γ .defs) γ →
        ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ∷ ⌜ A ⌝ γ →
        ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ →
        ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ≡ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ

      -- Soundness for normalise-level.

      normalise-level-sound :
        OK (normalise-level b n Γ l) nf γ st →
        Contexts-wf (Γ .defs) γ →
        ⌜ Γ ⌝ᶜ γ ⊢ ⌜ Term[]→Lvl l ⌝ γ ∷Level →
        ⌜ Γ ⌝ᶜ γ ⊢⌜ nf ⌝ⁿ γ ∷Level ×
        ⌜ Γ ⌝ᶜ γ ⊢ ⌜ Term[]→Lvl l ⌝ γ ≡ ⌜ nf ⌝ⁿ γ ∷Level

      -- Soundness for equal-ne-inf.

      equal-ne-inf-sound :
        OK (equal-ne-inf n Γ t₁ t₂) A γ st →
        Contexts-wf (Γ .defs) γ →
        ⊢ ⌜ Γ ⌝ᶜ γ →
        ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ≡ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ

-- Some lemmas that hold if P n is inhabited.

private module Lemmas (p : P n) where opaque

  open P p

  mutual

    -- Soundness for equal-con.

    equal-con-sound :
      OK (equal-con n Γ Δ) tt γ st →
      Contexts-wf (Γ .defs) γ →
      ⊢ ⌜ Γ ⌝ᶜ γ →
      ⌜ Γ ⌝ᶜ γ .defs »⊢ ⌜ Δ ⌝ᶜᵛ γ →
      ⌜ Γ ⌝ᶜ γ .defs »⊢ ⌜ Γ ⌝ᶜ γ .vars ≡ ⌜ Δ ⌝ᶜᵛ γ
    equal-con-sound eq ⊢γ ⊢Γ ⊢Δ =
      let inv Γ∼Δ _ eq = inv->>= eq in
      equal-con′-sound Γ∼Δ eq ⊢γ ⊢Γ ⊢Δ

    private

      -- Soundness for equal-con′.

      equal-con′-sound :
        (Δ₁∼Δ₂ : Equal-con-constructors⁼ Δ₁ Δ₂) →
        OK (equal-con′ n ∇ Δ₁∼Δ₂) tt γ st →
        Contexts-wf ∇ γ →
        ⌜ ∇ ⌝ᶜᵈ γ »⊢ ⌜ Δ₁ ⌝ᶜᵛ γ →
        ⌜ ∇ ⌝ᶜᵈ γ »⊢ ⌜ Δ₂ ⌝ᶜᵛ γ →
        ⌜ ∇ ⌝ᶜᵈ γ »⊢ ⌜ Δ₁ ⌝ᶜᵛ γ ≡ ⌜ Δ₂ ⌝ᶜᵛ γ
      equal-con′-sound (base PE.refl) ok! _ ⊢base _ =
        reflConEq ⊢base
      equal-con′-sound ε ok! _ ⊢ε _ =
        reflConEq ⊢ε
      equal-con′-sound (ext _ _ _ _) eq ⊢γ (∙ ⊢A₁) (∙ ⊢A₂) =
        let inv _ eq₁ eq₂ = inv->>= eq
            Δ₁≡Δ₂         = equal-con-sound eq₁ ⊢γ (wf ⊢A₁) (wf ⊢A₂)
        in
        Δ₁≡Δ₂ ∙
        equal-ty-sound eq₂ ⊢γ ⊢A₁ (stability (symConEq Δ₁≡Δ₂) ⊢A₂)

  -- Soundness for check-sub.

  check-sub-sound :
    ∀ σ →
    OK (check-sub n ∇ Δ₂ σ Δ₁) σ′ γ st →
    Contexts-wf ∇ γ →
    ⌜ ∇ ⌝ᶜᵈ γ »⊢ ⌜ Δ₂ ⌝ᶜᵛ γ →
    ⌜ ∇ ⌝ᶜᵈ γ »⊢ ⌜ Δ₁ ⌝ᶜᵛ γ →
    ⌜ ∇ ⌝ᶜᵈ γ » ⌜ Δ₂ ⌝ᶜᵛ γ ⊢ˢʷ ⌜ σ ⌝ˢ γ ≡ ⌜ σ′ ⌝ˢ γ ∷ ⌜ Δ₁ ⌝ᶜᵛ γ
  check-sub-sound σ eq = check-sub′-sound σ (inv-register eq)
    where
    check-sub′-sound :
      ∀ σ →
      OK (check-sub′ n ∇ Δ₂ σ Δ₁) σ′ γ st →
      Contexts-wf ∇ γ →
      ⌜ ∇ ⌝ᶜᵈ γ »⊢ ⌜ Δ₂ ⌝ᶜᵛ γ →
      ⌜ ∇ ⌝ᶜᵈ γ »⊢ ⌜ Δ₁ ⌝ᶜᵛ γ →
      ⌜ ∇ ⌝ᶜᵈ γ » ⌜ Δ₂ ⌝ᶜᵛ γ ⊢ˢʷ ⌜ σ ⌝ˢ γ ≡ ⌜ σ′ ⌝ˢ γ ∷ ⌜ Δ₁ ⌝ᶜᵛ γ
    check-sub′-sound id eq ⊢γ ⊢Δ₂ ⊢Δ₁
      with inv->>= eq
    … | inv _ eq₁ ok! =
      let Γ≡Δ = equal-con-sound eq₁ ⊢γ ⊢Δ₂ ⊢Δ₁ in
      refl-⊢ˢʷ≡∷ (stability-⊢ˢʷ∷ʳ Γ≡Δ (⊢ˢʷ∷-idSubst ⊢Δ₂))
    check-sub′-sound (wk1 σ) eq ⊢γ ⊢Δ₂ ⊢Δ₁
      with inv->>= eq
    … | inv (_ , _ , PE.refl) _ eq
      with inv->>= eq
    … | inv _ eq₁ ok! =
      let ⊢A   = ⊢∙→⊢ ⊢Δ₂
          σ≡σ′ = check-sub-sound σ eq₁ ⊢γ (wf ⊢A) ⊢Δ₁
      in
      ⊢ˢʷ≡∷-wk1Subst ⊢A σ≡σ′
    check-sub′-sound (σ ⇑) eq ⊢γ ⊢Δ₂ ⊢Δ₁
      with inv->>= eq
    … | inv (_ , _ , PE.refl) _ eq
      with inv->>= eq
    … | inv (_ , _ , PE.refl) _ eq
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv _ eq₂ ok! =
      let ⊢A          = ⊢∙→⊢ ⊢Δ₂
          ⊢B          = ⊢∙→⊢ ⊢Δ₁
          σ≡σ′        = check-sub-sound σ eq₁ ⊢γ (wf ⊢A) (wf ⊢B)
          _ , _ , ⊢σ′ = wf-⊢ˢʷ≡∷ σ≡σ′
          A≡B[σ′]     = equal-ty-sound eq₂ ⊢γ ⊢A (subst-⊢ ⊢B ⊢σ′)
      in
      stability-⊢ˢʷ≡∷ˡ (refl-∙ (sym A≡B[σ′])) $
      sym-⊢ˢʷ≡∷ ⊢Δ₁ (⊢ˢʷ≡∷-⇑′ ⊢B (sym-⊢ˢʷ≡∷ (wf ⊢B) σ≡σ′))
    check-sub′-sound (cons σ _) eq ⊢γ ⊢Δ₂ ⊢Δ₁
      with inv->>= eq
    … | inv (_ , _ , PE.refl) _ eq
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv _ eq₂ ok! =
      let ⊢B          = ⊢∙→⊢ ⊢Δ₁
          σ≡σ′        = check-sub-sound σ eq₁ ⊢γ ⊢Δ₂ (wf ⊢B)
          _ , _ , ⊢σ′ = wf-⊢ˢʷ≡∷ σ≡σ′
          t≡t′        = check-sound eq₂ ⊢γ (subst-⊢ ⊢B ⊢σ′)
      in
      sym-⊢ˢʷ≡∷ ⊢Δ₁ (→⊢ˢʷ≡∷∙ ⊢B (sym-⊢ˢʷ≡∷ (wf ⊢B) σ≡σ′) (sym′ t≡t′))

  -- Soundness for is-type.

  is-type-sound :
    OK (is-type n ∇ x) Δ γ st →
    Contexts-wf ∇ γ →
    Is-type γ (∇ » Δ) x ×
    ⌜ ∇ ⌝ᶜᵈ γ » ⌜ Δ ⌝ᶜᵛ γ ⊢ ⌜ x ⌝ᵐ γ
  is-type-sound {x} {γ} eq ⊢γ
    with inv->>= eq
  … | inv _ ok! eq
    with γ .metas .bindings x in γx≡ | ⊢γ .metas-wf .bindings-wf x | eq
  … | _ , type _   | ⊢A | ok!    = type γx≡ , ⊢A
  … | _ , term _ _ | ⊢t | eq
    with inv->>= eq
  … | inv _ eq₁ eq
    with inv->>= eq
  … | inv (_ , PE.refl) eq₂ ok! =
    let A≡U = red-ty-sound eq₁ ⊢γ (wf-⊢∷ ⊢t) in
    term γx≡ A≡U , univ (conv ⊢t A≡U)

  -- Soundness for is-level.

  is-level-sound :
    OK (is-level n Γ x σ) (Δ , l′) γ st →
    Contexts-wf (Γ .defs) γ →
    ⊢ ⌜ Γ ⌝ᶜ γ →
    Is-level σ γ Γ Δ x ×
    ⌜ Γ .defs ⌝ᶜᵈ γ »⊢ ⌜ Δ ⌝ᶜᵛ γ ×
    ⌜ Γ ⌝ᶜ γ ⊢ˢʷ ⌜ σ ⌝ˢ γ ∷ ⌜ Δ ⌝ᶜᵛ γ ×
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ Term[]→Lvl (meta-var x σ) ⌝ γ ≡ ⌜ Term[]→Lvl l′ ⌝ γ
      ∷Level
  is-level-sound {x} {γ} eq ⊢γ _
    with inv->>= eq
  … | inv _ ok! eq
    with γ .metas .bindings x in γx≡ | ⊢γ .metas-wf .bindings-wf x
  is-level-sound             _ _  _  | inv _ _ not-ok | _ , type _  | _
  is-level-sound {x} {σ} {γ} _ ⊢γ ⊢Γ | inv _ _ eq     | _ , level _ | ⊢l
    with inv->>= eq
  … | inv σ′ eq₁ ok!
    rewrite ⌜meta-var⌝ {γ = γ} {x = x} σ
          | ⌜meta-var⌝ {γ = γ} {x = x} σ′
          | γx≡ =
    let σ≡σ′       = check-sub-sound σ eq₁ ⊢γ ⊢Γ (wf ⊢l)
        _ , ⊢σ , _ = wf-⊢ˢʷ≡∷ σ≡σ′
    in
    level γx≡ ,
    wf ⊢l ,
    ⊢σ ,
    subst-⊢≡∷L (refl-⊢≡∷L ⊢l) σ≡σ′
  is-level-sound {x} {σ} {γ} _ ⊢γ ⊢Γ | inv _ _ eq | _ , term _ A | ⊢t
    with inv->>= eq
  … | inv σ′ eq₁ eq
    with inv->>= eq
  … | inv _ eq₂ eq
    with inv->>= eq
  … | inv PE.refl _ ok!
    rewrite ⌜meta-var⌝ {γ = γ} {x = x} σ
          | ⌜meta-var⌝ {γ = γ} {x = x} σ′
          | γx≡ =
    let open TyR

        σ≡σ′         = check-sub-sound σ eq₁ ⊢γ ⊢Γ (wf ⊢t)
        _ , ⊢σ , ⊢σ′ = wf-⊢ˢʷ≡∷ σ≡σ′
        ⊢A           = wf-⊢∷ ⊢t
        ⊢A[σ′]       = subst-⊢ ⊢A ⊢σ′
        ≡A[σ′]       = PE.sym (⌜[]⌝ A (type₂ ⊢A[σ′]))
        A[σ]≡Level   =
          ⌜ A ⌝ γ U.[ ⌜ σ ⌝ˢ γ ]   ≡⟨ subst-⊢≡ (refl ⊢A) σ≡σ′ ⟩⊢
          ⌜ A ⌝ γ U.[ ⌜ σ′ ⌝ˢ γ ]  ≡⟨ ≡A[σ′] ⟩⊢≡
          ⌜ A [ σ′ ] ⌝ γ           ≡⟨ red-ty-sound eq₂ ⊢γ $
                                      PE.subst (_⊢_ _) ≡A[σ′] ⊢A[σ′] ⟩⊢∎
          U.Level                  ∎
    in
    term γx≡ ⊢A A[σ]≡Level ,
    wf ⊢t ,
    ⊢σ ,
    term-⊢≡∷ (conv (subst-⊢≡∷ (refl ⊢t) σ≡σ′) A[σ]≡Level)

  -- Soundness for check-and-equal-ty.

  check-and-equal-ty-sound :
    OK (check-and-equal-ty n Γ A₁ A₂) A γ st →
    Contexts-wf (Γ .defs) γ →
    ⊢ ⌜ Γ ⌝ᶜ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A₁ ⌝ γ ≡ ⌜ A ⌝ γ ×
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A₁ ⌝ γ ≡ ⌜ A₂ ⌝ γ
  check-and-equal-ty-sound {A₁} {A₂} {γ} eq ⊢γ ⊢Γ
    with inv->>= eq
  … | inv A₁′ eq₁ eq
    with inv->>= eq
  … | inv A₂′ eq₂ eq
    with inv->>= eq
  … | inv _ eq₃ ok! =
    let A₁≡A₁′   = check-type-sound eq₁ ⊢γ ⊢Γ
        _ , ⊢A₁′ = wf-⊢≡ A₁≡A₁′
        A₂≡A₂′   = check-type-sound eq₂ ⊢γ ⊢Γ
        _ , ⊢A₂′ = wf-⊢≡ A₂≡A₂′
        A₁′≡A₂′  = equal-ty-sound eq₃ ⊢γ ⊢A₁′ ⊢A₂′
    in
    A₁≡A₁′ ,
    (⌜ A₁ ⌝ γ   ≡⟨ A₁≡A₁′ ⟩⊢
     ⌜ A₁′ ⌝ γ  ≡⟨ A₁′≡A₂′ ⟩⊢
     ⌜ A₂′ ⌝ γ  ≡˘⟨ A₂≡A₂′ ⟩⊢∎
     ⌜ A₂ ⌝ γ   ∎)
    where
    open TyR

  -- Soundness for check-and-equal-tm.

  check-and-equal-tm-sound :
    OK (check-and-equal-tm n Γ t₁ t₂ A) t γ st →
    Contexts-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ≡ ⌜ t ⌝ γ ∷ ⌜ A ⌝ γ ×
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ≡ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ
  check-and-equal-tm-sound {t₁} {t₂} {γ} eq ⊢γ ⊢Γ
    with inv->>= eq
  … | inv t₁′ eq₁ eq
    with inv->>= eq
  … | inv t₂′ eq₂ eq
    with inv->>= eq
  … | inv _ eq₃ ok! =
    let t₁≡t₁′       = check-sound eq₁ ⊢γ ⊢Γ
        _ , _ , ⊢t₁′ = wf-⊢≡∷ t₁≡t₁′
        t₂≡t₂′       = check-sound eq₂ ⊢γ ⊢Γ
        _ , _ , ⊢t₂′ = wf-⊢≡∷ t₂≡t₂′
        t₁′≡t₂′      = equal-tm-sound eq₃ ⊢γ ⊢t₁′ ⊢t₂′
    in
    t₁≡t₁′ ,
    (⌜ t₁ ⌝ γ   ≡⟨ t₁≡t₁′ ⟩⊢
     ⌜ t₁′ ⌝ γ  ≡⟨ t₁′≡t₂′ ⟩⊢
     ⌜ t₂′ ⌝ γ  ≡˘⟨ t₂≡t₂′ ⟩⊢∎
     ⌜ t₂ ⌝ γ   ∎)
    where
    open TmR

  mutual

    -- Soundness for equal-sub′.

    equal-sub′-sound :
      OK (equal-sub′ n b (∇ » Δ) σ₁ Η₁ σ₂ Η₂) PE.refl γ st →
      Contexts-wf ∇ γ →
      (T b → ⌜ ∇ ⌝ᶜᵈ γ » ⌜ Δ ⌝ᶜᵛ γ ⊢ˢʷ ⌜ σ₂ ⌝ˢ γ ∷ ⌜ Η₂ ⌝ᶜᵛ γ) →
      ⌜ ∇ ⌝ᶜᵈ γ »⊢ ⌜ Δ ⌝ᶜᵛ γ →
      ⌜ ∇ ⌝ᶜᵈ γ »⊢ ⌜ Η₂ ⌝ᶜᵛ γ →
      ⌜ ∇ ⌝ᶜᵈ γ » ⌜ Δ ⌝ᶜᵛ γ ⊢ˢʷ ⌜ σ₁ ⌝ˢ γ ≡ ⌜ σ₂ ⌝ˢ γ ∷ ⌜ Η₂ ⌝ᶜᵛ γ
    equal-sub′-sound eq = equal-sub′-sound′ PE.refl eq

    private

      -- Soundness for equal-sub′.

      equal-sub′-sound′ :
        (n₁≡n₂ : n₁ PE.≡ n₂) →
        OK (equal-sub′ n b (∇ » Δ) σ₁ Η₁ σ₂ Η₂) n₁≡n₂ γ st →
        Contexts-wf ∇ γ →
        (T b → ⌜ ∇ ⌝ᶜᵈ γ » ⌜ Δ ⌝ᶜᵛ γ ⊢ˢʷ ⌜ σ₂ ⌝ˢ γ ∷ ⌜ Η₂ ⌝ᶜᵛ γ) →
        ⌜ ∇ ⌝ᶜᵈ γ »⊢ ⌜ Δ ⌝ᶜᵛ γ →
        ⌜ ∇ ⌝ᶜᵈ γ »⊢ ⌜ Η₂ ⌝ᶜᵛ γ →
        ⌜ ∇ ⌝ᶜᵈ γ » ⌜ Δ ⌝ᶜᵛ γ ⊢ˢʷ
          PE.subst (U.Subst _) n₁≡n₂ (⌜ σ₁ ⌝ˢ γ) ≡
          ⌜ σ₂ ⌝ˢ γ ∷ ⌜ Η₂ ⌝ᶜᵛ γ
      equal-sub′-sound′ _ eq _ _ _ _
        with inv->>= eq
      equal-sub′-sound′ _ _ _ _ ⊢Δ _ | inv ε _ ok! =
        ⊢ˢʷ≡∷ε⇔ .proj₂ ⊢Δ
      equal-sub′-sound′ {σ₁} {σ₂} _ _ ⊢γ ⊢σ₂ ⊢Δ (∙ ⊢A)
        | inv (ext Δ₁ _ Δ₂ A) _ eq
        with inv->>= eq
      … | inv _ ok! eq
        with inv->>= eq
      equal-sub′-sound′ {b = true} {σ₁} {σ₂} {γ} _ _ ⊢γ ⊢σ₂ ⊢Δ (∙ ⊢A)
        | inv (ext _ _ _ A) _ _ | inv _ ok! _ | inv PE.refl eq₁ eq
        with inv->>= eq
      … | inv _ ok! eq
        with inv->>= eq
      … | inv σ₁₀ eq₂ eq
        with inv->>= eq
      … | inv _ eq₃ ok! =
        let ⊢σ₂₊ =
              cast-⊢ˢʷ∷ (PE.sym ∘→ ⌜tailₛ⌝ˢ σ₂) $
              ⊢ˢʷ∷∙⇔ .proj₁ (⊢σ₂ _) .proj₁
            σ₁₊≡σ₂₊ =
              cast-⊢ˢʷ≡∷ (⌜tailₛ⌝ˢ σ₁) (⌜tailₛ⌝ˢ σ₂) $
              equal-sub′-sound eq₁ ⊢γ (λ _ → ⊢σ₂₊) ⊢Δ (wf ⊢A)
            _ , ⊢σ₁₊ , _ =
              wf-⊢ˢʷ≡∷ σ₁₊≡σ₂₊
            σ₁₀≡σ₁₀ =
              check-sound eq₂ ⊢γ
                (subst-⊢ ⊢A (cast-⊢ˢʷ∷ (PE.sym ∘→ ⌜tailₛ⌝ˢ σ₁) ⊢σ₁₊))
            _ , _ , ⊢σ₁₀ =
              wf-⊢≡∷ σ₁₀≡σ₁₀
            A[]≡A[] =
              substVar-to-subst (⌜tailₛ⌝ˢ σ₁) (⌜ A ⌝ _)
            ⊢σ₂₀ =
              PE.subst₂ (_⊢_∷_ _)
                (PE.sym (⌜headₛ⌝ σ₂)) (PE.sym A[]≡A[]) $
              conv (⊢ˢʷ∷∙⇔ .proj₁ (⊢σ₂ _) .proj₂)
                (sym (subst-⊢≡ (refl ⊢A) σ₁₊≡σ₂₊))

            open TmR
        in
        ⊢ˢʷ≡∷∙⇔′ ⊢A .proj₂
          ( σ₁₊≡σ₂₊
          , (U.head (⌜ σ₁ ⌝ˢ γ) ∷ ⌜ A ⌝ γ U.[ U.tail (⌜ σ₁ ⌝ˢ γ) ]  ≡˘⟨ ⌜headₛ⌝ σ₁ ⟩⊢∷≡
                                                                     ˘⟨ A[]≡A[] ⟩≡≡
             ⌜ headₛ σ₁ ⌝ γ     ∷ ⌜ subst A (tailₛ σ₁) ⌝ γ          ≡⟨ σ₁₀≡σ₁₀ ⟩⊢∷
             ⌜ σ₁₀ ⌝ γ                                              ≡⟨ equal-tm-sound eq₃ ⊢γ ⊢σ₁₀ ⊢σ₂₀ ⟩⊢∎≡
             ⌜ headₛ σ₂ ⌝ γ                                         ≡⟨ ⌜headₛ⌝ σ₂ ⟩
             U.head (⌜ σ₂ ⌝ˢ γ)                                     ∎)
          )
      equal-sub′-sound′ {b = false} {σ₁} {σ₂} _ _ ⊢γ _ ⊢Δ (∙ ⊢A)
        | inv (ext _ _ _ A) _ _ | inv _ ok! _ | inv PE.refl eq₁ eq
        with inv->>= eq
      … | inv _ eq₂ ok! =
        let σ₁₊≡σ₂₊ =
              cast-⊢ˢʷ≡∷ (⌜tailₛ⌝ˢ σ₁) (⌜tailₛ⌝ˢ σ₂) $
              equal-sub′-sound eq₁ ⊢γ (λ ()) ⊢Δ (wf ⊢A)
            _ , ⊢σ₁₊ , _ =
              wf-⊢ˢʷ≡∷ σ₁₊≡σ₂₊
            A[]≡A[] = substVar-to-subst (⌜tailₛ⌝ˢ σ₁) (⌜ A ⌝ _)
        in
        ⊢ˢʷ≡∷∙⇔′ ⊢A .proj₂
          ( σ₁₊≡σ₂₊
          , PE.subst₃ (_⊢_≡_∷_ _) (⌜headₛ⌝ σ₁) (⌜headₛ⌝ σ₂) A[]≡A[]
              (check-and-equal-tm-sound eq₂ ⊢γ
                 (PE.subst (_⊢_ _) (PE.sym A[]≡A[]) (subst-⊢ ⊢A ⊢σ₁₊))
                 .proj₂)
          )
      equal-sub′-sound′ {∇} _ _ _ _ ⊢Δ _ | inv base _ eq
        with inv->>= eq
      … | inv (both _ PE.refl) _ eq
        with inv->>= eq
      … | inv _ eq ok! =
        refl-⊢ˢʷ≡∷ (equal-sub″-sound ∇ eq ⊢Δ)

  private

    -- Soundness for below′.

    below′-sound :
      ∀ l₁ →
      OK (below′ n Γ (n₁ , l₁) (n₂ , l₂)) tt γ st →
      Contexts-wf (Γ .defs) γ →
      ⌜ Γ ⌝ᶜ γ ⊢ ⌜ l₁ ⌝ γ ∷Level →
      ⌜ Γ ⌝ᶜ γ ⊢ ⌜ l₂ ⌝ γ ∷Level →
      ⌜ Γ ⌝ᶜ γ ⊢ U.1ᵘ+ⁿ n₁ (⌜ l₁ ⌝ γ) ≤ₗ U.1ᵘ+ⁿ n₂ (⌜ l₂ ⌝ γ) ∷Level
    below′-sound {l₂} l₁ eq ⊢γ ⊢l₁ ⊢l₂ with inv->>= eq
    … | inv n₁≤n₂ _ eq
      with are-meta-variables? l₁ l₂
    … | nothing
      with are-level? l₁ l₂
    … | just (_ , _ , PE.refl , PE.refl) =
      let inv _ eq₁ eq₂ = inv->>= eq
          L.lift okᴸ    = inv-require⁰ ⊢γ level-allowed eq₁
          l₁≡l₂         = equal-tm-sound eq₂ ⊢γ
                            (⊢∷Level→⊢∷Level okᴸ ⊢l₁)
                            (⊢∷Level→⊢∷Level okᴸ ⊢l₂)
      in
      1ᵘ+ⁿ-mono n₁≤n₂ (reflexive-⊢≤ₗ∷L (term-⊢≡∷ l₁≡l₂))
    … | nothing
      with eq
    … | not-ok
    below′-sound _ _ ⊢γ ⊢l₁ _
      | inv n₁≤n₂ _ eq
      | just (_ , _ , σ₁ , _ , _ , _ , PE.refl , PE.refl)
      with inv->>= eq
    … | inv _ _ eq
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv PE.refl eq₂ eq₃ =
      let ⊢Γ                       = wf ⊢l₁
          x₂-level , ⊢Δ₂ , ⊢σ₂ , _ = is-level-sound eq₁ ⊢γ ⊢Γ
          σ₁≡σ₂                    = equal-sub′-sound eq₂ ⊢γ (λ _ → ⊢σ₂)
                                       ⊢Γ ⊢Δ₂
          x₁[σ₁]≡x₂[σ₂]            = are-equal-meta-vars-sound-level σ₁
                                       eq₃ ⊢γ x₂-level σ₁≡σ₂
      in
      1ᵘ+ⁿ-mono n₁≤n₂ (reflexive-⊢≤ₗ∷L x₁[σ₁]≡x₂[σ₂])

  opaque
    unfolding ⌜_⌝ⁿ _⊢⌜_⌝ⁿ_∷Level

    -- Soundness for below.

    below-sound :
      OK (below n Γ ns₁ ns₂) tt γ st →
      Contexts-wf (Γ .defs) γ →
      ⌜ Γ ⌝ᶜ γ ⊢⌜ ns₁ , ℓ ⌝ⁿ γ ∷Level →
      ⌜ Γ ⌝ᶜ γ ⊢⌜ ns₂ , ℓ ⌝ⁿ γ ∷Level →
      Below (⌜ Γ ⌝ᶜ γ) γ (ns₁ , ℓ) (ns₂ , ℓ)
    below-sound {Γ} {γ} eq ⊢γ (⊢ns₁ , _) (⊢ns₂ , _) =
      ≤⁻-refl , below-sound₁ (All.map inv-any (inv-all eq)) ⊢ns₁ ⊢ns₂
      where
      below-sound₂ :
        ∀ l₁ →
        Any (λ nl₂ → OK (below′ n Γ (n₁ , l₁) nl₂) tt γ st) ns₂ →
        ⌜ Γ ⌝ᶜ γ ⊢ ⌜ l₁ ⌝ γ ∷Level →
        ⌜ Γ ⌝ᶜ γ ⊢⌜ ns₂ ⌝ⁿ′ γ ∷Level →
        Any
          (λ (n₂ , l₂) →
             ⌜ Γ ⌝ᶜ γ ⊢ U.1ᵘ+ⁿ n₁ (⌜ l₁ ⌝ γ) ≤ₗ U.1ᵘ+ⁿ n₂ (⌜ l₂ ⌝ γ)
               ∷Level)
          ns₂
      below-sound₂ l₁ (List.here eq) ⊢l₁ (⊢l₂ , _) =
        List.here (below′-sound l₁ eq ⊢γ ⊢l₁ ⊢l₂)
      below-sound₂ l₁ (List.there below) ⊢l₁ (_ , ⊢ns₂) =
        List.there (below-sound₂ l₁ below ⊢l₁ ⊢ns₂)

      below-sound₁ :
        All (λ nl₁ → Any (λ nl₂ → OK (below′ n Γ nl₁ nl₂) tt γ st) ns₂)
          ns₁ →
        ⌜ Γ ⌝ᶜ γ ⊢⌜ ns₁ ⌝ⁿ′ γ ∷Level →
        ⌜ Γ ⌝ᶜ γ ⊢⌜ ns₂ ⌝ⁿ′ γ ∷Level →
        All
          (λ (n₁ , l₁) →
             Any
               (λ (n₂ , l₂) →
                  ⌜ Γ ⌝ᶜ γ ⊢ U.1ᵘ+ⁿ n₁ (⌜ l₁ ⌝ γ) ≤ₗ
                    U.1ᵘ+ⁿ n₂ (⌜ l₂ ⌝ γ) ∷Level)
               ns₂)
          ns₁
      below-sound₁ List.[] _ _ =
        List.[]
      below-sound₁
        (List._∷_ {x = _ , l₁} below₁ below₂) (⊢l₁ , ⊢ns₁) ⊢ns₂ =
        below-sound₂ l₁ below₁ ⊢l₁ ⊢ns₂ List.∷
        below-sound₁ below₂ ⊢ns₁ ⊢ns₂

  -- Soundness for equal-level.

  equal-level-sound :
    OK (equal-level n Γ l₁ l₂) tt γ st →
    Contexts-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ Term[]→Lvl l₁ ⌝ γ ∷Level →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ Term[]→Lvl l₂ ⌝ γ ∷Level →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ Term[]→Lvl l₁ ⌝ γ ≡ ⌜ Term[]→Lvl l₂ ⌝ γ ∷Level
  equal-level-sound {l₁} {l₂} {γ} eq ⊢γ ⊢l₁ ⊢l₂
    with inv->>= eq
  … | inv nf₁ eq₁ eq
    with inv->>= eq
  … | inv nf₂ eq₂ eq
    with inv->>= eq
  … | inv PE.refl _ eq =
    let inv _ eq₃ eq₄ = inv->>= eq
        ⊢nf₁ , l₁≡nf₁ = normalise-level-sound eq₁ ⊢γ ⊢l₁
        ⊢nf₂ , l₂≡nf₂ = normalise-level-sound eq₂ ⊢γ ⊢l₂
    in
    ⌜ Term[]→Lvl l₁ ⌝ γ  ≡⟨ l₁≡nf₁ ⟩⊢
    ⌜ nf₁ ⌝ⁿ γ           ≡⟨ Below-antisymmetric ⊢nf₁ ⊢nf₂
                              (below-sound eq₃ ⊢γ ⊢nf₁ ⊢nf₂)
                              (below-sound eq₄ ⊢γ ⊢nf₂ ⊢nf₁) ⟩⊢
    ⌜ nf₂ ⌝ⁿ γ           ≡˘⟨ l₂≡nf₂ ⟩⊢∎
    ⌜ Term[]→Lvl l₂ ⌝ γ  ∎
    where
    open LvlR

  -- Soundness for check-and-equal-level.

  check-and-equal-level-sound :
    OK (check-and-equal-level n Γ l₁ l₂) l γ st →
    Contexts-wf (Γ .defs) γ →
    ⊢ ⌜ Γ ⌝ᶜ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ Term[]→Lvl l₁ ⌝ γ ≡ ⌜ Term[]→Lvl l ⌝ γ ∷Level ×
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ Term[]→Lvl l₁ ⌝ γ ≡ ⌜ Term[]→Lvl l₂ ⌝ γ ∷Level
  check-and-equal-level-sound {l₁} {l₂} {γ} eq ⊢γ ⊢Γ
    with inv->>= eq
  … | inv l₁′ eq₁ eq
    with inv->>= eq
  … | inv l₂′ eq₂ eq
    with inv->>= eq
  … | inv _ eq₃ ok! =
    let l₁≡l₁′   = check-level-sound eq₁ ⊢γ ⊢Γ
        _ , ⊢l₁′ = wf-⊢≡∷L l₁≡l₁′
        l₂≡l₂′   = check-level-sound eq₂ ⊢γ ⊢Γ
        _ , ⊢l₂′ = wf-⊢≡∷L l₂≡l₂′
        l₁′≡l₂′  = equal-level-sound eq₃ ⊢γ ⊢l₁′ ⊢l₂′
    in
    l₁≡l₁′ ,
    (⌜ Term[]→Lvl l₁ ⌝ γ   ≡⟨ l₁≡l₁′ ⟩⊢
     ⌜ Term[]→Lvl l₁′ ⌝ γ  ≡⟨ l₁′≡l₂′ ⟩⊢
     ⌜ Term[]→Lvl l₂′ ⌝ γ  ≡˘⟨ l₂≡l₂′ ⟩⊢∎
     ⌜ Term[]→Lvl l₂ ⌝ γ   ∎)
    where
    open LvlR

  -- Soundness for infer-red.

  infer-red-sound :
    OK (infer-red n Γ t) A γ st →
    Contexts-wf (Γ .defs) γ →
    ⊢ ⌜ Γ ⌝ᶜ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ∷ ⌜ A ⌝ γ
  infer-red-sound eq ⊢γ ⊢Γ =
    let inv _ eq₁ eq₂ = inv->>= eq
        ⊢t            = infer-sound eq₁ ⊢γ ⊢Γ
    in
    conv ⊢t (red-ty-sound eq₂ ⊢γ (wf-⊢∷ ⊢t))

  -- Soundness for infer-U.

  infer-U-sound :
    OK (infer-U n Γ t) l γ st →
    Contexts-wf (Γ .defs) γ →
    ⊢ ⌜ Γ ⌝ᶜ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ∷ ⌜ U l ⌝ γ
  infer-U-sound eq ⊢γ ⊢Γ
    with inv->>= eq
  … | inv _ eq₁ eq
    with inv->>= eq
  … | inv (_ , PE.refl) _ ok! =
    infer-red-sound eq₁ ⊢γ ⊢Γ

  -- Soundness for equal-ne.

  equal-ne-sound :
    OK (equal-ne n Γ t₁ t₂ A) tt γ st →
    Contexts-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ≡ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ
  equal-ne-sound eq ⊢γ ⊢A =
    let inv _ eq₁ eq₂ = inv->>= eq
        t₁≡t₂         = equal-ne-inf-sound eq₁ ⊢γ (wf ⊢A)
        ⊢A′ , _       = wf-⊢≡∷ t₁≡t₂
    in
    conv t₁≡t₂ (equal-ty-sound eq₂ ⊢γ ⊢A′ ⊢A)

  -- Soundness for equal-ne-inf-red.

  equal-ne-inf-red-sound :
    OK (equal-ne-inf-red n Γ t₁ t₂) A γ st →
    Contexts-wf (Γ .defs) γ →
    ⊢ ⌜ Γ ⌝ᶜ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ≡ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ
  equal-ne-inf-red-sound eq ⊢γ ⊢Γ =
    let inv _ eq₁ eq₂ = inv->>= eq
        t₁≡t₂         = equal-ne-inf-sound eq₁ ⊢γ ⊢Γ
        ⊢A , _        = wf-⊢≡∷ t₁≡t₂
    in
    conv t₁≡t₂ (red-ty-sound eq₂ ⊢γ ⊢A)

  -- Soundness for equal-ty-red.

  equal-ty-red-sound :
    ∀ A₁ A₂ →
    OK (equal-ty-red n Γ A₁ A₂) tt γ st →
    Contexts-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A₁ ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A₂ ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A₁ ⌝ γ ≡ ⌜ A₂ ⌝ γ
  equal-ty-red-sound A₁ A₂ _ _ _ _
    with are-equal-type-constructors? A₁ A₂
  equal-ty-red-sound {γ} _ _ eq ⊢γ ⊢x₁[σ₁] _
    | just (meta-var x₁ σ₁ x₂ σ₂ PE.refl)
    rewrite ⌜meta-var⌝ {γ = γ} {x = x₁} σ₁
          | ⌜meta-var⌝ {γ = γ} {x = x₂} σ₂
    with inv->>= eq
  … | inv _ _ eq
    with inv->>= eq
  … | inv _ eq₁ eq
    with inv->>= eq
  … | inv PE.refl eq₂ eq =
    let inv _ eq₃ _ = inv->>= eq
        x₂-type , ⊢x₂ = is-type-sound eq₁ ⊢γ
        σ₁≡σ₂         = equal-sub′-sound eq₂ ⊢γ (λ ()) (wf ⊢x₁[σ₁])
                          (wf ⊢x₂)
        Δ₁≡Δ₂ , _     = wf-⊢ˢʷ≡∷ σ₁≡σ₂
        x₁≡x₂         = are-equal-meta-vars-sound-ty eq₃ ⊢γ x₂-type ⊢x₂
    in
    subst-⊢≡ x₁≡x₂ σ₁≡σ₂
  equal-ty-red-sound _ _ _ _ ⊢A₁ _ | just (Level PE.refl) =
    refl ⊢A₁
  equal-ty-red-sound _ _ eq ⊢γ ⊢A₁ ⊢A₂ | just (U _ _ PE.refl) =
    let ⊢l₁ = inversion-U-Level ⊢A₁
        ⊢l₂ = inversion-U-Level ⊢A₂
    in
    U-cong-⊢≡ (equal-level-sound eq ⊢γ ⊢l₁ ⊢l₂)
  equal-ty-red-sound _ _ eq ⊢γ ⊢A₁ ⊢A₂ | just (Lift _ _ _ _ PE.refl) =
    let inv _ eq₁ eq₂ = inv->>= eq
        ⊢l₁ , ⊢A₁     = inversion-Lift ⊢A₁
        ⊢l₂ , ⊢A₂     = inversion-Lift ⊢A₂
        l₁≡l₂         = equal-level-sound eq₁ ⊢γ ⊢l₁ ⊢l₂
        A₁≡A₂         = equal-ty-sound eq₂ ⊢γ ⊢A₁ ⊢A₂
    in
    Lift-cong l₁≡l₂ A₁≡A₂
  equal-ty-red-sound _ _ _ _ ⊢A₁ _ | just (Empty PE.refl) =
    refl ⊢A₁
  equal-ty-red-sound _ _ _ _ ⊢A₁ _ | just (Unit PE.refl) =
    refl ⊢A₁
  equal-ty-red-sound _ _ eq ⊢γ ⊢A₁ ⊢A₂ | just (ΠΣ _ _ _ _ PE.refl) =
    let inv _ eq₁ eq₂       = inv->>= eq
        ⊢A₁₁ , ⊢A₁₂ , ΠΣ-ok = inversion-ΠΣ ⊢A₁
        ⊢A₂₁ , ⊢A₂₂ , _     = inversion-ΠΣ ⊢A₂
        A₁₁≡A₂₁             = equal-ty-sound eq₁ ⊢γ ⊢A₁₁ ⊢A₂₁
    in
    ΠΣ-cong A₁₁≡A₂₁
      (equal-ty-sound eq₂ ⊢γ ⊢A₁₂
         (stability (refl-∙ (sym A₁₁≡A₂₁)) ⊢A₂₂))
      ΠΣ-ok
  equal-ty-red-sound _ _ _ _ ⊢A₁ _ | just (ℕ PE.refl) =
    refl ⊢A₁
  equal-ty-red-sound _ _ eq ⊢γ ⊢A₁ ⊢A₂
    | just (Id _ _ _ _ _ _ PE.refl) =
    let inv _ eq₁ eq      = inv->>= eq
        inv _ eq₂ eq₃     = inv->>= eq
        ⊢A₁ , ⊢t₁₁ , ⊢t₁₂ = inversion-Id ⊢A₁
        ⊢A₂ , ⊢t₂₁ , ⊢t₂₂ = inversion-Id ⊢A₂
        A₁≡A₂             = equal-ty-sound eq₁ ⊢γ ⊢A₁ ⊢A₂
    in
    Id-cong A₁≡A₂
      (equal-tm-sound eq₂ ⊢γ ⊢t₁₁ (conv ⊢t₂₁ (sym A₁≡A₂)))
      (equal-tm-sound eq₃ ⊢γ ⊢t₁₂ (conv ⊢t₂₂ (sym A₁≡A₂)))
  equal-ty-red-sound _ _ eq ⊢γ ⊢A₁ ⊢A₂ | nothing
    with inv->>= eq
  … | inv _ eq₁ eq
    with inv->>= eq
  … | inv (_ , PE.refl) _ ok! =
    univ (equal-ne-inf-red-sound eq₁ ⊢γ (wf ⊢A₁))

  -- Soundness for equal-ty-red-U.

  equal-ty-red-U-sound :
    ∀ A₁ →
    OK (equal-ty-red-U n Γ A₁ A₂ l) tt γ st →
    Contexts-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A₁ ⌝ γ ∷ ⌜ U l ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A₂ ⌝ γ ∷ ⌜ U l ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A₁ ⌝ γ ≡ ⌜ A₂ ⌝ γ ∷ ⌜ U l ⌝ γ
  equal-ty-red-U-sound {A₂} A₁ _ _ _ _
    with are-equal-type-constructors? A₁ A₂
  equal-ty-red-U-sound {γ} _ eq ⊢γ ⊢x₁[σ₁] _
    | just (meta-var x₁ σ₁ x₂ σ₂ PE.refl)
    rewrite ⌜meta-var⌝ {γ = γ} {x = x₁} σ₁
          | ⌜meta-var⌝ {γ = γ} {x = x₂} σ₂
    with inv->>= eq
  … | inv _ _ eq
    with inv->>= eq
  … | inv _ eq₁ eq
    with inv->>= eq
  … | inv PE.refl eq₂ eq =
    let inv _ eq₃ eq₄ = inv->>= eq
        x₂-term , ⊢x₂ = is-term-sound eq₁ ⊢γ
        σ₁≡σ₂         = equal-sub′-sound eq₂ ⊢γ (λ ()) (wf ⊢x₁[σ₁])
                          (wf ⊢x₂)
        _ , ⊢σ₁ , _   = wf-⊢ˢʷ≡∷ σ₁≡σ₂
        x₁≡x₂         = are-equal-meta-vars-sound-tm eq₃ ⊢γ x₂-term ⊢x₂
        A[σ₁]≡Ul      = equal-ty-sound eq₄ ⊢γ
                          (subst-⊢ (wf-⊢∷ ⊢x₂) ⊢σ₁) (wf-⊢∷ ⊢x₁[σ₁])
    in
    conv (subst-⊢≡∷ x₁≡x₂ σ₁≡σ₂) A[σ₁]≡Ul
  equal-ty-red-U-sound _ _ _ ⊢A₁ _ | just (Level PE.refl) =
    refl ⊢A₁
  equal-ty-red-U-sound _ eq ⊢γ ⊢A₁ ⊢A₂ | just (U _ _ PE.refl) =
    let Ul≡U1+l₁ = inversion-U ⊢A₁
        ⊢l₁      = inversion-U∷-Level ⊢A₁
        ⊢l₂      = inversion-U∷-Level ⊢A₂
    in
    conv (U-cong-⊢≡∷ (equal-level-sound eq ⊢γ ⊢l₁ ⊢l₂)) (sym Ul≡U1+l₁)
  equal-ty-red-U-sound {γ} _ eq ⊢γ ⊢A₁ ⊢A₂
    | just (Lift _ A₁ _ A₂ PE.refl) =
    let open TmR

        inv _ eq₁ eq   = inv->>= eq
        inv _ eq₂ eq   = inv->>= eq
        inv A₂′ eq₃ eq = inv->>= eq
        inv _ eq₄ eq₅  = inv->>= eq
        _ , ⊢l₁ , _    = inversion-Lift∷ ⊢A₁
        _ , ⊢l₂ , _    = inversion-Lift∷ ⊢A₂
        l₁≡l₂          = equal-level-sound eq₁ ⊢γ ⊢l₁ ⊢l₂
        ⊢l₁ , _        = wf-⊢≡∷L l₁≡l₂
        ⊢A₁            = infer-U-sound eq₂ ⊢γ (wf ⊢A₁)
        ⊢l₃            = inversion-U-Level (wf-⊢∷ ⊢A₁)
        A₂≡A₂′         = check-sound eq₃ ⊢γ (⊢U ⊢l₃)
        _ , _ , ⊢A₂′   = wf-⊢≡∷ A₂≡A₂′
        A₁≡A₂′         = equal-tm-sound eq₄ ⊢γ ⊢A₁ ⊢A₂′
        ⊢l             = inversion-U-Level (wf-⊢∷ ⊢A₂)
        ⊔≡l            = equal-level-sound eq₅ ⊢γ (⊢supᵘₗ ⊢l₃ ⊢l₁) ⊢l
        A₁≡A₂          =
          ⌜ A₁ ⌝ γ   ≡⟨ A₁≡A₂′ ⟩⊢
          ⌜ A₂′ ⌝ γ  ≡˘⟨ A₂≡A₂′ ⟩⊢∎
          ⌜ A₂ ⌝ γ   ∎
    in
    conv (Lift-cong′ l₁≡l₂ A₁≡A₂) (U-cong-⊢≡ ⊔≡l)
  equal-ty-red-U-sound _ _ _ ⊢A₁ _ | just (Empty PE.refl) =
    refl ⊢A₁
  equal-ty-red-U-sound _ _ _ ⊢A₁ _ | just (Unit PE.refl) =
    refl ⊢A₁
  equal-ty-red-U-sound _ eq ⊢γ ⊢A₁ _ | just (ΠΣ _ _ _ _ PE.refl) =
    let inv _ eq₁ eq              = inv->>= eq
        inv _ eq₂ _               = inv->>= eq
        _ , _ , _ , _ , _ , ΠΣ-ok = inversion-ΠΣ-U ⊢A₁
        ⊢Ul                       = wf-⊢∷ ⊢A₁
        ⊢l                        = inversion-U-Level ⊢Ul
        A₁₁≡A₁ , A₁₁≡A₂₁          = check-and-equal-tm-sound eq₁ ⊢γ ⊢Ul
        _ , _ , ⊢A₁               = wf-⊢≡∷ A₁₁≡A₁
        _ , A₁₂≡A₂₂               = check-and-equal-tm-sound eq₂ ⊢γ
                                      (W.wk₁ (univ ⊢A₁) ⊢Ul)
    in
    ΠΣ-cong ⊢l A₁₁≡A₂₁
      (stability (refl-∙ (sym (univ A₁₁≡A₁))) A₁₂≡A₂₂) ΠΣ-ok
  equal-ty-red-U-sound _ _ _ ⊢A₁ _ | just (ℕ PE.refl) =
    refl ⊢A₁
  equal-ty-red-U-sound _ eq ⊢γ ⊢A₁ ⊢A₂
    | just (Id _ _ _ _ _ _ PE.refl) =
   let inv _ eq₁ eq      = inv->>= eq
       inv _ eq₂ eq₃     = inv->>= eq
       ⊢A₁ , ⊢t₁₁ , ⊢t₁₂ = inversion-Id∷U ⊢A₁
       ⊢A₂ , ⊢t₂₁ , ⊢t₂₂ = inversion-Id∷U ⊢A₂
       A₁≡A₂             = equal-tm-sound eq₁ ⊢γ ⊢A₁ ⊢A₂
       A₂≡A₁             = sym (univ A₁≡A₂)
   in
   Id-cong A₁≡A₂
     (equal-tm-sound eq₂ ⊢γ ⊢t₁₁ (conv ⊢t₂₁ A₂≡A₁))
     (equal-tm-sound eq₃ ⊢γ ⊢t₁₂ (conv ⊢t₂₂ A₂≡A₁))
  equal-ty-red-U-sound _ eq ⊢γ ⊢A₁ _ | nothing
    with inv->>= eq
  … | inv _ eq₁ eq
    with inv->>= eq
  … | inv _ eq₂ _ =
    let A₁≡A₂  = equal-ne-inf-red-sound eq₁ ⊢γ (wf ⊢A₁)
        ⊢B , _ = wf-⊢≡∷ A₁≡A₂
        B≡Ul   = equal-ty-sound eq₂ ⊢γ ⊢B (wf-⊢∷ ⊢A₁)
    in
    conv A₁≡A₂ B≡Ul

  -- Soundness for equal-ne-red.

  equal-ne-red-sound :
    OK (equal-ne-red n Γ t₁ t₂ A) tt γ st →
    Contexts-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ≡ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ
  equal-ne-red-sound {A} eq ⊢γ ⊢A =
    let inv A′ eq₁ eq₂ = inv->>= eq
        t₁≡t₂          = equal-ne-inf-red-sound eq₁ ⊢γ (wf ⊢A)
        ⊢A′ , _        = wf-⊢≡∷ t₁≡t₂
    in
    conv t₁≡t₂ (equal-ty-red-sound A′ A eq₂ ⊢γ ⊢A′ ⊢A)

  -- Soundness for equal-tm-red.

  equal-tm-red-sound :
    ∀ A →
    OK (equal-tm-red n Γ t₁ t₂ A) tt γ st →
    Contexts-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ∷ ⌜ A ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ≡ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ
  equal-tm-red-sound A _ _ _ _
    with is-type-constructorˡ? A
  equal-tm-red-sound _ eq ⊢γ ⊢t₁ ⊢t₂
    | just (meta-var _ _) =
    equal-ne-red-sound eq ⊢γ (wf-⊢∷ ⊢t₁)
  equal-tm-red-sound {t₁} {t₂} _ eq ⊢γ ⊢t₁ ⊢t₂
    | just Level
    using ⊢Γ  ← wf ⊢t₁
        | okᴸ ← inversion-Level-⊢ (wf-⊢∷ ⊢t₁)
    with equal-level-cons? t₁ t₂ | eq
  … | just zeroᵘ | ok! =
    refl (zeroᵘⱼ okᴸ ⊢Γ)
  … | just (1ᵘ+ _ _) | eq =
    let ⊢l₁ , _ = inversion-sucᵘ ⊢t₁
        ⊢l₂ , _ = inversion-sucᵘ ⊢t₂
    in
    sucᵘ-cong (equal-tm-sound eq ⊢γ ⊢l₁ ⊢l₂)
  … | nothing | eq =
    equal-ne-red-sound eq ⊢γ (Levelⱼ′ okᴸ ⊢Γ)
  equal-tm-red-sound {t₁} {t₂} _ eq ⊢γ ⊢t₁ ⊢t₂
    | just (U _)
    with inv-if-no-equality-reflection ⊢γ eq
  … | inj₁ (no-refl , eq) =
    inverseUnivEq ⦃ no-equality-reflection = no-refl ⦄ ⊢t₁ $
    equal-ty-red-sound t₁ t₂ eq ⊢γ (univ ⊢t₁) (univ ⊢t₂)
  … | inj₂ eq =
    equal-ty-red-U-sound t₁ eq ⊢γ ⊢t₁ ⊢t₂
  equal-tm-red-sound _ eq ⊢γ ⊢t₁ ⊢t₂
    | just (Lift _ _) =
    let lower-t₁≡lower-t₂ =
          equal-tm-sound eq ⊢γ (lowerⱼ ⊢t₁) (lowerⱼ ⊢t₂)
    in
    Lift-η′ ⊢t₁ ⊢t₂ lower-t₁≡lower-t₂
  equal-tm-red-sound _ eq ⊢γ ⊢t₁ ⊢t₂
    | just Empty =
    equal-ne-red-sound eq ⊢γ (wf-⊢∷ ⊢t₁)
  equal-tm-red-sound {t₁} {t₂} {γ} _ eq ⊢γ ⊢t₁ ⊢t₂
    | just (Unit s)
    with s ≟ˢ 𝕤
  … | just PE.refl =
    η-unit ⊢t₁ ⊢t₂ (inj₁ PE.refl)
  … | nothing
    with inv-catch eq
  … | inj₂ eq =
    let L.lift η = inv-require⁺ ⊢γ eq in
    η-unit ⊢t₁ ⊢t₂ η
  … | inj₁ eq
    with inv-if-no-equality-reflection ⊢γ eq
  … | inj₁ (no-refl , eq)
    with are-star? t₁ t₂
  … | just (s₁ , s₂ , PE.refl , PE.refl) =
    let s₁≡s , _ =
          inversion-star-Unit
            ⦃ ok = possibly-nonempty ⦃ ok = no-refl ⦄ ⦄ ⊢t₁
        s₂≡s , _ =
          inversion-star-Unit
            ⦃ ok = possibly-nonempty ⦃ ok = no-refl ⦄ ⦄ ⊢t₂

        open TmR
    in
    ⌜ star s₁ ⌝ γ  ≡⟨ PE.cong U.star s₁≡s ⟩⊢≡
    ⌜ star s  ⌝ γ  ≡⟨ PE.subst₃ (_⊢_≡_∷_ _) (PE.cong U.star s₂≡s) PE.refl PE.refl $
                      refl ⊢t₂ ⟩⊢∎
    ⌜ star s₂ ⌝ γ  ∎
  … | nothing =
    equal-ne-red-sound eq ⊢γ (wf-⊢∷ ⊢t₁)
  equal-tm-red-sound {t₁} {t₂} _ _ ⊢γ ⊢t₁ _
    | just (Unit s) | nothing | inj₁ _ | inj₂ eq
    with are-star⟨ s ⟩? t₁ t₂
  … | just (PE.refl , PE.refl) =
    refl ⊢t₁
  … | nothing =
    equal-ne-red-sound eq ⊢γ (wf-⊢∷ ⊢t₁)
  equal-tm-red-sound {t₁} {t₂} _ eq ⊢γ ⊢t₁ ⊢t₂
    | just ℕ
    with are-zero-or-suc? t₁ t₂
  … | just (inj₁ (PE.refl , PE.refl)) =
    refl ⊢t₁
  … | just (inj₂ (_ , _ , PE.refl , PE.refl)) =
    suc-cong $
    equal-tm-sound eq ⊢γ (inversion-suc ⊢t₁ .proj₁)
      (inversion-suc ⊢t₂ .proj₁)
  … | nothing =
    equal-ne-red-sound eq ⊢γ (wf-⊢∷ ⊢t₁)
  equal-tm-red-sound _ eq ⊢γ ⊢t₁ ⊢t₂
    | just (ΠΣ BMΠ _ _ _ _) =
    let ⊢A₁ , _     = inversion-ΠΣ (wf-⊢∷ ⊢t₁)
        t₁∘x0≡t₂∘x0 =
          equal-tm-sound eq ⊢γ
            (PE.subst (_⊢_∷_ _ _) (wkSingleSubstId _) $
             W.wk₁ ⊢A₁ ⊢t₁ ∘ⱼ var₀ ⊢A₁)
            (PE.subst (_⊢_∷_ _ _) (wkSingleSubstId _) $
             W.wk₁ ⊢A₁ ⊢t₂ ∘ⱼ var₀ ⊢A₁)
    in
    η-eq′ ⊢t₁ ⊢t₂ t₁∘x0≡t₂∘x0
  equal-tm-red-sound {t₁} {t₂} {γ} _ eq ⊢γ ⊢t₁ ⊢t₂
    | just (ΠΣ (BMΣ s) p _ _ _)
    with s ≟ˢ 𝕤
  … | just PE.refl =
    let inv _ eq₁ eq₂ = inv->>= eq
        _ , ⊢A₂ , _   = inversion-ΠΣ (wf-⊢∷ ⊢t₁)
        fst-t₁≡fst-t₂ = equal-tm-sound eq₁ ⊢γ (fstⱼ′ ⊢t₁) (fstⱼ′ ⊢t₂)
    in
    Σ-η′ ⊢t₁ ⊢t₂ fst-t₁≡fst-t₂
      (equal-tm-sound eq₂ ⊢γ (sndⱼ′ ⊢t₁)
         (conv (sndⱼ′ ⊢t₂) $
          subst-⊢≡₀ ⊢A₂ (sym′ fst-t₁≡fst-t₂)))
  … | nothing
    with inv-if-no-equality-reflection ⊢γ eq
  … | inj₁ (no-refl , eq)
    with are-prod? t₁ t₂
  … | nothing =
    equal-ne-red-sound eq ⊢γ (wf-⊢∷ ⊢t₁)
  … | just (s₁ , p₁ , _ , t₁₁ , t₁₂ ,
            s₂ , p₂ , _ , t₂₁ , t₂₂ , PE.refl , PE.refl) =
    let inv _ eq₁ eq₂ =
          inv->>= eq
        _ , ⊢A₂ , Σ-ok =
          inversion-ΠΣ (wf-⊢∷ ⊢t₁)
        ⊢t₁₁ , ⊢t₁₂ , s≡s₁ , p≡p₁ , _ =
          inversion-prod-Σ ⦃ ok = possibly-nonempty ⦃ ok = no-refl ⦄ ⦄
            ⊢t₁
        ⊢t₂₁ , ⊢t₂₂ , s≡s₂ , p≡p₂ , _ =
          inversion-prod-Σ ⦃ ok = possibly-nonempty ⦃ ok = no-refl ⦄ ⦄
            ⊢t₂
        t₁₁≡t₂₁ =
          equal-tm-sound eq₁ ⊢γ ⊢t₁₁ ⊢t₂₁
        t₁₂≡t₂₂ =
          equal-tm-sound eq₂ ⊢γ ⊢t₁₂
            (conv ⊢t₂₂ (sym (subst-⊢≡₀ ⊢A₂ t₁₁≡t₂₁)))

        open TmR
    in
    U.prod (⟦ s₁ ⟧ˢ γ) (⟦ p₁ ⟧ᵍ γ) (⌜ t₁₁ ⌝ γ) (⌜ t₁₂ ⌝ γ)  ≡˘⟨ PE.cong₂ (λ s p → U.prod s p _ _) s≡s₁ p≡p₁ ⟩⊢≡
    U.prod (⟦ s  ⟧ˢ γ) (⟦ p  ⟧ᵍ γ) (⌜ t₁₁ ⌝ γ) (⌜ t₁₂ ⌝ γ)  ≡⟨ prod-cong ⊢A₂ t₁₁≡t₂₁ t₁₂≡t₂₂ Σ-ok ⟩⊢∎≡
    U.prod (⟦ s  ⟧ˢ γ) (⟦ p  ⟧ᵍ γ) (⌜ t₂₁ ⌝ γ) (⌜ t₂₂ ⌝ γ)  ≡⟨ PE.cong₂ (λ s p → U.prod s p _ _) s≡s₂ p≡p₂ ⟩
    U.prod (⟦ s₂ ⟧ˢ γ) (⟦ p₂ ⟧ᵍ γ) (⌜ t₂₁ ⌝ γ) (⌜ t₂₂ ⌝ γ)  ∎
  equal-tm-red-sound {t₁} {t₂} _ _ ⊢γ ⊢t₁ _
    | just (ΠΣ (BMΣ s) p _ _ _) | nothing | inj₂ eq
    with are-prod⟨ s , p ⟩? t₁ t₂
  … | nothing =
    equal-ne-red-sound eq ⊢γ (wf-⊢∷ ⊢t₁)
  … | just (_ , _ , _ , _ , _ , _ , PE.refl , PE.refl) =
    let inv _ eq₁ eq     = inv->>= eq
        inv _ eq₂ _      = inv->>= eq
        ⊢A₁ , ⊢A₂ , Σ-ok = inversion-ΠΣ (wf-⊢∷ ⊢t₁)
        t₁₁≡t₁ , t₁₁≡t₂₁ = check-and-equal-tm-sound eq₁ ⊢γ ⊢A₁
        _ , _ , ⊢t₁      = wf-⊢≡∷ t₁₁≡t₁
        _ , t₁₂≡t₂₂      = check-and-equal-tm-sound eq₂ ⊢γ
                             (subst-⊢₀ ⊢A₂ ⊢t₁)
        t₁₂≡t₂₂          = conv t₁₂≡t₂₂ $
                           subst-⊢≡₀ ⊢A₂ (sym′ t₁₁≡t₁)
    in
    prod-cong ⊢A₂ t₁₁≡t₂₁ t₁₂≡t₂₂ Σ-ok
  equal-tm-red-sound {t₁} {t₂} _ eq ⊢γ ⊢t₁ ⊢t₂
    | just (Id _ _ _)
    with are-rfl? t₁ t₂
  … | just (_ , _ , PE.refl , PE.refl) =
    refl ⊢t₁
  … | nothing =
    equal-ne-red-sound eq ⊢γ (wf-⊢∷ ⊢t₁)
  equal-tm-red-sound _ eq ⊢γ ⊢t₁ ⊢t₂
    | nothing =
    equal-ne-red-sound eq ⊢γ (wf-⊢∷ ⊢t₁)

  opaque
    unfolding S._supᵘₗ_

    -- Soundness for red-tm′.

    red-tm′-sound :
      ∀ t → OK (red-tm′ n Γ t A) u γ st →
      Contexts-wf (Γ .defs) γ →
      ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ∷ ⌜ A ⌝ γ →
      ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ≡ ⌜ u ⌝ γ ∷ ⌜ A ⌝ γ
    red-tm′-sound (meta-var _ _) ok! _ ⊢x =
      refl ⊢x
    red-tm′-sound {u} {γ} (weaken ρ t) eq ⊢γ ⊢wk-ρ-t =
      let open TmR
          eq′ = PE.sym (⌜wk⌝ t)
      in
      U.wk ρ (⌜ t ⌝ γ)  ≡⟨ eq′ ⟩⊢≡
      ⌜ wk ρ t ⌝ γ      ≡⟨ red-tm-sound eq ⊢γ $
                           PE.subst (flip (_⊢_∷_ _) _) eq′ ⊢wk-ρ-t ⟩⊢∎
      ⌜ u ⌝ γ           ∎
    red-tm′-sound {u} {γ} (subst t σ) eq ⊢γ ⊢t[σ] =
      let open TmR
          eq′ = PE.sym (⌜[]⌝ t (term₂ ⊢t[σ]))
      in
      ⌜ t ⌝ γ U.[ ⌜ σ ⌝ˢ γ ]  ≡⟨ eq′ ⟩⊢≡
      ⌜ t [ σ ] ⌝ γ           ≡⟨ red-tm-sound eq ⊢γ $
                                 PE.subst (flip (_⊢_∷_ _) _) eq′ ⊢t[σ] ⟩⊢∎
      ⌜ u ⌝ γ                 ∎
    red-tm′-sound (var _) ok! _ ⊢x =
      refl ⊢x
    red-tm′-sound {Γ} {A} {u} {γ} (defn α) eq ⊢γ ⊢α
      using inv (t , B) eq₁ eq ← inv->>= eq
      with inv->>= eq
    … | inv t′ eq₂ ok! =
      let ⊢Γ               = wf ⊢α
          A′ , α↦A′ , A≡A′ = inversion-defn ⊢α
          α↦t∷B , B≡A′     = Σ.map idᶠ (λ hyp → hyp α↦A′) $
                             definition-of-sound (Γ .defs) eq₁
                               (defn-wf ⊢Γ)

          open TmR
      in
               ∷ ⌜ A ⌝ γ                ⟨ A≡A′ ⟩≡∷
               ∷ U.wk U.wk₀ A′         ˘⟨ W.wk (W.wk₀∷ʷ⊇ ⊢Γ) B≡A′ ⟩≡∷
      U.defn α ∷ U.wk U.wk₀ (⌜ B ⌝ γ)  ≡⟨ δ-red ⊢Γ α↦t∷B PE.refl PE.refl ⟩⊢∷
      U.wk U.wk₀ (⌜ t ⌝ γ)             ≡⟨ W.wk (W.wk₀∷ʷ⊇ ⊢Γ) $
                                          red-tm-sound eq₂ ⊢γ $
                                          wf-↦∷∈ α↦t∷B (defn-wf ⊢Γ) ⟩⊢∎≡
      U.wk U.wk₀ (⌜ t′ ⌝ γ)            ≡˘⟨ ⌜wk⌝ t′ ⟩
      ⌜ wk U.wk₀ t′ ⌝ γ                ≡⟨⟩
      ⌜ u ⌝ γ                          ∎
    red-tm′-sound Level ok! _ ⊢Level =
      refl ⊢Level
    red-tm′-sound zeroᵘ ok! _ ⊢zeroᵘ =
      refl ⊢zeroᵘ
    red-tm′-sound (1ᵘ+ _) ok! _ ⊢1ᵘ+ =
      refl ⊢1ᵘ+
    red-tm′-sound {A} {u} {γ} (l₁ supᵘₗ l₂) eq ⊢γ ⊢sup
      with inv->>= eq
    … | inv l₁′ eq₁ eq
      using ⊢l₁ , ⊢l₂ , A≡Level ← inversion-supᵘₗ-⊢∷ ⊢sup
          | okᴸ                 ← inversion-Level-⊢
                                    (wf-⊢≡ A≡Level .proj₂)
          | l₁≡l₁′              ← red-tm-sound eq₁ ⊢γ ⊢l₁
          | _ , _ , ⊢l₁′        ← wf-⊢≡∷ l₁≡l₁′
          | l₁⊔l₂≡              ←
              ⊢≡∷Level→⊢≡∷Level okᴸ $
              supᵘₗ-cong (term-⊢≡∷ l₁≡l₁′) (refl-⊢≡∷L (term-⊢∷ ⊢l₂))
      with level-con? l₁′ | eq
    … | nothing | ok! =
      let open TmR in
                        ∷ ⌜ A ⌝ γ   ⟨ A≡Level ⟩≡∷
      ⌜ l₁ supᵘₗ l₂ ⌝ γ ∷ U.Level  ≡⟨ l₁⊔l₂≡ ⟩⊢∷∎≡
      ⌜ l₁′ supᵘₗ l₂ ⌝ γ           ≡⟨⟩
      ⌜ u ⌝ γ                      ∎
    … | just zeroᵘ | eq =
      let open TmR in
                        ∷ ⌜ A ⌝ γ   ⟨ A≡Level ⟩≡∷
      ⌜ l₁ supᵘₗ l₂ ⌝ γ ∷ U.Level  ≡⟨ l₁⊔l₂≡ ⟩⊢∷
      ⌜ zeroᵘ supᵘₗ l₂ ⌝ γ         ≡⟨ ⊢≡∷Level→⊢≡∷Level okᴸ $
                                      supᵘₗ-zeroˡ (term-⊢∷ ⊢l₂) ⟩⊢
      ⌜ l₂ ⌝ γ                     ≡⟨ red-tm-sound eq ⊢γ ⊢l₂ ⟩⊢∎
      ⌜ u ⌝ γ                      ∎
    … | just (1ᵘ+ l₁″) | eq
      with inv->>= eq
    … | inv l₂′ eq₂ eq
      using ⊢l₁″ , _     ← inversion-sucᵘ ⊢l₁′
          | l₂≡l₂′       ← red-tm-sound eq₂ ⊢γ ⊢l₂
          | _ , _ , ⊢l₂′ ← wf-⊢≡∷ l₂≡l₂′
          | l₁′⊔l₂≡      ←
              ⊢≡∷Level→⊢≡∷Level okᴸ $
              supᵘₗ-cong (refl-⊢≡∷L (term-⊢∷ ⊢l₁′)) (term-⊢≡∷ l₂≡l₂′)
      with level-con? l₂′ | eq
    … | nothing | ok! =
      let open TmR in
                        ∷ ⌜ A ⌝ γ   ⟨ A≡Level ⟩≡∷
      ⌜ l₁ supᵘₗ l₂ ⌝ γ ∷ U.Level  ≡⟨ l₁⊔l₂≡ ⟩⊢∷
      ⌜ 1ᵘ+ l₁″ supᵘₗ l₂ ⌝ γ       ≡⟨ l₁′⊔l₂≡ ⟩⊢∎≡
      ⌜ 1ᵘ+ l₁″ supᵘₗ l₂′ ⌝ γ      ≡⟨⟩
      ⌜ u ⌝ γ                      ∎
    … | just zeroᵘ | ok! =
      let open TmR in
                        ∷ ⌜ A ⌝ γ   ⟨ A≡Level ⟩≡∷
      ⌜ l₁ supᵘₗ l₂ ⌝ γ ∷ U.Level  ≡⟨ l₁⊔l₂≡ ⟩⊢∷
      ⌜ 1ᵘ+ l₁″ supᵘₗ l₂ ⌝ γ       ≡⟨ l₁′⊔l₂≡ ⟩⊢
      ⌜ 1ᵘ+ l₁″ supᵘₗ zeroᵘ ⌝ γ    ≡⟨ ⊢≡∷Level→⊢≡∷Level okᴸ $
                                      supᵘₗ-zeroʳ (term-⊢∷ ⊢l₁′) ⟩⊢∎≡
      ⌜ 1ᵘ+ l₁″ ⌝ γ                ≡⟨⟩
      ⌜ u ⌝ γ                      ∎
    … | just (1ᵘ+ l₂″) | ok! =
      let ⊢l₂″ , _ = inversion-sucᵘ ⊢l₂′

          open TmR
      in
                        ∷ ⌜ A ⌝ γ   ⟨ A≡Level ⟩≡∷
      ⌜ l₁ supᵘₗ l₂ ⌝ γ ∷ U.Level  ≡⟨ l₁⊔l₂≡ ⟩⊢∷
      ⌜ 1ᵘ+ l₁″ supᵘₗ l₂ ⌝ γ       ≡⟨ l₁′⊔l₂≡ ⟩⊢
      ⌜ 1ᵘ+ l₁″ supᵘₗ 1ᵘ+ l₂″ ⌝ γ  ≡⟨ ⊢≡∷Level→⊢≡∷Level okᴸ $
                                      supᵘₗ-1ᵘ+ (term-⊢∷ ⊢l₁″) (term-⊢∷ ⊢l₂″) ⟩⊢∎≡
      ⌜ 1ᵘ+ (l₁″ supᵘₗ l₂″) ⌝ γ    ≡⟨⟩
      ⌜ u ⌝ γ                      ∎
    red-tm′-sound (U _) ok! _ ⊢U =
      refl ⊢U
    red-tm′-sound (Lift _ _) ok! _ ⊢Lift =
      refl ⊢Lift
    red-tm′-sound (lift _ _) ok! _ ⊢lift =
      refl ⊢lift
    red-tm′-sound {A} {u} {γ} (lower t) eq ⊢γ ⊢lower
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv (_ , C , PE.refl) _ eq
      using inv _ eq₂ eq ← inv->>= eq
      with inv->>= eq
    … | inv t′ eq₃ eq
      using ⊢A               ← wf-⊢∷ ⊢lower
          | ⊢Γ               ← wf ⊢A
          | ⊢t               ← infer-red-sound eq₁ ⊢γ ⊢Γ
          | _ , ⊢C           ← inversion-Lift (wf-⊢∷ ⊢t)
          | A≡C              ← equal-ty-sound eq₂ ⊢γ ⊢A ⊢C
          | lower-t≡lower-t′ ← lower-cong (red-tm-sound eq₃ ⊢γ ⊢t)
      with is-lift? t′ | eq
    … | just (l , t″ , PE.refl) | eq =
      let inv t‴ eq₄ eq₅ = inv->>= eq
          t″≡t‴          = check-sound eq₄ ⊢γ ⊢C
          _ , ⊢t″ , ⊢t‴  = wf-⊢≡∷ t″≡t‴

          open TmR
      in
                    ∷ ⌜ A ⌝ γ   ⟨ A≡C ⟩≡∷
      ⌜ lower t ⌝ γ ∷ ⌜ C ⌝ γ  ≡⟨ lower-t≡lower-t′ ⟩⊢∷
      ⌜ lower (lift l t″) ⌝ γ  ≡⟨ Lift-β′ ⊢t″ ⟩⊢
      ⌜ t″ ⌝ γ                 ≡⟨ t″≡t‴ ⟩⊢
      ⌜ t‴ ⌝ γ                 ≡⟨ red-tm-sound eq₅ ⊢γ ⊢t‴ ⟩⊢∎
      ⌜ u ⌝ γ                  ∎
    … | nothing | ok! =
      let open TmR in
                    ∷ ⌜ A ⌝ γ   ⟨ A≡C ⟩≡∷
      ⌜ lower t ⌝ γ ∷ ⌜ C ⌝ γ  ≡⟨ lower-t≡lower-t′ ⟩⊢∷∎≡
      ⌜ lower t′ ⌝ γ           ≡⟨⟩
      ⌜ u ⌝ γ                  ∎
    red-tm′-sound Empty ok! _ ⊢Empty =
      refl ⊢Empty
    red-tm′-sound (emptyrec _ _ _) eq ⊢γ ⊢er
      with inv->>= eq
    … | inv _ eq ok! =
      let ⊢A , ⊢t , ≡A = inversion-emptyrec ⊢er in
      conv (emptyrec-cong (refl ⊢A) (red-tm-sound eq ⊢γ ⊢t)) (sym ≡A)
    red-tm′-sound (Unit _) ok! _ ⊢Unit =
      refl ⊢Unit
    red-tm′-sound (star _) ok! _ ⊢star =
      refl ⊢star
    red-tm′-sound {A} {u} {γ} (unitrec p q B t₁ t₂) eq ⊢γ ⊢ur
      with inv->>= eq
    … | inv t₁′ eq₁ eq₂
      using ⊢B , ⊢t₁ , ⊢t₂ , A≡ ← inversion-unitrec ⊢ur
          | t₁≡                 ← red-tm-sound eq₁ ⊢γ ⊢t₁
          | ur≡                 ← unitrec-cong′ (refl ⊢B) t₁≡ (refl ⊢t₂)
      with is-star-𝕨? t₁′ | eq₂
    … | just ≡star | eq₂ =
      let ≡star =
            ⌜ t₁′ ⌝ γ     ≡⟨ PE.cong (flip ⌜_⌝ _) ≡star ⟩
            ⌜ star 𝕨 ⌝ γ  ∎

          open TmR
      in
                                      ∷ ⌜ A ⌝ γ                    ⟨ A≡ ⟩≡∷
      ⌜ unitrec p q B t₁       t₂ ⌝ γ ∷ ⌜ B ⌝ γ U.[ ⌜ t₁ ⌝ γ ]₀   ≡⟨ ur≡ ⟩⊢∷
      ⌜ unitrec p q B t₁′      t₂ ⌝ γ                             ≡⟨ PE.cong (flip (U.unitrec _ _ _) _) ≡star ⟩⊢≡
                                                                   ⟨ subst-⊢≡₀ ⊢B t₁≡ ⟩≡
                                      ∷ ⌜ B ⌝ γ U.[ ⌜ t₁′ ⌝ γ ]₀   ⟨ PE.cong (⌜ B ⌝ _ U.[_]₀) ≡star ⟩≡∷≡
      ⌜ unitrec p q B (star 𝕨) t₂ ⌝ γ ∷
        ⌜ B ⌝ γ U.[ U.starʷ ]₀                                    ⇒⟨ unitrec-β-⇒ ⊢B ⊢t₂ ⟩⊢∷
      ⌜ t₂ ⌝ γ                                                    ≡⟨ red-tm-sound eq₂ ⊢γ ⊢t₂ ⟩⊢∎
      ⌜ u ⌝ γ                                                     ∎
    … | nothing | ok! =
      let open TmR in
                                 ∷ ⌜ A ⌝ γ                   ⟨ A≡ ⟩≡∷
      ⌜ unitrec p q B t₁  t₂ ⌝ γ ∷ ⌜ B ⌝ γ U.[ ⌜ t₁ ⌝ γ ]₀  ≡⟨ ur≡ ⟩⊢∷∎≡
      ⌜ unitrec p q B t₁′ t₂ ⌝ γ                            ≡⟨⟩
      ⌜ u ⌝ γ                                               ∎
    red-tm′-sound (ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _) ok! _ ⊢ΠΣ =
      refl ⊢ΠΣ
    red-tm′-sound (lam _ _ _) ok! _ ⊢lam =
      refl ⊢lam
    red-tm′-sound {A} {u} {γ} (t₁ ∘⟨ p ⟩ t₂) eq ⊢γ ⊢app
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv (_ , _ , B₂ , PE.refl) _ eq
      with inv->>= eq
    … | inv t₂′ eq₂ eq
      using inv _ eq₃ eq ← inv->>= eq
      with inv->>= eq
    … | inv t₁′ eq₄ eq
      using ⊢A               ← wf-⊢∷ ⊢app
          | ⊢t₁              ← infer-red-sound eq₁ ⊢γ (wf ⊢A)
          | ⊢B₁ , ⊢B₂ , Π-ok ← inversion-ΠΣ (wf-⊢∷ ⊢t₁)
          | t₂≡t₂′           ← check-sound eq₂ ⊢γ ⊢B₁
          | _ , ⊢t₂ , ⊢t₂′   ← wf-⊢≡∷ t₂≡t₂′
          | A≡B₂[t₂′]        ← equal-ty-sound eq₃ ⊢γ ⊢A
                                 (subst-⊢₀ ⊢B₂ ⊢t₂′)
          | t₁≡t₁′           ← red-tm-sound eq₄ ⊢γ ⊢t₁
          | t₁′∘t₂′≡t₁∘t₂    ← app-cong (sym′ t₁≡t₁′) (sym′ t₂≡t₂′)
      with is-lam⟨ p ⟩? t₁′ | eq
    … | just (qB₁ , t₁″ , ≡lam) | eq =
      let inv t₁‴ eq₅ eq₆ = inv->>= eq
          t₁″≡t₁‴         = check-sound eq₅ ⊢γ ⊢B₂
          _ , ⊢t₁″ , ⊢t₁‴ = wf-⊢≡∷ t₁″≡t₁‴
          ≡t₁‴[t₂′]       =
            PE.sym (⌜[]⌝ t₁‴ (term₂ (subst-⊢₀ ⊢t₁‴ ⊢t₂′)))

          open TmR
      in
                                     ∷ ⌜ A ⌝ γ                     ⟨ A≡B₂[t₂′] ⟩≡∷
      ⌜ t₁            ∘⟨ p ⟩ t₂  ⌝ γ ∷ ⌜ B₂ ⌝ γ U.[ ⌜ t₂′ ⌝ γ ]₀  ≡˘⟨ t₁′∘t₂′≡t₁∘t₂ ⟩⊢∷
      ⌜ t₁′           ∘⟨ p ⟩ t₂′ ⌝ γ                              ≡⟨ PE.cong (U._∘⟨ _ ⟩ _ ∘→ flip ⌜_⌝ _) ≡lam ⟩⊢≡
      ⌜ lam p qB₁ t₁″ ∘⟨ p ⟩ t₂′ ⌝ γ                              ⇒⟨ β-red-⇒ ⊢t₁″ ⊢t₂′ Π-ok ⟩⊢
      ⌜ t₁″ ⌝ γ U.[ ⌜ t₂′ ⌝ γ ]₀                                  ≡⟨ subst-⊢≡₀ t₁″≡t₁‴ (refl ⊢t₂′) ⟩⊢
      ⌜ t₁‴ ⌝ γ U.[ ⌜ t₂′ ⌝ γ ]₀                                  ≡⟨ ≡t₁‴[t₂′] ⟩⊢≡
      ⌜ t₁‴ [ sgSubst t₂′ ] ⌝ γ                                   ≡⟨ red-tm-sound eq₆ ⊢γ $
                                                                     PE.subst (flip (_⊢_∷_ _) _) ≡t₁‴[t₂′] $
                                                                     subst-⊢₀ ⊢t₁‴ ⊢t₂′ ⟩⊢∎
      ⌜ u ⌝ γ                                                     ∎
    … | nothing | ok! =
      let open TmR in
                           ∷ ⌜ A  ⌝ γ                    ⟨ A≡B₂[t₂′] ⟩≡∷
      ⌜ t₁  ∘⟨ p ⟩ t₂  ⌝ γ ∷ ⌜ B₂ ⌝ γ U.[ ⌜ t₂′ ⌝ γ ]₀  ≡˘⟨ t₁′∘t₂′≡t₁∘t₂ ⟩⊢∷∎≡
      ⌜ t₁′ ∘⟨ p ⟩ t₂′ ⌝ γ                              ≡⟨⟩
      ⌜ u ⌝ γ                                           ∎
    red-tm′-sound (prod _ _ _ _ _) ok! _ ⊢prod =
      refl ⊢prod
    red-tm′-sound {A} {u} {γ} (fst p t) eq ⊢γ ⊢fst
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv (_ , B₁ , _ , PE.refl) _ eq
      using inv _ eq₂ eq ← inv->>= eq
      with inv->>= eq
    … | inv t′ eq₃ eq
      using ⊢A               ← wf-⊢∷ ⊢fst
          | ⊢t               ← infer-red-sound eq₁ ⊢γ (wf ⊢A)
          | ⊢B₁ , ⊢B₂ , Σ-ok ← inversion-ΠΣ (wf-⊢∷ ⊢t)
          | A≡B₁             ← equal-ty-sound eq₂ ⊢γ ⊢A ⊢B₁
          | t≡t′             ← red-tm-sound eq₃ ⊢γ ⊢t
      with is-prod⟨ 𝕤 , p ⟩? t′ | eq
    … | just (qB₂ , t₁ , t₂ , ≡prod) | eq =
      let inv t₁′ eq₄ eq  = inv->>= eq
          inv _   eq₅ eq₆ = inv->>= eq
          t₁≡t₁′          = check-sound eq₄ ⊢γ ⊢B₁
          _ , ⊢t₁ , ⊢t₁′  = wf-⊢≡∷ t₁≡t₁′
          _ , ⊢t₂ , _     = wf-⊢≡∷ $
                            check-sound eq₅ ⊢γ (subst-⊢₀ ⊢B₂ ⊢t₁′)

          open TmR
      in
                                       ∷ ⌜ A ⌝ γ    ⟨ A≡B₁ ⟩≡∷
      ⌜ fst p t                    ⌝ γ ∷ ⌜ B₁ ⌝ γ  ≡⟨ fst-cong′ t≡t′ ⟩⊢∷
      ⌜ fst p t′                   ⌝ γ             ≡⟨ PE.cong (U.fst _ ∘→ flip ⌜_⌝ _) ≡prod ⟩⊢≡
      ⌜ fst p (prod 𝕤 p qB₂ t₁ t₂) ⌝ γ             ≡⟨ Σ-β₁-≡ ⊢B₂ ⊢t₁ (conv ⊢t₂ (subst-⊢≡₀ ⊢B₂ (sym′ t₁≡t₁′))) Σ-ok ⟩⊢
      ⌜ t₁ ⌝ γ                                     ≡⟨ t₁≡t₁′ ⟩⊢
      ⌜ t₁′ ⌝ γ                                    ≡⟨ red-tm-sound eq₆ ⊢γ ⊢t₁′ ⟩⊢∎
      ⌜ u  ⌝ γ                                     ∎
    … | nothing | ok! =
      let open TmR in
                     ∷ ⌜ A ⌝ γ    ⟨ A≡B₁ ⟩≡∷
      ⌜ fst p t  ⌝ γ ∷ ⌜ B₁ ⌝ γ  ≡⟨ fst-cong′ t≡t′ ⟩⊢∷∎≡
      ⌜ fst p t′ ⌝ γ             ≡⟨⟩
      ⌜ u ⌝ γ                    ∎
    red-tm′-sound {A} {u} {γ} (snd p t) eq ⊢γ ⊢fst
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv (_ , _ , B₂ , PE.refl) _ eq
      using inv _ eq₂ eq ← inv->>= eq
      with inv->>= eq
    … | inv t′ eq₃ eq
      using ⊢A               ← wf-⊢∷ ⊢fst
          | ⊢t               ← infer-red-sound eq₁ ⊢γ (wf ⊢A)
          | ⊢B₁ , ⊢B₂ , Σ-ok ← inversion-ΠΣ (wf-⊢∷ ⊢t)
          | A≡B₂[fst-t]      ← equal-ty-sound eq₂ ⊢γ ⊢A
                                 (subst-⊢₀ ⊢B₂ (fstⱼ′ ⊢t))
          | t≡t′             ← red-tm-sound eq₃ ⊢γ ⊢t
      with is-prod⟨ 𝕤 , p ⟩? t′ | eq
    … | just (qB₂ , t₁ , t₂ , ≡prod) | eq =
      let inv t₁′ eq₄ eq  = inv->>= eq
          inv t₂′ eq₅ eq₆ = inv->>= eq
          t₁≡t₁′          = check-sound eq₄ ⊢γ ⊢B₁
          _ , ⊢t₁ , ⊢t₁′  = wf-⊢≡∷ t₁≡t₁′
          t₂≡t₂′          = check-sound eq₅ ⊢γ (subst-⊢₀ ⊢B₂ ⊢t₁′)
          _ , ⊢t₂ , ⊢t₂′  = wf-⊢≡∷ t₂≡t₂′
          ⊢t₂             = conv ⊢t₂ (subst-⊢≡₀ ⊢B₂ (sym′ t₁≡t₁′))

          open TmR
      in
                                       ∷ ⌜ A ⌝ γ                          ⟨ A≡B₂[fst-t] ⟩≡∷
      ⌜ snd p t                    ⌝ γ ∷ ⌜ B₂ ⌝ γ U.[ ⌜ fst p t ⌝ γ ]₀   ≡⟨ snd-cong′ t≡t′ ⟩⊢∷
                                                                          ⟨ subst-⊢≡₀ ⊢B₂ (fst-cong′ t≡t′) ⟩≡
      ⌜ snd p t′                   ⌝ γ ∷ ⌜ B₂ ⌝ γ U.[ ⌜ fst p t′ ⌝ γ ]₀  ≡⟨ PE.cong (U.snd _ ∘→ flip ⌜_⌝ _) ≡prod ⟩⊢∷≡
                                                                          ⟨ PE.cong (⌜ B₂ ⌝ γ U.[_]₀ ∘→ flip ⌜_⌝ _ ∘→ fst p) ≡prod ⟩≡≡
                     ∷ ⌜ B₂ ⌝ γ U.[ ⌜ fst p (prod 𝕤 p qB₂ t₁ t₂) ⌝ γ ]₀   ⟨ subst-⊢≡₀ ⊢B₂ (Σ-β₁-≡ ⊢B₂ ⊢t₁ ⊢t₂ Σ-ok) ⟩≡∷

      ⌜ snd p (prod 𝕤 p qB₂ t₁ t₂) ⌝ γ ∷ ⌜ B₂ ⌝ γ U.[ ⌜ t₁  ⌝ γ ]₀       ≡⟨ Σ-β₂-≡ ⊢B₂ ⊢t₁ ⊢t₂ Σ-ok ⟩⊢∷
                                                                          ⟨ subst-⊢≡₀ ⊢B₂ t₁≡t₁′ ⟩≡
      ⌜ t₂ ⌝ γ                         ∷ ⌜ B₂ ⌝ γ U.[ ⌜ t₁′ ⌝ γ ]₀       ≡⟨ t₂≡t₂′ ⟩⊢∷
      ⌜ t₂′ ⌝ γ                                                          ≡⟨ red-tm-sound eq₆ ⊢γ ⊢t₂′ ⟩⊢∎
      ⌜ u  ⌝ γ                                                           ∎
    … | nothing | ok! =
      let open TmR in
                     ∷ ⌜ A ⌝ γ                         ⟨ A≡B₂[fst-t] ⟩≡∷
      ⌜ snd p t  ⌝ γ ∷ ⌜ B₂ ⌝ γ U.[ ⌜ fst p t ⌝ γ ]₀  ≡⟨ snd-cong′ t≡t′ ⟩⊢∷∎≡
      ⌜ snd p t′ ⌝ γ                                  ≡⟨⟩
      ⌜ u ⌝ γ                                         ∎
    red-tm′-sound {A} {u} {γ} (prodrec r p q B t₁ t₂) eq ⊢γ ⊢pr
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv (_ , _ , _ , PE.refl) _ eq
      with inv->>= eq
    … | inv B′ eq₂ eq
      with inv->>= eq
    … | inv t₁′ eq₃ eq
      using inv _ eq₄ eq ← inv->>= eq
      with inv->>= eq
    … | inv t₂′ eq₅ eq
      using ⊢t₁              ← infer-red-sound eq₁ ⊢γ (wf ⊢pr)
          | ⊢Σ               ← wf-⊢∷ ⊢t₁
          | ⊢C₁ , ⊢C₂ , Σ-ok ← inversion-ΠΣ ⊢Σ
          | B≡B′             ← check-type-sound eq₂ ⊢γ (∙ ⊢Σ)
          | _ , ⊢B′          ← wf-⊢≡ B≡B′
          | t₁≡t₁′           ← red-tm-sound eq₃ ⊢γ ⊢t₁
          | _ , _ , ⊢t₁′     ← wf-⊢≡∷ t₁≡t₁′
          | A≡B′[t₁′]        ← equal-ty-sound eq₄ ⊢γ (wf-⊢∷ ⊢pr)
                                 (subst-⊢₀ ⊢B′ ⊢t₁′)
          | t₂≡t₂′           ← check-sound eq₅ ⊢γ
                                 (subst-⊢-↑ ⊢B′ (⊢1,0 ⊢Σ))
          | _ , _ , ⊢t₂′     ← wf-⊢≡∷ t₂≡t₂′
          | pr≡pr            ← prodrec-cong′ (sym B≡B′) (sym′ t₁≡t₁′)
                                 (sym′ t₂≡t₂′)
      with is-prod⟨ 𝕨 , p ⟩? t₁′ | eq
    … | just (qC , t₁₁ , t₁₂ , ≡prod) | eq =
      let inv t₁₁′ eq₆ eq  = inv->>= eq
          inv t₁₂′ eq₇ eq₈ = inv->>= eq
          t₁₁≡t₁₁′         = check-sound eq₆ ⊢γ ⊢C₁
          _ , ⊢t₁₁ , ⊢t₁₁′ = wf-⊢≡∷ t₁₁≡t₁₁′
          t₁₂≡t₁₂′         = check-sound eq₇ ⊢γ (subst-⊢₀ ⊢C₂ ⊢t₁₁′)
          _ , _ , ⊢t₁₂′    = wf-⊢≡∷ t₁₂≡t₁₂′
          t₁₂≡t₁₂′         = conv t₁₂≡t₁₂′
                               (subst-⊢≡₀ ⊢C₂ (sym′ t₁₁≡t₁₁′))
          _ , ⊢t₁₂ , _     = wf-⊢≡∷ t₁₂≡t₁₂′

          open TmR
      in
                                     ∷ ⌜ A ⌝ γ                      ⟨ A≡B′[t₁′] ⟩≡∷
      ⌜ prodrec r p q B  t₁  t₂  ⌝ γ ∷ ⌜ B′ ⌝ γ U.[ ⌜ t₁′ ⌝ γ ]₀  ≡˘⟨ pr≡pr ⟩⊢∷
      ⌜ prodrec r p q B′ t₁′ t₂′ ⌝ γ                              ≡⟨ PE.cong (flip (U.prodrec _ _ _ _) _ ∘→ flip ⌜_⌝ _) ≡prod ⟩⊢≡
                                                                   ⟨ PE.cong (⌜ B′ ⌝ _ U.[_]₀ ∘→ flip ⌜_⌝ _) ≡prod ⟩≡≡
      ⌜ prodrec r p q B′ (prod 𝕨 p qC t₁₁ t₁₂) t₂′ ⌝ γ ∷
        ⌜ B′ ⌝ γ U.[ ⌜ prod 𝕨 p qC t₁₁ t₁₂ ⌝ γ ]₀                 ⇒⟨ prodrec-β-⇒ ⊢B′ ⊢t₁₁ ⊢t₁₂ ⊢t₂′ ⟩⊢∷
      ⌜ subst t₂′ (cons (sgSubst t₁₁) t₁₂) ⌝ γ                    ≡⟨ PE.subst (_⊢_≡_∷_ _ _ _) ([1,0]↑²[,] (⌜ B′ ⌝ _)) $
                                                                     subst-⊢≡₁₀ ⊢t₂′ t₁₁≡t₁₁′ t₁₂≡t₁₂′ ⟩⊢
                                                                   ⟨ subst-⊢≡₀ ⊢B′ (prod-cong ⊢C₂ t₁₁≡t₁₁′ t₁₂≡t₁₂′ Σ-ok) ⟩≡
      ⌜ subst t₂′ (cons (sgSubst t₁₁′) t₁₂′) ⌝ γ ∷
        ⌜ B′ ⌝ γ U.[ ⌜ prod 𝕨 p qC t₁₁′ t₁₂′ ⌝ γ ]₀               ≡⟨ red-tm-sound eq₈ ⊢γ $
                                                                     PE.subst (_⊢_∷_ _ _) ([1,0]↑²[,] (⌜ B′ ⌝ _)) $
                                                                     subst-⊢₁₀ ⊢t₂′ ⊢t₁₁′ ⊢t₁₂′ ⟩⊢∷∎
      ⌜ u ⌝ γ                                                     ∎
    … | nothing | ok! =
      let open TmR in
                                      ∷ ⌜ A ⌝ γ                      ⟨ A≡B′[t₁′] ⟩≡∷
      ⌜ prodrec r p q B  t₁  t₂  ⌝ γ  ∷ ⌜ B′ ⌝ γ U.[ ⌜ t₁′ ⌝ γ ]₀  ≡˘⟨ pr≡pr ⟩⊢∷∎≡
      ⌜ prodrec r p q B′ t₁′ t₂′ ⌝ γ                               ≡⟨⟩
      ⌜ u ⌝ γ                                                      ∎
    red-tm′-sound ℕ ok! _ ⊢ℕ =
      refl ⊢ℕ
    red-tm′-sound zero ok! _ ⊢zero =
      refl ⊢zero
    red-tm′-sound (suc _) ok! _ ⊢suc =
      refl ⊢suc
    red-tm′-sound {A} {u} {γ} (natrec p q r B t₁ t₂ t₃) eq ⊢γ ⊢nr
      with inv->>= eq
    … | inv t₃′ eq₁ eq
      using ⊢B , ⊢t₁ , ⊢t₂ , ⊢t₃ , A≡ ← inversion-natrec ⊢nr
          | t₃≡t₃′                    ← red-tm-sound eq₁ ⊢γ ⊢t₃
      with is-zero-or-suc? t₃′ | eq
    … | just (inj₁ ≡zero) | eq₂ =
      let open TmR

          t₃≡0 =
            ⌜ t₃   ⌝ γ  ≡⟨ t₃≡t₃′ ⟩⊢∎≡
            ⌜ t₃′  ⌝ γ  ≡⟨ PE.cong (flip ⌜_⌝ _) ≡zero ⟩
            U.zero      ∎
      in
                                      ∷ ⌜ A ⌝ γ                   ⟨ A≡ ⟩≡∷
      ⌜ natrec p q r B t₁ t₂ t₃   ⌝ γ ∷ ⌜ B ⌝ γ U.[ ⌜ t₃ ⌝ γ ]₀  ≡⟨ natrec-cong (refl ⊢B) (refl ⊢t₁) (refl ⊢t₂) t₃≡0 ⟩⊢∷
                                                                  ⟨ subst-⊢≡₀ ⊢B t₃≡0 ⟩≡
      ⌜ natrec p q r B t₁ t₂ zero ⌝ γ ∷ ⌜ B ⌝ γ U.[ U.zero ]₀    ⇒⟨ natrec-zero ⊢t₁ ⊢t₂ ⟩⊢∷
      ⌜ t₁ ⌝ γ                                                   ≡⟨ red-tm-sound eq₂ ⊢γ ⊢t₁ ⟩⊢∎
      ⌜ u ⌝ γ                                                    ∎
    … | just (inj₂ (t₃″ , ≡suc)) | eq₂ =
      let open TmR

          t₃≡suc =
            ⌜ t₃      ⌝ γ  ≡⟨ t₃≡t₃′ ⟩⊢∎≡
            ⌜ t₃′     ⌝ γ  ≡⟨ PE.cong (flip ⌜_⌝ _) ≡suc ⟩
            ⌜ suc t₃″ ⌝ γ  ∎
          ⊢t₃″ , _ =
            inversion-suc (wf-⊢≡∷ t₃≡suc .proj₂ .proj₂)
      in
                                           ∷ ⌜ A ⌝ γ                   ⟨ A≡ ⟩≡∷
      ⌜ natrec p q r B t₁ t₂ t₃        ⌝ γ ∷ ⌜ B ⌝ γ U.[ ⌜ t₃ ⌝ γ ]₀  ≡⟨ natrec-cong (refl ⊢B) (refl ⊢t₁) (refl ⊢t₂) t₃≡suc ⟩⊢∷
                                                                       ⟨ subst-⊢≡₀ ⊢B t₃≡suc ⟩≡
      ⌜ natrec p q r B t₁ t₂ (suc t₃″) ⌝ γ ∷
        ⌜ B ⌝ γ U.[ ⌜ suc t₃″ ⌝ γ ]₀                                  ⇒⟨ natrec-suc ⊢t₁ ⊢t₂ ⊢t₃″ ⟩⊢∷
      ⌜ subst t₂ (cons (sgSubst t₃″) (natrec p q r B t₁ t₂ t₃″)) ⌝ γ  ≡⟨ red-tm-sound eq₂ ⊢γ $
                                                                         PE.subst (_⊢_∷_ _ _) (PE.sym $ substComp↑² (⌜ B ⌝ _) _) $
                                                                         subst-⊢₁₀ ⊢t₂ ⊢t₃″ (natrecⱼ ⊢t₁ ⊢t₂ ⊢t₃″) ⟩⊢∎
      ⌜ u ⌝ γ                                                         ∎
    … | nothing | ok! =
      let open TmR in
                                     ∷ ⌜ A ⌝ γ                    ⟨ A≡ ⟩≡∷
      ⌜ natrec p q r B t₁ t₂ t₃  ⌝ γ ∷ ⌜ B ⌝ γ U.[ ⌜ t₃  ⌝ γ ]₀  ≡⟨ natrec-cong (refl ⊢B) (refl ⊢t₁) (refl ⊢t₂) t₃≡t₃′ ⟩⊢∷∎≡
      ⌜ natrec p q r B t₁ t₂ t₃′ ⌝ γ                             ≡⟨⟩
      ⌜ u ⌝ γ                                                    ∎
    red-tm′-sound (Id _ _ _) ok! _ ⊢Id =
      refl ⊢Id
    red-tm′-sound (rfl _) ok! _ ⊢rfl =
      refl ⊢rfl
    red-tm′-sound {A} {u} {γ} (J p q B₁ t₁ B₂ t₂ t₃ t₄) eq ⊢γ ⊢J
      with inv->>= eq
    … | inv t₄′ eq₁ eq
      using ⊢B₁ , ⊢t₁ , ⊢B₂ , ⊢t₂ , ⊢t₃ , ⊢t₄ , A≡ ←
              inversion-J ⊢J
          | t₄≡t₄′ ←
              red-tm-sound eq₁ ⊢γ ⊢t₄
      with is-rfl? t₄′ | eq
    … | just (t₁? , ≡rfl) | eq =
      let open TmR

          inv _ eq₂ eq₃ = inv->>= eq
          t₁≡t₃         = equal-tm-sound eq₂ ⊢γ ⊢t₁ ⊢t₃
          t₄≡rfl        =
            ⌜ t₄  ⌝ γ  ≡⟨ t₄≡t₄′ ⟩⊢∎≡
            ⌜ t₄′ ⌝ γ  ≡⟨ PE.cong (flip ⌜_⌝ _) ≡rfl ⟩
            U.rfl      ∎
      in
                                    ∷ ⌜ A ⌝ γ   ⟨ A≡ ⟩≡∷
      ⌜ J p q B₁ t₁ B₂ t₂ t₃ t₄ ⌝ γ ∷
        ⌜ B₂ ⌝ γ U.[ ⌜ t₃ ⌝ γ , ⌜ t₄ ⌝ γ ]₁₀   ≡⟨ J-cong′ (refl ⊢B₁) (refl ⊢t₁) (refl ⊢B₂) (refl ⊢t₂) (refl ⊢t₃) t₄≡rfl ⟩⊢∷
                                                ⟨ subst-⊢≡₁₀ ⊢B₂ (sym′ t₁≡t₃) (PE.subst (_⊢_≡_∷_ _ _ _) ≡Id-wk1-wk1-0[]₀ t₄≡rfl) ⟩≡
      ⌜ J p q B₁ t₁ B₂ t₂ t₃ (rfl t₁?) ⌝ γ ∷
        ⌜ B₂ ⌝ γ U.[ ⌜ t₁ ⌝ γ , U.rfl ]₁₀      ⇒⟨ J-β-⇒ t₁≡t₃ ⊢B₂ ⊢t₂ ⟩⊢∷
      ⌜ t₂ ⌝ γ                                 ≡⟨ red-tm-sound eq₃ ⊢γ ⊢t₂ ⟩⊢∎
      ⌜ u ⌝ γ                                  ∎
    … | nothing | ok! =
      let open TmR in
                                    ∷ ⌜ A ⌝ γ   ⟨ A≡ ⟩≡∷
      ⌜ J p q B₁ t₁ B₂ t₂ t₃ t₄ ⌝ γ ∷
        ⌜ B₂ ⌝ γ U.[ ⌜ t₃ ⌝ γ , ⌜ t₄ ⌝ γ ]₁₀   ≡⟨ J-cong′ (refl ⊢B₁) (refl ⊢t₁) (refl ⊢B₂) (refl ⊢t₂) (refl ⊢t₃) t₄≡t₄′ ⟩⊢∷∎≡
      ⌜ J p q B₁ t₁ B₂ t₂ t₃ t₄′ ⌝ γ           ≡⟨⟩
      ⌜ u ⌝ γ                                  ∎
    red-tm′-sound {A} {u} {γ} (K p B₁ t₁ B₂ t₂ t₃) eq ⊢γ ⊢K
      with inv->>= eq
    … | inv t₃′ eq₁ eq₂
      using ⊢B₁ , ⊢t₁ , ⊢B₂ , ⊢t₂ , ⊢t₃ , K-ok , A≡ ←
              inversion-K ⊢K
          | t₃≡t₃′ ←
              red-tm-sound eq₁ ⊢γ ⊢t₃
      with is-rfl? t₃′ | eq₂
    … | just (t₁? , eq₃) | eq₂ =
      let open TmR

          t₃≡rfl =
            ⌜ t₃  ⌝ γ  ≡⟨ t₃≡t₃′ ⟩⊢∎≡
            ⌜ t₃′ ⌝ γ  ≡⟨ PE.cong (flip ⌜_⌝ _) eq₃ ⟩
            U.rfl      ∎
      in
                                      ∷ ⌜ A ⌝ γ                    ⟨ A≡ ⟩≡∷
      ⌜ K p B₁ t₁ B₂ t₂ t₃        ⌝ γ ∷ ⌜ B₂ ⌝ γ U.[ ⌜ t₃ ⌝ γ ]₀  ≡⟨ K-cong (refl ⊢B₁) (refl ⊢t₁) (refl ⊢B₂) (refl ⊢t₂) t₃≡rfl K-ok ⟩⊢∷
                                                                   ⟨ subst-⊢≡₀ ⊢B₂ t₃≡rfl ⟩≡
      ⌜ K p B₁ t₁ B₂ t₂ (rfl t₁?) ⌝ γ ∷ ⌜ B₂ ⌝ γ U.[ U.rfl ]₀     ⇒⟨ K-β ⊢B₂ ⊢t₂ K-ok ⟩⊢∷
      ⌜ t₂ ⌝ γ                                                    ≡⟨ red-tm-sound eq₂ ⊢γ ⊢t₂ ⟩⊢∎
      ⌜ u ⌝ γ                                                     ∎
    … | nothing | ok! =
      let open TmR in
                                ∷ ⌜ A ⌝ γ                    ⟨ A≡ ⟩≡∷
      ⌜ K p B₁ t₁ B₂ t₂ t₃  ⌝ γ ∷ ⌜ B₂ ⌝ γ U.[ ⌜ t₃ ⌝ γ ]₀  ≡⟨ K-cong (refl ⊢B₁) (refl ⊢t₁) (refl ⊢B₂) (refl ⊢t₂) t₃≡t₃′ K-ok ⟩⊢∷∎≡
      ⌜ K p B₁ t₁ B₂ t₂ t₃′ ⌝ γ                             ≡⟨⟩
      ⌜ u ⌝ γ                                               ∎
    red-tm′-sound {A} {u} {γ} ([]-cong s l B t₁ t₂ t₃) eq ⊢γ ⊢bc
      with inv->>= eq
    … | inv t₃′ eq₁ eq
      using ⊢l , ⊢B , ⊢t₁ , ⊢t₂ , ⊢t₃ , okᵇᶜ , A≡ ←
              inversion-[]-cong ⊢bc
          | t₃≡t₃′ ←
              red-tm-sound eq₁ ⊢γ ⊢t₃
      with is-rfl? t₃′ | eq
    … | nothing | ok! =
      let open TmR
          module E = Erased (⟦ s ⟧ˢ γ)
      in
                                   ∷ ⌜ A ⌝ γ                 ⟨ A≡ ⟩≡∷
      ⌜ []-cong s l B t₁ t₂ t₃ ⌝ γ ∷
        U.Id (E.Erased (⌜ l ⌝ γ) (⌜ B ⌝ γ)) E.[ ⌜ t₁ ⌝ γ ]
          E.[ ⌜ t₂ ⌝ γ ]                                    ≡⟨ []-cong-cong (refl-⊢≡∷L ⊢l) (refl ⊢B) (refl ⊢t₁) (refl ⊢t₂) t₃≡t₃′ okᵇᶜ ⟩⊢∷∎≡
      ⌜ []-cong s l B t₁ t₂ t₃′ ⌝ γ                         ≡⟨⟩
      ⌜ u ⌝ γ                                               ∎
    … | just (t₁? , ≡rfl) | eq
      with inv->>= eq
    … | inv _ eq₂ ok! =
      let open TmR
          module E = Erased (⟦ s ⟧ˢ γ)

          t₁≡t₂  = equal-tm-sound eq₂ ⊢γ ⊢t₁ ⊢t₂
          t₃≡rfl =
            ⌜ t₃  ⌝ γ  ≡⟨ t₃≡t₃′ ⟩⊢∎≡
            ⌜ t₃′ ⌝ γ  ≡⟨ PE.cong (flip ⌜_⌝ _) ≡rfl ⟩
            U.rfl      ∎
      in
                                   ∷ ⌜ A ⌝ γ                 ⟨ A≡ ⟩≡∷
      ⌜ []-cong s l B t₁ t₂ t₃ ⌝ γ ∷
        U.Id (E.Erased (⌜ l ⌝ γ) (⌜ B ⌝ γ)) E.[ ⌜ t₁ ⌝ γ ]
          E.[ ⌜ t₂ ⌝ γ ]                                    ≡⟨ []-cong-cong (refl-⊢≡∷L ⊢l) (refl ⊢B) (refl ⊢t₁) (refl ⊢t₂) t₃≡rfl okᵇᶜ ⟩⊢∷
      ⌜ []-cong s l B t₁ t₂ (rfl t₁?) ⌝ γ                   ≡⟨ subsetTerm ([]-cong-β ⊢l t₁≡t₂ okᵇᶜ) ⟩⊢∎≡
      U.rfl                                                 ≡⟨⟩
      ⌜ u ⌝ γ                                               ∎

  -- Soundness for check-type′.

  check-type′-sound :
    (A-c : Maybe (Is-type-constructor A)) →
    OK (check-type′ n Γ A-c) A′ γ st →
    Contexts-wf (Γ .defs) γ →
    ⊢ ⌜ Γ ⌝ᶜ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A ⌝ γ ≡ ⌜ A′ ⌝ γ
  check-type′-sound {γ} (just (meta-var x σ)) eq ⊢γ ⊢Γ
    using inv _ eq₁ eq ← inv->>= eq
    with inv->>= eq
  … | inv σ′ eq₂ ok!
    rewrite ⌜meta-var⌝ {γ = γ} {x = x} σ
          | ⌜meta-var⌝ {γ = γ} {x = x} σ′ =
    let _ , ⊢x = is-type-sound eq₁ ⊢γ
        σ≡σ′   = check-sub-sound σ eq₂ ⊢γ ⊢Γ (wf ⊢x)
    in
    subst-⊢≡ (refl ⊢x) σ≡σ′
  check-type′-sound (just Level) eq ⊢γ ⊢Γ
    with inv->>= eq
  … | inv _ eq₁ ok! =
    let L.lift okᴸ = inv-require⁰ ⊢γ level-allowed eq₁ in
    refl (Levelⱼ′ okᴸ ⊢Γ)
  check-type′-sound (just (U _)) eq ⊢γ ⊢Γ
    with inv->>= eq
  … | inv _ eq₁ ok! =
    U-cong-⊢≡ (check-level-sound eq₁ ⊢γ ⊢Γ)
  check-type′-sound (just (Lift _ _)) eq ⊢γ ⊢Γ
    with inv->>= eq
  … | inv _ eq₁ eq
    with inv->>= eq
  … | inv _ eq₂ ok! =
    Lift-cong (check-level-sound eq₁ ⊢γ ⊢Γ)
      (check-type-sound eq₂ ⊢γ ⊢Γ)
  check-type′-sound (just Empty) ok! _ ⊢Γ =
    refl (⊢Empty ⊢Γ)
  check-type′-sound (just (Unit _)) eq ⊢γ ⊢Γ
    with inv->>= eq
  … | inv _ eq₁ ok! =
    let Unit-ok = inv-require⁺ ⊢γ eq₁ in
    refl (⊢Unit ⊢Γ Unit-ok)
  check-type′-sound (just (ΠΣ _ _ _ _ _)) eq ⊢γ ⊢Γ
    with inv->>= eq
  … | inv _ eq₁ eq
    with inv->>= eq
  … | inv _ eq₂ eq
    with inv->>= eq
  … | inv _ eq₃ ok! =
    let A₁≡A₁′   = check-type-sound eq₁ ⊢γ ⊢Γ
        _ , ⊢A₁′ = wf-⊢≡ A₁≡A₁′
        A₂≡A₂′   = check-type-sound eq₂ ⊢γ (∙ ⊢A₁′)
        ΠΣ-ok    = inv-require⁺ ⊢γ eq₃
    in
    sym (ΠΣ-cong (sym A₁≡A₁′) (sym A₂≡A₂′) ΠΣ-ok)
  check-type′-sound (just ℕ) ok! _ ⊢Γ =
    refl (⊢ℕ ⊢Γ)
  check-type′-sound (just (Id _ _ _)) eq ⊢γ ⊢Γ
    with inv->>= eq
  … | inv _ eq₁ eq
    with inv->>= eq
  … | inv _ eq₂ eq
    with inv->>= eq
  … | inv _ eq₃ ok! =
    let A≡A′    = check-type-sound eq₁ ⊢γ ⊢Γ
        _ , ⊢A′ = wf-⊢≡ A≡A′
        t₁≡t₁′  = check-sound eq₂ ⊢γ ⊢A′
        t₂≡t₂′  = check-sound eq₃ ⊢γ ⊢A′
    in
    sym (Id-cong (sym A≡A′) (sym′ t₁≡t₁′) (sym′ t₂≡t₂′))
  check-type′-sound nothing eq ⊢γ ⊢Γ
    with inv->>= eq
  … | inv _ eq₁ eq
    with inv->>= eq
  … | inv (_ , PE.refl) _ ok! =
    refl (univ (infer-red-sound eq₁ ⊢γ ⊢Γ))

  opaque
    unfolding S._supᵘₗ_

    -- Soundness for check-level′.

    check-level′-sound :
      {l l′ l″ : Term[ c , k ] _} →
      (Remove-weaken-subst-assumption b γ l l′ →
       ⌜ l′ ⌝ γ PE.≡ ⌜ l ⌝ γ) →
      (l′-l : Maybe (Is-perhaps-level l′)) →
      OK (check-level′ n Γ l′-l b) l″ γ st →
      Contexts-wf (Γ .defs) γ →
      ⊢ ⌜ Γ ⌝ᶜ γ →
      ⌜ Γ ⌝ᶜ γ ⊢ ⌜ Term[]→Lvl l ⌝ γ ≡ ⌜ Term[]→Lvl l″ ⌝ γ ∷Level
    check-level′-sound l′≡l (just (meta-var _ _)) eq ⊢γ ⊢Γ
      with inv-<$> eq
    … | inv _ eq₁ PE.refl =
      let _ , _ , _ , l′≡l″ = is-level-sound eq₁ ⊢γ ⊢Γ in
      PE.subst (flip (_⊢_≡_∷Level _) _)
        (Term[]→Lvl-cong (l′≡l (not-supᵘₗ (λ { (_ , _ , ()) } ))))
        l′≡l″
    check-level′-sound l′≡l (just zeroᵘ) ok! _ ⊢Γ =
      PE.subst (flip (_⊢_≡_∷Level _) _)
        (PE.cong U.level (l′≡l (not-supᵘₗ (λ { (_ , _ , ()) } )))) $
      refl-⊢≡∷L (⊢zeroᵘ ⊢Γ)
    check-level′-sound {γ} {l} l′≡l (just (1ᵘ+ l′)) eq ⊢γ ⊢Γ
      with inv-<$> eq
    … | inv l″ eq₁ PE.refl =
      let l′≡ = 1ᵘ+-cong (check-level-sound eq₁ ⊢γ ⊢Γ) in
      PE.subst₂ (_⊢_≡_∷Level _)
        (U.1ᵘ+ (⌜ Term[]→Lvl l′ ⌝ γ)  ≡⟨ 1ᵘ+-⌜Term[]→Lvl⌝ l′ ⟩
         ⌜ Term[]→Lvl (1ᵘ+ l′) ⌝ γ    ≡⟨ Term[]→Lvl-cong (l′≡l (not-supᵘₗ (λ { (_ , _ , ()) } ))) ⟩
         ⌜ Term[]→Lvl l ⌝ γ           ∎)
        (1ᵘ+-⌜Term[]→Lvl⌝ l″)
        l′≡
    check-level′-sound {b} {γ} {l} l′≡l (just (l′₁ supᵘₗ l′₂)) eq ⊢γ ⊢Γ
      using inv _ eq₁ eq ← inv->>= eq
      with inv-⊛ eq
    … | inv _ l₂″ eq eq₃ PE.refl
      with inv-<$> eq
    … | inv l₁″ eq₂ PE.refl =
      let l′≡ = supᵘₗ-cong (check-level-sound eq₂ ⊢γ ⊢Γ)
                  (check-level-sound eq₃ ⊢γ ⊢Γ)
          ass = case PE.singleton b of λ where
            (true  , eq) → literal-free-or-iff eq
            (false , eq) →
              let L.lift okᴸ =
                    inv-require⁰ ⊢γ level-allowed (inv-unless eq eq₁)
              in
              level-allowed okᴸ
      in
      PE.subst₂ (_⊢_≡_∷Level _)
        (⌜ Term[]→Lvl l′₁ ⌝ γ S.supᵘₗ ⌜ Term[]→Lvl l′₂ ⌝ γ  ≡⟨ supᵘₗ-⌜Term[]→Lvl⌝ l′₁ _ ⟩
         ⌜ Term[]→Lvl (l′₁ supᵘₗ l′₂) ⌝ γ                   ≡⟨ Term[]→Lvl-cong (l′≡l ass) ⟩
         ⌜ Term[]→Lvl l ⌝ γ                                 ∎ )
        (supᵘₗ-⌜Term[]→Lvl⌝ l₁″ _)
        l′≡
    check-level′-sound l′≡l (just (ωᵘ+ _)) eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv _ eq ok! =
      let ω-ok = inv-require⁰ ⊢γ omega-plus-allowed eq in
      PE.subst (flip (_⊢_≡_∷Level _) _)
        (l′≡l (not-supᵘₗ (λ { (_ , _ , ()) } ))) $
      refl-⊢≡∷L (⊢ωᵘ+ ω-ok ⊢Γ)
    check-level′-sound l′≡l (just (level t)) eq ⊢γ ⊢Γ
      with inv-<$> eq
    … | inv _ eq PE.refl =
      PE.subst (flip (_⊢_≡_∷Level _) _)
        (l′≡l (not-supᵘₗ (λ { (_ , _ , ()) } ))) $
      check-level-sound eq ⊢γ ⊢Γ
    check-level′-sound {k = tm} l′≡l nothing eq ⊢γ ⊢Γ =
      let inv _ eq₁ eq₂ = inv->>= eq
          L.lift okᴸ    = inv-require⁰ ⊢γ level-allowed eq₁
          l′≡           = check-sound eq₂ ⊢γ (Levelⱼ′ okᴸ ⊢Γ)
      in
      PE.subst (flip (_⊢_≡_∷Level _) _)
        (PE.cong U.level (l′≡l (level-allowed okᴸ))) $
      term-⊢≡∷ l′≡
    check-level′-sound {k = lvl} _ nothing not-ok

  -- Soundness for check′.

  check′-sound :
    (t-c : Checkable t) →
    OK (check′ n Γ t-c A) t′ γ st →
    Contexts-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ≡ ⌜ t′ ⌝ γ ∷ ⌜ A ⌝ γ
  check′-sound (lift _) eq ⊢γ ⊢A
    with inv->>= eq
  … | inv (_ , _ , PE.refl) _ eq
    with inv->>= eq
  … | inv _ eq₁ ok! =
    let ⊢l , ⊢B = inversion-Lift ⊢A in
    lift-cong ⊢l (check-sound eq₁ ⊢γ ⊢B)
  check′-sound (lam p _) eq ⊢γ ⊢A
    with inv->>= eq
  … | inv (_ , _ , _ , PE.refl) _ eq
    with inv->>= eq
  … | inv _ eq₁ ok! =
    let _ , ⊢B₂ , Π-ok = inversion-ΠΣ ⊢A in
    lam-cong (check-sound eq₁ ⊢γ ⊢B₂) Π-ok
  check′-sound (prod s p _ _) eq ⊢γ ⊢A
    with inv->>= eq
  … | inv (_ , _ , _ , PE.refl) _ eq
    with inv->>= eq
  … | inv _ eq₁ eq
    with inv->>= eq
  … | inv _ eq₂ ok! =
    let ⊢B₁ , ⊢B₂ , Σ-ok = inversion-ΠΣ ⊢A
        t₁≡t₁′           = check-sound eq₁ ⊢γ ⊢B₁
        _ , _ , ⊢t₁′     = wf-⊢≡∷ t₁≡t₁′
        t₂≡t₂′           = check-sound eq₂ ⊢γ (subst-⊢₀ ⊢B₂ ⊢t₁′)
    in
    sym′ (prod-cong ⊢B₂ (sym′ t₁≡t₁′) (sym′ t₂≡t₂′) Σ-ok)
  check′-sound rfl eq ⊢γ ⊢A
    with inv->>= eq
  … | inv (_ , _ , _ , PE.refl) _ eq
    with inv->>= eq
  … | inv _ eq₁ ok! =
    let _ , ⊢t₁ , ⊢t₂ = inversion-Id ⊢A in
    refl (rflⱼ′ (equal-tm-sound eq₁ ⊢γ ⊢t₁ ⊢t₂))

  opaque
    unfolding Erased.Erased Erased.[_] S._supᵘₗ_

    -- Soundness for infer′.

    infer′-sound :
      (t-i : Inferable t) →
      OK (infer′ n Γ t-i) A γ st →
      Contexts-wf (Γ .defs) γ →
      ⊢ ⌜ Γ ⌝ᶜ γ →
      ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ∷ ⌜ A ⌝ γ
    infer′-sound {γ} (meta-var x σ) eq ⊢γ ⊢Γ
      rewrite ⌜meta-var⌝ {γ = γ} {x = x} σ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv _ eq₂ ok! =
      let _ , ⊢t = is-term-sound eq₁ ⊢γ
          ⊢Δ     = wf ⊢t
          σ≡σ′   = check-sub-sound σ eq₂ ⊢γ ⊢Γ ⊢Δ
      in
      wf-⊢≡∷ (subst-⊢≡∷ (refl ⊢t) (sym-⊢ˢʷ≡∷ ⊢Δ σ≡σ′)) .proj₂ .proj₂
    infer′-sound {Γ} (var _) eq _ ⊢Γ =
      var ⊢Γ (index-sound (Γ .vars) eq .proj₁ PE.refl)
    infer′-sound {Γ} (defn _) eq _ ⊢Γ
      with inv->>= eq
    … | inv _ eq ok! =
      defn ⊢Γ (type-of-sound (Γ .defs) eq) PE.refl
    infer′-sound Level eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ ok! =
      let L.lift Level-small = inv-require⁰ ⊢γ level-is-small eq₁ in
      Levelⱼ ⊢Γ Level-small
    infer′-sound zeroᵘ eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ ok! =
      let L.lift okᴸ = inv-require⁰ ⊢γ level-allowed eq₁ in
      zeroᵘⱼ okᴸ ⊢Γ
    infer′-sound (1ᵘ+ _) eq ⊢γ ⊢Γ
      using inv _ eq₁ eq ← inv->>= eq
      with inv->>= eq
    … | inv _ eq₂ ok! =
      let L.lift okᴸ = inv-require⁰ ⊢γ level-allowed eq₁
          l≡l′       = check-sound eq₂ ⊢γ (Levelⱼ′ okᴸ ⊢Γ)
          _ , ⊢l , _ = wf-⊢≡∷ l≡l′
      in
      sucᵘⱼ ⊢l
    infer′-sound (_ supᵘₗ _) eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv _ eq₂ eq
      with inv->>= eq
    … | inv _ eq₃ ok! =
      let L.lift okᴸ  = inv-require⁰ ⊢γ level-allowed eq₁
          ⊢Level      = Levelⱼ′ okᴸ ⊢Γ
          l₁≡         = check-sound eq₂ ⊢γ ⊢Level
          _ , ⊢l₁ , _ = wf-⊢≡∷ l₁≡
          l₂≡         = check-sound eq₃ ⊢γ ⊢Level
          _ , ⊢l₂ , _ = wf-⊢≡∷ l₂≡
      in
      ⊢∷Level→⊢∷Level okᴸ (⊢supᵘₗ (term-⊢∷ ⊢l₁) (term-⊢∷ ⊢l₂))
    infer′-sound (U _) eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ ok! =
      let l≡l′   = check-level-sound eq₁ ⊢γ ⊢Γ
          ⊢l , _ = wf-⊢≡∷L l≡l′
      in
      conv (Uⱼ ⊢l) (U-cong-⊢≡ (1ᵘ+-cong l≡l′))
    infer′-sound {γ} (Lift l _) eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv l₁ eq₁ eq
      with inv->>= eq
    … | inv l₂ eq₂ ok! =
      let open TyR

          l≡l₁   = check-level-sound eq₁ ⊢γ ⊢Γ
          ⊢l , _ = wf-⊢≡∷L l≡l₁
          ⊢A     = infer-U-sound eq₂ ⊢γ ⊢Γ
          ⊢l₂    = inversion-U-Level (wf-⊢∷ ⊢A)
          U≡U    =
            ⌜ U (l₂ supᵘₗ l) ⌝ γ   ≡⟨ U-cong-⊢≡ (supᵘₗ-comm ⊢l₂ ⊢l) ⟩⊢
            ⌜ U (l supᵘₗ l₂) ⌝ γ   ≡⟨ U-cong-⊢≡ (supᵘₗ-cong l≡l₁ (refl-⊢≡∷L ⊢l₂)) ⟩⊢∎
            ⌜ U (l₁ supᵘₗ l₂) ⌝ γ  ∎
      in
      conv (Liftⱼ′ ⊢l ⊢A) U≡U
    infer′-sound (lift _ _) eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv _ eq₂ ok! =
      let l≡l′    = check-level-sound eq₁ ⊢γ ⊢Γ
          _ , ⊢l′ = wf-⊢≡∷L l≡l′
          ⊢t      = infer-sound eq₂ ⊢γ ⊢Γ
      in
      liftⱼ′ ⊢l′ ⊢t
    infer′-sound (lower _) eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv (_ , _ , PE.refl) _ ok! =
      lowerⱼ (infer-red-sound eq₁ ⊢γ ⊢Γ)
    infer′-sound (Unit _) eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ ok! =
      let Unit-ok = inv-require⁺ ⊢γ eq₁ in
      Unitⱼ ⊢Γ Unit-ok
    infer′-sound (star _) eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ ok! =
      let Unit-ok = inv-require⁺ ⊢γ eq₁ in
      starⱼ ⊢Γ Unit-ok
    infer′-sound (unitrec A _ _) eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv _ eq₂ eq
      using inv _ eq₃ eq ← inv->>= eq
      with inv->>= eq
    … | inv _ eq₄ ok! =
      let Unit-ok = inv-require⁺ ⊢γ eq₄
          ⊢Unit   = ⊢Unit ⊢Γ Unit-ok
          A≡A′    = check-type-sound eq₁ ⊢γ (∙ ⊢Unit)
          _ , ⊢A′ = wf-⊢≡ A≡A′
          t₁≡t₁′  = check-sound eq₂ ⊢γ ⊢Unit
          t₂≡t₂′  = check-sound eq₃ ⊢γ $
                    subst-⊢₀ ⊢A′ (starⱼ ⊢Γ Unit-ok)
      in
      wf-⊢≡∷ (unitrec-cong′ (sym A≡A′) (sym′ t₁≡t₁′) (sym′ t₂≡t₂′))
        .proj₂ .proj₂
    infer′-sound Empty ok! _ ⊢Γ =
      Emptyⱼ ⊢Γ
    infer′-sound (emptyrec _ _) eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv _ eq₂ ok! =
      let A≡A′ = check-type-sound eq₁ ⊢γ ⊢Γ
          t≡t′ = check-sound eq₂ ⊢γ (⊢Empty ⊢Γ)
      in
      wf-⊢≡∷ (emptyrec-cong (sym A≡A′) (sym′ t≡t′)) .proj₂ .proj₂
    infer′-sound (ΠΣ _ _ _ _ _) eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv (_ , PE.refl) _ eq
      with inv->>= eq
    … | inv _ eq₂ eq
      with inv->>= eq
    … | inv _ eq₃ ok! =
      let ⊢A₁         = infer-red-sound eq₁ ⊢γ ⊢Γ
          ⊢l          = inversion-U-Level (wf-⊢∷ ⊢A₁)
          A₂≡         = check-sound eq₂ ⊢γ
                          (⊢U (W.wk₁ (univ ⊢A₁) ⊢l))
          _ , ⊢A₂ , _ = wf-⊢≡∷ A₂≡
          ΠΣ-ok       = inv-require⁺ ⊢γ eq₃
      in
      ΠΣⱼ ⊢l ⊢A₁ ⊢A₂ ΠΣ-ok
    infer′-sound (lam _ _ _ _) eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv _ eq₂ eq
      with inv->>= eq
    … | inv _ eq₃ ok! =
      let A₁≡A₁′   = check-type-sound eq₁ ⊢γ ⊢Γ
          _ , ⊢A₁′ = wf-⊢≡ A₁≡A₁′
          ⊢t       = infer-sound eq₂ ⊢γ (∙ ⊢A₁′)
          Π-ok     = inv-require⁺ ⊢γ eq₃
      in
      lamⱼ′ Π-ok ⊢t
    infer′-sound (app _ _ _) eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv (_ , _ , A₂ , PE.refl) _ eq
      with inv->>= eq
    … | inv _ eq₂ ok! =
      let ⊢t₁     = infer-red-sound eq₁ ⊢γ ⊢Γ
          ⊢A₁ , _ = inversion-ΠΣ (wf-⊢∷ ⊢t₁)
          t₂≡t₂′  = check-sound eq₂ ⊢γ ⊢A₁
      in
      wf-⊢≡∷ (app-cong (refl ⊢t₁) (sym′ t₂≡t₂′)) .proj₂ .proj₂
    infer′-sound (prod _ _ _ _ _ _) eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv _ eq₂ eq
      using inv _ eq₃ eq ← inv->>= eq
      with inv->>= eq
    … | inv _ eq₄ ok! =
      let ⊢t₁      = infer-sound eq₁ ⊢γ ⊢Γ
          ⊢A₁      = wf-⊢∷ ⊢t₁
          A₂≡A₂′   = check-type-sound eq₂ ⊢γ (∙ ⊢A₁)
          _ , ⊢A₂′ = wf-⊢≡ A₂≡A₂′
          t₂≡t₂′   = check-sound eq₃ ⊢γ (subst-⊢₀ ⊢A₂′ ⊢t₁)
          Σ-ok     = inv-require⁺ ⊢γ eq₄
      in
      wf-⊢≡∷ (prod-cong ⊢A₂′ (refl ⊢t₁) t₂≡t₂′ Σ-ok) .proj₂ .proj₁
    infer′-sound (fst _ _) eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv (_ , _ , _ , PE.refl) _ ok! =
      let ⊢t = infer-red-sound eq₁ ⊢γ ⊢Γ in
      fstⱼ′ ⊢t
    infer′-sound (snd _ _) eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv (_ , _ , _ , PE.refl) _ ok! =
      let ⊢t = infer-red-sound eq₁ ⊢γ ⊢Γ in
      sndⱼ′ ⊢t
    infer′-sound (prodrec _ _ _ _) eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv (_ , _ , _ , PE.refl) _ eq
      with inv->>= eq
    … | inv _ eq₂ eq
      with inv->>= eq
    … | inv _ eq₃ ok! =
      let ⊢t₁          = infer-red-sound eq₁ ⊢γ ⊢Γ
          ⊢ΣB₁B₂       = wf-⊢∷ ⊢t₁
          _ , _ , Σ-ok = inversion-ΠΣ ⊢ΣB₁B₂
          A≡A′         = check-type-sound eq₂ ⊢γ (∙ ⊢ΣB₁B₂)
          _ , ⊢A′      = wf-⊢≡ A≡A′
          t₂≡t₂′       = check-sound eq₃ ⊢γ $
                         subst-⊢ ⊢A′ (⊢ˢʷ∷-[][]↑ (⊢1,0 ⊢ΣB₁B₂))
      in
      wf-⊢≡∷ (prodrec-cong (sym A≡A′) (refl ⊢t₁) (sym′ t₂≡t₂′) Σ-ok)
        .proj₂ .proj₂
    infer′-sound ℕ ok! _ ⊢Γ =
      ℕⱼ ⊢Γ
    infer′-sound zero ok! _ ⊢Γ =
      zeroⱼ ⊢Γ
    infer′-sound (suc _) eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv _ eq ok! =
      let t≡t′       = check-sound eq ⊢γ (⊢ℕ ⊢Γ)
          _ , ⊢t , _ = wf-⊢≡∷ t≡t′
      in
      sucⱼ ⊢t
    infer′-sound (natrec _ _ _ _) eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      using inv _ eq₂ eq ← inv->>= eq
          | inv _ eq₃ eq ← inv->>= eq
      with inv->>= eq
    … | inv _ eq₄ ok! =
      let A≡A′    = check-type-sound eq₁ ⊢γ (∙ ⊢ℕ ⊢Γ)
          _ , ⊢A′ = wf-⊢≡ A≡A′
          t₁≡t₁′  = check-sound eq₂ ⊢γ (subst-⊢₀ ⊢A′ (zeroⱼ ⊢Γ))
          t₂≡t₂′  = check-sound eq₃ ⊢γ $
                    subst-⊢ ⊢A′ (⊢ˢʷ∷-[][]↑ (sucⱼ (var₁ ⊢A′)))
          t₃≡t₃′  = check-sound eq₄ ⊢γ (⊢ℕ ⊢Γ)
      in
      wf-⊢≡∷
        (natrec-cong (sym A≡A′) (sym′ t₁≡t₁′) (sym′ t₂≡t₂′)
           (sym′ t₃≡t₃′))
        .proj₂ .proj₂
    infer′-sound (Id _ _ _) eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv (_ , PE.refl) _ eq
      using inv _ eq₂ eq ← inv->>= eq
      with inv->>= eq
    … | inv _ eq₃ ok! =
      let ⊢A          = infer-red-sound eq₁ ⊢γ ⊢Γ
          t₁≡t₁′      = check-sound eq₂ ⊢γ (univ ⊢A)
          _ , ⊢t₁ , _ = wf-⊢≡∷ t₁≡t₁′
          t₂≡t₂′      = check-sound eq₃ ⊢γ (univ ⊢A)
          _ , ⊢t₂ , _ = wf-⊢≡∷ t₂≡t₂′
      in
      Idⱼ ⊢A ⊢t₁ ⊢t₂
    infer′-sound (rfl _) eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ ok! =
      rflⱼ (infer-sound eq₁ ⊢γ ⊢Γ)
    infer′-sound (J _ _ _ _ _ _) eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv _ eq₂ eq
      with inv->>= eq
    … | inv _ eq₃ eq
      using inv _ eq₄ eq ← inv->>= eq
      with inv->>= eq
    … | inv _ eq₅ eq
      with inv->>= eq
    … | inv _ eq₆ ok! =
      let A₁≡A₁′       = check-type-sound eq₁ ⊢γ ⊢Γ
          _ , ⊢A₁′     = wf-⊢≡ A₁≡A₁′
          t₁≡t₁′       = check-sound eq₂ ⊢γ ⊢A₁′
          _ , _ , ⊢t₁′ = wf-⊢≡∷ t₁≡t₁′
          A₂≡A₂′       = check-type-sound eq₃ ⊢γ
                           (J-motive-context ⊢t₁′)
          _ , ⊢A₂′     = wf-⊢≡ A₂≡A₂′
          t₂≡t₂′       = check-sound eq₄ ⊢γ (J-result ⊢A₂′ (rflⱼ ⊢t₁′))
          t₃≡t₃′       = check-sound eq₅ ⊢γ ⊢A₁′
          _ , _ , ⊢t₃′ = wf-⊢≡∷ t₃≡t₃′
          t₄≡t₄′       = check-sound eq₆ ⊢γ (Idⱼ′ ⊢t₁′ ⊢t₃′)
      in
      wf-⊢≡∷
        (J-cong′ (sym A₁≡A₁′) (sym′ t₁≡t₁′) (sym A₂≡A₂′) (sym′ t₂≡t₂′)
           (sym′ t₃≡t₃′) (sym′ t₄≡t₄′))
        .proj₂ .proj₂
    infer′-sound (K _ _ _ _ _) eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv _ eq₂ eq
      with inv->>= eq
    … | inv _ eq₃ eq
      using inv _ eq₄ eq ← inv->>= eq
      with inv->>= eq
    … | inv _ eq₅ eq
      with inv->>= eq
    … | inv _ eq₆ ok! =
      let A₁≡A₁′       = check-type-sound eq₁ ⊢γ ⊢Γ
          _ , ⊢A₁′     = wf-⊢≡ A₁≡A₁′
          t₁≡t₁′       = check-sound eq₂ ⊢γ ⊢A₁′
          _ , _ , ⊢t₁′ = wf-⊢≡∷ t₁≡t₁′
          ⊢Id          = Idⱼ′ ⊢t₁′ ⊢t₁′
          A₂≡A₂′       = check-type-sound eq₃ ⊢γ (∙ ⊢Id)
          _ , ⊢A₂′     = wf-⊢≡ A₂≡A₂′
          t₂≡t₂′       = check-sound eq₄ ⊢γ (subst-⊢₀ ⊢A₂′ (rflⱼ ⊢t₁′))
          t₃≡t₃′       = check-sound eq₅ ⊢γ ⊢Id
          K-ok         = inv-require⁰ ⊢γ k-allowed eq₆
      in
      wf-⊢≡∷
        (K-cong (sym A₁≡A₁′) (sym′ t₁≡t₁′) (sym A₂≡A₂′) (sym′ t₂≡t₂′)
           (sym′ t₃≡t₃′) K-ok)
        .proj₂ .proj₂
    infer′-sound ([]-cong _ _ _ _ _ _) eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv _ eq₂ eq
      with inv->>= eq
    … | inv _ eq₃ eq
      with inv->>= eq
    … | inv _ eq₄ eq
      using inv _ eq₅ eq ← inv->>= eq
      with inv->>= eq
    … | inv _ eq₆ ok! =
      let l≡l′         = check-level-sound eq₁ ⊢γ ⊢Γ
          A≡A′         = check-type-sound eq₂ ⊢γ ⊢Γ
          _ , ⊢A′      = wf-⊢≡ A≡A′
          t₁≡t₁′       = check-sound eq₃ ⊢γ ⊢A′
          _ , _ , ⊢t₁′ = wf-⊢≡∷ t₁≡t₁′
          t₂≡t₂′       = check-sound eq₄ ⊢γ ⊢A′
          _ , _ , ⊢t₂′ = wf-⊢≡∷ t₂≡t₂′
          t₃≡t₃′       = check-sound eq₅ ⊢γ (Idⱼ′ ⊢t₁′ ⊢t₂′)
          okᵇᶜ         = inv-require⁺ ⊢γ eq₆
      in
      wf-⊢≡∷
        ([]-cong-cong (sym-⊢≡∷L l≡l′) (sym A≡A′) (sym′ t₁≡t₁′)
           (sym′ t₂≡t₂′) (sym′ t₃≡t₃′) okᵇᶜ)
        .proj₂ .proj₂

  -- Soundness for normalise-level′.

  normalise-level′-sound :
    {l : Term[ c , k ] _}
    (l-l : Maybe (Is-perhaps-level l)) →
    OK (normalise-level′ b n Γ l-l) nf γ st →
    Contexts-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ Term[]→Lvl l ⌝ γ ∷Level →
    ⌜ Γ ⌝ᶜ γ ⊢⌜ nf ⌝ⁿ γ ∷Level ×
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ Term[]→Lvl l ⌝ γ ≡ ⌜ nf ⌝ⁿ γ ∷Level
  normalise-level′-sound (just (meta-var x _)) ok! _ ⊢x[σ] =
    ⌞⌟ⁿ-correct (meta-var x _) ⊢x[σ]
  normalise-level′-sound (just zeroᵘ) ok! _ ⊢zeroᵘ =
    zeroᵘⁿ-correct (wf ⊢zeroᵘ)
  normalise-level′-sound {γ} (just (1ᵘ+ l)) eq ⊢γ ⊢1ᵘ+
    with inv-<$> eq
  … | inv l′ eq PE.refl =
    let ⊢l                    = inversion-1ᵘ+-⊢∷L $
                                PE.subst (_⊢_∷Level _)
                                  (PE.sym (1ᵘ+-⌜Term[]→Lvl⌝ l)) ⊢1ᵘ+
        ⊢l′ , l≡l′            = normalise-level-sound eq ⊢γ ⊢l
        ⊢⌜1ᵘ+ⁿ-l′⌝ , ≡1ᵘ+⌜l′⌝ = 1ᵘ+ⁿ-correct ⊢l′
    in
    ⊢⌜1ᵘ+ⁿ-l′⌝ ,
    (⌜ Term[]→Lvl (1ᵘ+ l) ⌝ γ    ≡˘⟨ 1ᵘ+-⌜Term[]→Lvl⌝ l ⟩⊢≡
     U.1ᵘ+ (⌜ Term[]→Lvl l ⌝ γ)  ≡⟨ 1ᵘ+-cong l≡l′ ⟩⊢
     U.1ᵘ+ (⌜ l′ ⌝ⁿ γ)           ≡˘⟨ ≡1ᵘ+⌜l′⌝ ⟩⊢∎
     ⌜ 1ᵘ+ⁿ l′ ⌝ⁿ γ              ∎)
    where
    open LvlR
  normalise-level′-sound (just (ωᵘ+ _)) ok! _ ⊢ωᵘ+ =
    uncurry ωᵘ+ⁿ-correct (inversion-ωᵘ+ ⊢ωᵘ+)
  normalise-level′-sound (just (level _)) eq ⊢γ ⊢level =
    normalise-level-sound eq ⊢γ ⊢level
  normalise-level′-sound {k = lvl} {γ} (just (l₁ supᵘₗ l₂)) eq ⊢γ ⊢supᵘ
    with inv->>= eq
  … | inv l₁′ eq₁ eq
    with inv->>= eq
  … | inv l₂′ eq₂ eq
    with inv-⊛ eq
  … | inv _ l₂″ eq eq₄ PE.refl
    with inv-<$> eq
  … | inv l₁″ eq₃ PE.refl =
    let ⊢Γ                    = wf ⊢supᵘ
        l₁≡l₁′                = check-level-sound eq₁ ⊢γ ⊢Γ
        _ , ⊢l₁′              = wf-⊢≡∷L l₁≡l₁′
        ⊢l₁″ , l₁′≡l₁″        = normalise-level-sound eq₃ ⊢γ ⊢l₁′
        l₂≡l₂′                = check-level-sound eq₂ ⊢γ ⊢Γ
        _ , ⊢l₂′              = wf-⊢≡∷L l₂≡l₂′
        ⊢l₂″ , l₂′≡l₂″        = normalise-level-sound eq₄ ⊢γ ⊢l₂′
        ⊢⌜supᵘₗⁿ⌝ , ⌜supᵘₗⁿ⌝≡ = supᵘₗⁿ-correct ⊢l₁″ ⊢l₂″
    in
    ⊢⌜supᵘₗⁿ⌝ ,
    (⌜ l₁ ⌝ γ S.supᵘₗ ⌜ l₂ ⌝ γ      ≡⟨ supᵘₗ-cong l₁≡l₁′ l₂≡l₂′ ⟩⊢
     ⌜ l₁′ ⌝ γ S.supᵘₗ ⌜ l₂′ ⌝ γ    ≡⟨ supᵘₗ-cong l₁′≡l₁″ l₂′≡l₂″ ⟩⊢
     ⌜ l₁″ ⌝ⁿ γ S.supᵘₗ ⌜ l₂″ ⌝ⁿ γ  ≡˘⟨ ⌜supᵘₗⁿ⌝≡ ⟩⊢∎
     ⌜ supᵘₗⁿ l₁″ l₂″ ⌝ⁿ γ          ∎)
    where
    open LvlR
  normalise-level′-sound {k = tm} {γ} (just (t₁ supᵘₗ t₂)) eq ⊢γ ⊢supᵘ
    with inv-⊛ eq
  … | inv _ l₂ eq eq₂ PE.refl
    with inv-<$> eq
  … | inv l₁ eq₁ PE.refl =
    let ⊢t₁ , ⊢t₂             = inversion-supᵘₗ-level ⊢supᵘ
        ⊢l₁ , t₁≡l₁           = normalise-level-sound eq₁ ⊢γ ⊢t₁
        ⊢l₂ , t₂≡l₂           = normalise-level-sound eq₂ ⊢γ ⊢t₂
        ⊢⌜supᵘₗⁿ⌝ , ⌜supᵘₗⁿ⌝≡ = supᵘₗⁿ-correct ⊢l₁ ⊢l₂
    in
    ⊢⌜supᵘₗⁿ⌝ ,
    (U.level (⌜ t₁ ⌝ γ S.supᵘₗ ⌜ t₂ ⌝ γ)    ≡˘⟨ supᵘₗ-⌜Term[]→Lvl⌝ t₁ t₂ ⟩⊢≡
     ⌜ level t₁ ⌝ γ S.supᵘₗ ⌜ level t₂ ⌝ γ  ≡⟨ supᵘₗ-cong t₁≡l₁ t₂≡l₂ ⟩⊢
     ⌜ l₁ ⌝ⁿ γ S.supᵘₗ ⌜ l₂ ⌝ⁿ γ            ≡˘⟨ ⌜supᵘₗⁿ⌝≡ ⟩⊢∎
     ⌜ supᵘₗⁿ l₁ l₂ ⌝ⁿ γ                    ∎)
    where
    open LvlR
  normalise-level′-sound {k = lvl} {b = true} {l} nothing ok! _ ⊢l =
    ⌞⌟ⁿ-correct l ⊢l
  normalise-level′-sound {k = lvl} {b = false} {l} nothing ok! _ ⊢l =
    ⌞⌟ⁿ-correct l ⊢l
  normalise-level′-sound {k = tm} {b = true} {l} nothing ok! _ ⊢l =
    ⌞⌟ⁿ-correct l ⊢l
  normalise-level′-sound
    {k = tm} {b = false} {nf = l″} {γ} {l} nothing eq ⊢γ ⊢l =
    let inv _  eq₁ eq  = inv->>= eq
        inv l′ eq₂ eq₃ = inv->>= eq
        L.lift okᴸ     = inv-require⁰ ⊢γ level-allowed eq₁
        ⊢l             = ⊢∷Level→⊢∷Level okᴸ ⊢l
        l≡l′           = red-tm-sound eq₂ ⊢γ ⊢l
        _ , _ , ⊢l′    = wf-⊢≡∷ l≡l′
        ⊢l″ , l′≡l″    = normalise-level-sound eq₃ ⊢γ (term-⊢∷ ⊢l′)
    in
    ⊢l″ ,
    (⌜ Term[]→Lvl l ⌝ γ   ≡⟨ term-⊢≡∷ l≡l′ ⟩⊢
     ⌜ Term[]→Lvl l′ ⌝ γ  ≡⟨ l′≡l″ ⟩⊢∎
     ⌜ l″ ⌝ⁿ γ            ∎)
    where
    open LvlR

  opaque
    unfolding Erased.Erased Erased.[_]

    -- Soundness for equal-ne-inf′.

    equal-ne-inf′-sound :
      (eq : Are-equal-eliminators t₁ t₂) →
      OK (equal-ne-inf′ n Γ eq) A γ st →
      Contexts-wf (Γ .defs) γ →
      ⊢ ⌜ Γ ⌝ᶜ γ →
      ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ≡ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ
    equal-ne-inf′-sound {γ} (meta-var x₁ σ₁ x₂ σ₂ PE.refl) eq ⊢γ ⊢Γ
      rewrite ⌜meta-var⌝ {γ = γ} {x = x₁} σ₁
            | ⌜meta-var⌝ {γ = γ} {x = x₂} σ₂
      using inv _ _ eq ← inv->>= eq
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv PE.refl eq₂ eq
      with inv->>= eq
    … | inv _ eq₃ ok! =
      let x₂-term , ⊢x₂ = is-term-sound eq₁ ⊢γ
          σ₁≡σ₂         = equal-sub′-sound eq₂ ⊢γ (λ ()) ⊢Γ (wf ⊢x₂)
          x₁≡x₂         = are-equal-meta-vars-sound-tm eq₃ ⊢γ x₂-term
                            ⊢x₂
      in
      subst-⊢≡∷ x₁≡x₂ σ₁≡σ₂
    equal-ne-inf′-sound {Γ} (var _ PE.refl) eq _ ⊢Γ =
      refl (var ⊢Γ (index-sound (Γ .vars) eq .proj₁ PE.refl))
    equal-ne-inf′-sound {Γ} (defn _ PE.refl) eq _ ⊢Γ
      with inv->>= eq
    … | inv _ eq ok! =
      refl (defn ⊢Γ (type-of-sound (Γ .defs) eq) PE.refl)
    equal-ne-inf′-sound (sup _ _ _ _ PE.refl) eq ⊢γ ⊢Γ
      using inv _ eq₁ eq ← inv->>= eq
      with inv->>= eq
    … | inv _ eq₂ ok! =
      let _ , ⊔≡⊔    = check-and-equal-level-sound eq₁ ⊢γ ⊢Γ
          L.lift okᴸ = inv-require⁰ ⊢γ level-allowed eq₂
      in
      ⊢≡∷Level→⊢≡∷Level okᴸ ⊔≡⊔
    equal-ne-inf′-sound (lower _ _ PE.refl) eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv (_ , _ , PE.refl) _ ok! =
      lower-cong (equal-ne-inf-red-sound eq₁ ⊢γ ⊢Γ)
    equal-ne-inf′-sound (emptyrec _ _ _ _ PE.refl) eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv _ eq₂ ok! =
      let A₁≡A , A₁≡A₂ = check-and-equal-ty-sound eq₁ ⊢γ ⊢Γ
          t₁≡t₂        = equal-ne-red-sound eq₂ ⊢γ (⊢Empty ⊢Γ)
      in
      conv (emptyrec-cong A₁≡A₂ t₁≡t₂) A₁≡A
    equal-ne-inf′-sound (unitrec _ _ _ _ _ _ PE.refl) eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      using inv _ eq₂ eq ← inv->>= eq
          | inv _ eq₃ eq ← inv->>= eq
      with inv->>= eq
    … | inv _ eq₄ ok! =
      let Unit-ok      = inv-require⁺ ⊢γ eq₄
          ⊢Unit        = ⊢Unit ⊢Γ Unit-ok
          ⊢⋆           = starⱼ ⊢Γ Unit-ok
          A₁≡A , A₁≡A₂ = check-and-equal-ty-sound eq₁ ⊢γ (∙ ⊢Unit)
          _ , ⊢A       = wf-⊢≡ A₁≡A
          t₁₁≡t₂₁      = equal-ne-red-sound eq₂ ⊢γ ⊢Unit
          _ , ⊢t₁₁ , _ = wf-⊢≡∷ t₁₁≡t₂₁
          _ , t₁₂≡t₂₂  = check-and-equal-tm-sound eq₃ ⊢γ
                           (subst-⊢₀ ⊢A ⊢⋆)
          t₁₂≡t₂₂      = conv t₁₂≡t₂₂ (subst-⊢≡₀ (sym A₁≡A) (refl ⊢⋆))
      in
      conv (unitrec-cong′ A₁≡A₂ t₁₁≡t₂₁ t₁₂≡t₂₂)
        (subst-⊢≡₀ A₁≡A (refl ⊢t₁₁))
    equal-ne-inf′-sound (app _ _ _ _ _ PE.refl) eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv (_ , _ , _ , PE.refl) _ eq
      with inv->>= eq
    … | inv _ eq₂ ok! =
      let t₁₁≡t₂₁          = equal-ne-inf-red-sound eq₁ ⊢γ ⊢Γ
          ⊢Π , _           = wf-⊢≡∷ t₁₁≡t₂₁
          ⊢A₁ , ⊢A₂ , _    = inversion-ΠΣ ⊢Π
          t₁₂≡t₂ , t₁₂≡t₂₂ = check-and-equal-tm-sound eq₂ ⊢γ ⊢A₁
      in
      conv (app-cong t₁₁≡t₂₁ t₁₂≡t₂₂) (subst-⊢≡₀ ⊢A₂ t₁₂≡t₂)
    equal-ne-inf′-sound (fst _ _ _ PE.refl) eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv (_ , _ , _ , PE.refl) _ ok! =
      fst-cong′ (equal-ne-inf-red-sound eq₁ ⊢γ ⊢Γ)
    equal-ne-inf′-sound (snd _ _ _ PE.refl) eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv (_ , _ , _ , PE.refl) _ ok! =
      snd-cong′ (equal-ne-inf-red-sound eq₁ ⊢γ ⊢Γ)
    equal-ne-inf′-sound (prodrec _ _ _ _ _ _ _ PE.refl) eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv (_ , _ , _ , PE.refl) _ eq
      with inv->>= eq
    … | inv _ eq₂ eq
      with inv->>= eq
    … | inv _ eq₃ ok! =
      let t₁₁≡t₂₁      = equal-ne-inf-red-sound eq₁ ⊢γ ⊢Γ
          _ , ⊢t₁₁ , _ = wf-⊢≡∷ t₁₁≡t₂₁
          ⊢Σ , _       = wf-⊢≡∷ t₁₁≡t₂₁
          A₁≡A , A₁≡A₂ = check-and-equal-ty-sound eq₂ ⊢γ (∙ ⊢Σ)
          _ , ⊢A       = wf-⊢≡ A₁≡A
          _ , t₁₂≡t₂₂  = check-and-equal-tm-sound eq₃ ⊢γ
                           (subst-⊢-↑ ⊢A (⊢1,0 ⊢Σ))
          t₁₂≡t₂₂      = conv t₁₂≡t₂₂ $
                         subst-⊢≡-↑ (sym A₁≡A) (refl (⊢1,0 ⊢Σ))
      in
      conv (prodrec-cong′ A₁≡A₂ t₁₁≡t₂₁ t₁₂≡t₂₂)
        (subst-⊢≡₀ A₁≡A (refl ⊢t₁₁))
    equal-ne-inf′-sound (natrec _ _ _ _ _ _ _ _ PE.refl) eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      using inv _ eq₂ eq ← inv->>= eq
          | inv _ eq₃ eq ← inv->>= eq
      with inv->>= eq
    … | inv _ eq₄ ok! =
      let A₁≡A , A₁≡A₂ = check-and-equal-ty-sound eq₁ ⊢γ (∙ ⊢ℕ ⊢Γ)
          _ , ⊢A       = wf-⊢≡ A₁≡A
          ⊢0           = zeroⱼ ⊢Γ
          ⊢suc-1       = sucⱼ (var₁ ⊢A)
          _ , t₁₁≡t₂₁  = check-and-equal-tm-sound eq₂ ⊢γ
                           (subst-⊢₀ ⊢A ⊢0)
          t₁₁≡t₂₁      = conv t₁₁≡t₂₁ (subst-⊢≡₀ (sym A₁≡A) (refl ⊢0))
          _ , t₁₂≡t₂₂  = check-and-equal-tm-sound eq₃ ⊢γ
                           (subst-⊢-↑ ⊢A ⊢suc-1)
          t₁₂≡t₂₂      = stability (refl-∙ (sym A₁≡A)) $
                         conv t₁₂≡t₂₂ $
                         subst-⊢≡-↑ (sym A₁≡A) (refl ⊢suc-1)
          t₁₃≡t₂₃      = equal-ne-red-sound eq₄ ⊢γ (⊢ℕ ⊢Γ)
          _ , ⊢t₁₃ , _ = wf-⊢≡∷ t₁₃≡t₂₃
      in
      conv (natrec-cong A₁≡A₂ t₁₁≡t₂₁ t₁₂≡t₂₂ t₁₃≡t₂₃)
        (subst-⊢≡₀ A₁≡A (refl ⊢t₁₃))
    equal-ne-inf′-sound (J _ _ _ _ _ _ _ _ _ _ _ _ PE.refl) eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv _ eq₂ eq
      with inv->>= eq
    … | inv _ eq₃ eq
      using inv _ eq₄ eq ← inv->>= eq
      with inv->>= eq
    … | inv _ eq₅ eq
      with inv->>= eq
    … | inv _ eq₆ ok! =
      let A₁₁≡A₁ , A₁₁≡A₂₁ = check-and-equal-ty-sound eq₁ ⊢γ ⊢Γ
          _ , ⊢A₁          = wf-⊢≡ A₁₁≡A₁
          t₁₁≡t₁ , t₁₁≡t₂₁ = check-and-equal-tm-sound eq₂ ⊢γ ⊢A₁
          _ , _ , ⊢t₁      = wf-⊢≡∷ t₁₁≡t₁
          t₁₁≡t₂₁          = conv t₁₁≡t₂₁ (sym A₁₁≡A₁)
          A₁₂≡A₂ , A₁₂≡A₂₂ = check-and-equal-ty-sound eq₃ ⊢γ
                               (J-motive-context ⊢t₁)
          _ , ⊢A₂          = wf-⊢≡ A₁₂≡A₂
          A₁₂≡A₂₂          = stability
                               (J-motive-context-cong′ (sym A₁₁≡A₁)
                                  (sym′ t₁₁≡t₁))
                               A₁₂≡A₂₂
          _ , t₁₂≡t₂₂      = check-and-equal-tm-sound eq₄ ⊢γ
                               (J-result ⊢A₂ (rflⱼ ⊢t₁))
          t₁₂≡t₂₂          = conv t₁₂≡t₂₂ $
                             J-motive-rfl-cong (sym A₁₂≡A₂)
                               (sym′ t₁₁≡t₁)
          t₁₃≡t₃ , t₁₃≡t₂₃ = check-and-equal-tm-sound eq₅ ⊢γ ⊢A₁
          _ , _ , ⊢t₃      = wf-⊢≡∷ t₁₃≡t₃
          t₁₃≡t₂₃          = conv t₁₃≡t₂₃ (sym A₁₁≡A₁)
          t₁₄≡t₂₄          = equal-ne-red-sound eq₆ ⊢γ (Idⱼ′ ⊢t₁ ⊢t₃)
          _ , ⊢t₁₄ , _     = wf-⊢≡∷ t₁₄≡t₂₄
          t₁₄≡t₂₄          = conv t₁₄≡t₂₄ $
                             Id-cong (sym A₁₁≡A₁) (sym′ t₁₁≡t₁)
                               (sym′ t₁₃≡t₃)
      in
      conv (J-cong′ A₁₁≡A₂₁ t₁₁≡t₂₁ A₁₂≡A₂₂ t₁₂≡t₂₂ t₁₃≡t₂₃ t₁₄≡t₂₄)
        (sym (J-result-cong (sym A₁₂≡A₂) (sym′ t₁₃≡t₃) (refl ⊢t₁₄)))
    equal-ne-inf′-sound (K _ _ _ _ _ _ _ _ _ _ PE.refl) eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv _ eq₂ eq
      with inv->>= eq
    … | inv _ eq₃ eq
      using inv _ eq₄ eq ← inv->>= eq
          | inv _ eq₅ eq ← inv->>= eq
      with inv->>= eq
    … | inv _ eq₆ ok! =
      let A₁₁≡A₁ , A₁₁≡A₂₁ = check-and-equal-ty-sound eq₁ ⊢γ ⊢Γ
          _ , ⊢A₁          = wf-⊢≡ A₁₁≡A₁
          t₁₁≡t₁ , t₁₁≡t₂₁ = check-and-equal-tm-sound eq₂ ⊢γ ⊢A₁
          _ , _ , ⊢t₁      = wf-⊢≡∷ t₁₁≡t₁
          t₁₁≡t₂₁          = conv t₁₁≡t₂₁ (sym A₁₁≡A₁)
          Id≡Id            = Id-cong (sym A₁₁≡A₁) (sym′ t₁₁≡t₁)
                               (sym′ t₁₁≡t₁)
          ⊢Id , _          = wf-⊢≡ Id≡Id
          A₁₂≡A₂ , A₁₂≡A₂₂ = check-and-equal-ty-sound eq₃ ⊢γ (∙ ⊢Id)
          _ , ⊢A₂          = wf-⊢≡ A₁₂≡A₂
          A₁₂≡A₂₂          = stability (refl-∙ Id≡Id) A₁₂≡A₂₂
          _ , t₁₂≡t₂₂      = check-and-equal-tm-sound eq₄ ⊢γ $
                             subst-⊢₀ ⊢A₂ (rflⱼ ⊢t₁)
          t₁₂≡t₂₂          = conv t₁₂≡t₂₂ $
                             subst-⊢≡₀ (sym A₁₂≡A₂) (refl (rflⱼ ⊢t₁))
          t₁₃≡t₂₃          = equal-ne-red-sound eq₅ ⊢γ ⊢Id
          _ , ⊢t₁₃ , _     = wf-⊢≡∷ t₁₃≡t₂₃
          t₁₃≡t₂₃          = conv t₁₃≡t₂₃ Id≡Id
          K-ok             = inv-require⁰ ⊢γ k-allowed eq₆
      in
      conv (K-cong A₁₁≡A₂₁ t₁₁≡t₂₁ A₁₂≡A₂₂ t₁₂≡t₂₂ t₁₃≡t₂₃ K-ok)
        (subst-⊢≡₀ A₁₂≡A₂ (refl ⊢t₁₃))
    equal-ne-inf′-sound ([]-cong _ _ _ _ _ _ _ _ _ _ _ PE.refl) eq ⊢γ ⊢Γ
      with inv->>= eq
    … | inv _ eq₁ eq
      with inv->>= eq
    … | inv _ eq₂ eq
      with inv->>= eq
    … | inv _ eq₃ eq
      with inv->>= eq
    … | inv _ eq₄ eq
      using inv _ eq₅ eq ← inv->>= eq
      with inv->>= eq
    … | inv _ eq₆ ok! =
      let l₁≡l , l₁≡l₂     = check-and-equal-level-sound eq₁ ⊢γ ⊢Γ
          _ , ⊢l           = wf-⊢≡∷L l₁≡l
          A₁≡A , A₁≡A₂     = check-and-equal-ty-sound eq₂ ⊢γ ⊢Γ
          _ , ⊢A           = wf-⊢≡ A₁≡A
          t₁₁≡t₁ , t₁₁≡t₂₁ = check-and-equal-tm-sound eq₃ ⊢γ ⊢A
          _ , _ , ⊢t₁      = wf-⊢≡∷ t₁₁≡t₁
          t₁₁≡t₂₁          = conv t₁₁≡t₂₁ (sym A₁≡A)
          t₁₂≡t₂ , t₁₂≡t₂₂ = check-and-equal-tm-sound eq₄ ⊢γ ⊢A
          _ , _ , ⊢t₂      = wf-⊢≡∷ t₁₂≡t₂
          t₁₂≡t₂₂          = conv t₁₂≡t₂₂ (sym A₁≡A)
          t₁₃≡t₂₃          = equal-ne-red-sound eq₅ ⊢γ (Idⱼ′ ⊢t₁ ⊢t₂)
          t₁₃≡t₂₃          = conv t₁₃≡t₂₃ $
                             Id-cong (sym A₁≡A) (sym′ t₁₁≡t₁)
                               (sym′ t₁₂≡t₂)
          okᵇᶜ             = inv-require⁺ ⊢γ eq₆
          okᴱ              = []-cong→Erased okᵇᶜ
      in
      _⊢_≡_∷_.conv
        ([]-cong-cong l₁≡l₂ A₁≡A₂ t₁₁≡t₂₁ t₁₂≡t₂₂ t₁₃≡t₂₃ okᵇᶜ) $
      _⊢_≡_.sym $
      Id-cong (sym (Erased-cong okᴱ l₁≡l A₁≡A))
        (sym′ ([]-cong′ okᴱ ⊢l t₁₁≡t₁)) (sym′ ([]-cong′ okᴱ ⊢l t₁₂≡t₂))

-- P (1+ n) is inhabited if P n is inhabited.

private module P-1+ (p : P n) where opaque

  open Lemmas p
  open P p

  -- Soundness for red-ty (1+ n).

  red-ty-1+-sound :
    OK (red-ty (1+ n) Γ A) B γ st →
    Contexts-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A ⌝ γ ≡ ⌜ B ⌝ γ
  red-ty-1+-sound {A} {B} {γ} eq ⊢γ ⊢A
    with inv-if-no-equality-reflection ⊢γ (inv-register eq)
  … | inj₁ (no-refl , eq) =
    red-sound-⊢ ⦃ ok = possibly-nonempty ⦃ ok = no-refl ⦄ ⦄ n eq ⊢A
  … | inj₂ eq
    with inv->>= eq
  … | inv (A′ , _) eq₁ eq₂
    using A≡A′ ← really-remove-weaken-subst-sound n eq₁ (type₁ ⊢A)
    with is-type-constructor? A′ | eq₂
  … | just _ | ok! =
    PE.subst (_⊢_≡_ _ _) A≡A′ (refl ⊢A)
  … | nothing | eq
    with inv->>= eq
  … | inv _ eq₃ eq
    with inv->>= eq
  … | inv (_ , PE.refl) _ eq₄ =
    let ⊢A′ = infer-red-sound eq₃ ⊢γ (wf ⊢A) in
    ⌜ A  ⌝ γ  ≡⟨ A≡A′ ⟩⊢≡
    ⌜ A′ ⌝ γ  ≡⟨ univ (red-tm-sound eq₄ ⊢γ ⊢A′) ⟩⊢∎
    ⌜ B  ⌝ γ  ∎
    where
    open TyR

  -- Soundness for red-tm (1+ n).

  red-tm-1+-sound :
    OK (red-tm (1+ n) Γ t A) u γ st →
    Contexts-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ∷ ⌜ A ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ≡ ⌜ u ⌝ γ ∷ ⌜ A ⌝ γ
  red-tm-1+-sound {t} eq ⊢γ
    with inv-if-no-equality-reflection ⊢γ (inv-register eq)
  … | inj₁ (no-refl , eq) =
    red-sound-⊢∷ ⦃ ok = possibly-nonempty ⦃ ok = no-refl ⦄ ⦄ n eq
  … | inj₂ eq =
    red-tm′-sound t eq ⊢γ

  -- Soundness for check-type (1+ n).

  check-type-1+-sound :
    OK (check-type (1+ n) Γ A) A′ γ st →
    Contexts-wf (Γ .defs) γ →
    ⊢ ⌜ Γ ⌝ᶜ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A ⌝ γ ≡ ⌜ A′ ⌝ γ
  check-type-1+-sound {A} {A′} {γ} eq ⊢γ ⊢Γ
    with inv->>= (inv-register eq)
  … | inv (A″ , _) eq₁ eq₂ =
    let A″≡A′   = check-type′-sound (is-type-constructor? A″) eq₂ ⊢γ ⊢Γ
        ⊢A″ , _ = wf-⊢≡ A″≡A′
        A≡A″    = really-remove-weaken-subst-sound n eq₁ (type₂ ⊢A″)
    in
    ⌜ A ⌝ γ   ≡⟨ A≡A″ ⟩⊢≡
    ⌜ A″ ⌝ γ  ≡⟨ A″≡A′ ⟩⊢∎
    ⌜ A′ ⌝ γ  ∎
    where
    open TyR

  -- Soundness for check-level (1+ n).

  check-level-1+-sound :
    OK (check-level (1+ n) Γ l) l′ γ st →
    Contexts-wf (Γ .defs) γ →
    ⊢ ⌜ Γ ⌝ᶜ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ Term[]→Lvl l ⌝ γ ≡ ⌜ Term[]→Lvl l′ ⌝ γ ∷Level
  check-level-1+-sound eq ⊢γ ⊢Γ
    with inv->>= (inv-register eq)
  … | inv (l′ , _) eq₁ eq₂ =
    check-level′-sound
      (PE.sym ∘→ really-remove-weaken-subst-sound n eq₁)
      (is-perhaps-level? l′) eq₂ ⊢γ ⊢Γ

  -- Soundness for check (1+ n).

  check-1+-sound :
    OK (check (1+ n) Γ t A) t′ γ st →
    Contexts-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ≡ ⌜ t′ ⌝ γ ∷ ⌜ A ⌝ γ
  check-1+-sound eq _ ⊢A
    with inv->>= (inv-register eq)
  … | inv (t″ , _) eq₁ eq
    using t≡t″ ← really-remove-weaken-subst-sound n eq₁
    with checkable? t″
  check-1+-sound _ ⊢γ ⊢A | inv _ _ eq | nothing
    with inv->>= eq
  … | inv _ eq₂ eq
    with inv->>= eq
  … | inv _ eq₃ ok! =
    let ⊢t″ = infer-sound eq₂ ⊢γ (wf ⊢A)
        B≡A = equal-ty-sound eq₃ ⊢γ (wf-⊢∷ ⊢t″) ⊢A
    in
    PE.subst₃ (_⊢_≡_∷_ _) (PE.sym (t≡t″ (term₂ ⊢t″))) PE.refl PE.refl $
    refl (conv ⊢t″ B≡A)
  check-1+-sound {t} {t′} {γ} _ ⊢γ ⊢A
    | inv (t″ , _) _ eq | just t″-c =
    let inv _ eq₂ eq₃ = inv->>= eq
        A≡A′          = red-ty-sound eq₂ ⊢γ ⊢A
        _ , ⊢A′       = wf-⊢≡ A≡A′
        t″≡t′         = check′-sound t″-c eq₃ ⊢γ ⊢A′
        _ , ⊢t″ , _   = wf-⊢≡∷ t″≡t′
    in
    ⌜ t ⌝ γ   ≡⟨ t≡t″ (term₂ ⊢t″) ⟩⊢≡
    ⌜ t″ ⌝ γ  ≡⟨ conv t″≡t′ (sym A≡A′) ⟩⊢∎
    ⌜ t′ ⌝ γ  ∎
    where
    open TmR

  -- Soundness for infer (1+ n).

  infer-1+-sound :
    OK (infer (1+ n) Γ t) A γ st →
    Contexts-wf (Γ .defs) γ →
    ⊢ ⌜ Γ ⌝ᶜ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ∷ ⌜ A ⌝ γ
  infer-1+-sound eq ⊢γ ⊢Γ
    with inv->>= (inv-register eq)
  … | inv _ eq₁ eq =
    let inv t′-i _ eq₂ = inv->>= eq
        ⊢t′            = infer′-sound t′-i eq₂ ⊢γ ⊢Γ
        t≡t′           = really-remove-weaken-subst-sound n eq₁
                           (term₂ ⊢t′)
    in
    PE.subst (flip (_⊢_∷_ _) _) (PE.sym t≡t′) ⊢t′

  -- Soundness for equal-ty (1+ n).

  equal-ty-1+-sound :
    OK (equal-ty (1+ n) Γ A₁ A₂) tt γ st →
    Contexts-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A₁ ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A₂ ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A₁ ⌝ γ ≡ ⌜ A₂ ⌝ γ
  equal-ty-1+-sound {A₁} {A₂} {γ} eq ⊢γ ⊢A₁ ⊢A₂ =
    let open TyR

        inv A₁′ eq₁ eq  = inv->>= (inv-register eq)
        inv A₂′ eq₂ eq₃ = inv->>= eq

        A₁≡A₁′ = red-ty-sound eq₁ ⊢γ ⊢A₁
        A₂≡A₂′ = red-ty-sound eq₂ ⊢γ ⊢A₂
    in
    ⌜ A₁ ⌝ γ   ≡⟨ A₁≡A₁′ ⟩⊢
    ⌜ A₁′ ⌝ γ  ≡⟨ equal-ty-red-sound A₁′ A₂′ eq₃ ⊢γ
                    (wf-⊢≡ A₁≡A₁′ .proj₂) (wf-⊢≡ A₂≡A₂′ .proj₂) ⟩⊢
    ⌜ A₂′ ⌝ γ  ≡˘⟨ A₂≡A₂′ ⟩⊢∎
    ⌜ A₂ ⌝ γ   ∎

  -- Soundness for equal-tm (1+ n).

  equal-tm-1+-sound :
    OK (equal-tm (1+ n) Γ t₁ t₂ A) tt γ st →
    Contexts-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ∷ ⌜ A ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ≡ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ
  equal-tm-1+-sound {t₁} {t₂} {A} {γ} eq ⊢γ ⊢t₁ ⊢t₂ =
    let open TmR

        inv A′  eq₁ eq  = inv->>= (inv-register eq)
        inv t₁′ eq₂ eq  = inv->>= eq
        inv t₂′ eq₃ eq₄ = inv->>= eq

        A≡A′   = red-ty-sound eq₁ ⊢γ (wf-⊢∷ ⊢t₁)
        t₁≡t₁′ = red-tm-sound eq₂ ⊢γ (conv ⊢t₁ A≡A′)
        t₂≡t₂′ = red-tm-sound eq₃ ⊢γ (conv ⊢t₂ A≡A′)
    in
             ∷ ⌜ A ⌝ γ    ⟨ A≡A′ ⟩≡∷
    ⌜ t₁ ⌝ γ ∷ ⌜ A′ ⌝ γ  ≡⟨ t₁≡t₁′ ⟩⊢∷
    ⌜ t₁′ ⌝ γ            ≡⟨ equal-tm-red-sound A′ eq₄ ⊢γ
                              (wf-⊢≡∷ t₁≡t₁′ .proj₂ .proj₂)
                              (wf-⊢≡∷ t₂≡t₂′ .proj₂ .proj₂) ⟩⊢
    ⌜ t₂′ ⌝ γ            ≡˘⟨ t₂≡t₂′ ⟩⊢∎
    ⌜ t₂ ⌝ γ             ∎

  -- Soundness for normalise-level b (1+ n).

  normalise-level-1+-sound :
    OK (normalise-level b (1+ n) Γ l) nf γ st →
    Contexts-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ Term[]→Lvl l ⌝ γ ∷Level →
    ⌜ Γ ⌝ᶜ γ ⊢⌜ nf ⌝ⁿ γ ∷Level ×
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ Term[]→Lvl l ⌝ γ ≡ ⌜ nf ⌝ⁿ γ ∷Level
  normalise-level-1+-sound eq ⊢γ ⊢l
    with inv->>= (inv-register eq)
  … | inv (l′ , _) eq₁ eq₂ =
    let l≡l′ = Term[]→Lvl-cong $
               really-remove-weaken-subst-sound n eq₁ (level ⊢l)
    in
    Σ.map idᶠ (PE.subst (flip (_⊢_≡_∷Level _) _) (PE.sym l≡l′)) $
    normalise-level′-sound (is-perhaps-level? l′) eq₂ ⊢γ $
    PE.subst (_⊢_∷Level _) l≡l′ ⊢l

  -- Soundness for equal-ne-inf (1+ n).

  equal-ne-inf-1+-sound :
    OK (equal-ne-inf (1+ n) Γ t₁ t₂) A γ st →
    Contexts-wf (Γ .defs) γ →
    ⊢ ⌜ Γ ⌝ᶜ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ≡ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ
  equal-ne-inf-1+-sound eq ⊢γ ⊢Γ
    with inv->>= (inv-register eq)
  … | inv t₁-t₂-ee _ eq =
    equal-ne-inf′-sound t₁-t₂-ee eq ⊢γ ⊢Γ

  -- P (1+ n) is inhabited.

  inhabited : P (1+ n)
  inhabited = λ where
    .P.red-ty-sound          → red-ty-1+-sound
    .P.red-tm-sound          → red-tm-1+-sound
    .P.check-type-sound      → check-type-1+-sound
    .P.check-level-sound     → check-level-1+-sound
    .P.check-sound           → check-1+-sound
    .P.infer-sound           → infer-1+-sound
    .P.equal-ty-sound        → equal-ty-1+-sound
    .P.equal-tm-sound        → equal-tm-1+-sound
    .P.normalise-level-sound → normalise-level-1+-sound
    .P.equal-ne-inf-sound    → equal-ne-inf-1+-sound

private opaque

  -- P n is inhabited for every n.

  P-inhabited : ∀ n → P n
  P-inhabited 0 = λ where
    .P.red-ty-sound          not-ok
    .P.red-tm-sound          not-ok
    .P.check-type-sound      not-ok
    .P.check-level-sound     not-ok
    .P.check-sound           not-ok
    .P.infer-sound           not-ok
    .P.equal-ty-sound        not-ok
    .P.equal-tm-sound        not-ok
    .P.normalise-level-sound not-ok
    .P.equal-ne-inf-sound    not-ok
  P-inhabited (1+ n) =
    P-1+.inhabited (P-inhabited n)

opaque

  -- Soundness for check-type.

  check-type-sound :
    ∀ γ (Γ : Cons c m n) A n →
    check-type n Γ A .run (γ # []) PE.≡ inj₂ A′ →
    Contexts-wf (Γ .defs) γ →
    ⊢ ⌜ Γ ⌝ᶜ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A ⌝ γ
  check-type-sound _ _ _ n eq ⊢γ ⊢Γ =
    wf-⊢≡ (P.check-type-sound (P-inhabited n) (ok eq) ⊢γ ⊢Γ) .proj₁

opaque

  -- Soundness for check-level.

  check-level-sound :
    ∀ γ (Γ : Cons c m n) l n →
    check-level n Γ l .run (γ # []) PE.≡ inj₂ l′ →
    Contexts-wf (Γ .defs) γ →
    ⊢ ⌜ Γ ⌝ᶜ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ Term[]→Lvl l ⌝ γ ∷Level
  check-level-sound _ _ _ n eq ⊢γ ⊢Γ =
    wf-⊢≡∷L (P.check-level-sound (P-inhabited n) (ok eq) ⊢γ ⊢Γ) .proj₁

opaque

  -- Soundness for check.

  check-sound :
    ∀ γ (Γ : Cons c m n) t A n →
    check n Γ t A .run (γ # []) PE.≡ inj₂ t′ →
    Contexts-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ∷ ⌜ A ⌝ γ
  check-sound _ _ _ _ n eq ⊢γ ⊢A =
    wf-⊢≡∷ (P.check-sound (P-inhabited n) (ok eq) ⊢γ ⊢A) .proj₂ .proj₁

opaque

  -- Soundness for equal-con.

  equal-con-sound :
    ∀ γ (Γ : Cons c m n) Δ n →
    equal-con n Γ Δ .run (γ # []) PE.≡ inj₂ tt →
    Contexts-wf (Γ .defs) γ →
    ⊢ ⌜ Γ ⌝ᶜ γ →
    ⌜ Γ ⌝ᶜ γ .defs »⊢ ⌜ Δ ⌝ᶜᵛ γ →
    ⌜ Γ ⌝ᶜ γ .defs »⊢ ⌜ Γ ⌝ᶜ γ .vars ≡ ⌜ Δ ⌝ᶜᵛ γ
  equal-con-sound _ Γ _ _ eq =
    Lemmas.equal-con-sound (P-inhabited _) {Γ = Γ} (ok eq)

opaque

  -- Soundness for check-sub.

  check-sub-sound :
    ∀ γ (∇ : DCon c m) Δ₂ (σ : Subst c n₂ n₁) Δ₁ n →
    check-sub n ∇ Δ₂ σ Δ₁ .run (γ # []) PE.≡ inj₂ σ′ →
    Contexts-wf ∇ γ →
    ⌜ ∇ ⌝ᶜᵈ γ »⊢ ⌜ Δ₂ ⌝ᶜᵛ γ →
    ⌜ ∇ ⌝ᶜᵈ γ »⊢ ⌜ Δ₁ ⌝ᶜᵛ γ →
    ⌜ ∇ ⌝ᶜᵈ γ » ⌜ Δ₂ ⌝ᶜᵛ γ ⊢ˢʷ ⌜ σ ⌝ˢ γ ∷ ⌜ Δ₁ ⌝ᶜᵛ γ
  check-sub-sound _ _ _ σ _ _ eq ⊢γ ⊢Δ₂ ⊢Δ₁ =
    wf-⊢ˢʷ≡∷
      (Lemmas.check-sub-sound (P-inhabited _) σ (ok eq) ⊢γ ⊢Δ₂ ⊢Δ₁)
      .proj₂ .proj₁

opaque

  -- Soundness for equal-ty.

  equal-ty-sound :
    ∀ γ (Γ : Cons c m n) A₁ A₂ n →
    equal-ty n Γ A₁ A₂ .run (γ # []) PE.≡ inj₂ tt →
    Contexts-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A₁ ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A₂ ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A₁ ⌝ γ ≡ ⌜ A₂ ⌝ γ
  equal-ty-sound _ _ _ _ n eq = P.equal-ty-sound (P-inhabited n) (ok eq)

opaque

  -- Soundness for equal-level.

  equal-level-sound :
    ∀ γ (Γ : Cons c m n) (l₁ l₂ : Term[ c , k ] n) n →
    equal-level n Γ l₁ l₂ .run (γ # []) PE.≡ inj₂ tt →
    Contexts-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ Term[]→Lvl l₁ ⌝ γ ∷Level →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ Term[]→Lvl l₂ ⌝ γ ∷Level →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ Term[]→Lvl l₁ ⌝ γ ≡ ⌜ Term[]→Lvl l₂ ⌝ γ ∷Level
  equal-level-sound _ _ _ _ n eq =
    Lemmas.equal-level-sound (P-inhabited n) (ok eq)

opaque

  -- Soundness for equal-tm.

  equal-tm-sound :
    ∀ γ (Γ : Cons c m n) t₁ t₂ A n →
    equal-tm n Γ t₁ t₂ A .run (γ # []) PE.≡ inj₂ tt →
    Contexts-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ∷ ⌜ A ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ≡ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ
  equal-tm-sound _ _ _ _ _ n eq =
    P.equal-tm-sound (P-inhabited n) (ok eq)

opaque

  -- Soundness for check-type-and-term.

  check-type-and-term-sound′ :
    ∀ n →
    OK (check-type-and-term n Γ t A) (t′ , A′) γ st →
    Contexts-wf (Γ .defs) γ →
    ⊢ ⌜ Γ ⌝ᶜ γ →
    (⌜ Γ ⌝ᶜ γ ⊢ ⌜ A ⌝ γ ≡ ⌜ A′ ⌝ γ) ×
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ≡ ⌜ t′ ⌝ γ ∷ ⌜ A ⌝ γ
  check-type-and-term-sound′ n eq ⊢γ ⊢Γ
    with inv->>= eq
  … | inv _ eq₁ eq
    with inv->>= eq
  … | inv _ eq₂ ok! =
    let A≡A′    = P.check-type-sound (P-inhabited n) eq₁ ⊢γ ⊢Γ
        _ , ⊢A′ = wf-⊢≡ A≡A′
        t≡t′    = P.check-sound (P-inhabited n) eq₂ ⊢γ ⊢A′
    in
    A≡A′ , conv t≡t′ (sym A≡A′)

opaque

  -- Soundness for check-type-and-term.

  check-type-and-term-sound :
    ∀ γ (Γ : Cons c m n) t A n →
    check-type-and-term n Γ t A .run (γ # []) PE.≡ inj₂ (t′ , A′) →
    Contexts-wf (Γ .defs) γ →
    ⊢ ⌜ Γ ⌝ᶜ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ∷ ⌜ A ⌝ γ
  check-type-and-term-sound _ _ _ _ n eq ⊢γ ⊢Γ =
    wf-⊢≡∷ (check-type-and-term-sound′ n (ok eq) ⊢γ ⊢Γ .proj₂)
      .proj₂ .proj₁

opaque

  -- Soundness for check-and-equal-ty.

  check-and-equal-ty-sound :
    ∀ γ (Γ : Cons c m n) A₁ A₂ n →
    check-and-equal-ty n Γ A₁ A₂ .run (γ # []) PE.≡ inj₂ A →
    Contexts-wf (Γ .defs) γ →
    ⊢ ⌜ Γ ⌝ᶜ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A₁ ⌝ γ ≡ ⌜ A₂ ⌝ γ
  check-and-equal-ty-sound _ _ _ _ n eq ⊢γ ⊢Γ =
    Lemmas.check-and-equal-ty-sound (P-inhabited n) (ok eq) ⊢γ ⊢Γ .proj₂

opaque

  -- Soundness for check-and-equal-level.

  check-and-equal-level-sound :
    ∀ γ (Γ : Cons c m n) l₁ l₂ n →
    check-and-equal-level n Γ l₁ l₂ .run (γ # []) PE.≡ inj₂ l →
    Contexts-wf (Γ .defs) γ →
    ⊢ ⌜ Γ ⌝ᶜ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ Term[]→Lvl l₁ ⌝ γ ≡ ⌜ Term[]→Lvl l ⌝ γ ∷Level ×
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ Term[]→Lvl l₁ ⌝ γ ≡ ⌜ Term[]→Lvl l₂ ⌝ γ ∷Level
  check-and-equal-level-sound _ _ _ _ n eq =
    Lemmas.check-and-equal-level-sound (P-inhabited n) (ok eq)

opaque

  -- Soundness for check-and-equal-tm.

  check-and-equal-tm-sound :
    ∀ γ (Γ : Cons c m n) t₁ t₂ A n →
    check-and-equal-tm n Γ t₁ t₂ A .run (γ # []) PE.≡ inj₂ t →
    Contexts-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A ⌝ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ≡ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ
  check-and-equal-tm-sound _ _ _ _ _ n eq ⊢γ ⊢A =
    Lemmas.check-and-equal-tm-sound (P-inhabited n) (ok eq) ⊢γ ⊢A .proj₂

opaque

  -- Soundness for check-and-equal-type-and-terms.

  check-and-equal-type-and-terms-sound′ :
    ∀ n →
    OK (check-and-equal-type-and-terms n Γ t₁ t₂ A) tt γ st →
    Contexts-wf (Γ .defs) γ →
    ⊢ ⌜ Γ ⌝ᶜ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ≡ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ
  check-and-equal-type-and-terms-sound′ n eq ⊢γ ⊢Γ =
    let inv _ eq₁ eq = inv->>= eq
        inv _ eq₂ _  = inv->>= eq
        A≡A′         = P.check-type-sound (P-inhabited n) eq₁ ⊢γ ⊢Γ
        _ , ⊢A′      = wf-⊢≡ A≡A′
        _ , t₁≡t₂    = Lemmas.check-and-equal-tm-sound (P-inhabited n)
                         eq₂ ⊢γ ⊢A′
    in
    conv t₁≡t₂ (sym A≡A′)

opaque

  -- Soundness for check-and-equal-type-and-terms.

  check-and-equal-type-and-terms-sound :
    ∀ γ (Γ : Cons c m n) t₁ t₂ A n →
    check-and-equal-type-and-terms n Γ t₁ t₂ A .run (γ # []) PE.≡
      inj₂ tt →
    Contexts-wf (Γ .defs) γ →
    ⊢ ⌜ Γ ⌝ᶜ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ≡ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ
  check-and-equal-type-and-terms-sound _ _ _ _ _ n eq =
    check-and-equal-type-and-terms-sound′ n (ok eq)

opaque

  -- Soundness for equal-sub.

  equal-sub-sound′ :
    ∀ Δ →
    OK (equal-sub n Γ σ₁ σ₂ Δ) tt γ st →
    Contexts-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ .defs »⊢ ⌜ Δ ⌝ᶜᵛ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ˢʷ ⌜ σ₁ ⌝ˢ γ ∷ ⌜ Δ ⌝ᶜᵛ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ˢʷ ⌜ σ₂ ⌝ˢ γ ∷ ⌜ Δ ⌝ᶜᵛ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ˢʷ ⌜ σ₁ ⌝ˢ γ ≡ ⌜ σ₂ ⌝ˢ γ ∷ ⌜ Δ ⌝ᶜᵛ γ
  equal-sub-sound′ ε ok! _ _ ⊢σ₁ _ =
    ⊢ˢʷ≡∷ε⇔ .proj₂ (wf-⊢ˢʷ∷ ⊢σ₁)
  equal-sub-sound′ {n} {σ₁} {σ₂} (Δ ∙ B) eq ⊢γ (∙ ⊢B) ⊢σ₁ ⊢σ₂ =
    let inv _ eq₁ eq₂ = inv->>= eq
        ⊢σ₁₊ , ⊢σ₁₀   = ⊢ˢʷ∷∙⇔ .proj₁ ⊢σ₁
        ⊢σ₂₊ , ⊢σ₂₀   = ⊢ˢʷ∷∙⇔ .proj₁ ⊢σ₂
        σ₁₊≡σ₂₊       =
          cast-⊢ˢʷ≡∷ (⌜tailₛ⌝ˢ σ₁) (⌜tailₛ⌝ˢ σ₂) $
          equal-sub-sound′ Δ eq₁ ⊢γ (wf ⊢B)
            (cast-⊢ˢʷ∷ (PE.sym ∘→ ⌜tailₛ⌝ˢ σ₁) ⊢σ₁₊)
            (cast-⊢ˢʷ∷ (PE.sym ∘→ ⌜tailₛ⌝ˢ σ₂) ⊢σ₂₊)
        B[]≡B[] =
          substVar-to-subst (⌜tailₛ⌝ˢ σ₁) (⌜ B ⌝ _)
    in
    ⊢ˢʷ≡∷∙⇔′ ⊢B .proj₂
      ( σ₁₊≡σ₂₊
      , PE.subst₃ (_⊢_≡_∷_ _) (⌜headₛ⌝ σ₁) (⌜headₛ⌝ σ₂) B[]≡B[]
          (P.equal-tm-sound (P-inhabited n) eq₂ ⊢γ
             (PE.subst₂ (_⊢_∷_ _)
                (PE.sym (⌜headₛ⌝ σ₁)) (PE.sym B[]≡B[])
                ⊢σ₁₀)
             (PE.subst₂ (_⊢_∷_ _)
                (PE.sym (⌜headₛ⌝ σ₂)) (PE.sym B[]≡B[]) $
              conv ⊢σ₂₀ (sym (subst-⊢≡ (refl ⊢B) σ₁₊≡σ₂₊))))
      )
  equal-sub-sound′ {Γ} base eq _ _ ⊢σ₁ _
    with inv->>= eq
  … | inv (both _ PE.refl) _ eq =
    refl-⊢ˢʷ≡∷ (equal-sub″-sound (Γ .defs) eq (wf-⊢ˢʷ∷ ⊢σ₁))

opaque

  -- Soundness for equal-sub.

  equal-sub-sound :
    ∀ γ (Γ : Cons c m n₂) (σ₁ σ₂ : Subst c n₂ n₁) Δ n →
    equal-sub n Γ σ₁ σ₂ Δ .run (γ # []) PE.≡ inj₂ tt →
    Contexts-wf (Γ .defs) γ →
    ⌜ Γ ⌝ᶜ γ .defs »⊢ ⌜ Δ ⌝ᶜᵛ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ˢʷ ⌜ σ₁ ⌝ˢ γ ∷ ⌜ Δ ⌝ᶜᵛ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ˢʷ ⌜ σ₂ ⌝ˢ γ ∷ ⌜ Δ ⌝ᶜᵛ γ →
    ⌜ Γ ⌝ᶜ γ ⊢ˢʷ ⌜ σ₁ ⌝ˢ γ ≡ ⌜ σ₂ ⌝ˢ γ ∷ ⌜ Δ ⌝ᶜᵛ γ
  equal-sub-sound _ _ _ _ Δ _ eq = equal-sub-sound′ Δ (ok eq)

opaque

  -- Soundness for check-con.

  check-con-sound′ :
    ∀ (Δ : Con c n) {n} →
    OK (check-con n ∇ Δ) Δ′ γ st →
    Contexts-wf ∇ γ →
    (Base-con-allowed c → ⌜ ∇ ⌝ᶜᵈ γ »⊢ γ .⌜base⌝ .vars) →
    » ⌜ ∇ ⌝ᶜᵈ γ →
    ⌜ ∇ ⌝ᶜᵈ γ »⊢ ⌜ Δ ⌝ᶜᵛ γ ≡ ⌜ Δ′ ⌝ᶜᵛ γ
  check-con-sound′ (base {b}) ok! _ ⊢base _ =
    reflConEq (⊢base b)
  check-con-sound′ ε ok! _ _ »∇ =
    reflConEq (ε »∇)
  check-con-sound′ (Δ ∙ _) {n} eq ⊢γ ⊢base »∇
    with inv->>= eq
  … | inv _ eq₁ eq
    with inv->>= eq
  … | inv _ eq₂ ok! =
    let Δ≡Δ′        = check-con-sound′ Δ eq₁ ⊢γ ⊢base »∇
        _ , ⊢Δ′ , _ = contextConvSubst Δ≡Δ′
        A≡A′        = P.check-type-sound (P-inhabited n) eq₂ ⊢γ ⊢Δ′
    in
    Δ≡Δ′ ∙ stability (symConEq Δ≡Δ′) A≡A′

opaque

  -- Soundness for check-con.

  check-con-sound :
    ∀ γ (∇ : DCon c m) (Δ : Con c n) n →
    check-con n ∇ Δ .run (γ # []) PE.≡ inj₂ Δ′ →
    Contexts-wf ∇ γ →
    (Base-con-allowed c → ⌜ ∇ ⌝ᶜᵈ γ »⊢ γ .⌜base⌝ .vars) →
    » ⌜ ∇ ⌝ᶜᵈ γ →
    ⌜ ∇ ⌝ᶜᵈ γ »⊢ ⌜ Δ ⌝ᶜᵛ γ
  check-con-sound _ _ Γ _ eq ⊢γ ⊢base »∇ =
    contextConvSubst (check-con-sound′ Γ (ok eq) ⊢γ ⊢base »∇) .proj₁

opaque

  -- Soundness for check-dcon.

  check-dcon-sound′ :
    (∇ : DCon c m) →
    OK (check-dcon n ∇) tt γ st →
    Constraints-satisfied γ →
    » γ .⌜base⌝ .defs →
    » ⌜ ∇ ⌝ᶜᵈ γ
  check-dcon-sound′ (base nothing) _ _ ⊢base =
    ⊢base
  check-dcon-sound′ (base (just _)) eq ⊢cs ⊢base =
    let L.lift eq = inv-require′⁰ ⊢cs unfolding-mode-transitive eq in
    Transitive.unfold-» eq ⊢base
  check-dcon-sound′ ε _ _ _ =
    ε
  check-dcon-sound′ {n} (∇ ∙⟨ tra ⟩[ _ ∷ _ ]) eq ⊢cs ⊢base =
    let inv ms≡0 _   eq  = inv->>= eq
        inv _    eq₁ eq  = inv->>= eq
        inv _    eq₂ _   = inv->>= eq
        ⊢γ               = record
                             { metas-wf       = Meta-con-wf-empty ms≡0
                             ; constraints-wf = ⊢cs
                             }
        _ , t≡t′         = check-type-and-term-sound′ n eq₂ ⊢γ
                             (ε (check-dcon-sound′ ∇ eq₁ ⊢cs ⊢base))
        _ , ⊢t , _       = wf-⊢≡∷ t≡t′
    in
    ∙ᵗ[ ⊢t ]
  check-dcon-sound′ {n} (∇ ∙⟨ opa _ ⟩[ _ ∷ _ ]) eq ⊢cs ⊢base =
    let inv ms≡0 _   eq  = inv->>= eq
        inv _    eq₁ eq  = inv->>= eq
        inv _    eq₂ eq  = inv->>= eq
        inv _    eq₃ eq  = inv->>= eq
        inv _    eq₄ eq₅ = inv->>= eq

        opacity-ok             = inv-require′⁰ ⊢cs opacity-allowed eq₄
        L.lift unfolding≡trans =
          inv-require′⁰ ⊢cs unfolding-mode-transitive eq₅

        ⊢γ′ = record
          { metas-wf       = Meta-con-wf-empty ms≡0
          ; constraints-wf = ⊢cs
          }

        ⊢γ″ = record
          { metas-wf       = Meta-con-wf-empty ms≡0
          ; constraints-wf = ⊢cs
          }

        »∇     = check-dcon-sound′ ∇ eq₁ ⊢cs ⊢base
        A≡A′   = P.check-type-sound (P-inhabited n) eq₂ ⊢γ′ (ε »∇)
        ⊢A , _ = wf-⊢≡ A≡A′
        ⊢t     =
          PE.subst₃ _⊢_∷_
            (PE.cong (flip U._»_ _) (⌜Trans⌝ᶜᵈ ∇)) PE.refl PE.refl $
          wf-⊢≡∷
            (P.check-sound (P-inhabited n) eq₃ ⊢γ″
               (PE.subst (flip _⊢_ _)
                  (PE.cong (flip U._»_ _) (PE.sym (⌜Trans⌝ᶜᵈ ∇))) $
                Transitive.unfold-⊢ unfolding≡trans ⊢A))
            .proj₂ .proj₁
    in
    ∙ᵒ⟨ opacity-ok ⟩[ ⊢t ∷ ⊢A ]

opaque

  -- Soundness for check-dcon.

  check-dcon-sound :
    ∀ γ (∇ : DCon c m) n →
    check-dcon n ∇ .run (γ # []) PE.≡ inj₂ tt →
    Constraints-satisfied γ →
    » γ .⌜base⌝ .defs →
    » ⌜ ∇ ⌝ᶜᵈ γ
  check-dcon-sound _ ∇ _ eq = check-dcon-sound′ ∇ (ok eq)

opaque

  -- Soundness for check-cons.

  check-cons-sound′ :
    ∀ (Γ : Cons c m n) {n} →
    OK (check-cons n Γ) Γ′ γ st →
    Contexts-wf (Γ .defs) γ →
    » γ .⌜base⌝ .defs →
    (Base-con-allowed c → ⌜ Γ .defs ⌝ᶜᵈ γ »⊢ γ .⌜base⌝ .vars) →
    Γ .defs PE.≡ Γ′ .defs ×
    ⌜ Γ .defs ⌝ᶜᵈ γ »⊢ ⌜ Γ .vars ⌝ᶜᵛ γ ≡ ⌜ Γ′ .vars ⌝ᶜᵛ γ
  check-cons-sound′ (∇ » Γ) eq ⊢γ ⊢base₁ ⊢base₂
    using inv _ eq₁ eq ← inv->>= eq
    with inv->>= eq
  … | inv _ eq₂ ok! =
    let »∇ = check-dcon-sound′ ∇ eq₁ (⊢γ .constraints-wf) ⊢base₁ in
    PE.refl , check-con-sound′ Γ eq₂ ⊢γ ⊢base₂ »∇

opaque

  -- Soundness for check-cons.

  check-cons-sound :
    ∀ γ (Γ : Cons c m n) n →
    check-cons n Γ .run (γ # []) PE.≡ inj₂ Γ′ →
    Contexts-wf (Γ .defs) γ →
    » γ .⌜base⌝ .defs →
    (Base-con-allowed c → ⌜ Γ .defs ⌝ᶜᵈ γ »⊢ γ .⌜base⌝ .vars) →
    ⊢ ⌜ Γ ⌝ᶜ γ
  check-cons-sound _ Γ _ eq ⊢γ ⊢base₁ ⊢base₂ =
    contextConvSubst
      (check-cons-sound′ Γ (ok eq) ⊢γ ⊢base₁ ⊢base₂ .proj₂)
      .proj₁

opaque

  -- Soundness for check-cons-type-and-term.

  check-cons-type-and-term-sound′ :
    ∀ (Γ : Cons c m n) {n} →
    OK (check-cons-type-and-term n Γ t A) tt γ st →
    Contexts-wf (Γ .defs) γ →
    » γ .⌜base⌝ .defs →
    (Base-con-allowed c → ⌜ Γ .defs ⌝ᶜᵈ γ »⊢ γ .⌜base⌝ .vars) →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ∷ ⌜ A ⌝ γ
  check-cons-type-and-term-sound′ Γ {n} eq ⊢γ ⊢base₁ ⊢base₂
    with inv->>= eq
  … | inv _ eq₁ eq
    using inv _ eq₂ _ ← inv->>= eq
    with check-cons-sound′ Γ eq₁ ⊢γ ⊢base₁ ⊢base₂
  … | PE.refl , Δ≡Δ′ =
    let _ , ⊢Δ′ , _ = contextConvSubst Δ≡Δ′
        _ , t≡t′    = check-type-and-term-sound′ n eq₂ ⊢γ ⊢Δ′
        _ , ⊢t , _  = wf-⊢≡∷ t≡t′
    in
    stability (symConEq Δ≡Δ′) ⊢t

opaque

  -- Soundness for check-cons-type-and-term.

  check-cons-type-and-term-sound :
    ∀ γ (Γ : Cons c m n) t A n →
    check-cons-type-and-term n Γ t A .run (γ # []) PE.≡ inj₂ tt →
    Contexts-wf (Γ .defs) γ →
    » γ .⌜base⌝ .defs →
    (Base-con-allowed c → ⌜ Γ .defs ⌝ᶜᵈ γ »⊢ γ .⌜base⌝ .vars) →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t ⌝ γ ∷ ⌜ A ⌝ γ
  check-cons-type-and-term-sound _ Γ _ _ _ eq =
    check-cons-type-and-term-sound′ Γ (ok eq)

opaque

  -- Soundness for check-and-equal-cons-type-and-terms.

  check-and-equal-cons-type-and-terms-sound′ :
    ∀ (Γ : Cons c m n) {n} →
    OK (check-and-equal-cons-type-and-terms n Γ t₁ t₂ A) tt γ st →
    Contexts-wf (Γ .defs) γ →
    » γ .⌜base⌝ .defs →
    (Base-con-allowed c → ⌜ Γ .defs ⌝ᶜᵈ γ »⊢ γ .⌜base⌝ .vars) →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ≡ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ
  check-and-equal-cons-type-and-terms-sound′ Γ {n} eq ⊢γ ⊢base₁ ⊢base₂
    with inv->>= eq
  … | inv _ eq₁ eq₂
    with check-cons-sound′ Γ eq₁ ⊢γ ⊢base₁ ⊢base₂
  … | PE.refl , Δ≡Δ′ =
    let _ , ⊢Δ′ , _ = contextConvSubst Δ≡Δ′
        t₁≡t₂       = check-and-equal-type-and-terms-sound′ n eq₂ ⊢γ ⊢Δ′
    in
    stability (symConEq Δ≡Δ′) t₁≡t₂

opaque

  -- Soundness for check-and-equal-cons-type-and-terms.

  check-and-equal-cons-type-and-terms-sound :
    ∀ γ (Γ : Cons c m n) t₁ t₂ A n →
    check-and-equal-cons-type-and-terms n Γ t₁ t₂ A .run (γ # []) PE.≡
      inj₂ tt →
    Contexts-wf (Γ .defs) γ →
    » γ .⌜base⌝ .defs →
    (Base-con-allowed c → ⌜ Γ .defs ⌝ᶜᵈ γ »⊢ γ .⌜base⌝ .vars) →
    ⌜ Γ ⌝ᶜ γ ⊢ ⌜ t₁ ⌝ γ ≡ ⌜ t₂ ⌝ γ ∷ ⌜ A ⌝ γ
  check-and-equal-cons-type-and-terms-sound _ Γ _ _ _ _ eq =
    check-and-equal-cons-type-and-terms-sound′ Γ (ok eq)
