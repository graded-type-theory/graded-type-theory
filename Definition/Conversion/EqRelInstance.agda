------------------------------------------------------------------------
-- The algorithmic equality is (in the absence of equality reflection)
-- an instance of the abstract set of equality relations
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Conversion.EqRelInstance
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  ⦃ no-equality-reflection : No-equality-reflection ⦄
  where

open import Definition.Untyped M
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Properties M
open import Definition.Untyped.Whnf M type-variant
open import Definition.Typed R
open import Definition.Typed.EqRelInstance R
  using () renaming (eqRelInstance to eqRelInstance′)
open import Definition.Typed.EqualityRelation.Instance R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Stability R
open import Definition.Typed.Substitution R
open import Definition.Typed.Syntactic R
open import Definition.Typed.Weakening R using (_»_∷ʷ_⊇_; wkEq)
open import Definition.Typed.Weakening.Definition R
open import Definition.Typed.Well-formed R
open import Definition.Conversion R
open import Definition.Conversion.Reduction R
open import Definition.Conversion.Universe R
open import Definition.Conversion.Stability R
open import Definition.Conversion.Soundness R
open import Definition.Conversion.Lift R
open import Definition.Conversion.Conversion R
open import Definition.Conversion.Symmetry R
open import Definition.Conversion.Transitivity R
open import Definition.Conversion.Weakening R
open import Definition.Conversion.Weakening.Definition R
open import Definition.Typed.EqualityRelation R
import Definition.Typed.EqualityRelation.Instance
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Consequences.Equality R
open import Definition.Typed.Consequences.Reduction R

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Level
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Unit

private
  variable
    m n κ : Nat
    ∇ ∇′ : DCon (Term 0) κ
    Η : Con Term _
    Γ : Cons _ _
    A₁ A₂ B₁ B₂ t₁ t₂ u₁ u₂ v₁ v₂ w₁ w₂ : Term _
    ρ : Wk m n
    p p₁ p₂ p′ q q′ q₁ q₂ r r′ : M
    s : Strength
    l : Universe-level

-- Algorithmic equality of neutrals with injected conversion.

infix 4 _⊢_~_∷_

record _⊢_~_∷_ (Γ : Cons κ n) (k l A : Term n) : Set a where
  inductive
  no-eta-equality
  pattern
  constructor ↑
  field
    {B} : Term n
    A≡B : Γ ⊢ A ≡ B
    k~↑l : Γ ⊢ k ~ l ↑ B

-- Properties of algorithmic equality of neutrals with injected conversion.

private module Lemmas where

  ~-var : ∀ {x A} → Γ ⊢ var x ∷ A → Γ ⊢ var x ~ var x ∷ A
  ~-var x =
    let ⊢A = syntacticTerm x
    in  ↑ (refl ⊢A) (var-refl x PE.refl)

  ~-defn : ∀ {α A A′}
         → Γ ⊢ defn α ∷ A
         → α ↦⊘∷ A′ ∈ Γ .defs
         → Γ ⊢ defn α ~ defn α ∷ A
  ~-defn α α↦⊘ =
    let ⊢A = syntacticTerm α
    in  ↑ (refl ⊢A) (defn-refl α α↦⊘ PE.refl)

  ~-app : ∀ {f g a b F G}
        → Γ ⊢ f ~ g ∷ Π p , q ▷ F ▹ G
        → Γ ⊢ a [conv↑] b ∷ F
        → Γ ⊢ f ∘⟨ p ⟩ a ~ g ∘⟨ p ⟩ b ∷ G [ a ]₀
  ~-app (↑ A≡B x) x₁ =
    let _ , ⊢B = syntacticEq A≡B
        B′ , whnfB′ , D = whNorm ⊢B
        ΠFG≡B′ = trans A≡B (subset* D)
        _ , ⊢f , _ = syntacticEqTerm (soundnessConv↑Term x₁)
    in
    case Π≡A ΠFG≡B′ whnfB′ of λ {
      (H , E , B≡ΠHE) →
    case ΠΣ-injectivity (PE.subst (λ x → _ ⊢ _ ≡ x) B≡ΠHE ΠFG≡B′) of λ {
      (F≡H , G≡E , _ , _) →
    ↑ (G≡E (refl ⊢f))
      (app-cong
         (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) B≡ΠHE
            ([~] _ (D , whnfB′) x))
         (convConv↑Term F≡H x₁)) }}

  ~-fst :
    ∀ {p r F G} →
    Γ ⊢ p ~ r ∷ Σˢ p′ , q ▷ F ▹ G →
    Γ ⊢ fst p′ p ~ fst p′ r ∷ F
  ~-fst (↑ A≡B p~r) =
    case syntacticEq A≡B of λ (_ , ⊢B) →
    case whNorm ⊢B of λ (B′ , whnfB′ , D) →
    case trans A≡B (subset* D) of λ ΣFG≡B′ →
    case Σ≡A ΣFG≡B′ whnfB′ of λ where
      (H , _ , PE.refl) →
        case ΠΣ-injectivity ΣFG≡B′ of λ where
          (F≡H , _ , _ , _) →
            ↑ F≡H (fst-cong ([~] _ (D , whnfB′) p~r))

  ~-snd :
    ∀ {p r F G} →
    Γ ⊢ p ~ r ∷ Σ p′ , q ▷ F ▹ G →
    Γ ⊢ snd p′ p ~ snd p′ r ∷ G [ fst p′ p ]₀
  ~-snd (↑ A≡B p~r) =
    case syntacticEq A≡B of λ (⊢ΣFG , ⊢B) →
    case whNorm ⊢B of λ (B′ , whnfB′ , D) →
    case trans A≡B (subset* D) of λ ΣFG≡B′ →
    case Σ≡A ΣFG≡B′ whnfB′ of λ where
      (_ , E , PE.refl) →
        case ΠΣ-injectivity ΣFG≡B′ of λ where
          (_ , G≡E , _ , _) →
            let p~r↓       = [~] _ (D , whnfB′) p~r
                _ , ⊢G , _ = inversion-ΠΣ ⊢ΣFG
                _ , ⊢p , _ = syntacticEqTerm (soundness~↑ p~r)
                ⊢fst       = fstⱼ ⊢G (conv ⊢p (sym A≡B))
            in
            ↑ (G≡E (refl ⊢fst)) (snd-cong p~r↓)

  ~-natrec : ∀ {z z′ s s′ n n′ F F′}
           → Γ »∙ ℕ ⊢ F [conv↑] F′ →
        Γ ⊢ z [conv↑] z′ ∷ (F [ zero ]₀) →
        Γ »∙ ℕ »∙ F ⊢ s [conv↑] s′ ∷ F [ suc (var x1) ]↑² →
        Γ ⊢ n ~ n′ ∷ ℕ →
        Γ ⊢ natrec p q r F z s n ~ natrec p q r F′ z′ s′ n′ ∷ (F [ n ]₀)
  ~-natrec x x₁ x₂ (↑ A≡B x₄) =
    let _ , ⊢B = syntacticEq A≡B
        B′ , whnfB′ , D = whNorm ⊢B
        ℕ≡B′ = trans A≡B (subset* D)
        B≡ℕ = ℕ≡A ℕ≡B′ whnfB′
        k~l′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) B≡ℕ
                        ([~] _ (D , whnfB′) x₄)
        ⊢F , _ = syntacticEq (soundnessConv↑ x)
        _ , ⊢n , _ = syntacticEqTerm (soundness~↓ k~l′)
    in  ↑ (refl (substType ⊢F ⊢n))
          (natrec-cong x x₁ x₂ k~l′)

  ~-prodrec :
    ∀ {F G A A′ t t′ u u′} →
    Γ »∙ Σʷ p , q ▷ F ▹ G ⊢ A [conv↑] A′ →
    Γ ⊢ t ~ t′ ∷ (Σʷ p , q ▷ F ▹ G) →
    Γ »∙ F »∙ G ⊢ u [conv↑] u′ ∷ A [ prodʷ p (var x1) (var x0) ]↑² →
    Γ ⊢ prodrec r p q′ A t u ~ prodrec r p q′ A′ t′ u′ ∷ (A [ t ]₀)
  ~-prodrec x₂ (↑ A≡B k~↑l) x₄ =
    case syntacticEq A≡B of λ (_ , ⊢B) →
    case whNorm ⊢B of λ (B′ , whnfB′ , D) →
    case _⊢_≡_.trans A≡B (subset* D) of λ Σ≡Σ′ →
    case Σ≡A (trans A≡B (subset* D)) whnfB′ of λ where
      (F′ , G′ , PE.refl) →
        case ΠΣ-injectivity-no-equality-reflection Σ≡Σ′ of λ where
          (F≡F′ , G≡G′ , _ , _ , _) →
            let t~t′       = [~] _ (D , whnfB′) k~↑l
                ⊢A , _     = syntacticEq (soundnessConv↑ x₂)
                _ , ⊢t , _ = syntacticEqTerm (soundness~↑ k~↑l)
            in
            ↑ (refl (substType ⊢A (conv ⊢t (sym A≡B))))
              (prodrec-cong (stabilityConv↑ (refl-∙ Σ≡Σ′) x₂)
                 t~t′ (stabilityConv↑Term (refl-∙ F≡F′ ∙ G≡G′) x₄))

  ~-emptyrec : ∀ {n n′ F F′}
           → Γ ⊢ F [conv↑] F′ →
        Γ ⊢ n ~ n′ ∷ Empty →
        Γ ⊢ emptyrec p F n ~ emptyrec p F′ n′ ∷ F
  ~-emptyrec x (↑ A≡B x₄) =
    let _ , ⊢B = syntacticEq A≡B
        B′ , whnfB′ , D = whNorm ⊢B
        Empty≡B′ = trans A≡B (subset* D)
        B≡Empty = Empty≡A Empty≡B′ whnfB′
        k~l′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) B≡Empty
                        ([~] _ (D , whnfB′) x₄)
        ⊢F , _ = syntacticEq (soundnessConv↑ x)
        _ , ⊢n , _ = syntacticEqTerm (soundness~↓ k~l′)
    in  ↑ (refl ⊢F)
          (emptyrec-cong x k~l′)

  ~-unitrec : ∀ {A A′ t t′ u u′}
            → Γ »∙ Unitʷ l ⊢ A [conv↑] A′
            → Γ ⊢ t ~ t′ ∷ Unitʷ l
            → Γ ⊢ u [conv↑] u′ ∷ A [ starʷ l ]₀
            → Unitʷ-allowed
            → ¬ Unitʷ-η
            → Γ ⊢ unitrec l p q A t u ~ unitrec l p q A′ t′ u′ ∷
                A [ t ]₀
  ~-unitrec A<>A′ (↑ A≡B t~t′) u<>u′ ok no-η =
    let _ , ⊢B = syntacticEq A≡B
        B′ , whnfB′ , D = whNorm ⊢B
        Unit≡B′ = trans A≡B (subset* D)
        B≡Unit = Unit≡A Unit≡B′ whnfB′
        t~t″ = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) B≡Unit
                        ([~] _ (D , whnfB′) t~t′)
        ⊢A , _ = syntacticEq (soundnessConv↑ A<>A′)
        _ , ⊢t , _ = syntacticEqTerm (soundness~↓ t~t″)
    in  ↑ (refl (substType ⊢A ⊢t))
          (unitrec-cong A<>A′ t~t″ u<>u′ no-η)

  opaque

    ~-J :
      Γ ⊢ A₁ [conv↑] A₂ →
      Γ ⊢ t₁ ∷ A₁ →
      Γ ⊢ t₁ [conv↑] t₂ ∷ A₁ →
      Γ »∙ A₁ »∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊢ B₁ [conv↑] B₂ →
      Γ ⊢ u₁ [conv↑] u₂ ∷ B₁ [ t₁ , rfl ]₁₀ →
      Γ ⊢ v₁ [conv↑] v₂ ∷ A₁ →
      Γ ⊢ w₁ ~ w₂ ∷ Id A₁ t₁ v₁ →
      Γ ⊢ J p q A₁ t₁ B₁ u₁ v₁ w₁ ~ J p q A₂ t₂ B₂ u₂ v₂ w₂ ∷
        B₁ [ v₁ , w₁ ]₁₀
    ~-J A₁≡A₂ _ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ (↑ Id-t₁-v₁≡C w₁~w₂) =
      case Id-norm (sym Id-t₁-v₁≡C) of λ {
        (_ , _ , _ , C⇒*Id-t₃-v₃ , A₁≡A₃ , t₁≡t₃ , v₁≡v₃) →
      ↑ (refl $
         substType₂ (syntacticEq (soundnessConv↑ B₁≡B₂) .proj₁)
           (syntacticEqTerm v₁≡v₃ .proj₂ .proj₁)
           (conv (syntacticEqTerm (soundness~↑ w₁~w₂) .proj₂ .proj₁) $
            PE.subst (_⊢_≡_ _ _) ≡Id-wk1-wk1-0[]₀ $
            sym Id-t₁-v₁≡C))
        (J-cong A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂
           ([~] _ (C⇒*Id-t₃-v₃ , Idₙ) w₁~w₂)
           (trans (sym (subset* C⇒*Id-t₃-v₃)) (sym Id-t₁-v₁≡C))) }

    ~-K :
      Γ ⊢ A₁ [conv↑] A₂ →
      Γ ⊢ t₁ [conv↑] t₂ ∷ A₁ →
      Γ »∙ Id A₁ t₁ t₁ ⊢ B₁ [conv↑] B₂ →
      Γ ⊢ u₁ [conv↑] u₂ ∷ B₁ [ rfl ]₀ →
      Γ ⊢ v₁ ~ v₂ ∷ Id A₁ t₁ t₁ →
      K-allowed →
      Γ ⊢ K p A₁ t₁ B₁ u₁ v₁ ~ K p A₂ t₂ B₂ u₂ v₂ ∷ B₁ [ v₁ ]₀
    ~-K A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ (↑ Id-t₁-t₁≡C v₁~v₂) ok =
      case Id-norm (sym Id-t₁-t₁≡C) of λ {
        (_ , _ , _ , C⇒*Id-t₃-t₄ , A₁≡A₃ , t₁≡t₃ , t₁≡t₄) →
      ↑ (refl $
         substType (syntacticEq (soundnessConv↑ B₁≡B₂) .proj₁) $
         _⊢_∷_.conv
           (syntacticEqTerm (soundness~↑ v₁~v₂) .proj₂ .proj₁) $
         sym Id-t₁-t₁≡C)
        (K-cong A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂
           ([~] _ (C⇒*Id-t₃-t₄ , Idₙ) v₁~v₂)
           (trans (sym (subset* C⇒*Id-t₃-t₄)) (sym Id-t₁-t₁≡C)) ok) }

    ~-[]-cong :
      Γ ⊢ A₁ [conv↑] A₂ →
      Γ ⊢ t₁ [conv↑] t₂ ∷ A₁ →
      Γ ⊢ u₁ [conv↑] u₂ ∷ A₁ →
      Γ ⊢ v₁ ~ v₂ ∷ Id A₁ t₁ u₁ →
      []-cong-allowed s →
      let open Erased s in
      Γ ⊢ []-cong s A₁ t₁ u₁ v₁ ~ []-cong s A₂ t₂ u₂ v₂ ∷
        Id (Erased A₁) ([ t₁ ]) ([ u₁ ])
    ~-[]-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ (↑ Id-t₁-u₁≡B v₁~v₂) ok =
      case Id-norm (sym Id-t₁-u₁≡B) of λ {
        (_ , _ , _ , B⇒*Id-t₃-u₃ , A₁≡A₃ , t₁≡t₃ , u₁≡u₃) →
      ↑ (_⊢_≡_.refl $
         Idⱼ′
           ([]ⱼ ([]-cong→Erased ok)
              (syntacticEqTerm t₁≡t₃ .proj₂ .proj₁))
           ([]ⱼ ([]-cong→Erased ok)
              (syntacticEqTerm u₁≡u₃ .proj₂ .proj₁)))
        ([]-cong-cong A₁≡A₂ t₁≡t₂ u₁≡u₂
           ([~] _ (B⇒*Id-t₃-u₃ , Idₙ) v₁~v₂)
           (trans (sym (subset* B⇒*Id-t₃-u₃)) (sym Id-t₁-u₁≡B))
           ok) }

  ~-sym : ∀ {k l A} → Γ ⊢ k ~ l ∷ A → Γ ⊢ l ~ k ∷ A
  ~-sym (↑ A≡B x) =
    let ⊢Γ = wfEq A≡B
        B , A≡B′ , l~k = sym~↑ (reflConEq ⊢Γ) x
    in  ↑ (trans A≡B A≡B′) l~k

  ~-trans : ∀ {k l m A}
          → Γ ⊢ k ~ l ∷ A → Γ ⊢ l ~ m ∷ A
          → Γ ⊢ k ~ m ∷ A
  ~-trans (↑ x x₁) (↑ x₂ x₃) =
    let ⊢Γ = wfEq x
        k~m , _ = trans~↑ x₁ x₃
    in  ↑ x k~m

  ~-wk : ∀ {k l A} {ρ : Wk m n} {Γ Δ} →
        ∇ » ρ ∷ʷ Δ ⊇ Γ →
        ∇ » Γ ⊢ k ~ l ∷ A → ∇ » Δ ⊢ wk ρ k ~ wk ρ l ∷ wk ρ A
  ~-wk x (↑ x₂ x₃) = ↑ (wkEq x x₂) (wk~↑ x x₃)

  ~-defn-wk : ∀ {k l A} →
        » ∇′ ⊇ ∇ →
        ∇ » Η ⊢ k ~ l ∷ A → ∇′ » Η ⊢ k ~ l ∷ A
  ~-defn-wk ξ⊇ (↑ A≡B k~l) = ↑ (defn-wkEq ξ⊇ A≡B) (defn-wk~↑ ξ⊇ k~l)

  ~-conv : ∀ {k l A B} →
        Γ ⊢ k ~ l ∷ A → Γ ⊢ A ≡ B → Γ ⊢ k ~ l ∷ B
  ~-conv (↑ x x₁) x₂ = ↑ (trans (sym x₂) x) x₁

  ~-to-conv : ∀ {k l A} →
        Γ ⊢ k ~ l ∷ A → Γ ⊢ k [conv↑] l ∷ A
  ~-to-conv (↑ x x₁) = convConv↑Term (sym x) (lift~toConv↑ x₁)

private opaque

  -- A lemma used below.

  equality-relations :
    Equality-relations _⊢_[conv↑]_ _⊢_[conv↑]_∷_ _⊢_~_∷_ (Lift _ ⊤)
  equality-relations = let open Lemmas in λ where
    .Equality-relations.Var-included? →
      yes (lift tt)
    .Equality-relations.Equality-reflection-allowed→¬Var-included →
      λ ok _ → No-equality-reflection⇔ .proj₁ no-equality-reflection ok
    .Equality-relations.⊢≡→⊢≅      → ⊥-elim ∘→ (_$ _)
    .Equality-relations.⊢≡∷→⊢≅∷    → ⊥-elim ∘→ (_$ _)
    .Equality-relations.~-to-≅ₜ    → ~-to-conv
    .Equality-relations.≅-eq       → soundnessConv↑
    .Equality-relations.≅ₜ-eq      → soundnessConv↑Term
    .Equality-relations.≅-univ     → univConv↑
    .Equality-relations.≅-sym      → symConv
    .Equality-relations.≅ₜ-sym     → symConvTerm
    .Equality-relations.~-sym      → ~-sym
    .Equality-relations.≅-trans    → transConv
    .Equality-relations.≅ₜ-trans   → transConvTerm
    .Equality-relations.~-trans    → ~-trans
    .Equality-relations.≅-conv     → flip convConv↑Term
    .Equality-relations.~-conv     → ~-conv
    .Equality-relations.≅-wk       → wkConv↑
    .Equality-relations.≅ₜ-wk      → wkConv↑Term
    .Equality-relations.~-wk       → ~-wk
    .Equality-relations.≅-defn-wk  → defn-wkConv↑
    .Equality-relations.≅ₜ-defn-wk → defn-wkConv↑Term
    .Equality-relations.~-defn-wk  → ~-defn-wk
    .Equality-relations.≅-red      →
      λ (A⇒* , _) (B⇒* , _) → reductionConv↑ A⇒* B⇒*
    .Equality-relations.≅ₜ-red     →
      λ (A⇒* , _) (t⇒* , _) (u⇒* , _) → reductionConv↑Term A⇒* t⇒* u⇒*
    .Equality-relations.≅-Urefl    →
      λ ⊢Γ → liftConvTerm (univ (Uⱼ ⊢Γ) (Uⱼ ⊢Γ) (U-refl ⊢Γ))
    .Equality-relations.≅ₜ-ℕrefl   →
      λ x → liftConvTerm (univ (ℕⱼ x) (ℕⱼ x) (ℕ-refl x))
    .Equality-relations.≅ₜ-Emptyrefl →
      λ x → liftConvTerm (univ (Emptyⱼ x) (Emptyⱼ x) (Empty-refl x))
    .Equality-relations.≅ₜ-Unitrefl →
      λ ⊢Γ ok →
        liftConvTerm $
        univ (Unitⱼ ⊢Γ ok) (Unitⱼ ⊢Γ ok) (Unit-refl ⊢Γ ok)
    .Equality-relations.≅ₜ-η-unit →
      λ [e] [e'] ok →
        let u , uWhnf , uRed = whNormTerm [e]
            u' , u'Whnf , u'Red = whNormTerm [e']
            _ , _ , [u] = wf-⊢≡∷ (subset*Term uRed)
            _ , _ , [u'] = wf-⊢≡∷ (subset*Term u'Red)
        in  [↑]ₜ Unit! u u'
              (id (syntacticTerm [e]) , Unitₙ)
              (uRed , uWhnf)
              (u'Red , u'Whnf)
              (η-unit [u] [u'] uWhnf u'Whnf ok)
    .Equality-relations.≅-ΠΣ-cong →
      λ x₁ x₂ ok → liftConv (ΠΣ-cong x₁ x₂ ok)
    .Equality-relations.≅ₜ-ΠΣ-cong →
      λ x₁ x₂ ok →
        let _ , F∷U , H∷U = syntacticEqTerm (soundnessConv↑Term x₁)
            _ , G∷U , E∷U = syntacticEqTerm (soundnessConv↑Term x₂)
            ⊢Γ = wfTerm F∷U
            F<>H = univConv↑ x₁
            G<>E = univConv↑ x₂
            F≡H = soundnessConv↑ F<>H
            E∷U′ = stabilityTerm (refl-∙ F≡H) E∷U
        in
        liftConvTerm $
        univ (ΠΣⱼ F∷U G∷U ok) (ΠΣⱼ H∷U E∷U′ ok) (ΠΣ-cong F<>H G<>E ok)
    .Equality-relations.≅ₜ-zerorefl →
      liftConvTerm ∘ᶠ zero-refl
    .Equality-relations.≅ₜ-starrefl →
      λ x x₁ → liftConvTerm (star-refl x x₁)
    .Equality-relations.≅-suc-cong →
      liftConvTerm ∘ᶠ suc-cong
    .Equality-relations.≅-prod-cong →
      λ x₁ x₂ x₃ x₄ → liftConvTerm (prod-cong x₁ x₂ x₃ x₄)
    .Equality-relations.≅-η-eq →
      λ x₁ x₂ x₃ x₄ x₅ → liftConvTerm (η-eq x₁ x₂ x₃ x₄ x₅)
    .Equality-relations.≅-Σ-η →
      λ x₂ x₃ x₄ x₅ x₆ x₇ → (liftConvTerm (Σ-η x₂ x₃ x₄ x₅ x₆ x₇))
    .Equality-relations.~-var → ~-var
    .Equality-relations.~-defn → ~-defn
    .Equality-relations.~-app → ~-app
    .Equality-relations.~-fst →
      λ _ x₂ → ~-fst x₂
    .Equality-relations.~-snd →
      λ _ x₂ → ~-snd x₂
    .Equality-relations.~-natrec → ~-natrec
    .Equality-relations.~-prodrec →
      λ C↑D t₁~t₂ u₁↑u₂ _ → ~-prodrec C↑D t₁~t₂ u₁↑u₂
    .Equality-relations.~-emptyrec → ~-emptyrec
    .Equality-relations.~-unitrec  → ~-unitrec
    .Equality-relations.≅-Id-cong  →
      λ A₁≡A₂ t₁≡t₂ u₁≡u₂ → liftConv (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂)
    .Equality-relations.≅ₜ-Id-cong →
      λ A₁≡A₂ t₁≡t₂ u₁≡u₂ →
        case soundnessConv↑Term A₁≡A₂ of λ {
          ⊢A₁≡A₂ →
        case syntacticEqTerm ⊢A₁≡A₂ of λ {
          (_ , ⊢A₁ , ⊢A₂) →
        case syntacticEqTerm (soundnessConv↑Term t₁≡t₂) of λ {
          (_ , ⊢t₁ , ⊢t₂) →
        case syntacticEqTerm (soundnessConv↑Term u₁≡u₂) of λ {
          (_ , ⊢u₁ , ⊢u₂) →
        liftConvTerm $
        univ (Idⱼ ⊢A₁ ⊢t₁ ⊢u₁)
          (Idⱼ ⊢A₂ (conv ⊢t₂ (univ ⊢A₁≡A₂)) (conv ⊢u₂ (univ ⊢A₁≡A₂)))
          (Id-cong (univConv↑ A₁≡A₂) t₁≡t₂ u₁≡u₂) }}}}
    .Equality-relations.≅ₜ-rflrefl →
      liftConvTerm ∘→ rfl-refl ∘→ refl
    .Equality-relations.~-J       → ~-J
    .Equality-relations.~-K       → ~-K
    .Equality-relations.~-[]-cong → ~-[]-cong

-- An EqRelSet instance that uses algorithmic equality (_⊢_[conv↑]_,
-- _⊢_[conv↑]_∷_ and _⊢_~_∷_).

instance

  eqRelInstance : EqRelSet
  eqRelInstance = λ where
    .EqRelSet._⊢_≅_              → _⊢_[conv↑]_
    .EqRelSet._⊢_≅_∷_            → _⊢_[conv↑]_∷_
    .EqRelSet._⊢_~_∷_            → _⊢_~_∷_
    .EqRelSet.Var-included       → Lift _ ⊤
    .EqRelSet.equality-relations → equality-relations

open EqRelSet eqRelInstance public hiding (_⊢_~_∷_)
open Definition.Typed.EqualityRelation.Instance
       R ⦃ eq = eqRelInstance ⦄
  public

instance

  -- A variant of lift tt that is an instance.

  lift-tt : Lift a ⊤
  lift-tt = lift tt
