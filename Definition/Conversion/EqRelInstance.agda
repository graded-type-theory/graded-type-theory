------------------------------------------------------------------------
-- The algorithmic equality is an instance of the abstract set of
-- equality relations.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Conversion.EqRelInstance
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Weakening R using (_∷_⊇_; wkEq)
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
open import Definition.Typed.EqualityRelation R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Consequences.Substitution R
open import Definition.Typed.Consequences.Stability R
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Consequences.Equality R
open import Definition.Typed.Consequences.Reduction R

open import Graded.Derived.Erased.Typed R
import Graded.Derived.Erased.Untyped 𝕄 as Erased

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.Function
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum using (inj₁; inj₂)

private
  variable
    m n : Nat
    Γ : Con Term n
    A₁ A₂ B₁ B₂ t₁ t₂ u₁ u₂ v₁ v₂ w₁ w₂ : Term _
    ρ : Wk m n
    p p₁ p₂ p′ q q′ q₁ q₂ r r′ : M
    s : Strength

-- Algorithmic equality of neutrals with injected conversion.
record _⊢_~_∷_ (Γ : Con Term n) (k l A : Term n) : Set a where
  inductive
  constructor ↑
  field
    {B} : Term n
    A≡B : Γ ⊢ A ≡ B
    k~↑l : Γ ⊢ k ~ l ↑ B

-- Properties of algorithmic equality of neutrals with injected conversion.

~-var : ∀ {x A} → Γ ⊢ var x ∷ A → Γ ⊢ var x ~ var x ∷ A
~-var x =
  let ⊢A = syntacticTerm x
  in  ↑ (refl ⊢A) (var-refl x PE.refl)

~-app : ∀ {f g a b F G}
      → Γ ⊢ f ~ g ∷ Π p , q ▷ F ▹ G
      → Γ ⊢ a [conv↑] b ∷ F
      → Γ ⊢ f ∘⟨ p ⟩ a ~ g ∘⟨ p ⟩ b ∷ G [ a ]₀
~-app (↑ A≡B x) x₁ =
  let _ , ⊢B = syntacticEq A≡B
      B′ , whnfB′ , D = whNorm ⊢B
      ΠFG≡B′ = trans A≡B (subset* (red D))
      _ , ⊢f , _ = syntacticEqTerm (soundnessConv↑Term x₁)
  in
  case Π≡A ΠFG≡B′ whnfB′ of λ {
    (H , E , B≡ΠHE) →
  case injectivity (PE.subst (λ x → _ ⊢ _ ≡ x) B≡ΠHE ΠFG≡B′) of λ {
    (F≡H , G≡E , _ , _) →
  ↑ (substTypeEq G≡E (refl ⊢f))
    (app-cong
       (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) B≡ΠHE
          ([~] _ (red D , whnfB′) x))
       (convConv↑Term F≡H x₁)) }}

~-fst :
  ∀ {p r F G} →
  Γ ⊢ p ~ r ∷ Σˢ p′ , q ▷ F ▹ G →
  Γ ⊢ fst p′ p ~ fst p′ r ∷ F
~-fst (↑ A≡B p~r) =
  case syntacticEq A≡B of λ (_ , ⊢B) →
  case whNorm ⊢B of λ (B′ , whnfB′ , D) →
  case trans A≡B (subset* (red D)) of λ ΣFG≡B′ →
  case Σ≡A ΣFG≡B′ whnfB′ of λ where
    (H , _ , PE.refl) →
      case Σ-injectivity ΣFG≡B′ of λ where
        (F≡H , _ , _ , _) →
          ↑ F≡H (fst-cong ([~] _ (red D , whnfB′) p~r))

~-snd :
  ∀ {p r F G} →
  Γ ⊢ p ~ r ∷ Σ p′ , q ▷ F ▹ G →
  Γ ⊢ snd p′ p ~ snd p′ r ∷ G [ fst p′ p ]₀
~-snd (↑ A≡B p~r) =
  case syntacticEq A≡B of λ (⊢ΣFG , ⊢B) →
  case whNorm ⊢B of λ (B′ , whnfB′ , D) →
  case trans A≡B (subset* (red D)) of λ ΣFG≡B′ →
  case Σ≡A ΣFG≡B′ whnfB′ of λ where
    (_ , E , PE.refl) →
      case Σ-injectivity ΣFG≡B′ of λ where
        (_ , G≡E , _ , _) →
          let p~r↓       = [~] _ (red D , whnfB′) p~r
              ⊢F , ⊢G    = syntacticΣ ⊢ΣFG
              _ , ⊢p , _ = syntacticEqTerm (soundness~↑ p~r)
              ⊢fst       = fstⱼ ⊢F ⊢G (conv ⊢p (sym A≡B))
          in
          ↑ (substTypeEq G≡E (refl ⊢fst)) (snd-cong p~r↓)

~-natrec : ∀ {z z′ s s′ n n′ F F′}
         → Γ ∙ ℕ ⊢ F
         → (Γ ∙ ℕ) ⊢ F [conv↑] F′ →
      Γ ⊢ z [conv↑] z′ ∷ (F [ zero ]₀) →
      Γ ∙ ℕ ∙ F ⊢ s [conv↑] s′ ∷ F [ suc (var x1) ]↑² →
      Γ ⊢ n ~ n′ ∷ ℕ →
      Γ ⊢ natrec p q r F z s n ~ natrec p q r F′ z′ s′ n′ ∷ (F [ n ]₀)
~-natrec _ x x₁ x₂ (↑ A≡B x₄) =
  let _ , ⊢B = syntacticEq A≡B
      B′ , whnfB′ , D = whNorm ⊢B
      ℕ≡B′ = trans A≡B (subset* (red D))
      B≡ℕ = ℕ≡A ℕ≡B′ whnfB′
      k~l′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) B≡ℕ
                      ([~] _ (red D , whnfB′) x₄)
      ⊢F , _ = syntacticEq (soundnessConv↑ x)
      _ , ⊢n , _ = syntacticEqTerm (soundness~↓ k~l′)
  in  ↑ (refl (substType ⊢F ⊢n))
        (natrec-cong x x₁ x₂ k~l′)

~-prodrec :
  ∀ {F G A A′ t t′ u u′} →
  Γ ⊢ F →
  Γ ∙ F ⊢ G →
  Γ ∙ (Σʷ p , q ▷ F ▹ G) ⊢ A [conv↑] A′ →
  Γ ⊢ t ~ t′ ∷ (Σʷ p , q ▷ F ▹ G) →
  Γ ∙ F ∙ G ⊢ u [conv↑] u′ ∷ A [ prodʷ p (var x1) (var x0) ]↑² →
  Γ ⊢ prodrec r p q′ A t u ~ prodrec r p q′ A′ t′ u′ ∷ (A [ t ]₀)
~-prodrec x x₁ x₂ (↑ A≡B k~↑l) x₄ =
  case syntacticEq A≡B of λ (_ , ⊢B) →
  case whNorm ⊢B of λ (B′ , whnfB′ , D) →
  case _⊢_≡_.trans A≡B (subset* (red D)) of λ Σ≡Σ′ →
  case Σ≡A (trans A≡B (subset* (red D))) whnfB′ of λ where
    (F′ , G′ , PE.refl) →
      case Σ-injectivity Σ≡Σ′ of λ where
        (F≡F′ , G≡G′ , _ , _ , _) →
          let t~t′       = [~] _ (red D , whnfB′) k~↑l
              ⊢Γ         = wf ⊢B
              ⊢Γ≡Γ       = reflConEq ⊢Γ
              ⊢A , _     = syntacticEq (soundnessConv↑ x₂)
              _ , ⊢t , _ = syntacticEqTerm (soundness~↑ k~↑l)
          in
          ↑ (refl (substType ⊢A (conv ⊢t (sym A≡B))))
            (prodrec-cong (stabilityConv↑ (⊢Γ≡Γ ∙ Σ≡Σ′) x₂)
               t~t′ (stabilityConv↑Term (⊢Γ≡Γ ∙ F≡F′ ∙ G≡G′) x₄))

~-emptyrec : ∀ {n n′ F F′}
         → Γ ⊢ F [conv↑] F′ →
      Γ ⊢ n ~ n′ ∷ Empty →
      Γ ⊢ emptyrec p F n ~ emptyrec p F′ n′ ∷ F
~-emptyrec x (↑ A≡B x₄) =
  let _ , ⊢B = syntacticEq A≡B
      B′ , whnfB′ , D = whNorm ⊢B
      Empty≡B′ = trans A≡B (subset* (red D))
      B≡Empty = Empty≡A Empty≡B′ whnfB′
      k~l′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) B≡Empty
                      ([~] _ (red D , whnfB′) x₄)
      ⊢F , _ = syntacticEq (soundnessConv↑ x)
      _ , ⊢n , _ = syntacticEqTerm (soundness~↓ k~l′)
  in  ↑ (refl ⊢F)
        (emptyrec-cong x k~l′)

~-unitrec : ∀ {A A′ t t′ u u′}
          → Γ ∙ Unitʷ ⊢ A [conv↑] A′
          → Γ ⊢ t ~ t′ ∷ Unitʷ
          → Γ ⊢ u [conv↑] u′ ∷ A [ starʷ ]₀
          → Unitʷ-allowed
          → ¬ Unitʷ-η
          → Γ ⊢ unitrec p q A t u ~ unitrec p q A′ t′ u′ ∷ A [ t ]₀
~-unitrec A<>A′ (↑ A≡B t~t′) u<>u′ ok no-η =
  let _ , ⊢B = syntacticEq A≡B
      B′ , whnfB′ , D = whNorm ⊢B
      Unit≡B′ = trans A≡B (subset* (red D))
      B≡Unit = Unit≡A Unit≡B′ whnfB′
      t~t″ = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) B≡Unit
                      ([~] _ (red D , whnfB′) t~t′)
      ⊢A , _ = syntacticEq (soundnessConv↑ A<>A′)
      _ , ⊢t , _ = syntacticEqTerm (soundness~↓ t~t″)
  in  ↑ (refl (substType ⊢A ⊢t))
        (unitrec-cong A<>A′ t~t″ u<>u′ no-η)

opaque

  ~-J :
    Γ ⊢ A₁ →
    Γ ⊢ A₁ [conv↑] A₂ →
    Γ ⊢ t₁ ∷ A₁ →
    Γ ⊢ t₁ [conv↑] t₂ ∷ A₁ →
    Γ ∙ A₁ ∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊢ B₁ [conv↑] B₂ →
    Γ ⊢ u₁ [conv↑] u₂ ∷ B₁ [ t₁ , rfl ]₁₀ →
    Γ ⊢ v₁ [conv↑] v₂ ∷ A₁ →
    Γ ⊢ w₁ ~ w₂ ∷ Id A₁ t₁ v₁ →
    Γ ⊢ J p q A₁ t₁ B₁ u₁ v₁ w₁ ~ J p q A₂ t₂ B₂ u₂ v₂ w₂ ∷
      B₁ [ v₁ , w₁ ]₁₀
  ~-J _ A₁≡A₂ _ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ (↑ Id-t₁-v₁≡C w₁~w₂) =
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
    Γ ⊢ t₁ ∷ A₁ →
    Γ ⊢ t₁ [conv↑] t₂ ∷ A₁ →
    Γ ∙ Id A₁ t₁ t₁ ⊢ B₁ [conv↑] B₂ →
    Γ ⊢ u₁ [conv↑] u₂ ∷ B₁ [ rfl ]₀ →
    Γ ⊢ v₁ ~ v₂ ∷ Id A₁ t₁ t₁ →
    K-allowed →
    Γ ⊢ K p A₁ t₁ B₁ u₁ v₁ ~ K p A₂ t₂ B₂ u₂ v₂ ∷ B₁ [ v₁ ]₀
  ~-K A₁≡A₂ _ t₁≡t₂ B₁≡B₂ u₁≡u₂ (↑ Id-t₁-t₁≡C v₁~v₂) ok =
    case Id-norm (sym Id-t₁-t₁≡C) of λ {
      (_ , _ , _ , C⇒*Id-t₃-t₄ , A₁≡A₃ , t₁≡t₃ , t₁≡t₄) →
    ↑ (refl $
       substType (syntacticEq (soundnessConv↑ B₁≡B₂) .proj₁) $
       _⊢_∷_.conv (syntacticEqTerm (soundness~↑ v₁~v₂) .proj₂ .proj₁) $
       sym Id-t₁-t₁≡C)
      (K-cong A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ ([~] _ (C⇒*Id-t₃-t₄ , Idₙ) v₁~v₂)
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
       Idⱼ
         ([]ⱼ ([]-cong→Erased ok) (syntacticEqTerm t₁≡t₃ .proj₂ .proj₁))
         ([]ⱼ ([]-cong→Erased ok)
            (syntacticEqTerm u₁≡u₃ .proj₂ .proj₁)))
      ([]-cong-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ ([~] _ (B⇒*Id-t₃-u₃ , Idₙ) v₁~v₂)
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
      ρ ∷ Δ ⊇ Γ →
      ⊢ Δ → Γ ⊢ k ~ l ∷ A → Δ ⊢ wk ρ k ~ wk ρ l ∷ wk ρ A
~-wk x x₁ (↑ x₂ x₃) = ↑ (wkEq x x₁ x₂) (wk~↑ x x₁ x₃)

~-conv : ∀ {k l A B} →
      Γ ⊢ k ~ l ∷ A → Γ ⊢ A ≡ B → Γ ⊢ k ~ l ∷ B
~-conv (↑ x x₁) x₂ = ↑ (trans (sym x₂) x) x₁

~-to-conv : ∀ {k l A} →
      Γ ⊢ k ~ l ∷ A → Γ ⊢ k [conv↑] l ∷ A
~-to-conv (↑ x x₁) = convConv↑Term (sym x) (lift~toConv↑ x₁)


-- Algorithmic equality instance of the generic equality relation.
instance eqRelInstance : EqRelSet
eqRelInstance = record {
  _⊢_≅_ = _⊢_[conv↑]_;
  _⊢_≅_∷_ = _⊢_[conv↑]_∷_;
  _⊢_~_∷_ = _⊢_~_∷_;
  ~-to-≅ₜ = ~-to-conv;
  ≅-eq = soundnessConv↑;
  ≅ₜ-eq = soundnessConv↑Term;
  ≅-univ = univConv↑;
  ≅-sym = symConv;
  ≅ₜ-sym = symConvTerm;
  ~-sym = ~-sym;
  ≅-trans = transConv;
  ≅ₜ-trans = transConvTerm;
  ~-trans = ~-trans;
  ≅-conv = flip convConv↑Term;
  ~-conv = ~-conv;
  ≅-wk = wkConv↑;
  ≅ₜ-wk = wkConv↑Term;
  ~-wk = ~-wk;
  ≅-red = λ (A⇒* , _) (B⇒* , _) → reductionConv↑ A⇒* B⇒*;
  ≅ₜ-red = λ (A⇒* , _) (t⇒* , _) (u⇒* , _) →
             reductionConv↑Term A⇒* t⇒* u⇒*;
  ≅-Urefl = λ ⊢Γ → liftConvTerm (univ (Uⱼ ⊢Γ) (Uⱼ ⊢Γ) (U-refl ⊢Γ));
  ≅ₜ-ℕrefl = λ x → liftConvTerm (univ (ℕⱼ x) (ℕⱼ x) (ℕ-refl x));
  ≅ₜ-Emptyrefl = λ x → liftConvTerm (univ (Emptyⱼ x) (Emptyⱼ x) (Empty-refl x));
  ≅ₜ-Unitrefl = λ ⊢Γ ok →
                  liftConvTerm $
                  univ (Unitⱼ ⊢Γ ok) (Unitⱼ ⊢Γ ok) (Unit-refl ⊢Γ ok);
  ≅ₜ-η-unit = λ [e] [e'] ok →
    let u , uWhnf , uRed = whNormTerm [e]
        u' , u'Whnf , u'Red = whNormTerm [e']
        [u] = ⊢u-redₜ uRed
        [u'] = ⊢u-redₜ u'Red
    in  [↑]ₜ Unit! u u'
          (red (idRed:*: (syntacticTerm [e])) , Unitₙ)
          (redₜ uRed , uWhnf)
          (redₜ u'Red , u'Whnf)
          (η-unit [u] [u'] uWhnf u'Whnf ok);
  ≅-ΠΣ-cong = λ _ x₁ x₂ ok → liftConv (ΠΣ-cong x₁ x₂ ok);
  ≅ₜ-ΠΣ-cong = λ _ x₁ x₂ ok →
    let _ , F∷U , H∷U = syntacticEqTerm (soundnessConv↑Term x₁)
        _ , G∷U , E∷U = syntacticEqTerm (soundnessConv↑Term x₂)
        ⊢Γ = wfTerm F∷U
        F<>H = univConv↑ x₁
        G<>E = univConv↑ x₂
        F≡H = soundnessConv↑ F<>H
        E∷U′ = stabilityTerm (reflConEq ⊢Γ ∙ F≡H) E∷U
    in
    liftConvTerm $
    univ (ΠΣⱼ F∷U G∷U ok) (ΠΣⱼ H∷U E∷U′ ok) (ΠΣ-cong F<>H G<>E ok);
  ≅ₜ-zerorefl = liftConvTerm ∘ᶠ zero-refl;
  ≅ₜ-starrefl = λ x x₁ → liftConvTerm (star-refl x x₁);
  ≅-suc-cong = liftConvTerm ∘ᶠ suc-cong;
  ≅-prod-cong = λ _ x₁ x₂ x₃ x₄ →
                  liftConvTerm (prod-cong x₁ x₂ x₃ x₄);
  ≅-η-eq = λ x x₁ x₂ x₃ x₄ x₅ → liftConvTerm (η-eq x₁ x₂ x₃ x₄ x₅);
  ≅-Σ-η = λ x x₁ x₂ x₃ x₄ x₅ x₆ x₇ → (liftConvTerm (Σ-η x₂ x₃ x₄ x₅ x₆ x₇));
  ~-var = ~-var;
  ~-app = ~-app;
  ~-fst = λ x x₁ x₂ → ~-fst x₂;
  ~-snd = λ x x₁ x₂ → ~-snd x₂;
  ~-natrec = ~-natrec;
  ~-prodrec = λ ⊢A ⊢B C↑D t₁~t₂ u₁↑u₂ _ →
                ~-prodrec ⊢A ⊢B C↑D t₁~t₂ u₁↑u₂;
  ~-emptyrec = ~-emptyrec;
  ~-unitrec = ~-unitrec;
  ≅-Id-cong = λ { A₁≡A₂ t₁≡t₂ u₁≡u₂ →
    liftConv (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) };
  ≅ₜ-Id-cong = λ { A₁≡A₂ t₁≡t₂ u₁≡u₂ →
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
      (Id-cong (univConv↑ A₁≡A₂) t₁≡t₂ u₁≡u₂) }}}}};
  ≅ₜ-rflrefl = liftConvTerm ∘→ rfl-refl ∘→ refl;
  ~-J = ~-J;
  ~-K = ~-K;
  ~-[]-cong = ~-[]-cong }
