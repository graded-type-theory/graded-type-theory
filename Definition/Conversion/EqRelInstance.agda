------------------------------------------------------------------------
-- The algorithmic equality is an instance of the abstract set of
-- equality relations.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions

module Definition.Conversion.EqRelInstance
  {a} {M : Set a}
  (R : Type-restrictions M)
  where

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Weakening R using (_∷_⊆_; wkEq)
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

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.Function
import Tools.PropositionalEquality as PE

private
  variable
    m n : Nat
    Γ : Con Term n
    ρ : Wk m n
    p p₁ p₂ p′ q q′ q₁ q₂ r r′ : M

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
          ([~] _ (red D) whnfB′ x))
       (convConvTerm x₁ F≡H)) }}

~-fst :
  ∀ {p r F G} →
  Γ ⊢ p ~ r ∷ Σₚ p′ , q ▷ F ▹ G →
  Γ ⊢ fst p′ p ~ fst p′ r ∷ F
~-fst (↑ A≡B p~r) =
  case syntacticEq A≡B of λ (_ , ⊢B) →
  case whNorm ⊢B of λ (B′ , whnfB′ , D) →
  case trans A≡B (subset* (red D)) of λ ΣFG≡B′ →
  case Σ≡A ΣFG≡B′ whnfB′ of λ where
    (H , _ , PE.refl) →
      case Σ-injectivity ΣFG≡B′ of λ where
        (F≡H , _ , _ , _) →
          ↑ F≡H (fst-cong ([~] _ (red D) whnfB′ p~r))

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
          let p~r↓       = [~] _ (red D) whnfB′ p~r
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
                      ([~] _ (red D) whnfB′ x₄)
      ⊢F , _ = syntacticEq (soundnessConv↑ x)
      _ , ⊢n , _ = syntacticEqTerm (soundness~↓ k~l′)
  in  ↑ (refl (substType ⊢F ⊢n))
        (natrec-cong x x₁ x₂ k~l′)

~-prodrec :
  ∀ {F G A A′ t t′ u u′} →
  Γ ⊢ F →
  Γ ∙ F ⊢ G →
  Γ ∙ (Σᵣ p , q ▷ F ▹ G) ⊢ A [conv↑] A′ →
  Γ ⊢ t ~ t′ ∷ (Σᵣ p , q ▷ F ▹ G) →
  Γ ∙ F ∙ G ⊢ u [conv↑] u′ ∷ A [ prodᵣ p (var x1) (var x0) ]↑² →
  Γ ⊢ prodrec r p q′ A t u ~ prodrec r p q′ A′ t′ u′ ∷ (A [ t ]₀)
~-prodrec x x₁ x₂ (↑ A≡B k~↑l) x₄ =
  case syntacticEq A≡B of λ (_ , ⊢B) →
  case whNorm ⊢B of λ (B′ , whnfB′ , D) →
  case _⊢_≡_.trans A≡B (subset* (red D)) of λ Σ≡Σ′ →
  case Σ≡A (trans A≡B (subset* (red D))) whnfB′ of λ where
    (F′ , G′ , PE.refl) →
      case Σ-injectivity Σ≡Σ′ of λ where
        (F≡F′ , G≡G′ , _ , _ , _) →
          let t~t′       = [~] _ (red D) whnfB′ k~↑l
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
                      ([~] _ (red D) whnfB′ x₄)
      ⊢F , _ = syntacticEq (soundnessConv↑ x)
      _ , ⊢n , _ = syntacticEqTerm (soundness~↓ k~l′)
  in  ↑ (refl ⊢F)
        (emptyrec-cong x k~l′)

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
      ρ ∷ Δ ⊆ Γ →
      ⊢ Δ → Γ ⊢ k ~ l ∷ A → Δ ⊢ wk ρ k ~ wk ρ l ∷ wk ρ A
~-wk x x₁ (↑ x₂ x₃) = ↑ (wkEq x x₁ x₂) (wk~↑ x x₁ x₃)

~-conv : ∀ {k l A B} →
      Γ ⊢ k ~ l ∷ A → Γ ⊢ A ≡ B → Γ ⊢ k ~ l ∷ B
~-conv (↑ x x₁) x₂ = ↑ (trans (sym x₂) x) x₁

~-to-conv : ∀ {k l A} →
      Γ ⊢ k ~ l ∷ A → Γ ⊢ k [conv↑] l ∷ A
~-to-conv (↑ x x₁) = convConvTerm (lift~toConv↑ x₁) (sym x)


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
  ≅-conv = convConvTerm;
  ~-conv = ~-conv;
  ≅-wk = wkConv↑;
  ≅ₜ-wk = wkConv↑Term;
  ~-wk = ~-wk;
  ≅-red = λ x x₁ x₂ x₃ x₄ → reductionConv↑ x x₁ x₄;
  ≅ₜ-red = λ x x₁ x₂ x₃ x₄ x₅ x₆ → reductionConv↑Term x x₁ x₂ x₆;
  ≅-Urefl = liftConv ∘ᶠ U-refl;
  ≅-ℕrefl = liftConv ∘ᶠ ℕ-refl;
  ≅ₜ-ℕrefl = λ x → liftConvTerm (univ (ℕⱼ x) (ℕⱼ x) (ℕ-refl x));
  ≅-Emptyrefl = liftConv ∘ᶠ Empty-refl;
  ≅ₜ-Emptyrefl = λ x → liftConvTerm (univ (Emptyⱼ x) (Emptyⱼ x) (Empty-refl x));
  ≅-Unitrefl = λ ⊢Γ → liftConv ∘→ Unit-refl ⊢Γ;
  ≅ₜ-Unitrefl = λ ⊢Γ ok →
                  liftConvTerm $
                  univ (Unitⱼ ⊢Γ ok) (Unitⱼ ⊢Γ ok) (Unit-refl ⊢Γ ok);
  ≅ₜ-η-unit = λ [e] [e'] → let u , uWhnf , uRed = whNormTerm [e]
                               u' , u'Whnf , u'Red = whNormTerm [e']
                               [u] = ⊢u-redₜ uRed
                               [u'] = ⊢u-redₜ u'Red
                           in  [↑]ₜ Unit u u'
                               (red (idRed:*: (syntacticTerm [e])))
                               (redₜ uRed)
                               (redₜ u'Red)
                               Unitₙ uWhnf u'Whnf
                               (η-unit [u] [u'] uWhnf u'Whnf);
  ≅-ΠΣ-cong = λ x x₁ x₂ ok → liftConv (ΠΣ-cong x x₁ x₂ ok);
  ≅ₜ-ΠΣ-cong = λ x x₁ x₂ ok →
    let _ , F∷U , H∷U = syntacticEqTerm (soundnessConv↑Term x₁)
        _ , G∷U , E∷U = syntacticEqTerm (soundnessConv↑Term x₂)
        ⊢Γ = wfTerm F∷U
        F<>H = univConv↑ x₁
        G<>E = univConv↑ x₂
        F≡H = soundnessConv↑ F<>H
        E∷U′ = stabilityTerm (reflConEq ⊢Γ ∙ F≡H) E∷U
    in
    liftConvTerm $
    univ (ΠΣⱼ F∷U G∷U ok) (ΠΣⱼ H∷U E∷U′ ok) (ΠΣ-cong x F<>H G<>E ok);
  ≅ₜ-zerorefl = liftConvTerm ∘ᶠ zero-refl;
  ≅-suc-cong = liftConvTerm ∘ᶠ suc-cong;
  ≅-prod-cong = λ x x₁ x₂ x₃ x₄ →
                  liftConvTerm (prod-cong x x₁ x₂ x₃ x₄);
  ≅-η-eq = λ x x₁ x₂ x₃ x₄ x₅ → liftConvTerm (η-eq x₁ x₂ x₃ x₄ x₅);
  ≅-Σ-η = λ x x₁ x₂ x₃ x₄ x₅ x₆ x₇ → (liftConvTerm (Σ-η x₂ x₃ x₄ x₅ x₆ x₇));
  ~-var = ~-var;
  ~-app = ~-app;
  ~-fst = λ x x₁ x₂ → ~-fst x₂;
  ~-snd = λ x x₁ x₂ → ~-snd x₂;
  ~-natrec = ~-natrec;
  ~-prodrec = λ ⊢A ⊢B C↑D t₁~t₂ u₁↑u₂ _ →
                ~-prodrec ⊢A ⊢B C↑D t₁~t₂ u₁↑u₂;
  ~-emptyrec = ~-emptyrec }
