------------------------------------------------------------------------
-- Properties of the reduction relation.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.Reduction
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
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.Consequences.Equality R
open import Definition.Typed.Consequences.Inequality R as I
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Inversion R
open import Definition.Typed.Reasoning.Type R
open import Definition.Typed.Syntactic R
open import Definition.Typed.Weakening R
open import Definition.Typed.Well-formed R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Fundamental.Reducibility R
open import Definition.LogicalRelation.Substitution.Introductions R

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum

private
  variable
    Γ Δ : Con Term _
    A B C t u v : Term _
    p q : M
    b : BinderMode
    m s : Strength
    l : Universe-level

opaque

  -- If the type of t is U l, then t reduces to an application of a
  -- type constructor or a neutral term (given a certain assumption).

  red-U :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Γ ⊢ t ∷ U l → ∃ λ u → Type u × Γ ⊢ t ⇒* u ∷ U l
  red-U ⊢t =
    case ⊩∷U⇔ .proj₁ $ proj₂ $ reducible-⊩∷ ⊢t of λ
      (_ , _ , u , t⇒*u , u-type , _) →
    u , u-type , t⇒*u

opaque

  -- If the type of t is Empty, then t reduces to a neutral term
  -- (given a certain assumption).

  red-Empty :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Γ ⊢ t ∷ Empty → ∃ λ u → Neutral u × Γ ⊢ t ⇒* u ∷ Empty
  red-Empty ⊢t =
    case ⊩∷Empty⇔ .proj₁ $ proj₂ $ reducible-⊩∷ ⊢t of λ {
      (Emptyₜ u t⇒*u _ (ne (neNfₜ _ u-ne _))) →
    u , u-ne , t⇒*u }

opaque

  -- If t has a unit type, then t reduces to star or a neutral term
  -- (given a certain assumption).

  red-Unit :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Γ ⊢ t ∷ Unit s l → ∃ λ u → Star u × Γ ⊢ t ⇒* u ∷ Unit s l
  red-Unit ⊢t =
    case ⊩∷Unit⇔ .proj₁ $ proj₂ $ reducible-⊩∷ ⊢t of λ {
      (_ , _ , Unitₜ u t⇒*u _ rest) →
      u
    , (case rest of λ where
         starᵣ                 → starₙ
         (ne (neNfₜ _ u-ne _)) → ne u-ne)
    , t⇒*u }

opaque

  -- If the type of t is ℕ, then t reduces to zero, an application of
  -- suc, or a neutral term (given a certain assumption).

  red-ℕ :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Γ ⊢ t ∷ ℕ → ∃ λ u → Natural u × Γ ⊢ t ⇒* u ∷ ℕ
  red-ℕ ⊢t =
    case ⊩∷ℕ⇔ .proj₁ $ proj₂ $ reducible-⊩∷ ⊢t of λ {
      (ℕₜ u t⇒*u _ rest) →
      u
    , (case rest of λ where
         zeroᵣ                 → zeroₙ
         (sucᵣ _)              → sucₙ
         (ne (neNfₜ _ u-ne _)) → ne u-ne)
    , t⇒*u }

opaque

  -- If t has a Π-type, then t reduces to a lambda or a neutral term
  -- (given a certain assumption).

  red-Π :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Γ ⊢ t ∷ Π p , q ▷ A ▹ B →
    ∃ λ u → Function u × Γ ⊢ t ⇒* u ∷ Π p , q ▷ A ▹ B
  red-Π ⊢t =
    case ⊩∷Π⇔ .proj₁ $ proj₂ $ reducible-⊩∷ ⊢t of λ
      (_ , u , t⇒*u , u-fun , _) →
    u , u-fun , t⇒*u

opaque

  -- If t has a Σ-type, then t reduces to a pair or a neutral term
  -- (given a certain assumption).

  red-Σ :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Γ ⊢ t ∷ Σ⟨ m ⟩ p , q ▷ A ▹ B →
    ∃ λ u → Product u × Γ ⊢ t ⇒* u ∷ Σ⟨ m ⟩ p , q ▷ A ▹ B
  red-Σ {m = 𝕤} ⊢t =
    case ⊩∷Σˢ⇔ .proj₁ $ proj₂ $ reducible-⊩∷ ⊢t of λ
      (_ , u , t⇒*u , u-prod , _) →
    u , u-prod , t⇒*u
  red-Σ {m = 𝕨} ⊢t =
    case ⊩∷Σʷ⇔ .proj₁ $ proj₂ $ reducible-⊩∷ ⊢t of λ
      (_ , u , t⇒*u , _ , rest) →
    u , ⊩∷Σʷ→Product rest , t⇒*u

opaque

  -- If the type of t is Id A u v, then t reduces to rfl or a neutral
  -- term (given a certain assumption).

  red-Id :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Γ ⊢ t ∷ Id A u v →
    ∃ λ w → Identity w × Γ ⊢ t ⇒* w ∷ Id A u v
  red-Id ⊢t =
    case ⊩∷Id⇔ .proj₁ $ proj₂ $ reducible-⊩∷ ⊢t of λ
      (w , t⇒*w , _ , _ , rest) →
      w
    , (case rest of λ where
         (rflᵣ _)      → rflₙ
         (ne _ w-ne _) → ne w-ne)
    , t⇒*w

-- Helper function where all reducible types can be reduced to WHNF.
whNorm′ : ∀ {A l} ([A] : Γ ⊩⟨ l ⟩ A)
                → ∃ λ B → Whnf B × Γ ⊢ A ⇒* B
whNorm′ (Uᵣ′ l _ ⇒*U) = U l , Uₙ , ⇒*U
whNorm′ (ℕᵣ D) = ℕ , ℕₙ , D
whNorm′ (Emptyᵣ D) = Empty , Emptyₙ , D
whNorm′ (Unitᵣ (Unitₜ D _)) = Unit! , Unitₙ , D
whNorm′ (ne′ _ H D neH H≡H) = H , ne neH , D
whNorm′ (Πᵣ′ F G D _ _ _ _ _) = Π _ , _ ▷ F ▹ G , ΠΣₙ , D
whNorm′ (Σᵣ′ F G D _ _ _ _ _) = Σ _ , _ ▷ F ▹ G , ΠΣₙ , D
whNorm′ (Idᵣ ⊩Id) = _ , Idₙ , _⊩ₗId_.⇒*Id ⊩Id
whNorm′ (emb ≤ᵘ-refl     ⊩A) = whNorm′ ⊩A
whNorm′ (emb (≤ᵘ-step p) ⊩A) = whNorm′ (emb p ⊩A)

opaque

  -- Well-formed types reduce to WHNF (given a certain assumption).

  whNorm :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Γ ⊢ A → ∃ λ B → Whnf B × Γ ⊢ A ⇒* B
  whNorm A = whNorm′ (reducible-⊩ A .proj₂)

opaque

  -- If A is definitionally equal to U l, then A reduces to U l (given
  -- a certain assumption).

  U-norm :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Γ ⊢ A ≡ U l → Γ ⊢ A ⇒* U l
  U-norm {A} {l} A≡U =
    let B , B-whnf , A⇒*B = whNorm (syntacticEq A≡U .proj₁)
        U≡B               =
          U l  ≡˘⟨ A≡U ⟩⊢
          A    ≡⟨ subset* A⇒*B ⟩⊢∎
          B    ∎
    in
    PE.subst (_⊢_⇒*_ _ _) (U≡A U≡B B-whnf) A⇒*B

opaque

  -- If equality reflection is not allowed or the context is empty,
  -- and A is definitionally equal to ΠΣ⟨ b ⟩ p , q ▷ B ▹ C, then A
  -- reduces to ΠΣ⟨ b ⟩ p , q ▷ B′ ▹ C′, where B′ satisfies
  -- Γ ⊢ B ≡ B′, and C′ satisfies certain properties.

  ΠΣNorm :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Γ ⊢ A ≡ ΠΣ⟨ b ⟩ p , q ▷ B ▹ C →
    ∃₂ λ B′ C′ →
      Γ ⊢ A ⇒* ΠΣ⟨ b ⟩ p , q ▷ B′ ▹ C′ × Γ ⊢ B ≡ B′ ×
      (⦃ not-ok : No-equality-reflection ⦄ → Γ ∙ B ⊢ C ≡ C′) ×
      (∀ {t u} → Γ ⊢ t ≡ u ∷ B → Γ ⊢ C [ t ]₀ ≡ C′ [ u ]₀)
  ΠΣNorm {A} A≡ΠΣ with whNorm (syntacticEq A≡ΠΣ .proj₁)
  … | _ , Uₙ , D =
    ⊥-elim (U≢ΠΣⱼ (trans (sym (subset* D)) A≡ΠΣ))
  … | _ , ΠΣₙ , D =
    let B≡B′ , C≡C′ , C[]≡C′[] , p≡p′ , q≡q′ , b≡b′ =
          ΠΣ-injectivity′ (trans (sym A≡ΠΣ) (subset* D))
        D′ = PE.subst₃ (λ b p q → _ ⊢ A ⇒* ΠΣ⟨ b ⟩ p , q ▷ _ ▹ _)
               (PE.sym b≡b′) (PE.sym p≡p′) (PE.sym q≡q′) D
    in
    _ , _ , D′ , B≡B′ , C≡C′ , C[]≡C′[]
  … | _ , ℕₙ , D =
    ⊥-elim (ℕ≢ΠΣⱼ (trans (sym (subset* D)) A≡ΠΣ))
  … | _ , Unitₙ , D =
    ⊥-elim (Unit≢ΠΣⱼ (trans (sym (subset* D)) A≡ΠΣ))
  … | _ , Emptyₙ , D =
    ⊥-elim (Empty≢ΠΣⱼ (trans (sym (subset* D)) A≡ΠΣ))
  … | _ , Idₙ , A⇒*Id =
    ⊥-elim $ I.Id≢ΠΣ (trans (sym (subset* A⇒*Id)) A≡ΠΣ)
  … | _ , lamₙ , A⇒lam =
    case wf-⊢≡ (subset* A⇒lam) of λ where
      (_ , univ ⊢lam) →
        let _ , _ , _ , _ , _ , U≡Π , _ = inversion-lam ⊢lam in
        ⊥-elim (U≢ΠΣⱼ U≡Π)
  … | _ , zeroₙ , A⇒zero =
    case wf-⊢≡ (subset* A⇒zero) of λ where
      (_ , univ ⊢zero) →
        ⊥-elim (U≢ℕ (inversion-zero ⊢zero))
  … | _ , sucₙ , A⇒suc =
    case wf-⊢≡ (subset* A⇒suc) of λ where
      (_ , univ ⊢suc) →
        ⊥-elim (U≢ℕ (proj₂ (inversion-suc ⊢suc)))
  … | _ , starₙ , A⇒star =
    case wf-⊢≡ (subset* A⇒star) of λ where
      (_ , univ ⊢star) →
        ⊥-elim (U≢Unitⱼ (inversion-star ⊢star .proj₁))
  … | _ , prodₙ , A⇒prod =
    case wf-⊢≡ (subset* A⇒prod) of λ where
      (_ , univ ⊢prod) →
        let _ , _ , _ , _ , _ , _ , _ , U≡Σ , _ = inversion-prod ⊢prod in
        ⊥-elim (U≢ΠΣⱼ U≡Σ)
  … | _ , rflₙ , A⇒rfl =
    case wf-⊢≡ (subset* A⇒rfl) of λ where
      (_ , univ ⊢rfl) →
        ⊥-elim $ Id≢U $
        sym (inversion-rfl ⊢rfl .proj₂ .proj₂ .proj₂ .proj₂)
  … | _ , ne n , D =
    ⊥-elim (I.ΠΣ≢ne n (trans (sym A≡ΠΣ) (subset* D)))

opaque

  -- If equality reflection is not allowed or the context is empty,
  -- and A is definitionally equal to Id B t u, then A reduces to
  -- Id B′ t′ u′ for some B′, t′ and u′ that are definitionally equal
  -- to B, t and u.

  Id-norm :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Γ ⊢ A ≡ Id B t u →
    ∃₃ λ B′ t′ u′ → (Γ ⊢ A ⇒* Id B′ t′ u′) ×
    (Γ ⊢ B ≡ B′) × Γ ⊢ t ≡ t′ ∷ B × Γ ⊢ u ≡ u′ ∷ B
  Id-norm A≡Id =
    case whNorm (syntacticEq A≡Id .proj₁) of λ {
      (_ , A′-whnf , A⇒*A′) →
    case trans (sym A≡Id) (subset* A⇒*A′) of λ {
      Id≡A′ →
    case Id≡Whnf Id≡A′ A′-whnf of λ {
      (_ , _ , _ , PE.refl) →
    _ , _ , _ , A⇒*A′ , Id-injectivity Id≡A′ }}}

-- Helper function where reducible all terms can be reduced to WHNF.
whNormTerm′ : ∀ {a A l} ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ a ∷ A / [A]
                → ∃ λ b → Whnf b × Γ ⊢ a ⇒* b ∷ A
whNormTerm′ (Uᵣ′ _ _ A⇒*U) (Uₜ C B⇒*C C-type C≅C ⊩B) =
    C , typeWhnf C-type , conv* B⇒*C (sym (subset* A⇒*U))
whNormTerm′ (ℕᵣ x) (ℕₜ n d n≡n prop) =
  let natN = natural prop
  in  n , naturalWhnf natN , conv* d (sym (subset* x))
whNormTerm′ (Emptyᵣ x) (Emptyₜ n d n≡n prop) =
  let emptyN = empty prop
  in  n , ne emptyN , conv* d (sym (subset* x))
whNormTerm′ (Unitᵣ (Unitₜ x _)) (Unitₜ n d n≡n prop) =
  n , unit prop , conv* d (sym (subset* x))
whNormTerm′ (ne (ne _ H D neH H≡H)) (neₜ k d (neNfₜ _ neH₁ k≡k)) =
  k , ne neH₁ , conv* d (sym (subset* D))
whNormTerm′ (Πᵣ′ _ _ D _ _ _ _ _) (Πₜ f d funcF _ _ _) =
  f , functionWhnf funcF , conv* d (sym (subset* D))
whNormTerm′ (Σᵣ′ _ _ D _ _ _ _ _) (Σₜ p d _ pProd _) =
  p , productWhnf pProd , conv* d (sym (subset* D))
whNormTerm′ (Idᵣ ⊩Id) (a′ , a⇒*a′ , a′-id , _) =
    a′ , identityWhnf a′-id
  , conv* a⇒*a′ (sym (subset* (_⊩ₗId_.⇒*Id ⊩Id)))
whNormTerm′ (emb ≤ᵘ-refl     ⊩A) ⊩a = whNormTerm′ ⊩A ⊩a
whNormTerm′ (emb (≤ᵘ-step p) ⊩A) ⊩a = whNormTerm′ (emb p ⊩A) ⊩a

opaque

  -- Well-formed terms reduce to WHNF (given a certain assumption).

  whNormTerm :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Γ ⊢ t ∷ A → ∃ λ u → Whnf u × Γ ⊢ t ⇒* u ∷ A
  whNormTerm ⊢t =
    case reducible-⊩∷ ⊢t of λ
      (_ , ⊩t) →
    case wf-⊩∷ ⊩t of λ
      ⊩A →
    whNormTerm′ ⊩A (⊩∷→⊩∷/ ⊩A ⊩t)

private opaque

  -- A lemma used below.

  term-without-WHNF′ :
    Equality-reflection →
    Π-allowed p q →
    ∃₂ λ (Γ : Con Term 1) A →
      Γ ⊢ A ∷ U 0 ×
      (¬ ∃₂ λ Δ B → Whnf B × Δ ⊢ A ⇒* B) ×
      (¬ ∃₃ λ Δ B C → Whnf B × Δ ⊢ A ⇒* B ∷ C)
  term-without-WHNF′ {p} {q} ok₁ ok₂ =
    ε ∙ Empty , Ω , ⊢Ω ,
    (λ (_ , _ , B-whnf , A⇒*B) → without-WHNF₁ B-whnf A⇒*B) ,
    (λ (_ , _ , _ , B-whnf , A⇒*B) → without-WHNF₂ B-whnf A⇒*B)
    where
    ⊢U : ε ∙ Empty ⊢ U 0 ∷ U 1
    ⊢U = Uⱼ (∙ Emptyⱼ ε)

    Π≡U : ε ∙ Empty ⊢ Π p , q ▷ U 0 ▹ U 0 ≡ U 0
    Π≡U =
      _⊢_≡_.univ $
      ⊢∷Empty→⊢≡∷ ok₁ (var₀ (Emptyⱼ ε))
        (ΠΣⱼ ⊢U (wkTerm₁ (univ ⊢U) ⊢U) ok₂) ⊢U

    ω : Term 1
    ω = lam p (var x0 ∘⟨ p ⟩ var x0)

    Ω : Term 1
    Ω = ω ∘⟨ p ⟩ ω

    ⊢ω : ε ∙ Empty ⊢ ω ∷ U 0
    ⊢ω =
      conv
        (lamⱼ′ ok₂ $
         conv (var₀ (univ ⊢U))
           (sym (wkEq₁ (univ ⊢U) Π≡U)) ∘ⱼ
         var₀ (univ ⊢U))
        Π≡U

    ⊢Ω : ε ∙ Empty ⊢ Ω ∷ U 0
    ⊢Ω = conv ⊢ω (sym Π≡U) ∘ⱼ ⊢ω

    ¬-Whnf-Ω : ¬ Whnf Ω
    ¬-Whnf-Ω (ne (∘ₙ ()))

    without-WHNF₁ : Whnf A → ¬ Δ ⊢ Ω ⇒* A
    without-WHNF₁ Whnf-Ω (id _)           = ¬-Whnf-Ω Whnf-Ω
    without-WHNF₁ Whnf-u (univ Ω⇒t ⇨ t⇒u) =
      case inv-⇒-∘ Ω⇒t of λ where
        (inj₁ (_ , _ , ω⇒ , PE.refl)) → ⊥-elim (whnfRedTerm ω⇒ lamₙ)
        (inj₂ (_ , ω≡lam , PE.refl))  →
          case lam-PE-injectivity ω≡lam of λ {
            (_ , PE.refl) →
          without-WHNF₁ Whnf-u t⇒u }

    without-WHNF₂ : Whnf A → ¬ Δ ⊢ Ω ⇒* A ∷ B
    without-WHNF₂ Whnf-Ω (id _)      = ¬-Whnf-Ω Whnf-Ω
    without-WHNF₂ Whnf-u (Ω⇒t ⇨ t⇒u) =
      case inv-⇒-∘ Ω⇒t of λ where
        (inj₁ (_ , _ , ω⇒ , PE.refl)) → ⊥-elim (whnfRedTerm ω⇒ lamₙ)
        (inj₂ (_ , ω≡lam , PE.refl))  →
          case lam-PE-injectivity ω≡lam of λ {
            (_ , PE.refl) →
          without-WHNF₂ Whnf-u t⇒u }

opaque

  -- If equality reflection is allowed, then there is a well-formed
  -- type that does not reduce to WHNF (if at least one Π-type is
  -- allowed).

  type-without-WHNF :
    Equality-reflection →
    Π-allowed p q →
    ∃₂ λ (Γ : Con Term 1) A →
      Γ ⊢ A × ¬ ∃₂ λ Δ B → Whnf B × Δ ⊢ A ⇒* B
  type-without-WHNF ok₁ ok₂ =
    let _ , _ , ⊢A , hyp , _ = term-without-WHNF′ ok₁ ok₂ in
    _ , _ , univ ⊢A , hyp

opaque

  -- If equality reflection is allowed, then there is a well-typed
  -- term that does not reduce to WHNF (if at least one Π-type is
  -- allowed).

  term-without-WHNF :
    Equality-reflection →
    Π-allowed p q →
    ∃₃ λ (Γ : Con Term 1) t A →
      Γ ⊢ t ∷ A × ¬ ∃₃ λ Δ u B → Whnf u × Δ ⊢ t ⇒* u ∷ B
  term-without-WHNF ok₁ ok₂ =
    let _ , _ , ⊢A , _ , hyp = term-without-WHNF′ ok₁ ok₂ in
    _ , _ , _ , ⊢A , hyp
