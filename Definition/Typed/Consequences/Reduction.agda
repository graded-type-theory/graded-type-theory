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
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.Consequences.Equality R
open import Definition.Typed.Consequences.Inequality R as I
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Inversion R
open import Definition.Typed.Reasoning.Type R
open import Definition.Typed.RedSteps R
open import Definition.Typed.Syntactic R
open import Definition.Typed.Well-formed R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Fundamental.Reducibility R
open import Definition.LogicalRelation.Substitution.Introductions R

open import Tools.Empty
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    A B C t u v : Term _
    p q : M
    b : BinderMode
    m s : Strength
    l : Universe-level

opaque

  -- If the type of t is U l, then t reduces to an application of a
  -- type constructor or a neutral term.

  red-U : Γ ⊢ t ∷ U l → ∃ λ u → Type u × Γ ⊢ t ⇒* u ∷ U l
  red-U ⊢t =
    case ⊩∷U⇔ .proj₁ $ proj₂ $ reducible-⊩∷ ⊢t of λ
      (_ , _ , u , t⇒*u , u-type , _) →
    u , u-type , t⇒*u

opaque

  -- If the type of t is Empty, then t reduces to a neutral term.

  red-Empty : Γ ⊢ t ∷ Empty → ∃ λ u → Neutral u × Γ ⊢ t ⇒* u ∷ Empty
  red-Empty ⊢t =
    case ⊩∷Empty⇔ .proj₁ $ proj₂ $ reducible-⊩∷ ⊢t of λ {
      (Emptyₜ u t⇒*u _ (ne (neNfₜ u-ne _))) →
    u , u-ne , t⇒*u }

opaque

  -- If t has a unit type, then t reduces to star or a neutral term.

  red-Unit : Γ ⊢ t ∷ Unit s l → ∃ λ u → Star u × Γ ⊢ t ⇒* u ∷ Unit s l
  red-Unit ⊢t =
    case ⊩∷Unit⇔ .proj₁ $ proj₂ $ reducible-⊩∷ ⊢t of λ {
      (_ , _ , Unitₜ u t⇒*u _ rest) →
      u
    , (case rest of λ where
         starᵣ               → starₙ
         (ne (neNfₜ u-ne _)) → ne u-ne)
    , t⇒*u }

opaque

  -- If the type of t is ℕ, then t reduces to zero, an application of
  -- suc, or a neutral term.

  red-ℕ : Γ ⊢ t ∷ ℕ → ∃ λ u → Natural u × Γ ⊢ t ⇒* u ∷ ℕ
  red-ℕ ⊢t =
    case ⊩∷ℕ⇔ .proj₁ $ proj₂ $ reducible-⊩∷ ⊢t of λ {
      (ℕₜ u t⇒*u _ rest) →
      u
    , (case rest of λ where
         zeroᵣ               → zeroₙ
         (sucᵣ _)            → sucₙ
         (ne (neNfₜ u-ne _)) → ne u-ne)
    , t⇒*u }

opaque

  -- If t has a Π-type, then t reduces to a lambda or a neutral term.

  red-Π :
    Γ ⊢ t ∷ Π p , q ▷ A ▹ B →
    ∃ λ u → Function u × Γ ⊢ t ⇒* u ∷ Π p , q ▷ A ▹ B
  red-Π ⊢t =
    case ⊩∷Π⇔ .proj₁ $ proj₂ $ reducible-⊩∷ ⊢t of λ
      (_ , u , t⇒*u , u-fun , _) →
    u , u-fun , t⇒*u

opaque

  -- If t has a Σ-type, then t reduces to a pair or a neutral term.

  red-Σ :
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
  -- term.

  red-Id :
    Γ ⊢ t ∷ Id A u v →
    ∃ λ w → Identity w × Γ ⊢ t ⇒* w ∷ Id A u v
  red-Id ⊢t =
    case ⊩∷Id⇔ .proj₁ $ proj₂ $ reducible-⊩∷ ⊢t of λ
      (w , t⇒*w , _ , _ , rest) →
      w
    , (case rest of λ where
         (rflᵣ _)    → rflₙ
         (ne w-ne _) → ne w-ne)
    , t⇒*w

-- Helper function where all reducible types can be reduced to WHNF.
whNorm′ : ∀ {A l} ([A] : Γ ⊩⟨ l ⟩ A)
                → ∃ λ B → Whnf B × Γ ⊢ A ⇒* B
whNorm′ (Uᵣ′ l _ ⇒*U) = U l , Uₙ , ⇒*U
whNorm′ (ℕᵣ D) = ℕ , ℕₙ , D
whNorm′ (Emptyᵣ D) = Empty , Emptyₙ , D
whNorm′ (Unitᵣ (Unitₜ D _)) = Unit! , Unitₙ , D
whNorm′ (ne′ H D neH H≡H) = H , ne neH , D
whNorm′ (Πᵣ′ F G D _ _ _ _ _) = Π _ , _ ▷ F ▹ G , ΠΣₙ , D
whNorm′ (𝕨′ F G D _ _ _ _ _) = Σ _ , _ ▷ F ▹ G , ΠΣₙ , D
whNorm′ (Idᵣ ⊩Id) = _ , Idₙ , _⊩ₗId_.⇒*Id ⊩Id
whNorm′ (emb ≤ᵘ-refl     ⊩A) = whNorm′ ⊩A
whNorm′ (emb (≤ᵘ-step p) ⊩A) = whNorm′ (emb p ⊩A)

-- Well-formed types can all be reduced to WHNF.
whNorm : ∀ {A} → Γ ⊢ A → ∃ λ B → Whnf B × Γ ⊢ A ⇒* B
whNorm A = whNorm′ (reducible-⊩ A .proj₂)

opaque

  -- If A is definitionally equal to U l, then A reduces to U l.

  U-norm : Γ ⊢ A ≡ U l → Γ ⊢ A ⇒* U l
  U-norm {A} {l} A≡U =
    let B , B-whnf , A⇒*B = whNorm (syntacticEq A≡U .proj₁)
        U≡B               =
          U l  ≡˘⟨ A≡U ⟩⊢
          A    ≡⟨ subset* A⇒*B ⟩⊢∎
          B    ∎
    in
    PE.subst (_⊢_⇒*_ _ _) (U≡A U≡B B-whnf) A⇒*B

opaque

  -- If A is definitionally equal to ΠΣ⟨ b ⟩ p , q ▷ B ▹ C, then A
  -- reduces to ΠΣ⟨ b ⟩ p , q ▷ B′ ▹ C′, where B′ and C′ satisfy
  -- Γ ⊢ B ≡ B′ and Γ ∙ B ⊢ C ≡ C′.

  ΠΣNorm :
    Γ ⊢ A ≡ ΠΣ⟨ b ⟩ p , q ▷ B ▹ C →
    ∃₂ λ B′ C′ →
      Γ ⊢ A ⇒* ΠΣ⟨ b ⟩ p , q ▷ B′ ▹ C′ × Γ ⊢ B ≡ B′ × Γ ∙ B ⊢ C ≡ C′
  ΠΣNorm {A} A≡ΠΣ with whNorm (syntacticEq A≡ΠΣ .proj₁)
  … | _ , Uₙ , D =
    ⊥-elim (U≢ΠΣⱼ (trans (sym (subset* D)) A≡ΠΣ))
  … | _ , ΠΣₙ , D =
    let B≡B′ , C≡C′ , p≡p′ , q≡q′ , b≡b′ =
          ΠΣ-injectivity (trans (sym A≡ΠΣ) (subset* D))
        D′ = PE.subst₃ (λ b p q → _ ⊢ A ⇒* ΠΣ⟨ b ⟩ p , q ▷ _ ▹ _)
               (PE.sym b≡b′) (PE.sym p≡p′) (PE.sym q≡q′) D
    in
    _ , _ , D′ , B≡B′ , C≡C′
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
        ⊥-elim (U≢Π U≡Π)
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
        ⊥-elim (U≢Σ U≡Σ)
  … | _ , rflₙ , A⇒rfl =
    case wf-⊢≡ (subset* A⇒rfl) of λ where
      (_ , univ ⊢rfl) →
        ⊥-elim $ Id≢U $
        sym (inversion-rfl ⊢rfl .proj₂ .proj₂ .proj₂ .proj₂)
  … | _ , ne n , D =
    ⊥-elim (I.ΠΣ≢ne n (trans (sym A≡ΠΣ) (subset* D)))

opaque

  -- If A is definitionally equal to Id B t u, then A reduces to
  -- Id B′ t′ u′ for some B′, t′ and u′ that are definitionally equal to
  -- B, t and u.

  Id-norm :
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
whNormTerm′ (ne (ne H D neH H≡H)) (neₜ k d (neNfₜ neH₁ k≡k)) =
  k , ne neH₁ , conv* d (sym (subset* D))
whNormTerm′ (Πᵣ′ _ _ D _ _ _ _ _) (Πₜ f d funcF _ _ _) =
  f , functionWhnf funcF , conv* d (sym (subset* D))
whNormTerm′ (𝕨′ _ _ D _ _ _ _ _) (Σₜ p d _ pProd _) =
  p , productWhnf pProd , conv* d (sym (subset* D))
whNormTerm′ (Idᵣ ⊩Id) (a′ , a⇒*a′ , a′-id , _) =
    a′ , identityWhnf a′-id
  , conv* a⇒*a′ (sym (subset* (_⊩ₗId_.⇒*Id ⊩Id)))
whNormTerm′ (emb ≤ᵘ-refl     ⊩A) ⊩a = whNormTerm′ ⊩A ⊩a
whNormTerm′ (emb (≤ᵘ-step p) ⊩A) ⊩a = whNormTerm′ (emb p ⊩A) ⊩a

opaque

  -- Well-formed terms reduce to WHNFs.

  whNormTerm : Γ ⊢ t ∷ A → ∃ λ u → Whnf u × Γ ⊢ t ⇒* u ∷ A
  whNormTerm ⊢t =
    case reducible-⊩∷ ⊢t of λ
      (_ , ⊩t) →
    case wf-⊩∷ ⊩t of λ
      ⊩A →
    whNormTerm′ ⊩A (⊩∷→⊩∷/ ⊩A ⊩t)
