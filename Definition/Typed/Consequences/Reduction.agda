------------------------------------------------------------------------
-- Properties of the reduction relation.
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.Reduction
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Untyped M
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.Consequences.Equality R
open import Definition.Typed.Consequences.Inequality R
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.RedSteps R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Fundamental.Reducibility R
open import Definition.LogicalRelation.ShapeView R

open import Tools.Empty
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    A B t u v : Term _
    p q : M
    l : TypeLevel
    m : Strength

opaque

  -- If the type of t is U, then t reduces to an application of a type
  -- constructor or a neutral term.

  red-U : Γ ⊢ t ∷ U → ∃ λ u → Type u × Γ ⊢ t :⇒*: u ∷ U
  red-U {Γ} {t} ⊢t =
    case reducibleTerm ⊢t of λ {
      (⊩U , ⊩t) →
    helper (U-elim ⊩U) (irrelevanceTerm ⊩U (U-intr (U-elim ⊩U)) ⊩t) }
    where
    helper :
      (⊩U : Γ ⊩⟨ l ⟩U) →
      Γ ⊩⟨ l ⟩ t ∷ U / U-intr ⊩U →
      ∃ λ u → Type u × Γ ⊢ t :⇒*: u ∷ U
    helper (emb 0<1 ⊩U) ⊩t =
      helper ⊩U ⊩t
    helper (noemb (Uᵣ _ _ _)) (Uₜ u t⇒*u u-type _ _) =
      u , u-type , t⇒*u

opaque

  -- If the type of t is Empty, then t reduces to a neutral term.

  red-Empty : Γ ⊢ t ∷ Empty → ∃ λ u → Neutral u × Γ ⊢ t :⇒*: u ∷ Empty
  red-Empty {Γ} {t} ⊢t =
    case reducibleTerm ⊢t of λ {
      (⊩Empty′ , ⊩t) →
    helper (Empty-elim ⊩Empty′)
      (irrelevanceTerm ⊩Empty′ (Empty-intr (Empty-elim ⊩Empty′)) ⊩t) }
    where
    helper :
      (⊩A : Γ ⊩⟨ l ⟩Empty A) →
      Γ ⊩⟨ l ⟩ t ∷ A / Empty-intr ⊩A →
      ∃ λ u → Neutral u × Γ ⊢ t :⇒*: u ∷ A
    helper (emb 0<1 ⊩A) ⊩t =
      helper ⊩A ⊩t
    helper (noemb A⇒*Empty) (Emptyₜ u t⇒*u _ (ne (neNfₜ u-ne _ _))) =
        u
      , u-ne
      , convRed:*: t⇒*u (sym (subset* (red A⇒*Empty)))

opaque

  -- If the type of t is Unit, then t reduces to star or a neutral
  -- term.

  red-Unit : Γ ⊢ t ∷ Unit m → ∃ λ u → Star u × Γ ⊢ t :⇒*: u ∷ Unit m
  red-Unit {Γ} {t} ⊢t =
    case reducibleTerm ⊢t of λ {
      (⊩Unit′ , ⊩t) →
    helper (Unit-elim ⊩Unit′)
      (irrelevanceTerm ⊩Unit′ (Unit-intr (Unit-elim ⊩Unit′)) ⊩t) }
    where
    helper :
      (⊩A : Γ ⊩⟨ l ⟩Unit⟨ m ⟩ A) →
      Γ ⊩⟨ l ⟩ t ∷ A / Unit-intr ⊩A →
      ∃ λ u → Star u × Γ ⊢ t :⇒*: u ∷ A
    helper (emb 0<1 ⊩A) ⊩t =
      helper ⊩A ⊩t
    helper (noemb (Unitₜ A⇒*Unit _)) (Unitₜ u t⇒*u _ prop) =
        u
      , (case prop of λ where
              starᵣ → starₙ
              (ne (neNfₜ neK ⊢k k≡k)) → ne neK)
      , convRed:*: t⇒*u (sym (subset* (red A⇒*Unit)))

opaque

  -- If the type of t is ℕ, then t reduces to zero, an application of
  -- suc, or a neutral term.

  red-ℕ : Γ ⊢ t ∷ ℕ → ∃ λ u → Natural u × Γ ⊢ t :⇒*: u ∷ ℕ
  red-ℕ {Γ} {t} ⊢t =
    case reducibleTerm ⊢t of λ {
      (⊩ℕ′ , ⊩t) →
    helper (ℕ-elim ⊩ℕ′) (irrelevanceTerm ⊩ℕ′ (ℕ-intr (ℕ-elim ⊩ℕ′)) ⊩t) }
    where
    helper :
      (⊩A : Γ ⊩⟨ l ⟩ℕ A) →
      Γ ⊩⟨ l ⟩ t ∷ A / ℕ-intr ⊩A →
      ∃ λ u → Natural u × Γ ⊢ t :⇒*: u ∷ A
    helper (emb 0<1 ⊩A) ⊩t =
      helper ⊩A ⊩t
    helper (noemb A⇒*ℕ) (ℕₜ u t⇒*u _ ok) =
        u
      , (case ok of λ where
           zeroᵣ                 → zeroₙ
           (sucᵣ _)              → sucₙ
           (ne (neNfₜ u-ne _ _)) → ne u-ne)
      , convRed:*: t⇒*u (sym (subset* (red A⇒*ℕ)))

opaque

  -- If t has a Π-type, then t reduces to a lambda or a neutral term.

  red-Π :
    Γ ⊢ t ∷ Π p , q ▷ A ▹ B →
    ∃ λ u → Function u × Γ ⊢ t :⇒*: u ∷ Π p , q ▷ A ▹ B
  red-Π {Γ} {t} {p} {q} ⊢t =
    case reducibleTerm ⊢t of λ {
      (⊩Π , ⊩t) →
    helper (Π-elim ⊩Π)
      (irrelevanceTerm ⊩Π (B-intr (BΠ p q) (Π-elim ⊩Π)) ⊩t) }
    where
    helper :
      (⊩A : Γ ⊩⟨ l ⟩B⟨ BΠ p q ⟩ A) →
      Γ ⊩⟨ l ⟩ t ∷ A / B-intr (BΠ p q) ⊩A →
      ∃ λ u → Function u × Γ ⊢ t :⇒*: u ∷ A
    helper (emb 0<1 ⊩A) ⊩t =
      helper ⊩A ⊩t
    helper (noemb (Bᵣ _ _ A⇒*Π _ _ _ _ _ _ _)) (u , t⇒*u , u-fun , _) =
      u , u-fun , convRed:*: t⇒*u (sym (subset* (red A⇒*Π)))

opaque

  -- If t has a Σ-type, then t reduces to a pair or a neutral term.

  red-Σ :
    Γ ⊢ t ∷ Σ⟨ m ⟩ p , q ▷ A ▹ B →
    ∃ λ u → Product u × Γ ⊢ t :⇒*: u ∷ Σ⟨ m ⟩ p , q ▷ A ▹ B
  red-Σ {Γ} {t} {m} {p} {q} ⊢t =
    case reducibleTerm ⊢t of λ {
      (⊩Σ , ⊩t) →
    helper (Σ-elim ⊩Σ)
      (irrelevanceTerm ⊩Σ (B-intr (BΣ m p q) (Σ-elim ⊩Σ)) ⊩t) }
    where
    helper :
      (⊩A : Γ ⊩⟨ l ⟩B⟨ BΣ m p q ⟩ A) →
      Γ ⊩⟨ l ⟩ t ∷ A / B-intr (BΣ m p q) ⊩A →
      ∃ λ u → Product u × Γ ⊢ t :⇒*: u ∷ A
    helper (emb 0<1 ⊩A) ⊩t =
      helper ⊩A ⊩t
    helper
      (noemb (Bᵣ _ _ A⇒*Σ _ _ _ _ _ _ _)) (u , t⇒*u , _ , u-prod , _) =
      u , u-prod , convRed:*: t⇒*u (sym (subset* (red A⇒*Σ)))

opaque

  -- If the type of t is Id A u v, then t reduces to rfl or a neutral
  -- term.

  red-Id :
    Γ ⊢ t ∷ Id A u v →
    ∃ λ w → Identity w × Γ ⊢ t :⇒*: w ∷ Id A u v
  red-Id {Γ} {t} ⊢t =
    case reducibleTerm ⊢t of λ {
      (⊩Id , ⊩t) →
    helper (Id-elim ⊩Id)
      (irrelevanceTerm ⊩Id (Id-intr (Id-elim ⊩Id)) ⊩t) }
    where
    helper :
      (⊩A : Γ ⊩⟨ l ⟩Id A) →
      Γ ⊩⟨ l ⟩ t ∷ A / Id-intr ⊩A →
      ∃ λ w → Identity w × Γ ⊢ t :⇒*: w ∷ A
    helper (emb 0<1 ⊩A) ⊩t =
      helper ⊩A ⊩t
    helper (noemb ⊩A) (w , t⇒*w , w-id , _) =
        w
      , w-id
      , convRed:*: t⇒*w (sym (subset* (red (_⊩ₗId_.⇒*Id ⊩A))))

-- Helper function where all reducible types can be reduced to WHNF.
whNorm′ : ∀ {A l} ([A] : Γ ⊩⟨ l ⟩ A)
                → ∃ λ B → Whnf B × Γ ⊢ A :⇒*: B
whNorm′ (Uᵣ′ .⁰ 0<1 ⊢Γ) = U , Uₙ , idRed:*: (Uⱼ ⊢Γ)
whNorm′ (ℕᵣ D) = ℕ , ℕₙ , D
whNorm′ (Emptyᵣ D) = Empty , Emptyₙ , D
whNorm′ (Unitᵣ (Unitₜ D _)) = Unit! , Unitₙ , D
whNorm′ (ne′ H D neH H≡H) = H , ne neH , D
whNorm′ (Πᵣ′ F G D _ _ _ _ _ _ _) = Π _ , _ ▷ F ▹ G , ΠΣₙ , D
whNorm′ (𝕨′ F G D _ _ _ _ _ _ _) = Σ _ , _ ▷ F ▹ G , ΠΣₙ , D
whNorm′ (Idᵣ ⊩Id) = _ , Idₙ , _⊩ₗId_.⇒*Id ⊩Id
whNorm′ (emb 0<1 [A]) = whNorm′ [A]

-- Well-formed types can all be reduced to WHNF.
whNorm : ∀ {A} → Γ ⊢ A → ∃ λ B → Whnf B × Γ ⊢ A :⇒*: B
whNorm A = whNorm′ (reducible A)

ΠNorm : ∀ {A F G} → Γ ⊢ A → Γ ⊢ A ≡ Π p , q ▷ F ▹ G
      → ∃₂ λ F′ G′ → Γ ⊢ A ⇒* Π p , q ▷ F′ ▹ G′ × Γ ⊢ F ≡ F′
         × Γ ∙ F ⊢ G ≡ G′
ΠNorm {A = A} ⊢A A≡ΠFG with whNorm ⊢A
... | _ , Uₙ , D = ⊥-elim (U≢Π (trans (sym (subset* (red D))) A≡ΠFG))
... | _ , ΠΣₙ {b = BMΠ} , D =
  let Π≡Π′ = trans (sym A≡ΠFG) (subset* (red D))
      F≡F′ , G≡G′ , p≡p′ , q≡q′ = injectivity Π≡Π′
      D′ = PE.subst₂ (λ p q → _ ⊢ A ⇒* Π p , q ▷ _ ▹ _) (PE.sym p≡p′) (PE.sym q≡q′) (red D)
  in  _ , _ , D′ , F≡F′ , G≡G′
... | _ , ΠΣₙ {b = BMΣ s} , D = ⊥-elim (Π≢Σⱼ (trans (sym A≡ΠFG) (subset* (red D))))
... | _ , ℕₙ , D = ⊥-elim (ℕ≢Π (trans (sym (subset* (red D))) A≡ΠFG))
... | _ , Unitₙ , D = ⊥-elim (Unit≢Πⱼ (trans (sym (subset* (red D))) A≡ΠFG))
... | _ , Emptyₙ , D = ⊥-elim (Empty≢Πⱼ (trans (sym (subset* (red D))) A≡ΠFG))
... | _ , Idₙ , A⇒*Id =
  ⊥-elim $ Id≢Π (trans (sym (subset* (red A⇒*Id))) A≡ΠFG)
... | _ , lamₙ , [ ⊢A , univ ⊢B , A⇒B ] =
  let _ , _ , _ , _ , _ , U≡Π , _ = inversion-lam ⊢B
  in  ⊥-elim (U≢Π U≡Π)
... | _ , zeroₙ , [ ⊢A , univ ⊢B , A⇒B ] = ⊥-elim (U≢ℕ (inversion-zero ⊢B))
... | _ , sucₙ , [ ⊢A , univ ⊢B , A⇒B ] = ⊥-elim (U≢ℕ (proj₂ (inversion-suc ⊢B)))
... | _ , starₙ , [ _ , univ ⊢B , _ ] =
  ⊥-elim (U≢Unitⱼ (inversion-star ⊢B .proj₁))
... | _ , prodₙ , [ _ , univ ⊢B , _ ] =
  let _ , _ , _ , _ , _ , _ , _ , U≡Σ , _ = inversion-prod ⊢B
  in  ⊥-elim (U≢Σ U≡Σ)
... | _ , rflₙ , [ _ , univ ⊢rfl , _ ] =
  ⊥-elim $ Id≢U $ sym (inversion-rfl ⊢rfl .proj₂ .proj₂ .proj₂ .proj₂)
... | _ , ne x , D = ⊥-elim (Π≢ne x (trans (sym A≡ΠFG) (subset* (red D))))

ΣNorm : ∀ {A F G m} → Γ ⊢ A → Γ ⊢ A ≡ Σ⟨ m ⟩ p , q ▷ F ▹ G
      → ∃₂ λ F′ G′ → Γ ⊢ A ⇒* Σ⟨ m ⟩ p , q ▷ F′ ▹ G′
         × Γ ⊢ F ≡ F′ × Γ ∙ F ⊢ G ≡ G′
ΣNorm {A = A} ⊢A A≡ΣFG with whNorm ⊢A
... | _ , Uₙ , D = ⊥-elim (U≢Σ (trans (sym (subset* (red D))) A≡ΣFG))
... | _ , (ΠΣₙ {b = BMΠ}) , D = ⊥-elim (Π≢Σⱼ (trans (sym (subset* (red D))) A≡ΣFG))
... | _ , (ΠΣₙ {b = BMΣ m}) , D =
  let Σ≡Σ′ = trans (sym A≡ΣFG) (subset* (red D))
      F≡F′ , G≡G′ , p≡p′ , q≡q′ , m≡m′ = Σ-injectivity Σ≡Σ′
      D′ = PE.subst₃ (λ m p q → _ ⊢ A ⇒* Σ⟨ m ⟩ p , q ▷ _ ▹ _)
                     (PE.sym m≡m′) (PE.sym p≡p′) (PE.sym q≡q′) (red D)
  in  _ , _ , D′ , F≡F′ , G≡G′
... | _ , ℕₙ , D = ⊥-elim (ℕ≢Σ (trans (sym (subset* (red D))) A≡ΣFG))
... | _ , Unitₙ , D = ⊥-elim (Unit≢Σⱼ (trans (sym (subset* (red D))) A≡ΣFG))
... | _ , Emptyₙ , D = ⊥-elim (Empty≢Σⱼ (trans (sym (subset* (red D))) A≡ΣFG))
... | _ , Idₙ , A⇒*Id =
  ⊥-elim $ Id≢Σ (trans (sym (subset* (red A⇒*Id))) A≡ΣFG)
... | _ , lamₙ , [ ⊢A , univ ⊢B , A⇒B ] =
  let _ , _ , _ , _ , _ , U≡Π , _ = inversion-lam ⊢B
  in  ⊥-elim (U≢Π U≡Π)
... | _ , zeroₙ , [ ⊢A , univ ⊢B , A⇒B ] = ⊥-elim (U≢ℕ (inversion-zero ⊢B))
... | _ , sucₙ , [ ⊢A , univ ⊢B , A⇒B ] = ⊥-elim (U≢ℕ (proj₂ (inversion-suc ⊢B)))
... | _ , starₙ , [ _ , univ ⊢B , _ ] =
  ⊥-elim (U≢Unitⱼ (inversion-star ⊢B .proj₁))
... | _ , prodₙ , [ _ , univ ⊢B , _ ] =
  let _ , _ , _ , _ , _ , _ , _ , U≡Σ , _ = inversion-prod ⊢B
  in  ⊥-elim (U≢Σ U≡Σ)
... | _ , rflₙ , [ _ , univ ⊢rfl , _ ] =
  ⊥-elim $ Id≢U $ sym (inversion-rfl ⊢rfl .proj₂ .proj₂ .proj₂ .proj₂)
... | _ , ne x , D = ⊥-elim (Σ≢ne x (trans (sym A≡ΣFG) (subset* (red D))))

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
    case trans (sym A≡Id) (subset* (red A⇒*A′)) of λ {
      Id≡A′ →
    case Id≡Whnf Id≡A′ A′-whnf of λ {
      (_ , _ , _ , PE.refl) →
    _ , _ , _ , red A⇒*A′ , Id-injectivity Id≡A′ }}}

-- Helper function where reducible all terms can be reduced to WHNF.
whNormTerm′ : ∀ {a A l} ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ a ∷ A / [A]
                → ∃ λ b → Whnf b × Γ ⊢ a :⇒*: b ∷ A
whNormTerm′ (Uᵣ x) (Uₜ A d typeA A≡A [t]) = A , typeWhnf typeA , d
whNormTerm′ (ℕᵣ x) (ℕₜ n d n≡n prop) =
  let natN = natural prop
  in  n , naturalWhnf natN , convRed:*: d (sym (subset* (red x)))
whNormTerm′ (Emptyᵣ x) (Emptyₜ n d n≡n prop) =
  let emptyN = empty prop
  in  n , ne emptyN , convRed:*: d (sym (subset* (red x)))
whNormTerm′ (Unitᵣ (Unitₜ x _)) (Unitₜ n d n≡n prop) =
  n , unit prop , convRed:*: d (sym (subset* (red x)))
whNormTerm′ (ne (ne H D neH H≡H)) (neₜ k d (neNfₜ neH₁ ⊢k k≡k)) =
  k , ne neH₁ , convRed:*: d (sym (subset* (red D)))
whNormTerm′ (Πᵣ′ _ _ D _ _ _ _ _ _ _) (Πₜ f d funcF _ _ _) =
  f , functionWhnf funcF , convRed:*: d (sym (subset* (red D)))
whNormTerm′ (𝕨′ _ _ D _ _ _ _ _ _ _) (Σₜ p d _ pProd _) =
  p , productWhnf pProd , convRed:*: d (sym (subset* (red D)))
whNormTerm′ (Idᵣ ⊩Id) (a′ , a⇒*a′ , a′-id , _) =
    a′ , identityWhnf a′-id
  , convRed:*: a⇒*a′ (sym (subset* (red (_⊩ₗId_.⇒*Id ⊩Id))))
whNormTerm′ (emb 0<1 [A]) [a] = whNormTerm′ [A] [a]

-- Well-formed terms can all be reduced to WHNF.
whNormTerm : ∀ {a A} → Γ ⊢ a ∷ A → ∃ λ b → Whnf b × Γ ⊢ a :⇒*: b ∷ A
whNormTerm {a} {A} ⊢a =
  let [A] , [a] = reducibleTerm ⊢a
  in  whNormTerm′ [A] [a]

redMany : ∀ {t u A} → Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ⇒* u ∷ A
redMany d =
  let _ , _ , ⊢u = syntacticEqTerm (subsetTerm d)
  in  d ⇨ id ⊢u
