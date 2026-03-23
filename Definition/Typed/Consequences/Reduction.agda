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
open import Definition.Untyped.Allowed-literal R
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Neutral.Atomic M type-variant
open import Definition.Untyped.Omega M
open import Definition.Untyped.Properties M
open import Definition.Untyped.Whnf M type-variant
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.Consequences.Canonicity R
open import Definition.Typed.Consequences.Equality R
open import Definition.Typed.Consequences.Inequality R as I
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Consequences.Inversion R
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
open import Definition.LogicalRelation.Unary R

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
import Tools.Level as L
open import Tools.Nat using (Nat)
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum
open import Tools.Unit

private
  variable
    ∇ : DCon (Term 0) _
    Δ : Con Term _
    Γ : Cons _ _
    A B C t u v w : Term _
    l : Lvl _
    p q : M
    b : BinderMode
    m s : Strength

-- Is-level ∇ holds for zeroᵘ, applications of sucᵘ, and (certain)
-- neutral terms.

data Is-level {m n} (∇ : DCon (Term 0) m) : Term n → Set a where
  zeroᵘ : Is-level ∇ zeroᵘ
  sucᵘ  : Is-level ∇ (sucᵘ t)
  ne    : Neutral⁺ ∇ t → Is-level ∇ t

opaque

  -- If the type of l is Level, then l reduces to an application of a
  -- level constructor or a neutral term (given a certain assumption).

  red-Level :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    Γ ⊢ t ∷ Level → ∃ λ u → Is-level (Γ .defs) u × Γ ⊢ t ⇒* u ∷ Level
  red-Level ⊢t =
    case ⊩∷Level⇔ .proj₁ $ proj₂ $ reducible-⊩∷ ⊢t of λ where
      (okᴸ , literal ok _) →
        Level-allowed→Allowed-literal→ okᴸ ok
      (_ , term t⇒u u-prop) →
        _ ,
        (case u-prop of λ where
           (zeroᵘᵣ _)  → zeroᵘ
           (sucᵘᵣ _ _) → sucᵘ
           (neLvl n)   → ne (ne→ _ (nelevel n))) ,
        t⇒u

opaque

  -- If the type of t is U l, then t reduces to an application of a
  -- type constructor or a neutral term (given a certain assumption).

  red-U :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    Γ ⊢ t ∷ U l → ∃ λ u →
    Type No-equality-reflection (Γ .defs) u × Γ ⊢ t ⇒* u ∷ U l
  red-U ⊢t =
    case ⊩∷U⇔ .proj₁ $ proj₂ $ reducible-⊩∷ ⊢t of λ
      (_ , _ , _ , u , t⇒*u , u-type , _) →
    u , u-type , t⇒*u

opaque

  -- If the type of t is Empty, then t reduces to a neutral term
  -- (given a certain assumption).

  red-Empty :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    Γ ⊢ t ∷ Empty → ∃ λ u →
    Neutral No-equality-reflection (Γ .defs) u × Γ ⊢ t ⇒* u ∷ Empty
  red-Empty ⊢t =
    case ⊩∷Empty⇔ .proj₁ $ proj₂ $ reducible-⊩∷ ⊢t of λ {
      (Emptyₜ u t⇒*u _ (ne (neNfₜ u-ne _))) →
    u , ne⁻ u-ne , t⇒*u }

opaque

  -- WHNFs of type Empty are neutral (given a certain assumption).

  ⊢∷Empty→Whnf→Neutral :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    Γ ⊢ t ∷ Empty →
    Whnf (Γ .defs) t →
    Neutral⁺ (Γ .defs) t
  ⊢∷Empty→Whnf→Neutral ⊢t t-whnf =
    case red-Empty ⊢t of λ
      (_ , u-ne , t⇒*u) →
    case whnfRed*Term t⇒*u t-whnf of λ {
      PE.refl →
    ne→ _ u-ne }

opaque

  -- If t has a unit type, then t reduces to star or a neutral term
  -- (given a certain assumption).

  red-Unit :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    Γ ⊢ t ∷ Unit s →
    ∃ λ u →
      Star No-equality-reflection (Γ .defs) u × Γ ⊢ t ⇒* u ∷ Unit s
  red-Unit ⊢t =
    case ⊩∷Unit⇔ .proj₁ $ proj₂ $ reducible-⊩∷ ⊢t of λ {
      (_ , Unitₜ u (t⇒*u , u-whnf) _) →
      u
    , (case whnfStar (wf-⊢ (subset*Term t⇒*u) .proj₂ .proj₂)
              u-whnf of λ where
         starₙ     → starₙ
         (ne u-ne) → ne (or-empty-Neutral u-ne))
    , t⇒*u }

opaque

  -- If the type of t is ℕ, then t reduces to zero, an application of
  -- suc, or a neutral term (given a certain assumption).

  red-ℕ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    Γ ⊢ t ∷ ℕ → ∃ λ u →
    Natural No-equality-reflection (Γ .defs) u × Γ ⊢ t ⇒* u ∷ ℕ
  red-ℕ ⊢t =
    case ⊩∷ℕ⇔ .proj₁ $ proj₂ $ reducible-⊩∷ ⊢t of λ {
      (ℕₜ u t⇒*u _ rest) →
      u
    , (case rest of λ where
         zeroᵣ               → zeroₙ
         (sucᵣ _)            → sucₙ
         (ne (neNfₜ u-ne _)) → ne (ne⁻ u-ne))
    , t⇒*u }

opaque

  -- If t has a Π-type, then t reduces to a lambda or a neutral term
  -- (given a certain assumption).

  red-Π :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    Γ ⊢ t ∷ Π p , q ▷ A ▹ B →
    ∃ λ u → Function No-equality-reflection (Γ .defs) u ×
            Γ ⊢ t ⇒* u ∷ Π p , q ▷ A ▹ B
  red-Π ⊢t =
    case ⊩∷Π⇔ .proj₁ $ proj₂ $ reducible-⊩∷ ⊢t of λ
      (_ , u , t⇒*u , u-fun , _) →
    u , Functionᵃ→ u-fun , t⇒*u

opaque

  -- If t has a Σ-type, then t reduces to a pair or a neutral term
  -- (given a certain assumption).

  red-Σ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    Γ ⊢ t ∷ Σ⟨ m ⟩ p , q ▷ A ▹ B →
    ∃ λ u → Product No-equality-reflection (Γ .defs) u ×
            Γ ⊢ t ⇒* u ∷ Σ⟨ m ⟩ p , q ▷ A ▹ B
  red-Σ {m = 𝕤} ⊢t =
    case ⊩∷Σˢ⇔ .proj₁ $ proj₂ $ reducible-⊩∷ ⊢t of λ
      (_ , u , t⇒*u , u-prod , _) →
    u , Productᵃ→ u-prod , t⇒*u
  red-Σ {m = 𝕨} ⊢t =
    case ⊩∷Σʷ⇔ .proj₁ $ proj₂ $ reducible-⊩∷ ⊢t of λ
      (_ , u , t⇒*u , _ , rest) →
    u , Productᵃ→ (⊩∷Σʷ→Product rest) , t⇒*u

opaque

  -- If the type of t is Id A u v, then t reduces to rfl or a neutral
  -- term (given a certain assumption).

  red-Id :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    Γ ⊢ t ∷ Id A u v →
    ∃ λ w → Identity No-equality-reflection (Γ .defs) w ×
            Γ ⊢ t ⇒* w ∷ Id A u v
  red-Id ⊢t =
    case ⊩∷Id⇔ .proj₁ $ proj₂ $ reducible-⊩∷ ⊢t of λ
      (w , t⇒*w , _ , _ , rest) →
      w
    , (case rest of λ where
         (rflᵣ _)    → rflₙ
         (ne w-ne _) → ne (ne⁻ w-ne))
    , t⇒*w

opaque

  -- A variant of red-Id.

  red-Id′ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    Γ ⊢ t ∷ Id A u v →
    ∃ λ w → Γ ⊢ t ⇒* w ∷ Id A u v ×
      ∃ λ (w-id : Identity No-equality-reflection (Γ .defs) w) →
      Identity-rec w-id (Γ ⊢ u ≡ v ∷ A) (L.Lift _ ⊤)
  red-Id′ {Γ} ⊢t =
    let _ , w-id , t⇒*w = red-Id ⊢t in
    _ , t⇒*w , w-id ,
    lemma (wf-⊢ (subset*Term t⇒*w) .proj₂ .proj₂) w-id
    where
    lemma :
      Γ ⊢ w ∷ Id A u v →
      (w-id : Identity No-equality-reflection (Γ .defs) w) →
      Identity-rec w-id (Γ ⊢ u ≡ v ∷ A) (L.Lift _ ⊤)
    lemma ⊢w rflₙ   = inversion-rfl-Id ⊢w
    lemma ⊢w (ne _) = _

-- Helper function where all reducible types can be reduced to WHNF.
whNorm′ : ∀ {A l} ([A] : Γ ⊩⟨ l ⟩ A)
                → ∃ λ B → Whnf (Γ .defs) B × Γ ⊢ A ⇒* B
whNorm′ (Levelᵣ D) = Level , Levelₙ , D
whNorm′ (Uᵣ′ l _ _ ⇒*U) = U l , Uₙ , ⇒*U
whNorm′ (Liftᵣ′ D [k] [F]) = Lift _ _ , Liftₙ , D
whNorm′ (ℕᵣ D) = ℕ , ℕₙ , D
whNorm′ (Emptyᵣ D) = Empty , Emptyₙ , D
whNorm′ (Unitᵣ′ D _) = Unit! , Unitₙ , D
whNorm′ (ne′ H D neH H≡H) = H , ne-whnf neH , D
whNorm′ (Πᵣ′ F G D _ _ _ _ _) = Π _ , _ ▷ F ▹ G , ΠΣₙ , D
whNorm′ (Σᵣ′ F G D _ _ _ _ _) = Σ _ , _ ▷ F ▹ G , ΠΣₙ , D
whNorm′ (Idᵣ ⊩Id) = _ , Idₙ , _⊩ₗId_.⇒*Id ⊩Id

opaque

  -- Well-formed types reduce to WHNF (given a certain assumption).

  whNorm :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    Γ ⊢ A → ∃ λ B → Whnf (Γ .defs) B × Γ ⊢ A ⇒* B
  whNorm A = whNorm′ (reducible-⊩ A .proj₂)

opaque

  -- If A is definitionally equal to U l, then A reduces to a universe (given
  -- a certain assumption).

  U-norm :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    Γ ⊢ A ≡ U l → ∃ λ k → Γ ⊢ A ⇒* U k
  U-norm {A} {l} A≡U =
    let B , B-whnf , A⇒*B = whNorm (syntacticEq A≡U .proj₁)
        U≡B               =
          U l  ≡˘⟨ A≡U ⟩⊢
          A    ≡⟨ subset* A⇒*B ⟩⊢∎
          B    ∎
    in
    Σ.map idᶠ (λ eq → PE.subst (_⊢_⇒*_ _ _) eq A⇒*B) (U≡A U≡B B-whnf)

opaque

  Lift-norm :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    Γ ⊢ A ≡ Lift l B →
    ∃₂ λ k C → Γ ⊢ A ⇒* Lift k C
  Lift-norm {A} {l} {B} A≡Lift =
    case whNorm (syntacticEq A≡Lift .proj₁) of λ
      (A′ , A′-whnf , A⇒*A′) →
    let Lift≡A′ =
          Lift l B  ≡˘⟨ A≡Lift ⟩⊢
          A         ≡⟨ subset* A⇒*A′ ⟩⊢∎
          A′        ∎
    in case Lift≡A Lift≡A′ A′-whnf of λ {
      (_ , _ , PE.refl) →
    _ , _ , A⇒*A′ }

opaque

  -- If A is definitionally equal to Unit s, then A reduces to Unit s
  -- (given a certain assumption).

  Unit-norm :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    Γ ⊢ A ≡ Unit s → Γ ⊢ A ↘ Unit s
  Unit-norm A≡Unit =
    let ⊢A , _ = wf-⊢ A≡Unit in
    case whNorm ⊢A of λ
      (_ , B-whnf , A⇒*B) →
    case Unit≡A (trans (sym A≡Unit) (subset* A⇒*B)) B-whnf of λ {
      PE.refl →
    A⇒*B , Unitₙ }

opaque

  -- If equality reflection is not allowed or the context is empty,
  -- and A is definitionally equal to ΠΣ⟨ b ⟩ p , q ▷ B ▹ C, then A
  -- reduces to ΠΣ⟨ b ⟩ p , q ▷ B′ ▹ C′, where B′ satisfies
  -- Γ ⊢ B ≡ B′, and C′ satisfies certain properties.

  ΠΣNorm :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    Γ ⊢ A ≡ ΠΣ⟨ b ⟩ p , q ▷ B ▹ C →
    ∃₂ λ B′ C′ →
      Γ ⊢ A ⇒* ΠΣ⟨ b ⟩ p , q ▷ B′ ▹ C′ × Γ ⊢ B ≡ B′ ×
      (⦃ not-ok : No-equality-reflection ⦄ → Γ »∙ B ⊢ C ≡ C′) ×
      (∀ {t u} → Γ ⊢ t ≡ u ∷ B → Γ ⊢ C [ t ]₀ ≡ C′ [ u ]₀)
  ΠΣNorm {A} A≡ΠΣ with whNorm (syntacticEq A≡ΠΣ .proj₁)
  … | _ , Levelₙ , D =
    ⊥-elim (Level≢ΠΣⱼ (trans (sym (subset* D)) A≡ΠΣ))
  … | _ , zeroᵘₙ , A⇒zeroᵘ =
    case wf-⊢ (subset* A⇒zeroᵘ) of λ where
      (_ , univ ⊢zeroᵘ) →
        ⊥-elim (U≢Level (inversion-zeroᵘ ⊢zeroᵘ))
  … | _ , sucᵘₙ , A⇒sucᵘ =
    case wf-⊢ (subset* A⇒sucᵘ) of λ where
      (_ , univ ⊢sucᵘ) →
        ⊥-elim (U≢Level (proj₂ (inversion-sucᵘ ⊢sucᵘ)))
  … | _ , Uₙ , D =
    ⊥-elim (U≢ΠΣⱼ (trans (sym (subset* D)) A≡ΠΣ))
  … | _ , Liftₙ , D =
    ⊥-elim (Lift≢ΠΣⱼ (trans (sym (subset* D)) A≡ΠΣ))
  … | _ , liftₙ , D =
    case wf-⊢ (subset* D) of λ where
      (fst₁ , univ x) →
        let _ , _ , _ , B≡Lift = inversion-lift x
        in ⊥-elim (U≢Liftⱼ B≡Lift)
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
    case wf-⊢ (subset* A⇒lam) of λ where
      (_ , univ ⊢lam) →
        let _ , _ , _ , _ , _ , U≡Π , _ = inversion-lam ⊢lam in
        ⊥-elim (U≢ΠΣⱼ U≡Π)
  … | _ , zeroₙ , A⇒zero =
    case wf-⊢ (subset* A⇒zero) of λ where
      (_ , univ ⊢zero) →
        ⊥-elim (U≢ℕ (inversion-zero ⊢zero))
  … | _ , sucₙ , A⇒suc =
    case wf-⊢ (subset* A⇒suc) of λ where
      (_ , univ ⊢suc) →
        ⊥-elim (U≢ℕ (proj₂ (inversion-suc ⊢suc)))
  … | _ , starₙ , A⇒star =
    case wf-⊢ (subset* A⇒star) of λ where
      (_ , univ ⊢star) →
        ⊥-elim (U≢Unitⱼ (inversion-star ⊢star .proj₁))
  … | _ , prodₙ , A⇒prod =
    case wf-⊢ (subset* A⇒prod) of λ where
      (_ , univ ⊢prod) →
        let _ , _ , _ , _ , _ , _ , _ , U≡Σ , _ = inversion-prod ⊢prod in
        ⊥-elim (U≢ΠΣⱼ U≡Σ)
  … | _ , rflₙ , A⇒rfl =
    case wf-⊢ (subset* A⇒rfl) of λ where
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
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
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
                → ∃ λ b → Whnf (Γ .defs) b × Γ ⊢ a ⇒* b ∷ A
whNormTerm′ (Levelᵣ x) (term d d′ prop) =
  let w , _ = lsplit prop
  in _ , w , conv* d (sym (subset* x))
whNormTerm′ (Levelᵣ A⇒*Level) (literal ok _ _) =
  ⇒*Level→Allowed-literal→ A⇒*Level ok
whNormTerm′ (Uᵣ′ _ _ _ A⇒*U) ⊩a =
  let Uₜ C B⇒*C C-type C≅C ⊩B = ⊩U∷U⇔⊩U≡∷U .proj₂ ⊩a in
  C , typeWhnf C-type , conv* B⇒*C (sym (subset* A⇒*U))
whNormTerm′ (Liftᵣ′ D _ _) (Liftₜ₌ _ _ (t⇒* , wt) _ _) =
  _ , wt , conv* t⇒* (sym (subset* D))
whNormTerm′ (ℕᵣ x) ⊩a =
  let ℕₜ n d n≡n prop = ⊩ℕ∷ℕ⇔⊩ℕ≡∷ℕ .proj₂ ⊩a
      natN = natural prop
  in  n , naturalWhnf natN , conv* d (sym (subset* x))
whNormTerm′ (Emptyᵣ x) ⊩a =
  let Emptyₜ n d n≡n prop = ⊩Empty∷Empty⇔⊩Empty≡∷Empty .proj₂ ⊩a
      emptyN = empty prop
  in  n , ne! emptyN , conv* d (sym (subset* x))
whNormTerm′ (Unitᵣ′ A⇒*Unit _) ⊩a =
  let Unitₜ t (a⇒*t , t-whnf) _ = ⊩Unit∷Unit⇔⊩Unit≡∷Unit .proj₂ ⊩a in
  t , t-whnf , conv* a⇒*t (sym (subset* A⇒*Unit))
whNormTerm′ (ne (ne H D neH H≡H)) ⊩a =
  let neₜ k d (neNfₜ neH₁ k≡k) = ⊩ne∷⇔⊩ne≡∷ .proj₂ ⊩a in
  k , ne! neH₁ , conv* d (sym (subset* D))
whNormTerm′ (Bᵣ BΠ! ⊩A@(Bᵣ _ _ D _ _ _ _ _)) ⊩a =
  let Πₜ f d funcF _ _ = ⊩Π∷⇔⊩Π≡∷ ⊩A .proj₂ ⊩a in
  f , Functionᵃ→Whnf funcF , conv* d (sym (subset* D))
whNormTerm′ (Bᵣ BΣ! ⊩A@(Bᵣ _ _ D _ _ _ _ _)) ⊩a =
  let Σₜ p d pProd _ _ = ⊩Σ∷⇔⊩Σ≡∷ ⊩A .proj₂ ⊩a in
  p , Productᵃ→Whnf pProd , conv* d (sym (subset* D))
whNormTerm′ (Idᵣ ⊩Id) ⊩a =
  let Idₜ a′ a⇒*a′ a′-id _ = ⊩Id∷⇔⊩Id≡∷ ⊩Id .proj₂ ⊩a in
    a′ , Identityᵃ→Whnf a′-id
  , conv* a⇒*a′ (sym (subset* (_⊩ₗId_.⇒*Id ⊩Id)))

opaque

  -- Well-formed terms reduce to WHNF (given a certain assumption).

  whNormTerm :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    Γ ⊢ t ∷ A → ∃ λ u → Whnf (Γ .defs) u × Γ ⊢ t ⇒* u ∷ A
  whNormTerm ⊢t =
    case reducible-⊩∷ ⊢t of λ
      (_ , ⊩t) →
    case wf-⊩∷ ⊩t of λ
      ⊩A →
    whNormTerm′ ⊩A (⊩∷→⊩∷/ ⊩A ⊩t)

opaque

  -- If equality reflection is allowed, then there is a well-formed
  -- type that does not reduce to WHNF (if at least one Π-type is
  -- allowed).

  type-without-WHNF :
    Equality-reflection →
    Π-allowed p q →
    » ∇ →
    ∃₂ λ (Γ : Con Term 1) A →
      ∇ » Γ ⊢ A × ¬ ∃₂ λ Δ B → Whnf ∇ B × ∇ » Δ ⊢ A ⇒* B
  type-without-WHNF {p} ok₁ ok₂ »∇ =
    let ⊢E = ⊢Empty (ε »∇) in
    ε ∙ Empty , Ω p , univ (⊢Ω∷ ok₁ ok₂ (var₀ ⊢E) (⊢U₀∷ (∙ ⊢E))) ,
    (λ (_ , _ , B-whnf , A⇒*B) →
       Ω-does-not-reduce-to-WHNF-⊢ B-whnf A⇒*B)

opaque

  -- If equality reflection is allowed, then there is a well-typed
  -- term that does not reduce to WHNF (if at least one Π-type is
  -- allowed).

  term-without-WHNF :
    Equality-reflection →
    Π-allowed p q →
    » ∇ →
    ∃₃ λ (Γ : Con Term 1) t A →
      ∇ » Γ ⊢ t ∷ A × ¬ ∃₃ λ Δ u B → Whnf ∇ u × ∇ » Δ ⊢ t ⇒* u ∷ B
  term-without-WHNF {p} ok₁ ok₂ »∇ =
    let ⊢E = ⊢Empty (ε »∇) in
    ε ∙ Empty , Ω p , Empty , ⊢Ω∷ ok₁ ok₂ (var₀ ⊢E) (Emptyⱼ (∙ ⊢E)) ,
    (λ (_ , _ , _ , u-whnf , t⇒*u) →
       Ω-does-not-reduce-to-WHNF-⊢∷ u-whnf t⇒*u)
