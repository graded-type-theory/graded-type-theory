------------------------------------------------------------------------
-- Translations (liftings) between different algorithmic equality
-- relations.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Conversion.Lift
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  -- Equality reflection is not allowed.
  ⦃ no-equality-reflection : No-equality-reflection ⦄
  where

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Neutral.Atomic M type-variant
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.EqualityRelation.Instance R
open import Definition.Typed.Inversion R
open import Definition.Typed.Stability R
open import Definition.Typed.Syntactic R
open import Definition.Typed.Weakening R
open import Definition.Typed.Properties R
open import Definition.Typed.EqRelInstance R using (eqRelInstance)
open import Definition.Conversion R
open import Definition.Conversion.Whnf R
open import Definition.Conversion.Soundness R
open import Definition.Conversion.Symmetry R
open import Definition.Conversion.Transitivity R
open import Definition.Conversion.Weakening R
open import Definition.LogicalRelation R ⦃ eqRelInstance ⦄
open import Definition.LogicalRelation.Properties R ⦃ eqRelInstance ⦄
open import Definition.LogicalRelation.Fundamental.Reducibility R ⦃ eqRelInstance ⦄
open import Definition.LogicalRelation.Weakening.Restricted R ⦃ eqRelInstance ⦄
open import Definition.Typed.Consequences.Reduction R

open import Tools.Fin
open import Tools.Function
open import Tools.List hiding (_∷_)
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Sum using (inj₁; inj₂)

private
  variable
    n : Nat
    Γ : Con Term n

-- Some lemmas used below.

wf~↓Level : ∀ {t u} → Γ ⊢ t ~ u ↓ Level → Γ ⊢ t ~ t ↓ Level × Γ ⊢ u ~ u ↓ Level
wf~↓Level t~u =
    trans~↓ t~u (sym~↓Level t~u) .proj₁
  , trans~↓ (sym~↓Level t~u) t~u .proj₁

~↓→~∷ : ∀ {t u A} → Γ ⊢ t ~ u ↓ A → Γ ⊢ t ~ u ∷ A
~↓→~∷ ([~] A (D , _) k~l) = ↑ (sym (subset* D)) k~l

-- Lifting of algorithmic equality of types from WHNF to generic types.
liftConv : ∀ {A B}
          → Γ ⊢ A [conv↓] B
          → Γ ⊢ A [conv↑] B
liftConv A<>B =
  let ⊢A , ⊢B = syntacticEq (soundnessConv↓ A<>B)
      whnfA , whnfB = whnfConv↓ A<>B
  in  [↑] _ _ (id ⊢A , whnfA) (id ⊢B , whnfB) A<>B

-- Lifting of algorithmic equality of terms from WHNF to generic terms.
liftConvTerm : ∀ {t u A}
             → Γ ⊢ t [conv↓] u ∷ A
             → Γ ⊢ t [conv↑] u ∷ A
liftConvTerm t<>u =
  let ⊢A , ⊢t , ⊢u = syntacticEqTerm (soundnessConv↓Term t<>u)
      whnfA , whnfT , whnfU = whnfConv↓Term t<>u
  in  [↑]ₜ _ _ _ (id ⊢A , whnfA) (id ⊢t , whnfT) (id ⊢u , whnfU) t<>u

mutual
  -- Helper function for lifting from neutrals to generic terms in WHNF.
  lift~toConv↓′ : ∀ {t u A A′ l}
                → Γ ⊩⟨ l ⟩ A′
                → Γ ⊢ A′ ⇒* A
                → Γ ⊢ t ~ u ↓ A
                → Γ ⊢ t [conv↓] u ∷ A
  lift~toConv↓′ (Levelᵣ D) D₁ ([~] A (D₂ , whnfB) t~u)
                rewrite PE.sym (whrDet* (D , Levelₙ) (D₁ , whnfB)) =
    let nt , nu = ne~↑ t~u
        t≡u = conv (soundness~↑ t~u) (subset* D₂)
        ⊢Level , ⊢t , ⊢u = syntacticEqTerm t≡u
        ⊩t≡u = neNfₜ₌ no-equality-reflection nt nu t≡u
        t↓u = [~] A (D₂ , Levelₙ) t~u
        [t] , [u] = wf~↓Level t↓u
    in Level-ins ([↓]ˡ
      (neᵛ [t]) (neᵛ [u])
      (neₙ (neₙ [t] PE.refl)) (neₙ (neₙ [u] PE.refl))
      (Any.here (≤-refl , ne≤ (ne≡ t↓u)) All.∷ All.[] , Any.here (≤-refl , ne≤ (ne≡' t↓u)) All.∷ All.[]))
  lift~toConv↓′ (Uᵣ′ _ _ _ A′⇒*U) A′⇒*A ([~] _ (B⇒*A , A-whnf) t~u)
    rewrite PE.sym (whrDet* (A′⇒*U , Uₙ) (A′⇒*A , A-whnf)) =
    let _ , ⊢t , ⊢u =
          syntacticEqTerm (conv (soundness~↑ t~u) (subset* B⇒*A))
    in
    univ ⊢t ⊢u (ne ([~] _ (B⇒*A , Uₙ) t~u))
  lift~toConv↓′ (Liftᵣ′ D [k] [F]) A′⇒*A ([~] _ (B⇒*A , A-whnf) t~u) =
    case whrDet* (D , Liftₙ) (A′⇒*A , A-whnf) of λ {
      PE.refl →
    let t~u↓ = [~] _ (B⇒*A , Liftₙ) t~u
        nt , nu = ne~↑ t~u
        _ , ⊢t , ⊢u = syntacticEqTerm (soundness~↓ t~u↓)
    in Lift-η ⊢t ⊢u (ne! nt) (ne! nu) (lift~toConv↑′ [F] (lower-cong t~u↓)) }
  lift~toConv↓′ (ℕᵣ D) D₁ ([~] A (D₂ , whnfB) k~l)
                rewrite PE.sym (whrDet* (D , ℕₙ) (D₁ , whnfB)) =
    ℕ-ins ([~] A (D₂ , ℕₙ) k~l)
  lift~toConv↓′ (Emptyᵣ D) D₁ ([~] A (D₂ , whnfB) k~l)
                rewrite PE.sym (whrDet* (D , Emptyₙ) (D₁ , whnfB)) =
    Empty-ins ([~] A (D₂ , Emptyₙ) k~l)
  lift~toConv↓′
    (Unitᵣ {s} (Unitᵣ A′⇒*Unit ok)) A′⇒*A
    t~u↓@([~] _ (B⇒*A , A-whnf) t~u↑) =
    case whrDet* (A′⇒*Unit , Unitₙ) (A′⇒*A , A-whnf) of λ {
      PE.refl →
    case Unit-with-η? s of λ where
      (inj₂ (PE.refl , no-η)) → Unitʷ-ins no-η t~u↓
      (inj₁ η)                →
        case ne~↑ t~u↑ of λ
          (t-ne , u-ne) →
        case syntacticEqTerm (soundness~↑ t~u↑) of λ
          (_ , ⊢t , ⊢u) →
        case subset* B⇒*A of λ
          B≡Unit →
        η-unit (conv ⊢t B≡Unit) (conv ⊢u B≡Unit) (ne! t-ne) (ne! u-ne) ok η }
  lift~toConv↓′ (ne′ _ H D neH H≡H) D₁ ([~] A (D₂ , whnfB) k~l)
                rewrite PE.sym (whrDet* (D , ne neH) (D₁ , whnfB)) =
    let _ , ⊢t , ⊢u = syntacticEqTerm (soundness~↑ k~l)
        A≡H = subset* D₂
    in
    ne-ins (conv ⊢t A≡H) (conv ⊢u A≡H) neH ([~] A (D₂ , ne neH) k~l)
  lift~toConv↓′
    (Πᵣ′ F G D A≡A [F] [G] G-ext _) D₁ ([~] A (D₂ , whnfB) k~l)
    rewrite PE.sym (whrDet* (D , ΠΣₙ) (D₁ , whnfB)) =
    let ⊢ΠFG , ⊢t , ⊢u = syntacticEqTerm
                           (soundness~↓ ([~] A (D₂ , ΠΣₙ) k~l))
        ⊢F , ⊢G , _ = inversion-ΠΣ ⊢ΠFG
        neT , neU = ne~↑ k~l
        step-id = stepʷ id ⊢F
        step-idʳ = ∷ʷ⊇→∷ʷʳ⊇ step-id
        var0 = neuTerm no-equality-reflection ([F] step-idʳ) varᵃ
                 (refl (var₀ ⊢F))
        0≡0 = lift~toConv↑′ ([F] step-idʳ) (var-refl (var₀ ⊢F) PE.refl)
    in  η-eq ⊢t ⊢u (ne (ne⁻ neT)) (ne (ne⁻ neU))
          (PE.subst (λ x → _ ⊢ _ [conv↑] _ ∷ x) (wkSingleSubstId _) $
           lift~toConv↑′ ([G] step-idʳ var0) $
           app-cong (wk~↓ step-id ([~] A (D₂ , ΠΣₙ) k~l)) 0≡0)
  lift~toConv↓′
    (Bᵣ′ BΣˢ F G D Σ≡Σ [F] [G] G-ext _) D₁
    ([~] A″ (D₂ , whnfA) t~u)
    rewrite
      -- Σ F ▹ G ≡ A.
      PE.sym (whrDet* (D , ΠΣₙ) (D₁ , whnfA)) =
    let neT , neU = ne~↑ t~u
        t~u↓ = [~] A″ (D₂ , ΠΣₙ) t~u
        ⊢ΣFG , ⊢t , ⊢u = syntacticEqTerm (soundness~↓ t~u↓)
        ⊢F , ⊢G , _ = inversion-ΠΣ ⊢ΣFG
        ⊢Γ = wf ⊢F

        wkId = wk-id F
        wkLiftId = PE.cong (λ x → x [ fst _ _ ]₀) (wk-lift-id G)

        wk[F] = [F] (id ⊢Γ)
        wkfst≡ = PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym wkId)
                   (fst-cong ⊢G (refl ⊢t))
        wk[fst] = neuTerm no-equality-reflection wk[F] (fstₙᵃ neT)
                    wkfst≡
        wk[Gfst] = [G] (id ⊢Γ) wk[fst]

        wkfst~ = PE.subst (λ x → _ ⊢ _ ~ _ ↑ x) (PE.sym wkId) (fst-cong t~u↓)
        wksnd~ = PE.subst (λ x → _ ⊢ _ ~ _ ↑ x) (PE.sym wkLiftId) (snd-cong t~u↓)
    in  Σ-η ⊢t ⊢u (ne (ne⁻ neT)) (ne (ne⁻ neU))
            (PE.subst (λ x → _ ⊢ _ [conv↑] _ ∷ x) wkId
                      (lift~toConv↑′ wk[F] wkfst~))
            (PE.subst (λ x → _ ⊢ _ [conv↑] _ ∷ x) wkLiftId
                      (lift~toConv↑′ wk[Gfst] wksnd~))
  lift~toConv↓′
    (Bᵣ′ BΣʷ F G D Σ≡Σ [F] [G] G-ext _) D₁
    ([~] A″ (D₂ , whnfA) t~u)
    rewrite
      -- Σ F ▹ G ≡ A.
      PE.sym (whrDet* (D , ΠΣₙ) (D₁ , whnfA)) =
    let t~u↓ = [~] A″ (D₂ , ΠΣₙ) t~u
        _ , ⊢t , ⊢u = syntacticEqTerm (soundness~↓ t~u↓)
    in  Σʷ-ins ⊢t ⊢u t~u↓
  lift~toConv↓′ (Idᵣ ⊩A′) A′⇒*A t~u@([~] _ (_ , A-whnf) _) =
    case whrDet* (_⊩ₗId_.⇒*Id ⊩A′ , Idₙ) (A′⇒*A , A-whnf) of λ {
      PE.refl →
    case syntacticEqTerm (soundness~↓ t~u) .proj₂ .proj₁ of λ {
      ⊢t →
    Id-ins ⊢t t~u }}

  -- Helper function for lifting from neutrals to generic terms.
  lift~toConv↑′ : ∀ {t u A l}
                → Γ ⊩⟨ l ⟩ A
                → Γ ⊢ t ~ u ↑ A
                → Γ ⊢ t [conv↑] u ∷ A
  lift~toConv↑′ [A] t~u =
    let B , whnfB , D = whNorm′ [A]
        t~u↓ = [~] _ (D , whnfB) t~u
        neT , neU = ne~↑ t~u
        _ , ⊢t , ⊢u = syntacticEqTerm (soundness~↓ t~u↓)
    in  [↑]ₜ _ _ _ (D , whnfB) (id ⊢t , ne! neT) (id ⊢u , ne! neU)
          (lift~toConv↓′ [A] D t~u↓)

-- Lifting of algorithmic equality of terms from neutrals to generic terms in WHNF.
lift~toConv↓ : ∀ {t u A}
             → Γ ⊢ t ~ u ↓ A
             → Γ ⊢ t [conv↓] u ∷ A
lift~toConv↓ ([~] A₁ D@(D′ , _) k~l) =
  lift~toConv↓′
    (reducible-⊩ (syntacticRed D′ .proj₁) .proj₂) D′
    ([~] A₁ D k~l)

-- Lifting of algorithmic equality of terms from neutrals to generic terms.
lift~toConv↑ : ∀ {t u A}
             → Γ ⊢ t ~ u ↑ A
             → Γ ⊢ t [conv↑] u ∷ A
lift~toConv↑ t~u =
  lift~toConv↑′
    (reducible-⊩ (syntacticEqTerm (soundness~↑ t~u) .proj₁) .proj₂)
    t~u

lift-↓ᵛ : ∀ {t v} → Γ ⊢ t ↓ᵛ v → Γ ⊢ t ↑ᵛ v
lift-↓ᵛ x = [↑]ᵛ (id (wf↓ᵛ x) , whnfConv↓ᵛ x) x
