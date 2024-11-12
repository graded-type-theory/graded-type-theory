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
  where

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.Syntactic R
open import Definition.Typed.Weakening R
open import Definition.Typed.Properties R
open import Definition.Typed.EqRelInstance R
open import Definition.Conversion R
open import Definition.Conversion.Whnf R
open import Definition.Conversion.Soundness R
open import Definition.Conversion.Weakening R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Fundamental.Reducibility R
open import Definition.Typed.Consequences.Reduction R

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Sum using (inj₁; inj₂)

private
  variable
    n : Nat
    Γ : Con Term n

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
  lift~toConv↓′ (Uᵣ′ _ _ A′⇒*U) A′⇒*A ([~] _ (B⇒*A , A-whnf) t~u)
    rewrite PE.sym (whrDet* (red A′⇒*U , Uₙ) (A′⇒*A , A-whnf)) =
    let _ , ⊢t , ⊢u =
          syntacticEqTerm (conv (soundness~↑ t~u) (subset* B⇒*A))
    in
    univ ⊢t ⊢u (ne ([~] _ (B⇒*A , Uₙ) t~u))
  lift~toConv↓′ (ℕᵣ D) D₁ ([~] A (D₂ , whnfB) k~l)
                rewrite PE.sym (whrDet* (red D , ℕₙ) (D₁ , whnfB)) =
    ℕ-ins ([~] A (D₂ , ℕₙ) k~l)
  lift~toConv↓′ (Emptyᵣ D) D₁ ([~] A (D₂ , whnfB) k~l)
                rewrite PE.sym (whrDet* (red D , Emptyₙ) (D₁ , whnfB)) =
    Empty-ins ([~] A (D₂ , Emptyₙ) k~l)
  lift~toConv↓′
    (Unitᵣ {s} (Unitₜ A′⇒*Unit _)) A′⇒*A
    t~u↓@([~] _ (B⇒*A , A-whnf) t~u↑) =
    case whrDet* (red A′⇒*Unit , Unitₙ) (A′⇒*A , A-whnf) of λ {
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
        η-unit (conv ⊢t B≡Unit) (conv ⊢u B≡Unit) (ne t-ne) (ne u-ne) η }
  lift~toConv↓′ (ne′ H D neH H≡H) D₁ ([~] A (D₂ , whnfB) k~l)
                rewrite PE.sym (whrDet* (red D , ne neH) (D₁ , whnfB)) =
    let _ , ⊢t , ⊢u = syntacticEqTerm (soundness~↑ k~l)
        A≡H = subset* D₂
    in  ne-ins (conv ⊢t A≡H) (conv ⊢u A≡H) neH ([~] A (D₂ , ne neH) k~l)
  lift~toConv↓′
    (Πᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext _) D₁ ([~] A (D₂ , whnfB) k~l)
    rewrite PE.sym (whrDet* (red D , ΠΣₙ) (D₁ , whnfB)) =
    let ⊢ΠFG , ⊢t , ⊢u = syntacticEqTerm
                           (soundness~↓ ([~] A (D₂ , ΠΣₙ) k~l))
        ⊢F , ⊢G = syntacticΠ ⊢ΠFG
        neT , neU = ne~↑ k~l
        step-id = stepʷ id ⊢F
        var0 = neuTerm ([F] step-id) (var x0) (var₀ ⊢F) (refl (var₀ ⊢F))
        0≡0 = lift~toConv↑′ ([F] step-id) (var-refl (var₀ ⊢F) PE.refl)
    in  η-eq ⊢t ⊢u (ne neT) (ne neU)
          (PE.subst (λ x → _ ⊢ _ [conv↑] _ ∷ x) (wkSingleSubstId _) $
           lift~toConv↑′ ([G] step-id var0) $
           app-cong (wk~↓ step-id ([~] A (D₂ , ΠΣₙ) k~l)) 0≡0)
  lift~toConv↓′
    (Bᵣ′ BΣˢ F G D ⊢F ⊢G Σ≡Σ [F] [G] G-ext _) D₁
    ([~] A″ (D₂ , whnfA) t~u)
    rewrite
      -- Σ F ▹ G ≡ A.
      PE.sym (whrDet* (red D , ΠΣₙ) (D₁ , whnfA)) =
    let neT , neU = ne~↑ t~u
        t~u↓ = [~] A″ (D₂ , ΠΣₙ) t~u
        ⊢ΣFG , ⊢t , ⊢u = syntacticEqTerm (soundness~↓ t~u↓)
        ⊢F , ⊢G = syntacticΣ ⊢ΣFG
        ⊢Γ = wf ⊢F

        wkId = wk-id F
        wkLiftId = PE.cong (λ x → x [ fst _ _ ]₀) (wk-lift-id G)

        wk[F] = [F] (idʷ ⊢Γ)
        wk⊢fst = PE.subst (_⊢_∷_ _ _) (PE.sym wkId) (fstⱼ ⊢G ⊢t)
        wkfst≡ = PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym wkId)
                   (fst-cong ⊢G (refl ⊢t))
        wk[fst] = neuTerm wk[F] (fstₙ neT) wk⊢fst wkfst≡
        wk[Gfst] = [G] (idʷ ⊢Γ) wk[fst]

        wkfst~ = PE.subst (λ x → _ ⊢ _ ~ _ ↑ x) (PE.sym wkId) (fst-cong t~u↓)
        wksnd~ = PE.subst (λ x → _ ⊢ _ ~ _ ↑ x) (PE.sym wkLiftId) (snd-cong t~u↓)
    in  Σ-η ⊢t ⊢u (ne neT) (ne neU)
            (PE.subst (λ x → _ ⊢ _ [conv↑] _ ∷ x) wkId
                      (lift~toConv↑′ wk[F] wkfst~))
            (PE.subst (λ x → _ ⊢ _ [conv↑] _ ∷ x) wkLiftId
                      (lift~toConv↑′ wk[Gfst] wksnd~))
  lift~toConv↓′
    (Bᵣ′ BΣʷ F G D ⊢F ⊢G Σ≡Σ [F] [G] G-ext _) D₁
    ([~] A″ (D₂ , whnfA) t~u)
    rewrite
      -- Σ F ▹ G ≡ A.
      PE.sym (whrDet* (red D , ΠΣₙ) (D₁ , whnfA)) =
    let t~u↓ = [~] A″ (D₂ , ΠΣₙ) t~u
        _ , ⊢t , ⊢u = syntacticEqTerm (soundness~↓ t~u↓)
    in  Σʷ-ins ⊢t ⊢u t~u↓
  lift~toConv↓′ (Idᵣ ⊩A′) A′⇒*A t~u@([~] _ (_ , A-whnf) _) =
    case whrDet* (red (_⊩ₗId_.⇒*Id ⊩A′) , Idₙ) (A′⇒*A , A-whnf) of λ {
      PE.refl →
    case syntacticEqTerm (soundness~↓ t~u) .proj₂ .proj₁ of λ {
      ⊢t →
    Id-ins ⊢t t~u }}
  lift~toConv↓′ (emb ≤ᵘ-refl     ⊩A) = lift~toConv↓′ ⊩A
  lift~toConv↓′ (emb (≤ᵘ-step p) ⊩A) = lift~toConv↓′ (emb p ⊩A)

  -- Helper function for lifting from neutrals to generic terms.
  lift~toConv↑′ : ∀ {t u A l}
                → Γ ⊩⟨ l ⟩ A
                → Γ ⊢ t ~ u ↑ A
                → Γ ⊢ t [conv↑] u ∷ A
  lift~toConv↑′ [A] t~u =
    let B , whnfB , D = whNorm′ [A]
        t~u↓ = [~] _ (red D , whnfB) t~u
        neT , neU = ne~↑ t~u
        _ , ⊢t , ⊢u = syntacticEqTerm (soundness~↓ t~u↓)
    in  [↑]ₜ _ _ _ (red D , whnfB) (id ⊢t , ne neT) (id ⊢u , ne neU)
          (lift~toConv↓′ [A] (red D) t~u↓)

-- Lifting of algorithmic equality of terms from neutrals to generic terms in WHNF.
lift~toConv↓ : ∀ {t u A}
             → Γ ⊢ t ~ u ↓ A
             → Γ ⊢ t [conv↓] u ∷ A
lift~toConv↓ ([~] A₁ D@(D′ , _) k~l) =
  lift~toConv↓′ (reducible-⊩ (proj₁ (syntacticRed D′)) .proj₂) D′
    ([~] A₁ D k~l)

-- Lifting of algorithmic equality of terms from neutrals to generic terms.
lift~toConv↑ : ∀ {t u A}
             → Γ ⊢ t ~ u ↑ A
             → Γ ⊢ t [conv↑] u ∷ A
lift~toConv↑ t~u =
  lift~toConv↑′
    (reducible-⊩ (proj₁ (syntacticEqTerm (soundness~↑ t~u))) .proj₂) t~u
