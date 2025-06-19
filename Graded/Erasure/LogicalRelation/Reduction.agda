------------------------------------------------------------------------
-- The logical relation is clsoed under reduction (in both directions).
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Erasure.LogicalRelation.Assumptions
open import Graded.Modality

module Graded.Erasure.LogicalRelation.Reduction
  {a} {M : Set a}
  {𝕄 : Modality M}
  {R : Type-restrictions 𝕄}
  (as : Assumptions R)
  where

open Assumptions as
open Modality 𝕄
open Type-restrictions R

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Properties.Escape R

import Definition.LogicalRelation.Fundamental R as F
import Definition.LogicalRelation.Irrelevance R as I
import Definition.LogicalRelation.Properties.Reduction R as R
open import Definition.LogicalRelation.Weakening.Restricted R

open import Definition.Untyped M as U
open import Definition.Untyped.Neutral M type-variant
open import Definition.Typed R
open import Definition.Typed.Properties R

open import Definition.Untyped.Properties M as UP using (wk-id ; wk-lift-id)

open import Graded.Erasure.Extraction.Properties 𝕄
open import Graded.Erasure.LogicalRelation as
open import Graded.Erasure.Target as T hiding (_⇒_; _⇒*_)
open import Graded.Erasure.Target.Properties as TP
open import Graded.Erasure.Target.Reasoning

open import Tools.Function
open import Tools.Nat
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum using (inj₁; inj₂)

private
  variable
    n : Nat
    t t′ A : U.Term n
    v v′ : T.Term n
    Γ : U.Con U.Term n

-- The logical relation for erasure is preserved by backward
-- "reduction" for the source term.

sourceRedSubstTerm : ∀ {l} ([A] : Δ ⊩⟨ l ⟩ A) → t′ ®⟨ l ⟩ v ∷ A / [A]
                   → t ⇛ t′ ∷ A → t ®⟨ l ⟩ v ∷ A / [A]
sourceRedSubstTerm (Levelᵣ _) (U/Levelᵣ ⇒*↯) _ =
  U/Levelᵣ ⇒*↯
sourceRedSubstTerm (Uᵣ _) (U/Levelᵣ ⇒*↯) _ =
  U/Levelᵣ ⇒*↯
sourceRedSubstTerm (ℕᵣ D) (zeroᵣ t′⇒zero v⇒v′) t⇒t′ =
  zeroᵣ (trans-⇛ (conv-⇛ t⇒t′ (subset* D)) t′⇒zero) v⇒v′
sourceRedSubstTerm (ℕᵣ ⇒*ℕ) (sucᵣ t′⇒suc v⇒v′ num t®v) t⇒t′ =
  sucᵣ (trans-⇛ (conv-⇛ t⇒t′ (subset* ⇒*ℕ)) t′⇒suc) v⇒v′ num t®v
sourceRedSubstTerm
  (Unitᵣ′ _ _ _ D ok) (starᵣ t′⇒star u≡u′ v⇒star) t⇒t′ =
  starᵣ
    (trans-⇛ (conv-⇛ t⇒t′ (trans (subset* D) (Unit-cong u≡u′ ok)))
       t′⇒star)
    u≡u′ v⇒star
sourceRedSubstTerm (Bᵣ′ (BΠ p q) F G D A≡A [F] [G] G-ext _) t®v′ t⇒t′
  with is-𝟘? p
... | yes PE.refl = t®v′ .proj₁ , λ {a = a} [a] →
  let t®v = t®v′ .proj₂ [a]
      ⊢a = escapeTerm ([F] (id ⊢Δ)) [a]
      ⊢a′ = PE.subst (Δ ⊢ a ∷_) (UP.wk-id F) ⊢a
      t∘a⇒t′∘w′ = app-⇛ (conv-⇛ t⇒t′ (subset* D)) ⊢a′
      t∘a⇒t′∘w = PE.subst (_⇛_∷_ _ _)
                   (PE.cong (U._[ a ]₀) (PE.sym (UP.wk-lift-id G)))
                   t∘a⇒t′∘w′
  in  sourceRedSubstTerm ([G] (id ⊢Δ) [a]) t®v t∘a⇒t′∘w
... | no p≢𝟘 = t®v′ .proj₁ , λ {a = a} [a] a®w →
  let t®v = t®v′ .proj₂ [a] a®w
      ⊢a = escapeTerm ([F] (id ⊢Δ)) [a]
      ⊢a′ = PE.subst (Δ ⊢ a ∷_) (UP.wk-id F) ⊢a
      t∘a⇒t′∘w′ = app-⇛ (conv-⇛ t⇒t′ (subset* D)) ⊢a′
      t∘a⇒t′∘w = PE.subst (_⇛_∷_ _ _)
                   (PE.cong (U._[ a ]₀) (PE.sym (UP.wk-lift-id G)))
                   t∘a⇒t′∘w′
  in  sourceRedSubstTerm ([G] (id ⊢Δ) [a]) t®v t∘a⇒t′∘w
sourceRedSubstTerm
  (Bᵣ′ BΣ! F G D A≡A [F] [G] G-ext _)
  (t₁ , t₂ , t′⇒p , [t₁] , v₂ , t₂®v₂ , extra) t⇒t′ =
  t₁ , t₂ , trans-⇛ (conv-⇛ t⇒t′ (subset* D)) t′⇒p , [t₁] , v₂ , t₂®v₂ ,
  extra
sourceRedSubstTerm (Idᵣ ⊩A) (rflᵣ t′⇒*rfl ⇒*↯) t⇒t′ =
  rflᵣ (trans-⇛ (conv-⇛ t⇒t′ (subset* (_⊩ₗId_.⇒*Id ⊩A))) t′⇒*rfl) ⇒*↯
sourceRedSubstTerm (ne record{}) ()
sourceRedSubstTerm (Emptyᵣ _)    ()

-- Logical relation for erasure is preserved under a single reduction backwards on the target language term
-- If t ® v′ ∷ A and v ⇒ v′ then t ® v ∷ A
--
-- Proof by induction on t ® v′ ∷ A

targetRedSubstTerm : ∀ {l} ([A] : Δ ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v′ ∷ A / [A]
                   → v T.⇒ v′ → t ®⟨ l ⟩ v ∷ A / [A]
targetRedSubstTerm (Levelᵣ _) (U/Levelᵣ ⇒*↯) v⇒v′ =
  U/Levelᵣ (T.trans v⇒v′ ∘→ ⇒*↯)
targetRedSubstTerm (Uᵣ _) (U/Levelᵣ ⇒*↯) v⇒v′ =
  U/Levelᵣ (T.trans v⇒v′ ∘→ ⇒*↯)
targetRedSubstTerm (ℕᵣ x) (zeroᵣ t′⇒zero v′⇒zero) v⇒v′ = zeroᵣ t′⇒zero (trans v⇒v′ v′⇒zero)
targetRedSubstTerm (ℕᵣ _) (sucᵣ t′⇒suc v′⇒suc num t®v) v⇒v′ =
  sucᵣ t′⇒suc (trans v⇒v′ v′⇒suc) num t®v
targetRedSubstTerm (Unitᵣ x) (starᵣ x₁ u≡u′ v′⇒star) v⇒v′ =
  starᵣ x₁ u≡u′ (trans v⇒v′ v′⇒star)
targetRedSubstTerm
  (Bᵣ′ (BΠ p q) F G D A≡A [F] [G] G-ext _) (v′⇒*lam , t®v′) v⇒v′
  with is-𝟘? p | Σ.map idᶠ (T.trans v⇒v′) ∘→ v′⇒*lam
... | yes PE.refl | v⇒*lam = v⇒*lam , λ {a = a} [a] →
  let t®v = t®v′ [a]
      [G[a]] = [G] (id ⊢Δ) [a]
  in  targetRedSubstTerm [G[a]] t®v (app-𝟘′-subst v⇒v′)
... | no p≢𝟘 | v⇒*lam = v⇒*lam , λ {a = a} [a] a®w →
  let t®v = t®v′ [a] a®w
      v∘w⇒v′∘w′ = T.app-subst v⇒v′
      [G[a]] = [G] (id ⊢Δ) [a]
  in  targetRedSubstTerm [G[a]] t®v v∘w⇒v′∘w′
targetRedSubstTerm {A = A} {t = t} {v = v}
  [Σ]@(Bᵣ′ (BΣ _ p _) F G D A≡A [F] [G] G-ext _)
  (t₁ , t₂ , t⇒t′ , [t₁] , v₂ , t₂®v₂ , extra) v⇒v′ =
    t₁ , t₂ , t⇒t′ , [t₁] , v₂ , t₂®v₂ , extra′
  where
  extra′ = Σ-®-elim (λ _ → Σ-® _ F ([F] (id ⊢Δ)) t₁ v v₂ p) extra
                    (λ v′⇒v₂         → Σ-®-intro-𝟘 (trans v⇒v′ v′⇒v₂))
                    (λ v₁ v′⇒p t₁®v₁ → Σ-®-intro-ω v₁ (trans v⇒v′ v′⇒p) t₁®v₁)
targetRedSubstTerm (Idᵣ _) (rflᵣ t⇒*rfl ⇒*↯) v⇒v′ =
  rflᵣ t⇒*rfl (T.trans v⇒v′ ∘→ ⇒*↯)
targetRedSubstTerm (ne record{}) ()
targetRedSubstTerm (Emptyᵣ _)    ()


-- Logical relation for erasure is preserved under reduction closure backwards
-- on the target language term.
-- If t ® v′ ∷ A and v ⇒* v′ then t ® v ∷ A
--
-- Proof by induction on t ® v′ ∷ A

targetRedSubstTerm* : ∀ {l} ([A] : Δ ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v′ ∷ A / [A]
                    → v T.⇒* v′ → t ®⟨ l ⟩ v ∷ A / [A]
targetRedSubstTerm* [A] t®v′ refl = t®v′
targetRedSubstTerm* [A] t®v′ (trans x v⇒v′) =
  targetRedSubstTerm [A] (targetRedSubstTerm* [A] t®v′ v⇒v′) x


-- The logical relation for erasure is preserved by backward
-- "reduction" for the source term and backward reduction for the
-- target term.

redSubstTerm : ∀ {l} ([A] : Δ ⊩⟨ l ⟩ A) → t′ ®⟨ l ⟩ v′ ∷ A / [A]
             → t ⇛ t′ ∷ A → v T.⇒ v′ → t ®⟨ l ⟩ v ∷ A / [A]
redSubstTerm [A] t′®v′ t⇒t′ v⇒v′ =
  targetRedSubstTerm [A] (sourceRedSubstTerm [A] t′®v′ t⇒t′) v⇒v′


-- The logical relation for erasure is preserved by backward
-- "reduction" for the source term and backward reduction for the
-- target term.

redSubstTerm* : ∀ {l} ([A] : Δ ⊩⟨ l ⟩ A) → t′ ®⟨ l ⟩ v′ ∷ A / [A]
              → t ⇛ t′ ∷ A → v T.⇒* v′ → t ®⟨ l ⟩ v ∷ A / [A]
redSubstTerm* [A] t′®v′ t⇒t′ v⇒v′ =
  targetRedSubstTerm* [A] (sourceRedSubstTerm [A] t′®v′ t⇒t′) v⇒v′


-- The logical relation for erasure is preserved by "reduction" for
-- the source term.

sourceRedSubstTerm′ : ∀ {l} ([A] : Δ ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v ∷ A / [A]
                    → t ⇛ t′ ∷ A → t′ ®⟨ l ⟩ v ∷ A / [A]
sourceRedSubstTerm′ (Levelᵣ _) (U/Levelᵣ ⇒*↯) _ =
  U/Levelᵣ ⇒*↯
sourceRedSubstTerm′ (Uᵣ _) (U/Levelᵣ ⇒*↯) _ =
  U/Levelᵣ ⇒*↯
sourceRedSubstTerm′ (ℕᵣ D) (zeroᵣ t⇒zero v⇒zero) t⇒t′
  with whnf-⇛ t⇒zero zeroₙ (conv-⇛ t⇒t′ (subset* D))
... | t′⇒zero = zeroᵣ t′⇒zero v⇒zero
sourceRedSubstTerm′ (ℕᵣ D) (sucᵣ t⇒suc v⇒suc num t®v) t⇒t′
  with whnf-⇛ t⇒suc sucₙ (conv-⇛ t⇒t′ (subset* D))
... | t′⇒suc = sucᵣ t′⇒suc v⇒suc num t®v
sourceRedSubstTerm′
  (Unitᵣ′ _ _ _ ⇒*Unit ok) (starᵣ t⇒star u≡u′ v⇒star) t⇒t′
  with whnf-⇛ t⇒star starₙ
         (conv-⇛ t⇒t′ (trans (subset* ⇒*Unit) (Unit-cong u≡u′ ok)))
... | t′⇒star = starᵣ t′⇒star u≡u′ v⇒star
sourceRedSubstTerm′
  (Bᵣ′ (BΠ p q) F G D A≡A [F] [G] G-ext _) t®v′ t⇒t′
  with is-𝟘? p
... | yes PE.refl = t®v′ .proj₁ , λ {a = a} [a] →
  let t®v = t®v′ .proj₂ [a]
      ⊢a = escapeTerm ([F] (id ⊢Δ)) [a]
      ⊢a′ = PE.subst (Δ ⊢ a ∷_) (UP.wk-id F) ⊢a
      t∘a⇒t′∘a′ = app-⇛ (conv-⇛ t⇒t′ (subset* D)) ⊢a′
      t∘a⇒t′∘a = PE.subst (_⇛_∷_ _ _)
                          (PE.cong (U._[ a ]₀) (PE.sym (UP.wk-lift-id G)))
                          t∘a⇒t′∘a′
  in  sourceRedSubstTerm′ ([G] (id ⊢Δ) [a]) t®v t∘a⇒t′∘a
... | no p≢𝟘 = t®v′ .proj₁ , λ {a = a} [a] a®w →
  let t®v = t®v′ .proj₂ [a] a®w
      ⊢a = escapeTerm ([F] (id ⊢Δ)) [a]
      ⊢a′ = PE.subst (Δ ⊢ a ∷_) (UP.wk-id F) ⊢a
      t∘a⇒t′∘a′ = app-⇛ (conv-⇛ t⇒t′ (subset* D)) ⊢a′
      t∘a⇒t′∘a = PE.subst (_⇛_∷_ _ _)
                          (PE.cong (U._[ a ]₀) (PE.sym (UP.wk-lift-id G)))
                          t∘a⇒t′∘a′
  in  sourceRedSubstTerm′ ([G] (id ⊢Δ) [a]) t®v t∘a⇒t′∘a
sourceRedSubstTerm′
  (Bᵣ′ BΣ! F G D A≡A [F] [G] G-ext _)
  (t₁ , t₂ , t⇒p , [t₁] , v₂ , t₂®v₂ , extra) t⇒t′ =
  t₁ , t₂
     , whnf-⇛ t⇒p prodₙ (conv-⇛ t⇒t′ (subset* D))
     , [t₁] , v₂ , t₂®v₂ , extra
sourceRedSubstTerm′ (Idᵣ ⊩A) (rflᵣ t⇒*rfl ⇒*↯) t⇒t′ =
  rflᵣ (whnf-⇛ t⇒*rfl rflₙ (conv-⇛ t⇒t′ (subset* (_⊩ₗId_.⇒*Id ⊩A)))) ⇒*↯
sourceRedSubstTerm′ (ne record{}) ()
sourceRedSubstTerm′ (Emptyᵣ _)    ()


private opaque

  -- Some lemmas used below.

  Π-lemma :
    v T.⇒ v′ →
    (∃ λ v″ → v T.⇒* T.lam v″) →
    (∃ λ v″ → v′ T.⇒* T.lam v″)
  Π-lemma v⇒v′ (_ , v⇒*lam)
    with red*Det v⇒*lam (T.trans v⇒v′ T.refl)
  … | inj₁ lam⇒*v′ rewrite Value→⇒*→≡ T.lam lam⇒*v′ = _ , T.refl
  … | inj₂ v′⇒*lam = _ , v′⇒*lam

  ⇒*↯→⇒→⇒*↯ :
    (str PE.≡ strict → v T.⇒* ↯) → v T.⇒ v′ →
    str PE.≡ strict → v′ T.⇒* ↯
  ⇒*↯→⇒→⇒*↯ {v′} v⇒*↯ v⇒v′ ≡strict =
    case red*Det (v⇒*↯ ≡strict) (T.trans v⇒v′ T.refl) of λ where
      (inj₂ v′⇒*↯) → v′⇒*↯
      (inj₁ ↯⇒*v′) →
        v′  ≡⟨ ↯-noRed ↯⇒*v′ ⟩⇒
        ↯   ∎⇒

-- The logical relation for erasure is preserved under reduction of
-- the target language term.

targetRedSubstTerm*′ :
  ∀ {l} ([A] : Δ ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v ∷ A / [A] →
  v T.⇒* v′ → t ®⟨ l ⟩ v′ ∷ A / [A]

-- Logical relation for erasure is preserved under one reduction step on the target language term
-- If t ® v ∷ A and v ⇒ v′  then t ® v′ ∷ A
--
-- Proof by induction on t ® v ∷ A

targetRedSubstTerm′ : ∀ {l} ([A] : Δ ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v ∷ A / [A]
                    → v T.⇒ v′ → t ®⟨ l ⟩ v′ ∷ A / [A]
targetRedSubstTerm′ (Levelᵣ _) (U/Levelᵣ v⇒*↯) v⇒v′ =
  U/Levelᵣ (⇒*↯→⇒→⇒*↯ v⇒*↯ v⇒v′)
targetRedSubstTerm′ (Uᵣ _) (U/Levelᵣ v⇒*↯) v⇒v′ =
  U/Levelᵣ (⇒*↯→⇒→⇒*↯ v⇒*↯ v⇒v′)
targetRedSubstTerm′ (ℕᵣ x) (zeroᵣ x₁ v⇒zero) v⇒v′ with red*Det v⇒zero (T.trans v⇒v′ T.refl)
... | inj₁ x₂ rewrite zero-noRed x₂ = zeroᵣ x₁ T.refl
... | inj₂ x₂ = zeroᵣ x₁ x₂
targetRedSubstTerm′ (ℕᵣ _) (sucᵣ t⇒suc v⇒suc num t®v) v⇒v′
  with red*Det v⇒suc (T.trans v⇒v′ T.refl)
... | inj₁ suc⇒* rewrite suc-noRed suc⇒* = sucᵣ t⇒suc T.refl num t®v
... | inj₂ ⇒*suc = sucᵣ t⇒suc ⇒*suc num t®v
targetRedSubstTerm′ (Unitᵣ _) (starᵣ ⇛⋆ u≡u′ v⇒star) v⇒v′
  with red*Det v⇒star (T.trans v⇒v′ T.refl)
... | inj₁ ⋆⇒v′ rewrite star-noRed ⋆⇒v′ = starᵣ ⇛⋆ u≡u′ T.refl
... | inj₂ v′⇒⋆                         = starᵣ ⇛⋆ u≡u′ v′⇒⋆
targetRedSubstTerm′
  (Bᵣ′ (BΠ p q) F G D A≡A [F] [G] G-ext _) t®v′ v⇒v′
  with is-𝟘? p
... | yes PE.refl = Π-lemma v⇒v′ ∘→ t®v′ .proj₁ , λ [a] →
  let t®v = t®v′ .proj₂ [a]
  in  targetRedSubstTerm′ ([G] (id ⊢Δ) [a]) t®v (app-𝟘′-subst v⇒v′)
... | no p≢𝟘 = Π-lemma v⇒v′ ∘→ t®v′ .proj₁ , λ [a] a®w →
  let t®v = t®v′ .proj₂ [a] a®w
      v∘w⇒v′∘w = T.app-subst v⇒v′
  in  targetRedSubstTerm′ ([G] (id ⊢Δ) [a]) t®v v∘w⇒v′∘w
targetRedSubstTerm′
  {v′ = v′}
  (Bᵣ′ (BΣ _ p _) F G D A≡A [F] [G] G-ext _)
  (t₁ , t₂ , t⇒t′ , [t₁] , v₂ , t₂®v₂ , extra) v⇒v′ =
  let [Gt₁] = [G] (id ⊢Δ) [t₁]
  in  t₁ , t₂ , t⇒t′ , [t₁]
      , Σ-®-elim
         (λ _ → ∃ λ v₂ → (t₂ ®⟨ _ ⟩ v₂ ∷ U.wk (lift id) G U.[ t₁ ]₀ / [Gt₁])
                       × Σ-® _ F _ t₁ v′ v₂ p)
         extra
         (λ v⇒v₂ p≡𝟘 → case red*Det v⇒v₂ (trans v⇒v′ refl) of λ where
           (inj₁ v₂⇒v′) → v′ , targetRedSubstTerm*′ [Gt₁] t₂®v₂ v₂⇒v′
                             , Σ-®-intro-𝟘 refl p≡𝟘
           (inj₂ v′⇒v₂) → v₂ , t₂®v₂ , Σ-®-intro-𝟘 v′⇒v₂ p≡𝟘)
         λ v₁ v⇒p t₁®v₁ p≢𝟘 → v₂ , t₂®v₂ , (case red*Det v⇒p (trans v⇒v′ refl) of λ where
           (inj₁ p⇒v′) → case prod-noRed p⇒v′ of λ where
             PE.refl → Σ-®-intro-ω v₁ refl t₁®v₁ p≢𝟘
           (inj₂ v′⇒p) → Σ-®-intro-ω v₁ v′⇒p t₁®v₁ p≢𝟘)

targetRedSubstTerm′ (Idᵣ _) (rflᵣ t⇒*rfl v⇒*↯) v⇒v′ =
  rflᵣ t⇒*rfl (⇒*↯→⇒→⇒*↯ v⇒*↯ v⇒v′)
targetRedSubstTerm′ (ne record{}) ()
targetRedSubstTerm′ (Emptyᵣ _)    ()


targetRedSubstTerm*′ [A] t®v refl = t®v
targetRedSubstTerm*′ [A] t®v (trans x v⇒v′) =
  targetRedSubstTerm*′ [A] (targetRedSubstTerm′ [A] t®v x) v⇒v′

-- The logical relation for erasure is preserved by "reduction" for
-- the source term and reduction for the target term.

redSubstTerm′ : ∀ {l} ([A] : Δ ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v ∷ A / [A]
              → t ⇛ t′ ∷ A → v T.⇒ v′ → t′ ®⟨ l ⟩ v′ ∷ A / [A]
redSubstTerm′ [A] t®v t⇒t′ v⇒v′ =
  targetRedSubstTerm′ [A] (sourceRedSubstTerm′ [A] t®v t⇒t′) v⇒v′

-- The logical relation for erasure is preserved by "reduction" for
-- the source term and reduction for the target term.

redSubstTerm*′ : ∀ {l} ([A] : Δ ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v ∷ A / [A]
               → t ⇛ t′ ∷ A → v T.⇒* v′ → t′ ®⟨ l ⟩ v′ ∷ A / [A]
redSubstTerm*′ [A] t®v t⇒t′ v⇒v′ =
  targetRedSubstTerm*′ [A] (sourceRedSubstTerm′ [A] t®v t⇒t′) v⇒v′
