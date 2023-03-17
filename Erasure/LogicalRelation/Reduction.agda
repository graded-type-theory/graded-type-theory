open import Definition.Modality.Instances.Erasure
open import Definition.Modality.Restrictions
open import Definition.Typed.EqualityRelation
open import Definition.Untyped Erasure as U hiding (_∷_)
open import Definition.Typed Erasure

module Erasure.LogicalRelation.Reduction
  {k} {Δ : Con Term k} (⊢Δ : ⊢ Δ)
  (restrictions : Restrictions Erasure)
  {{eqrel : EqRelSet Erasure}}
  where

open EqRelSet {{...}}

open import Definition.LogicalRelation Erasure
open import Definition.LogicalRelation.Properties.Escape Erasure

import Definition.LogicalRelation.Fundamental Erasure as F
import Definition.LogicalRelation.Irrelevance Erasure as I
import Definition.LogicalRelation.Properties.Reduction Erasure as R

open import Definition.Typed.Consequences.Syntactic Erasure
open import Definition.Typed.Consequences.Reduction Erasure
open import Definition.Typed.Properties Erasure
open import Definition.Typed.RedSteps Erasure as RS
open import Definition.Typed.Weakening Erasure

open import Definition.Untyped.Properties Erasure as UP using (wk-id ; wk-lift-id)

open import Erasure.LogicalRelation ⊢Δ restrictions
open import Erasure.Target as T hiding (_⇒_; _⇒*_)
open import Erasure.Target.Properties as TP

open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Sum hiding (id ; sym)

private
  variable
    n : Nat
    t t′ A : U.Term n
    v v′ : T.Term n
    Γ : Con U.Term n

-- Logical relation for erasure is preserved under a single reduction backwards on the source language term
-- If t′ ® v ∷ A and Δ ⊢ t ⇒ t′ ∷ A then t ® v ∷ A

sourceRedSubstTerm : ∀ {l} ([A] : Δ ⊩⟨ l ⟩ A) → t′ ®⟨ l ⟩ v ∷ A / [A]
                   → Δ ⊢ t ⇒ t′ ∷ A → t ®⟨ l ⟩ v ∷ A / [A]
sourceRedSubstTerm (Uᵣ _) (Uᵣ _) t⇒t′ =
  Uᵣ (redFirstTerm t⇒t′)
sourceRedSubstTerm (ℕᵣ ([ ⊢A , ⊢B , D ])) (zeroᵣ t′⇒zero v⇒v′) t⇒t′ =
  zeroᵣ ((conv t⇒t′ (subset* D)) ⇨ t′⇒zero) v⇒v′
sourceRedSubstTerm (ℕᵣ ([ ⊢A , ⊢B , D ])) (sucᵣ t′⇒suc v⇒v′ t®v) t⇒t′ =
  sucᵣ ((conv t⇒t′ (subset* D)) ⇨ t′⇒suc) v⇒v′ t®v
sourceRedSubstTerm (Unitᵣ ([ ⊢A , ⊢B , D ])) (starᵣ x v⇒star) t⇒t′ =
  starᵣ (conv (redFirstTerm t⇒t′) (subset* D)) v⇒star
sourceRedSubstTerm (Bᵣ′ (BΠ 𝟘 q) F G ([ ⊢A , ⊢B , D ]) ⊢F ⊢G A≡A [F] [G] G-ext)
                   t®v′ t⇒t′ {a = a} [a] =
  let t®v = t®v′ [a]
      ⊢a = escapeTerm ([F] id ⊢Δ) [a]
      ⊢a′ = PE.subst (Δ ⊢ a ∷_) (UP.wk-id F) ⊢a
      t∘a⇒t′∘w′ = app-subst (conv t⇒t′ (subset* D)) ⊢a′
      t∘a⇒t′∘w = PE.subst (_⊢_⇒_∷_ Δ _ _) (PE.cong (U._[ a ]) (PE.sym (UP.wk-lift-id G))) t∘a⇒t′∘w′
  in sourceRedSubstTerm ([G] id ⊢Δ [a]) t®v t∘a⇒t′∘w
sourceRedSubstTerm (Bᵣ′ (BΠ ω q) F G ([ ⊢A , ⊢B , D ]) ⊢F ⊢G A≡A [F] [G] G-ext)
                   t®v′ t⇒t′ {a = a} [a] a®w =
  let t®v = t®v′ [a] a®w
      ⊢a = escapeTerm ([F] id ⊢Δ) [a]
      ⊢a′ = PE.subst (Δ ⊢ a ∷_) (UP.wk-id F) ⊢a
      t∘a⇒t′∘w′ = app-subst (conv t⇒t′ (subset* D)) ⊢a′
      t∘a⇒t′∘w = PE.subst (Δ ⊢ _ ⇒ _ ∷_) (PE.cong (U._[ a ]) (PE.sym (UP.wk-lift-id G))) t∘a⇒t′∘w′
  in sourceRedSubstTerm ([G] id ⊢Δ [a]) t®v t∘a⇒t′∘w
sourceRedSubstTerm
  (Bᵣ′ BΣ! F G ([ ⊢A , ⊢B , D ]) ⊢F ⊢G A≡A [F] [G] G-ext)
  (t₁ , t₂ , t′⇒p , [t₁] , v₂ , t₂®v₂ , extra) t⇒t′ =
  t₁ , t₂ , conv t⇒t′ (subset* D) ⇨ t′⇒p , [t₁] , v₂ , t₂®v₂ , extra
sourceRedSubstTerm (emb 0<1 [A]) t®v t⇒t′ = sourceRedSubstTerm [A] t®v t⇒t′


-- Logical relation for erasure is preserved under reduction closure backwards on the source language term
-- If t′ ® v ∷ A and Δ ⊢ t ⇒* t′ ∷ A then t ® v ∷ A

sourceRedSubstTerm* : ∀ {l} ([A] : Δ ⊩⟨ l ⟩ A) → t′ ®⟨ l ⟩ v ∷ A / [A]
                    → Δ ⊢ t ⇒* t′ ∷ A → t ®⟨ l ⟩ v ∷ A / [A]
sourceRedSubstTerm* [A] t′®v (id x) = t′®v
sourceRedSubstTerm* [A] t′®v (x ⇨ t⇒t′) =
  sourceRedSubstTerm [A] (sourceRedSubstTerm* [A] t′®v t⇒t′) x


-- Logical relation for erasure is preserved under a single reduction backwards on the target language term
-- If t ® v′ ∷ A and v ⇒ v′ then t ® v ∷ A

targetRedSubstTerm : ∀ {l} ([A] : Δ ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v′ ∷ A / [A]
                   → v T.⇒ v′ → t ®⟨ l ⟩ v ∷ A / [A]
targetRedSubstTerm (Uᵣ x) (Uᵣ x₁) v⇒v′ = Uᵣ x₁
targetRedSubstTerm (ℕᵣ x) (zeroᵣ t′⇒zero v′⇒zero) v⇒v′ = zeroᵣ t′⇒zero (trans v⇒v′ v′⇒zero)
targetRedSubstTerm (ℕᵣ x) (sucᵣ t′⇒suc v′⇒suc t®v) v⇒v′ = sucᵣ t′⇒suc (trans v⇒v′ v′⇒suc) t®v
targetRedSubstTerm (Unitᵣ x) (starᵣ x₁ v′⇒star) v⇒v′ = starᵣ x₁ (trans v⇒v′ v′⇒star)
targetRedSubstTerm (Bᵣ′ (BΠ 𝟘 q) F G ([ ⊢A , ⊢B , D ]) ⊢F ⊢G A≡A [F] [G] G-ext)
                   t®v′ v⇒v′ {a = a} [a] =
  let t®v = t®v′ [a]
      v∘w⇒v′∘w′ = T.app-subst v⇒v′
      [G[a]] = [G] id ⊢Δ [a]
  in targetRedSubstTerm [G[a]] t®v v∘w⇒v′∘w′
targetRedSubstTerm (Bᵣ′ (BΠ ω q) F G ([ ⊢A , ⊢B , D ]) ⊢F ⊢G A≡A [F] [G] G-ext)
       t®v′ v⇒v′ {a = a} [a] a®w =
  let t®v = t®v′ [a] a®w
      v∘w⇒v′∘w′ = T.app-subst v⇒v′
      [G[a]] = [G] id ⊢Δ [a]
  in targetRedSubstTerm [G[a]] t®v v∘w⇒v′∘w′
targetRedSubstTerm
  (Bᵣ′ BΣ! F G ([ ⊢A , ⊢B , D ]) ⊢F ⊢G A≡A [F] [G] G-ext)
  (t₁ , t₂ , v₂ , t⇒t′ , [t₁] , t₂®v₂ , extra) v⇒v′ =
  t₁ , t₂ , v₂ , t⇒t′ , [t₁] , t₂®v₂ ,
  (case Σ-®-view extra of λ where
     (𝟘 v′⇒p)          → trans v⇒v′ v′⇒p
     (ω v₁ v′⇒p t₁®v₁) → v₁ , trans v⇒v′ v′⇒p , t₁®v₁)
targetRedSubstTerm (emb 0<1 [A]) t®v′ v⇒v′ = targetRedSubstTerm [A] t®v′ v⇒v′


-- Logical relation for erasure is preserved under reduction closure backwards
-- on the target language term.
-- If t ® v′ ∷ A and v ⇒* v′ then t ® v ∷ A

targetRedSubstTerm* : ∀ {l} ([A] : Δ ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v′ ∷ A / [A]
                    → v T.⇒* v′ → t ®⟨ l ⟩ v ∷ A / [A]
targetRedSubstTerm* [A] t®v′ refl = t®v′
targetRedSubstTerm* [A] t®v′ (trans x v⇒v′) =
  targetRedSubstTerm [A] (targetRedSubstTerm* [A] t®v′ v⇒v′) x


-- Logical relation for erasure is preserved under reduction backwards
-- If t′ ® v′ ∷ A and Δ ⊢ t ⇒ t′ ∷ A and v ⇒ v′ then t ® v ∷ A

redSubstTerm : ∀ {l} ([A] : Δ ⊩⟨ l ⟩ A) → t′ ®⟨ l ⟩ v′ ∷ A / [A]
             → Δ ⊢ t ⇒ t′ ∷ A → v T.⇒ v′ → t ®⟨ l ⟩ v ∷ A / [A]
redSubstTerm [A] t′®v′ t⇒t′ v⇒v′ =
  targetRedSubstTerm [A] (sourceRedSubstTerm [A] t′®v′ t⇒t′) v⇒v′


-- Logical relation for erasure is preserved under reduction closure backwards
-- If t′ ® v′ ∷ A and Δ ⊢ t ⇒* t′ ∷ A and v ⇒* v′ then t ® v ∷ A

redSubstTerm* : ∀ {l} ([A] : Δ ⊩⟨ l ⟩ A) → t′ ®⟨ l ⟩ v′ ∷ A / [A]
              → Δ ⊢ t ⇒* t′ ∷ A → v T.⇒* v′ → t ®⟨ l ⟩ v ∷ A / [A]
redSubstTerm* [A] t′®v′ t⇒t′ v⇒v′ = targetRedSubstTerm* [A] (sourceRedSubstTerm* [A] t′®v′ t⇒t′) v⇒v′


-- Logical relation for erasure is preserved under one reduction step on the source language term
-- If t ® v ∷ A and Δ ⊢ t ⇒ t′ ∷ A  then t′ ® v ∷ A

sourceRedSubstTerm′ : ∀ {l} ([A] : Δ ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v ∷ A / [A]
                    → Δ ⊢ t ⇒ t′ ∷ A → t′ ®⟨ l ⟩ v ∷ A / [A]
sourceRedSubstTerm′ (Uᵣ x) (Uᵣ x₁) t⇒t′ with syntacticRedTerm (redMany t⇒t′)
... | _ , _ , Δ⊢t′∷U = Uᵣ Δ⊢t′∷U
sourceRedSubstTerm′ (ℕᵣ [ ⊢A , ⊢B , D ]) (zeroᵣ t⇒zero v⇒zero) t⇒t′ with whrDet↘Term (t⇒zero , zeroₙ) (conv* (redMany t⇒t′) (subset* D))
... | t′⇒zero = zeroᵣ t′⇒zero v⇒zero
sourceRedSubstTerm′ (ℕᵣ [ ⊢A , ⊢B , D ]) (sucᵣ t⇒suc v⇒suc t®v) t⇒t′ with whrDet↘Term (t⇒suc , sucₙ) (conv* (redMany t⇒t′) (subset* D))
... | t′⇒suc = sucᵣ t′⇒suc v⇒suc t®v
sourceRedSubstTerm′ (Unitᵣ x) (starᵣ x₁ v⇒star) t⇒t′ with syntacticRedTerm (redMany t⇒t′)
... | _ , _ , Δ⊢t′∷Unit = starᵣ (conv Δ⊢t′∷Unit (subset* (red x))) v⇒star
sourceRedSubstTerm′ (Bᵣ′ (BΠ 𝟘 q) F G D ⊢F ⊢G A≡A [F] [G] G-ext) t®v′ t⇒t′ {a = a} [a] =
  let t®v = t®v′ [a]
      ⊢a = escapeTerm ([F] id ⊢Δ) [a]
      ⊢a′ = PE.subst (Δ ⊢ a ∷_) (UP.wk-id F) ⊢a
      t∘a⇒t′∘a′ = app-subst (conv t⇒t′ (subset* (red D))) ⊢a′
      t∘a⇒t′∘a = PE.subst (_⊢_⇒_∷_ Δ _ _)
                          (PE.cong (U._[ a ]) (PE.sym (UP.wk-lift-id G)))
                          t∘a⇒t′∘a′
  in  sourceRedSubstTerm′ ([G] id ⊢Δ [a]) t®v t∘a⇒t′∘a
sourceRedSubstTerm′ (Bᵣ′ (BΠ ω q) F G D ⊢F ⊢G A≡A [F] [G] G-ext) t®v′ t⇒t′ {a = a} [a] a®w =
  let t®v = t®v′ [a] a®w
      ⊢a = escapeTerm ([F] id ⊢Δ) [a]
      ⊢a′ = PE.subst (Δ ⊢ a ∷_) (UP.wk-id F) ⊢a
      t∘a⇒t′∘a′ = app-subst (conv t⇒t′ (subset* (red D))) ⊢a′
      t∘a⇒t′∘a = PE.subst (_⊢_⇒_∷_ Δ _ _)
                          (PE.cong (U._[ a ]) (PE.sym (UP.wk-lift-id G)))
                          t∘a⇒t′∘a′
  in  sourceRedSubstTerm′ ([G] id ⊢Δ [a]) t®v t∘a⇒t′∘a
sourceRedSubstTerm′
  (Bᵣ′ BΣ! F G D ⊢F ⊢G A≡A [F] [G] G-ext)
  (t₁ , t₂ , t⇒p , [t₁] , v₂ , t₂®v₂ , extra) t⇒t′ =
  t₁ , t₂
     , whrDet↘Term (t⇒p , prodₙ) (redMany (conv t⇒t′ (subset* (red D))))
     , [t₁] , v₂ , t₂®v₂ , extra
sourceRedSubstTerm′ (emb 0<1 [A]) t®v t⇒t′ = sourceRedSubstTerm′ [A] t®v t⇒t′


-- Logical relation for erasure is preserved under reduction closure on the source language term
-- If t ® v ∷ A and Δ ⊢ t ⇒* t′ ∷ A  then t′ ® v ∷ A

sourceRedSubstTerm*′ : ∀ {l} ([A] : Δ ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v ∷ A / [A]
                     → Δ ⊢ t ⇒* t′ ∷ A → t′ ®⟨ l ⟩ v ∷ A / [A]
sourceRedSubstTerm*′ [A] t®v (id x) = t®v
sourceRedSubstTerm*′ [A] t®v (x ⇨ t⇒t′) =
  sourceRedSubstTerm*′ [A] (sourceRedSubstTerm′ [A] t®v x) t⇒t′

-- The logical relation for erasure is preserved under reduction of
-- the target language term.

targetRedSubstTerm*′ :
  ∀ {l} ([A] : Δ ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v ∷ A / [A] →
  v T.⇒* v′ → t ®⟨ l ⟩ v′ ∷ A / [A]

-- Logical relation for erasure is preserved under one reduction step on the target language term
-- If t ® v ∷ A and v ⇒ v′  then t ® v′ ∷ A

targetRedSubstTerm′ : ∀ {l} ([A] : Δ ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v ∷ A / [A]
                    → v T.⇒ v′ → t ®⟨ l ⟩ v′ ∷ A / [A]
targetRedSubstTerm′ (Uᵣ x) (Uᵣ x₁) v⇒v′ = Uᵣ x₁
targetRedSubstTerm′ (ℕᵣ x) (zeroᵣ x₁ v⇒zero) v⇒v′ with red*Det v⇒zero (T.trans v⇒v′ T.refl)
... | inj₁ x₂ rewrite zero-noRed x₂ = zeroᵣ x₁ T.refl
... | inj₂ x₂ = zeroᵣ x₁ x₂
targetRedSubstTerm′ (ℕᵣ x) (sucᵣ x₁ v⇒suc t®v) v⇒v′ with red*Det v⇒suc (T.trans v⇒v′ T.refl)
... | inj₁ x₂ rewrite suc-noRed x₂ = sucᵣ x₁ T.refl t®v
... | inj₂ x₂ = sucᵣ x₁ x₂ t®v
targetRedSubstTerm′ (Unitᵣ x) (starᵣ x₁ v⇒star) v⇒v′ with red*Det v⇒star (T.trans v⇒v′ T.refl)
... | inj₁ x₂ rewrite star-noRed x₂ = starᵣ x₁ T.refl
... | inj₂ x₂ = starᵣ x₁ x₂
targetRedSubstTerm′ (Bᵣ′ (BΠ 𝟘 q) F G D ⊢F ⊢G A≡A [F] [G] G-ext) t®v′ v⇒v′ [a] =
  let t®v = t®v′ [a]
      v∘w⇒v′∘w = T.app-subst v⇒v′
  in  targetRedSubstTerm′ ([G] id ⊢Δ [a]) t®v v∘w⇒v′∘w
targetRedSubstTerm′ (Bᵣ′ (BΠ ω q) F G D ⊢F ⊢G A≡A [F] [G] G-ext) t®v′ v⇒v′ [a] a®w =
  let t®v = t®v′ [a] a®w
      v∘w⇒v′∘w = T.app-subst v⇒v′
  in  targetRedSubstTerm′ ([G] id ⊢Δ [a]) t®v v∘w⇒v′∘w
targetRedSubstTerm′
  {v′ = v′}
  (Bᵣ′ BΣ! F G D ⊢F ⊢G A≡A [F] [G] G-ext)
  (t₁ , t₂ , t⇒t′ , [t₁] , v₂ , t₂®v₂ , extra) v⇒v′ =
  t₁ , t₂ , t⇒t′ , [t₁] ,
  (case Σ-®-view extra of λ where
     (𝟘 v⇒v₂) →
       case red*Det v⇒v₂ (trans v⇒v′ refl) of λ where
         (inj₂ v′⇒v₂) → v₂ , t₂®v₂ , v′⇒v₂
         (inj₁ v₂⇒v′) →
           v′ , targetRedSubstTerm*′ ([G] id ⊢Δ [t₁]) t₂®v₂ v₂⇒v′ , refl
     (ω v₁ v⇒v₁,v₂ t₁®v₁) →
       case red*Det v⇒v₁,v₂ (trans v⇒v′ refl) of λ where
         (inj₂ v′⇒v₁,v₂) → v₂ , t₂®v₂ , v₁ , v′⇒v₁,v₂ , t₁®v₁
         (inj₁ v₁,v₂⇒v′) → case prod-noRed v₁,v₂⇒v′ of λ where
           PE.refl → v₂ , t₂®v₂ , v₁ , refl , t₁®v₁)

targetRedSubstTerm′ (emb 0<1 [A]) t®v v⇒v′ = targetRedSubstTerm′ [A] t®v v⇒v′


targetRedSubstTerm*′ [A] t®v refl = t®v
targetRedSubstTerm*′ [A] t®v (trans x v⇒v′) =
  targetRedSubstTerm*′ [A] (targetRedSubstTerm′ [A] t®v x) v⇒v′

-- Logical relation for erasure is preserved under reduction
-- If t ® v ∷ A and Δ ⊢ t ⇒ t′ ∷ A and v ⇒ v′ then t′ ® v′ ∷ A

redSubstTerm′ : ∀ {l} ([A] : Δ ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v ∷ A / [A]
              → Δ ⊢ t ⇒ t′ ∷ A → v T.⇒ v′ → t′ ®⟨ l ⟩ v′ ∷ A / [A]
redSubstTerm′ [A] t®v t⇒t′ v⇒v′ =
  targetRedSubstTerm′ [A] (sourceRedSubstTerm′ [A] t®v t⇒t′) v⇒v′

-- Logical relation for erasure is preserved under reduction closure
-- If t ® v ∷ A and Δ ⊢ t ⇒* t′ ∷ A and v ⇒* v′ then t′ ® v′ ∷ A

redSubstTerm*′ : ∀ {l} ([A] : Δ ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v ∷ A / [A]
               → Δ ⊢ t ⇒* t′ ∷ A → v T.⇒* v′ → t′ ®⟨ l ⟩ v′ ∷ A / [A]
redSubstTerm*′ [A] t®v t⇒t′ v⇒v′ =
  targetRedSubstTerm*′ [A] (sourceRedSubstTerm*′ [A] t®v t⇒t′) v⇒v′
