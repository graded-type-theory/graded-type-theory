{-# OPTIONS --without-K --safe #-}
open import Definition.Modality.Erasure

open import Definition.Typed.EqualityRelation

module Erasure.LogicalRelation.Properties {{eqrel : EqRelSet Erasure}} where
open EqRelSet {{...}}

open import Definition.LogicalRelation Erasure
open import Definition.LogicalRelation.Properties.Escape Erasure
open import Definition.Typed Erasure
open import Definition.Typed.Properties Erasure
open import Definition.Typed.RedSteps Erasure as RS
open import Definition.Typed.Weakening Erasure
open import Definition.Untyped Erasure as U hiding (_∷_)
open import Definition.Untyped.Properties Erasure using (noClosedNe ; wk-id ; wk-lift-id)

open import Erasure.LogicalRelation
open import Erasure.Target as T hiding (_⇒*_)
open import Erasure.Target.Properties.Reduction as TP using (red*concat)

open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    t t′ A : U.Term 0
    v v′ : T.Term 0

-- Related terms are well-formed

wfTermEscapeℕ : t ® v ∷ℕ → ε ⊢ t ∷ ℕ
wfTermEscapeℕ (zeroᵣ x x₁) = redFirst*Term x
wfTermEscapeℕ (sucᵣ x x₁ t®v) = redFirst*Term x

wfTermEscapeU : t ® v ∷U → ε ⊢ t ∷ U
wfTermEscapeU (Uᵣ x x₁) = x

wfTermEscapeUnit : t ® v ∷Unit → ε ⊢ t ∷ Unit
wfTermEscapeUnit (starᵣ x x₁) = redFirst*Term x

wfTermEscapeEmpty : t ® v ∷Empty → ε ⊢ t ∷ Empty
wfTermEscapeEmpty (Emptyᵣ x x₁) = x



-- Relation is preserved by reduction backwards

®-back-closureˡ : ∀ {l} ([A] : ε ⊩⟨ l ⟩ A) → t′ ®⟨ l ⟩ v ∷ A / [A] → ε ⊢ t ⇒* t′ ∷ A → t ®⟨ l ⟩ v ∷ A / [A]
®-back-closureˡ (Uᵣ x) (Uᵣ x₁ x₂) t⇒t′ = Uᵣ (redFirst*Term t⇒t′) x₂
®-back-closureˡ (ℕᵣ [ ⊢A , ⊢B , D ]) (zeroᵣ t′⇒zero v⇒zero) t⇒t′ = zeroᵣ
  ((conv* t⇒t′ (subset* D)) ⇨∷* t′⇒zero)
  v⇒zero
®-back-closureˡ [ℕ]@(ℕᵣ ([ ⊢A , ⊢B , D ])) (sucᵣ t⇒suct′ v⇒sucv′ t′®v′) t⇒t′ = sucᵣ
  ((conv* t⇒t′ (subset* D)) ⇨∷* t⇒suct′)
  v⇒sucv′
  t′®v′
®-back-closureˡ (Emptyᵣ [ ⊢A , ⊢B , D ]) (Emptyᵣ ⊢t:Empty v⇒undefined) t⇒t′ = Emptyᵣ
  (conv (redFirst*Term t⇒t′) (subset* D))
  v⇒undefined
®-back-closureˡ (Unitᵣ [ ⊢A , ⊢B , D ]) (starᵣ t′⇒star v⇒star) t⇒t′ = starᵣ
  ((conv* t⇒t′ (subset* D)) ⇨∷* t′⇒star)
  v⇒star
®-back-closureˡ (ne′ K D neK K≡K) t′®v t⇒t′ with noClosedNe neK
... | ()
®-back-closureˡ {A} (Bᵣ′ (BΠ 𝟘 q) F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext) t®v t⇒t′ [a] = ®-back-closureˡ
  ([G] id ε [a])
  (t®v [a])
  (RS.app-subst* (conv* t⇒t′
                              (PE.subst (ε ⊢ A ≡_)
                                        ((PE.cong₂ (⟦ BΠ 𝟘 q ⟧_▹_))
                                                   (PE.sym (wk-id F))
                                                   (PE.sym (wk-lift-id G)))
                                        (subset* D)))
                       (escapeTerm ([F] id ε) [a]))
®-back-closureˡ {A} (Bᵣ′ (BΠ ω q) F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext) t®v t⇒t′ [a] a®w = ®-back-closureˡ
  ([G] id ε [a])
  (t®v [a] a®w)
  (RS.app-subst* (conv* t⇒t′
                              (PE.subst (ε ⊢ A ≡_)
                                        (PE.cong₂ (⟦ BΠ ω q ⟧_▹_)
                                                  (PE.sym (wk-id F))
                                                  (PE.sym (wk-lift-id G)))
                                        (subset* D)))
                       (escapeTerm ([F] id ε) [a]))
®-back-closureˡ (Bᵣ′ (BΣ q) F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext) t®v t⇒t′ [t₁] [t₂] =
  let ®Σ = t®v [t₁] [t₂]
      t′⇒p = proj₁ ®Σ
      v⇒w = proj₁ (proj₂ ®Σ)
      t₁®v₁ = proj₁ (proj₂ (proj₂ ®Σ))
      t₂®v₂ = proj₂ (proj₂ (proj₂ ®Σ))
  in  ((conv* t⇒t′ (subset* D)) ⇨∷* t′⇒p) , v⇒w , t₁®v₁ , t₂®v₂
®-back-closureˡ (emb 0<1 [A]) t′®v t⇒t′ = ®-back-closureˡ [A] t′®v t⇒t′


®-back-closureʳ : ∀ {l} ([A] : ε ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v′ ∷ A / [A] → v T.⇒* v′ → t ®⟨ l ⟩ v ∷ A / [A]
®-back-closureʳ (Uᵣ x) (Uᵣ ⊢t:U v′⇒undefined) v⇒v′ = Uᵣ ⊢t:U (red*concat v⇒v′ v′⇒undefined)
®-back-closureʳ (ℕᵣ x) (zeroᵣ t⇒zero v′⇒zero) v⇒v′ = zeroᵣ t⇒zero (red*concat v⇒v′ v′⇒zero)
®-back-closureʳ (ℕᵣ x) (sucᵣ t⇒suct′ v′⇒sucw t′®w) v⇒v′ = sucᵣ t⇒suct′ (red*concat v⇒v′ v′⇒sucw) t′®w
®-back-closureʳ (Emptyᵣ x) (Emptyᵣ ⊢t:Empty v′⇒undefined) v⇒v′ = Emptyᵣ ⊢t:Empty (red*concat v⇒v′ v′⇒undefined)
®-back-closureʳ (Unitᵣ x) (starᵣ t⇒star v′⇒star) v⇒v′ = starᵣ t⇒star (red*concat v⇒v′ v′⇒star)
®-back-closureʳ (ne′ K D neK K≡K) t®v′ v⇒v′ with noClosedNe neK
... | ()
®-back-closureʳ (Bᵣ′ (BΠ 𝟘 q) F G D ⊢F ⊢G A≡A [F] [G] G-ext) t®v v⇒v′ [a] = ®-back-closureʳ ([G] id ε [a]) (t®v [a]) (TP.app-subst* v⇒v′)
®-back-closureʳ (Bᵣ′ (BΠ ω q) F G D ⊢F ⊢G A≡A [F] [G] G-ext) t®v v⇒v′ [a] a®w = ®-back-closureʳ ([G] id ε [a]) (t®v [a] a®w) (TP.app-subst* v⇒v′)
®-back-closureʳ (Bᵣ (BΣ q) x) t®v v⇒v′ [t₁] [t₂] =
  let ®Σ = t®v [t₁] [t₂]
      t⇒p = proj₁ ®Σ
      v′⇒w = proj₁ (proj₂ ®Σ)
      t₁®v₁ = proj₁ (proj₂ (proj₂ ®Σ))
      t₂®v₂ = proj₂ (proj₂ (proj₂ ®Σ))
  in t⇒p , red*concat v⇒v′ v′⇒w , t₁®v₁ , t₂®v₂
®-back-closureʳ (emb 0<1 [A]) t®v′ v⇒v′ = ®-back-closureʳ [A] t®v′ v⇒v′
