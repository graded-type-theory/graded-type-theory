open import Definition.Modality.Erasure

open import Definition.Typed.EqualityRelation

module Erasure.LogicalRelation {{eqrel : EqRelSet Erasure}} where
open EqRelSet {{...}}



open import Definition.Untyped Erasure as U hiding (_∷_)
open import Definition.Untyped.Properties Erasure
open import Definition.Typed Erasure as Ty
open import Definition.Typed.Properties Erasure
open import Definition.Typed.RedSteps Erasure
open import Erasure.Target as T renaming (_⇒*_ to _=>*_)
open import Erasure.Extraction

open import Definition.LogicalRelation Erasure
open import Definition.LogicalRelation.Properties.Escape Erasure

open import Tools.Nat
open import Tools.Product



private
  variable
    n : Nat
    t t′ u A B : U.Term n
    v v′ : T.Term n
    p : Erasure

mutual

  data _®_∷U : (t : U.Term 0) (v : T.Term 0) → Set where
    Uᵣ : ε ⊢ t ∷ U → v T.⇒* undefined → t ® v ∷U

  data _®_∷ℕ : (t : U.Term 0) (v : T.Term 0) → Set where
    zeroᵣ : ε ⊢ t ⇒* U.zero ∷ ℕ → v T.⇒* T.zero → t ® v ∷ℕ
    sucᵣ : ε ⊢ t ⇒* U.suc t′ ∷ ℕ → v T.⇒* T.suc v′ → t′ ® v′ ∷ℕ → t ® v ∷ℕ

  data _®_∷Empty : (t : U.Term 0) (v : T.Term 0) → Set where
    Emptyᵣ : ε ⊢ t ∷ Empty → v T.⇒* undefined → t ® v ∷Empty

  data _®_∷Unit : (t : U.Term 0) (v : T.Term 0) → Set where
    starᵣ : ε ⊢ t ⇒* U.star ∷ Unit → v T.⇒* T.star → t ® v ∷Unit

  data _®_∷Π_ : (t : U.Term 0) (v : T.Term 0) (p : Erasure) → Set where
    Πωᵣ : ∀ {l} → (∀ {a a′} → (⊢a:A : ε ⊢ a ∷ A)
                            → ([A] : ε ⊩⟨ l ⟩ A)
                            → ([B] : ε ⊩⟨ l ⟩ B U.[ a ])
                            →  a ®⟨ l ⟩ a′ ∷ A / [A]
                            → (t ∘ ω ▷ a) ®⟨ l ⟩ v ∘ a′ ∷ B U.[ a ] / [B])
                → t ® v ∷Π ω
    Π𝟘ᵣ : ∀ {l} → (∀ {a} → (⊢a:A : ε ⊢ a ∷ A)
                         -- → ([A] : ε ⊩⟨ l ⟩ A)
                         → ([B] : ε ⊩⟨ l ⟩ B U.[ a ])
                         → (t ∘ 𝟘 ▷ a) ®⟨ l ⟩ v ∘ undefined ∷ B U.[ a ] / [B])
                → t ® v ∷Π 𝟘


  data _®_∷Σ : (t : U.Term 0) (v : T.Term 0) → Set where
    Σᵣ : ∀ {t₁ t₂ v₁ v₂ q l} → ([A] : ε ⊩⟨ l ⟩ A) → ([B] : ε ⊩⟨ l ⟩ B U.[ t₁ ])
       → ε ⊢ t ⇒* U.prod t₁ t₂ ∷ Σ q ▷ A ▹ B → v T.⇒* T.prod v₁ v₂ → t₁ ®⟨ l ⟩ v₁ ∷ A / [A]
       → t₂ ®⟨ l ⟩ v₂ ∷ B U.[ t₁ ] / [B] → t ® v ∷Σ



  _®⟨_⟩_∷_/_ : (t : U.Term 0) (l : TypeLevel) (v : T.Term 0) (A : U.Term 0) ([A] : ε ⊩⟨ l ⟩ A) → Set
  t ®⟨ l ⟩ v ∷ .(gen Ukind []) / Uᵣ x = t ® v ∷U
  t ®⟨ l ⟩ v ∷ A / ℕᵣ x = t ® v ∷ℕ
  t ®⟨ l ⟩ v ∷ A / Emptyᵣ x = t ® v ∷Empty
  t ®⟨ l ⟩ v ∷ A / Unitᵣ x = t ® v ∷Unit
  t ®⟨ l ⟩ v ∷ A / ne′ K D neK K≡K with noClosedNe neK
  ... | ()
  t ®⟨ l ⟩ v ∷ A / Bᵣ (BΠ p q) x = t ® v ∷Π p
  t ®⟨ l ⟩ v ∷ A / Bᵣ (BΣ q) x = t ® v ∷Σ
  t ®⟨ ¹ ⟩ v ∷ A / emb 0<1 [A] = t ®⟨ ⁰ ⟩ v ∷ A / [A]


wfTermEscapeℕ : t ® v ∷ℕ → ε ⊢ t ∷ ℕ
wfTermEscapeℕ (zeroᵣ x x₁) = redFirst*Term x
wfTermEscapeℕ (sucᵣ x x₁ t®v) = redFirst*Term x

wfTermEscapeU : t ® v ∷U → ε ⊢ t ∷ U
wfTermEscapeU (Uᵣ x x₁) = x

wfTermEscapeUnit : t ® v ∷Unit → ε ⊢ t ∷ Unit
wfTermEscapeUnit (starᵣ x x₁) = redFirst*Term x

wfTermEscapeEmpty : t ® v ∷Empty → ε ⊢ t ∷ Empty
wfTermEscapeEmpty (Emptyᵣ x x₁) = x

wfTermEscapeΠ : t ® v ∷Π p → ε ⊢ t ∷ Π p , _ ▷ _ ▹ _
wfTermEscapeΠ (Πωᵣ x) = {!!}
wfTermEscapeΠ (Π𝟘ᵣ x) = {!!}


®-back-closure : ∀ {l} ([A] : ε ⊩⟨ l ⟩ A) → t′ ®⟨ l ⟩ v ∷ A / [A] → ε ⊢ t ⇒* t′ ∷ A → t ®⟨ l ⟩ v ∷ A / [A]
®-back-closure (Uᵣ x) (Uᵣ x₁ x₂) t⇒t′ = Uᵣ (redFirst*Term t⇒t′) x₂
-- {!Uᵣ (redFirst*Term t⇒t′) x₂!}
®-back-closure (ℕᵣ [ ⊢A , ⊢B , D ]) (zeroᵣ t′⇒zero v⇒zero) t⇒t′ = zeroᵣ
  ((conv* t⇒t′ (subset* D)) ⇨∷* t′⇒zero)
  v⇒zero
®-back-closure {l = l} (ℕᵣ [ ⊢A , ⊢B , D ]) (sucᵣ t⇒suct′ v⇒sucv′ t′®v′) t⇒t′ = sucᵣ
  ((conv* t⇒t′ (subset* D)) ⇨∷* t⇒suct′)
  v⇒sucv′
  (®-back-closure {l = l} ((ℕᵣ ([ ⊢A , ⊢B , D ])))
        t′®v′
        (id (conv (wfTermEscapeℕ t′®v′) (sym (subset* D)))))
®-back-closure (Emptyᵣ [ ⊢A , ⊢B , D ]) (Emptyᵣ ⊢t:Empty v⇒undefined) t⇒t′ = Emptyᵣ
  (conv (redFirst*Term t⇒t′) (subset* D))
  v⇒undefined
®-back-closure (Unitᵣ [ ⊢A , ⊢B , D ]) (starᵣ t′⇒star v⇒star) t⇒t′ = starᵣ
  ((conv* t⇒t′ (subset* D)) ⇨∷* t′⇒star)
  v⇒star
®-back-closure (ne′ K D neK K≡K) t′®v t⇒t′ with noClosedNe neK
... | ()
®-back-closure (Bᵣ′ (BΠ 𝟘 q) F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Π𝟘ᵣ prop) t⇒t′ = Π𝟘ᵣ (λ ⊢a:A [B] → prop {!!} {!!})
®-back-closure (Bᵣ′ (BΠ ω q) F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext) (Πωᵣ prop) t⇒t′ = Πωᵣ λ ⊢a:A [A] [B] x → prop ⊢a:A [A] [B] (®-back-closure {!!} x (conv* t⇒t′ (subset* D)))
®-back-closure (Bᵣ′ (BΣ q) F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Σᵣ [A] [B] t′⇒p v⇒p′ p₁®p₁′ p₂®p₂′) t⇒t′ = Σᵣ
  {!!}
  {!D!}
  ({!t⇒t′!} ⇨∷* {!!})
  v⇒p′
  (®-back-closure {!!} p₁®p₁′ (id {!wfTermEscape!}))
  (®-back-closure {!!} p₂®p₂′ (id {!!}))
®-back-closure (emb 0<1 [A]) t′®v t⇒t′ = ®-back-closure [A] t′®v t⇒t′
