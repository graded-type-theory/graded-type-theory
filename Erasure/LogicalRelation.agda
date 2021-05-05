open import Definition.Modality.Erasure

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Weakening

module Erasure.LogicalRelation {{eqrel : EqRelSet Erasure}} where
open EqRelSet {{...}}



open import Definition.Untyped Erasure as U hiding (_∷_)
open import Definition.Untyped.Properties Erasure as UP
open import Definition.Typed Erasure as Ty
open import Definition.Typed.Properties Erasure
open import Definition.Typed.RedSteps Erasure as RedSteps
open import Erasure.Target as T hiding (_⇒*_)
open import Erasure.Target.Properties as TP
open import Erasure.Extraction

open import Definition.LogicalRelation Erasure
open import Definition.LogicalRelation.Properties.Escape Erasure

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as P



private
  variable
    n : Nat
    t t′ u A B : U.Term n
    v v′ : T.Term n
    p : Erasure

data _®_∷U (t : U.Term 0) (v : T.Term 0) : Set where
  Uᵣ : ε ⊢ t ∷ U → v T.⇒* undefined → t ® v ∷U

data _®_∷ℕ (t : U.Term 0) (v : T.Term 0) : Set where
  zeroᵣ : ε ⊢ t ⇒* U.zero ∷ ℕ → v T.⇒* T.zero → t ® v ∷ℕ
  sucᵣ : ε ⊢ t ⇒* U.suc t′ ∷ ℕ → v T.⇒* T.suc v′ → t′ ® v′ ∷ℕ → t ® v ∷ℕ

data _®_∷Empty (t : U.Term 0) (v : T.Term 0) : Set where
  Emptyᵣ : ε ⊢ t ∷ Empty → v T.⇒* undefined → t ® v ∷Empty

data _®_∷Unit (t : U.Term 0) (v : T.Term 0) : Set where
  starᵣ : ε ⊢ t ⇒* U.star ∷ Unit → v T.⇒* T.star → t ® v ∷Unit

mutual

{-
  data _®⟨_⟩_∷Π⟨_▷_⟩_ (t : U.Term 0) (l : TypeLevel) (v : T.Term 0)
    {A} ([A] : ε ⊩⟨ l ⟩ A)
    {B} ([B] : ∀{a} → ε ⊩⟨ l ⟩ a ∷ A / [A] → ε ⊩⟨ l ⟩ B U.[ a ])
    : (p : Erasure) → Set where

    Πωᵣ : (∀ {a w} ([a] : ε ⊩⟨ l ⟩ a ∷ A / [A])
                   → a ®⟨ l ⟩ w ∷ A / [A]
                   → (t ∘ ω ▷ a) ®⟨ l ⟩ v ∘ w ∷ B U.[ a ] / [B] [a])
        → t ®⟨ l ⟩ v ∷Π⟨ [A] ▷ [B] ⟩  ω

    Π𝟘ᵣ : (∀ {a}   ([a] : ε ⊩⟨ l ⟩ a ∷ A / [A])
                   → (t ∘ 𝟘 ▷ a) ®⟨ l ⟩ v ∘ undefined ∷ B U.[ a ] / [B] [a])
        → t ®⟨ l ⟩ v ∷Π⟨ [A] ▷ [B] ⟩ 𝟘
-}


  _®⟨_⟩_∷Π⟨_▷_⟩_ : ∀
    (t : U.Term 0) (l : TypeLevel) (v : T.Term 0)
    {A} ([A] : ε ⊩⟨ l ⟩ A)
    {B} ([B] : ∀{a} → ε ⊩⟨ l ⟩ a ∷ A / [A] → ε ⊩⟨ l ⟩ U.wk (lift id) B U.[ a ])
    (p : Erasure) → Set

  _®⟨_⟩_∷Π⟨_▷_⟩_ t l v {A} [A] {B} [B] ω =
      ∀ {a w} ([a] : ε ⊩⟨ l ⟩ a ∷ A / [A])
                     → a ®⟨ l ⟩ w ∷ A / [A]
                     → (t ∘ ω ▷ a) ®⟨ l ⟩ v ∘ w ∷ U.wk (lift id) B U.[ a ] / [B] [a]
  _®⟨_⟩_∷Π⟨_▷_⟩_ t l v {A} [A] {B} [B] 𝟘 =
      ∀ {a}   ([a] : ε ⊩⟨ l ⟩ a ∷ A / [A])
                     → (t ∘ 𝟘 ▷ a) ®⟨ l ⟩ v ∘ undefined ∷ U.wk (lift id) B U.[ a ] / [B] [a]

{-
  data _®_∷Σ : (t : U.Term 0) (v : T.Term 0) → Set where
    Σᵣ : ∀ {t₁ t₂ v₁ v₂ q l} → ([A] : ε ⊩⟨ l ⟩ A) → ([B] : ε ⊩⟨ l ⟩ B U.[ t₁ ])
       → ε ⊢ t ⇒* U.prod t₁ t₂ ∷ Σ q ▷ A ▹ B → v T.⇒* T.prod v₁ v₂ → t₁ ®⟨ l ⟩ v₁ ∷ A / [A]
       → t₂ ®⟨ l ⟩ v₂ ∷ B U.[ t₁ ] / [B] → t ® v ∷Σ
-}


  _®⟨_⟩_∷_/_ : (t : U.Term 0) (l : TypeLevel) (v : T.Term 0) (A : U.Term 0) ([A] : ε ⊩⟨ l ⟩ A) → Set
  t ®⟨ l ⟩ v ∷ .(gen Ukind []) / Uᵣ x = t ® v ∷U
  t ®⟨ l ⟩ v ∷ A / ℕᵣ x = t ® v ∷ℕ
  t ®⟨ l ⟩ v ∷ A / Emptyᵣ x = t ® v ∷Empty
  t ®⟨ l ⟩ v ∷ A / Unitᵣ x = t ® v ∷Unit
  t ®⟨ l ⟩ v ∷ A / ne′ K D neK K≡K with noClosedNe neK
  ... | ()
  t ®⟨ l ⟩ v ∷ A / Bᵣ′ (BΠ ω q) F G D ⊢F ⊢G A≡A [F] [G] G-ext =
      ∀ {a w} ([a] : ε ⊩⟨ l ⟩ a ∷ U.wk id F / [F] id ε)
                     → a ®⟨ l ⟩ w ∷ U.wk id F / [F] id ε
                     → (t ∘ ω ▷ a) ®⟨ l ⟩ v ∘ w ∷ U.wk (lift id) G U.[ a ] / [G] id ε [a]
  t ®⟨ l ⟩ v ∷ A / Bᵣ′ (BΠ 𝟘 q) F G D ⊢F ⊢G A≡A [F] [G] G-ext =
      ∀ {a} ([a] : ε ⊩⟨ l ⟩ a ∷ U.wk id F / [F] id ε)
                     → (t ∘ 𝟘 ▷ a) ®⟨ l ⟩ v ∘ undefined ∷ U.wk (lift id) G U.[ a ] / [G] id ε [a]

    -- _®⟨_⟩_∷Π⟨_▷_⟩_ t l v ( [F] id ε ) {G} (λ{a} [a] → [G] id ε [a]) p
--    _®⟨_⟩_∷Π⟨_▷_⟩_ t l v ( [F] id ε ) {G} (λ{a} [a] →  P.subst (λ □ → ε ⊩⟨ l ⟩ (□ U.[ a ])) {x = U.wk (lift id) G} {y = G} (UP.wk-lift-id G) ([G] id ε [a]) ) p
    -- t ®⟨ l ⟩ v ∷Π⟨ [F] id ε ▷ (λ{a} [a] →  P.subst (λ □ → ε ⊩⟨ l ⟩ (□ U.[ a ])) {x = U.wk (lift id) G} {y = G} (UP.wk-lift-id G) ([G] id ε [a]) ) ⟩ p
  t ®⟨ l ⟩ v ∷ A / Bᵣ (BΣ q) x = {! t ® v ∷Σ !}
  t ®⟨ ¹ ⟩ v ∷ A / emb 0<1 [A] = t ®⟨ ⁰ ⟩ v ∷ A / [A]

{-
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

wfTermEscape : ∀ {l} → ([A] : ε ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v ∷ A / [A] → ε ⊢ t ∷ A
wfTermEscape (Uᵣ x) t®v = wfTermEscapeU t®v
wfTermEscape (ℕᵣ [ ⊢A , ⊢B , D ]) t®v = conv (wfTermEscapeℕ t®v) (sym (subset* D))
wfTermEscape (Emptyᵣ [ ⊢A , ⊢B , D ]) t®v = conv (wfTermEscapeEmpty t®v) (sym (subset* D))
wfTermEscape (Unitᵣ [ ⊢A , ⊢B , D ]) t®v = conv (wfTermEscapeUnit t®v) (sym (subset* D))
wfTermEscape (ne′ K D neK K≡K) t®v with noClosedNe neK
... | ()
wfTermEscape (Bᵣ (BΠ p q) x) t®v = {!!}
wfTermEscape (Bᵣ (BΣ p) x) t®v = {!!}
wfTermEscape (emb 0<1 [A]) t®v = wfTermEscape [A] t®v

-- Relation is preserved by reduction backwards

®-back-closureˡ : ∀ {l} ([A] : ε ⊩⟨ l ⟩ A) → t′ ®⟨ l ⟩ v ∷ A / [A] → ε ⊢ t ⇒* t′ ∷ A → t ®⟨ l ⟩ v ∷ A / [A]
®-back-closureˡ (Uᵣ x) (Uᵣ x₁ x₂) t⇒t′ = Uᵣ (redFirst*Term t⇒t′) x₂
®-back-closureˡ (ℕᵣ [ ⊢A , ⊢B , D ]) (zeroᵣ t′⇒zero v⇒zero) t⇒t′ = zeroᵣ
  ((conv* t⇒t′ (subset* D)) ⇨∷* t′⇒zero)
  v⇒zero
®-back-closureˡ {l = l} (ℕᵣ [ ⊢A , ⊢B , D ]) (sucᵣ t⇒suct′ v⇒sucv′ t′®v′) t⇒t′ = sucᵣ
  ((conv* t⇒t′ (subset* D)) ⇨∷* t⇒suct′)
  v⇒sucv′
  (®-back-closureˡ {l = l} ((ℕᵣ ([ ⊢A , ⊢B , D ])))
                  t′®v′
                  (id (conv (wfTermEscapeℕ t′®v′) (sym (subset* D)))))
®-back-closureˡ (Emptyᵣ [ ⊢A , ⊢B , D ]) (Emptyᵣ ⊢t:Empty v⇒undefined) t⇒t′ = Emptyᵣ
  (conv (redFirst*Term t⇒t′) (subset* D))
  v⇒undefined
®-back-closureˡ (Unitᵣ [ ⊢A , ⊢B , D ]) (starᵣ t′⇒star v⇒star) t⇒t′ = starᵣ
  ((conv* t⇒t′ (subset* D)) ⇨∷* t′⇒star)
  v⇒star
®-back-closureˡ (ne′ K D neK K≡K) t′®v t⇒t′ with noClosedNe neK
... | ()
®-back-closureˡ (Bᵣ′ (BΠ 𝟘 q) F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext) (Π𝟘ᵣ prop) t⇒t′ = Π𝟘ᵣ λ [B] → ®-back-closureˡ [B] (prop [B]) (RedSteps.app-subst* (conv* t⇒t′ (subset* D)) {!!})
®-back-closureˡ {A} (Bᵣ′ (BΠ ω q) F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext) (Πωᵣ {A₁} prop) t⇒t′ = Πωᵣ (λ [A] [B] x → ®-back-closureˡ [B] (prop [A] [B] x) (RedSteps.app-subst* (conv* t⇒t′ (subset* D)) {!!}))
®-back-closureˡ (Bᵣ′ (BΣ q) F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext) (Σᵣ [A] [B] t′⇒p v⇒p′ p₁®p₁′ p₂®p₂′) t⇒t′ = Σᵣ
  [A]
  [B]
  (conv* t⇒t′ {!subset* D!} ⇨∷* t′⇒p)
  v⇒p′
  (®-back-closureˡ [A] p₁®p₁′ (id (wfTermEscape [A] p₁®p₁′)))
  (®-back-closureˡ [B] p₂®p₂′ (id (wfTermEscape [B] p₂®p₂′)))
®-back-closureˡ (emb 0<1 [A]) t′®v t⇒t′ = ®-back-closureˡ [A] t′®v t⇒t′

®-back-closureʳ : ∀ {l} ([A] : ε ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v′ ∷ A / [A] → v T.⇒* v′ → t ®⟨ l ⟩ v ∷ A / [A]
®-back-closureʳ (Uᵣ x) (Uᵣ ⊢t:U v′⇒undefined) v⇒v′ = Uᵣ ⊢t:U (red*concat v⇒v′ v′⇒undefined)
®-back-closureʳ (ℕᵣ x) (zeroᵣ t⇒zero v′⇒zero) v⇒v′ = zeroᵣ t⇒zero (red*concat v⇒v′ v′⇒zero)
®-back-closureʳ (ℕᵣ x) (sucᵣ t⇒suct′ v′⇒sucw t′®w) v⇒v′ = sucᵣ t⇒suct′ (red*concat v⇒v′ v′⇒sucw) t′®w
®-back-closureʳ (Emptyᵣ x) (Emptyᵣ ⊢t:Empty v′⇒undefined) v⇒v′ = Emptyᵣ ⊢t:Empty (red*concat v⇒v′ v′⇒undefined)
®-back-closureʳ (Unitᵣ x) (starᵣ t⇒star v′⇒star) v⇒v′ = starᵣ t⇒star (red*concat v⇒v′ v′⇒star)
®-back-closureʳ (ne′ K D neK K≡K) t®v′ v⇒v′ with noClosedNe neK
... | ()
®-back-closureʳ (Bᵣ′ (BΠ 𝟘 q) F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Π𝟘ᵣ {B} prop) v⇒v′ = Π𝟘ᵣ {B} λ [B] → ®-back-closureʳ [B] (prop [B]) (TP.app-subst* v⇒v′)
®-back-closureʳ (Bᵣ (BΠ ω q) x) (Πωᵣ {B = B} prop) v⇒v′ = Πωᵣ {B = B} (λ [A] [B] x₁ → ®-back-closureʳ [B] (prop [A] [B] x₁) (TP.app-subst* v⇒v′))
®-back-closureʳ (Bᵣ (BΣ q) x) (Σᵣ [A] [B] t⇒p v′⇒p′ p₁®p₁′ p₂®p₂′) v⇒v′ = Σᵣ [A] [B] t⇒p (red*concat v⇒v′ v′⇒p′) (®-back-closureʳ [A] p₁®p₁′ refl) (®-back-closureʳ [B] p₂®p₂′ refl)
®-back-closureʳ (emb 0<1 [A]) t®v′ v⇒v′ = ®-back-closureʳ [A] t®v′ v⇒v′

-- -}
-- -}
-- -}
-- -}
