open import Graded.Modality
open import Definition.Typed.Variant

module Heap.Normalization
  {a} {M : Set a} (𝕄 : Modality M)
  (type-variant : Type-variant)
  (open Modality 𝕄)
  ⦃ _ : Has-nr M semiring-with-meet ⦄
  ⦃ _ : Has-factoring-nr M semiring-with-meet ⦄
  where

open Type-variant type-variant

open import Tools.Bool
open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum hiding (id)

open import Heap.Options

private
  opts : Options
  opts = not-tracking-and-ℕ-fullred-if false

open import Heap.Reduction 𝕄 type-variant opts
open import Heap.Reduction.Properties 𝕄 type-variant opts
open import Heap.Untyped 𝕄 type-variant
open import Heap.Untyped.Properties 𝕄 type-variant

open import Definition.Untyped M hiding (head)
open import Definition.Untyped.Properties M

private variable
  m n n′ : Nat

opaque mutual

  normalize-var : (H : Heap m) (x : Fin m)
                → ∃₄ λ n t (E′ : Env m n) S → Normal t
                  × ⟨ H , var x , id , ε ⟩ ⇒ₙ* ⟨ H , t , E′ , S ⟩
  normalize-var (H ∙ (p , t , E)) y0 =
    case normalize H t E ε of λ
      (_ , t′ , E′ , S , n , d) →
    _ , t′ , step E′ , wk1ˢ S , n
      , varₕ′ here ⇨ wk1-⇒ₙ* d

  normalize-var (H ∙ c) (y +1) =
    case normalize-var H y of λ
      (_ , t , E , S , n , d) →
    _ , t , step E , wk1ˢ S , n
      , var-env-⇒ₙ* (wk1-⇒ₙ* d) refl n

  normalize : (H : Heap m) (t : Term n) (E : Env m n) (S : Stack m)
            → ∃₄ λ n′ t′ (E′ : Env m n′) (S′ : Stack m) → Normal t′ ×
              ⟨ H , t , E , S ⟩ ⇒ₙ* ⟨ H , t′ , E′ , S′ ⟩
  normalize H (var x) E S =
    case normalize-var H (wkVar E x) of λ
      (_ , t , E′ , S′ , n , d) →
    _ , t , E′ , S′ ++ S , n
      , ++-⇒ₙ* S (var-env-⇒ₙ* d refl n)
  normalize H (lam p t) E S =
    _ , lam p t , E , S , val lamᵥ , id
  normalize H (t ∘⟨ p ⟩ u) E S =
    case normalize H t E (∘ₑ p u E ∙ S) of λ
      (_ , _ , _ , _ , n , d) →
    _ , _ , _ , _ , n , appₕ ⇨ d
  normalize H (prod s p t u) E S =
    _ , prod s p t u , E , S , val prodᵥ , id
  normalize H (fst p t) E S =
    case normalize H t E (fstₑ p ∙ S) of λ
      (_ , _ , _ , _ , n , d) →
    _ , _ , _ , _ , n , fstₕ ⇨ d
  normalize H (snd p t) E S =
    case normalize H t E (sndₑ p ∙ S) of λ
      (_ , _ , _ , _ , n , d) →
    _ , _ , _ , _ , n , sndₕ ⇨ d
  normalize H (prodrec r p q A t u) E S =
    case normalize H t E (prodrecₑ r p q A u E ∙ S) of λ
      (_ , _ , _ , _ , n , d) →
    _ , _ , _ , _ , n , prodrecₕ ⇨ d
  normalize H (star s) E S =
    _ , star s , E , S , val starᵥ , id
  normalize H (unitrec p q A t u) E S =
    case Unitʷ-η? of λ where
      (yes η) →
        _ , unitrec p q A t u , E , S , unitrec-ηₙ η , id
      (no no-η) →
        case normalize H t E (unitrecₑ p q A u E ∙ S) of λ
          (_ , _ , _ , _ , n , d) →
        _ , _ , _ , _ , n , unitrecₕ no-η ⇨ d
  normalize H zero E S =
    _ , zero , E , S , val zeroᵥ , id
  normalize H (suc t) E S =
    _ , suc t , E , S , val sucᵥ , id
  normalize H (natrec p q r A z s n) E S =
    case normalize H n E (natrecₑ p q r A z s E ∙ S) of λ
      (_ , _ , _ , _ , n , d) →
    _ , _ , _ , _ , n , (natrecₕ ⇨ d)
  normalize H (emptyrec p A t) E S =
    _ , _ , _ , _ , emptyrecₙ , id
  normalize H rfl E S =
    _ , rfl , E , S , val rflᵥ , id
  normalize H (J p q A t B u v w) E S =
    case normalize H w E (Jₑ p q A t B u v E ∙ S) of λ
      (_ , _ , _ , _ , n , d) →
    _ , _ , _ , _ , n , Jₕ ⇨ d
  normalize H (K p A t B u v) E S =
    case normalize H v E (Kₑ p A t B u E ∙ S) of λ
      (_ , _ , _ , _ , n , d) →
    _ , _ , _ , _ , n , Kₕ ⇨ d
  normalize H ([]-cong s A t u v) E S =
    case normalize H v E ([]-congₑ s A t u E ∙ S) of λ
      (_ , _ , _ , _ , n , d) →
    _ , _ , _ , _ , n , []-congₕ ⇨ d
  normalize H U E S =
    _ , U , E , S , val Uᵥ , id
  normalize H ℕ E S =
    _ , ℕ , E , S , val ℕᵥ , id
  normalize H Empty E S =
    _ , Empty , E , S , val Emptyᵥ , id
  normalize H (Unit s) E S =
    _ , Unit s , E , S , val Unitᵥ , id
  normalize H (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B) E S =
    _ , ΠΣ⟨ b ⟩ p , q ▷ A ▹ B , E , S , val ΠΣᵥ , id
  normalize H (Id A t u) E S =
    _ , Id A t u , E , S , val Idᵥ , id
