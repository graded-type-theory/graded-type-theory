------------------------------------------------------------------------
-- A normalization procedure for evaluating states to normal form.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Variant

module Graded.Heap.Normalization
  {a} {M : Set a} {𝕄 : Modality M}
  (type-variant : Type-variant)
  (UR : Usage-restrictions 𝕄)
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
open import Tools.Relation
open import Tools.Sum hiding (id)

open import Graded.Heap.Reduction type-variant UR
open import Graded.Heap.Reduction.Properties type-variant UR
open import Graded.Heap.Untyped type-variant UR
open import Graded.Heap.Untyped.Properties type-variant UR

open import Definition.Untyped M hiding (head)

private variable
  k m n n′ : Nat

opaque mutual

  -- Normalization of states with variables in head position

  normalize-var : (H : Heap k m) (x : Fin m)
                → ∃₄ λ n t (ρ′ : Wk m n) S → Normal ⟨ H , t , ρ′ , S ⟩
                  × ⟨ H , var x , id , ε ⟩ ⇢ₑ* ⟨ H , t , ρ′ , S ⟩
  normalize-var (H ∙ (p , t , ρ)) y0 =
    case normalize H t ρ ε of λ
      (_ , t′ , ρ′ , S , n , d) →
    _ , t′ , step ρ′ , wk1ˢ S , wk1-Normal n
      , var here ⇨ wk1-⇢ₑ* d

  normalize-var (H ∙ c) (y +1) =
    case normalize-var H y of λ
      (_ , t , ρ , S , n , d) →
    case wk1-Normal n of λ
      n′ →
    case var-env-⇢ₑ* (wk1-⇢ₑ* d) refl n′ of λ where
      (inj₁ d′) →
        _ , t , step ρ , wk1ˢ S , n′ , d′
      (inj₂ (refl , s≡s′)) →
        case State-injectivity s≡s′ of λ {
          (_ , refl , refl , _) →
        case n′ of λ {
          (var ¬d) →
        _ , var (y +1) , id , ε , var ¬d , id }}


  normalize-var (H ∙●) y0 =
    _ , var x0 , id  , ε , var here , id

  normalize-var (H ∙●) (y +1) =
    case normalize-var H y of λ
      (_ , t , ρ , S , n , d) →
    case wk1●-Normal n of λ
      n′ →
    case var-env-⇢ₑ* (wk1●-⇢ₑ* d) refl n′ of λ where
      (inj₁ d′) →
        _ , t , step ρ , wk1ˢ S , n′ , d′
      (inj₂ (refl , s≡s′)) →
        case State-injectivity s≡s′ of λ {
          (_ , refl , refl , _) →
        case n′ of λ {
          (var d) →
        _ , var (y +1) , id , ε , var d , id }}

  -- Normalization of states

  normalize : (H : Heap k m) (t : Term n) (ρ : Wk m n) (S : Stack m)
            → ∃₄ λ n′ t′ (ρ′ : Wk m n′) (S′ : Stack m) → Normal ⟨ H , t′ , ρ′ , S′ ⟩ ×
              ⟨ H , t , ρ , S ⟩ ⇢ₑ* ⟨ H , t′ , ρ′ , S′ ⟩
  normalize H (var x) ρ S =
    case normalize-var H (wkVar ρ x) of λ
      (_ , t , ρ′ , S′ , n , d) →
    case var-env-⇢ₑ* d refl n of λ where
      (inj₁ d′) →
        _ , t , ρ′ , S′ ++ S , Normal-stack n
          , ++-⇢ₑ* S d′
      (inj₂ (refl , s≡s′)) →
        case State-injectivity s≡s′ of λ {
          (_ , refl , refl , refl) →
        case n of λ {
          (var ¬d) →
        _ , var x , ρ , S , var ¬d , id }}
  normalize H (lam p t) ρ S =
    _ , lam p t , ρ , S , val lamᵥ , id
  normalize H (t ∘⟨ p ⟩ u) ρ S =
    case normalize H t ρ (∘ₑ p u ρ ∙ S) of λ
      (_ , _ , _ , _ , n , d) →
    _ , _ , _ , _ , n , ⇒ₑ appₕ ⇨ d
  normalize H (prod s p t u) ρ S =
    _ , prod s p t u , ρ , S , val prodᵥ , id
  normalize H (fst p t) ρ S =
    case normalize H t ρ (fstₑ p ∙ S) of λ
      (_ , _ , _ , _ , n , d) →
    _ , _ , _ , _ , n , ⇒ₑ fstₕ ⇨ d
  normalize H (snd p t) ρ S =
    case normalize H t ρ (sndₑ p ∙ S) of λ
      (_ , _ , _ , _ , n , d) →
    _ , _ , _ , _ , n , ⇒ₑ sndₕ ⇨ d
  normalize H (prodrec r p q A t u) ρ S =
    case normalize H t ρ (prodrecₑ r p q A u ρ ∙ S) of λ
      (_ , _ , _ , _ , n , d) →
    _ , _ , _ , _ , n , ⇒ₑ prodrecₕ ⇨ d
  normalize H (star s l) ρ S =
    _ , star s l , ρ , S , val starᵥ , id
  normalize H (unitrec l p q A t u) ρ S =
    case Unitʷ-η? of λ where
      (yes η) →
        _ , unitrec l p q A t u , ρ , S , val (unitrec-ηᵥ η) , id
      (no no-η) →
        case normalize H t ρ (unitrecₑ l p q A u ρ ∙ S) of λ
          (_ , _ , _ , _ , n , d) →
        _ , _ , _ , _ , n , ⇒ₑ unitrecₕ no-η ⇨ d
  normalize H zero ρ S =
    _ , zero , ρ , S , val zeroᵥ , id
  normalize H (suc t) ρ S =
    _ , suc t , ρ , S , val sucᵥ , id
  normalize H (natrec p q r A z s n) ρ S =
    case normalize H n ρ (natrecₑ p q r A z s ρ ∙ S) of λ
      (_ , _ , _ , _ , n , d) →
    _ , _ , _ , _ , n , ⇒ₑ natrecₕ ⇨ d
  normalize H (emptyrec p A t) ρ S =
    case normalize H t ρ (emptyrecₑ p A ρ ∙ S) of λ
      (_ , _ , _ , _ , n , d) →
    _ , _ , _ , _ , n , ⇒ₑ emptyrecₕ ⇨ d
  normalize H rfl ρ S =
    _ , rfl , ρ , S , val rflᵥ , id
  normalize H (J p q A t B u v w) ρ S =
    case normalize H w ρ (Jₑ p q A t B u v ρ ∙ S) of λ
      (_ , _ , _ , _ , n , d) →
    _ , _ , _ , _ , n , ⇒ₑ Jₕ ⇨ d
  normalize H (K p A t B u v) ρ S =
    case normalize H v ρ (Kₑ p A t B u ρ ∙ S) of λ
      (_ , _ , _ , _ , n , d) →
    _ , _ , _ , _ , n , ⇒ₑ Kₕ ⇨ d
  normalize H ([]-cong s A t u v) ρ S =
    case normalize H v ρ ([]-congₑ s A t u ρ ∙ S) of λ
      (_ , _ , _ , _ , n , d) →
    _ , _ , _ , _ , n , ⇒ₑ []-congₕ ⇨ d
  normalize H (U l) ρ S =
    _ , U l , ρ , S , val Uᵥ , id
  normalize H ℕ ρ S =
    _ , ℕ , ρ , S , val ℕᵥ , id
  normalize H Empty ρ S =
    _ , Empty , ρ , S , val Emptyᵥ , id
  normalize H (Unit s l) ρ S =
    _ , Unit s l , ρ , S , val Unitᵥ , id
  normalize H (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B) ρ S =
    _ , ΠΣ⟨ b ⟩ p , q ▷ A ▹ B , ρ , S , val ΠΣᵥ , id
  normalize H (Id A t u) ρ S =
    _ , Id A t u , ρ , S , val Idᵥ , id

opaque

  -- A version of normalize that acts on states

  normalizeₛ : (s : State k m n)
             → ∃₂ λ n′ (s′ : State k m n′) → Normal s′ × s ⇢ₑ* s′
  normalizeₛ ⟨ H , t , ρ , S ⟩ =
    case normalize H t ρ S of λ
      (_ , t′ , ρ′ , S′ , n , d) →
    _ , _ , n , d
