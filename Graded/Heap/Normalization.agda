------------------------------------------------------------------------
-- A normalization procedure for evaluating states to normal form.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode
open import Graded.Usage.Restrictions
open import Definition.Typed.Variant
open import Graded.Usage.Restrictions.Natrec

module Graded.Heap.Normalization
  {a b} {M : Set a} {Mode : Set b}
  {𝕄 : Modality M}
  {𝐌 : IsMode Mode 𝕄}
  (type-variant : Type-variant)
  (UR : Usage-restrictions 𝕄 𝐌)
  (open Usage-restrictions UR)
  (factoring-nr :
    ⦃ has-nr : Nr-available ⦄ →
    Is-factoring-nr M (Natrec-mode-Has-nr 𝕄 has-nr))
  where

open Type-variant type-variant
open Modality 𝕄

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum

open import Graded.Heap.Reduction type-variant UR factoring-nr
open import Graded.Heap.Reduction.Properties type-variant UR factoring-nr
open import Graded.Heap.Untyped type-variant UR factoring-nr
open import Graded.Heap.Untyped.Properties type-variant UR factoring-nr

open import Definition.Untyped M hiding (head)
open import Definition.Untyped.Names-below M as B using (No-names)

private variable
  k m n n′ : Nat

opaque mutual

  -- Normalization of states with variables in head position

  normalize-var :
    (H : Heap k m) → No-namesʰ H → (x : Fin m) →
    ∃₄ λ n t (ρ′ : Wk m n) S →
    Normal ⟨ H , t , ρ′ , S ⟩ ×
    ⟨ H , var x , id , ε ⟩ ⇢ₑ* ⟨ H , t , ρ′ , S ⟩
  normalize-var ε _ ()

  normalize-var (H ∙ (p , t , ρ)) (H-nn ∙ t-nn) y0 =
    case normalize H t ρ ε H-nn t-nn of λ
      (_ , t′ , ρ′ , S , n , d) →
    _ , t′ , step ρ′ , wk1ˢ S , wk1-Normal n
      , var here ⇨ wk1-⇢ₑ* d

  normalize-var (H ∙ c) (nn ∙ _) (y +1) =
    case normalize-var H nn y of λ
      (_ , t , ρ , S , n , d) →
    case wk1-Normal n of λ
      n′ →
    case var-env-⇢ₑ* (wk1-⇢ₑ* d) refl n′ of λ where
      (inj₁ d′) →
        _ , t , step ρ , wk1ˢ S , n′ , d′
      (inj₂ (refl , s≡s′)) →
        case State-injectivity s≡s′ of λ {
          (_ , refl , refl , _) →
        case n′ of λ where
          (var ¬d) → _ , var (y +1) , id , ε , var ¬d , id
          (val ()) }


  normalize-var (H ∙●) _ y0 =
    _ , var x0 , id  , ε , var here , id

  normalize-var (H ∙●) (nn ∙●) (y +1) =
    case normalize-var H nn y of λ
      (_ , t , ρ , S , n , d) →
    case wk1●-Normal n of λ
      n′ →
    case var-env-⇢ₑ* (wk1●-⇢ₑ* d) refl n′ of λ where
      (inj₁ d′) →
        _ , t , step ρ , wk1ˢ S , n′ , d′
      (inj₂ (refl , s≡s′)) →
        case State-injectivity s≡s′ of λ {
          (_ , refl , refl , _) →
        case n′ of λ where
          (var d)  → _ , var (y +1) , id , ε , var d , id
          (val ()) }

  -- Normalization of states

  normalize : (H : Heap k m) (t : Term n) (ρ : Wk m n) (S : Stack m)
            → No-namesʰ H → No-names t
            → ∃₄ λ n′ t′ (ρ′ : Wk m n′) (S′ : Stack m) → Normal ⟨ H , t′ , ρ′ , S′ ⟩ ×
              ⟨ H , t , ρ , S ⟩ ⇢ₑ* ⟨ H , t′ , ρ′ , S′ ⟩
  normalize _ (defn _) _ _ _ (B.defn ())
  normalize H (var x) ρ S nn _ =
    case normalize-var H nn (wkVar ρ x) of λ
      (_ , t , ρ′ , S′ , n , d) →
    case var-env-⇢ₑ* d refl n of λ where
      (inj₁ d′) →
        _ , t , ρ′ , S′ ++ S , Normal-stack n
          , ++-⇢ₑ* S d′
      (inj₂ (refl , s≡s′)) →
        case State-injectivity s≡s′ of λ {
          (_ , refl , refl , refl) →
        case n of λ where
          (var ¬d) → _ , var x , ρ , S , var ¬d , id
          (val ()) }
  normalize H Level ρ S _ _ =
    _ , Level , ρ , S , val Levelᵥ , id
  normalize h zeroᵘ ρ s _ _ =
    _ , zeroᵘ , ρ , s , val zeroᵘᵥ , id
  normalize h (sucᵘ t) ρ s _ _ =
    _ , sucᵘ t , ρ , s , val sucᵘᵥ , id
  normalize h (t supᵘ u) ρ s _ _ =
    _ , t supᵘ u , ρ , s , sup , id
  normalize H (Lift t A) ρ S _ _ =
    _ , Lift t A , ρ , S , val Liftᵥ , id
  normalize H (lift t) ρ S _ _ =
    _ , lift t , ρ , S , val liftᵥ , id
  normalize H (lower t) ρ S nn (B.lower t-nn) =
    case normalize H t ρ (lowerₑ ∙ S) nn t-nn of λ
      (_ , _ , _ , _ , n , d) →
    _ , _ , _ , _ , n , ⇒ₑ lowerₕ ⇨ d
  normalize H (lam p t) ρ S _ _ =
    _ , lam p t , ρ , S , val lamᵥ , id
  normalize H (t ∘⟨ p ⟩ u) ρ S H-nn (B.app t-nn _) =
    case normalize H t ρ (∘ₑ p u ρ ∙ S) H-nn t-nn of λ
      (_ , _ , _ , _ , n , d) →
    _ , _ , _ , _ , n , ⇒ₑ appₕ ⇨ d
  normalize H (prod s p t u) ρ S _ _ =
    _ , prod s p t u , ρ , S , val prodᵥ , id
  normalize H (fst p t) ρ S H-nn (B.fst t-nn) =
    case normalize H t ρ (fstₑ p ∙ S) H-nn t-nn of λ
      (_ , _ , _ , _ , n , d) →
    _ , _ , _ , _ , n , ⇒ₑ fstₕ ⇨ d
  normalize H (snd p t) ρ S H-nn (B.snd t-nn) =
    case normalize H t ρ (sndₑ p ∙ S) H-nn t-nn of λ
      (_ , _ , _ , _ , n , d) →
    _ , _ , _ , _ , n , ⇒ₑ sndₕ ⇨ d
  normalize H (prodrec r p q A t u) ρ S H-nn (B.prodrec _ t-nn _) =
    case normalize H t ρ (prodrecₑ r p q A u ρ ∙ S) H-nn t-nn of λ
      (_ , _ , _ , _ , n , d) →
    _ , _ , _ , _ , n , ⇒ₑ prodrecₕ ⇨ d
  normalize H (star s) ρ S _ _ =
    _ , star s , ρ , S , val starᵥ , id
  normalize H (unitrec p q A t u) ρ S H-nn (B.unitrec _ t-nn _) =
    case Unitʷ-η? of λ where
      (yes η) →
        _ , unitrec p q A t u , ρ , S , val (unitrec-ηᵥ η) , id
      (no no-η) →
        case normalize H t ρ (unitrecₑ p q A u ρ ∙ S) H-nn t-nn of λ
          (_ , _ , _ , _ , n , d) →
        _ , _ , _ , _ , n , ⇒ₑ unitrecₕ no-η ⇨ d
  normalize H zero ρ S _ _ =
    _ , zero , ρ , S , val zeroᵥ , id
  normalize H (suc t) ρ S _ _ =
    _ , suc t , ρ , S , val sucᵥ , id
  normalize H (natrec p q r A z s n) ρ S H-nn (B.natrec _ _ _ n-nn) =
    case normalize H n ρ (natrecₑ p q r A z s ρ ∙ S) H-nn n-nn of λ
      (_ , _ , _ , _ , n , d) →
    _ , _ , _ , _ , n , ⇒ₑ natrecₕ ⇨ d
  normalize H (emptyrec p A t) ρ S H-nn (B.emptyrec _ t-nn) =
    case normalize H t ρ (emptyrecₑ p A ρ ∙ S) H-nn t-nn of λ
      (_ , _ , _ , _ , n , d) →
    _ , _ , _ , _ , n , ⇒ₑ emptyrecₕ ⇨ d
  normalize H rfl ρ S _ _ =
    _ , rfl , ρ , S , val rflᵥ , id
  normalize H (J p q A t B u v w) ρ S H-nn (B.J _ _ _ _ _ w-nn) =
    case normalize H w ρ (Jₑ p q A t B u v ρ ∙ S) H-nn w-nn of λ
      (_ , _ , _ , _ , n , d) →
    _ , _ , _ , _ , n , ⇒ₑ Jₕ ⇨ d
  normalize H (K p A t B u v) ρ S H-nn (B.K _ _ _ _ v-nn) =
    case normalize H v ρ (Kₑ p A t B u ρ ∙ S) H-nn v-nn of λ
      (_ , _ , _ , _ , n , d) →
    _ , _ , _ , _ , n , ⇒ₑ Kₕ ⇨ d
  normalize H ([]-cong s l A t u v) ρ S H-nn (B.[]-cong _ _ _ _ v-nn) =
    case normalize H v ρ ([]-congₑ s l A t u ρ ∙ S) H-nn v-nn of λ
      (_ , _ , _ , _ , n , d) →
    _ , _ , _ , _ , n , ⇒ₑ []-congₕ ⇨ d
  normalize H (U l) ρ S _ _ =
    _ , U l , ρ , S , val Uᵥ , id
  normalize H ℕ ρ S _ _ =
    _ , ℕ , ρ , S , val ℕᵥ , id
  normalize H Empty ρ S _ _ =
    _ , Empty , ρ , S , val Emptyᵥ , id
  normalize H (Unit s) ρ S _ _ =
    _ , Unit s , ρ , S , val Unitᵥ , id
  normalize H (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B) ρ S _ _ =
    _ , ΠΣ⟨ b ⟩ p , q ▷ A ▹ B , ρ , S , val ΠΣᵥ , id
  normalize H (Id A t u) ρ S _ _ =
    _ , Id A t u , ρ , S , val Idᵥ , id

opaque

  -- A version of normalize that acts on states

  normalizeₛ :
    (s : State k m n) → No-namesₛ′ s →
    ∃₂ λ n′ (s′ : State k m n′) → Normal s′ × s ⇢ₑ* s′
  normalizeₛ ⟨ H , t , ρ , S ⟩ (H-nn , t-nn) =
    case normalize H t ρ S H-nn t-nn of λ
      (_ , t′ , ρ′ , S′ , n , d) →
    _ , _ , n , d
