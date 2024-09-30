------------------------------------------------------------------------
-- A resource aware heap semantics. The reduction relation.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Graded.Heap.Options
open import Definition.Typed.Variant

module Graded.Heap.Reduction
  {a} {M : Set a}
  {𝕄 : Modality M}
  (type-variant : Type-variant)
  (UR : Usage-restrictions 𝕄)
  (opts : Options)
  (open Modality 𝕄)
  ⦃ _ : Has-nr M semiring-with-meet ⦄
  ⦃ _ : Has-factoring-nr M semiring-with-meet ⦄
  where

open import Tools.Fin
open import Tools.Nat hiding (_+_)
open import Tools.Product
open import Tools.Relation

open import Definition.Untyped M
open import Graded.Modality.Nr-instances
open import Graded.Heap.Untyped type-variant UR

open Options opts
open Type-variant type-variant

private variable
  m m′ n n′ k : Nat
  H H′ : Heap _ _
  ρ ρ′ : Wk _ _
  t t′ u v w z s A B t₁ t₂ : Term _
  x : Fin _
  S S′ : Stack _
  p q r : M
  s′ : Strength
  l : Universe-level

-- The reduction relation is divided into three different relations:
-- _⇒ₙ_, _⇒ᵥ_ and _⇒ₛ_
-- They describe different parts of the evaluation and therefore have
-- slightly different properties.

-- The relation _⇒ₙ_ evaluates terms to normal form by variable lookups
-- and putting eliminators on the stack.
-- See Graded.Heap.Normalization

-- There are two mutually exclusive variable rules depending on if resource
-- tracking should be used or not (specified by Options).

infix 28 _⇒ₙ_

data _⇒ₙ_ {k m n} : State k m n → State k m n′ → Set a where
  varₕ : ⦃ tr : Track-resources ⦄
       → H ⊢ wkVar ρ x ↦[ ∣ S ∣ ] (t , ρ′) ⨾ H′ →
          ⟨ H  , var x , ρ  , S ⟩
       ⇒ₙ ⟨ H′ , t     , ρ′ , S ⟩
  varₕ′ : ⦃ tr : ¬Track-resources ⦄
        → H ⊢ wkVar ρ x ↦ (t , ρ′) →
          ⟨ H  , var x , ρ  , S ⟩
        ⇒ₙ ⟨ H , t     , ρ′ , S  ⟩
  appₕ : ⟨ H , t ∘⟨ p ⟩ u , ρ , S            ⟩
       ⇒ₙ ⟨ H , t         , ρ , ∘ₑ p u ρ ∙ S ⟩
  fstₕ : ⟨ H , fst p t , ρ , S          ⟩
       ⇒ₙ ⟨ H , t       , ρ , fstₑ p ∙ S ⟩
  sndₕ : ⟨ H , snd p t , ρ , S          ⟩
       ⇒ₙ ⟨ H , t       , ρ , sndₑ p ∙ S ⟩
  prodrecₕ : ⟨ H , prodrec r p q A t u , ρ , S ⟩
           ⇒ₙ ⟨ H , t                   , ρ , prodrecₑ r p q A u ρ ∙ S ⟩
  natrecₕ : ⟨ H , natrec p q r A z s t , ρ , S                         ⟩
          ⇒ₙ ⟨ H , t                    , ρ , natrecₑ p q r A z s ρ ∙ S ⟩
  unitrecₕ : ¬ Unitʷ-η
           →  ⟨ H , unitrec l p q A t u , ρ ,                        S ⟩
           ⇒ₙ ⟨ H ,                 t   , ρ , unitrecₑ l p q A u ρ ∙ S ⟩
  emptyrecₕ : ⟨ H , emptyrec p A t , ρ , S ⟩
            ⇒ₙ ⟨ H , t , ρ , emptyrecₑ p A ρ ∙ S ⟩
  Jₕ : ⟨ H , J p q A t B u v w , ρ , S ⟩
     ⇒ₙ ⟨ H , w , ρ , Jₑ p q A t B u v ρ ∙ S ⟩
  Kₕ : ⟨ H , K p A t B u v , ρ , S ⟩
     ⇒ₙ ⟨ H , v , ρ , Kₑ p A t B u ρ ∙ S ⟩
  []-congₕ : ⟨ H , []-cong s′ A t u v , ρ , S ⟩
           ⇒ₙ ⟨ H , v , ρ , []-congₑ s′ A t u ρ ∙ S ⟩

-- Reflexive, transistive closure of the reduction relation

infix 28 _⇒ₙ*_

data _⇒ₙ*_ (s : State k m n) : (s′ : State k m n′) → Set a where
  id : s ⇒ₙ* s
  _⇨_ : ∀ {n″} {s′ : State k m n′} {s″ : State k m n″}
      → s ⇒ₙ s′ → s′ ⇒ₙ* s″ → s ⇒ₙ* s″

-- The relation _⇒ᵥ_ evaluates states with values in head position and a
-- matching eliminator on the top of the stack.

infix 28 _⇒ᵥ_

data _⇒ᵥ_ {k m n} : State k m n → State k m′ n′ → Set a where
  lamₕ : ⟨ H                        , lam p t , ρ           , ∘ₑ p u ρ′ ∙ S ⟩
       ⇒ᵥ ⟨ H ∙ (∣ S ∣ · p , u , ρ′) , t       , lift ρ      , wk1ˢ S        ⟩
  prodˢₕ₁ : ⟨ H , prodˢ p t₁ t₂ , ρ , fstₑ p ∙ S ⟩
          ⇒ᵥ ⟨ H , t₁           , ρ , S          ⟩
  prodˢₕ₂ : ⟨ H , prodˢ p t₁ t₂ , ρ , sndₑ p ∙ S ⟩
          ⇒ᵥ ⟨ H , t₂           , ρ , S          ⟩
  prodʷₕ : ⟨ H                                                        , prodʷ p t₁ t₂ , ρ          , prodrecₑ r p q A u ρ′ ∙ S ⟩
         ⇒ᵥ ⟨ H ∙ (∣ S ∣ · r · p , t₁ , ρ) ∙ (∣ S ∣ · r , t₂ , step ρ) , u             , liftn ρ′ 2 , wk2ˢ S                    ⟩
  zeroₕ   : ⟨ H , zero , ρ  , natrecₑ p q r A z s ρ′ ∙ S ⟩
          ⇒ᵥ ⟨ H , z    , ρ′ , S                          ⟩
  sucₕ    : ⟨ H , suc t , ρ , natrecₑ p q r A z s ρ′ ∙ S ⟩
          ⇒ᵥ ⟨ H ∙ (∣ S ∣ · nr₂ p r , t , ρ) ∙ (∣ S ∣ · r , natrec p q r (wk (lift (step id)) A) (wk1 z) (wk (liftn (step id) 2) s) (var x0) , lift ρ′)
                , s , liftn ρ′ 2 , wk2ˢ S ⟩
  starʷₕ :  ⟨ H , starʷ l , ρ  , unitrecₑ l p q A u ρ′ ∙ S ⟩
         ⇒ᵥ ⟨ H , u       , ρ′ ,                         S ⟩
  unitrec-ηₕ : Unitʷ-η
             →  ⟨ H , unitrec l p q A t u , ρ , S ⟩
             ⇒ᵥ ⟨ H ,                   u , ρ , S ⟩
  rflₕⱼ : ⟨ H , rfl , ρ , Jₑ p q A t B u v ρ′ ∙ S ⟩
        ⇒ᵥ ⟨ H , u , ρ′ , S ⟩
  rflₕₖ : ⟨ H , rfl , ρ ,  Kₑ p A t B u ρ′ ∙ S ⟩
        ⇒ᵥ ⟨ H , u , ρ′ , S ⟩
  rflₕₑ : ⟨ H , rfl , ρ , []-congₑ s′ A t u ρ′ ∙ S ⟩
        ⇒ᵥ ⟨ H , rfl , ρ′ , S ⟩

-- The relation _⇒ₛ_ allows evaluation under the successor constructor in order
-- to fully evaluate terms to numerals.

infix 28 _⇒ₛ_

data _⇒ₛ_ {m′ m n} : State m′ m n → State m′ m n → Set a where
  sucₕ : ¬ Numeral t
       → ⟨ H , suc t , ρ , sucₛ k ⟩ ⇒ₛ ⟨ H , t , ρ , sucₑ ∙ sucₛ k ⟩
  numₕ : Numeral t
       → ⟨ H , t , ρ , sucₑ ∙ S ⟩ ⇒ₛ ⟨ H , suc t , ρ , S ⟩


-- The main reductio relation is the conjunction of the three relations
-- described above.
-- The reduction _⇒ₛ_ is included only if evaluation under suc is allowed
-- as specified by the Options

infix 30 ⇒ₙ_
infix 30 ⇒ᵥ_
infix 30 ⇒ₛ_
infix 28 _⇒_

data _⇒_ (s : State k m n) : State k m′ n′ → Set a where
  ⇒ₙ_ : {s′ : State k m n′} → s ⇒ₙ s′ → s ⇒ s′
  ⇒ᵥ_ : {s′ : State k m′ n′} → s ⇒ᵥ s′ → s ⇒ s′
  ⇒ₛ_ : {s′ : State k m n} → ⦃ ℕ-Fullred ⦄ → s ⇒ₛ s′ → s ⇒ s′

-- Reflexive, transistive closure of the reduction relation

infixr 30 _⇨_
infix 28 _⇒*_

data _⇒*_ (s : State k m n) : (s′ : State k m′ n′) → Set a where
  id : s ⇒* s
  _⇨_ : ∀ {m″ n″} {s′ : State k m′ n′} {s″ : State k m″ n″}
      → s ⇒ s′ → s′ ⇒* s″ → s ⇒* s″
