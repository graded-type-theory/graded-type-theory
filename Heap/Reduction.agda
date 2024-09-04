------------------------------------------------------------------------
-- A resource aware heap semantics. The reduction relation.
------------------------------------------------------------------------

open import Graded.Modality
open import Tools.Bool
open import Heap.Options

module Heap.Reduction
  {a} {M : Set a} (𝕄 : Modality M)
  (opts : Options)
  (open Modality 𝕄)
  ⦃ _ : Has-nr M semiring-with-meet ⦄
  ⦃ _ : Has-factoring-nr M semiring-with-meet ⦄
  where

open import Tools.Empty
open import Tools.Fin
open import Tools.Nat hiding (_+_)
open import Tools.Product
open import Tools.Relation

open import Definition.Untyped M
open import Graded.Modality.Nr-instances
open import Heap.Untyped 𝕄

open Options opts

private variable
  m m′ n n′ k : Nat
  H H′ : Heap _
  E E′ : Env _ _
  t t′ u v w z s A B t₁ t₂ : Term _
  x : Fin _
  S S′ : Stack _
  p q r : M
  s′ : Strength



data _⇒ₙ_ {m n} : State m n → State m n′ → Set a where
  varₕ : ⦃ tr : Track-resources ⦄
       → H ⊢ wkVar E x ↦[ ∣ S ∣ ] (t , E′) ⨾ H′ →
          ⟨ H  , var x , E  , S ⟩
       ⇒ₙ ⟨ H′ , t     , E′ , S ⟩
  varₕ′ : ⦃ tr : ¬Track-resources ⦄
        → H ⊢ wkVar E x ↦ (t , E′) →
          ⟨ H  , var x , E  , S ⟩
        ⇒ₙ ⟨ H , t     , E′ , S  ⟩
  appₕ : ⟨ H , t ∘⟨ p ⟩ u , E , S            ⟩
       ⇒ₙ ⟨ H , t         , E , ∘ₑ p u E ∙ S ⟩
  fstₕ : ⟨ H , fst p t , E , S          ⟩
       ⇒ₙ ⟨ H , t       , E , fstₑ p ∙ S ⟩
  sndₕ : ⟨ H , snd p t , E , S          ⟩
       ⇒ₙ ⟨ H , t       , E , sndₑ p ∙ S ⟩
  prodrecₕ : ⟨ H , prodrec r p q A t u , E , S ⟩
           ⇒ₙ ⟨ H , t                   , E , prodrecₑ r p q A u E ∙ S ⟩
  natrecₕ : ⟨ H , natrec p q r A z s t , E , S                         ⟩
          ⇒ₙ ⟨ H , t                    , E , natrecₑ p q r A z s E ∙ S ⟩
  unitrecₕ : ⟨ H , unitrec p q A t u , E , S                      ⟩
           ⇒ₙ ⟨ H , t                 , E , unitrecₑ p q A u E ∙ S ⟩
  Jₕ : ⟨ H , J p q A t B u v w , E , S ⟩
     ⇒ₙ ⟨ H , w , E , Jₑ p q A t B u v E ∙ S ⟩
  Kₕ : ⟨ H , K p A t B u v , E , S ⟩
     ⇒ₙ ⟨ H , v , E , Kₑ p A t B u E ∙ S ⟩
  []-congₕ : ⟨ H , []-cong s′ A t u v , E , S ⟩
           ⇒ₙ ⟨ H , v , E , []-congₑ s′ A t u E ∙ S ⟩

-- Reflexive, transistive closure of the reduction relation

data _⇒ₙ*_ (s : State m n) : (s′ : State m n′) → Set a where
  id : s ⇒ₙ* s
  _⇨_ : ∀ {n″} {s′ : State m n′} {s″ : State m n″}
      → s ⇒ₙ s′ → s′ ⇒ₙ* s″ → s ⇒ₙ* s″

data _⇒ᵥ_ {m n} : State m n → State m′ n′ → Set a where
  lamₕ : ⟨ H                        , lam p t , E           , ∘ₑ p u E′ ∙ S ⟩
       ⇒ᵥ ⟨ H ∙ (∣ S ∣ · p , u , E′) , t       , lift E      , wk1ˢ S        ⟩
  prodˢₕ₁ : ⟨ H , prodˢ p t₁ t₂ , E , fstₑ p ∙ S ⟩
          ⇒ᵥ ⟨ H , t₁           , E , S          ⟩
  prodˢₕ₂ : ⟨ H , prodˢ p t₁ t₂ , E , sndₑ p ∙ S ⟩
          ⇒ᵥ ⟨ H , t₂           , E , S          ⟩
  prodʷₕ : ⟨ H                                                        , prodʷ p t₁ t₂ , E          , prodrecₑ r p q A u E′ ∙ S ⟩
         ⇒ᵥ ⟨ H ∙ (∣ S ∣ · r · p , t₁ , E) ∙ (∣ S ∣ · r , t₂ , step E) , u             , liftn E′ 2 , wk2ˢ S                    ⟩
  zeroₕ   : ⟨ H , zero , E  , natrecₑ p q r A z s E′ ∙ S ⟩
          ⇒ᵥ ⟨ H , z    , E′ , S                          ⟩
  sucₕ    : ⟨ H , suc t , E , natrecₑ p q r A z s E′ ∙ S ⟩
          ⇒ᵥ ⟨ H ∙ (∣ S ∣ · nr₂ p r , t , E) ∙ (∣ S ∣ · r , natrec p q r (wk (lift (step id)) A) (wk1 z) (wk (liftn (step id) 2) s) (var x0) , lift E′)
                , s , liftn E′ 2 , wk2ˢ S ⟩
  starʷₕ : ⟨ H , starʷ , E  , unitrecₑ p q A u E′ ∙ S ⟩
         ⇒ᵥ ⟨ H , u     , E′ , S                       ⟩
  rflₕⱼ : ⟨ H , rfl , E , Jₑ p q A t B u v E′ ∙ S ⟩
        ⇒ᵥ ⟨ H , u , E′ , S ⟩
  rflₕₖ : ⟨ H , rfl , E ,  Kₑ p A t B u E′ ∙ S ⟩
        ⇒ᵥ ⟨ H , u , E′ , S ⟩
  rflₕₑ : ⟨ H , rfl , E , []-congₑ s′ A t u E′ ∙ S ⟩
        ⇒ᵥ ⟨ H , rfl , E′ , S ⟩

data _⇒ₛ_ {m n} : State m n → State m n → Set a where
  sucₕ : ¬ Numeral t
       → ⟨ H , suc t , E , sucₛ k ⟩ ⇒ₛ ⟨ H , t , E , sucₑ ∙ sucₛ k ⟩
  numₕ : Numeral t
       → ⟨ H , t , E , sucₑ ∙ S ⟩ ⇒ₛ ⟨ H , suc t , E , S ⟩


-- The heap semantics using single step reductions of heap states.
-- The number of free variables and the size of the heap
-- may change in an evaluation step.

data _⇒_ : State m n → State m′ n′ → Set a where
  ⇒ₙ_ : {s : State m n} {s′ : State m n′} → s ⇒ₙ s′ → s ⇒ s′
  ⇒ᵥ_ : {s : State m n} {s′ : State m′ n′} → s ⇒ᵥ s′ → s ⇒ s′
  ⇒ₛ_ : {s s′ : State m n} → ⦃ ℕ-Fullred ⦄ → s ⇒ₛ s′ → s ⇒ s′

-- Reflexive, transistive closure of the reduction relation

data _⇒*_ : (s : State m n) (s′ : State m′ n′) → Set a where
  id : {s : State m n} → s ⇒* s
  _⇨_ : ∀ {m″ n″} {s : State m n} {s′ : State m′ n′} {s″ : State m″ n″}
      → s ⇒ s′ → s′ ⇒* s″ → s ⇒* s″
