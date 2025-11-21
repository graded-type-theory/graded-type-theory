------------------------------------------------------------------------
-- A resource aware heap semantics. The reduction relations.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode
open import Graded.Usage.Restrictions
open import Definition.Typed.Variant
open import Graded.Usage.Restrictions.Natrec

module Graded.Heap.Reduction
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

open import Tools.Empty
open import Tools.Fin
open import Tools.Level
open import Tools.Nat hiding (_⊔_)
open import Tools.Product
open import Tools.Relation

open import Definition.Untyped M
open import Graded.Heap.Untyped type-variant UR factoring-nr

open Type-variant type-variant
open Modality 𝕄

private variable
  m m′ n n′ k ℓ : Nat
  H H′ : Heap _ _
  ρ ρ′ : Wk _ _
  t t′ u v w z s A B t₁ t₂ : Term _
  x : Fin _
  S S′ : Stack _
  p p′ q q′ r : M
  str : Strength
  l : Universe-level
  s₁ s₂ s₃ : State _ _ _

-- The abstract machine has three different semantics.
-- 1. A call-by-name semantics with resource tracking that reduces terms
--    to WHNF. Denoted by _⇾_.
-- 2. A call-by-name semantics without resource tracking that reduces
--    terms to WHNF. Denoted by _⇢_.
-- 3. A call-by-name semantics with resource tracking that fully
--    evaluates natural numbers to numerals (but that otherwise reduces
--    terms to WHNF). Denoted by _↠_.
--
-- These are defined using a few additional reduction relations.

------------------------------------------------------------------------
-- The preliminary reduction relations.

-- The relation _⇒ₑ_ describes evaluation of states with an eliminator
-- in head position.

infix 28 _⇒ₑ_

data _⇒ₑ_ {k m n} : State k m n → State k m n → Set a where
  appₕ : ⟨ H , t ∘⟨ p ⟩ u , ρ , S ⟩ ⇒ₑ ⟨ H , t , ρ , ∘ₑ p u ρ ∙ S ⟩
  fstₕ : ⟨ H , fst p t , ρ , S ⟩ ⇒ₑ ⟨ H , t , ρ , fstₑ p ∙ S ⟩
  sndₕ : ⟨ H , snd p t , ρ , S ⟩ ⇒ₑ ⟨ H , t , ρ , sndₑ p ∙ S ⟩
  prodrecₕ : ⟨ H , prodrec r p q A t u , ρ , S ⟩ ⇒ₑ
             ⟨ H , t , ρ , prodrecₑ r p q A u ρ ∙ S ⟩
  natrecₕ : ⟨ H , natrec p q r A z s t , ρ , S ⟩ ⇒ₑ
            ⟨ H , t , ρ , natrecₑ p q r A z s ρ ∙ S ⟩
  unitrecₕ : ¬ Unitʷ-η →
             ⟨ H , unitrec l p q A t u , ρ , S ⟩ ⇒ₑ
             ⟨ H , t , ρ , unitrecₑ l p q A u ρ ∙ S ⟩
  emptyrecₕ : ⟨ H , emptyrec p A t , ρ , S ⟩ ⇒ₑ
              ⟨ H , t , ρ , emptyrecₑ p A ρ ∙ S ⟩
  Jₕ : ⟨ H , J p q A t B u v w , ρ , S ⟩ ⇒ₑ
       ⟨ H , w , ρ , Jₑ p q A t B u v ρ ∙ S ⟩
  Kₕ : ⟨ H , K p A t B u v , ρ , S ⟩ ⇒ₑ
       ⟨ H , v , ρ , Kₑ p A t B u ρ ∙ S ⟩
  []-congₕ : ⟨ H , []-cong str A t u v , ρ , S ⟩ ⇒ₑ
             ⟨ H , v , ρ , []-congₑ str A t u ρ ∙ S ⟩

-- The relation _⇾ₑ_ describes evaluation of states with an eliminator
-- or a variable in head position with resource tracking.

infix 28 _⇾ₑ_
infix 30 ⇒ₑ_

data _⇾ₑ_ {k m n} : State k m n → State k m n′ → Set (a ⊔ b) where
  var : ∣ S ∣≡ p →
        H ⊢ wkVar ρ x ↦[ p ] (t , ρ′) ⨾ H′ →
        ⟨ H , var x , ρ , S ⟩ ⇾ₑ ⟨ H′ , t , ρ′ , S ⟩
  ⇒ₑ_ : s₁ ⇒ₑ s₂ → s₁ ⇾ₑ s₂

-- Reflexive, transistive closure of _⇾ₑ_.

infix 28 _⇾ₑ*_
infixr 29 _⇨_

data _⇾ₑ*_ (s : State k m n) : (s′ : State k m n′) → Set (a ⊔ b) where
  id : s ⇾ₑ* s
  _⇨_ : ∀ {n″} {s′ : State k m n′} {s″ : State k m n″}
      → s ⇾ₑ s′ → s′ ⇾ₑ* s″ → s ⇾ₑ* s″

-- The relation _⇢ₑ_ describes evaluation of states with an eliminator
-- or a variable in head position without resource tracking.

infix 28 _⇢ₑ_

data _⇢ₑ_ {k m n} : State k m n → State k m n′ → Set a where
  var : H ⊢ wkVar ρ x ↦ (t , ρ′) →
        ⟨ H , var x , ρ , S ⟩ ⇢ₑ ⟨ H , t , ρ′ , S ⟩
  ⇒ₑ_ : s₁ ⇒ₑ s₂ → s₁ ⇢ₑ s₂

-- Reflexive, transistive closure of _⇢ₑ*_

infix 28 _⇢ₑ*_

data _⇢ₑ*_ (s : State k m n) : (s′ : State k m n′) → Set a where
  id : s ⇢ₑ* s
  _⇨_ : ∀ {n″} {s′ : State k m n′} {s″ : State k m n″}
      → s ⇢ₑ s′ → s′ ⇢ₑ* s″ → s ⇢ₑ* s″

-- The relation _⇒ᵥ_ evaluates states with values in head position and a
-- matching continuation on the top of the stack.

infix 28 _⇒ᵥ_

data _⇒ᵥ_ {k m n} : State k m n → State k m′ n′ → Set (a ⊔ b) where
  lamₕ : ∣ S ∣≡ q
       → ⟨ H , lam p t , ρ , ∘ₑ p u ρ′ ∙ S ⟩ ⇒ᵥ
         ⟨ H ∙ (q · p , u , ρ′) , t , lift ρ , wk1ˢ S ⟩
  prodˢₕ₁ : ⟨ H , prodˢ p t₁ t₂ , ρ , fstₑ p ∙ S ⟩ ⇒ᵥ
            ⟨ H , t₁           , ρ , S          ⟩
  prodˢₕ₂ : ⟨ H , prodˢ p t₁ t₂ , ρ , sndₑ p ∙ S ⟩
          ⇒ᵥ ⟨ H , t₂           , ρ , S          ⟩
  prodʷₕ : ∣ S ∣≡ q′
         → ⟨ H , prodʷ p t₁ t₂ , ρ , prodrecₑ r p q A u ρ′ ∙ S ⟩ ⇒ᵥ
           ⟨ H ∙ (q′ · r · p , t₁ , ρ) ∙ (q′ · r , t₂ , step ρ)
              , u             , liftn ρ′ 2 , wk2ˢ S ⟩
  zeroₕ : ⟨ H , zero , ρ  , natrecₑ p q r A z s ρ′ ∙ S ⟩ ⇒ᵥ
          ⟨ H , z    , ρ′ , S                          ⟩

  sucₕ : -- p′ is the multiplicity of the natrec continuation
         -- on top of the stack and q′ is the multiplicity of
         -- the rest of the stack.
         ∣ S ∣≡ q′ → ∣natrec p , r ∣≡ p′ →
         ⟨ H , suc t , ρ , natrecₑ p q r A z s ρ′ ∙ S ⟩ ⇒ᵥ
         ⟨ H ∙ (q′ · p′ , t , ρ)
             ∙ (q′ · r , natrec p q r (wk (lift (step id)) A) (wk1 z)
                              (wk (liftn (step id) 2) s) (var x0)
                          , lift ρ′)
             , s , liftn ρ′ 2 , wk2ˢ S ⟩
  starʷₕ :  ⟨ H , starʷ l , ρ  , unitrecₑ l p q A u ρ′ ∙ S ⟩ ⇒ᵥ
            ⟨ H , u       , ρ′ ,                         S ⟩
  unitrec-ηₕ : Unitʷ-η →
               ⟨ H , unitrec l p q A t u , ρ , S ⟩ ⇒ᵥ
               ⟨ H ,                   u , ρ , S ⟩
  rflₕⱼ : ⟨ H , rfl , ρ  , Jₑ p q A t B u v ρ′ ∙ S ⟩ ⇒ᵥ
          ⟨ H , u   , ρ′ , S ⟩
  rflₕₖ : ⟨ H , rfl , ρ ,  Kₑ p A t B u ρ′ ∙ S ⟩ ⇒ᵥ ⟨ H , u , ρ′ , S ⟩
  rflₕₑ : ⟨ H , rfl , ρ  , []-congₑ str A t u ρ′ ∙ S ⟩ ⇒ᵥ
          ⟨ H , rfl , ρ′ , S ⟩

-- The relation _⇒ₙ_ allows evaluation under the successor constructor
-- in order to fully evaluate terms to numerals.

infix 28 _⇒ₙ_

data _⇒ₙ_ {k m n} : State k m n → State k m n → Set a where
  sucₕ : ¬ Numeral t →
         ⟨ H , suc t , ρ , sucₛ ℓ ⟩ ⇒ₙ ⟨ H , t , ρ , sucₑ ∙ sucₛ ℓ ⟩
  numₕ : Numeral t →
         ⟨ H , t , ρ , sucₑ ∙ S ⟩ ⇒ₙ ⟨ H , suc t , ρ , S ⟩

------------------------------------------------------------------------
-- The main reduction relations.

infix 30 ⇾ₑ_
infix 30 ⇒ᵥ_
infix 30 ⇒ₙ_
infix 30 ⇢ₑ_

-- Evaluation to WHNF with resource tracking.

data _⇾_ (s₁ : State k m n) : State k m′ n′ → Set (a ⊔ b) where
  ⇾ₑ_ : s₁ ⇾ₑ s₂ → s₁ ⇾ s₂
  ⇒ᵥ_ : s₁ ⇒ᵥ s₂ → s₁ ⇾ s₂

-- Evaluation of natural numbers to numerals with resource tracking.

data _↠_ (s₁ : State k m n) : State k m′ n′ → Set (a ⊔ b) where
  ⇾ₑ_ : s₁ ⇾ₑ s₂ → s₁ ↠ s₂
  ⇒ᵥ_ : s₁ ⇒ᵥ s₂ → s₁ ↠ s₂
  ⇒ₙ_ : s₁ ⇒ₙ s₂ → s₁ ↠ s₂

pattern ⇾ₑ′ d = ⇾ₑ (⇒ₑ d)

-- Evaluation to WHNF without resource tracking.

data _⇢_ (s₁ : State k m n) : State k m′ n′ → Set (a ⊔ b) where
  ⇢ₑ_ : s₁ ⇢ₑ s₂ → s₁ ⇢ s₂
  ⇒ᵥ_ : s₁ ⇒ᵥ s₂ → s₁ ⇢ s₂

infix 28 _⇾*_
infix 28 _↠*_
infix 28 _⇢*_

-- Reflexive, transitive closure of _⇾_.

data _⇾*_ (s₁ : State k m n) : State k m′ n′ → Set (a ⊔ b) where
  id  : s₁ ⇾* s₁
  _⇨_ : s₁ ⇾ s₂ → s₂ ⇾* s₃ → s₁ ⇾* s₃

-- Reflexive, transitive closure of _↠_.

data _↠*_ (s₁ : State k m n) : State k m′ n′ → Set (a ⊔ b) where
  id  : s₁ ↠* s₁
  _⇨_ : s₁ ↠ s₂ → s₂ ↠* s₃ → s₁ ↠* s₃

-- Reflexive, transitive closure of _⇢_.

data _⇢*_ (s₁ : State k m n) : State k m′ n′ → Set (a ⊔ b) where
  id  : s₁ ⇢* s₁
  _⇨_ : s₁ ⇢ s₂ → s₂ ⇢* s₃ → s₁ ⇢* s₃

Final : State k m n → Set (a ⊔ b)
Final s = ∀ {m n} {s′ : State _ m n} → s ⇾ s′ → ⊥

_⇘_ : State k m n → State k m′ n′ → Set (a ⊔ b)
s ⇘ s′ = s ⇾* s′ × Final s′
