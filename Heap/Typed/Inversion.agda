------------------------------------------------------------------------
-- Inversion lemmata for Heap typing
------------------------------------------------------------------------

open import Graded.Modality
open import Definition.Typed.Restrictions
open import Tools.Bool

module Heap.Typed.Inversion
  {a} {M : Set a} {𝕄 : Modality M}
  (TR : Type-restrictions 𝕄)
  (ℕ-fullred : Bool)
  where

open Type-restrictions TR

open import Definition.Untyped M
open import Definition.Untyped.Properties M
open import Definition.Typed TR
open import Definition.Typed.Consequences.DerivedRules TR
open import Definition.Typed.Consequences.Injectivity TR
open import Definition.Typed.Consequences.Inversion TR
open import Definition.Typed.Consequences.Substitution TR
open import Definition.Typed.Consequences.Syntactic TR
import Graded.Derived.Erased.Untyped 𝕄 as E
open import Graded.Derived.Erased.Typed TR

open import Heap.Typed TR ℕ-fullred
open import Heap.Untyped 𝕄

open import Tools.Fin
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Sum hiding (sym)

private variable
  H : Heap _
  Γ : Con Term _
  t u v w z s A B C D F G : Term _
  p q r : M
  E : Env _ _
  S : Stack _
  e : Elim _
  s′ : Strength

opaque

  -- Inversion of application

  inversion-∘ₑ : H ⊢ᵉ ∘ₑ p u E ∷ t ∷ A ↝ B
               → ∃₃ λ F G q → ε ⊢ wk E u [ H ]ₕ ∷ F
                 × A PE.≡ Π p , q ▷ F ▹ G × ε ⊢ B ≡ G [ wk E u [ H ]ₕ ]₀
  inversion-∘ₑ (∘ₑ ⊢u ⊢B) =
      _ , _ , _ , ⊢u
    , PE.refl
    , refl (substType ⊢B ⊢u)
  inversion-∘ₑ (conv ⊢e B≡B′) =
    case inversion-∘ₑ ⊢e of λ
      (F , G , q , ⊢u , A≡Π , B≡) →
    _ , _ , _ , ⊢u , A≡Π , trans (sym B≡B′) B≡

opaque

  -- Inversion of fst

  inversion-fstₑ : H ⊢ᵉ fstₑ p ∷ t ∷ A ↝ B
                 → ∃₃ λ F G q → (ε ⊢ F) × (ε ∙ F ⊢ G)
                   × A PE.≡ Σˢ p , q ▷ F ▹ G × ε ⊢ B ≡ F
  inversion-fstₑ (fstₑ ⊢A ⊢B) =
    _ , _ , _ , ⊢A , ⊢B , PE.refl , refl ⊢A
  inversion-fstₑ (conv ⊢e B≡B′) =
    case inversion-fstₑ ⊢e of λ
      (F , G , q , ⊢F , ⊢G , A≡Σ , B′≡) →
    _ , _ , _ , ⊢F , ⊢G , A≡Σ , trans (sym B≡B′) B′≡

opaque

  -- Inversion of snd

  inversion-sndₑ : H ⊢ᵉ sndₑ p ∷ t ∷ A ↝ B
                 → ∃₃ λ F G q → (ε ⊢ F) × (ε ∙ F ⊢ G)
                   × A PE.≡ Σˢ p , q ▷ F ▹ G
                   × (ε ⊢ t [ H ]ₕ ∷ A → ε ⊢ B ≡ G [ fst p t [ H ]ₕ ]₀)
  inversion-sndₑ (sndₑ ⊢A ⊢B) =
    _ , _ , _ , ⊢A , ⊢B , PE.refl
      , λ ⊢t → refl (substType ⊢B (fstⱼ′ ⊢t))
  inversion-sndₑ (conv ⊢e B≡B′) =
    case inversion-sndₑ ⊢e of λ
      (F , G , q , ⊢F , ⊢G , A≡Σ , B≡Gt) →
    _ , _ , _ , ⊢F , ⊢G , A≡Σ
      , λ ⊢t → trans (sym B≡B′) (B≡Gt ⊢t)

opaque

  -- Inversion or prodrec

  inversion-prodrecₑ : H ⊢ᵉ prodrecₑ r p q A u E ∷ t ∷ B ↝ C
                     → ∃₃ λ F G q′
                       → ε ∙ F ∙ G ⊢ wk (liftn E 2) u [ liftSubstn (toSubstₕ H) 2 ] ∷ (wk (lift E) A [ H ]⇑ₕ [ prodʷ p (var x1) (var x0) ]↑²)
                       × ε ∙ Σʷ p , q′ ▷ F ▹ G ⊢ wk (lift E) A [ H ]⇑ₕ
                       × B PE.≡ Σʷ p , q′ ▷ F ▹ G
                       × (ε ⊢ t [ H ]ₕ ∷ Σʷ p , q′ ▷ F ▹ G → ε ⊢ C ≡ wk (lift E) A [ H ]⇑ₕ [ t [ H ]ₕ ]₀)
  inversion-prodrecₑ (prodrecₑ ⊢u ⊢A) =
    _ , _ , _ , ⊢u , ⊢A , PE.refl , λ ⊢t → refl (substType ⊢A ⊢t)
  inversion-prodrecₑ (conv ⊢e ≡C) =
    case inversion-prodrecₑ ⊢e of λ
      (_ , _ , _ , ⊢u , ⊢A , B≡ , C′≡) →
    _ , _ , _ , ⊢u , ⊢A , B≡ , λ ⊢t → trans (sym ≡C) (C′≡ ⊢t)

opaque

  -- Inversion of natrec

  inversion-natrecₑ : H ⊢ᵉ natrecₑ p q r A z s E ∷ t ∷ B ↝ C
                    → ε ⊢ wk E z [ H ]ₕ ∷ wk (lift E) A [ H ]⇑ₕ [ zero ]₀
                    × ε ∙ ℕ ∙ wk (lift E) A [ H ]⇑ₕ ⊢ wk (liftn E 2) s [ H ]⇑²ₕ ∷ wk (lift E) A [ H ]⇑ₕ [ suc (var x1) ]↑²
                    × ε ∙ ℕ ⊢ wk (lift E) A [ H ]⇑ₕ
                    × B PE.≡ ℕ
                    × (ε ⊢ t [ H ]ₕ ∷ ℕ → ε ⊢ C ≡ wk (lift E) A [ H ]⇑ₕ [ t [ H ]ₕ ]₀)
  inversion-natrecₑ (natrecₑ ⊢z ⊢s ⊢A) =
    ⊢z , ⊢s , ⊢A , PE.refl , λ ⊢t → refl (substType ⊢A ⊢t)
  inversion-natrecₑ (conv ⊢e ≡C) =
    case inversion-natrecₑ ⊢e of λ
      (⊢z , ⊢s , ⊢A , B≡ , C′≡) →
    ⊢z , ⊢s , ⊢A , B≡ , λ ⊢t → trans (sym ≡C) (C′≡ ⊢t)

opaque

  -- Inversion of unitrec

  inversion-unitrecₑ : H ⊢ᵉ unitrecₑ p q A u E ∷ t ∷ B ↝ C
                     → ε ⊢ wk E u [ H ]ₕ ∷ wk (lift E) A [ H ]⇑ₕ [ starʷ ]₀
                     × (ε ∙ Unitʷ ⊢ wk (lift E) A [ H ]⇑ₕ)
                     × B PE.≡ Unitʷ
                     × (ε ⊢ t [ H ]ₕ ∷ B → ε ⊢ C ≡ (wk (lift E) A [ H ]⇑ₕ [ t [ H ]ₕ ]₀))
  inversion-unitrecₑ {A} (unitrecₑ ⊢u ⊢A) =
    ⊢u , ⊢A , PE.refl
       , λ ⊢t → refl (substType ⊢A ⊢t)
  inversion-unitrecₑ (conv ⊢e ≡C) =
    case inversion-unitrecₑ ⊢e of λ
      (⊢u , ⊢A , B≡ , C≡) →
    ⊢u , ⊢A , B≡ , λ ⊢t → trans (sym ≡C) (C≡ ⊢t)

-- opaque

--   -- Inversion of emptyrec

--   inversion-emptyrecₑ : H ⊢ᵉ emptyrecₑ p A E ∷ t ∷ B ↝ C
--                       → ε ⊢ wk E A [ H ]ₕ
--                       × B PE.≡ Empty
--                       × (ε ⊢ C ≡ wk E A [ H ]ₕ)
--   inversion-emptyrecₑ (emptyrecₑ ⊢A) =
--     ⊢A , PE.refl , refl ⊢A
--   inversion-emptyrecₑ (conv ⊢e ≡C) =
--     case inversion-emptyrecₑ ⊢e of λ
--       (⊢A , B≡ , C≡) →
--     ⊢A , B≡ , trans (sym ≡C) C≡

opaque

  -- Inversion of J

  inversion-Jₑ : H ⊢ᵉ Jₑ p q A t B u v E ∷ w ∷ C ↝ D
               → ε ⊢ wk E u [ H ]ₕ ∷ wk (liftn E 2) B [ liftSubstn (toSubstₕ H) 2 ] [ wk E t [ H ]ₕ , rfl ]₁₀
               × ε ∙ wk E A [ H ]ₕ ∙ Id (wk1 (wk E A [ H ]ₕ)) (wk1 (wk E t [ H ]ₕ)) (var x0) ⊢ wk (liftn E 2) B [ liftSubstn (toSubstₕ H) 2 ]
               × C PE.≡ wk E (Id A t v) [ H ]ₕ
               × (ε ⊢ w [ H ]ₕ ∷ wk E (Id A t v) [ H ]ₕ →
                  ε ⊢ D ≡ wk (liftn E 2) B [ liftSubstn (toSubstₕ H) 2 ] [ wk E v [ H ]ₕ , w [ H ]ₕ ]₁₀)
  inversion-Jₑ (Jₑ ⊢u ⊢B) =
    ⊢u , ⊢B , PE.refl , λ ⊢w → refl (J-result ⊢B ⊢w)
  inversion-Jₑ (conv ⊢e ≡D) =
    case inversion-Jₑ ⊢e of λ
      (⊢u , ⊢B , C≡ , D′≡) →
    ⊢u , ⊢B , C≡ , λ ⊢w → trans (sym ≡D) (D′≡ ⊢w)

opaque

  -- Inversion of K

  inversion-Kₑ : H ⊢ᵉ Kₑ p A t B u E ∷ v ∷ C ↝ D
               → ε ⊢ wk E u [ H ]ₕ ∷ wk (lift E) B [ H ]⇑ₕ [ rfl ]₀
               × ε ∙ wk E (Id A t t) [ H ]ₕ ⊢ wk (lift E) B [ H ]⇑ₕ
               × K-allowed
               × C PE.≡ wk E (Id A t t) [ H ]ₕ
               × (ε ⊢ v [ H ]ₕ ∷ wk E (Id A t t) [ H ]ₕ → ε ⊢ D ≡ wk (lift E) B [ H ]⇑ₕ [ v [ H ]ₕ ]₀)
  inversion-Kₑ (Kₑ ⊢u ⊢B ok) =
    ⊢u , ⊢B , ok , PE.refl , λ ⊢v → refl (substType ⊢B ⊢v)
  inversion-Kₑ (conv ⊢e ≡D) =
    case inversion-Kₑ ⊢e of λ
      (⊢u , ⊢B , ok , C≡ , D′≡) →
    ⊢u , ⊢B , ok , C≡ , λ ⊢v → trans (sym ≡D) (D′≡ ⊢v)

opaque

  -- Inversion of []-cong

  inversion-[]-congₑ : H ⊢ᵉ []-congₑ s′ A t u E ∷ v ∷ B ↝ C
                     → let open E s′ in
                     []-cong-allowed s′
                     × B PE.≡ wk E (Id A t u) [ H ]ₕ
                     × (ε ⊢ wk E t [ H ]ₕ ∷ wk E A [ H ]ₕ →
                        ε ⊢ wk E u [ H ]ₕ ∷ wk E A [ H ]ₕ →
                        ε ⊢ C ≡ (wk E (Id (Erased A) ([ t ]) ([ u ])) [ H ]ₕ))
  inversion-[]-congₑ ([]-congₑ ok) =
    ok , PE.refl
       , λ ⊢t ⊢u → refl (Idⱼ ([]ⱼ ([]-cong→Erased ok) ⊢t)
                             ([]ⱼ ([]-cong→Erased ok) ⊢u))
  inversion-[]-congₑ (conv ⊢e ≡C) =
    case inversion-[]-congₑ ⊢e of λ
      (ok , B≡ , C′≡) →
    ok , B≡ , λ ⊢t ⊢u → trans (sym ≡C) (C′≡ ⊢t ⊢u)

opaque

  -- Inversion of suc

  inversion-sucₑ : H ⊢ᵉ sucₑ ∷ t ∷ A ↝ B
                 → T ℕ-fullred × A PE.≡ ℕ × ε ⊢ B ≡ ℕ
  inversion-sucₑ (sucₑ ⦃ (x) ⦄) =
    x , PE.refl , refl (ℕⱼ ε)
  inversion-sucₑ (conv ⊢e ≡B) =
    case inversion-sucₑ ⊢e of λ
      (x , A≡ , B′≡) →
    x , A≡ , trans (sym ≡B) B′≡
