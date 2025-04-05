------------------------------------------------------------------------
-- Inversion lemmata for Heap typing
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions
open import Graded.Usage.Restrictions.Natrec

module Graded.Heap.Typed.Inversion
  {a} {M : Set a} {𝕄 : Modality M}
  (UR : Usage-restrictions 𝕄)
  (TR : Type-restrictions 𝕄)
  (open Usage-restrictions UR)
  (factoring-nr :
    ⦃ has-nr : Nr-available ⦄ →
    Is-factoring-nr M (Natrec-mode-Has-nr 𝕄 has-nr))
  where

open Type-restrictions TR

open import Definition.Untyped M
import Definition.Untyped.Erased 𝕄 as E
open import Definition.Typed TR
open import Definition.Typed.Properties TR
open import Definition.Typed.Substitution TR

open import Graded.Heap.Typed UR TR factoring-nr
open import Graded.Heap.Untyped type-variant UR factoring-nr

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation

private variable
  H : Heap _ _
  Δ : Con Term _
  t u v w z s A B C D F G : Term _
  p q q′ r : M
  ρ : Wk _ _
  S : Stack _
  c : Cont _
  s′ : Strength
  l : Universe-level

opaque

  -- Inversion of application

  inversion-∘ₑ : Δ ⨾ H ⊢ᶜ ∘ₑ p u ρ ⟨ t ⟩∷ A ↝ B
               → ∃₃ λ F G q → Δ ⊢ wk ρ u [ H ]ₕ ∷ F
                 × A PE.≡ Π p , q ▷ F ▹ G
                 × Δ ⊢ B ≡ G [ wk ρ u [ H ]ₕ ]₀
  inversion-∘ₑ {H} (∘ₑ {ρ} {u} {A} {B} ⊢u ⊢B) =
    A , B , _ , ⊢u , PE.refl
      , refl (substType ⊢B ⊢u)
  inversion-∘ₑ (conv ⊢c B≡B′) =
    case inversion-∘ₑ ⊢c of λ
      (F , G , q , ⊢u , A≡Π , B≡) →
    F , G , _ , ⊢u , A≡Π , trans (sym B≡B′) B≡

opaque

  -- Inversion of fst

  inversion-fstₑ :
    Δ ⨾ H ⊢ᶜ fstₑ p ⟨ t ⟩∷ A ↝ B →
    ∃₃ λ F G q → (Δ ∙ F ⊢ G) × A PE.≡ Σˢ p , q ▷ F ▹ G × Δ ⊢ B ≡ F
  inversion-fstₑ (fstₑ ⊢B) =
    _ , _ , _ , ⊢B , PE.refl , refl (⊢∙→⊢ (wf ⊢B))
  inversion-fstₑ (conv ⊢c B≡B′) =
    case inversion-fstₑ ⊢c of λ
      (F , G , q , ⊢G , A≡Σ , B′≡) →
    _ , _ , _ , ⊢G , A≡Σ , trans (sym B≡B′) B′≡

opaque

  -- Inversion of snd

  inversion-sndₑ :
    Δ ⨾ H ⊢ᶜ sndₑ p ⟨ t ⟩∷ A ↝ B →
    ∃₃ λ F G q → (Δ ∙ F ⊢ G) × A PE.≡ Σˢ p , q ▷ F ▹ G ×
      (Δ ⊢ t [ H ]ₕ ∷ A → Δ ⊢ B ≡ G [ fst p t [ H ]ₕ ]₀)
  inversion-sndₑ (sndₑ ⊢B) =
    _ , _ , _ , ⊢B , PE.refl
      , λ ⊢t → refl (substType ⊢B (fstⱼ′ ⊢t))
  inversion-sndₑ (conv ⊢c B≡B′) =
    case inversion-sndₑ ⊢c of λ
      (F , G , q , ⊢G , A≡Σ , B≡Gt) →
    _ , _ , _ , ⊢G , A≡Σ
      , λ ⊢t → trans (sym B≡B′) (B≡Gt ⊢t)

opaque

  -- Inversion or prodrec

  inversion-prodrecₑ : Δ ⨾ H ⊢ᶜ prodrecₑ r p q A u ρ ⟨ t ⟩∷ B ↝ C
                     → ∃₃ λ F G q′
                       → Δ ∙ F ∙ G ⊢
                           wk (liftn ρ 2) u [ liftSubstn (toSubstₕ H) 2 ] ∷
                           (wk (lift ρ) A [ H ]⇑ₕ [ prodʷ p (var x1) (var x0) ]↑²)
                       × Δ ∙ Σʷ p , q′ ▷ F ▹ G ⊢ wk (lift ρ) A [ H ]⇑ₕ
                       × B PE.≡ Σʷ p , q′ ▷ F ▹ G
                       × (Δ ⊢ t [ H ]ₕ ∷ Σʷ p , q′ ▷ F ▹ G → Δ ⊢ C ≡ wk (lift ρ) A [ H ]⇑ₕ [ t [ H ]ₕ ]₀)
  inversion-prodrecₑ (prodrecₑ ⊢u ⊢A) =
    _ , _ , _ , ⊢u , ⊢A , PE.refl , λ ⊢t → refl (substType ⊢A ⊢t)
  inversion-prodrecₑ (conv ⊢c ≡C) =
    case inversion-prodrecₑ ⊢c of λ
      (_ , _ , _ , ⊢u , ⊢A , B≡ , C′≡) →
    _ , _ , _ , ⊢u , ⊢A , B≡ , λ ⊢t → trans (sym ≡C) (C′≡ ⊢t)

opaque

  -- Inversion of natrec

  inversion-natrecₑ : Δ ⨾ H ⊢ᶜ natrecₑ p q r A z s ρ ⟨ t ⟩∷ B ↝ C
                    → Δ ⊢ wk ρ z [ H ]ₕ ∷ wk (lift ρ) A [ H ]⇑ₕ [ zero ]₀
                    × Δ ∙ ℕ ∙ wk (lift ρ) A [ H ]⇑ₕ ⊢ wk (liftn ρ 2) s [ H ]⇑²ₕ ∷ wk (lift ρ) A [ H ]⇑ₕ [ suc (var x1) ]↑²
                    × B PE.≡ ℕ
                    × (Δ ⊢ t [ H ]ₕ ∷ ℕ → Δ ⊢ C ≡ wk (lift ρ) A [ H ]⇑ₕ [ t [ H ]ₕ ]₀)
  inversion-natrecₑ (natrecₑ ⊢z ⊢s) =
    ⊢z , ⊢s , PE.refl , λ ⊢t → refl (substType (⊢∙→⊢ (wfTerm ⊢s)) ⊢t)
  inversion-natrecₑ (conv ⊢c ≡C) =
    case inversion-natrecₑ ⊢c of λ
      (⊢z , ⊢s , B≡ , C′≡) →
    ⊢z , ⊢s , B≡ , λ ⊢t → trans (sym ≡C) (C′≡ ⊢t)

opaque

  -- Inversion of unitrec

  inversion-unitrecₑ :
    Δ ⨾ H ⊢ᶜ unitrecₑ l p q A u ρ ⟨ t ⟩∷ B ↝ C →
    Δ ⊢ wk ρ u [ H ]ₕ ∷ wk (lift ρ) A [ H ]⇑ₕ [ starʷ l ]₀ ×
    (Δ ∙ Unitʷ l ⊢ wk (lift ρ) A [ H ]⇑ₕ) ×
    ¬ Unitʷ-η ×
    B PE.≡ Unitʷ l ×
    (Δ ⊢ t [ H ]ₕ ∷ B → Δ ⊢ C ≡ wk (lift ρ) A [ H ]⇑ₕ [ t [ H ]ₕ ]₀)
  inversion-unitrecₑ {A} (unitrecₑ ⊢u ⊢A no-η) =
    ⊢u , ⊢A , no-η , PE.refl
       , λ ⊢t → refl (substType ⊢A ⊢t)
  inversion-unitrecₑ (conv ⊢c ≡C) =
    case inversion-unitrecₑ ⊢c of λ
      (⊢u , ⊢A , no-η , B≡ , C≡) →
    ⊢u , ⊢A , no-η , B≡ , λ ⊢t → trans (sym ≡C) (C≡ ⊢t)

opaque

  -- Inversion of emptyrec

  inversion-emptyrecₑ : Δ ⨾ H ⊢ᶜ emptyrecₑ p A ρ ⟨ t ⟩∷ B ↝ C
                      → Δ ⊢ wk ρ A [ H ]ₕ
                      × B PE.≡ Empty
                      × (Δ ⊢ C ≡ wk ρ A [ H ]ₕ)
  inversion-emptyrecₑ (emptyrecₑ ⊢A) =
    ⊢A , PE.refl , refl ⊢A
  inversion-emptyrecₑ (conv ⊢c ≡C) =
    case inversion-emptyrecₑ ⊢c of λ
      (⊢A , B≡ , C≡) →
    ⊢A , B≡ , trans (sym ≡C) C≡

opaque

  -- Inversion of J

  inversion-Jₑ : Δ ⨾ H ⊢ᶜ Jₑ p q A t B u v ρ ⟨ w ⟩∷ C ↝ D
               → Δ ⊢ wk ρ u [ H ]ₕ ∷ wk (liftn ρ 2) B [ liftSubstn (toSubstₕ H) 2 ] [ wk ρ t [ H ]ₕ , rfl ]₁₀
               × Δ ∙ wk ρ A [ H ]ₕ ∙ Id (wk1 (wk ρ A [ H ]ₕ)) (wk1 (wk ρ t [ H ]ₕ)) (var x0) ⊢ wk (liftn ρ 2) B [ liftSubstn (toSubstₕ H) 2 ]
               × C PE.≡ wk ρ (Id A t v) [ H ]ₕ
               × (Δ ⊢ w [ H ]ₕ ∷ wk ρ (Id A t v) [ H ]ₕ →
                  Δ ⊢ D ≡ wk (liftn ρ 2) B [ liftSubstn (toSubstₕ H) 2 ] [ wk ρ v [ H ]ₕ , w [ H ]ₕ ]₁₀)
  inversion-Jₑ (Jₑ ⊢u ⊢B) =
    ⊢u , ⊢B , PE.refl , λ ⊢w → refl (J-result ⊢B ⊢w)
  inversion-Jₑ (conv ⊢c ≡D) =
    case inversion-Jₑ ⊢c of λ
      (⊢u , ⊢B , C≡ , D′≡) →
    ⊢u , ⊢B , C≡ , λ ⊢w → trans (sym ≡D) (D′≡ ⊢w)

opaque

  -- Inversion of K

  inversion-Kₑ : Δ ⨾ H ⊢ᶜ Kₑ p A t B u ρ ⟨ v ⟩∷ C ↝ D
               → Δ ⊢ wk ρ u [ H ]ₕ ∷ wk (lift ρ) B [ H ]⇑ₕ [ rfl ]₀
               × Δ ∙ wk ρ (Id A t t) [ H ]ₕ ⊢ wk (lift ρ) B [ H ]⇑ₕ
               × K-allowed
               × C PE.≡ wk ρ (Id A t t) [ H ]ₕ
               × (Δ ⊢ v [ H ]ₕ ∷ wk ρ (Id A t t) [ H ]ₕ → Δ ⊢ D ≡ wk (lift ρ) B [ H ]⇑ₕ [ v [ H ]ₕ ]₀)
  inversion-Kₑ (Kₑ ⊢u ⊢B ok) =
    ⊢u , ⊢B , ok , PE.refl , λ ⊢v → refl (substType ⊢B ⊢v)
  inversion-Kₑ (conv ⊢c ≡D) =
    case inversion-Kₑ ⊢c of λ
      (⊢u , ⊢B , ok , C≡ , D′≡) →
    ⊢u , ⊢B , ok , C≡ , λ ⊢v → trans (sym ≡D) (D′≡ ⊢v)

opaque

  -- Inversion of []-cong

  inversion-[]-congₑ : Δ ⨾ H ⊢ᶜ []-congₑ s′ A t u ρ ⟨ v ⟩∷ B ↝ C
                     → let open E s′ in
                     []-cong-allowed s′
                     × B PE.≡ wk ρ (Id A t u) [ H ]ₕ
                     × (Δ ⊢ wk ρ t [ H ]ₕ ∷ wk ρ A [ H ]ₕ →
                        Δ ⊢ wk ρ u [ H ]ₕ ∷ wk ρ A [ H ]ₕ →
                        Δ ⊢ C ≡ (wk ρ (Id (Erased A) ([ t ]) ([ u ])) [ H ]ₕ))
  inversion-[]-congₑ ([]-congₑ ok) =
    let E-ok = []-cong→Erased ok in
    ok , PE.refl , λ ⊢t ⊢u → refl (Idⱼ′ ([]ⱼ E-ok ⊢t) ([]ⱼ E-ok ⊢u))
  inversion-[]-congₑ (conv ⊢c ≡C) =
    case inversion-[]-congₑ ⊢c of λ
      (ok , B≡ , C′≡) →
    ok , B≡ , λ ⊢t ⊢u → trans (sym ≡C) (C′≡ ⊢t ⊢u)

opaque

  -- Inversion of suc

  inversion-sucₑ : Δ ⨾ H ⊢ᶜ sucₑ ⟨ t ⟩∷ A ↝ B → ⊥
  inversion-sucₑ (conv ⊢c _) = inversion-sucₑ ⊢c

opaque

  -- Inversion of stack typing

  ⊢ˢ-inv :
    Δ ⨾ H ⊢ c ∙ S ⟨ t ⟩∷ A ↝ B →
    ∃ λ C → Δ ⨾ H ⊢ᶜ c ⟨ t ⟩∷ A ↝ C ×
    (Δ ⨾ H ⊢ S ⟨ ⦅ c ⦆ᶜ t ⟩∷ C ↝ B)
  ⊢ˢ-inv (⊢c ∙ ⊢S) = _ , ⊢c , ⊢S

opaque

  -- Inversion of state typing

  ⊢ₛ-inv :
    Δ ⊢ₛ ⟨ H , t , ρ , S ⟩ ∷ A →
    ∃₂ λ Γ B → Δ ⊢ʰ H ∷ Γ ×
    Δ ⊢ wk ρ t [ H ]ₕ ∷ B ×
    Δ ⨾ H ⊢ S ⟨ wk ρ t ⟩∷ B ↝ A
  ⊢ₛ-inv (⊢ₛ ⊢H ⊢t ⊢S) =
    _ , _ , ⊢H , ⊢t , ⊢S

opaque

  -- Inversion of state typing with a non-empty stack.

  ⊢ₛ-inv′ :
    Δ ⊢ₛ ⟨ H , t , ρ , c ∙ S ⟩ ∷ A →
    ∃₃ λ Γ B C → Δ ⊢ʰ H ∷ Γ ×
    Δ ⊢ wk ρ t [ H ]ₕ ∷ B ×
    Δ ⨾ H ⊢ᶜ c ⟨ wk ρ t ⟩∷ B ↝ C ×
    Δ ⨾ H ⊢ S ⟨ ⦅ c ⦆ᶜ (wk ρ t) ⟩∷ C ↝ A
  ⊢ₛ-inv′ ⊢s =
    let _ , _ , ⊢H , ⊢t , ⊢eS = ⊢ₛ-inv ⊢s
        _ , ⊢c , ⊢S = ⊢ˢ-inv ⊢eS
    in  _ , _ , _ , (⊢H , ⊢t , ⊢c , ⊢S)
