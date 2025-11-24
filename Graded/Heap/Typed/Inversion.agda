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
open import Definition.Typed.Inversion TR
open import Definition.Typed.Properties TR
open import Definition.Typed.Substitution TR
open import Definition.Typed.Well-formed TR

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
  A B C D F G l s t u v w z : Term _
  p q q′ r : M
  ρ : Wk _ _
  S : Stack _
  e : Elim _
  s′ : Strength

opaque

  -- Inversion of lower

  inversion-lowerₑ :
    Δ ⨾ H ⊢ᵉ lowerₑ ⟨ t ⟩∷ A ↝ B →
    ∃₂ λ u F → (Δ ⊢ F) × A PE.≡ Lift u F × Δ ⊢ B ≡ F
  inversion-lowerₑ (lowerₑ ⊢B) =
    _ , _ , ⊢B , PE.refl , refl ⊢B
  inversion-lowerₑ (conv ⊢e B≡B′) =
    case inversion-lowerₑ ⊢e of λ
      (u , F , ⊢F , A≡Lift , B′≡) →
    -- _ , _ , _ , ⊢G , A≡Σ , trans (sym B≡B′) B′≡
    _ , _ , ⊢F , A≡Lift , trans (sym B≡B′) B′≡

opaque

  -- Inversion of application

  inversion-∘ₑ : Δ ⨾ H ⊢ᵉ ∘ₑ p u ρ ⟨ t ⟩∷ A ↝ B
               → ∃₃ λ F G q → Δ ⊢ wk ρ u [ H ]ₕ ∷ F
                 × A PE.≡ Π p , q ▷ F ▹ G
                 × Δ ⊢ B ≡ G [ wk ρ u [ H ]ₕ ]₀
  inversion-∘ₑ {H} (∘ₑ {ρ} {u} {A} {B} ⊢u ⊢B) =
    A , B , _ , ⊢u , PE.refl
      , refl (substType ⊢B ⊢u)
  inversion-∘ₑ (conv ⊢e B≡B′) =
    case inversion-∘ₑ ⊢e of λ
      (F , G , q , ⊢u , A≡Π , B≡) →
    F , G , _ , ⊢u , A≡Π , trans (sym B≡B′) B≡

opaque

  -- Inversion of fst

  inversion-fstₑ :
    Δ ⨾ H ⊢ᵉ fstₑ p ⟨ t ⟩∷ A ↝ B →
    ∃₃ λ F G q → (Δ ∙ F ⊢ G) × A PE.≡ Σˢ p , q ▷ F ▹ G × Δ ⊢ B ≡ F
  inversion-fstₑ (fstₑ ⊢B) =
    _ , _ , _ , ⊢B , PE.refl , refl (⊢∙→⊢ (wf ⊢B))
  inversion-fstₑ (conv ⊢e B≡B′) =
    case inversion-fstₑ ⊢e of λ
      (F , G , q , ⊢G , A≡Σ , B′≡) →
    _ , _ , _ , ⊢G , A≡Σ , trans (sym B≡B′) B′≡

opaque

  -- Inversion of snd

  inversion-sndₑ :
    Δ ⨾ H ⊢ᵉ sndₑ p ⟨ t ⟩∷ A ↝ B →
    ∃₃ λ F G q → (Δ ∙ F ⊢ G) × A PE.≡ Σˢ p , q ▷ F ▹ G ×
      (Δ ⊢ t [ H ]ₕ ∷ A → Δ ⊢ B ≡ G [ fst p t [ H ]ₕ ]₀)
  inversion-sndₑ (sndₑ ⊢B) =
    _ , _ , _ , ⊢B , PE.refl
      , λ ⊢t → refl (substType ⊢B (fstⱼ′ ⊢t))
  inversion-sndₑ (conv ⊢e B≡B′) =
    case inversion-sndₑ ⊢e of λ
      (F , G , q , ⊢G , A≡Σ , B≡Gt) →
    _ , _ , _ , ⊢G , A≡Σ
      , λ ⊢t → trans (sym B≡B′) (B≡Gt ⊢t)

opaque

  -- Inversion or prodrec

  inversion-prodrecₑ : Δ ⨾ H ⊢ᵉ prodrecₑ r p q A u ρ ⟨ t ⟩∷ B ↝ C
                     → ∃₃ λ F G q′
                       → Δ ∙ F ∙ G ⊢
                           wk (liftn ρ 2) u [ liftSubstn (toSubstₕ H) 2 ] ∷
                           (wk (lift ρ) A [ H ]⇑ₕ [ prodʷ p (var x1) (var x0) ]↑²)
                       × Δ ∙ Σʷ p , q′ ▷ F ▹ G ⊢ wk (lift ρ) A [ H ]⇑ₕ
                       × B PE.≡ Σʷ p , q′ ▷ F ▹ G
                       × (Δ ⊢ t [ H ]ₕ ∷ Σʷ p , q′ ▷ F ▹ G → Δ ⊢ C ≡ wk (lift ρ) A [ H ]⇑ₕ [ t [ H ]ₕ ]₀)
  inversion-prodrecₑ (prodrecₑ ⊢u ⊢A) =
    _ , _ , _ , ⊢u , ⊢A , PE.refl , λ ⊢t → refl (substType ⊢A ⊢t)
  inversion-prodrecₑ (conv ⊢e ≡C) =
    case inversion-prodrecₑ ⊢e of λ
      (_ , _ , _ , ⊢u , ⊢A , B≡ , C′≡) →
    _ , _ , _ , ⊢u , ⊢A , B≡ , λ ⊢t → trans (sym ≡C) (C′≡ ⊢t)

opaque

  -- Inversion of natrec

  inversion-natrecₑ : Δ ⨾ H ⊢ᵉ natrecₑ p q r A z s ρ ⟨ t ⟩∷ B ↝ C
                    → Δ ⊢ wk ρ z [ H ]ₕ ∷ wk (lift ρ) A [ H ]⇑ₕ [ zero ]₀
                    × Δ ∙ ℕ ∙ wk (lift ρ) A [ H ]⇑ₕ ⊢ wk (liftn ρ 2) s [ H ]⇑²ₕ ∷ wk (lift ρ) A [ H ]⇑ₕ [ suc (var x1) ]↑²
                    × B PE.≡ ℕ
                    × (Δ ⊢ t [ H ]ₕ ∷ ℕ → Δ ⊢ C ≡ wk (lift ρ) A [ H ]⇑ₕ [ t [ H ]ₕ ]₀)
  inversion-natrecₑ (natrecₑ ⊢z ⊢s) =
    ⊢z , ⊢s , PE.refl , λ ⊢t → refl (substType (⊢∙→⊢ (wfTerm ⊢s)) ⊢t)
  inversion-natrecₑ (conv ⊢e ≡C) =
    case inversion-natrecₑ ⊢e of λ
      (⊢z , ⊢s , B≡ , C′≡) →
    ⊢z , ⊢s , B≡ , λ ⊢t → trans (sym ≡C) (C′≡ ⊢t)

opaque

  -- Inversion of unitrec

  inversion-unitrecₑ :
    Δ ⨾ H ⊢ᵉ unitrecₑ p q A u ρ ⟨ t ⟩∷ B ↝ C →
    Δ ⊢ wk ρ u [ H ]ₕ ∷ wk (lift ρ) A [ H ]⇑ₕ [ starʷ ]₀ ×
    (Δ ∙ Unitʷ ⊢ wk (lift ρ) A [ H ]⇑ₕ) ×
    ¬ Unitʷ-η ×
    B PE.≡ Unitʷ ×
    (Δ ⊢ t [ H ]ₕ ∷ B → Δ ⊢ C ≡ wk (lift ρ) A [ H ]⇑ₕ [ t [ H ]ₕ ]₀)
  inversion-unitrecₑ {A} (unitrecₑ ⊢u ⊢A no-η) =
    ⊢u , ⊢A , no-η , PE.refl
       , λ ⊢t → refl (substType ⊢A ⊢t)
  inversion-unitrecₑ (conv ⊢e ≡C) =
    case inversion-unitrecₑ ⊢e of λ
      (⊢u , ⊢A , no-η , B≡ , C≡) →
    ⊢u , ⊢A , no-η , B≡ , λ ⊢t → trans (sym ≡C) (C≡ ⊢t)

opaque

  -- Inversion of emptyrec

  inversion-emptyrecₑ : Δ ⨾ H ⊢ᵉ emptyrecₑ p A ρ ⟨ t ⟩∷ B ↝ C
                      → Δ ⊢ wk ρ A [ H ]ₕ
                      × B PE.≡ Empty
                      × (Δ ⊢ C ≡ wk ρ A [ H ]ₕ)
  inversion-emptyrecₑ (emptyrecₑ ⊢A) =
    ⊢A , PE.refl , refl ⊢A
  inversion-emptyrecₑ (conv ⊢e ≡C) =
    case inversion-emptyrecₑ ⊢e of λ
      (⊢A , B≡ , C≡) →
    ⊢A , B≡ , trans (sym ≡C) C≡

opaque

  -- Inversion of J

  inversion-Jₑ : Δ ⨾ H ⊢ᵉ Jₑ p q A t B u v ρ ⟨ w ⟩∷ C ↝ D
               → Δ ⊢ wk ρ u [ H ]ₕ ∷ wk (liftn ρ 2) B [ liftSubstn (toSubstₕ H) 2 ] [ wk ρ t [ H ]ₕ , rfl ]₁₀
               × Δ ∙ wk ρ A [ H ]ₕ ∙ Id (wk1 (wk ρ A [ H ]ₕ)) (wk1 (wk ρ t [ H ]ₕ)) (var x0) ⊢ wk (liftn ρ 2) B [ liftSubstn (toSubstₕ H) 2 ]
               × C PE.≡ wk ρ (Id A t v) [ H ]ₕ
               × (Δ ⊢ w [ H ]ₕ ∷ wk ρ (Id A t v) [ H ]ₕ →
                  Δ ⊢ D ≡ wk (liftn ρ 2) B [ liftSubstn (toSubstₕ H) 2 ] [ wk ρ v [ H ]ₕ , w [ H ]ₕ ]₁₀)
  inversion-Jₑ (Jₑ ⊢u ⊢B) =
    ⊢u , ⊢B , PE.refl , λ ⊢w → refl (J-result ⊢B ⊢w)
  inversion-Jₑ (conv ⊢e ≡D) =
    case inversion-Jₑ ⊢e of λ
      (⊢u , ⊢B , C≡ , D′≡) →
    ⊢u , ⊢B , C≡ , λ ⊢w → trans (sym ≡D) (D′≡ ⊢w)

opaque

  -- Inversion of K

  inversion-Kₑ : Δ ⨾ H ⊢ᵉ Kₑ p A t B u ρ ⟨ v ⟩∷ C ↝ D
               → Δ ⊢ wk ρ u [ H ]ₕ ∷ wk (lift ρ) B [ H ]⇑ₕ [ rfl ]₀
               × Δ ∙ wk ρ (Id A t t) [ H ]ₕ ⊢ wk (lift ρ) B [ H ]⇑ₕ
               × K-allowed
               × C PE.≡ wk ρ (Id A t t) [ H ]ₕ
               × (Δ ⊢ v [ H ]ₕ ∷ wk ρ (Id A t t) [ H ]ₕ → Δ ⊢ D ≡ wk (lift ρ) B [ H ]⇑ₕ [ v [ H ]ₕ ]₀)
  inversion-Kₑ (Kₑ ⊢u ⊢B ok) =
    ⊢u , ⊢B , ok , PE.refl , λ ⊢v → refl (substType ⊢B ⊢v)
  inversion-Kₑ (conv ⊢e ≡D) =
    case inversion-Kₑ ⊢e of λ
      (⊢u , ⊢B , ok , C≡ , D′≡) →
    ⊢u , ⊢B , ok , C≡ , λ ⊢v → trans (sym ≡D) (D′≡ ⊢v)

opaque

  -- Inversion of []-cong

  inversion-[]-congₑ :
    Δ ⨾ H ⊢ᵉ []-congₑ s′ l A t u ρ ⟨ v ⟩∷ B ↝ C →
    let module E′ = E s′ in
    []-cong-allowed s′ ×
    Δ ⊢ wk ρ l [ H ]ₕ ∷Level ×
    B PE.≡ wk ρ (Id A t u) [ H ]ₕ ×
    (Δ ⊢ wk ρ t [ H ]ₕ ∷ wk ρ A [ H ]ₕ →
     Δ ⊢ wk ρ u [ H ]ₕ ∷ wk ρ A [ H ]ₕ →
     Δ ⊢ C ≡
       Id (E′.Erased (wk ρ l [ H ]ₕ) (wk ρ A [ H ]ₕ))
         E′.[ wk ρ t [ H ]ₕ ] E′.[ wk ρ u [ H ]ₕ ])
  inversion-[]-congₑ ([]-congₑ {s′} ok ⊢l) =
    let E-ok = []-cong→Erased ok in
    ok , ⊢l , PE.refl ,
    λ ⊢t ⊢u →
      PE.subst₂ (_⊢_≡_ _) wk-Id-Erased-[]-[] PE.refl $
      _⊢_≡_.refl $
      Idⱼ′ ([]ⱼ E-ok ⊢l ⊢t) ([]ⱼ E-ok ⊢l ⊢u)
    where
    open E s′
  inversion-[]-congₑ (conv ⊢e ≡C) =
    case inversion-[]-congₑ ⊢e of λ
      (ok , ⊢l , B≡ , C′≡) →
    ok , ⊢l , B≡ , λ ⊢t ⊢u → trans (sym ≡C) (C′≡ ⊢t ⊢u)

opaque

  -- Inversion of suc

  inversion-sucₑ : Δ ⨾ H ⊢ᵉ sucₑ ⟨ t ⟩∷ A ↝ B → ⊥
  inversion-sucₑ (conv ⊢e _) = inversion-sucₑ ⊢e

opaque

  -- Inversion of stack typing

  ⊢ˢ-inv :
    Δ ⨾ H ⊢ e ∙ S ⟨ t ⟩∷ A ↝ B →
    ∃ λ C → Δ ⨾ H ⊢ᵉ e ⟨ t ⟩∷ A ↝ C ×
    (Δ ⨾ H ⊢ S ⟨ ⦅ e ⦆ᵉ t ⟩∷ C ↝ B)
  ⊢ˢ-inv (⊢e ∙ ⊢S) = _ , ⊢e , ⊢S

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
    Δ ⊢ₛ ⟨ H , t , ρ , e ∙ S ⟩ ∷ A →
    ∃₃ λ Γ B C → Δ ⊢ʰ H ∷ Γ ×
    Δ ⊢ wk ρ t [ H ]ₕ ∷ B ×
    Δ ⨾ H ⊢ᵉ e ⟨ wk ρ t ⟩∷ B ↝ C ×
    Δ ⨾ H ⊢ S ⟨ ⦅ e ⦆ᵉ (wk ρ t) ⟩∷ C ↝ A
  ⊢ₛ-inv′ ⊢s =
    let _ , _ , ⊢H , ⊢t , ⊢eS = ⊢ₛ-inv ⊢s
        _ , ⊢e , ⊢S = ⊢ˢ-inv ⊢eS
    in  _ , _ , _ , (⊢H , ⊢t , ⊢e , ⊢S)
