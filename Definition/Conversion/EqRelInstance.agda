------------------------------------------------------------------------
-- The algorithmic equality is (in the absence of equality reflection)
-- an instance of the abstract set of equality relations
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Conversion.EqRelInstance
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  ⦃ no-equality-reflection : No-equality-reflection ⦄
  where

open import Definition.Untyped M
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.EqRelInstance R
  using () renaming (eqRelInstance to eqRelInstance′)
open import Definition.Typed.EqualityRelation.Instance R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Stability R
open import Definition.Typed.Substitution R
open import Definition.Typed.Syntactic R
open import Definition.Typed.Weakening R using (_∷ʷ_⊇_; wkEq)
open import Definition.Typed.Well-formed R
open import Definition.Conversion R
open import Definition.Conversion.Level R
open import Definition.Conversion.Reduction R
open import Definition.Conversion.Universe R
open import Definition.Conversion.Stability R
open import Definition.Conversion.Soundness R
open import Definition.Conversion.Lift R
open import Definition.Conversion.Conversion R
open import Definition.Conversion.Inversion R
open import Definition.Conversion.Symmetry R
open import Definition.Conversion.Transitivity R
open import Definition.Conversion.Weakening R
open import Definition.Conversion.Whnf R
open import Definition.Typed.EqualityRelation R
import Definition.Typed.EqualityRelation.Instance
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Consequences.Equality R
open import Definition.Typed.Consequences.Reduction R

open import Tools.Bool
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Level hiding (Level)
open import Tools.Nat
open import Tools.Product
open import Tools.Sum
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Unit

import Data.List as L
import Data.List.Properties as L
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.All.Properties as All
import Data.List.Relation.Unary.Any as Any
import Data.List.Relation.Unary.Any.Properties as Any

private
  variable
    m n : Nat
    Γ : Con Term n
    A₁ A₂ B₁ B₂ l l′ t t′ t₁ t₂ u u′ u₁ u₂ v v₁ v₂ w₁ w₂ : Term _
    ρ : Wk m n
    p p₁ p₂ p′ q q′ q₁ q₂ r r′ : M
    s : Strength
    d : Bool

opaque

  star-cong′ :
    Γ ⊢ l [conv↑] l′ ∷ Level → Unit-allowed s → Γ ⊢ star s l [conv↓] star s l′ ∷ Unit s l
  star-cong′ {s} l≡l′ ok =
    let ⊢l≡l′ = soundnessConv↑Term l≡l′
        ⊢Level , ⊢l , ⊢l′ = syntacticEqTerm ⊢l≡l′
    in case Unit-with-η? s of λ where
      (inj₂ (PE.refl , no-η)) → starʷ-cong (refl ⊢l) ⊢l≡l′ ok no-η
      (inj₁ η)                →
        η-unit ⊢l (starⱼ ⊢l ok) (conv (starⱼ ⊢l′ ok) (Unit-cong (sym ⊢Level ⊢l≡l′) ok))
          starₙ starₙ ok η

-- Properties of algorithmic equality of neutrals with injected conversion.

private module Lemmas where

  ~-var : ∀ {x A} → Γ ⊢ var x ∷ A → Γ ⊢ var x ~ var x ∷ A
  ~-var x =
    let ⊢A = syntacticTerm x
    in  ↑ (refl ⊢A) (var-refl x PE.refl)

  ~-app : ∀ {f g a b F G}
        → Γ ⊢ f ~ g ∷ Π p , q ▷ F ▹ G
        → Γ ⊢ a [conv↑] b ∷ F
        → Γ ⊢ f ∘⟨ p ⟩ a ~ g ∘⟨ p ⟩ b ∷ G [ a ]₀
  ~-app (↑ A≡B x) x₁ =
    let _ , ⊢B = syntacticEq A≡B
        B′ , whnfB′ , D = whNorm ⊢B
        ΠFG≡B′ = trans A≡B (subset* D)
        _ , ⊢f , _ = syntacticEqTerm (soundnessConv↑Term x₁)
    in
    case Π≡A ΠFG≡B′ whnfB′ of λ {
      (H , E , B≡ΠHE) →
    case ΠΣ-injectivity (PE.subst (λ x → _ ⊢ _ ≡ x) B≡ΠHE ΠFG≡B′) of λ {
      (F≡H , G≡E , _ , _) →
    ↑ (G≡E (refl ⊢f))
      (app-cong
         (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) B≡ΠHE
            ([~] _ (D , whnfB′) x))
         (convConv↑Term F≡H x₁)) }}

  ~-fst :
    ∀ {p r F G} →
    Γ ⊢ p ~ r ∷ Σˢ p′ , q ▷ F ▹ G →
    Γ ⊢ fst p′ p ~ fst p′ r ∷ F
  ~-fst (↑ A≡B p~r) =
    case syntacticEq A≡B of λ (_ , ⊢B) →
    case whNorm ⊢B of λ (B′ , whnfB′ , D) →
    case trans A≡B (subset* D) of λ ΣFG≡B′ →
    case Σ≡A ΣFG≡B′ whnfB′ of λ where
      (H , _ , PE.refl) →
        case ΠΣ-injectivity ΣFG≡B′ of λ where
          (F≡H , _ , _ , _) →
            ↑ F≡H (fst-cong ([~] _ (D , whnfB′) p~r))

  ~-snd :
    ∀ {p r F G} →
    Γ ⊢ p ~ r ∷ Σ p′ , q ▷ F ▹ G →
    Γ ⊢ snd p′ p ~ snd p′ r ∷ G [ fst p′ p ]₀
  ~-snd (↑ A≡B p~r) =
    case syntacticEq A≡B of λ (⊢ΣFG , ⊢B) →
    case whNorm ⊢B of λ (B′ , whnfB′ , D) →
    case trans A≡B (subset* D) of λ ΣFG≡B′ →
    case Σ≡A ΣFG≡B′ whnfB′ of λ where
      (_ , E , PE.refl) →
        case ΠΣ-injectivity ΣFG≡B′ of λ where
          (_ , G≡E , _ , _) →
            let p~r↓       = [~] _ (D , whnfB′) p~r
                _ , ⊢G , _ = inversion-ΠΣ ⊢ΣFG
                _ , ⊢p , _ = syntacticEqTerm (soundness~↑ p~r)
                ⊢fst       = fstⱼ ⊢G (conv ⊢p (sym A≡B))
            in
            ↑ (G≡E (refl ⊢fst)) (snd-cong p~r↓)

  ~-natrec : ∀ {z z′ s s′ n n′ F F′}
           → (Γ ∙ ℕ) ⊢ F [conv↑] F′ →
        Γ ⊢ z [conv↑] z′ ∷ (F [ zero ]₀) →
        Γ ∙ ℕ ∙ F ⊢ s [conv↑] s′ ∷ F [ suc (var x1) ]↑² →
        Γ ⊢ n ~ n′ ∷ ℕ →
        Γ ⊢ natrec p q r F z s n ~ natrec p q r F′ z′ s′ n′ ∷ (F [ n ]₀)
  ~-natrec x x₁ x₂ (↑ A≡B x₄) =
    let _ , ⊢B = syntacticEq A≡B
        B′ , whnfB′ , D = whNorm ⊢B
        ℕ≡B′ = trans A≡B (subset* D)
        B≡ℕ = ℕ≡A ℕ≡B′ whnfB′
        k~l′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) B≡ℕ
                        ([~] _ (D , whnfB′) x₄)
        ⊢F , _ = syntacticEq (soundnessConv↑ x)
        _ , ⊢n , _ = syntacticEqTerm (soundness~↓ k~l′)
    in  ↑ (refl (substType ⊢F ⊢n))
          (natrec-cong x x₁ x₂ k~l′)

  ~-prodrec :
    ∀ {F G A A′ t t′ u u′} →
    Γ ∙ (Σʷ p , q ▷ F ▹ G) ⊢ A [conv↑] A′ →
    Γ ⊢ t ~ t′ ∷ (Σʷ p , q ▷ F ▹ G) →
    Γ ∙ F ∙ G ⊢ u [conv↑] u′ ∷ A [ prodʷ p (var x1) (var x0) ]↑² →
    Γ ⊢ prodrec r p q′ A t u ~ prodrec r p q′ A′ t′ u′ ∷ (A [ t ]₀)
  ~-prodrec x₂ (↑ A≡B k~↑l) x₄ =
    case syntacticEq A≡B of λ (_ , ⊢B) →
    case whNorm ⊢B of λ (B′ , whnfB′ , D) →
    case _⊢_≡_.trans A≡B (subset* D) of λ Σ≡Σ′ →
    case Σ≡A (trans A≡B (subset* D)) whnfB′ of λ where
      (F′ , G′ , PE.refl) →
        case ΠΣ-injectivity-no-equality-reflection Σ≡Σ′ of λ where
          (F≡F′ , G≡G′ , _ , _ , _) →
            let t~t′       = [~] _ (D , whnfB′) k~↑l
                ⊢A , _     = syntacticEq (soundnessConv↑ x₂)
                _ , ⊢t , _ = syntacticEqTerm (soundness~↑ k~↑l)
            in
            ↑ (refl (substType ⊢A (conv ⊢t (sym A≡B))))
              (prodrec-cong (stabilityConv↑ (refl-∙ Σ≡Σ′) x₂)
                 t~t′ (stabilityConv↑Term (refl-∙ F≡F′ ∙ G≡G′) x₄))

  ~-emptyrec : ∀ {n n′ F F′}
           → Γ ⊢ F [conv↑] F′ →
        Γ ⊢ n ~ n′ ∷ Empty →
        Γ ⊢ emptyrec p F n ~ emptyrec p F′ n′ ∷ F
  ~-emptyrec x (↑ A≡B x₄) =
    let _ , ⊢B = syntacticEq A≡B
        B′ , whnfB′ , D = whNorm ⊢B
        Empty≡B′ = trans A≡B (subset* D)
        B≡Empty = Empty≡A Empty≡B′ whnfB′
        k~l′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x) B≡Empty
                        ([~] _ (D , whnfB′) x₄)
        ⊢F , _ = syntacticEq (soundnessConv↑ x)
        _ , ⊢n , _ = syntacticEqTerm (soundness~↓ k~l′)
    in  ↑ (refl ⊢F)
          (emptyrec-cong x k~l′)

  ~-unitrec : ∀ {A A′ t t′ u u′}
            → Γ ⊢ l ∷ Level
            → Γ ⊢ l′ ∷ Level
            → Γ ⊢ l [conv↑] l′ ∷ Level
            → Γ ∙ Unitʷ l ⊢ A [conv↑] A′
            → Γ ⊢ t ~ t′ ∷ Unitʷ l
            → Γ ⊢ u [conv↑] u′ ∷ A [ starʷ l ]₀
            → Unitʷ-allowed
            → ¬ Unitʷ-η
            → Γ ⊢ unitrec p q l A t u ~ unitrec p q l′ A′ t′ u′ ∷
                A [ t ]₀
  ~-unitrec ⊢l ⊢l′ l≡l′ A<>A′ t~t′ u<>u′ ok no-η =
    let ⊢A , _ = syntacticEq (soundnessConv↑ A<>A′)
        _ , ⊢t , _ = syntacticEqTerm (soundness~∷ t~t′)
    in ↑ (refl (substType ⊢A ⊢t))
         (unitrec-cong l≡l′ A<>A′ t~t′ u<>u′ no-η)

  opaque

    ~-J :
      Γ ⊢ A₁ [conv↑] A₂ →
      Γ ⊢ t₁ ∷ A₁ →
      Γ ⊢ t₁ [conv↑] t₂ ∷ A₁ →
      Γ ∙ A₁ ∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊢ B₁ [conv↑] B₂ →
      Γ ⊢ u₁ [conv↑] u₂ ∷ B₁ [ t₁ , rfl ]₁₀ →
      Γ ⊢ v₁ [conv↑] v₂ ∷ A₁ →
      Γ ⊢ w₁ ~ w₂ ∷ Id A₁ t₁ v₁ →
      Γ ⊢ J p q A₁ t₁ B₁ u₁ v₁ w₁ ~ J p q A₂ t₂ B₂ u₂ v₂ w₂ ∷
        B₁ [ v₁ , w₁ ]₁₀
    ~-J A₁≡A₂ _ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ (↑ Id-t₁-v₁≡C w₁~w₂) =
      case Id-norm (sym Id-t₁-v₁≡C) of λ {
        (_ , _ , _ , C⇒*Id-t₃-v₃ , A₁≡A₃ , t₁≡t₃ , v₁≡v₃) →
      ↑ (refl $
         substType₂ (syntacticEq (soundnessConv↑ B₁≡B₂) .proj₁)
           (syntacticEqTerm v₁≡v₃ .proj₂ .proj₁)
           (conv (syntacticEqTerm (soundness~↑ w₁~w₂) .proj₂ .proj₁) $
            PE.subst (_⊢_≡_ _ _) ≡Id-wk1-wk1-0[]₀ $
            sym Id-t₁-v₁≡C))
        (J-cong A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂
           ([~] _ (C⇒*Id-t₃-v₃ , Idₙ) w₁~w₂)
           (trans (sym (subset* C⇒*Id-t₃-v₃)) (sym Id-t₁-v₁≡C))) }

    ~-K :
      Γ ⊢ A₁ [conv↑] A₂ →
      Γ ⊢ t₁ [conv↑] t₂ ∷ A₁ →
      Γ ∙ Id A₁ t₁ t₁ ⊢ B₁ [conv↑] B₂ →
      Γ ⊢ u₁ [conv↑] u₂ ∷ B₁ [ rfl ]₀ →
      Γ ⊢ v₁ ~ v₂ ∷ Id A₁ t₁ t₁ →
      K-allowed →
      Γ ⊢ K p A₁ t₁ B₁ u₁ v₁ ~ K p A₂ t₂ B₂ u₂ v₂ ∷ B₁ [ v₁ ]₀
    ~-K A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ (↑ Id-t₁-t₁≡C v₁~v₂) ok =
      case Id-norm (sym Id-t₁-t₁≡C) of λ {
        (_ , _ , _ , C⇒*Id-t₃-t₄ , A₁≡A₃ , t₁≡t₃ , t₁≡t₄) →
      ↑ (refl $
         substType (syntacticEq (soundnessConv↑ B₁≡B₂) .proj₁) $
         _⊢_∷_.conv
           (syntacticEqTerm (soundness~↑ v₁~v₂) .proj₂ .proj₁) $
         sym Id-t₁-t₁≡C)
        (K-cong A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂
           ([~] _ (C⇒*Id-t₃-t₄ , Idₙ) v₁~v₂)
           (trans (sym (subset* C⇒*Id-t₃-t₄)) (sym Id-t₁-t₁≡C)) ok) }

    ~-[]-cong :
      Γ ⊢ A₁ [conv↑] A₂ →
      Γ ⊢ t₁ [conv↑] t₂ ∷ A₁ →
      Γ ⊢ u₁ [conv↑] u₂ ∷ A₁ →
      Γ ⊢ v₁ ~ v₂ ∷ Id A₁ t₁ u₁ →
      []-cong-allowed s →
      let open Erased s in
      Γ ⊢ []-cong s A₁ t₁ u₁ v₁ ~ []-cong s A₂ t₂ u₂ v₂ ∷
        Id (Erased A₁) ([ t₁ ]) ([ u₁ ])
    ~-[]-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ (↑ Id-t₁-u₁≡B v₁~v₂) ok =
      case Id-norm (sym Id-t₁-u₁≡B) of λ {
        (_ , _ , _ , B⇒*Id-t₃-u₃ , A₁≡A₃ , t₁≡t₃ , u₁≡u₃) →
      ↑ (_⊢_≡_.refl $
         Idⱼ′
           ([]ⱼ ([]-cong→Erased ok)
              (syntacticEqTerm t₁≡t₃ .proj₂ .proj₁))
           ([]ⱼ ([]-cong→Erased ok)
              (syntacticEqTerm u₁≡u₃ .proj₂ .proj₁)))
        ([]-cong-cong A₁≡A₂ t₁≡t₂ u₁≡u₂
           ([~] _ (B⇒*Id-t₃-u₃ , Idₙ) v₁~v₂)
           (trans (sym (subset* B⇒*Id-t₃-u₃)) (sym Id-t₁-u₁≡B))
           ok) }

  ~-sym : ∀ {k l A} → Γ ⊢ k ~ l ∷ A → Γ ⊢ l ~ k ∷ A
  ~-sym x@(↑ A≡B _) = sym~∷ (reflConEq (wfEq A≡B)) x

  ~-trans : ∀ {k l m A}
          → Γ ⊢ k ~ l ∷ A → Γ ⊢ l ~ m ∷ A
          → Γ ⊢ k ~ m ∷ A
  ~-trans x y = trans~∷ x y .proj₁

  ~-wk : ∀ {k l A} {ρ : Wk m n} {Γ Δ} →
        ρ ∷ʷ Δ ⊇ Γ →
        Γ ⊢ k ~ l ∷ A → Δ ⊢ wk ρ k ~ wk ρ l ∷ wk ρ A
  ~-wk = wk~∷

  ~-conv : ∀ {k l A B} →
        Γ ⊢ k ~ l ∷ A → Γ ⊢ A ≡ B → Γ ⊢ k ~ l ∷ B
  ~-conv (↑ x x₁) x₂ = ↑ (trans (sym x₂) x) x₁

  ~-to-conv : ∀ {k l A} →
        Γ ⊢ k ~ l ∷ A → Γ ⊢ k [conv↑] l ∷ A
  ~-to-conv (↑ x x₁) = convConv↑Term (sym x) (lift~toConv↑ x₁)

  ≅ₜ-sucᵘ-cong : Γ ⊢ t [conv↑] u ∷ Level → Γ ⊢ sucᵘ t [conv↓] sucᵘ u ∷Level
  ≅ₜ-sucᵘ-cong ([↑]ₜ B t′ u′ (D , _) d d′ t<>u) =
    case whnfRed* D Levelₙ of λ {
      PE.refl →
    let [↓]ˡ tᵛ uᵛ t≡ u≡ t≡u = inv-[conv↓]∷-Level t<>u
    in [↓]ˡ (sucᵛ tᵛ) (sucᵛ uᵛ)
      (sucᵘ-↓ᵛ PE.refl ([↑]ᵛ d t≡))
      (sucᵘ-↓ᵛ PE.refl ([↑]ᵛ d′ u≡))
      (≡ᵛ-suc t≡u) }

  maxᵘ-↑ᵛ : ∀ {v′ v″} → Γ ⊢ t ↑ᵛ v′ → Γ ⊢ u ↑ᵛ v″ → ∃ λ v → Γ ⊢ t maxᵘ u ↑ᵛ v × v ≡ᵛ maxᵛ v′ v″
  maxᵘ-↑ᵛ {v′} {v″} ([↑]ᵛ (t⇒ , tw) t↓) u↑@([↑]ᵛ (u⇒ , uw) u↓) =
    let ⊢u = redFirst*Term u⇒
    in case t↓ of λ where
      (zeroᵘ-↓ᵛ _) → v″ , [↑]ᵛ (maxᵘ-substˡ* t⇒ ⊢u ⇨∷* (maxᵘ-zeroˡ ⊢u ⇨ u⇒) , uw) u↓ , ≡ᵛ-maxᵘ-zeroˡ
      (sucᵘ-↓ᵛ {v′ = v₁} PE.refl t′↑) →
        let ⊢t′ = wf↑ᵛ t′↑
        in case u↓ of λ where
          (zeroᵘ-↓ᵛ _) → v′ , [↑]ᵛ (maxᵘ-substˡ* t⇒ ⊢u ⇨∷* (maxᵘ-substʳ* ⊢t′ u⇒ ⇨∷* redMany (maxᵘ-zeroʳ ⊢t′)) , sucᵘₙ) t↓ , sym-≡ᵛ ≡ᵛ-maxᵘ-zeroʳ
          (sucᵘ-↓ᵛ PE.refl u′↑) →
            let ⊢u′ = wf↑ᵛ u′↑
                a , a↑ , a≡ = maxᵘ-↑ᵛ t′↑ u′↑
            in sucᵛ a , [↑]ᵛ (maxᵘ-substˡ* t⇒ ⊢u ⇨∷* (maxᵘ-substʳ* ⊢t′ u⇒ ⇨∷* redMany (maxᵘ-sucᵘ ⊢t′ ⊢u′)) , sucᵘₙ) (sucᵘ-↓ᵛ PE.refl a↑) , trans-≡ᵛ (≡ᵛ-suc a≡) ≡ᵛ-maxᵘ-sucᵘ
          (maxᵘ-↓ᵛ (ne x) PE.refl u′↑ u″↑) →
            let w = ne (maxᵘʳₙ x)
            in maxᵛ v′ v″ , [↑]ᵛ (maxᵘ-substˡ* t⇒ ⊢u ⇨∷* maxᵘ-substʳ* ⊢t′ u⇒ , w) (maxᵘ-↓ᵛ w PE.refl (lift-↓ᵛ t↓) (lift-↓ᵛ u↓)) , ≡ᵛ-refl _
          (ne-↓ᵛ [t] x) →
            let w = ne (maxᵘʳₙ (ne (ne~↓ [t] .proj₂ .proj₁)))
            in maxᵛ v′ v″ , [↑]ᵛ (maxᵘ-substˡ* t⇒ ⊢u ⇨∷* maxᵘ-substʳ* ⊢t′ u⇒ , w) (maxᵘ-↓ᵛ w PE.refl (lift-↓ᵛ t↓) (lift-↓ᵛ u↓)) , ≡ᵛ-refl _
      (maxᵘ-↓ᵛ (ne x) x₁ x₂ x₃) →
        let w = ne (maxᵘˡₙ x)
        in maxᵛ v′ v″ , [↑]ᵛ (maxᵘ-substˡ* t⇒ ⊢u , w) (maxᵘ-↓ᵛ w PE.refl (lift-↓ᵛ t↓) u↑) , ≡ᵛ-refl _
      (ne-↓ᵛ [t] x) →
        let w = ne (maxᵘˡₙ (ne (ne~↓ [t] .proj₂ .proj₁)))
        in maxᵛ v′ v″ , [↑]ᵛ (maxᵘ-substˡ* t⇒ ⊢u , w) (maxᵘ-↓ᵛ w PE.refl (lift-↓ᵛ t↓) u↑) , ≡ᵛ-refl _

  ≅ₜ-maxᵘ-cong : Γ ⊢ t [conv↑] u ∷Level → Γ ⊢ t′ [conv↑] u′ ∷Level → Γ ⊢ t maxᵘ t′ [conv↑] u maxᵘ u′ ∷Level
  ≅ₜ-maxᵘ-cong ([↑]ˡ tᵛ uᵛ t↑ u↑ t≡u) ([↑]ˡ tᵛ₁ uᵛ₁ t↑₁ u↑₁ t≡u₁) =
    let [a] , a↑ , a≡ = maxᵘ-↑ᵛ t↑ t↑₁
        [b] , b↑ , b≡ = maxᵘ-↑ᵛ u↑ u↑₁
    in [↑]ˡ [a] [b] a↑ b↑ (trans-≡ᵛ a≡ (trans-≡ᵛ (≡ᵛ-max t≡u t≡u₁) (sym-≡ᵛ b≡)))

  zeroᵘ-↑ᵛ : ⊢ Γ → Γ ⊢ zeroᵘ ↑ᵛ zeroᵛ
  zeroᵘ-↑ᵛ ⊢Γ = [↑]ᵛ (id (zeroᵘⱼ ⊢Γ) , zeroᵘₙ) (zeroᵘ-↓ᵛ ⊢Γ)

  ≅ₜ-maxᵘ-zeroʳ : Γ ⊢ t [conv↑] t ∷Level → Γ ⊢ t maxᵘ zeroᵘ [conv↑] t ∷Level
  ≅ₜ-maxᵘ-zeroʳ ([↑]ˡ v _ t↑ _ _) =
    let v′ , x , y = maxᵘ-↑ᵛ t↑ (zeroᵘ-↑ᵛ (wfTerm (wf↑ᵛ t↑)))
    in [↑]ˡ _ _ x t↑ (trans-≡ᵛ y ≡ᵛ-maxᵘ-zeroʳ)

  ≅ₜ-maxᵘ-assoc : Γ ⊢ t [conv↑] t ∷Level → Γ ⊢ u [conv↑] u ∷Level → Γ ⊢ v [conv↑] v ∷Level → Γ ⊢ (t maxᵘ u) maxᵘ v [conv↑] t maxᵘ (u maxᵘ v) ∷Level
  ≅ₜ-maxᵘ-assoc ([↑]ˡ tᵛ _ t↑ _ _) ([↑]ˡ uᵛ _ u↑ _ _) ([↑]ˡ vᵛ _ v↑ _ _) =
    let tuᵛ , tu↑ , tu≡ = maxᵘ-↑ᵛ t↑ u↑
        uvᵛ , uv↑ , uv≡ = maxᵘ-↑ᵛ u↑ v↑
        [tu]vᵛ , [tu]v↑ , [tu]v≡ = maxᵘ-↑ᵛ tu↑ v↑
        t[uv]ᵛ , t[uv]↑ , t[uv]≡ = maxᵘ-↑ᵛ t↑ uv↑
    in [↑]ˡ [tu]vᵛ t[uv]ᵛ [tu]v↑ t[uv]↑
    $ trans-≡ᵛ [tu]v≡
    $ trans-≡ᵛ (≡ᵛ-max tu≡ (≡ᵛ-refl _))
    $ trans-≡ᵛ (≡ᵛ-maxᵘ-assoc {a = tᵛ} {b = uᵛ} {c = vᵛ})
    $ trans-≡ᵛ (≡ᵛ-max (≡ᵛ-refl _) (sym-≡ᵛ uv≡))
    $ sym-≡ᵛ t[uv]≡

  ≅ₜ-maxᵘ-comm : Γ ⊢ t [conv↑] t ∷Level → Γ ⊢ u [conv↑] u ∷Level →  Γ ⊢ t maxᵘ u [conv↑] u maxᵘ t ∷Level
  ≅ₜ-maxᵘ-comm ([↑]ˡ tᵛ _ t↑ _ _) ([↑]ˡ uᵛ _ u↑ _ _) =
    let tuᵛ , tu↑ , tu≡ = maxᵘ-↑ᵛ t↑ u↑
        utᵛ , ut↑ , ut≡ = maxᵘ-↑ᵛ u↑ t↑
    in [↑]ˡ tuᵛ utᵛ tu↑ ut↑ (trans-≡ᵛ tu≡ (trans-≡ᵛ (≡ᵛ-maxᵘ-comm {a = tᵛ}) (sym-≡ᵛ ut≡)))

  ≅ₜ-maxᵘ-idem : Γ ⊢ t [conv↑] t ∷Level →  Γ ⊢ t maxᵘ t [conv↑] t ∷Level
  ≅ₜ-maxᵘ-idem ([↑]ˡ tᵛ _ t↑ _ _) =
    let ttᵛ , tt↑ , tt≡ = maxᵘ-↑ᵛ t↑ t↑
    in [↑]ˡ ttᵛ tᵛ tt↑ t↑ (trans-≡ᵛ tt≡ ≡ᵛ-maxᵘ-idem)

  ≅ₜ-maxᵘ-sub : Γ ⊢ t [conv↑] t ∷Level →  Γ ⊢ t maxᵘ sucᵘ t [conv↑] sucᵘ t ∷Level
  ≅ₜ-maxᵘ-sub ([↑]ˡ tᵛ _ t↑ _ _) =
    let t+1↑ = lift-↓ᵛ (sucᵘ-↓ᵛ PE.refl t↑)
        ttᵛ , tt↑ , tt≡ = maxᵘ-↑ᵛ t↑ t+1↑
    in [↑]ˡ ttᵛ (sucᵛ tᵛ) tt↑ t+1↑ (trans-≡ᵛ tt≡ ≡ᵛ-maxᵘ-sub)

private opaque

  -- A lemma used below.

  equality-relations :
    Equality-relations _⊢_[conv↑]_ _⊢_[conv↑]_∷_ _⊢_~_∷_ (Lift _ ⊤)
  equality-relations = let open Lemmas in λ where
    .Equality-relations.Neutrals-included? →
      yes (lift tt)
    .Equality-relations.Equality-reflection-allowed→¬Neutrals-included →
      λ ok _ → No-equality-reflection⇔ .proj₁ no-equality-reflection ok
    .Equality-relations.⊢≡→⊢≅    → ⊥-elim ∘→ (_$ _)
    .Equality-relations.⊢≡∷→⊢≅∷  → ⊥-elim ∘→ (_$ _)
    .Equality-relations.~-to-≅ₜ  → ~-to-conv
    .Equality-relations.≅-eq     → soundnessConv↑
    .Equality-relations.≅ₜ-eq    → soundnessConv↑Term
    .Equality-relations.≅-univ   → univConv↑
    .Equality-relations.≅-sym    → symConv
    .Equality-relations.≅ₜ-sym   → symConvTerm
    .Equality-relations.~-sym    → ~-sym
    .Equality-relations.≅-trans  → transConv
    .Equality-relations.≅ₜ-trans → transConvTerm
    .Equality-relations.~-trans  → ~-trans
    .Equality-relations.≅-conv   → flip convConv↑Term
    .Equality-relations.~-conv   → ~-conv
    .Equality-relations.≅-wk     → wkConv↑
    .Equality-relations.≅ₜ-wk    → wkConv↑Term
    .Equality-relations.~-wk     → ~-wk
    .Equality-relations.≅-red    →
      λ (A⇒* , _) (B⇒* , _) → reductionConv↑ A⇒* B⇒*
    .Equality-relations.≅ₜ-red   →
      λ (A⇒* , _) (t⇒* , _) (u⇒* , _) → reductionConv↑Term A⇒* t⇒* u⇒*
    .Equality-relations.≅ₜ-Levelrefl →
      λ x → liftConvTerm (univ (Levelⱼ x) (Levelⱼ x) (Level-refl x))
    .Equality-relations.≅ₜ-zeroᵘrefl →
      liftConvTerm ∘ᶠ Level-ins ∘ᶠ zeroᵘrefl
    .Equality-relations.≅ₜ-sucᵘ-cong →
      liftConvTerm ∘ᶠ Level-ins ∘ᶠ ≅ₜ-sucᵘ-cong
    .Equality-relations.≅ₜ-maxᵘ-cong → λ a b → inv-[conv↑]∷-Level⇔ .proj₂ (≅ₜ-maxᵘ-cong (inv-[conv↑]∷-Level⇔ .proj₁ a) (inv-[conv↑]∷-Level⇔ .proj₁ b))
    .Equality-relations.≅ₜ-maxᵘ-zeroʳ → λ a → inv-[conv↑]∷-Level⇔ .proj₂ (≅ₜ-maxᵘ-zeroʳ (inv-[conv↑]∷-Level⇔ .proj₁ a))
    .Equality-relations.≅ₜ-maxᵘ-assoc →
      λ a b c → inv-[conv↑]∷-Level⇔ .proj₂ (≅ₜ-maxᵘ-assoc (inv-[conv↑]∷-Level⇔ .proj₁ a) (inv-[conv↑]∷-Level⇔ .proj₁ b) (inv-[conv↑]∷-Level⇔ .proj₁ c))
    .Equality-relations.≅ₜ-maxᵘ-comm →
      λ a b → inv-[conv↑]∷-Level⇔ .proj₂ (≅ₜ-maxᵘ-comm (inv-[conv↑]∷-Level⇔ .proj₁ a) (inv-[conv↑]∷-Level⇔ .proj₁ b))
    .Equality-relations.≅ₜ-maxᵘ-idem →
      λ a → inv-[conv↑]∷-Level⇔ .proj₂ (≅ₜ-maxᵘ-idem (inv-[conv↑]∷-Level⇔ .proj₁ a))
    .Equality-relations.≅ₜ-maxᵘ-sub →
      λ a → inv-[conv↑]∷-Level⇔ .proj₂ (≅ₜ-maxᵘ-sub (inv-[conv↑]∷-Level⇔ .proj₁ a))
    .Equality-relations.≅ₜ-U-cong →
      λ l≡l′ →
        let ⊢l≡l′ = soundnessConv↑Term l≡l′
            ⊢Level , ⊢l , ⊢l′ = syntacticEqTerm ⊢l≡l′
        in liftConvTerm (univ (Uⱼ ⊢l) (conv (Uⱼ ⊢l′) (U-cong (sucᵘ-cong (sym ⊢Level ⊢l≡l′)))) (U-cong l≡l′))
    .Equality-relations.≅ₜ-ℕrefl →
      λ x → liftConvTerm (univ (ℕⱼ x) (ℕⱼ x) (ℕ-refl x))
    .Equality-relations.≅ₜ-Emptyrefl →
      λ x → liftConvTerm (univ (Emptyⱼ x) (Emptyⱼ x) (Empty-refl x))
    .Equality-relations.≅ₜ-Unit-cong →
      λ l≡l′ ok →
        let ⊢l≡l′ = soundnessConv↑Term l≡l′
            ⊢Level , ⊢l , ⊢l′ = syntacticEqTerm ⊢l≡l′
        in liftConvTerm $
        univ (Unitⱼ ⊢l ok) (conv (Unitⱼ ⊢l′ ok) (U-cong (sym ⊢Level ⊢l≡l′))) (Unit-cong l≡l′ ok)
    .Equality-relations.≅ₜ-η-unit →
      λ [l] [e] [e'] ok η →
        let u , uWhnf , uRed = whNormTerm [e]
            u' , u'Whnf , u'Red = whNormTerm [e']
            _ , _ , [u] = wf-⊢≡∷ (subset*Term uRed)
            _ , _ , [u'] = wf-⊢≡∷ (subset*Term u'Red)
        in  [↑]ₜ Unit! u u'
              (id (syntacticTerm [e]) , Unitₙ)
              (uRed , uWhnf)
              (u'Red , u'Whnf)
              (η-unit [l] [u] [u'] uWhnf u'Whnf ok η)
    .Equality-relations.≅-ΠΣ-cong →
      λ x₁ x₂ ok → liftConv (ΠΣ-cong x₁ x₂ ok)
    .Equality-relations.≅ₜ-ΠΣ-cong →
      λ l₁ x₁ x₂ ok →
        let _ , F∷U , H∷U = syntacticEqTerm (soundnessConv↑Term x₁)
            _ , G∷U , E∷U = syntacticEqTerm (soundnessConv↑Term x₂)
            ⊢Γ = wfTerm F∷U
            F<>H = univConv↑ x₁
            G<>E = univConv↑ x₂
            F≡H = soundnessConv↑ F<>H
            E∷U′ = stabilityTerm (refl-∙ F≡H) E∷U
        in
        liftConvTerm $ univ
          (ΠΣⱼ l₁ F∷U G∷U ok)
          (ΠΣⱼ l₁ H∷U E∷U′ ok)
          (ΠΣ-cong F<>H G<>E ok)
    .Equality-relations.≅ₜ-zerorefl →
      liftConvTerm ∘ᶠ zero-refl
    .Equality-relations.≅ₜ-star-cong →
      λ l≡l′ ok → liftConvTerm (star-cong′ l≡l′ ok)
    .Equality-relations.≅-suc-cong →
      liftConvTerm ∘ᶠ suc-cong
    .Equality-relations.≅-prod-cong →
      λ x₁ x₂ x₃ x₄ → liftConvTerm (prod-cong x₁ x₂ x₃ x₄)
    .Equality-relations.≅-η-eq →
      λ x₁ x₂ x₃ x₄ x₅ → liftConvTerm (η-eq x₁ x₂ x₃ x₄ x₅)
    .Equality-relations.≅-Σ-η →
      λ x₂ x₃ x₄ x₅ x₆ x₇ → (liftConvTerm (Σ-η x₂ x₃ x₄ x₅ x₆ x₇))
    .Equality-relations.~-var → ~-var
    .Equality-relations.~-app → ~-app
    .Equality-relations.~-fst →
      λ _ x₂ → ~-fst x₂
    .Equality-relations.~-snd →
      λ _ x₂ → ~-snd x₂
    .Equality-relations.~-natrec → ~-natrec
    .Equality-relations.~-prodrec →
      λ C↑D t₁~t₂ u₁↑u₂ _ → ~-prodrec C↑D t₁~t₂ u₁↑u₂
    .Equality-relations.~-emptyrec → ~-emptyrec
    .Equality-relations.~-unitrec  → ~-unitrec
    .Equality-relations.≅-Id-cong  →
      λ A₁≡A₂ t₁≡t₂ u₁≡u₂ → liftConv (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂)
    .Equality-relations.≅ₜ-Id-cong →
      λ A₁≡A₂ t₁≡t₂ u₁≡u₂ →
        case soundnessConv↑Term A₁≡A₂ of λ {
          ⊢A₁≡A₂ →
        case syntacticEqTerm ⊢A₁≡A₂ of λ {
          (_ , ⊢A₁ , ⊢A₂) →
        case syntacticEqTerm (soundnessConv↑Term t₁≡t₂) of λ {
          (_ , ⊢t₁ , ⊢t₂) →
        case syntacticEqTerm (soundnessConv↑Term u₁≡u₂) of λ {
          (_ , ⊢u₁ , ⊢u₂) →
        liftConvTerm $
        univ (Idⱼ ⊢A₁ ⊢t₁ ⊢u₁)
          (Idⱼ ⊢A₂ (conv ⊢t₂ (univ ⊢A₁≡A₂)) (conv ⊢u₂ (univ ⊢A₁≡A₂)))
          (Id-cong (univConv↑ A₁≡A₂) t₁≡t₂ u₁≡u₂) }}}}
    .Equality-relations.≅ₜ-rflrefl →
      liftConvTerm ∘→ rfl-refl ∘→ refl
    .Equality-relations.~-J       → ~-J
    .Equality-relations.~-K       → ~-K
    .Equality-relations.~-[]-cong → ~-[]-cong

-- An EqRelSet instance that uses algorithmic equality (_⊢_[conv↑]_,
-- _⊢_[conv↑]_∷_ and _⊢_~_∷_).

instance

  eqRelInstance : EqRelSet
  eqRelInstance = λ where
    .EqRelSet._⊢_≅_              → _⊢_[conv↑]_
    .EqRelSet._⊢_≅_∷_            → _⊢_[conv↑]_∷_
    .EqRelSet._⊢_~_∷_            → _⊢_~_∷_
    .EqRelSet.Neutrals-included  → Lift _ ⊤
    .EqRelSet.equality-relations → equality-relations

open EqRelSet eqRelInstance public hiding (_⊢_~_∷_)
open Definition.Typed.EqualityRelation.Instance
       R ⦃ eq = eqRelInstance ⦄
  public

instance

  -- A variant of lift tt that is an instance.

  lift-tt : Lift a ⊤
  lift-tt = lift tt
