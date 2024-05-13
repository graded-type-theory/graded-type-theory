------------------------------------------------------------------------
-- Inversion lemmata for the typing relation.
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.Inversion
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Typed R
open import Definition.Typed.Properties R

open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Consequences.Stability R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Consequences.Substitution R
open import Definition.Typed.Consequences.Inequality R

import Graded.Derived.Erased.Untyped 𝕄 as Erased

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Empty using (⊥; ⊥-elim)

private
  variable
    n : Nat
    Γ : Con Term n
    p p′ q q′ r : M
    b : BinderMode
    s s′ : Strength
    A B C t u v w : Term _

-- Inversion of U (it has no type).
inversion-U : ∀ {C} → Γ ⊢ U ∷ C → ⊥
inversion-U (conv x x₁) = inversion-U x

-- Inversion of natural number type.
inversion-ℕ : ∀ {C} → Γ ⊢ ℕ ∷ C → Γ ⊢ C ≡ U
inversion-ℕ (ℕⱼ x) = refl (Uⱼ x)
inversion-ℕ (conv x x₁) = trans (sym x₁) (inversion-ℕ x)

-- Inversion of Empty.
inversion-Empty : ∀ {C} → Γ ⊢ Empty ∷ C → Γ ⊢ C ≡ U
inversion-Empty (Emptyⱼ x) = refl (Uⱼ x)
inversion-Empty (conv x x₁) = trans (sym x₁) (inversion-Empty x)

-- Inversion for the term Unit.
inversion-Unit-U : Γ ⊢ Unit s ∷ C → Γ ⊢ C ≡ U × Unit-allowed s
inversion-Unit-U (Unitⱼ ⊢Γ ok) = refl (Uⱼ ⊢Γ) , ok
inversion-Unit-U (conv ⊢Unit A≡B) =
  case inversion-Unit-U ⊢Unit of λ {
    (A≡U , ok) →
  trans (sym A≡B) A≡U , ok }

-- Inversion for the Unit type.
inversion-Unit : Γ ⊢ Unit s → Unit-allowed s
inversion-Unit = λ where
  (Unitⱼ _ ok) → ok
  (univ ⊢Unit) → case inversion-Unit-U ⊢Unit of λ where
    (_ , ok) → ok

-- If a term has type Unit, then Unit-allowed holds.
⊢∷Unit→Unit-allowed : Γ ⊢ t ∷ Unit s → Unit-allowed s
⊢∷Unit→Unit-allowed {Γ = Γ} {t = t} {s = s} =
  Γ ⊢ t ∷ Unit s  →⟨ syntacticTerm ⟩
  Γ ⊢ Unit s      →⟨ inversion-Unit ⟩
  Unit-allowed s  □

-- Inversion for terms that are Π- or Σ-types.
inversion-ΠΣ-U :
  ∀ {F G C} →
  Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G ∷ C →
  Γ ⊢ F ∷ U × Γ ∙ F ⊢ G ∷ U × Γ ⊢ C ≡ U × ΠΣ-allowed b p q
inversion-ΠΣ-U (ΠΣⱼ x x₁ ok) = x , x₁ , refl (Uⱼ (wfTerm x)) , ok
inversion-ΠΣ-U (conv x x₁)  =
  let a , b , c , ok = inversion-ΠΣ-U x
  in  a , b , trans (sym x₁) c , ok

-- Inversion for Π- and Σ-types.
inversion-ΠΣ :
  Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
  Γ ⊢ A × Γ ∙ A ⊢ B × ΠΣ-allowed b p q
inversion-ΠΣ = λ where
  (ΠΣⱼ ⊢A ⊢B ok) → ⊢A , ⊢B , ok
  (univ ⊢ΠΣAB)  → case inversion-ΠΣ-U ⊢ΠΣAB of λ where
    (⊢A , ⊢B , _ , ok) → univ ⊢A , univ ⊢B , ok

-- If a term has type ΠΣ⟨ b ⟩ p , q ▷ A ▹ B, then ΠΣ-allowed b p q
-- holds.
⊢∷ΠΣ→ΠΣ-allowed :
  Γ ⊢ t ∷ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B → ΠΣ-allowed b p q
⊢∷ΠΣ→ΠΣ-allowed
  {Γ = Γ} {t = t} {b = b} {p = p} {q = q} {A = A} {B = B} =
  Γ ⊢ t ∷ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B  →⟨ syntacticTerm ⟩
  Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B      →⟨ proj₂ ∘→ proj₂ ∘→ inversion-ΠΣ ⟩
  ΠΣ-allowed b p q               □

-- Inversion of variables
inversion-var : ∀ {x C} → Γ ⊢ var x ∷ C → ∃ λ A → x ∷ A ∈ Γ × Γ ⊢ C ≡ A
inversion-var ⊢x@(var x x₁) =
  let ⊢C = syntacticTerm ⊢x
  in  _ , x₁ , refl ⊢C
inversion-var (conv x x₁) =
  let a , b , c = inversion-var x
  in  a , b , trans (sym x₁) c

-- Inversion of zero.
inversion-zero : ∀ {C} → Γ ⊢ zero ∷ C → Γ ⊢ C ≡ ℕ
inversion-zero (zeroⱼ x) = refl (ℕⱼ x)
inversion-zero (conv x x₁) = trans (sym x₁) (inversion-zero x)

-- Inversion of successor.
inversion-suc : ∀ {t C} → Γ ⊢ suc t ∷ C → Γ ⊢ t ∷ ℕ × Γ ⊢ C ≡ ℕ
inversion-suc (sucⱼ x) = x , refl (ℕⱼ (wfTerm x))
inversion-suc (conv x x₁) =
  let a , b = inversion-suc x
  in  a , trans (sym x₁) b

-- Inversion of natural recursion.
inversion-natrec : ∀ {c g n A C} → Γ ⊢ natrec p q r C c g n ∷ A
  → (Γ ∙ ℕ ⊢ C)
  × Γ ⊢ c ∷ C [ zero ]₀
  × Γ ∙ ℕ ∙ C ⊢ g ∷ C [ suc (var x1) ]↑²
  × Γ ⊢ n ∷ ℕ
  × Γ ⊢ A ≡ C [ n ]₀
inversion-natrec (natrecⱼ x d d₁ n) = x , d , d₁ , n , refl (substType x n)
inversion-natrec (conv d x) = let a , b , c , d , e = inversion-natrec d
                              in  a , b , c , d , trans (sym x) e

-- Inversion of application.
inversion-app :  ∀ {f a A} → Γ ⊢ f ∘⟨ p ⟩ a ∷ A →
  ∃₃ λ F G q → Γ ⊢ f ∷ Π p , q ▷ F ▹ G × Γ ⊢ a ∷ F × Γ ⊢ A ≡ G [ a ]₀
inversion-app (d ∘ⱼ d₁) = _ , _ , _ , d , d₁ , refl (substTypeΠ (syntacticTerm d) d₁)
inversion-app (conv d x) = let a , b , c , d , e , f = inversion-app d
                           in  a , b , c , d , e , trans (sym x) f

-- Inversion of lambda.
inversion-lam : ∀ {t A} → Γ ⊢ lam p t ∷ A →
  ∃₃ λ F G q →
     (Γ ⊢ F) ×
     Γ ∙ F ⊢ t ∷ G ×
     Γ ⊢ A ≡ Π p , q ▷ F ▹ G ×
     Π-allowed p q
inversion-lam (lamⱼ ⊢F ⊢G ok) =
  _ , _ , _ , ⊢F , ⊢G , refl (ΠΣⱼ ⊢F (syntacticTerm ⊢G) ok) , ok
inversion-lam (conv x x₁) =
  let a , b , c , d , e , f , g = inversion-lam x
  in  a , b , c , d , e , trans (sym x₁) f , g

opaque

  -- A variant of the previous lemma.

  inversion-lam-Π :
    Γ ⊢ lam p′ t ∷ Π p , q ▷ A ▹ B →
    Γ ∙ A ⊢ t ∷ B × p PE.≡ p′ × Π-allowed p q
  inversion-lam-Π ⊢lam =
    case inversion-lam ⊢lam of λ {
      (_ , _ , _ , _ , ⊢t , Π≡Π , ok) →
    case ΠΣ-injectivity Π≡Π of λ {
      (A≡A′ , B≡B′ , PE.refl , PE.refl , _) →
      conv (stabilityTerm (reflConEq (wfTerm ⊢lam) ∙ sym A≡A′) ⊢t)
        (sym B≡B′)
    , PE.refl
    , ok }}

-- Inversion of products.
inversion-prod :
  ∀ {t u A m} →
  Γ ⊢ prod m p t u ∷ A →
  ∃₃ λ F G q →
    (Γ ⊢ F) ×
    (Γ ∙ F ⊢ G) ×
    (Γ ⊢ t ∷ F) ×
    (Γ ⊢ u ∷ G [ t ]₀) ×
    Γ ⊢ A ≡ Σ⟨ m ⟩ p , q ▷ F ▹ G ×
    Σ-allowed m p q
  -- NOTE fundamental theorem not required since prodⱼ has inversion built-in.
inversion-prod (prodⱼ ⊢F ⊢G ⊢t ⊢u ok) =
  _ , _ , _ , ⊢F , ⊢G , ⊢t , ⊢u , refl (ΠΣⱼ ⊢F ⊢G ok) , ok
inversion-prod (conv x x₁) =
  let F , G , q , a , b , c , d , e , ok = inversion-prod x
  in F , G , q , a , b , c , d , trans (sym x₁) e , ok

opaque

  -- A variant of the previous lemma.

  inversion-prod-Σ :
    Γ ⊢ prod s′ p′ t u ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B →
    Γ ⊢ t ∷ A × Γ ⊢ u ∷ B [ t ]₀ ×
    s PE.≡ s′ × p PE.≡ p′ × Σ-allowed s p q
  inversion-prod-Σ ⊢prod =
    case inversion-prod ⊢prod of λ {
      (_ , _ , _ , _ , _ , ⊢t , ⊢u , Σ≡Σ , ok) →
    case ΠΣ-injectivity Σ≡Σ of λ {
      (A≡A′ , B≡B′ , PE.refl , PE.refl , PE.refl) →
    case conv ⊢t (sym A≡A′) of λ {
      ⊢t →
      ⊢t
    , conv ⊢u (sym (substTypeEq B≡B′ (refl ⊢t)))
    , PE.refl
    , PE.refl
    , ok }}}

-- Inversion of projections
inversion-fst : ∀ {t A} → Γ ⊢ fst p t ∷ A →
  ∃₃ λ F G q →
    Γ ⊢ F × Γ ∙ F ⊢ G ×
    (Γ ⊢ t ∷ Σˢ p , q ▷ F ▹ G) × (Γ ⊢ A ≡ F)
inversion-fst (fstⱼ ⊢F ⊢G ⊢t) = _ , _ , _ , ⊢F , ⊢G , ⊢t , refl ⊢F
inversion-fst (conv ⊢t x) =
  let F , G , q , a , b , c , d = inversion-fst ⊢t
  in  F , G , q , a , b , c , trans (sym x) d

inversion-snd : ∀ {t A} → Γ ⊢ snd p t ∷ A →
  ∃₃ λ F G q →
    Γ ⊢ F × Γ ∙ F ⊢ G ×
    (Γ ⊢ t ∷ Σˢ p , q ▷ F ▹ G) × (Γ ⊢ A ≡ G [ fst p t ]₀)
inversion-snd (sndⱼ ⊢F ⊢G ⊢t) =
  _ , _ , _ , ⊢F , ⊢G , ⊢t , refl (substType ⊢G (fstⱼ ⊢F ⊢G ⊢t))
inversion-snd (conv ⊢t x) =
  let F , G , q , a , b , c , d = inversion-snd ⊢t
  in  F , G , q , a , b , c , trans (sym x) d

-- Inversion of prodrec
inversion-prodrec :
  ∀ {t u A C} →
  Γ ⊢ prodrec r p q′ C t u ∷ A →
  ∃₃ λ F G q →
    (Γ ⊢ F) ×
    (Γ ∙ F ⊢ G) ×
    (Γ ∙ (Σʷ p , q ▷ F ▹ G) ⊢ C) ×
    Γ ⊢ t ∷ Σʷ p , q ▷ F ▹ G ×
    Γ ∙ F ∙ G ⊢ u ∷ C [ prodʷ p (var x1) (var x0) ]↑² ×
    Γ ⊢ A ≡ C [ t ]₀
inversion-prodrec (prodrecⱼ ⊢F ⊢G ⊢C ⊢t ⊢u _) =
  _ , _ , _ , ⊢F , ⊢G , ⊢C , ⊢t , ⊢u , refl (substType ⊢C ⊢t)
inversion-prodrec (conv x x₁) =
  let F , G , q , a , b , c , d , e , f = inversion-prodrec x
  in  F , G , q , a , b , c , d , e , trans (sym x₁) f

-- Inversion of star.
inversion-star : Γ ⊢ star s ∷ C → Γ ⊢ C ≡ Unit s × Unit-allowed s
inversion-star (starⱼ ⊢Γ ok) = refl (Unitⱼ ⊢Γ ok) , ok
inversion-star (conv ⊢star A≡B) =
  case inversion-star ⊢star of λ {
    (A≡Unit , ok) →
  trans (sym A≡B) A≡Unit , ok }

-- Inversion of unitrec
inversion-unitrec : Γ ⊢ unitrec p q A t u ∷ C
                  → (Γ ∙ Unitʷ ⊢ A)
                  × (Γ ⊢ t ∷ Unitʷ)
                  × (Γ ⊢ u ∷ A [ starʷ ]₀)
                  × (Γ ⊢ C ≡ A [ t ]₀)
inversion-unitrec (unitrecⱼ ⊢A ⊢t ⊢u _) =
  ⊢A , ⊢t , ⊢u , refl (substType ⊢A ⊢t)
inversion-unitrec (conv x x₁) =
  let ⊢A , ⊢t , ⊢u , x = inversion-unitrec x
  in  ⊢A , ⊢t , ⊢u , trans (sym x₁) x

-- Inversion of emptyrec
inversion-emptyrec : ∀ {C A t} → Γ ⊢ emptyrec p A t ∷ C
                   → (Γ ⊢ A) × (Γ ⊢ t ∷ Empty) × Γ ⊢ C ≡ A
inversion-emptyrec (emptyrecⱼ x ⊢t) = x , ⊢t , refl x
inversion-emptyrec (conv ⊢t x) =
  let q , w , e = inversion-emptyrec ⊢t
  in  q , w , trans (sym x) e

opaque

  -- Inversion for terms that are identity types.

  inversion-Id-U :
    Γ ⊢ Id A t u ∷ B →
    Γ ⊢ A ∷ U × Γ ⊢ t ∷ A × Γ ⊢ u ∷ A × Γ ⊢ B ≡ U
  inversion-Id-U = λ where
    (Idⱼ ⊢A ⊢t ⊢u) → ⊢A , ⊢t , ⊢u , refl (Uⱼ (wfTerm ⊢A))
    (conv ⊢Id C≡B) →
      case inversion-Id-U ⊢Id of λ {
        (⊢A , ⊢t , ⊢u , C≡U) →
      ⊢A , ⊢t , ⊢u , trans (sym C≡B) C≡U }

opaque

  -- Inversion for identity types.

  inversion-Id :
    Γ ⊢ Id A t u →
    (Γ ⊢ A) × Γ ⊢ t ∷ A × Γ ⊢ u ∷ A
  inversion-Id = λ where
    (Idⱼ ⊢t ⊢u) → syntacticTerm ⊢t , ⊢t , ⊢u
    (univ ⊢Id)  →
      case inversion-Id-U ⊢Id of λ {
        (⊢A , ⊢t , ⊢u , _) →
      univ ⊢A , ⊢t , ⊢u }

opaque

  -- Inversion for rfl.

  inversion-rfl :
    Γ ⊢ rfl ∷ A →
    ∃₂ λ B t → (Γ ⊢ B) × Γ ⊢ t ∷ B × Γ ⊢ A ≡ Id B t t
  inversion-rfl = λ where
    ⊢rfl@(rflⱼ ⊢t)  →
      _ , _ , syntacticTerm ⊢t , ⊢t , refl (syntacticTerm ⊢rfl)
    (conv ⊢rfl C≡A) →
      case inversion-rfl ⊢rfl of λ {
        (_ , _ , ⊢B , ⊢t , C≡Id) →
      _ , _ , ⊢B , ⊢t , trans (sym C≡A) C≡Id }

opaque

  -- A variant of the previous lemma.

  inversion-rfl-Id : Γ ⊢ rfl ∷ Id A t u → Γ ⊢ t ≡ u ∷ A
  inversion-rfl-Id ⊢rfl =
    case inversion-rfl ⊢rfl of λ {
      (_ , _ , _ , _ , Id≡Id) →
    case Id-injectivity Id≡Id of λ {
      (_ , t≡v , u≡v) →
    trans t≡v (sym u≡v) }}

opaque

  -- Inversion for J.

  inversion-J :
    Γ ⊢ J p q A t B u v w ∷ C →
    (Γ ⊢ A) ×
    Γ ⊢ t ∷ A ×
    (Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B) ×
    Γ ⊢ u ∷ B [ t , rfl ]₁₀ ×
    Γ ⊢ v ∷ A ×
    Γ ⊢ w ∷ Id A t v ×
    Γ ⊢ C ≡ B [ v , w ]₁₀
  inversion-J = λ where
    ⊢J@(Jⱼ ⊢A ⊢t ⊢B ⊢u ⊢v ⊢w) →
      ⊢A , ⊢t , ⊢B , ⊢u , ⊢v , ⊢w , refl (syntacticTerm ⊢J)
    (conv ⊢J D≡C) →
      case inversion-J ⊢J of λ {
        (⊢A , ⊢t , ⊢B , ⊢u , ⊢v , ⊢w , D≡B) →
      ⊢A , ⊢t , ⊢B , ⊢u , ⊢v , ⊢w , trans (sym D≡C) D≡B }

opaque

  -- Inversion for K.

  inversion-K :
    Γ ⊢ K p A t B u v ∷ C →
    (Γ ⊢ A) ×
    Γ ⊢ t ∷ A ×
    (Γ ∙ Id A t t ⊢ B) ×
    Γ ⊢ u ∷ B [ rfl ]₀ ×
    Γ ⊢ v ∷ Id A t t ×
    K-allowed ×
    Γ ⊢ C ≡ B [ v ]₀
  inversion-K = λ where
    ⊢K@(Kⱼ ⊢t ⊢B ⊢u ⊢v ok) →
        syntacticTerm ⊢t , ⊢t , ⊢B , ⊢u , ⊢v , ok
      , refl (syntacticTerm ⊢K)
    (conv ⊢K D≡C) →
      case inversion-K ⊢K of λ {
        (⊢A , ⊢t , ⊢B , ⊢u , ⊢v , ok , D≡B) →
      ⊢A , ⊢t , ⊢B , ⊢u , ⊢v , ok , trans (sym D≡C) D≡B }

opaque

  -- Inversion for []-cong.

  inversion-[]-cong :
    Γ ⊢ []-cong s A t u v ∷ B →
    let open Erased s in
      (Γ ⊢ A) ×
      Γ ⊢ t ∷ A ×
      Γ ⊢ u ∷ A ×
      Γ ⊢ v ∷ Id A t u ×
      []-cong-allowed s ×
      Γ ⊢ B ≡ Id (Erased A) ([ t ]) ([ u ])
  inversion-[]-cong = λ where
    ⊢[]-cong@([]-congⱼ ⊢t ⊢u ⊢v ok) →
        syntacticTerm ⊢t , ⊢t , ⊢u , ⊢v , ok
      , refl (syntacticTerm ⊢[]-cong)
    (conv ⊢[]-cong C≡B) →
      case inversion-[]-cong ⊢[]-cong of λ {
        (⊢A , ⊢t , ⊢u , ⊢v , ok , C≡Id) →
      ⊢A , ⊢t , ⊢u , ⊢v , ok , trans (sym C≡B) C≡Id }

-- Inversion of products in WHNF.
whnfProduct :
  ∀ {p F G m} →
  Γ ⊢ p ∷ Σ⟨ m ⟩ p′ , q ▷ F ▹ G → Whnf p → Product p
whnfProduct x prodₙ = prodₙ
whnfProduct x (ne pNe) = ne pNe

whnfProduct x Uₙ = ⊥-elim (inversion-U x)
whnfProduct x ΠΣₙ =
  let _ , _ , Σ≡U , _ = inversion-ΠΣ-U x
  in  ⊥-elim (U≢Σ (sym Σ≡U))
whnfProduct x ℕₙ = ⊥-elim (U≢Σ (sym (inversion-ℕ x)))
whnfProduct x Unitₙ = ⊥-elim (U≢Σ (sym (inversion-Unit-U x .proj₁)))
whnfProduct x Emptyₙ = ⊥-elim (U≢Σ (sym (inversion-Empty x)))
whnfProduct x lamₙ =
  let _ , _ , _ , _ , _ , Σ≡Π , _ = inversion-lam x
  in  ⊥-elim (Π≢Σⱼ (sym Σ≡Π))
whnfProduct x zeroₙ = ⊥-elim (ℕ≢Σ (sym (inversion-zero x)))
whnfProduct x sucₙ =
  let _ , A≡ℕ = inversion-suc x
  in  ⊥-elim (ℕ≢Σ (sym A≡ℕ))
whnfProduct x starₙ = ⊥-elim (Unit≢Σⱼ (sym (inversion-star x .proj₁)))
whnfProduct ⊢∷Σ Idₙ =
  ⊥-elim (U≢Σ (sym (inversion-Id-U ⊢∷Σ .proj₂ .proj₂ .proj₂)))
whnfProduct ⊢∷Σ rflₙ =
  ⊥-elim (Id≢Σ (sym (inversion-rfl ⊢∷Σ .proj₂ .proj₂ .proj₂ .proj₂)))
