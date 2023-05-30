------------------------------------------------------------------------
-- Inversion lemmata for the typing relation.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions

module Definition.Typed.Consequences.Inversion
  {a} {M : Set a}
  (R : Type-restrictions M)
  where

open Type-restrictions R

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed R
open import Definition.Typed.Properties R

open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Consequences.Substitution R
open import Definition.Typed.Consequences.Inequality R

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.Empty using (⊥; ⊥-elim)

private
  variable
    n : Nat
    Γ : Con Term n
    p p′ q q′ r : M
    b : BinderMode
    A B C t : Term _

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
inversion-Unit-U : Γ ⊢ Unit ∷ C → Γ ⊢ C ≡ U × Unit-restriction
inversion-Unit-U (Unitⱼ ⊢Γ ok) = refl (Uⱼ ⊢Γ) , ok
inversion-Unit-U (conv ⊢Unit A≡B) =
  case inversion-Unit-U ⊢Unit of λ {
    (A≡U , ok) →
  trans (sym A≡B) A≡U , ok }

-- Inversion for the Unit type.
inversion-Unit : Γ ⊢ Unit → Unit-restriction
inversion-Unit = λ where
  (Unitⱼ _ ok) → ok
  (univ ⊢Unit) → case inversion-Unit-U ⊢Unit of λ where
    (_ , ok) → ok

-- If a term has type Unit, then Unit-restriction holds.
⊢∷Unit→Unit-restriction : Γ ⊢ t ∷ Unit → Unit-restriction
⊢∷Unit→Unit-restriction {Γ = Γ} {t = t} =
  Γ ⊢ t ∷ Unit      →⟨ syntacticTerm ⟩
  Γ ⊢ Unit          →⟨ inversion-Unit ⟩
  Unit-restriction  □

-- Inversion for terms that are Π- or Σ-types.
inversion-ΠΣ-U :
  ∀ {F G C} →
  Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G ∷ C →
  Γ ⊢ F ∷ U × Γ ∙ F ⊢ G ∷ U × Γ ⊢ C ≡ U × ΠΣ-restriction b p q
inversion-ΠΣ-U (ΠΣⱼ x x₁ ok) = x , x₁ , refl (Uⱼ (wfTerm x)) , ok
inversion-ΠΣ-U (conv x x₁)  =
  let a , b , c , ok = inversion-ΠΣ-U x
  in  a , b , trans (sym x₁) c , ok

-- Inversion for Π- and Σ-types.
inversion-ΠΣ :
  Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
  Γ ⊢ A × Γ ∙ A ⊢ B × ΠΣ-restriction b p q
inversion-ΠΣ = λ where
  (ΠΣⱼ ⊢A ⊢B ok) → ⊢A , ⊢B , ok
  (univ ⊢ΠΣAB)  → case inversion-ΠΣ-U ⊢ΠΣAB of λ where
    (⊢A , ⊢B , _ , ok) → univ ⊢A , univ ⊢B , ok

-- If a term has type ΠΣ⟨ b ⟩ p , q ▷ A ▹ B, then ΠΣ-restriction b p q
-- holds.
⊢∷ΠΣ→ΠΣ-restriction :
  Γ ⊢ t ∷ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B → ΠΣ-restriction b p q
⊢∷ΠΣ→ΠΣ-restriction
  {Γ = Γ} {t = t} {b = b} {p = p} {q = q} {A = A} {B = B} =
  Γ ⊢ t ∷ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B  →⟨ syntacticTerm ⟩
  Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B      →⟨ proj₂ ∘→ proj₂ ∘→ inversion-ΠΣ ⟩
  ΠΣ-restriction b p q           □

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
  × Γ ⊢ c ∷ C [ zero ]
  × Γ ∙ ℕ ∙ C ⊢ g ∷ wk1 (C [ suc (var x0) ]↑)
  × Γ ⊢ n ∷ ℕ
  × Γ ⊢ A ≡ C [ n ]
inversion-natrec (natrecⱼ x d d₁ n) = x , d , d₁ , n , refl (substType x n)
inversion-natrec (conv d x) = let a , b , c , d , e = inversion-natrec d
                              in  a , b , c , d , trans (sym x) e

-- Inversion of application.
inversion-app :  ∀ {f a A} → Γ ⊢ f ∘⟨ p ⟩ a ∷ A →
  ∃₃ λ F G q → Γ ⊢ f ∷ Π p , q ▷ F ▹ G × Γ ⊢ a ∷ F × Γ ⊢ A ≡ G [ a ]
inversion-app (d ∘ⱼ d₁) = _ , _ , _ , d , d₁ , refl (substTypeΠ (syntacticTerm d) d₁)
inversion-app (conv d x) = let a , b , c , d , e , f = inversion-app d
                           in  a , b , c , d , e , trans (sym x) f

-- Inversion of lambda.
inversion-lam : ∀ {t A} → Γ ⊢ lam p t ∷ A →
  ∃₃ λ F G q →
     (Γ ⊢ F) ×
     Γ ∙ F ⊢ t ∷ G ×
     Γ ⊢ A ≡ Π p , q ▷ F ▹ G ×
     Π-restriction p q
inversion-lam (lamⱼ ⊢F ⊢G ok) =
  _ , _ , _ , ⊢F , ⊢G , refl (ΠΣⱼ ⊢F (syntacticTerm ⊢G) ok) , ok
inversion-lam (conv x x₁) =
  let a , b , c , d , e , f , g = inversion-lam x
  in  a , b , c , d , e , trans (sym x₁) f , g

-- Inversion of products.
inversion-prod :
  ∀ {t u A m} →
  Γ ⊢ prod m p t u ∷ A →
  ∃₃ λ F G q →
    (Γ ⊢ F) ×
    (Γ ∙ F ⊢ G) ×
    (Γ ⊢ t ∷ F) ×
    (Γ ⊢ u ∷ G [ t ]) ×
    Γ ⊢ A ≡ Σ⟨ m ⟩ p , q ▷ F ▹ G ×
    Σ-restriction m p q
  -- NOTE fundamental theorem not required since prodⱼ has inversion built-in.
inversion-prod (prodⱼ ⊢F ⊢G ⊢t ⊢u ok) =
  _ , _ , _ , ⊢F , ⊢G , ⊢t , ⊢u , refl (ΠΣⱼ ⊢F ⊢G ok) , ok
inversion-prod (conv x x₁) =
  let F , G , q , a , b , c , d , e , ok = inversion-prod x
  in F , G , q , a , b , c , d , trans (sym x₁) e , ok

-- Inversion of projections
inversion-fst : ∀ {t A} → Γ ⊢ fst p t ∷ A →
  ∃₃ λ F G q →
    Γ ⊢ F × Γ ∙ F ⊢ G ×
    (Γ ⊢ t ∷ Σₚ p , q ▷ F ▹ G) × (Γ ⊢ A ≡ F)
inversion-fst (fstⱼ ⊢F ⊢G ⊢t) = _ , _ , _ , ⊢F , ⊢G , ⊢t , refl ⊢F
inversion-fst (conv ⊢t x) =
  let F , G , q , a , b , c , d = inversion-fst ⊢t
  in  F , G , q , a , b , c , trans (sym x) d

inversion-snd : ∀ {t A} → Γ ⊢ snd p t ∷ A →
  ∃₃ λ F G q →
    Γ ⊢ F × Γ ∙ F ⊢ G ×
    (Γ ⊢ t ∷ Σₚ p , q ▷ F ▹ G) × (Γ ⊢ A ≡ G [ fst p t ])
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
    (Γ ∙ (Σᵣ p , q ▷ F ▹ G) ⊢ C) ×
    Γ ⊢ t ∷ Σᵣ p , q ▷ F ▹ G ×
    Γ ∙ F ∙ G ⊢ u ∷ C [ prodᵣ p (var x1) (var x0) ]↑² ×
    Γ ⊢ A ≡ C [ t ]
inversion-prodrec (prodrecⱼ ⊢F ⊢G ⊢C ⊢t ⊢u _) =
  _ , _ , _ , ⊢F , ⊢G , ⊢C , ⊢t , ⊢u , refl (substType ⊢C ⊢t)
inversion-prodrec (conv x x₁) =
  let F , G , q , a , b , c , d , e , f = inversion-prodrec x
  in  F , G , q , a , b , c , d , e , trans (sym x₁) f

-- Inversion of star.
inversion-star : Γ ⊢ star ∷ C → Γ ⊢ C ≡ Unit × Unit-restriction
inversion-star (starⱼ ⊢Γ ok) = refl (Unitⱼ ⊢Γ ok) , ok
inversion-star (conv ⊢star A≡B) =
  case inversion-star ⊢star of λ {
    (A≡Unit , ok) →
  trans (sym A≡B) A≡Unit , ok }

-- Inversion of Emptyrec
inversion-Emptyrec : ∀ {C A t} → Γ ⊢ Emptyrec p A t ∷ C
                   → (Γ ⊢ A) × (Γ ⊢ t ∷ Empty) × Γ ⊢ C ≡ A
inversion-Emptyrec (Emptyrecⱼ x ⊢t) = x , ⊢t , refl x
inversion-Emptyrec (conv ⊢t x) =
  let q , w , e = inversion-Emptyrec ⊢t
  in  q , w , trans (sym x) e

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
