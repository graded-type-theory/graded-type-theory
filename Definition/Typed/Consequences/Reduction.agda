module Definition.Typed.Consequences.Reduction
  {a} (M : Set a) where

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed M
open import Definition.Typed.Properties M
open import Definition.Typed.EqRelInstance M
open import Definition.Typed.Consequences.Inequality M
open import Definition.Typed.Consequences.Injectivity M
open import Definition.Typed.Consequences.Inversion M
open import Definition.Typed.Consequences.Syntactic M
open import Definition.LogicalRelation M
open import Definition.LogicalRelation.Properties M
open import Definition.LogicalRelation.Fundamental.Reducibility M

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    p q : M

-- Helper function where all reducible types can be reduced to WHNF.
whNorm′ : ∀ {A l} ([A] : Γ ⊩⟨ l ⟩ A)
                → ∃ λ B → Whnf B × Γ ⊢ A :⇒*: B
whNorm′ (Uᵣ′ .⁰ 0<1 ⊢Γ) = U , Uₙ , idRed:*: (Uⱼ ⊢Γ)
whNorm′ (ℕᵣ D) = ℕ , ℕₙ , D
whNorm′ (Emptyᵣ D) = Empty , Emptyₙ , D
whNorm′ (Unitᵣ D) = Unit , Unitₙ , D
whNorm′ (ne′ K D neK K≡K) = K , ne neK , D
whNorm′ (Πᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) = Π _ , _ ▷ F ▹ G , ΠΣₙ , D
whNorm′ (Σᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) = Σ _ , _ ▷ F ▹ G , ΠΣₙ , D
whNorm′ (emb 0<1 [A]) = whNorm′ [A]

-- Well-formed types can all be reduced to WHNF.
whNorm : ∀ {A} → Γ ⊢ A → ∃ λ B → Whnf B × Γ ⊢ A :⇒*: B
whNorm A = whNorm′ (reducible A)

ΠNorm : ∀ {A F G} → Γ ⊢ A → Γ ⊢ A ≡ Π p , q ▷ F ▹ G
      → ∃₄ λ p′ q′ F′ G′ → Γ ⊢ A ⇒* Π p′ , q′ ▷ F′ ▹ G′ × Γ ⊢ F ≡ F′
         × Γ ∙ F ⊢ G ≡ G′ × p PE.≈ p′ × q PE.≈ q′
ΠNorm ⊢A A≡ΠFG with whNorm ⊢A
... | _ , Uₙ , D = PE.⊥-elim (U≢Π (trans (sym (subset* (red D))) A≡ΠFG))
... | _ , ΠΣₙ {b = BMΠ} , D =
  let Π≡Π′ = trans (sym A≡ΠFG) (subset* (red D))
  in  _ , _ , _ , _ , red D , injectivity Π≡Π′
... | _ , ΠΣₙ {b = BMΣ s} , D = PE.⊥-elim (Π≢Σⱼ (trans (sym A≡ΠFG) (subset* (red D))))
... | _ , ℕₙ , D = PE.⊥-elim (ℕ≢Π (trans (sym (subset* (red D))) A≡ΠFG))
... | _ , Unitₙ , D = PE.⊥-elim (Unit≢Πⱼ (trans (sym (subset* (red D))) A≡ΠFG))
... | _ , Emptyₙ , D = PE.⊥-elim (Empty≢Πⱼ (trans (sym (subset* (red D))) A≡ΠFG))
... | _ , lamₙ , [ ⊢A , univ ⊢B , A⇒B ] =
  let F , G , q , ⊢F , ⊢t , U≡Π = inversion-lam ⊢B
  in  PE.⊥-elim (U≢Π U≡Π)
... | _ , zeroₙ , [ ⊢A , univ ⊢B , A⇒B ] = PE.⊥-elim (U≢ℕ (inversion-zero ⊢B))
... | _ , sucₙ , [ ⊢A , univ ⊢B , A⇒B ] = PE.⊥-elim (U≢ℕ (proj₂ (inversion-suc ⊢B)))
... | _ , starₙ , [ ⊢A , univ ⊢B , A⇒B ] = PE.⊥-elim (U≢Unitⱼ (inversion-star ⊢B))
... | _ , prodₙ , [ ⊢A , univ ⊢B , A⇒B ] =
  let F , G , q , ⊢F , ⊢G , ⊢t , ⊢u , U≡Σ = inversion-prod ⊢B
  in  PE.⊥-elim (U≢Σ U≡Σ)
... | _ , ne x , D = PE.⊥-elim (Π≢ne x (trans (sym A≡ΠFG) (subset* (red D))))

ΣNorm : ∀ {A F G m} → Γ ⊢ A → Γ ⊢ A ≡ Σ⟨ m ⟩ p , q ▷ F ▹ G
      → ∃₄ λ p′ q′ F′ G′ → Γ ⊢ A ⇒* Σ⟨ m ⟩ p′ , q′ ▷ F′ ▹ G′
         × Γ ⊢ F ≡ F′ × Γ ∙ F ⊢ G ≡ G′ × p PE.≈ p′ × q PE.≈ q′
ΣNorm ⊢A A≡ΣFG with whNorm ⊢A
... | _ , Uₙ , D = PE.⊥-elim (U≢Σ (trans (sym (subset* (red D))) A≡ΣFG))
... | _ , (ΠΣₙ {b = BMΠ}) , D = PE.⊥-elim (Π≢Σⱼ (trans (sym (subset* (red D))) A≡ΣFG))
... | _ , (ΠΣₙ {b = BMΣ m}) , D =
  let Σ≡Σ′ = trans (sym A≡ΣFG) (subset* (red D))
      F≡F′ , G≡G′ , p≈p′ , q≈q′ , m≡m′ = Σ-injectivity Σ≡Σ′
  in  _ , _ , _ , _
   , PE.subst (λ m → _ ⊢ _ ⇒* Σ⟨ m ⟩ _ , _ ▷ _ ▹ _) (PE.sym m≡m′) (red D)
   , F≡F′ , G≡G′ , p≈p′ , q≈q′
... | _ , ℕₙ , D = PE.⊥-elim (ℕ≢Σ (trans (sym (subset* (red D))) A≡ΣFG))
... | _ , Unitₙ , D = PE.⊥-elim (Unit≢Σⱼ (trans (sym (subset* (red D))) A≡ΣFG))
... | _ , Emptyₙ , D = PE.⊥-elim (Empty≢Σⱼ (trans (sym (subset* (red D))) A≡ΣFG))
... | _ , lamₙ , [ ⊢A , univ ⊢B , A⇒B ] =
  let F , G , q , ⊢F , ⊢t , U≡Π = inversion-lam ⊢B
  in  PE.⊥-elim (U≢Π U≡Π)
... | _ , zeroₙ , [ ⊢A , univ ⊢B , A⇒B ] = PE.⊥-elim (U≢ℕ (inversion-zero ⊢B))
... | _ , sucₙ , [ ⊢A , univ ⊢B , A⇒B ] = PE.⊥-elim (U≢ℕ (proj₂ (inversion-suc ⊢B)))
... | _ , starₙ , [ ⊢A , univ ⊢B , A⇒B ] = PE.⊥-elim (U≢Unitⱼ (inversion-star ⊢B))
... | _ , prodₙ , [ ⊢A , univ ⊢B , A⇒B ] =
  let F , G , q , ⊢F , ⊢G , ⊢t , ⊢u , U≡Σ = inversion-prod ⊢B
  in  PE.⊥-elim (U≢Σ U≡Σ)
... | _ , ne x , D = PE.⊥-elim (Σ≢ne x (trans (sym A≡ΣFG) (subset* (red D))))

-- Helper function where reducible all terms can be reduced to WHNF.
whNormTerm′ : ∀ {a A l} ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ a ∷ A / [A]
                → ∃ λ b → Whnf b × Γ ⊢ a :⇒*: b ∷ A
whNormTerm′ (Uᵣ x) (Uₜ A d typeA A≡A [t]) = A , typeWhnf typeA , d
whNormTerm′ (ℕᵣ x) (ℕₜ n d n≡n prop) =
  let natN = natural prop
  in  n , naturalWhnf natN , convRed:*: d (sym (subset* (red x)))
whNormTerm′ (Emptyᵣ x) (Emptyₜ n d n≡n prop) =
  let emptyN = empty prop
  in  n , ne emptyN , convRed:*: d (sym (subset* (red x)))
whNormTerm′ (Unitᵣ x) (Unitₜ n d prop) =
  n , prop , convRed:*: d (sym (subset* (red x)))
whNormTerm′ (ne (ne K D neK K≡K)) (neₜ k d (neNfₜ neK₁ ⊢k k≡k)) =
  k , ne neK₁ , convRed:*: d (sym (subset* (red D)))
whNormTerm′ (Πᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Πₜ f d funcF f≡f [f] [f]₁) =
  f , functionWhnf funcF , convRed:*: d (sym (subset* (red D)))
whNormTerm′ (Σᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Σₜ p d p≡p pProd pProp) =
  p , productWhnf pProd , convRed:*: d (sym (subset* (red D)))
whNormTerm′ (emb 0<1 [A]) [a] = whNormTerm′ [A] [a]

-- Well-formed terms can all be reduced to WHNF.
whNormTerm : ∀ {a A} → Γ ⊢ a ∷ A → ∃ λ b → Whnf b × Γ ⊢ a :⇒*: b ∷ A
whNormTerm {a} {A} ⊢a =
  let [A] , [a] = reducibleTerm ⊢a
  in  whNormTerm′ [A] [a]

redMany : ∀ {t u A} → Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ⇒* u ∷ A
redMany d =
  let _ , _ , ⊢u = syntacticEqTerm (subsetTerm d)
  in  d ⇨ id ⊢u
