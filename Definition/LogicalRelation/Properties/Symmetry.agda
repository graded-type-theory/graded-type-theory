------------------------------------------------------------------------
-- Equality in the logical relation is symmetric
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Properties.Symmetry
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped M hiding (K)
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Typed.Properties R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties.Conversion R
open import Definition.LogicalRelation.Weakening.Restricted R

open import Tools.Function
open import Tools.Nat hiding (_<_)
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n   : Nat
    Γ   : Con Term n
    t u : Term _
    l   : Universe-level
    s   : Strength

symNeutralTerm : ∀ {t u A}
               → Γ ⊩neNf t ≡ u ∷ A
               → Γ ⊩neNf u ≡ t ∷ A
symNeutralTerm (neNfₜ₌ inc neK neM k≡m) = neNfₜ₌ inc neM neK (~-sym k≡m)

symNatural-prop : ∀ {k k′}
                → [Natural]-prop Γ k k′
                → [Natural]-prop Γ k′ k
symNatural-prop (sucᵣ (ℕₜ₌ k k′ d d′ t≡u prop)) =
  sucᵣ (ℕₜ₌ k′ k d′ d (≅ₜ-sym t≡u) (symNatural-prop prop))
symNatural-prop zeroᵣ = zeroᵣ
symNatural-prop (ne prop) = ne (symNeutralTerm prop)

symEmpty-prop : ∀ {k k′}
              → [Empty]-prop Γ k k′
              → [Empty]-prop Γ k′ k
symEmpty-prop (ne prop) = ne (symNeutralTerm prop)

symUnitʷ-prop : [Unitʷ]-prop Γ l t u → [Unitʷ]-prop Γ l u t
symUnitʷ-prop starᵣ     = starᵣ
symUnitʷ-prop (ne prop) = ne (symNeutralTerm prop)

symUnit-prop : ∀ {k k′}
             → [Unit]-prop Γ l s k k′
             → [Unit]-prop Γ l s k′ k
symUnit-prop (Unitₜ₌ʷ prop no-η) = Unitₜ₌ʷ (symUnitʷ-prop prop) no-η
symUnit-prop (Unitₜ₌ˢ η)         = Unitₜ₌ˢ η


-- Helper function for symmetry of type equality using shape views.
symEqT :
  ∀ {Γ : Con Term n} {A B l l′}
    {[A] : Γ ⊩⟨ l ⟩ A} {[B] : Γ ⊩⟨ l′ ⟩ B} →
  ShapeView Γ l l′ A B [A] [B] →
  Γ ⊩⟨ l  ⟩ A ≡ B / [A] →
  Γ ⊩⟨ l′ ⟩ B ≡ A / [B]

-- Symmetry of type equality.
symEq : ∀ {A B l l′} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l′ ⟩ B)
      → Γ ⊩⟨ l ⟩ A ≡ B / [A]
      → Γ ⊩⟨ l′ ⟩ B ≡ A / [B]
symEq [A] [B] A≡B = symEqT (goodCases [A] [B] A≡B) A≡B

-- Symmetry of term equality.
symEqTerm : ∀ {l A t u} ([A] : Γ ⊩⟨ l ⟩ A)
          → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
          → Γ ⊩⟨ l ⟩ u ≡ t ∷ A / [A]

symEqT (ℕᵥ D D′) A≡B = D
symEqT (Emptyᵥ D D′) A≡B = D
symEqT (Unitᵥ (Unitᵣ _ _ A⇒*Unit _) (Unitᵣ _ _ B⇒*Unit₁ _)) B⇒*Unit₂ =
  case Unit-PE-injectivity $
       whrDet* (B⇒*Unit₁ , Unitₙ) (B⇒*Unit₂ , Unitₙ) of λ {
    (_ , PE.refl) →
  A⇒*Unit }
symEqT
  (ne (ne _ _ D neK K≡K) (ne _ K₁ D₁ neK₁ K≡K₁)) (ne₌ inc M D′ neM K≡M)
  rewrite whrDet* (D′ , ne neM) (D₁ , ne neK₁) =
  ne₌ inc _ D neK (≅-sym K≡M)
symEqT
  {n} {Γ = Γ} {l′ = l′}
  (Bᵥ W (Bᵣ F G D A≡A [F] [G] G-ext _)
     (Bᵣ F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ _))
  (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  let ΠF₁G₁≡ΠF′G′       = whrDet* (D₁ , ⟦ W ⟧ₙ) (D′ , ⟦ W ⟧ₙ)
      F₁≡F′ , G₁≡G′ , _ = B-PE-injectivity W W ΠF₁G₁≡ΠF′G′
      [F₁≡F] :
        {ℓ : Nat} {Δ : Con Term ℓ} {ρ : Wk ℓ n}
        ([ρ] : ρ ∷ʷʳ Δ ⊇ Γ) →
        Δ ⊩⟨ l′ ⟩ (wk ρ F₁) ≡ (wk ρ F) / [F]₁ [ρ]
      [F₁≡F] {_} {Δ} {ρ} [ρ] =
        let ρF′≡ρF₁ ρ = PE.cong (wk ρ) (PE.sym F₁≡F′)
            [ρF′] {ρ} [ρ] =
              PE.subst (Δ ⊩⟨ l′ ⟩_ ∘→ wk ρ) F₁≡F′ ([F]₁ [ρ])
        in  irrelevanceEq′ {Γ = Δ} (ρF′≡ρF₁ ρ)
              ([ρF′] [ρ]) ([F]₁ [ρ]) (symEq ([F] [ρ]) ([ρF′] [ρ])
              ([F≡F′] [ρ]))
  in
  B₌ _ _ D
    (≅-sym (PE.subst (Γ ⊢ ⟦ W ⟧ F ▹ G ≅_) (PE.sym ΠF₁G₁≡ΠF′G′) A≡B))
    [F₁≡F]
    (λ {_} {ρ} {Δ} {a} [ρ] [a] →
       let ρG′a≡ρG₁′a = PE.cong (_[ a ]₀ ∘→ wk (lift ρ)) (PE.sym G₁≡G′)
           [ρG′a] = PE.subst (λ x → Δ ⊩⟨ l′ ⟩ wk (lift ρ) x [ a ]₀)
                      G₁≡G′ ([G]₁ [ρ] [a])
           [a]₁ = convTerm₁ ([F]₁ [ρ]) ([F] [ρ]) ([F₁≡F] [ρ]) [a]
       in  irrelevanceEq′ ρG′a≡ρG₁′a [ρG′a] ([G]₁ [ρ] [a])
             (symEq ([G] [ρ] [a]₁) [ρG′a] ([G≡G′] [ρ] [a]₁)))
symEqT (Uᵥ (Uᵣ l′ l< ⇒*U) (Uᵣ l′₁ l<₁ ⇒*U₁)) D with whrDet* (D , Uₙ) (⇒*U₁ , Uₙ)
symEqT (Uᵥ (Uᵣ l′ l< ⇒*U) (Uᵣ l′₁ l<₁ ⇒*U₁)) D | PE.refl = ⇒*U
symEqT (Idᵥ ⊩A ⊩B@record{}) A≡B =
  case whrDet* (_⊩ₗId_.⇒*Id ⊩B , Idₙ)
         (_⊩ₗId_≡_/_.⇒*Id′ A≡B , Idₙ) of λ {
    PE.refl →
  record
    { ⇒*Id′    = _⊩ₗId_.⇒*Id ⊩A
    ; Ty≡Ty′   = symEq (_⊩ₗId_.⊩Ty ⊩A) (_⊩ₗId_.⊩Ty ⊩B) Ty≡Ty′
    ; lhs≡lhs′ =
        convEqTerm₁ (_⊩ₗId_.⊩Ty ⊩A) (_⊩ₗId_.⊩Ty ⊩B) Ty≡Ty′ $
        symEqTerm (_⊩ₗId_.⊩Ty ⊩A) lhs≡lhs′
    ; rhs≡rhs′ =
        convEqTerm₁ (_⊩ₗId_.⊩Ty ⊩A) (_⊩ₗId_.⊩Ty ⊩B) Ty≡Ty′ $
        symEqTerm (_⊩ₗId_.⊩Ty ⊩A) rhs≡rhs′
    ; lhs≡rhs→lhs′≡rhs′ =
        convEqTerm₁ (_⊩ₗId_.⊩Ty ⊩A) (_⊩ₗId_.⊩Ty ⊩B) Ty≡Ty′ ∘→
        lhs′≡rhs′→lhs≡rhs ∘→
        convEqTerm₂ (_⊩ₗId_.⊩Ty ⊩A) (_⊩ₗId_.⊩Ty ⊩B) Ty≡Ty′
    ; lhs′≡rhs′→lhs≡rhs =
        convEqTerm₁ (_⊩ₗId_.⊩Ty ⊩A) (_⊩ₗId_.⊩Ty ⊩B) Ty≡Ty′ ∘→
        lhs≡rhs→lhs′≡rhs′ ∘→
        convEqTerm₂ (_⊩ₗId_.⊩Ty ⊩A) (_⊩ₗId_.⊩Ty ⊩B) Ty≡Ty′
    } }
  where
  open _⊩ₗId_≡_/_ A≡B

symEqTerm (ℕᵣ D) (ℕₜ₌ k k′ d d′ t≡u prop) =
  ℕₜ₌ k′ k d′ d (≅ₜ-sym t≡u) (symNatural-prop prop)
symEqTerm (Emptyᵣ D) (Emptyₜ₌ k k′ d d′ t≡u prop) =
  Emptyₜ₌ k′ k d′ d (≅ₜ-sym t≡u) (symEmpty-prop prop)
symEqTerm (Unitᵣ _) (Unitₜ₌ k k′ d d′ prop) =
  Unitₜ₌ k′ k d′ d (symUnit-prop prop)
symEqTerm (ne′ _ _ D neK K≡K) (neₜ₌ k m d d′ nf) =
  neₜ₌ m k d′ d (symNeutralTerm nf)
symEqTerm (Bᵣ′ BΠ! F G D A≡A [F] [G] G-ext _)
  (Πₜ₌ f g d d′ funcF funcG f≡g [f≡g]) =
  Πₜ₌ g f d′ d funcG funcF (≅ₜ-sym f≡g)
      (λ ρ ⊩v ⊩w v≡w →
         let w≡v = symEqTerm ([F] ρ) v≡w in
         convEqTerm₁ ([G] ρ ⊩w) ([G] ρ ⊩v) (G-ext ρ ⊩w ⊩v w≡v) $
         symEqTerm ([G] ρ ⊩w) ([f≡g] ρ ⊩w ⊩v w≡v))
symEqTerm (Bᵣ′ BΣˢ F G D A≡A [F] [G] G-ext _)
  (Σₜ₌ p r d d′ pProd rProd p≅r ([fstp] , [fstr] , [fst≡] , [snd≡])) =
  let [Gfstp≡Gfstr] = G-ext _ [fstp] [fstr] [fst≡]
  in  Σₜ₌ r p d′ d rProd pProd (≅ₜ-sym p≅r)
          ([fstr] , [fstp] , (symEqTerm ([F] _) [fst≡]) ,
           convEqTerm₁ ([G] _ [fstp]) ([G] _ [fstr]) [Gfstp≡Gfstr]
             (symEqTerm ([G] _ [fstp]) [snd≡]))
symEqTerm
  (Bᵣ′ BΣʷ F G D A≡A [F] [G] G-ext _)
  (Σₜ₌ p r d d′ prodₙ prodₙ p≅r
     (PE.refl , PE.refl , PE.refl , PE.refl ,
      [p₁] , [r₁] , [fst≡] , [snd≡])) =
  let [Gfstp≡Gfstr] = G-ext _ [p₁] [r₁] [fst≡]
  in  Σₜ₌ r p d′ d prodₙ prodₙ (≅ₜ-sym p≅r)
        (PE.refl , PE.refl , PE.refl , PE.refl ,
         [r₁] , [p₁] ,
         symEqTerm ([F] _) [fst≡] ,
         convEqTerm₁ ([G] _ [p₁]) ([G] _ [r₁]) [Gfstp≡Gfstr]
           (symEqTerm ([G] _ [p₁]) [snd≡]))
symEqTerm (Bᵣ′ BΣʷ F G D A≡A [F] [G] G-ext _)
  (Σₜ₌ p r d d′ (ne x) (ne y) p≅r (inc , p~r)) =
  Σₜ₌ r p d′ d (ne y) (ne x) (≅ₜ-sym p≅r) (inc , ~-sym p~r)
symEqTerm (Bᵣ′ BΣʷ _ _ _ _ _ _ _ _) (Σₜ₌ _ _ _ _ prodₙ  (ne _) _ ())
symEqTerm (Bᵣ′ BΣʷ _ _ _ _ _ _ _ _) (Σₜ₌ _ _ _ _ (ne _) prodₙ  _ ())
symEqTerm (Idᵣ ⊩A) t≡u =
  let ⊩t , ⊩u , _ = ⊩Id≡∷⁻¹ ⊩A t≡u in
  ⊩Id≡∷ ⊩A ⊩u ⊩t
    (case ⊩Id≡∷-view-inhabited ⊩A t≡u of λ where
       (ne inc _ _ t′~u′) → inc , ~-sym t′~u′
       (rfl₌ _)           → _)
symEqTerm
  (Uᵣ′ _ ≤ᵘ-refl _) (Uₜ₌ A B d d′ typeA typeB A≡B [t] [u] [t≡u]) =
    Uₜ₌ B A d′ d typeB typeA (≅ₜ-sym A≡B) [u] [t] (symEq [t] [u] [t≡u])
symEqTerm
  {Γ} {A} {t = B} {u = C} (Uᵣ′ l′ (≤ᵘ-step {n = l} p) A⇒*U) B≡C =
                                                   $⟨ B≡C ⟩
  Γ ⊩⟨ 1+ l ⟩ B ≡ C ∷ A / Uᵣ′ l′ (≤ᵘ-step p) A⇒*U  →⟨ irrelevanceEqTerm (Uᵣ′ l′ (≤ᵘ-step p) A⇒*U) (Uᵣ′ l′ p A⇒*U) ⟩
  Γ ⊩⟨    l ⟩ B ≡ C ∷ A / Uᵣ′ l′ p A⇒*U            →⟨ symEqTerm (Uᵣ′ _ p A⇒*U) ⟩
  Γ ⊩⟨    l ⟩ C ≡ B ∷ A / Uᵣ′ l′ p A⇒*U            →⟨ irrelevanceEqTerm (Uᵣ′ l′ p A⇒*U) (Uᵣ′ l′ (≤ᵘ-step p) A⇒*U) ⟩
  Γ ⊩⟨ 1+ l ⟩ C ≡ B ∷ A / Uᵣ′ l′ (≤ᵘ-step p) A⇒*U  □
