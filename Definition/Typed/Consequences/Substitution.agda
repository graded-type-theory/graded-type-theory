------------------------------------------------------------------------
-- The typing and reduction relations are closed under substitutions.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.Substitution
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M hiding (wk)
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.Weakening R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.LogicalRelation.Fundamental R
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Substitution R

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

private
  variable
    ℓ m n : Nat
    Γ Δ : Con Term n
    A B C C₁ C₂ D E t t₁ t₂ u u₁ u₂ v : Term _
    σ σ′ : Subst m n
    ρ : Wk ℓ m
    p q : M

opaque

  -- A substitution lemma for _⊢_.

  substitution : Γ ⊢ A → Δ ⊢ˢ σ ∷ Γ → ⊢ Δ → Δ ⊢ A [ σ ]
  substitution ⊢A ⊢σ ⊢Δ =
    escape-⊩ $
    ⊩ᵛ→⊩ˢ∷→⊩[] (fundamental-⊩ᵛ ⊢A .proj₂)
      (fundamental-⊩ˢ∷ ⊢Δ (wf ⊢A) ⊢σ)

opaque

  -- A substitution lemma for _⊢_≡_.

  substitutionEq :
    Γ ⊢ A ≡ B → Δ ⊢ˢ σ ≡ σ′ ∷ Γ → ⊢ Δ → Δ ⊢ A [ σ ] ≡ B [ σ′ ]
  substitutionEq A≡B σ≡σ′ ⊢Δ =
    escape-⊩≡ $
    ⊩ᵛ≡⇔ .proj₁ (fundamental-⊩ᵛ≡ A≡B .proj₂) .proj₂ $
    fundamental-⊩ˢ≡∷ ⊢Δ (wfEq A≡B) σ≡σ′

opaque

  -- A substitution lemma for _⊢_∷_.

  substitutionTerm :
    Γ ⊢ t ∷ A → Δ ⊢ˢ σ ∷ Γ → ⊢ Δ → Δ ⊢ t [ σ ] ∷ A [ σ ]
  substitutionTerm ⊢t ⊢σ ⊢Δ =
    escape-⊩∷ $
    ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ (fundamental-⊩ᵛ∷ ⊢t .proj₂)
      (fundamental-⊩ˢ∷ ⊢Δ (wfTerm ⊢t) ⊢σ)

opaque

  -- A substitution lemma for _⊢_≡_∷_.

  substitutionEqTerm :
    Γ ⊢ t ≡ u ∷ A → Δ ⊢ˢ σ ≡ σ′ ∷ Γ → ⊢ Δ →
    Δ ⊢ t [ σ ] ≡ u [ σ′ ] ∷ A [ σ ]
  substitutionEqTerm t≡u σ≡σ′ ⊢Δ =
    escape-⊩≡∷ $
    ⊩ᵛ≡∷⇔ .proj₁ (fundamental-⊩ᵛ≡∷ t≡u .proj₂) .proj₂ $
    fundamental-⊩ˢ≡∷ ⊢Δ (wfEqTerm t≡u) σ≡σ′

-- Reflexivity of well-formed substitution.
substRefl : ∀ {Γ Δ}
          → Δ ⊢ˢ σ ∷ Γ
          → Δ ⊢ˢ σ ≡ σ ∷ Γ
substRefl id = id
substRefl (σ , x) = substRefl σ , refl x

-- Weakening of well-formed substitution.
wkSubst′ : ∀ {Γ Δ Δ′} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ) (⊢Δ′ : ⊢ Δ′)
           ([ρ] : ρ ∷ Δ′ ⊇ Δ)
           ([σ] : Δ ⊢ˢ σ ∷ Γ)
         → Δ′ ⊢ˢ ρ •ₛ σ ∷ Γ
wkSubst′ ε ⊢Δ ⊢Δ′ ρ id = id
wkSubst′ (_∙_ {Γ = Γ} {A} ⊢Γ ⊢A) ⊢Δ ⊢Δ′ ρ (tailσ , headσ) =
  wkSubst′ ⊢Γ ⊢Δ ⊢Δ′ ρ tailσ
  , PE.subst (λ x → _ ⊢ _ ∷ x) (wk-subst A) (wkTerm ρ ⊢Δ′ headσ)

-- Weakening of well-formed substitution by one.
wk1Subst′ : ∀ {F Γ Δ} (⊢Γ : ⊢ Γ)
            (⊢F : Δ ⊢ F)
            ([σ] : Δ ⊢ˢ σ ∷ Γ)
          → (Δ ∙ F) ⊢ˢ wk1Subst σ ∷ Γ
wk1Subst′ {σ = σ} {F} {Γ} {Δ} ⊢Γ ⊢F [σ] =
  wkSubst′ ⊢Γ (wf ⊢F) (⊢→⊢∙ ⊢F) (step id) [σ]

-- Lifting of well-formed substitution.
liftSubst′ : ∀ {F Γ Δ} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ)
             (⊢F  : Γ ⊢ F)
             ([σ] : Δ ⊢ˢ σ ∷ Γ)
           → Δ ∙ F [ σ ] ⊢ˢ liftSubst σ ∷ Γ ∙ F
liftSubst′ {σ = σ} {F} {Γ} {Δ} ⊢Γ ⊢Δ ⊢F [σ] =
  let ⊢Δ∙F = ⊢Δ ∙ substitution ⊢F [σ] ⊢Δ
  in  wkSubst′ ⊢Γ ⊢Δ ⊢Δ∙F (step id) [σ]
  ,   var ⊢Δ∙F (PE.subst (λ x → x0 ∷ x ∈ Δ ∙ F [ σ ])
                         (wk-subst F) here)

-- Well-formed identity substitution.
idSubst′ : (⊢Γ : ⊢ Γ)
         → Γ ⊢ˢ idSubst ∷ Γ
idSubst′ ε = id
idSubst′ (_∙_ {Γ = Γ} {A} ⊢Γ ⊢A) =
  wk1Subst′ ⊢Γ ⊢A (idSubst′ ⊢Γ)
  , PE.subst (λ x → Γ ∙ A ⊢ _ ∷ x) (wk1-tailId A) (var₀ ⊢A)

-- Well-formed substitution composition.
substComp′ : ∀ {Γ Δ Δ′} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ) (⊢Δ′ : ⊢ Δ′)
             ([σ] : Δ′ ⊢ˢ σ ∷ Δ)
             ([σ′] : Δ ⊢ˢ σ′ ∷ Γ)
           → Δ′ ⊢ˢ σ ₛ•ₛ σ′ ∷ Γ
substComp′ ε ⊢Δ ⊢Δ′ [σ] id = id
substComp′ (_∙_ {Γ = Γ} {A} ⊢Γ ⊢A) ⊢Δ ⊢Δ′ [σ] ([tailσ′] , [headσ′]) =
  substComp′ ⊢Γ ⊢Δ ⊢Δ′ [σ] [tailσ′]
  , PE.subst (λ x → _ ⊢ _ ∷ x) (substCompEq A)
             (substitutionTerm [headσ′] [σ] ⊢Δ′)

-- Well-formed singleton substitution of terms.
singleSubst : ∀ {A t} → Γ ⊢ t ∷ A → Γ ⊢ˢ sgSubst t ∷ Γ ∙ A
singleSubst {A = A} t =
  let ⊢Γ = wfTerm t
  in  idSubst′ ⊢Γ , PE.subst (λ x → _ ⊢ _ ∷ x) (PE.sym (subst-id A)) t

-- Well-formed singleton substitution of term equality.
singleSubstEq : ∀ {A t u} → Γ ⊢ t ≡ u ∷ A
              → Γ ⊢ˢ sgSubst t ≡ sgSubst u ∷ Γ ∙ A
singleSubstEq {A = A} t =
  let ⊢Γ = wfEqTerm t
  in  substRefl (idSubst′ ⊢Γ) , PE.subst (λ x → _ ⊢ _ ≡ _ ∷ x) (PE.sym (subst-id A)) t

opaque

  -- A substitution lemma related to _[_]↑.

  singleSubst↑ :
    Γ ∙ A ⊢ t ∷ wk1 B →
    Γ ∙ A ⊢ˢ consSubst (wk1Subst idSubst) t ∷ Γ ∙ B
  singleSubst↑ {A} t =
    case wfTerm t of λ {
      (⊢Γ ∙ ⊢A) →
      wk1Subst′ ⊢Γ ⊢A (idSubst′ ⊢Γ)
    , PE.subst (_⊢_∷_ _ _) (wk1-tailId _) t }

-- Well-formed singleton substitution of term equality with lifting.
singleSubst↑Eq : ∀ {A t u} → Γ ∙ A ⊢ t ≡ u ∷ wk1 A
              → Γ ∙ A ⊢ˢ consSubst (wk1Subst idSubst) t ≡ consSubst (wk1Subst idSubst) u ∷ Γ ∙ A
singleSubst↑Eq {A = A} t with wfEqTerm t
... | ⊢Γ ∙ ⊢A = substRefl (wk1Subst′ ⊢Γ ⊢A (idSubst′ ⊢Γ))
              , PE.subst (λ x → _ ∙ A ⊢ _ ≡ _ ∷ x) (wk1-tailId A) t

-- Helper lemmas for single substitution

substType : ∀ {t F G} → Γ ∙ F ⊢ G → Γ ⊢ t ∷ F → Γ ⊢ G [ t ]₀
substType {t = t} {F} {G} ⊢G ⊢t =
  let ⊢Γ = wfTerm ⊢t
  in  substitution ⊢G (singleSubst ⊢t) ⊢Γ

substTypeEq : ∀ {t u F G E} → Γ ∙ F ⊢ G ≡ E → Γ ⊢ t ≡ u ∷ F → Γ ⊢ G [ t ]₀ ≡ E [ u ]₀
substTypeEq {F = F} ⊢G ⊢t =
  let ⊢Γ = wfEqTerm ⊢t
  in  substitutionEq ⊢G (singleSubstEq ⊢t) ⊢Γ

substTerm : ∀ {F G t f} → Γ ∙ F ⊢ f ∷ G → Γ ⊢ t ∷ F → Γ ⊢ f [ t ]₀ ∷ G [ t ]₀
substTerm {F = F} {G} {t} {f} ⊢f ⊢t =
  let ⊢Γ = wfTerm ⊢t
  in  substitutionTerm ⊢f (singleSubst ⊢t) ⊢Γ

opaque

  -- A substitution lemma for term equality.

  substTermEq :
    Γ ∙ A ⊢ t₁ ≡ t₂ ∷ B → Γ ⊢ u₁ ≡ u₂ ∷ A →
    Γ ⊢ t₁ [ u₁ ]₀ ≡ t₂ [ u₂ ]₀ ∷ B [ u₁ ]₀
  substTermEq t₁≡t₂ u₁≡u₂ =
    substitutionEqTerm t₁≡t₂ (singleSubstEq u₁≡u₂) (wfEqTerm u₁≡u₂)

substTypeΠ : ∀ {t F G} → Γ ⊢ Π p , q ▷ F ▹ G → Γ ⊢ t ∷ F → Γ ⊢ G [ t ]₀
substTypeΠ ΠFG t with syntacticΠ ΠFG
substTypeΠ ΠFG t | F , G = substType G t

opaque

  -- A substitution lemma related to _[_]↑.

  subst↑Type : Γ ∙ B ⊢ C → Γ ∙ A ⊢ t ∷ wk1 B → Γ ∙ A ⊢ C [ t ]↑
  subst↑Type ⊢C ⊢t = substitution ⊢C (singleSubst↑ ⊢t) (wfTerm ⊢t)

subst↑TypeEq : ∀ {t u F G E}
             → Γ ∙ F ⊢ G ≡ E
             → Γ ∙ F ⊢ t ≡ u ∷ wk1 F
             → Γ ∙ F ⊢ G [ t ]↑ ≡ E [ u ]↑
subst↑TypeEq ⊢G ⊢t = substitutionEq ⊢G (singleSubst↑Eq ⊢t) (wfEqTerm ⊢t)

opaque

  -- A substitution lemma related to _[_]↑².

  subst↑²Type :
    Γ ∙ A ⊢ B →
    Γ ∙ C ∙ D ⊢ t ∷ wk2 A →
    Γ ∙ C ∙ D ⊢ B [ t ]↑²
  subst↑²Type {A} ⊢B ⊢t =
    case wfTerm ⊢t of λ {
      ⊢ΓCD@(⊢Γ ∙ ⊢C ∙ ⊢D) →
    substitution ⊢B
      ( wk1Subst′ ⊢Γ ⊢D (wk1Subst′ ⊢Γ ⊢C (idSubst′ ⊢Γ))
      , PE.subst (_⊢_∷_ _ _) (wk[]≡[] 2) ⊢t
      )
      ⊢ΓCD }

subst↑²Type-prod : ∀ {m F G A}
                 → Γ ∙ (Σ⟨ m ⟩ p , q ▷ F ▹ G) ⊢ A
                 → Σ-allowed m p q
                 → Γ ∙ F ∙ G ⊢ A [ prod m p (var x1) (var x0) ]↑²
subst↑²Type-prod {Γ = Γ} {F = F} {G} {A} ⊢A ok =
  let ⊢ΓΣ = wf ⊢A
      ⊢Γ , ⊢Σ = splitCon ⊢ΓΣ
      ⊢F , ⊢G = syntacticΣ ⊢Σ
      ⊢ΓFG = ⊢Γ ∙ ⊢F ∙ ⊢G
      ⊢ρF = wk (step (step id)) ⊢ΓFG ⊢F
      ⊢ρG = wk (lift (step (step id))) (⊢ΓFG ∙ ⊢ρF) ⊢G
      ⊢ρF′ = PE.subst (λ x → _ ⊢ x) (wk≡subst (step (step id)) F) ⊢ρF
      ⊢ρG′ = PE.subst₂ (λ x y → (Γ ∙ F ∙ G ∙ x) ⊢ y)
                       (wk≡subst (step (step id)) F)
                       (PE.trans (wk≡subst (lift (step (step id))) G)
                                 (substVar-to-subst (λ{x0 → PE.refl
                                                    ; (x +1) → PE.refl}) G))
                       ⊢ρG
      var1 = PE.subst (λ x → Γ ∙ F ∙ G ⊢ var (x0 +1) ∷ x)
                      (PE.trans (wk-comp (step id) (step id) F)
                                (wk≡subst (step id • step id) F))
                      (var₁ ⊢G)
      var0 = PE.subst (λ x → Γ ∙ F ∙ G ⊢ var x0 ∷ x)
                      (PE.trans (wk≡subst (step id) G)
                                (PE.trans (substVar-to-subst (λ{x0 → PE.refl
                                                             ; (x +1) → PE.refl}) G)
                                          (PE.sym (substCompEq G))))
                      (var₀ ⊢G)
  in  substitution ⊢A
                   (wk1Subst′ ⊢Γ ⊢G (wk1Subst′ ⊢Γ ⊢F (idSubst′ ⊢Γ))
                   , prodⱼ ⊢ρF′ ⊢ρG′ var1 var0 ok)
                   ⊢ΓFG
  where
  splitCon : ∀ {Γ : Con Term n} {F} → ⊢ (Γ ∙ F) → ⊢ Γ × Γ ⊢ F
  splitCon (x ∙ x₁) = x , x₁

opaque

  -- A substitution lemma related to _[_]↑².

  subst↑²TypeEq :
    Γ ∙ A ⊢ B ≡ C →
    Γ ∙ D ∙ E ⊢ t ≡ u ∷ wk2 A →
    Γ ∙ D ∙ E ⊢ B [ t ]↑² ≡ C [ u ]↑²
  subst↑²TypeEq {A} B≡C t≡u =
    case wfEqTerm t≡u of λ {
      ⊢ΓDE@(⊢Γ ∙ ⊢D ∙ ⊢E) →
    substitutionEq B≡C
      ( substRefl (wk1Subst′ ⊢Γ ⊢E (wk1Subst′ ⊢Γ ⊢D (idSubst′ ⊢Γ)))
      , PE.subst (_⊢_≡_∷_ _ _ _) (wk[]≡[] 2) t≡u
      )
      ⊢ΓDE }

subst↑²TypeEq-prod : ∀ {m F G A B}
              → Γ ∙ (Σ⟨ m ⟩ p , q ▷ F ▹ G) ⊢ A ≡ B
              → Σ-allowed m p q
              → Γ ∙ F ∙ G ⊢ A [ prod m p (var x1) (var x0) ]↑²
                          ≡ B [ prod m p (var x1) (var x0) ]↑²
subst↑²TypeEq-prod {Γ = Γ} {F = F} {G} {A} {B} A≡B ok =
  let ⊢A , ⊢B = syntacticEq A≡B
      ⊢ΓΣ = wf ⊢A
      ⊢Γ , ⊢Σ = splitCon ⊢ΓΣ
      ⊢F , ⊢G = syntacticΣ ⊢Σ
      ⊢ΓFG = ⊢Γ ∙ ⊢F ∙ ⊢G
      ⊢ρF = wk (step (step id)) ⊢ΓFG ⊢F
      ⊢ρG = wk (lift (step (step id))) (⊢ΓFG ∙ ⊢ρF) ⊢G
      ⊢ρF′ = PE.subst (λ x → _ ⊢ x) (wk≡subst (step (step id)) F) ⊢ρF
      ⊢ρG′ = PE.subst₂ (λ x y → (Γ ∙ F ∙ G ∙ x) ⊢ y)
                       (wk≡subst (step (step id)) F)
                       (PE.trans (wk≡subst (lift (step (step id))) G)
                                 (substVar-to-subst (λ{x0 → PE.refl
                                                    ; (x +1) → PE.refl}) G))
                       ⊢ρG
      var1 = PE.subst (λ x → Γ ∙ F ∙ G ⊢ var (x0 +1) ∷ x)
                      (PE.trans (wk-comp (step id) (step id) F)
                                (wk≡subst (step id • step id) F))
                      (var₁ ⊢G)
      var0 = PE.subst (λ x → Γ ∙ F ∙ G ⊢ var x0 ∷ x)
                      (PE.trans (wk≡subst (step id) G)
                                (PE.trans (substVar-to-subst (λ{x0 → PE.refl
                                                             ; (x +1) → PE.refl}) G)
                                          (PE.sym (substCompEq G))))
                      (var₀ ⊢G)
  in  substitutionEq A≡B
                     (substRefl (wk1Subst′ ⊢Γ ⊢G
                                           (wk1Subst′ ⊢Γ ⊢F
                                                      (idSubst′ ⊢Γ))
                                , prodⱼ ⊢ρF′ ⊢ρG′ var1 var0 ok))
                     ⊢ΓFG
  where
  splitCon : ∀ {Γ : Con Term n} {F} → ⊢ (Γ ∙ F) → ⊢ Γ × Γ ⊢ F
  splitCon (x ∙ x₁) = x , x₁

opaque

  -- A variant of substType for _[_,_]₁₀.

  substType₂ :
    Γ ∙ A ∙ B ⊢ C → Γ ⊢ t ∷ A → Γ ⊢ u ∷ B [ t ]₀ → Γ ⊢ C [ t , u ]₁₀
  substType₂ ⊢C ⊢t ⊢u =
    substitution ⊢C (singleSubst ⊢t , ⊢u) (wfTerm ⊢t)

opaque

  -- A variant of substTypeEq for _[_,_]₁₀.

  substTypeEq₂ :
    Γ ∙ A ∙ B ⊢ C₁ ≡ C₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ A →
    Γ ⊢ u₁ ≡ u₂ ∷ B [ t₁ ]₀ →
    Γ ⊢ C₁ [ t₁ , u₁ ]₁₀ ≡ C₂ [ t₂ , u₂ ]₁₀
  substTypeEq₂ C₁≡C₂ t₁≡t₂ u₁≡u₂ =
    substitutionEq C₁≡C₂ (singleSubstEq t₁≡t₂ , u₁≡u₂) (wfEqTerm t₁≡t₂)

opaque

  -- A variant of substTerm for _[_,_]₁₀.

  substTerm₂ :
    Γ ∙ A ∙ B ⊢ t ∷ C → Γ ⊢ u ∷ A → Γ ⊢ v ∷ B [ u ]₀ →
    Γ ⊢ t [ u , v ]₁₀ ∷ C [ u , v ]₁₀
  substTerm₂ ⊢t ⊢u ⊢v =
    substitutionTerm ⊢t (singleSubst ⊢u , ⊢v) (wfTerm ⊢u)

opaque

  -- Well-formed substitution of term reduction.

  substitutionRedTerm :
    Γ ⊢ t ⇒ u ∷ A →
    Δ ⊢ˢ σ ∷ Γ →
    ⊢ Δ →
    Δ ⊢ t [ σ ] ⇒ u [ σ ] ∷ A [ σ ]
  substitutionRedTerm (conv d x) ⊢σ ⊢Δ =
    conv (substitutionRedTerm d ⊢σ ⊢Δ) (substitutionEq x (substRefl ⊢σ) ⊢Δ)
  substitutionRedTerm (app-subst {G = G} {a} d x) ⊢σ ⊢Δ =
    PE.subst (_ ⊢ _ ⇒ _ ∷_) (PE.sym (singleSubstLift G a))
      (app-subst (substitutionRedTerm d ⊢σ ⊢Δ) (substitutionTerm x ⊢σ ⊢Δ))
  substitutionRedTerm {σ} (β-red {G = G} {t} {a} x x₁ x₂ x₃ x₄ x₅) ⊢σ ⊢Δ =
    case substitution x ⊢σ ⊢Δ of λ
      ⊢σF →
    case liftSubst′ (wf x) ⊢Δ x ⊢σ of λ
      ⊢⇑σ →
    PE.subst₂ (_ ⊢ (lam _ t ∘ a) [ σ ] ⇒_∷_)
      (PE.sym (singleSubstLift t a))
      (PE.sym (singleSubstLift G a))
      (β-red ⊢σF (substitution x₁ ⊢⇑σ (⊢Δ ∙ ⊢σF))
        (substitutionTerm x₂ ⊢⇑σ (⊢Δ ∙ ⊢σF))
        (substitutionTerm x₃ ⊢σ ⊢Δ) x₄ x₅)
  substitutionRedTerm (fst-subst x x₁ d) ⊢σ ⊢Δ =
    case substitution x ⊢σ ⊢Δ of λ
      ⊢σA →
    fst-subst ⊢σA
      (substitution x₁ (liftSubst′ (wf x) ⊢Δ x ⊢σ) (⊢Δ ∙ ⊢σA))
      (substitutionRedTerm d ⊢σ ⊢Δ)
  substitutionRedTerm (snd-subst {G = G} {t} x x₁ d) ⊢σ ⊢Δ =
    case substitution x ⊢σ ⊢Δ of λ
      ⊢σA →
    PE.subst (_ ⊢ _ ⇒ _ ∷_)
      (PE.sym (singleSubstLift G (fst _ t)))
      (snd-subst ⊢σA
        (substitution x₁ (liftSubst′ (wf x) ⊢Δ x ⊢σ) (⊢Δ ∙ ⊢σA))
        (substitutionRedTerm d ⊢σ ⊢Δ))
  substitutionRedTerm (Σ-β₁ {G = G} {t} x x₁ x₂ x₃ x₄ x₅) ⊢σ ⊢Δ =
    case substitution x ⊢σ ⊢Δ of λ
      ⊢σA →
    Σ-β₁ ⊢σA
      (substitution x₁ (liftSubst′ (wf x) ⊢Δ x ⊢σ) (⊢Δ ∙ ⊢σA))
      (substitutionTerm x₂ ⊢σ ⊢Δ)
      (PE.subst (_ ⊢ _ ∷_) (singleSubstLift G t) (substitutionTerm x₃ ⊢σ ⊢Δ))
      x₄ x₅
  substitutionRedTerm (Σ-β₂ {G = G} x x₁ x₂ x₃ x₄ x₅) ⊢σ ⊢Δ =
    case substitution x ⊢σ ⊢Δ of λ
      ⊢σA →
    PE.subst (_ ⊢ _ ⇒ _ ∷_)
      (PE.sym (singleSubstLift G _))
      (Σ-β₂ ⊢σA (substitution x₁ (liftSubst′ (wf x) ⊢Δ x ⊢σ) (⊢Δ ∙ ⊢σA))
        (substitutionTerm x₂ ⊢σ ⊢Δ)
        (PE.subst (_ ⊢ _ ∷_) (singleSubstLift G _) (substitutionTerm x₃ ⊢σ ⊢Δ))
        x₄ x₅)
  substitutionRedTerm {σ} (prodrec-subst {A = A} {u = u} {t = t} x x₁ x₂ x₃ d x₄) ⊢σ ⊢Δ =
    case substitution x ⊢σ ⊢Δ of λ
      ⊢σA →
    case liftSubst′ (wf x) ⊢Δ x ⊢σ of λ
      ⊢⇑σ →
    case substitution x₁ ⊢⇑σ (⊢Δ ∙ ⊢σA) of λ
      ⊢σB →
    PE.subst (_ ⊢ prodrec _ _ _ A t u [ σ ] ⇒ _ ∷_)
      (PE.sym (singleSubstLift A t))
      (prodrec-subst ⊢σA ⊢σB
        (substitution x₂ (liftSubst′ (wf x) ⊢Δ (ΠΣⱼ x x₁ x₄) ⊢σ) (⊢Δ ∙ ΠΣⱼ ⊢σA ⊢σB x₄))
        (PE.subst (_ ⊢ _ ∷_) (subst-β-prodrec A σ)
          (substitutionTerm x₃ (liftSubst′ (wf x ∙ x) (⊢Δ ∙ ⊢σA) x₁ ⊢⇑σ) (⊢Δ ∙ ⊢σA ∙ ⊢σB)))
        (substitutionRedTerm d ⊢σ ⊢Δ) x₄)
  substitutionRedTerm {σ} (prodrec-β {G = G} {A = A} {t} {t′} {u} x x₁ x₂ x₃ x₄ x₅ x₆ x₇) ⊢σ ⊢Δ =
    case substitution x ⊢σ ⊢Δ of λ
      ⊢σA →
    case liftSubst′ (wf x) ⊢Δ x ⊢σ of λ
      ⊢⇑σ →
    case substitution x₁ ⊢⇑σ (⊢Δ ∙ ⊢σA) of λ
      ⊢σB →
    PE.subst₂ (_ ⊢ prodrec _ _ _ A (prod! t t′) u [ σ ] ⇒_∷_)
      (PE.sym ([,]-[]-commute u))
      (PE.sym (singleSubstLift A _))
      (prodrec-β ⊢σA ⊢σB
        (substitution x₂ (liftSubst′ (wf x) ⊢Δ (ΠΣⱼ x x₁ x₇) ⊢σ) (⊢Δ ∙ ΠΣⱼ ⊢σA ⊢σB x₇))
        (substitutionTerm x₃ ⊢σ ⊢Δ)
        (PE.subst (_ ⊢ _ ∷_) (singleSubstLift G _)
          (substitutionTerm x₄ ⊢σ ⊢Δ))
        (PE.subst (_ ⊢ _ ∷_) (subst-β-prodrec A σ)
          (substitutionTerm x₅ (liftSubst′ (wf x ∙ x) (⊢Δ ∙ ⊢σA) x₁ ⊢⇑σ) (⊢Δ ∙ ⊢σA ∙ ⊢σB)))
        x₆ x₇)
  substitutionRedTerm {σ} (natrec-subst {A = A} {z} {s} {n = n} x x₁ x₂ d) ⊢σ ⊢Δ =
    case wfTerm x₁ of λ
      ⊢Γ →
    case liftSubst′ ⊢Γ ⊢Δ (ℕⱼ ⊢Γ) ⊢σ of λ
      ⊢⇑σ →
    case substitution x ⊢⇑σ (⊢Δ ∙ ℕⱼ ⊢Δ) of λ
      ⊢σA →
    PE.subst (_ ⊢ natrec _ _ _ A z s n [ σ ] ⇒ _ ∷_)
      (PE.sym (singleSubstLift A n))
      (natrec-subst ⊢σA
        (PE.subst (_ ⊢ _ ∷_) (singleSubstLift A zero) (substitutionTerm x₁ ⊢σ ⊢Δ))
        (PE.subst (_ ∙ ℕ ∙ A [ liftSubst σ ] ⊢ _ ∷_) (natrecSucCase σ A)
          (substitutionTerm x₂ (liftSubst′ (⊢Γ ∙ ℕⱼ ⊢Γ) (⊢Δ ∙ ℕⱼ ⊢Δ) x ⊢⇑σ) (⊢Δ ∙ ℕⱼ ⊢Δ ∙ ⊢σA)))
        (substitutionRedTerm d ⊢σ ⊢Δ))
  substitutionRedTerm {σ} (natrec-zero {A = A} {z} {s} x x₁ x₂) ⊢σ ⊢Δ =
    case wfTerm x₁ of λ
      ⊢Γ →
    case liftSubst′ ⊢Γ ⊢Δ (ℕⱼ ⊢Γ) ⊢σ of λ
      ⊢⇑σ →
    case substitution x ⊢⇑σ (⊢Δ ∙ ℕⱼ ⊢Δ) of λ
      ⊢σA →
    PE.subst (_ ⊢ natrec _ _ _ A z s zero [ σ ] ⇒ _ ∷_)
      (PE.sym (singleSubstLift A zero))
      (natrec-zero ⊢σA
        (PE.subst (_ ⊢ _ ∷_) (singleSubstLift A zero) (substitutionTerm x₁ ⊢σ ⊢Δ))
        (PE.subst ((_ ∙ ℕ ∙ A [ liftSubst σ ]) ⊢ _ ∷_) (natrecSucCase σ A)
        (substitutionTerm x₂ (liftSubst′ (⊢Γ ∙ ℕⱼ ⊢Γ) (⊢Δ ∙ ℕⱼ ⊢Δ) x ⊢⇑σ) (⊢Δ ∙ ℕⱼ ⊢Δ ∙ ⊢σA))))
  substitutionRedTerm {σ} (natrec-suc {A = A} {z} {s} {n = n} x x₁ x₂ x₃) ⊢σ ⊢Δ =
    case wfTerm x₁ of λ
      ⊢Γ →
    case liftSubst′ ⊢Γ ⊢Δ (ℕⱼ ⊢Γ) ⊢σ of λ
      ⊢⇑σ →
    case substitution x ⊢⇑σ (⊢Δ ∙ ℕⱼ ⊢Δ) of λ
      ⊢σA →
    PE.subst₂ (_ ⊢ natrec _ _ _ A z s (suc n) [ σ ] ⇒_∷_)
      (PE.sym ([,]-[]-commute s))
      (PE.sym (singleSubstLift A (suc n)))
      (natrec-suc ⊢σA
        (PE.subst (_ ⊢ _ ∷_) (singleSubstLift A zero) (substitutionTerm x₁ ⊢σ ⊢Δ))
        (PE.subst ((_ ∙ ℕ ∙ A [ liftSubst σ ]) ⊢ _ ∷_) (natrecSucCase σ A)
          (substitutionTerm x₂ (liftSubst′ (⊢Γ ∙ ℕⱼ ⊢Γ) (⊢Δ ∙ ℕⱼ ⊢Δ) x ⊢⇑σ) (⊢Δ ∙ ℕⱼ ⊢Δ ∙ ⊢σA)))
        (substitutionTerm x₃ ⊢σ ⊢Δ))
  substitutionRedTerm (emptyrec-subst x d) ⊢σ ⊢Δ =
    emptyrec-subst (substitution x ⊢σ ⊢Δ) (substitutionRedTerm d ⊢σ ⊢Δ)
  substitutionRedTerm {σ} (unitrec-subst {A = A} {u} {t} x x₁ d x₂ x₃) ⊢σ ⊢Δ =
    PE.subst (_⊢_⇒_∷_ _ _ _)
      (PE.sym (singleSubstLift A t))
      (unitrec-subst
        (substitution x (liftSubst′ (wfTerm x₁) ⊢Δ (Unitⱼ (wfTerm x₁) x₂) ⊢σ) (⊢Δ ∙ Unitⱼ ⊢Δ x₂))
        (PE.subst (_ ⊢ _ ∷_) (singleSubstLift A _) $
         substitutionTerm x₁ ⊢σ ⊢Δ)
        (substitutionRedTerm d ⊢σ ⊢Δ) x₂ x₃)
  substitutionRedTerm {σ} (unitrec-β {A = A} {u} x x₁ x₂ x₃) ⊢σ ⊢Δ =
    PE.subst (_⊢_⇒_∷_ _ _ _)
      (PE.sym (singleSubstLift A _))
      (unitrec-β
        (substitution x (liftSubst′ (wfTerm x₁) ⊢Δ (Unitⱼ (wfTerm x₁) x₂) ⊢σ) (⊢Δ ∙ Unitⱼ ⊢Δ x₂))
        (PE.subst (_ ⊢ _ ∷_) (singleSubstLift A _) $
         substitutionTerm x₁ ⊢σ ⊢Δ)
        x₂ x₃)
  substitutionRedTerm {σ} (unitrec-β-η {A} {t} {u} x x₁ x₂ x₃ x₄) ⊢σ ⊢Δ =
    PE.subst (_⊢_⇒_∷_ _ _ _)
      (PE.sym (singleSubstLift A t))
      (unitrec-β-η
        (substitution x (liftSubst′ (wfTerm x₁) ⊢Δ (Unitⱼ (wfTerm x₁) x₃) ⊢σ) (⊢Δ ∙ Unitⱼ ⊢Δ x₃))
        (substitutionTerm x₁ ⊢σ ⊢Δ)
        (PE.subst (_ ⊢ _ ∷_) (singleSubstLift A _) $
         substitutionTerm x₂ ⊢σ ⊢Δ)
        x₃ x₄)
  substitutionRedTerm {σ} (J-subst {A = A} {t} {B} {u} {v} {w₁} x x₁ x₂ x₃ x₄ d) ⊢σ ⊢Δ =
    case substitution x ⊢σ ⊢Δ of λ
      ⊢σA →
    case wf x₂ of λ {
      (⊢Γ ∙ _ ∙ ⊢Id) →
    case liftSubst′ ⊢Γ ⊢Δ x ⊢σ of
      λ ⊢⇑σ →
    case substitution ⊢Id ⊢⇑σ (⊢Δ ∙ ⊢σA) of λ
      ⊢σId →
    case substitution x₂
           (liftSubst′ (⊢Γ ∙ x) (⊢Δ ∙ ⊢σA) ⊢Id ⊢⇑σ)
           (⊢Δ ∙ ⊢σA ∙ ⊢σId) of λ
      ⊢σB →
    PE.subst (_ ⊢ J _ _ A t B u v w₁ [ σ ] ⇒ _ ∷_)
      (PE.sym ([,]-[]-commute B))
      (J-subst ⊢σA (substitutionTerm x₁ ⊢σ ⊢Δ)
        (PE.subst₂ (λ x y → _ ∙ A [ σ ] ∙ Id x y (var x0) ⊢ _)
          (wk1-liftSubst A) (wk1-liftSubst t) ⊢σB)
        (PE.subst (_ ⊢ _ ∷_) ([,]-[]-commute B) (substitutionTerm x₃ ⊢σ ⊢Δ))
        (substitutionTerm x₄ ⊢σ ⊢Δ)
        (substitutionRedTerm d ⊢σ ⊢Δ)) }
  substitutionRedTerm {σ} (K-subst {A = A} {t} {B} {u} {v₁} x x₁ x₂ x₃ d x₄) ⊢σ ⊢Δ =
    case substitution x ⊢σ ⊢Δ of λ
      ⊢σA →
    case substitutionTerm x₁ ⊢σ ⊢Δ of λ
      ⊢σt →
    PE.subst (_ ⊢ K _ A t B u v₁ [ σ ] ⇒ _ ∷_)
      (PE.sym (singleSubstLift B v₁))
      (K-subst ⊢σA ⊢σt
        (substitution x₂ (liftSubst′ (wf x) ⊢Δ (Idⱼ x₁ x₁) ⊢σ) (⊢Δ ∙ Idⱼ ⊢σt ⊢σt))
        (PE.subst (_ ⊢ _ ∷_) (singleSubstLift B rfl) (substitutionTerm x₃ ⊢σ ⊢Δ))
        (substitutionRedTerm d ⊢σ ⊢Δ) x₄)
  substitutionRedTerm ([]-cong-subst x x₁ x₂ d x₃) ⊢σ ⊢Δ =
    []-cong-subst (substitution x ⊢σ ⊢Δ) (substitutionTerm x₁ ⊢σ ⊢Δ)
      (substitutionTerm x₂ ⊢σ ⊢Δ) (substitutionRedTerm d ⊢σ ⊢Δ) x₃
  substitutionRedTerm {σ} (J-β {A = A} {t} {t′} {B} {u} x x₁ x₂ x₃ x₄ x₅ x₆) ⊢σ ⊢Δ =
    case substitution x ⊢σ ⊢Δ of λ
      ⊢σA →
    case wf x₄ of λ {
      (⊢Γ ∙ _ ∙ ⊢Id) →
    case liftSubst′ ⊢Γ ⊢Δ x ⊢σ of
      λ ⊢⇑σ →
    case substitution ⊢Id ⊢⇑σ (⊢Δ ∙ ⊢σA) of λ
      ⊢σId →
    case substitution x₄
           (liftSubst′ (⊢Γ ∙ x) (⊢Δ ∙ ⊢σA) ⊢Id ⊢⇑σ)
           (⊢Δ ∙ ⊢σA ∙ ⊢σId) of λ
      ⊢σB →
    case substitutionTerm x₁ ⊢σ ⊢Δ of λ
      ⊢σt →
    case substitutionEqTerm x₃ (substRefl ⊢σ) ⊢Δ of λ
      ⊢σt≡σt′ →
    case PE.subst (λ x → _ ⊢ rfl ∷ Id ((wk1 A [ liftSubst σ ]) [ t [ σ ] ]₀) x (t [ σ ]))
           (lemma t t)
           (rflⱼ (PE.subst (_ ⊢ _ ∷_) (lemma A t) ⊢σt)) of λ
      ⊢rfl →
    PE.subst (_ ⊢ J _ _ A t B u t′ rfl [ σ ] ⇒ _ ∷_)
      (PE.sym ([,]-[]-commute B))
        (J-β ⊢σA ⊢σt
          (substitutionTerm x₂ ⊢σ ⊢Δ) ⊢σt≡σt′
          (PE.subst₂ (λ x y → (_ ∙ A [ σ ] ∙ Id x y (var x0)) ⊢ _)
            (wk1-liftSubst A) (wk1-liftSubst t) ⊢σB)
          (substTypeEq₂ (refl ⊢σB) ⊢σt≡σt′ (refl ⊢rfl))
          (PE.subst (_ ⊢ _ ∷_) ([,]-[]-commute B) (substitutionTerm x₆ ⊢σ ⊢Δ)))}
    where
    lemma : ∀ t u → t [ σ ] PE.≡ wk1 t [ liftSubst σ ] [ u [ σ ] ]₀
    lemma t u =
      PE.sym (PE.trans (PE.cong (_[ u [ σ ] ]₀) (wk1-liftSubst t))
        (wk1-sgSubst (t [ σ ]) _))
  substitutionRedTerm {σ} (K-β {t = t} {A} {B} {u} x x₁ x₂ x₃) ⊢σ ⊢Δ =
    case wf x₁ of λ {
      (⊢Γ ∙ ⊢Id) →
    PE.subst (_ ⊢ K _ A t B u rfl [ σ ] ⇒ _ ∷_)
      (PE.sym (singleSubstLift B rfl))
      (K-β (substitutionTerm x ⊢σ ⊢Δ)
        (substitution x₁ (liftSubst′ ⊢Γ ⊢Δ ⊢Id ⊢σ)
          (⊢Δ ∙ substitution ⊢Id ⊢σ ⊢Δ))
        (PE.subst (_ ⊢ _ ∷_) (singleSubstLift B rfl) (substitutionTerm x₂ ⊢σ ⊢Δ))
        x₃)}
  substitutionRedTerm ([]-cong-β  x x₁ x₂ x₃ x₄) ⊢σ ⊢Δ =
    []-cong-β (substitution x ⊢σ ⊢Δ)
      (substitutionTerm x₁ ⊢σ ⊢Δ)
      (substitutionTerm x₂ ⊢σ ⊢Δ)
      (substitutionEqTerm x₃ (substRefl ⊢σ) ⊢Δ) x₄

opaque

  -- Well-formed substitution of term reduction closure.

  substitutionRed*Term :
    Γ ⊢ t ⇒* u ∷ A →
    Δ ⊢ˢ σ ∷ Γ →
    ⊢ Δ →
    Δ ⊢ t [ σ ] ⇒* u [ σ ] ∷ A [ σ ]
  substitutionRed*Term (id x) ⊢σ ⊢Δ =
    id (substitutionTerm x ⊢σ ⊢Δ)
  substitutionRed*Term (x ⇨ d) ⊢σ ⊢Δ =
    substitutionRedTerm x ⊢σ ⊢Δ ⇨ substitutionRed*Term d ⊢σ ⊢Δ

opaque

  -- Well-formed substitution of type reduction.

  substitutionRed :
    Γ ⊢ A ⇒ B →
    Δ ⊢ˢ σ ∷ Γ →
    ⊢ Δ →
    Δ ⊢ A [ σ ] ⇒ B [ σ ]
  substitutionRed (univ x) ⊢σ ⊢Δ =
    univ (substitutionRedTerm x ⊢σ ⊢Δ)

opaque

  -- Well-formed substitution of type reduction closure.

  substitutionRed* :
    Γ ⊢ A ⇒* B →
    Δ ⊢ˢ σ ∷ Γ →
    ⊢ Δ →
    Δ ⊢ A [ σ ] ⇒* B [ σ ]
  substitutionRed* (id x) ⊢σ ⊢Δ =
    id (substitution x ⊢σ ⊢Δ)
  substitutionRed* (x ⇨ d) ⊢σ ⊢Δ =
    substitutionRed x ⊢σ ⊢Δ ⇨ substitutionRed* d ⊢σ ⊢Δ
