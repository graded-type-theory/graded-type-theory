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

private
  variable
    ℓ m n : Nat
    Γ Δ : Con Term n
    A B C C₁ C₂ t t₁ t₂ u u₁ u₂ v : Term _
    σ σ′ : Subst m n
    ρ : Wk ℓ m
    p q : M

opaque

  -- A substitution lemma for _⊢_.

  substitution : Γ ⊢ A → Δ ⊢ˢ σ ∷ Γ → ⊢ Δ → Δ ⊢ A [ σ ]
  substitution ⊢A ⊢σ ⊢Δ =
    escape-⊩ $
    ⊩ᵛ→⊩ˢ∷→⊩[] (fundamental-⊩ᵛ ⊢A) (fundamental-⊩ˢ∷ ⊢Δ (wf ⊢A) ⊢σ)

opaque

  -- A substitution lemma for _⊢_≡_.

  substitutionEq :
    Γ ⊢ A ≡ B → Δ ⊢ˢ σ ≡ σ′ ∷ Γ → ⊢ Δ → Δ ⊢ A [ σ ] ≡ B [ σ′ ]
  substitutionEq A≡B σ≡σ′ ⊢Δ =
    escape-⊩≡ $
    ⊩ᵛ≡⇔′ .proj₁ (fundamental-⊩ᵛ≡ A≡B) .proj₂ .proj₂ $
    fundamental-⊩ˢ≡∷ ⊢Δ (wfEq A≡B) σ≡σ′

opaque

  -- A substitution lemma for _⊢_∷_.

  substitutionTerm :
    Γ ⊢ t ∷ A → Δ ⊢ˢ σ ∷ Γ → ⊢ Δ → Δ ⊢ t [ σ ] ∷ A [ σ ]
  substitutionTerm ⊢t ⊢σ ⊢Δ =
    escape-⊩∷ $
    ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ (fundamental-⊩ᵛ∷ ⊢t)
      (fundamental-⊩ˢ∷ ⊢Δ (wfTerm ⊢t) ⊢σ)

opaque

  -- A substitution lemma for _⊢_≡_∷_.

  substitutionEqTerm :
    Γ ⊢ t ≡ u ∷ A → Δ ⊢ˢ σ ≡ σ′ ∷ Γ → ⊢ Δ →
    Δ ⊢ t [ σ ] ≡ u [ σ′ ] ∷ A [ σ ]
  substitutionEqTerm t≡u σ≡σ′ ⊢Δ =
    escape-⊩≡∷ $
    ⊩ᵛ≡∷⇔′ .proj₁ (fundamental-⊩ᵛ≡∷ t≡u) .proj₂ .proj₂ $
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

-- Well-formed singleton substitution of terms with lifting.
singleSubst↑ : ∀ {A t} → Γ ∙ A ⊢ t ∷ wk1 A → Γ ∙ A ⊢ˢ consSubst (wk1Subst idSubst) t ∷ Γ ∙ A
singleSubst↑ {A = A} t with wfTerm t
... | ⊢Γ ∙ ⊢A = wk1Subst′ ⊢Γ ⊢A (idSubst′ ⊢Γ)
              , PE.subst (λ x → _ ∙ A ⊢ _ ∷ x) (wk1-tailId A) t

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

substTypeΠ : ∀ {t F G} → Γ ⊢ Π p , q ▷ F ▹ G → Γ ⊢ t ∷ F → Γ ⊢ G [ t ]₀
substTypeΠ ΠFG t with syntacticΠ ΠFG
substTypeΠ ΠFG t | F , G = substType G t

subst↑Type : ∀ {t F G}
           → Γ ∙ F ⊢ G
           → Γ ∙ F ⊢ t ∷ wk1 F
           → Γ ∙ F ⊢ G [ t ]↑
subst↑Type ⊢G ⊢t = substitution ⊢G (singleSubst↑ ⊢t) (wfTerm ⊢t)

subst↑TypeEq : ∀ {t u F G E}
             → Γ ∙ F ⊢ G ≡ E
             → Γ ∙ F ⊢ t ≡ u ∷ wk1 F
             → Γ ∙ F ⊢ G [ t ]↑ ≡ E [ u ]↑
subst↑TypeEq ⊢G ⊢t = substitutionEq ⊢G (singleSubst↑Eq ⊢t) (wfEqTerm ⊢t)

subst↑²Type : ∀ {t F G A B}
            → Γ ⊢ F
            → Γ ∙ F ⊢ G
            → Γ ∙ A ⊢ B
            → Γ ∙ F ∙ G ⊢ t ∷ wk1 (wk1 A)
            → Γ ∙ F ∙ G ⊢ B [ t ]↑²
subst↑²Type ⊢F ⊢G ⊢B ⊢t =
  let ⊢Γ = wf ⊢F
      ⊢t′ = PE.subst (_⊢_∷_ _ _)
              (PE.trans (wk-comp (step id) (step id) _) (wk≡subst _ _))
              ⊢t
      ⊢σ = wk1Subst′ ⊢Γ ⊢G (wk1Subst′ ⊢Γ ⊢F (idSubst′ ⊢Γ)) , ⊢t′
  in  substitution ⊢B ⊢σ (⊢Γ ∙ ⊢F ∙ ⊢G)

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

subst↑²TypeEq : ∀ {t u F G A B C}
              → Γ ⊢ F
              → Γ ∙ F ⊢ G
              → Γ ∙ A ⊢ B ≡ C
              → Γ ∙ F ∙ G ⊢ t ≡ u ∷ wk1 (wk1 A)
              → Γ ∙ F ∙ G ⊢ B [ t ]↑² ≡ C [ u ]↑²
subst↑²TypeEq ⊢F ⊢G B≡C t≡u =
  let ⊢Γ = wf ⊢F
      t≡u′ = PE.subst (_⊢_≡_∷_ _ _ _)
               (PE.trans (wk-comp (step id) (step id) _) (wk≡subst _ _))
               t≡u
      σ≡σ′ = substRefl (wk1Subst′ ⊢Γ ⊢G (wk1Subst′ ⊢Γ ⊢F (idSubst′ ⊢Γ)))
           , t≡u′
  in  substitutionEq B≡C σ≡σ′ (⊢Γ ∙ ⊢F ∙ ⊢G)


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
