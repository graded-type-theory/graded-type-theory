------------------------------------------------------------------------
-- The typing and reduction relations are closed under substitutions.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions

module Definition.Typed.Consequences.Substitution
  {a} {M : Set a}
  (R : Type-restrictions M)
  where

open Type-restrictions R

open import Definition.Untyped M hiding (_∷_; wk)
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.Weakening R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Irrelevance R
open import Definition.LogicalRelation.Fundamental R

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    ℓ m n : Nat
    Γ : Con Term n
    σ σ′ : Subst m n
    ρ : Wk ℓ m
    p q : M

-- Well-formed substitution of types.
substitution : ∀ {A Γ Δ} → Γ ⊢ A → Δ ⊢ˢ σ ∷ Γ → ⊢ Δ → Δ ⊢ A [ σ ]
substitution A σ ⊢Δ with fundamental A | fundamentalSubst (wf A) ⊢Δ σ
substitution A σ ⊢Δ | [Γ] , [A] | [Γ]′ , [σ] =
  escape (proj₁ (unwrap [A] ⊢Δ (irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ])))

-- Well-formed substitution of type equality.
substitutionEq : ∀ {A B Γ Δ}
               → Γ ⊢ A ≡ B → Δ ⊢ˢ σ ≡ σ′ ∷ Γ → ⊢ Δ → Δ ⊢ A [ σ ] ≡ B [ σ′ ]
substitutionEq A≡B σ ⊢Δ with fundamentalEq A≡B | fundamentalSubstEq (wfEq A≡B) ⊢Δ σ
substitutionEq A≡B σ ⊢Δ | [Γ] , [A] , [B] , [A≡B] | [Γ]′ , [σ] , [σ′] , [σ≡σ′]  =
  let [σ]′ = irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ]
      [σ′]′ = irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ′]
      [σ≡σ′]′ = irrelevanceSubstEq [Γ]′ [Γ] ⊢Δ ⊢Δ [σ] [σ]′ [σ≡σ′]
  in  escapeEq (proj₁ (unwrap [A] ⊢Δ [σ]′))
                   (transEq (proj₁ (unwrap [A] ⊢Δ [σ]′)) (proj₁ (unwrap [B] ⊢Δ [σ]′))
                            (proj₁ (unwrap [B] ⊢Δ [σ′]′)) ([A≡B] ⊢Δ [σ]′)
                            (proj₂ (unwrap [B] ⊢Δ [σ]′) [σ′]′ [σ≡σ′]′))

-- Well-formed substitution of terms.
substitutionTerm : ∀ {t A Γ Δ}
               → Γ ⊢ t ∷ A → Δ ⊢ˢ σ ∷ Γ → ⊢ Δ → Δ ⊢ t [ σ ] ∷ A [ σ ]
substitutionTerm t σ ⊢Δ with fundamentalTerm t | fundamentalSubst (wfTerm t) ⊢Δ σ
substitutionTerm t σ ⊢Δ | [Γ] , [A] , [t] | [Γ]′ , [σ] =
  let [σ]′ = irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ]
  in  escapeTerm (proj₁ (unwrap [A] ⊢Δ [σ]′)) (proj₁ ([t] ⊢Δ [σ]′))

-- Well-formed substitution of term equality.
substitutionEqTerm : ∀ {t u A Γ Δ}
                   → Γ ⊢ t ≡ u ∷ A → Δ ⊢ˢ σ ≡ σ′ ∷ Γ → ⊢ Δ
                   → Δ ⊢ t [ σ ] ≡ u [ σ′ ] ∷ A [ σ ]
substitutionEqTerm t≡u σ≡σ′ ⊢Δ with fundamentalTermEq t≡u
                                  | fundamentalSubstEq (wfEqTerm t≡u) ⊢Δ σ≡σ′
... | [Γ] , modelsTermEq [A] [t] [u] [t≡u] | [Γ]′ , [σ] , [σ′] , [σ≡σ′] =
  let [σ]′ = irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ]
      [σ′]′ = irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ′]
      [σ≡σ′]′ = irrelevanceSubstEq [Γ]′ [Γ] ⊢Δ ⊢Δ [σ] [σ]′ [σ≡σ′]
  in  escapeTermEq (proj₁ (unwrap [A] ⊢Δ [σ]′))
                       (transEqTerm (proj₁ (unwrap [A] ⊢Δ [σ]′)) ([t≡u] ⊢Δ [σ]′)
                                    (proj₂ ([u] ⊢Δ [σ]′) [σ′]′ [σ≡σ′]′))

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
wk1Subst′ : ∀ {F Γ Δ} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ)
            (⊢F : Δ ⊢ F)
            ([σ] : Δ ⊢ˢ σ ∷ Γ)
          → (Δ ∙ F) ⊢ˢ wk1Subst σ ∷ Γ
wk1Subst′ {σ = σ} {F} {Γ} {Δ} ⊢Γ ⊢Δ ⊢F [σ] =
  wkSubst′ ⊢Γ ⊢Δ (⊢Δ ∙ ⊢F) (step id) [σ]

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
  wk1Subst′ ⊢Γ ⊢Γ ⊢A (idSubst′ ⊢Γ)
  , PE.subst (λ x → Γ ∙ A ⊢ _ ∷ x) (wk1-tailId A) (var (⊢Γ ∙ ⊢A) here)

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
... | ⊢Γ ∙ ⊢A = wk1Subst′ ⊢Γ ⊢Γ ⊢A (idSubst′ ⊢Γ)
              , PE.subst (λ x → _ ∙ A ⊢ _ ∷ x) (wk1-tailId A) t

-- Well-formed singleton substitution of term equality with lifting.
singleSubst↑Eq : ∀ {A t u} → Γ ∙ A ⊢ t ≡ u ∷ wk1 A
              → Γ ∙ A ⊢ˢ consSubst (wk1Subst idSubst) t ≡ consSubst (wk1Subst idSubst) u ∷ Γ ∙ A
singleSubst↑Eq {A = A} t with wfEqTerm t
... | ⊢Γ ∙ ⊢A = substRefl (wk1Subst′ ⊢Γ ⊢Γ ⊢A (idSubst′ ⊢Γ))
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
subst↑²Type {n} {Γ} {t} {F} {G} {A} {B} ⊢F ⊢G ⊢B ⊢t =
  let ⊢Γ = wf ⊢F
      ⊢t′ = PE.subst (λ x → Γ ∙ F ∙ G ⊢ t ∷ x)
                     (PE.trans (wk-comp (step id) (step id) A) (wk≡subst _ A))
                     ⊢t
      ⊢σ = wk1Subst′ ⊢Γ (⊢Γ ∙ ⊢F) ⊢G (wk1Subst′ ⊢Γ ⊢Γ ⊢F (idSubst′ ⊢Γ)) , ⊢t′
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
                      (var ⊢ΓFG (there here))
      var0 = PE.subst (λ x → Γ ∙ F ∙ G ⊢ var x0 ∷ x)
                      (PE.trans (wk≡subst (step id) G)
                                (PE.trans (substVar-to-subst (λ{x0 → PE.refl
                                                             ; (x +1) → PE.refl}) G)
                                          (PE.sym (substCompEq G))))
                      (var ⊢ΓFG here)
  in  substitution ⊢A
                   (wk1Subst′ ⊢Γ (⊢Γ ∙ ⊢F) ⊢G (wk1Subst′ ⊢Γ ⊢Γ ⊢F (idSubst′ ⊢Γ))
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
subst↑²TypeEq {n} {Γ} {t} {u} {F} {G} {A} {B} {C} ⊢F ⊢G B≡C t≡u =
  let ⊢Γ = wf ⊢F
      t≡u′ = PE.subst (λ x → Γ ∙ F ∙ G ⊢ t ≡ u ∷ x)
                      (PE.trans (wk-comp (step id) (step id) A) (wk≡subst _ A)) t≡u
      σ≡σ′ = substRefl (wk1Subst′ ⊢Γ (⊢Γ ∙ ⊢F) ⊢G (wk1Subst′ ⊢Γ ⊢Γ ⊢F (idSubst′ ⊢Γ))) , t≡u′
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
                      (var ⊢ΓFG (there here))
      var0 = PE.subst (λ x → Γ ∙ F ∙ G ⊢ var x0 ∷ x)
                      (PE.trans (wk≡subst (step id) G)
                                (PE.trans (substVar-to-subst (λ{x0 → PE.refl
                                                             ; (x +1) → PE.refl}) G)
                                          (PE.sym (substCompEq G))))
                      (var ⊢ΓFG here)
  in  substitutionEq A≡B
                     (substRefl (wk1Subst′ ⊢Γ (⊢Γ ∙ ⊢F) ⊢G
                                           (wk1Subst′ ⊢Γ ⊢Γ ⊢F
                                                      (idSubst′ ⊢Γ))
                                , prodⱼ ⊢ρF′ ⊢ρG′ var1 var0 ok))
                     ⊢ΓFG
  where
  splitCon : ∀ {Γ : Con Term n} {F} → ⊢ (Γ ∙ F) → ⊢ Γ × Γ ⊢ F
  splitCon (x ∙ x₁) = x , x₁
