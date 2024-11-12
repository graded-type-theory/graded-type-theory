------------------------------------------------------------------------
-- The typing and reduction relations are closed under substitutions.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Substitution
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M hiding (wk)
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.Inversion.Primitive R
open import Definition.Typed.Properties.Admissible R
open import Definition.Typed.Properties.Well-formed R
import Definition.Typed.Substitution.Primitive R as P
open import Definition.Typed.Weakening R
open import Definition.Typed.Well-formed R

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

open P public using () renaming (refl-⊢ˢ≡∷ to substRefl)

private
  variable
    k ℓ m n : Nat
    Γ Δ Η : Con Term n
    A A₁ A₂ B B₁ B₂ C C₁ C₂ D E t t₁ t₂ u u₁ u₂ v : Term _
    σ σ₁ σ₂ σ′ : Subst m n
    ρ : Wk ℓ m
    p q : M

opaque

  -- A substitution lemma for _⊢_.

  substitution : Γ ⊢ A → Δ ⊢ˢ σ ∷ Γ → ⊢ Δ → Δ ⊢ A [ σ ]
  substitution ⊢A ⊢σ ⊢Δ =
    P.subst-⊢ ⊢A (P.⊢ˢʷ∷⇔ .proj₂ (⊢Δ , ⊢σ))

opaque

  -- A substitution lemma for _⊢_≡_.

  substitutionEq :
    Γ ⊢ A₁ ≡ A₂ → Δ ⊢ˢ σ₁ ≡ σ₂ ∷ Γ → ⊢ Δ → Δ ⊢ A₁ [ σ₁ ] ≡ A₂ [ σ₂ ]
  substitutionEq A₁≡A₂ σ₁≡σ₂ ⊢Δ =
    P.subst-⊢≡ A₁≡A₂ (⊢ˢʷ≡∷⇔′ (wfEq A₁≡A₂) .proj₂ (⊢Δ , σ₁≡σ₂))

opaque

  -- A substitution lemma for _⊢_∷_.

  substitutionTerm :
    Γ ⊢ t ∷ A → Δ ⊢ˢ σ ∷ Γ → ⊢ Δ → Δ ⊢ t [ σ ] ∷ A [ σ ]
  substitutionTerm ⊢t ⊢σ ⊢Δ =
    P.subst-⊢∷ ⊢t (P.⊢ˢʷ∷⇔ .proj₂ (⊢Δ , ⊢σ))

opaque

  -- A substitution lemma for _⊢_≡_∷_.

  substitutionEqTerm :
    Γ ⊢ t₁ ≡ t₂ ∷ A → Δ ⊢ˢ σ₁ ≡ σ₂ ∷ Γ → ⊢ Δ →
    Δ ⊢ t₁ [ σ₁ ] ≡ t₂ [ σ₂ ] ∷ A [ σ₁ ]
  substitutionEqTerm t₁≡t₂ σ₁≡σ₂ ⊢Δ =
    P.subst-⊢≡∷ t₁≡t₂ (⊢ˢʷ≡∷⇔′ (wfEqTerm t₁≡t₂) .proj₂ (⊢Δ , σ₁≡σ₂))

opaque

  -- A well-formedness lemma for _•ₛ_.

  wkSubst′ : ρ ∷ʷ Η ⊇ Δ → Δ ⊢ˢ σ ∷ Γ → Η ⊢ˢ ρ •ₛ σ ∷ Γ
  wkSubst′ _  id                    = id
  wkSubst′ ρ⊇ (_,_ {A} ⊢tail ⊢head) =
    wkSubst′ ρ⊇ ⊢tail ,
    PE.subst (_⊢_∷_ _ _) (wk-subst A) (wkTerm ρ⊇ ⊢head)

opaque

  -- A well-formedness lemma for wk1Subst.

  wk1Subst′ : Δ ⊢ A → Δ ⊢ˢ σ ∷ Γ → Δ ∙ A ⊢ˢ wk1Subst σ ∷ Γ
  wk1Subst′ ⊢A = wkSubst′ (stepʷ id ⊢A)

opaque

  -- A well-formedness lemma for wkSubst.

  ⊢ˢ-wkSubst :
    ⊢ Δ →
    drop k Δ ⊢ˢ σ ∷ Γ →
    Δ ⊢ˢ wkSubst k σ ∷ Γ
  ⊢ˢ-wkSubst {k = 0}    _      ⊢σ = ⊢σ
  ⊢ˢ-wkSubst {k = 1+ _} (∙ ⊢A) ⊢σ =
    wk1Subst′ ⊢A (⊢ˢ-wkSubst (wf ⊢A) ⊢σ)

opaque

  -- A well-formedness lemma for liftSubst.

  liftSubst′ :
    ⊢ Δ → Γ ⊢ A → Δ ⊢ˢ σ ∷ Γ →
    Δ ∙ A [ σ ] ⊢ˢ liftSubst σ ∷ Γ ∙ A
  liftSubst′ {A} ⊢Δ ⊢A ⊢σ =
    let ⊢A = substitution ⊢A ⊢σ ⊢Δ in
    wkSubst′ (stepʷ id ⊢A) ⊢σ ,
    PE.subst (_⊢_∷_ _ _) (wk-subst A) (var₀ ⊢A)

opaque

  -- A well-formedness lemma for idSubst.

  idSubst′ : (⊢Γ : ⊢ Γ) → Γ ⊢ˢ idSubst ∷ Γ
  idSubst′ = proj₂ ∘→ P.⊢ˢʷ∷⇔ .proj₁ ∘→ P.⊢ˢʷ∷-idSubst

opaque

  -- A well-formedness lemma for _ₛ•ₛ_.

  substComp′ :
    ⊢ Η →
    Η ⊢ˢ σ ∷ Δ →
    Δ ⊢ˢ σ′ ∷ Γ →
    Η ⊢ˢ σ ₛ•ₛ σ′ ∷ Γ
  substComp′ _  _  id                    = id
  substComp′ ⊢Η ⊢σ (_,_ {A} ⊢tail ⊢head) =
    substComp′ ⊢Η ⊢σ ⊢tail ,
    PE.subst (_⊢_∷_ _ _) (substCompEq A) (substitutionTerm ⊢head ⊢σ ⊢Η)

opaque

  -- A well-formedness lemma for sgSubst.

  singleSubst : Γ ⊢ t ∷ A → Γ ⊢ˢ sgSubst t ∷ Γ ∙ A
  singleSubst = proj₂ ∘→ P.⊢ˢʷ∷⇔ .proj₁ ∘→ P.⊢ˢʷ∷-sgSubst

opaque

  -- A well-formedness lemma for sgSubst.

  singleSubstEq : Γ ⊢ t ≡ u ∷ A → Γ ⊢ˢ sgSubst t ≡ sgSubst u ∷ Γ ∙ A
  singleSubstEq =
    proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ P.⊢ˢʷ≡∷⇔ .proj₁ ∘→ ⊢ˢʷ≡∷-sgSubst′

opaque

  -- A substitution lemma related to _[_]↑.

  singleSubst↑ :
    Γ ∙ A ⊢ t ∷ wk1 B →
    Γ ∙ A ⊢ˢ consSubst (wk1Subst idSubst) t ∷ Γ ∙ B
  singleSubst↑ {A} t =
    let ⊢A = ⊢∙→⊢ (wfTerm t) in
      wk1Subst′ ⊢A (idSubst′ (wf ⊢A))
    , PE.subst (_⊢_∷_ _ _) (wk1-tailId _) t

opaque

  -- Well-formed singleton substitution of term equality with lifting.
  singleSubst↑Eq :
    Γ ∙ A ⊢ t ≡ u ∷ wk1 A →
    Γ ∙ A ⊢ˢ
      consSubst (wk1Subst idSubst) t ≡
      consSubst (wk1Subst idSubst) u ∷
      Γ ∙ A
  singleSubst↑Eq t =
    let ⊢A = ⊢∙→⊢ (wfEqTerm t) in
      substRefl (wk1Subst′ ⊢A (idSubst′ (wf ⊢A)))
    , PE.subst (_⊢_≡_∷_ _ _ _) (wk1-tailId _) t

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

opaque

  substTypeΠ : Γ ⊢ Π p , q ▷ A ▹ B → Γ ⊢ t ∷ A → Γ ⊢ B [ t ]₀
  substTypeΠ ⊢ΠAB ⊢t =
    let _ , ⊢B , _ = inversion-ΠΣ ⊢ΠAB in
    substType ⊢B ⊢t

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
    let ⊢ΓCD = wfTerm ⊢t
        ⊢D   = ⊢∙→⊢ ⊢ΓCD
        ⊢C   = ⊢∙→⊢ (wf ⊢D)
        ⊢Γ   = wf ⊢C
    in
    substitution ⊢B
      ( wk1Subst′ ⊢D (wk1Subst′ ⊢C (idSubst′ ⊢Γ))
      , PE.subst (_⊢_∷_ _ _) (wk[]≡[] 2) ⊢t
      )
      ⊢ΓCD

subst↑²Type-prod : ∀ {m F G A}
                 → Γ ∙ (Σ⟨ m ⟩ p , q ▷ F ▹ G) ⊢ A
                 → Σ-allowed m p q
                 → Γ ∙ F ∙ G ⊢ A [ prod m p (var x1) (var x0) ]↑²
subst↑²Type-prod {Γ = Γ} {F = F} {G} {A} ⊢A ok =
  let ⊢ΓΣ = wf ⊢A
      ⊢Γ , ⊢Σ = splitCon ⊢ΓΣ
      ⊢F , ⊢G , _ = inversion-ΠΣ ⊢Σ
      ⊢ρF = wk (stepʷ (step id) ⊢G) ⊢F
      ⊢ρG = wk (liftʷ (step (step id)) ⊢ρF) ⊢G
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
                   (wk1Subst′ ⊢G (wk1Subst′ ⊢F (idSubst′ ⊢Γ))
                   , prodⱼ ⊢ρG′ var1 var0 ok)
                   (∙ ⊢G)
  where
  splitCon : ∀ {Γ : Con Term n} {F} → ⊢ (Γ ∙ F) → ⊢ Γ × Γ ⊢ F
  splitCon (∙ x₁) = wf x₁ , x₁

opaque

  -- A substitution lemma related to _[_]↑².

  subst↑²TypeEq :
    Γ ∙ A ⊢ B ≡ C →
    Γ ∙ D ∙ E ⊢ t ≡ u ∷ wk2 A →
    Γ ∙ D ∙ E ⊢ B [ t ]↑² ≡ C [ u ]↑²
  subst↑²TypeEq {A} B≡C t≡u =
    let ⊢ΓDE = wfEqTerm t≡u
        ⊢E   = ⊢∙→⊢ ⊢ΓDE
        ⊢D   = ⊢∙→⊢ (wf ⊢E)
        ⊢Γ   = wf ⊢D
    in
    substitutionEq B≡C
      ( substRefl (wk1Subst′ ⊢E (wk1Subst′ ⊢D (idSubst′ ⊢Γ)))
      , PE.subst (_⊢_≡_∷_ _ _ _) (wk[]≡[] 2) t≡u
      )
      ⊢ΓDE

subst↑²TypeEq-prod : ∀ {m F G A B}
              → Γ ∙ (Σ⟨ m ⟩ p , q ▷ F ▹ G) ⊢ A ≡ B
              → Σ-allowed m p q
              → Γ ∙ F ∙ G ⊢ A [ prod m p (var x1) (var x0) ]↑²
                          ≡ B [ prod m p (var x1) (var x0) ]↑²
subst↑²TypeEq-prod {Γ = Γ} {F = F} {G} {A} {B} A≡B ok =
  let ⊢A , ⊢B = wf-⊢≡ A≡B
      ⊢ΓΣ = wf ⊢A
      ⊢Γ , ⊢Σ = splitCon ⊢ΓΣ
      ⊢F , ⊢G , _ = inversion-ΠΣ ⊢Σ
      ⊢ρF = wk (stepʷ (step id) ⊢G) ⊢F
      ⊢ρG = wk (liftʷ (step (step id)) ⊢ρF) ⊢G
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
        (substRefl (wk1Subst′ ⊢G (wk1Subst′ ⊢F (idSubst′ ⊢Γ)) ,
         prodⱼ ⊢ρG′ var1 var0 ok))
        (∙ ⊢G)
  where
  splitCon : ∀ {Γ : Con Term n} {F} → ⊢ (Γ ∙ F) → ⊢ Γ × Γ ⊢ F
  splitCon (∙ x₁) = wf x₁ , x₁

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

  -- A variant of substTypeEq for _[_][_]↑.

  [][]↑-cong :
    drop k Γ ∙ A ⊢ B₁ ≡ B₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ A [ wkSubst k idSubst ] →
    Γ ⊢ B₁ [ k ][ t₁ ]↑ ≡ B₂ [ k ][ t₂ ]↑
  [][]↑-cong {k} {Γ} B₁≡B₂ t₁≡t₂ =
    substitutionEq B₁≡B₂
      (substRefl (⊢ˢ-wkSubst ⊢Γ (idSubst′ ⊢Γ⁻)) , t₁≡t₂)
      ⊢Γ
    where
    ⊢Γ : ⊢ Γ
    ⊢Γ = wfEqTerm t₁≡t₂

    ⊢Γ⁻ : ⊢ drop k Γ
    ⊢Γ⁻ = wf (⊢∙→⊢ (wfEq B₁≡B₂))

opaque

  -- A variant of substType for _[_][_]↑.

  ⊢[][]↑ :
    drop k Γ ∙ A ⊢ B →
    Γ ⊢ t ∷ A [ wkSubst k idSubst ] →
    Γ ⊢ B [ k ][ t ]↑
  ⊢[][]↑ ⊢B ⊢t =
    wf-⊢≡ ([][]↑-cong (refl ⊢B) (refl ⊢t)) .proj₁

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
  substitutionRedTerm {σ} (β-red {G} {t} {a} x₁ x₂ x₃ x₄ x₅) ⊢σ ⊢Δ =
    let x = ⊢∙→⊢ (wf x₁) in
    case substitution x ⊢σ ⊢Δ of λ
      ⊢σF →
    case liftSubst′ ⊢Δ x ⊢σ of λ
      ⊢⇑σ →
    PE.subst₂ (_ ⊢ (lam _ t ∘ a) [ σ ] ⇒_∷_)
      (PE.sym (singleSubstLift t a))
      (PE.sym (singleSubstLift G a))
      (β-red (substitution x₁ ⊢⇑σ (∙ ⊢σF))
        (substitutionTerm x₂ ⊢⇑σ (∙ ⊢σF))
        (substitutionTerm x₃ ⊢σ ⊢Δ) x₄ x₅)
  substitutionRedTerm (fst-subst x₁ d) ⊢σ ⊢Δ =
    let x = ⊢∙→⊢ (wf x₁) in
    case substitution x ⊢σ ⊢Δ of λ
      ⊢σA →
    fst-subst (substitution x₁ (liftSubst′ ⊢Δ x ⊢σ) (∙ ⊢σA))
      (substitutionRedTerm d ⊢σ ⊢Δ)
  substitutionRedTerm (snd-subst {G} {t} x₁ d) ⊢σ ⊢Δ =
    let x = ⊢∙→⊢ (wf x₁) in
    case substitution x ⊢σ ⊢Δ of λ
      ⊢σA →
    PE.subst (_ ⊢ _ ⇒ _ ∷_)
      (PE.sym (singleSubstLift G (fst _ t)))
      (snd-subst (substitution x₁ (liftSubst′ ⊢Δ x ⊢σ) (∙ ⊢σA))
        (substitutionRedTerm d ⊢σ ⊢Δ))
  substitutionRedTerm (Σ-β₁ {G} {t} x₁ x₂ x₃ x₄ x₅) ⊢σ ⊢Δ =
    let x = ⊢∙→⊢ (wf x₁) in
    case substitution x ⊢σ ⊢Δ of λ
      ⊢σA →
    Σ-β₁ (substitution x₁ (liftSubst′ ⊢Δ x ⊢σ) (∙ ⊢σA))
      (substitutionTerm x₂ ⊢σ ⊢Δ)
      (PE.subst (_ ⊢ _ ∷_) (singleSubstLift G t) (substitutionTerm x₃ ⊢σ ⊢Δ))
      x₄ x₅
  substitutionRedTerm (Σ-β₂ {G} x₁ x₂ x₃ x₄ x₅) ⊢σ ⊢Δ =
    let x = ⊢∙→⊢ (wf x₁) in
    case substitution x ⊢σ ⊢Δ of λ
      ⊢σA →
    PE.subst (_ ⊢ _ ⇒ _ ∷_)
      (PE.sym (singleSubstLift G _))
      (Σ-β₂ (substitution x₁ (liftSubst′ ⊢Δ x ⊢σ) (∙ ⊢σA))
        (substitutionTerm x₂ ⊢σ ⊢Δ)
        (PE.subst (_ ⊢ _ ∷_) (singleSubstLift G _) (substitutionTerm x₃ ⊢σ ⊢Δ))
        x₄ x₅)
  substitutionRedTerm
    {σ} (prodrec-subst {A} {u} {t} x₂ x₃ d x₄) ⊢σ ⊢Δ =
    let x₁ = ⊢∙→⊢ (wfTerm x₃)
        x  = ⊢∙→⊢ (wf x₁)
    in
    case substitution x ⊢σ ⊢Δ of λ
      ⊢σA →
    case liftSubst′ ⊢Δ x ⊢σ of λ
      ⊢⇑σ →
    case substitution x₁ ⊢⇑σ (∙ ⊢σA) of λ
      ⊢σB →
    PE.subst (_ ⊢ prodrec _ _ _ A t u [ σ ] ⇒ _ ∷_)
      (PE.sym (singleSubstLift A t))
      (prodrec-subst
        (substitution x₂ (liftSubst′ ⊢Δ (ΠΣⱼ x₁ x₄) ⊢σ) (∙ ΠΣⱼ ⊢σB x₄))
        (PE.subst (_ ⊢ _ ∷_) (subst-β-prodrec A σ)
          (substitutionTerm x₃ (liftSubst′ (∙ ⊢σA) x₁ ⊢⇑σ) (∙ ⊢σB)))
        (substitutionRedTerm d ⊢σ ⊢Δ) x₄)
  substitutionRedTerm
    {σ} (prodrec-β {G} {A} {t} {t′} {u} x₂ x₃ x₄ x₅ x₆ x₇) ⊢σ ⊢Δ =
    let x₁ = ⊢∙→⊢ (wfTerm x₅)
        x  = ⊢∙→⊢ (wf x₁)
    in
    case substitution x ⊢σ ⊢Δ of λ
      ⊢σA →
    case liftSubst′ ⊢Δ x ⊢σ of λ
      ⊢⇑σ →
    case substitution x₁ ⊢⇑σ (∙ ⊢σA) of λ
      ⊢σB →
    PE.subst₂ (_ ⊢ prodrec _ _ _ A (prod! t t′) u [ σ ] ⇒_∷_)
      (PE.sym ([,]-[]-commute u))
      (PE.sym (singleSubstLift A _))
      (prodrec-β
        (substitution x₂ (liftSubst′ ⊢Δ (ΠΣⱼ x₁ x₇) ⊢σ) (∙ ΠΣⱼ ⊢σB x₇))
        (substitutionTerm x₃ ⊢σ ⊢Δ)
        (PE.subst (_ ⊢ _ ∷_) (singleSubstLift G _)
          (substitutionTerm x₄ ⊢σ ⊢Δ))
        (PE.subst (_ ⊢ _ ∷_) (subst-β-prodrec A σ)
          (substitutionTerm x₅ (liftSubst′ (∙ ⊢σA) x₁ ⊢⇑σ) (∙ ⊢σB)))
        x₆ x₇)
  substitutionRedTerm {σ} (natrec-subst {z} {A} {s} {n} x₁ x₂ d) ⊢σ ⊢Δ =
    let x = ⊢∙→⊢ (wfTerm x₂) in
    case wfTerm x₁ of λ
      ⊢Γ →
    case liftSubst′ ⊢Δ (ℕⱼ ⊢Γ) ⊢σ of λ
      ⊢⇑σ →
    case substitution x ⊢⇑σ (∙ ℕⱼ ⊢Δ) of λ
      ⊢σA →
    PE.subst (_ ⊢ natrec _ _ _ A z s n [ σ ] ⇒ _ ∷_)
      (PE.sym (singleSubstLift A n))
      (natrec-subst
        (PE.subst (_ ⊢ _ ∷_) (singleSubstLift A zero) (substitutionTerm x₁ ⊢σ ⊢Δ))
        (PE.subst (_ ∙ ℕ ∙ A [ liftSubst σ ] ⊢ _ ∷_) (natrecSucCase σ A)
          (substitutionTerm x₂ (liftSubst′ (∙ ℕⱼ ⊢Δ) x ⊢⇑σ) (∙ ⊢σA)))
        (substitutionRedTerm d ⊢σ ⊢Δ))
  substitutionRedTerm {σ} (natrec-zero {z} {A} {s} x₁ x₂) ⊢σ ⊢Δ =
    let x = ⊢∙→⊢ (wfTerm x₂) in
    case wfTerm x₁ of λ
      ⊢Γ →
    case liftSubst′ ⊢Δ (ℕⱼ ⊢Γ) ⊢σ of λ
      ⊢⇑σ →
    case substitution x ⊢⇑σ (∙ ℕⱼ ⊢Δ) of λ
      ⊢σA →
    PE.subst (_ ⊢ natrec _ _ _ A z s zero [ σ ] ⇒ _ ∷_)
      (PE.sym (singleSubstLift A zero))
      (natrec-zero
        (PE.subst (_ ⊢ _ ∷_) (singleSubstLift A zero) (substitutionTerm x₁ ⊢σ ⊢Δ))
        (PE.subst ((_ ∙ ℕ ∙ A [ liftSubst σ ]) ⊢ _ ∷_) (natrecSucCase σ A)
        (substitutionTerm x₂ (liftSubst′ (∙ ℕⱼ ⊢Δ) x ⊢⇑σ) (∙ ⊢σA))))
  substitutionRedTerm {σ} (natrec-suc {z} {A} {s} {n} x₁ x₂ x₃) ⊢σ ⊢Δ =
    let x = ⊢∙→⊢ (wfTerm x₂) in
    case wfTerm x₁ of λ
      ⊢Γ →
    case liftSubst′ ⊢Δ (ℕⱼ ⊢Γ) ⊢σ of λ
      ⊢⇑σ →
    case substitution x ⊢⇑σ (∙ ℕⱼ ⊢Δ) of λ
      ⊢σA →
    PE.subst₂ (_ ⊢ natrec _ _ _ A z s (suc n) [ σ ] ⇒_∷_)
      (PE.sym ([,]-[]-commute s))
      (PE.sym (singleSubstLift A (suc n)))
      (natrec-suc
        (PE.subst (_ ⊢ _ ∷_) (singleSubstLift A zero) (substitutionTerm x₁ ⊢σ ⊢Δ))
        (PE.subst ((_ ∙ ℕ ∙ A [ liftSubst σ ]) ⊢ _ ∷_) (natrecSucCase σ A)
          (substitutionTerm x₂ (liftSubst′ (∙ ℕⱼ ⊢Δ) x ⊢⇑σ) (∙ ⊢σA)))
        (substitutionTerm x₃ ⊢σ ⊢Δ))
  substitutionRedTerm (emptyrec-subst x d) ⊢σ ⊢Δ =
    emptyrec-subst (substitution x ⊢σ ⊢Δ) (substitutionRedTerm d ⊢σ ⊢Δ)
  substitutionRedTerm {σ} (unitrec-subst {A = A} {u} {t} x x₁ d x₂ x₃) ⊢σ ⊢Δ =
    PE.subst (_⊢_⇒_∷_ _ _ _)
      (PE.sym (singleSubstLift A t))
      (unitrec-subst
        (substitution x (liftSubst′ ⊢Δ (Unitⱼ (wfTerm x₁) x₂) ⊢σ)
           (∙ Unitⱼ ⊢Δ x₂))
        (PE.subst (_ ⊢ _ ∷_) (singleSubstLift A _) $
         substitutionTerm x₁ ⊢σ ⊢Δ)
        (substitutionRedTerm d ⊢σ ⊢Δ) x₂ x₃)
  substitutionRedTerm {σ} (unitrec-β {A = A} {u} x x₁ x₂ x₃) ⊢σ ⊢Δ =
    PE.subst (_⊢_⇒_∷_ _ _ _)
      (PE.sym (singleSubstLift A _))
      (unitrec-β
        (substitution x (liftSubst′ ⊢Δ (Unitⱼ (wfTerm x₁) x₂) ⊢σ)
           (∙ Unitⱼ ⊢Δ x₂))
        (PE.subst (_ ⊢ _ ∷_) (singleSubstLift A _) $
         substitutionTerm x₁ ⊢σ ⊢Δ)
        x₂ x₃)
  substitutionRedTerm {σ} (unitrec-β-η {A} {t} {u} x x₁ x₂ x₃ x₄) ⊢σ ⊢Δ =
    PE.subst (_⊢_⇒_∷_ _ _ _)
      (PE.sym (singleSubstLift A t))
      (unitrec-β-η
        (substitution x (liftSubst′ ⊢Δ (Unitⱼ (wfTerm x₁) x₃) ⊢σ)
           (∙ Unitⱼ ⊢Δ x₃))
        (substitutionTerm x₁ ⊢σ ⊢Δ)
        (PE.subst (_ ⊢ _ ∷_) (singleSubstLift A _) $
         substitutionTerm x₂ ⊢σ ⊢Δ)
        x₃ x₄)
  substitutionRedTerm
    {σ} (J-subst {t} {A} {B} {u} {v} {w₁} x₁ x₂ x₃ x₄ d) ⊢σ ⊢Δ =
    let x = ⊢∙→⊢ (wf (⊢∙→⊢ (wf x₂))) in
    case substitution x ⊢σ ⊢Δ of λ
      ⊢σA →
    case wf x₂ of λ {
      (∙ ⊢Id) →
    case liftSubst′ ⊢Δ x ⊢σ of
      λ ⊢⇑σ →
    case substitution ⊢Id ⊢⇑σ (∙ ⊢σA) of λ
      ⊢σId →
    case substitution x₂ (liftSubst′ (∙ ⊢σA) ⊢Id ⊢⇑σ) (∙ ⊢σId) of λ
      ⊢σB →
    PE.subst (_ ⊢ J _ _ A t B u v w₁ [ σ ] ⇒ _ ∷_)
      (PE.sym ([,]-[]-commute B))
      (J-subst (substitutionTerm x₁ ⊢σ ⊢Δ)
        (PE.subst₂ (λ x y → _ ∙ A [ σ ] ∙ Id x y (var x0) ⊢ _)
          (wk1-liftSubst A) (wk1-liftSubst t) ⊢σB)
        (PE.subst (_ ⊢ _ ∷_) ([,]-[]-commute B) (substitutionTerm x₃ ⊢σ ⊢Δ))
        (substitutionTerm x₄ ⊢σ ⊢Δ)
        (substitutionRedTerm d ⊢σ ⊢Δ)) }
  substitutionRedTerm (K-subst {B} x₂ x₃ d x₄) ⊢σ ⊢Δ =
    let _ , (x₁ , _) , _ = inversion-Id-⊢ (⊢∙→⊢ (wf x₂)) in
    case substitutionTerm x₁ ⊢σ ⊢Δ of λ
      ⊢σt →
    PE.subst (_⊢_⇒_∷_ _ _ _)
      (PE.sym (singleSubstLift B _))
      (K-subst
        (substitution x₂ (liftSubst′ ⊢Δ (Idⱼ′ x₁ x₁) ⊢σ)
           (∙ Idⱼ′ ⊢σt ⊢σt))
        (PE.subst (_ ⊢ _ ∷_) (singleSubstLift B rfl) (substitutionTerm x₃ ⊢σ ⊢Δ))
        (substitutionRedTerm d ⊢σ ⊢Δ) x₄)
  substitutionRedTerm ([]-cong-subst x x₁ x₂ d x₃) ⊢σ ⊢Δ =
    []-cong-subst (substitution x ⊢σ ⊢Δ) (substitutionTerm x₁ ⊢σ ⊢Δ)
      (substitutionTerm x₂ ⊢σ ⊢Δ) (substitutionRedTerm d ⊢σ ⊢Δ) x₃
  substitutionRedTerm
    {σ} (J-β {t} {A} {t′} {B} {u} x₁ x₂ x₃ x₄ x₅ x₆) ⊢σ ⊢Δ =
    let x = ⊢∙→⊢ (wf (⊢∙→⊢ (wf x₄))) in
    case substitution x ⊢σ ⊢Δ of λ
      ⊢σA →
    case wf x₄ of λ {
      (∙ ⊢Id) →
    case liftSubst′ ⊢Δ x ⊢σ of
      λ ⊢⇑σ →
    case substitution ⊢Id ⊢⇑σ (∙ ⊢σA) of λ
      ⊢σId →
    case substitution x₄ (liftSubst′ (∙ ⊢σA) ⊢Id ⊢⇑σ) (∙ ⊢σId) of λ
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
        (J-β ⊢σt
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
  substitutionRedTerm (K-β {B} x₁ x₂ x₃) ⊢σ ⊢Δ =
    case wf x₁ of λ {
      (∙ ⊢Id) →
    PE.subst (_⊢_⇒_∷_ _ _ _)
      (PE.sym (singleSubstLift B rfl))
      (K-β
        (substitution x₁ (liftSubst′ ⊢Δ ⊢Id ⊢σ)
          (∙ substitution ⊢Id ⊢σ ⊢Δ))
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
