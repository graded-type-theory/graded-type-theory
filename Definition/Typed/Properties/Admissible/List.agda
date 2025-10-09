------------------------------------------------------------------------
-- Typing, equality and reduction rules related to List
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
import Definition.Untyped
import Definition.Untyped.List
open import Graded.Modality

module Definition.Typed.Properties.Admissible.List
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Definition.Untyped M)
  (pₕ pₗ : M)
  (open Definition.Untyped.List 𝕄 pₕ pₗ)
  (open Modality 𝕄)
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  -- It is assumed that a certain unit type is allowed.
  (Unit-ok : Unitʷ-allowed)
  -- It is assumed that certain Σ-types are allowed
  (Σ-ok₁ : Σʷ-allowed pₕ 𝟘)
  (Σ-ok₂ : Σʷ-allowed pₗ 𝟙)
  where

open import Graded.Mode 𝕄
open import Definition.Typed R
open import Definition.Typed.Properties R
import Definition.Typed.Properties.Admissible.Vec 𝕨 pₕ R Unit-ok Σ-ok₁ as V
import Definition.Untyped.Vec 𝕄 𝕨 pₕ as VU
import Definition.Typed.Reasoning.Reduction R as RRed
import Definition.Typed.Reasoning.Term R as RTerm
import Definition.Typed.Reasoning.Type R as RType
open import Definition.Typed.Stability R
open import Definition.Typed.Syntactic R
open import Definition.Typed.Substitution.Primitive R
open import Definition.Typed.Weakening R renaming (wk to wkType)
open import Definition.Untyped.Properties M

open import Tools.Fin
open import Tools.Function
open import Tools.Nat hiding (_+_)
open import Tools.Product
open import Tools.Reasoning.PropositionalEquality
import Tools.PropositionalEquality as PE

private variable
  n : Nat
  A A′ P k h h′ t t′ nl cs xs : Term _
  Γ : Cons _ _
  p₁ p₂ q r₁ r₂ : M
  l : Universe-level

opaque
  unfolding List

  -- A typing rule for List as a term

  ⊢∷-List :
    Γ ⊢ A ∷ U l →
    Γ ⊢ List l A ∷ U l
  ⊢∷-List {Γ} {A} {l} ⊢A =
    let ⊢Γ = wfTerm ⊢A
        ⊢A′ = wkTerm (stepʷ id (ℕⱼ ⊢Γ)) ⊢A
    in  ⊢∷-conv-PE (ΠΣⱼ (ℕⱼ ⊢Γ) (V.⊢Vec′∷U ⊢A′ (var (∙ ℕⱼ ⊢Γ) here)) Σ-ok₂)
          (PE.cong U (⊔-comm l 0))

opaque

  -- A typing rule for List

  ⊢-List :
    Γ ⊢ A ∷ U l →
    Γ ⊢ List l A
  ⊢-List ⊢A =
    univ (⊢∷-List ⊢A)

opaque
  unfolding List

  -- Congruence for List

  ⊢≡∷-List-cong :
    Γ ⊢ A ≡ A′ ∷ U l →
    Γ ⊢ List l A ≡ List l A′ ∷ U l
  ⊢≡∷-List-cong A≡A′ =
    let ⊢Γ = wfEqTerm A≡A′
    in  ⊢≡∷-conv-PE (ΠΣ-cong (refl (ℕⱼ ⊢Γ)) (V.⊢∷Vec′-cong (wkEqTerm (stepʷ id (ℕⱼ ⊢Γ)) A≡A′) (refl (var₀ (ℕⱼ ⊢Γ)))) Σ-ok₂)
          (PE.cong U (⊔-identityʳ _))

opaque
  unfolding List

  -- Congruence for List

  ⊢≡-List-cong :
    Γ ⊢ A ≡ A′ ∷ U l →
    Γ ⊢ List l A ≡ List l A′
  ⊢≡-List-cong A≡A′ = univ (⊢≡∷-List-cong A≡A′)

opaque
  unfolding nil

  -- A typing rule for nil

  ⊢∷-nil :
    Γ ⊢ A ∷ U l →
    Γ ⊢ nil l A ∷ List l A
  ⊢∷-nil ⊢A =
    let ⊢Γ = wfTerm ⊢A
        ⊢A′ = wkTerm (stepʷ id (ℕⱼ ⊢Γ)) ⊢A
    in  ⊢∷-conv-PE
          (prodⱼ (V.⊢Vec′ ⊢A′ (var (∙ ℕⱼ ⊢Γ) here)) (zeroⱼ ⊢Γ)
            (⊢∷-conv-PE (V.⊢nil′ ⊢A) V.Vec₀≡₀)
            Σ-ok₂)
          (PE.sym List≡)

opaque

  -- Reduction under cons

  ⊢⇒*∷-cons-subst :
    Γ ⊢ A ∷ U l →
    Γ ⊢ h ∷ A →
    Γ ⊢ t ⇒* t′ ∷ List l A →
    Γ ⊢ cons l A h t ⇒* cons l A h t′ ∷ List l A
  ⊢⇒*∷-cons-subst {A} {l} ⊢A ⊢h t⇒*t′ =
   let ⊢Γ = wfTerm ⊢h
       ⊢L = ⊢-List ⊢A
       ⊢L′ = wkType (stepʷ id (⊢-cong ⊢L List≡)) ⊢L
       ⊢A₁ = wkTerm (stepʷ id (ℕⱼ ⊢Γ)) ⊢A
       ⊢V = V.⊢Vec′ ⊢A₁ (var₀ (ℕⱼ ⊢Γ))
       ⊢x1 = var₁ ⊢V
       ⊢x0 = ⊢∷-conv-PE (var₀ ⊢V)
             (PE.trans VU.Vec′-wk (PE.cong (λ x → VU.Vec′ _ x _) (wk-comp _ _ _)))
       ⊢A₂ = wkTerm (stepʷ (step id) ⊢V) ⊢A
       ⊢h₂ = wkTerm (stepʷ (step id) ⊢V) ⊢h
       ⊢cs = ⊢∷-conv-PE (V.⊢cons′ ⊢A₂ ⊢x1 ⊢h₂ ⊢x0) $ begin
         VU.Vec′ l (wk₂ A) (suc (var x1))                        ≡˘⟨ PE.cong (λ x → VU.Vec′ l x _) (step-sgSubst _ _) ⟩
         VU.Vec′ l (wk[ 3 ]′ A [ suc (var x1) ]₀) (suc (var x1)) ≡˘⟨ VU.Vec′-subst ⟩
         VU.Vec′ l (wk[ 3 ]′ A) (var x0) [ suc (var x1) ]₀       ∎
       ⊢A₃ = wkTerm (stepʷ (step (step id)) (ℕⱼ (∙ ⊢V))) ⊢A
       ⊢V₃ = V.⊢Vec′ ⊢A₃ (var₀ (ℕⱼ (∙ ⊢V)))
       ⊢u = ⊢∷-conv-PE (prodⱼ ⊢V₃ (sucⱼ ⊢x1) ⊢cs Σ-ok₂) $ begin
         Σʷ pₗ , 𝟙 ▷ ℕ ▹ VU.Vec′ l (wk[ 3 ]′ A) (var x0)                     ≡˘⟨ PE.cong (λ x → Σʷ pₗ , 𝟙 ▷ ℕ ▹ VU.Vec′ l x _) (wk-comp _ _ A) ⟩
         Σʷ pₗ , 𝟙 ▷ ℕ ▹ VU.Vec′ l (wk (lift (stepn id 2)) (wk1 A)) (var x0) ≡˘⟨ PE.cong (Σʷ pₗ , 𝟙 ▷ ℕ ▹_) VU.Vec′-wk ⟩
         Σʷ pₗ , 𝟙 ▷ ℕ ▹ wk (lift (stepn id 2)) (VU.Vec′ l (wk1 A) (var x0)) ≡⟨⟩
         wk₂ (Σʷ pₗ , 𝟙 ▷ ℕ ▹ VU.Vec′ l (wk1 A) (var x0))                    ≡˘⟨ PE.cong wk₂ List≡ ⟩
         wk₂ (List l A)                                                     ≡⟨ wk≡subst _ _ ⟩
         List l A [ wkSubst 2 idSubst ]                                     ≡˘⟨ wk1-tail (List l A) ⟩
         wk1 (List l A) [ consSubst (wkSubst 2 idSubst) _ ]                 ≡⟨⟩
         wk1 (List l A) [ prodʷ pₗ (var x1) (var x0) ]↑²                    ∎
   in  ⊢⇒*∷-cong (⊢⇒*∷-conv-PE
         (prodrec-subst* ⊢L′ (⊢⇒*∷-conv-PE t⇒*t′ List≡) ⊢u)
         (wk1-sgSubst _ _)) (PE.sym cons≡) (PE.sym cons≡)

opaque
  unfolding cons

  -- A typing rule for cons

  ⊢∷-cons :
    Γ ⊢ A ∷ U l →
    Γ ⊢ h ∷ A →
    Γ ⊢ t ∷ List l A →
    Γ ⊢ cons l A h t ∷ List l A
  ⊢∷-cons ⊢A ⊢h ⊢t =
    redFirst*Term (⊢⇒*∷-cons-subst ⊢A ⊢h (id ⊢t))

opaque

  -- Congruence for cons

  ⊢≡∷-cons-cong :
    Γ ⊢ A ≡ A′ ∷ U l →
    Γ ⊢ h ≡ h′ ∷ A →
    Γ ⊢ t ≡ t′ ∷ List l A →
    Γ ⊢ cons l A h t ≡ cons l A′ h′ t′ ∷ List l A
  ⊢≡∷-cons-cong {A} {A′} {l} {h} {h′} {t} {t′} A≡A′ h≡h′ t≡t′ =
    let ⊢Γ = wfEqTerm A≡A′
        _ , ⊢A , _ = syntacticEqTerm A≡A′
        ⊢L = ⊢-cong (⊢-List ⊢A) List≡
        ⊢V = V.⊢Vec′ (wkTerm (stepʷ id (ℕⱼ ⊢Γ)) ⊢A) (var₀ (ℕⱼ ⊢Γ))
        L≡L′ = wkEq (stepʷ id ⊢L) (⊢≡-List-cong A≡A′)
        t≡t′ = ⊢≡∷-conv-PE t≡t′ List≡
        ⊢x1 = var₁ ⊢V
        ⊢x0 = ⊢∷-conv-PE (var₀ ⊢V)
               (PE.trans VU.Vec′-wk (PE.cong (λ x → VU.Vec′ l x _) (wk-comp _ _ A)))
        h₂≡h′₂ = wkEqTerm (stepʷ (step id) ⊢V) h≡h′
        cs≡cs′ = ⊢≡∷-conv-PE (V.⊢≡∷-cons′-cong (wkTerm (stepʷ (step id) ⊢V) ⊢A) ⊢x1 h₂≡h′₂ (refl ⊢x0)) $ begin
          VU.Vec′ l (wk₂ A) (suc (var x1)) ≡˘⟨ PE.cong (λ x → VU.Vec′ l x _) (step-sgSubst _ _) ⟩
          VU.Vec′ l (wk[ 3 ]′ A [ suc (var x1) ]₀) (suc (var x1)) ≡˘⟨ VU.Vec′-subst ⟩
          VU.Vec′ l (wk[ 3 ]′ A) (var x0) [ suc (var x1) ]₀ ∎
        ⊢V₃ = V.⊢Vec′ (wkTerm (stepʷ (step (step id)) (ℕⱼ (∙ ⊢V))) ⊢A) (var₀ (ℕⱼ (∙ ⊢V)))
        u≡u′ = ⊢≡∷-conv-PE (prod-cong ⊢V₃ (refl (sucⱼ ⊢x1)) cs≡cs′ Σ-ok₂) $ begin
          Σʷ pₗ , 𝟙 ▷ ℕ ▹ VU.Vec′ l (wk[ 3 ]′ A) (var x0)                                     ≡˘⟨ PE.cong (λ x → Σʷ _ , _ ▷ ℕ ▹ VU.Vec′ l x _) (wk-comp _ _ _) ⟩
          Σʷ pₗ , 𝟙 ▷ ℕ ▹ VU.Vec′ l (wk1 (wk₂ A)) (var x0)                                    ≡˘⟨ List≡ ⟩
          List l (wk₂ A)                                                                     ≡˘⟨ List-wk ⟩
          wk₂ (List l A)                                                                     ≡⟨ wk≡subst _ _ ⟩
          List l A [ wkSubst 2 idSubst ]                                                     ≡⟨⟩
          List l A [ consSubst (wkSubst 2 idSubst) (prodʷ pₗ (var x1) (var x0)) ₛ• step id ] ≡˘⟨ subst-wk (List l A) ⟩
          wk1 (List l A) [ prodʷ pₗ (var x1) (var x0) ]↑²                                    ∎
    in
    flip ⊢≡∷-conv-PE (wk1-sgSubst _ _)
      (cons l A h t
        ≡⟨ cons≡ ⟩⊢≡
      prodrec 𝟙 pₗ 𝟘 (wk1 (List l A)) t (prodʷ pₗ (suc (var x1)) (VU.cons′ (wk₂ A) (var x1) (wk₂ h) (var x0)))
        ≡⟨ prodrec-cong′ L≡L′ t≡t′ u≡u′ ⟩⊢∎≡
      prodrec 𝟙 pₗ 𝟘 (wk1 (List l A′)) t′ (prodʷ pₗ (suc (var x1)) (VU.cons′ (wk₂ A′) (var x1) (wk₂ h′) (var x0)))
        ≡˘⟨ cons≡ ⟩
      cons l A′ h′ t′ ∎)
    where
    open RTerm

opaque

  -- cons reduces to a pair when the tail is a pair.

  ⊢⇒∷-cons-prod :
    Γ ⊢ A ∷ U l →
    Γ ⊢ k ∷ ℕ →
    Γ ⊢ h ∷ A →
    Γ ⊢ t ∷ VU.Vec′ l A k →
    Γ ⊢ cons l A h (prodʷ pₗ k t) ⇒ prodʷ pₗ (suc k) (VU.cons′ A k h t) ∷ List l A
  ⊢⇒∷-cons-prod {A} {l} {k} {h} {t} ⊢A ⊢k ⊢h ⊢t =
    let ⊢Γ = wfTerm ⊢A
        ⊢L = ⊢-List ⊢A
        ⊢L′ = ⊢-cong ⊢L List≡
        ⊢L₁ = wkType (stepʷ id ⊢L′) ⊢L
        ⊢t′ = ⊢∷-conv-PE ⊢t (PE.sym (PE.trans VU.Vec′-subst (PE.cong (λ x → VU.Vec′ l x k) (wk1-sgSubst _ _))))
        ⊢A₁ = wkTerm (stepʷ id (ℕⱼ ⊢Γ)) ⊢A
        ⊢V = V.⊢Vec′ ⊢A₁ (var₀ (ℕⱼ ⊢Γ))
        ⊢A₂ = wkTerm (stepʷ (step id) ⊢V) ⊢A
        ⊢h₂ = wkTerm (stepʷ (step id) ⊢V) ⊢h
        ⊢x0 = ⊢∷-conv-PE (var₀ ⊢V) $ begin
          wk1 (VU.Vec′ l (wk1 A) (var x0)) ≡⟨ VU.Vec′-wk ⟩
          VU.Vec′ l (wk2 A) (var x1)       ≡⟨ PE.cong (λ x → VU.Vec′ l x _) wk[]≡wk[]′ ⟩
          VU.Vec′ l (wk₂ A) (var x1)       ∎
        ⊢cs = ⊢∷-conv-PE (V.⊢cons′ ⊢A₂ (var₁ ⊢V) ⊢h₂ ⊢x0) $ begin
          VU.Vec′ l (wk₂ A) (suc (var x1))                         ≡˘⟨ PE.cong (λ x → VU.Vec′ l x _) (wk1-sgSubst _ _) ⟩
          VU.Vec′ l (wk1 (wk₂ A) [ suc (var x1) ]₀) (suc (var x1)) ≡˘⟨ VU.Vec′-subst ⟩
          VU.Vec′ l (wk1 (wk₂ A)) (var x0) [ suc (var x1) ]₀       ∎
        ⊢A₃ = wkTerm (stepʷ id (ℕⱼ (∙ ⊢V))) ⊢A₂
        ⊢V₃ = V.⊢Vec′ ⊢A₃ (var₀ (ℕⱼ (∙ ⊢V)))
        ⊢p = ⊢∷-conv-PE (prodⱼ ⊢V₃ (sucⱼ (var₁ ⊢V)) ⊢cs Σ-ok₂) $ begin
          Σʷ pₗ , 𝟙 ▷ ℕ ▹ VU.Vec′ l (wk1 (wk₂ A)) (var x0)                                      ≡˘⟨ List≡ ⟩
          List l (wk₂ A)                                                                       ≡⟨ PE.cong (List l) (wk≡subst _ _) ⟩
          List l (A [ wkSubst 2 idSubst ])                                                     ≡⟨ PE.cong (List l) (substVar-to-subst (λ _ → PE.refl) A) ⟩
          List l (A [ consSubst (wkSubst 2 idSubst) (prodʷ pₗ (var x1) (var x0)) ₛ• step id ]) ≡˘⟨ PE.cong (List l) (subst-wk A) ⟩
          List l (wk1 A [ prodʷ pₗ (var x1) (var x0) ]↑²)                                      ≡˘⟨ List-subst ⟩
          List l (wk1 A) [ prodʷ pₗ (var x1) (var x0) ]↑²                                      ≡˘⟨ PE.cong (_[ prodʷ pₗ (var x1) (var x0) ]↑²) List-wk ⟩
          wk1 (List l A) [ prodʷ pₗ (var x1) (var x0) ]↑²                                      ∎
    in  ⊢⇒∷-conv-PE (⊢⇒∷-cong (prodrec-β-⇒ ⊢L₁ ⊢k ⊢t′ ⊢p) (PE.sym cons≡)
          (PE.trans (PE.cong (prodʷ _ _) VU.cons′-subst) (PE.cong₂ (λ x y → prodʷ _ _ (VU.cons′ x k y t)) wk₂-[,] wk₂-[,])))
          (wk1-sgSubst _ _)
    where
    open RRed

opaque

  -- cons is definitionally equal to a pair when the tail is a pair.

  ⊢≡∷-cons-prod :
    Γ ⊢ A ∷ U l →
    Γ ⊢ k ∷ ℕ →
    Γ ⊢ h ∷ A →
    Γ ⊢ t ∷ VU.Vec′ l A k →
    Γ ⊢ cons l A h (prodʷ pₗ k t) ≡ prodʷ pₗ (suc k) (VU.cons′ A k h t) ∷ List l A
  ⊢≡∷-cons-prod ⊢A ⊢k ⊢h ⊢t = subsetTerm (⊢⇒∷-cons-prod ⊢A ⊢k ⊢h ⊢t)

private opaque
  unfolding listrec

  -- A lemma used to prove several typing and reduction rules for listrec

  listrec-lemma :
    Γ ⊢ A ∷ U l →
    Γ »∙ List l A ⊢ P →
    Γ ⊢ nl ∷ P [ nil l A ]₀ →
    Γ »∙ A »∙ wk1 (List l A) »∙ P [ var x0 ]↑² ⊢ cs ∷ P [ 3 ][ cons l (wk[ 3 ]′ A) (var x2) (var x1) ]↑ →
    Π-allowed r₂ q →
    (∀ {xs} → Γ ⊢ xs ∷ List l A → Γ ⊢ listrec l r₁ r₂ p₁ p₂ q A P nl cs xs ∷ P [ xs ]₀) ×
    Γ ⊢ listrec l r₁ r₂ p₁ p₂ q A P nl cs (nil l A) ⇒* nl ∷ P [ nil l A ]₀ ×
    (∀ {h t k t′} → Γ ⊢ h ∷ A →
      Γ ⊢ k ∷ ℕ →
      Γ ⊢ t′ ∷ VU.Vec′ l A k →
      (Γ ⊢ t ⇒* prodʷ pₗ k t′ ∷ List l A →
        Γ ⊢ listrec l r₁ r₂ p₁ p₂ q A P nl cs (cons l A h t) ⇒*
            cs [ consSubst (consSubst (sgSubst h) (prodʷ pₗ k t′))
                   (VU.vecrec′ l (p₁ · pₗ) p₂ r₂ (q · pₗ) q A (P [ 2 ][ prodʷ pₗ (var x1) (var x0) ]↑) nl
                   (cs [ consSubst (consSubst (wkSubst 3 idSubst) (var x1)) (prodʷ pₗ (var x2) (var x0)) ⇑ ])
                   k t′) ] ∷
            P [ cons l A h t ]₀) ×
     (Γ ⊢ t ≡ prodʷ pₗ k t′ ∷ List l A →
       Γ ⊢ listrec l r₁ r₂ p₁ p₂ q A P nl cs (cons l A h t) ≡
           cs [ consSubst (consSubst (sgSubst h) (prodʷ pₗ k t′)) (listrec l r₁ r₂ p₁ p₂ q A P nl cs t) ] ∷
           P [ cons l A h t ]₀))
  listrec-lemma {Γ} {A} {l} {P} {nl} {cs} {r₂} {q} {r₁} {p₁} {p₂} ⊢A ⊢P ⊢nl ⊢cs Π-ok =
    let ⊢Γ = wfTerm ⊢A
        ⊢L = ⊢-List ⊢A
        ⊢P′ = stability (refl-∙ (⊢≡-refl-PE List≡ ⊢L)) ⊢P
        ⊢A₁ = wkTerm (stepʷ id (ℕⱼ ⊢Γ)) ⊢A
        ⊢V = V.⊢Vec′ ⊢A₁ (var₀ (ℕⱼ ⊢Γ))
        ⊢A₂ = wkTerm (stepʷ (step id) ⊢V) ⊢A
        ⊢nl₂ = ⊢∷-conv-PE (wkTerm (stepʷ (step id) ⊢V) ⊢nl) $ begin
          wk₂ (P [ nil l A ]₀)                                            ≡⟨ wk-subst P ⟩
          P [ stepn id 2 •ₛ sgSubst (nil l A) ]                           ≡⟨ substVar-to-subst (λ
                                                                               { x0 → PE.trans (PE.cong wk₂ nil≡) (PE.cong (prodʷ pₗ zero) VU.nil′-wk)
                                                                               ; (_+1 x) → PE.refl})
                                                                               P ⟩
          P [ consSubst (sgSubst zero) (VU.nil′ l (wk₂ A)) ₛ•ₛ
              consSubst (wkSubst 4 idSubst) (prodʷ pₗ (var x1) (var x0)) ] ≡˘⟨ substCompEq P ⟩
          P [ 4 ][ prodʷ pₗ (var x1) (var x0) ]↑
            [ zero , VU.nil′ l (wk₂ A) ]₁₀                                 ∎
        ⊢A₃ = wkTerm (stepʷ id (ℕⱼ (∙ ⊢V))) ⊢A₂
        ⊢V₃ = V.⊢Vec′ ⊢A₃ (var₀ (ℕⱼ (∙ ⊢V)))
        ⊢Γ₄ = ∙ ⊢V₃
        ⊢A₅ = wkTerm (stepʷ (step (step (step (step id)))) (ℕⱼ ⊢Γ₄)) ⊢A
        ⊢V₅ = V.⊢Vec′ ⊢A₅ (var₀ (ℕⱼ ⊢Γ₄))
        ⊢x0′ = ⊢∷-conv-PE (var₀ ⊢V₃) $ begin
          wk1 (VU.Vec′ l (wk1 (wk₂ A)) (var x0))      ≡⟨ PE.cong (λ x → wk1 (VU.Vec′ l x _)) (wk-comp _ _ A) ⟩
          wk1 (VU.Vec′ l (wk[ 3 ]′ A) (var x0))       ≡⟨ VU.Vec′-wk ⟩
          VU.Vec′ l (wk1 (wk[ 3 ]′ A)) (var x1)       ≡⟨ PE.cong (λ x → VU.Vec′ l x _) (wk-comp _ _ A) ⟩
          VU.Vec′ l (wk[ 4 ]′ A) (var x1)             ≡˘⟨ PE.cong (λ x → VU.Vec′ l x _) (step-sgSubst _ _) ⟩
          VU.Vec′ l (wk[ 5 ]′ A [ var x1 ]₀) (var x1) ≡˘⟨ VU.Vec′-subst ⟩
          VU.Vec′ l (wk[ 5 ]′ A) (var x0) [ var x1 ]₀ ∎
        ⊢p = ⊢∷-conv-PE (prodⱼ ⊢V₅ (var₁ ⊢V₃) ⊢x0′ Σ-ok₂) $ begin
          Σʷ pₗ , 𝟙 ▷ ℕ ▹ VU.Vec′ l (wk[ 5 ]′ A) (var x0)       ≡˘⟨ PE.cong (λ x → Σʷ pₗ , 𝟙 ▷ ℕ ▹ VU.Vec′ l x _) (wk-comp _ _ _) ⟩
          Σʷ pₗ , 𝟙 ▷ ℕ ▹ VU.Vec′ l (wk1 (wk[ 4 ]′ A)) (var x0) ≡˘⟨ List≡ ⟩
          List l (wk[ 4 ]′ A)                                  ≡˘⟨ List-wk ⟩
          wk[ 4 ]′ (List l A)                                  ≡˘⟨ wk[]≡wk[]′ ⟩
          wk[ 4 ] (List l A)                                   ∎
        ⊢P₊ = subst-⊢ ⊢P (⊢ˢʷ∷-[][]↑ ⊢p)
        ⊢V₄ = ⊢-cong (wkType (stepʷ id (univ ⊢A₃)) ⊢V₃) (wk≡subst _ _)
        V₄≡ = begin
          VU.Vec′ l (wk1 (wk₂ A)) (var x0) [ wk1Subst idSubst ] ≡˘⟨ wk≡subst _ _ ⟩
          wk1 (VU.Vec′ l (wk1 (wk₂ A)) (var x0))                ≡⟨ VU.Vec′-wk ⟩
          VU.Vec′ l (wk1 (wk1 (wk₂ A))) (var x1)                ≡⟨ PE.cong (λ x → VU.Vec′ l x _) (wk-comp _ _ (wk₂ A)) ⟩
          VU.Vec′ l (wk₂ (wk₂ A)) (var x1)                      ∎
        ⊢P₊₊ = stability (refl-∙ (⊢≡-refl-PE V₄≡ ⊢V₄))
                 (subst-⊢ ⊢P₊ (⊢ˢʷ∷-⇑ ⊢V₄ (⊢ˢʷ∷-wkSubst {k = 1} (∙ (univ ⊢A₃)) (⊢ˢʷ∷-idSubst (wf (⊢∙→⊢ (wf ⊢P₊)))))))
        ⊢x2 = ⊢∷-conv-PE (var₂ ⊢P₊₊) $ begin
          wk[ 4 ] (wk₂ A)         ≡⟨ wk[]≡wk[]′ ⟩
          wk[ 4 ]′ (wk₂ A)        ≡⟨ wk-comp _ _ A ⟩
          wk[ 6 ]′ A              ≡⟨ wk≡subst _ A ⟩
          A [ wkSubst 6 idSubst ] ∎
        ⊢x2′ = ⊢∷-conv-PE ⊢x2 (PE.sym (wk≡subst _ _))
        ⊢x1′ = ⊢∷-conv-PE (var₁ ⊢P₊₊) $ begin
          wk2 (VU.Vec′ l (wk₂ (wk₂ A)) (var x1))      ≡⟨ PE.cong (λ x → wk2 (VU.Vec′ l x _)) (wk-comp _ _ A) ⟩
          wk2 (VU.Vec′ l (wk[ 4 ]′ A) (var x1))       ≡⟨ wk[]≡wk[]′ ⟩
          wk₂ (VU.Vec′ l (wk[ 4 ]′ A) (var x1))       ≡⟨ VU.Vec′-wk ⟩
          VU.Vec′ l (wk₂ (wk[ 4 ]′ A)) (var x3)       ≡⟨ PE.cong (λ x → VU.Vec′ l x _) (wk-comp _ _ A) ⟩
          VU.Vec′ l (wk[ 6 ]′ A) (var x3)             ∎
        ⊢x1 = ⊢∷-conv-PE ⊢x1′ $ begin
          VU.Vec′ l (wk[ 6 ]′ A) (var x3)             ≡˘⟨ PE.cong (λ x → VU.Vec′ l x _) (step-sgSubst _ _) ⟩
          VU.Vec′ l (wk[ 7 ]′ A [ var x3 ]₀) (var x3) ≡˘⟨ VU.Vec′-subst ⟩
          VU.Vec′ l (wk[ 7 ]′ A) (var x0) [ var x3 ]₀ ∎
        ⊢A₇ = wkTerm (stepʷ (step (step (step (step (step (step id)))))) (ℕⱼ (∙ ⊢P₊₊))) ⊢A
        ⊢V₇ = V.⊢Vec′ ⊢A₇ (var₀ (ℕⱼ (∙ ⊢P₊₊)))
        ⊢p′ = ⊢∷-conv-PE (prodⱼ ⊢V₇ (var₃ ⊢P₊₊) ⊢x1 Σ-ok₂) $ begin
          Σʷ pₗ , 𝟙 ▷ ℕ ▹ VU.Vec′ l (wk[ 7 ]′ A) (var x0)       ≡˘⟨ PE.cong (λ x → Σʷ _ , _ ▷ ℕ ▹ VU.Vec′ l x _) (wk-comp _ _ A) ⟩
          Σʷ pₗ , 𝟙 ▷ ℕ ▹ VU.Vec′ l (wk1 (wk[ 6 ]′ A)) (var x0) ≡˘⟨ List≡ ⟩
          List l (wk[ 6 ]′ A)                                  ≡˘⟨ List-wk ⟩
          wk[ 6 ]′ (List l A)                                  ≡⟨ wk≡subst _ _ ⟩
          List l A [ wkSubst 6 idSubst ]                       ≡˘⟨ wk1-tail (List l A) ⟩
          wk1 (List l A) [ 6 ][ var x2 ]↑                      ∎
        ⊢x0′ = ⊢∷-conv-PE (var₀ ⊢P₊₊) $ begin
          wk1 (P [ 4 ][ prodʷ pₗ (var x1) (var x0) ]↑ [ wk1Subst idSubst ⇑ ])
            ≡⟨ PE.cong wk1 (substCompEq P) ⟩
          wk1 (P [ (wk1Subst idSubst ⇑) ₛ•ₛ consSubst (wkSubst 4 idSubst) (prodʷ pₗ (var x1) (var x0)) ])
            ≡⟨ wk-subst P ⟩
          P [ step id •ₛ ((wk1Subst idSubst ⇑) ₛ•ₛ consSubst (wkSubst 4 idSubst) (prodʷ pₗ (var x1) (var x0))) ]
            ≡⟨ substVar-to-subst (λ { x0 → PE.refl ; (_+1 x) → PE.refl}) P ⟩
          P [ consSubst (consSubst (wkSubst 6 idSubst) (var x2)) (prodʷ pₗ (var x3) (var x1)) ₛ•ₛ consSubst (wkSubst 2 idSubst) (var x0) ]
            ≡˘⟨ substCompEq P ⟩
          P [ 2 ][ var x0 ]↑ [ consSubst (consSubst (wkSubst 6 idSubst) (var x2)) (prodʷ pₗ (var x3) (var x1)) ] ∎
        ⊢cs′ = subst-⊢∷ ⊢cs (→⊢ˢʷ∷∙ (→⊢ˢʷ∷∙ (→⊢ˢʷ∷∙ (⊢ˢʷ∷-wkSubst (∙ ⊢P₊₊) (⊢ˢʷ∷-idSubst ⊢Γ)) ⊢x2) ⊢p′) ⊢x0′)
        ⊢A₆ = wkTerm (stepʷ (step (step (step (step (step id))))) ⊢P₊₊) ⊢A
        A₆≡ = begin
          wk[ 3 ]′ A [ consSubst (consSubst (consSubst (wkSubst 6 idSubst) _) _) _ ] ≡⟨ step-consSubst A ⟩
          wk[ 2 ]′ A [ consSubst (consSubst (wkSubst 6 idSubst) _) _ ]               ≡⟨ step-consSubst A ⟩
          wk[ 1 ]′ A [ consSubst (wkSubst 6 idSubst) _ ]                             ≡⟨ wk1-tail A ⟩
          A [ wkSubst 6 idSubst ]                                                    ≡˘⟨ wk≡subst _ A ⟩
          wk[ 6 ]′ A                                                                 ∎
        cons≡prod = ⊢≡∷-conv-PE (⊢≡∷-cons-prod ⊢A₆ (var₃ ⊢P₊₊) ⊢x2′ ⊢x1′) $ begin
          List l (wk[ 6 ]′ A)            ≡˘⟨ List-wk ⟩
          wk[ 6 ]′ (List l A)            ≡⟨ wk≡subst _ _ ⟩
          List l A [ wkSubst 6 idSubst ] ∎
        ⊢cs″ = let open RType
               in  conv ⊢cs′
                 (P [ 3 ][ cons l (wk[ 3 ]′ A) (var x2) (var x1) ]↑
                    [ consSubst (consSubst (consSubst (wkSubst 6 idSubst) (var x2)) (prodʷ pₗ (var x3) (var x1))) (var x0) ]
                       ≡⟨ substCompEq P ⟩⊢≡
                 P [ consSubst (consSubst (consSubst (wkSubst 6 idSubst) (var x2)) (prodʷ pₗ (var x3) (var x1))) (var x0) ₛ•ₛ
                     consSubst (wkSubst 3 idSubst) (cons l (wk[ 3 ]′ A) (var x2) (var x1)) ]
                       ≡⟨ substVar-to-subst (λ { x0 → PE.trans cons-subst (PE.cong (λ x → cons l x _ _) A₆≡) ; (_+1 x) → PE.refl}) P ⟩⊢≡
                 P [ consSubst (wkSubst 6 idSubst) (cons l (wk[ 6 ]′ A) (var x2) (prodʷ pₗ (var x3) (var x1))) ]
                       ≡⟨ subst-⊢≡ (refl ⊢P) (→⊢ˢʷ≡∷∙ ⊢L (refl-⊢ˢʷ≡∷ (⊢ˢʷ∷-wkSubst (∙ ⊢P₊₊) (⊢ˢʷ∷-idSubst ⊢Γ))) cons≡prod) ⟩⊢∎≡
                 P [ consSubst (wkSubst 6 idSubst) (prodʷ pₗ (suc (var x3)) (VU.cons′ (wk[ 6 ]′ A) (var x3) (var x2) (var x1))) ]
                       ≡⟨ PE.cong (λ x → P [ consSubst _ (prodʷ _ _ (VU.cons′ x _ _ _)) ]) (PE.sym (wk-comp _ _ A)) ⟩
                 P [ consSubst (wkSubst 6 idSubst) (prodʷ pₗ (suc (var x3)) (VU.cons′ (wk[ 4 ]′ (wk₂ A)) (var x3) (var x2) (var x1))) ]
                       ≡˘⟨ substVar-to-subst (λ { x0 → PE.refl ; (_+1 x) → PE.refl}) P ⟩
                 P [ consSubst (consSubst (wkSubst 4 idSubst) (suc (var x3))) (VU.cons′ (wk[ 4 ]′ (wk₂ A)) (var x3) (var x2) (var x1)) ₛ•ₛ
                     consSubst (wkSubst 4 idSubst) (prodʷ pₗ (var x1) (var x0)) ]
                       ≡˘⟨ substCompEq P ⟩
                 P [ 4 ][ prodʷ pₗ (var x1) (var x0) ]↑
                   [ consSubst (consSubst (wkSubst 4 idSubst) (suc (var x3))) (VU.cons′ (wk[ 4 ]′ (wk₂ A)) (var x3) (var x2) (var x1)) ] ∎)
        ⊢x0 = ⊢∷-conv-PE (var₀ ⊢V) $ begin
               wk1 (VU.Vec′ l (wk1 A) (var x0)) ≡⟨ VU.Vec′-wk ⟩
               VU.Vec′ l (wk2 A) (var x1)       ≡⟨ PE.cong (λ x → VU.Vec′ l x _) wk[]≡wk[]′ ⟩
               VU.Vec′ l (wk₂ A) (var x1)       ∎
        ⊢vr = ⊢∷-conv-PE (V.⊢∷-vecrec′ PE.refl ⊢P₊ ⊢A₂ ⊢nl₂ ⊢cs″ (var₁ ⊢V) ⊢x0 Π-ok) $ begin
                P [ 4 ][ prodʷ pₗ (var x1) (var x0) ]↑ [ var x1 , var x0 ]₁₀
                  ≡⟨ substCompEq P ⟩
                P [ consSubst (sgSubst (var x1)) (var x0) ₛ•ₛ consSubst (wkSubst 4 idSubst) (prodʷ pₗ (var x1) (var x0)) ]
                  ≡⟨ substVar-to-subst (λ { x0 → PE.refl ; (x +1) → PE.refl}) P ⟩
                P [ prodʷ pₗ (var x1) (var x0) ]↑² ∎
        vrec = VU.vecrec′ l (p₁ · pₗ) p₂ r₂ (q · pₗ) q
                 (wk₂ A) (P [ 4 ][ prodʷ pₗ (var x1) (var x0) ]↑) (wk₂ nl)
                 (cs [ consSubst (consSubst (consSubst (wkSubst 6 idSubst)
                         (var x2)) (prodʷ pₗ (var x3) (var x1))) (var x0) ])
                 (var x1) (var x0)
        P[nil]≡ = begin
          P [ nil l A ]₀                                                  ≡⟨ substVar-to-subst (λ { x0 → nil≡ ; (_+1 x) → PE.refl}) P ⟩
          P [ consSubst (sgSubst zero) (VU.nil′ l A) ₛ•ₛ
              consSubst (wkSubst 2 idSubst) (prodʷ pₗ (var x1) (var x0)) ] ≡˘⟨ substCompEq P ⟩
          P [ 2 ][ prodʷ pₗ (var x1) (var x0) ]↑ [ zero , VU.nil′ l A ]₁₀ ∎
        ⊢nl′ = ⊢∷-conv-PE ⊢nl P[nil]≡
        A₁≡ = λ {k t} → begin
          wk1 A                                     ≡˘⟨ PE.cong wk1 wk₂-[,] ⟩
          wk1 (wk₂ A [ k , t ]₁₀)                   ≡˘⟨ wk1-liftSubst (wk₂ A) ⟩
          wk1 (wk₂ A) [ consSubst (sgSubst k) t ⇑ ] ∎
        V₂≡ = λ {k t} → begin
          VU.Vec′ l (wk₂ A) (var x1)                                          ≡˘⟨ PE.cong (λ x → VU.Vec′ l (wk₂ x) _) wk₂-[,] ⟩
          VU.Vec′ l (wk₂ (wk₂ A [ k , t ]₁₀)) (var x1)                        ≡˘⟨ PE.cong (λ x → VU.Vec′ l x _) (wk[]′-[⇑] (wk₂ A)) ⟩
          VU.Vec′ l (wk₂ (wk₂ A) [ consSubst (sgSubst k) t ⇑[ 2 ] ]) (var x1) ≡˘⟨ VU.Vec′-subst ⟩
          VU.Vec′ l (wk₂ (wk₂ A)) (var x1) [ consSubst (sgSubst k) t ⇑[ 2 ] ] ∎
        P[]≡₁ = λ {k t} → begin
          P [ 4 ][ prodʷ pₗ (var x1) (var x0) ]↑ [ wk1Subst idSubst ⇑ ] [ consSubst (sgSubst k) t ⇑[ 3 ] ]
              ≡⟨ PE.cong (_[ consSubst (sgSubst k) t ⇑[ 3 ] ]) (substCompEq P) ⟩
          P [ (wk1Subst idSubst ⇑) ₛ•ₛ consSubst (wkSubst 4 idSubst) (prodʷ pₗ (var x1) (var x0)) ]
            [ consSubst (sgSubst k) t ⇑[ 3 ] ]
              ≡⟨ substCompEq P ⟩
          P [ (consSubst (sgSubst k) t ⇑[ 3 ]) ₛ•ₛ ((wk1Subst idSubst ⇑) ₛ•ₛ
              consSubst (wkSubst 4 idSubst) (prodʷ pₗ (var x1) (var x0))) ]
                ≡⟨ substVar-to-subst (λ { x0 → PE.refl ; (_+1 x) → PE.refl}) P ⟩
          P [ (wk1Subst idSubst ⇑) ₛ•ₛ consSubst (wkSubst 2 idSubst) (prodʷ pₗ (var x1) (var x0)) ]
                ≡˘⟨ substCompEq P ⟩
          P [ 2 ][ prodʷ pₗ (var x1) (var x0) ]↑ [ wk1Subst idSubst ⇑ ] ∎
        cns = λ {n} (A : Term (4+ n)) → VU.cons′ A (var x3) (var x2) (var x1)
        cns≡ = λ {k t} → begin
          cns (wk[ 4 ]′ (wk₂ A)) [ consSubst (sgSubst k) t ⇑[ 4 ] ] ≡⟨ VU.cons′-subst ⟩
          cns (wk[ 4 ]′ (wk₂ A) [ consSubst (sgSubst k) t ⇑[ 4 ] ]) ≡⟨ PE.cong cns (wk[]′-[⇑] (wk₂ A)) ⟩
          cns (wk[ 4 ]′ (wk₂ A [ k , t ]₁₀))                        ≡⟨ PE.cong (λ x → cns (wk[ 4 ]′ x)) wk₂-[,] ⟩
          cns (wk[ 4 ]′ A)                                                         ∎
        P[]≡₂ = λ {k t} → begin
          P [ 4 ][ prodʷ pₗ (var x1) (var x0) ]↑ [ consSubst (consSubst (wkSubst 4 idSubst) (suc (var x3))) (cns (wk[ 4 ]′ (wk₂ A))) ]
            [ consSubst (sgSubst k) t ⇑[ 4 ] ]
              ≡⟨ PE.cong (_[ consSubst (sgSubst k) t ⇑[ 4 ] ]) (substCompEq P) ⟩
          P [ consSubst (consSubst (wkSubst 4 idSubst) (suc (var x3))) (cns (wk[ 4 ]′ (wk₂ A))) ₛ•ₛ
              consSubst (wkSubst 4 idSubst) (prodʷ pₗ (var x1) (var x0)) ]
            [ consSubst (sgSubst k) t ⇑[ 4 ] ]
              ≡⟨ substCompEq P ⟩
          P [ (consSubst (sgSubst k) t ⇑[ 4 ]) ₛ•ₛ
              (consSubst (consSubst (wkSubst 4 idSubst) (suc (var x3))) (cns (wk[ 4 ]′ (wk₂ A))) ₛ•ₛ
              consSubst (wkSubst 4 idSubst) (prodʷ pₗ (var x1) (var x0))) ]
              ≡⟨ substVar-to-subst (λ { x0 → PE.cong (prodʷ pₗ _) cns≡ ; (_+1 x) → PE.refl}) P ⟩
          P [ consSubst (consSubst (wkSubst 4 idSubst) (suc (var x3))) (cns (wk[ 4 ]′ A)) ₛ•ₛ
              consSubst (wkSubst 2 idSubst) (prodʷ pₗ (var x1) (var x0)) ]
              ≡˘⟨ substCompEq P ⟩
          P [ 2 ][ prodʷ pₗ (var x1) (var x0) ]↑ [ consSubst (consSubst (wkSubst 4 idSubst) (suc (var x3))) (cns (wk[ 4 ]′ A)) ] ∎
        P[]≡₃ = λ {k t} → begin
          P [ 4 ][ prod 𝕨 pₗ (var x1) (var x0) ]↑ [ consSubst (sgSubst k) t ⇑[ 2 ] ]
              ≡⟨ substCompEq P ⟩
          P [ (consSubst (sgSubst k) t ⇑[ 2 ]) ₛ•ₛ consSubst (wkSubst 4 idSubst) (prod 𝕨 pₗ (var x1) (var x0)) ]
              ≡⟨ substVar-to-subst (λ { x0 → PE.refl ; (_+1 x) → PE.refl}) P ⟩
          P [ consSubst (wkSubst 2 idSubst) (prod 𝕨 pₗ (var x1) (var x0)) ] ∎
    in
        (λ ⊢xs →
          let ⊢xs′ = ⊢∷-conv-PE ⊢xs List≡
          in prodrecⱼ ⊢P′ ⊢xs′ ⊢vr Σ-ok₂)
      , (let ⊢nil = ⊢∷-conv-PE (V.⊢nil′ ⊢A) V.Vec₀≡₀
             ⊢A₁′ = ⊢∷-cong ⊢A₁ A₁≡
             ⊢V₂ = V.⊢Vec′ (wkTerm (stepʷ (step id) (univ ⊢A₁′)) ⊢A) (var₁ (univ ⊢A₁′))
             ⊢σ = →⊢ˢʷ∷∙ (⊢ˢʷ∷-sgSubst (zeroⱼ ⊢Γ)) ⊢nil
             ⊢cs₊ = subst-⊢∷ ⊢cs″ (⊢ˢʷ∷-⇑[] {k = 4} (∙ ⊢P₊₊) ⊢σ)
             ⊢P₊₊₊ = subst-⊢ ⊢P₊₊ (⊢ˢʷ∷-⇑[] {k = 3} (∙ ⊢-cong ⊢V₄ V₄≡) ⊢σ)
             ⊢cs₊′ = stabilityTerm
               (refl-∙ (⊢≡-refl-PE′ (PE.sym A₁≡) (univ ⊢A₁)) ∙
                       ⊢≡-refl-PE′ (PE.sym V₂≡) ⊢V₂ ∙
                       ⊢≡-refl-PE P[]≡₁ ⊢P₊₊₊)
               (⊢∷-conv-PE ⊢cs₊ P[]≡₂)
             open RRed
         in
         listrec l r₁ r₂ p₁ p₂ q A P nl cs (nil l A)
             ≡⟨⟩⇒
         prodrec r₁ pₗ q P (nil l A) vrec
             ≡⟨ PE.cong (λ x → prodrec _ _ _ _ x vrec) nil≡ ⟩⇒
         prodrec r₁ pₗ q P (prodʷ pₗ zero (VU.nil′ l A)) vrec
             ⇒⟨ ⊢⇒∷-conv-PE (prodrec-β-⇒ ⊢P′ (zeroⱼ ⊢Γ) ⊢nil ⊢vr) (PE.cong (P [_]₀) (PE.sym nil≡)) ⟩
         vrec [ zero , VU.nil′ l A ]₁₀
             ≡⟨ VU.vecrec′-subst ⟩⇒
         VU.vecrec′ l (p₁ · pₗ) p₂ r₂ (q · pₗ) q (wk₂ A [ zero , VU.nil′ l A ]₁₀)
           (P [ 4 ][ prodʷ pₗ (var x1) (var x0) ]↑ [ consSubst (sgSubst zero) (VU.nil′ l A) ⇑[ 2 ] ])
           (wk₂ nl [ zero , VU.nil′ l A ]₁₀)
           (cs [ consSubst (consSubst (consSubst (wkSubst 6 idSubst)
                  (var x2)) (prodʷ pₗ (var x3) (var x1))) (var x0) ]
               [ consSubst (sgSubst zero) (VU.nil′ l A) ⇑[ 4 ] ])
           zero (VU.nil′ l A)
             ≡⟨ PE.cong₆ (VU.vecrec′ _ _ _ _ _ _) wk₂-[,] P[]≡₃ wk₂-[,] PE.refl PE.refl PE.refl ⟩⇒
         VU.vecrec′ l (p₁ · pₗ) p₂ r₂ (q · pₗ) q A
          (P [ consSubst (wkSubst 2 idSubst) (prod 𝕨 pₗ (var x1) (var x0)) ]) nl
          (cs [ consSubst (consSubst (consSubst (wkSubst 6 idSubst) (var x2))
                   (prod 𝕨 pₗ (var x3) (var x1))) (var x0) ]
              [ consSubst (sgSubst zero) (VU.nil′ l A) ⇑[ 4 ] ])
          zero (VU.nil′ l A)
             ⇒*⟨ ⊢⇒*∷-conv-PE (V.⊢⇒*∷-vecrec-β-nil PE.refl (subst↑²Type-prod ⊢P′) ⊢A ⊢nl′ ⊢cs₊′ Π-ok) (PE.sym P[nil]≡) ⟩∎
         nl ∎)
    , λ {h} {t} {k} {t′} ⊢h ⊢k ⊢t′ →
      let cons⇒ = ⊢⇒∷-conv-PE (⊢⇒∷-cons-prod ⊢A ⊢k ⊢h ⊢t′) List≡
          ⊢P[]≡₁ = substTypeEq (refl ⊢P′) (subsetTerm cons⇒)
          ⊢cns = ⊢∷-conv-PE (V.⊢cons′ ⊢A ⊢k ⊢h ⊢t′) V.Vec₀≡₀
          ⊢A₁′ = ⊢∷-cong ⊢A₁ A₁≡
          ⊢V₂ = V.⊢Vec′ (wkTerm (stepʷ (step id) (univ ⊢A₁′)) ⊢A) (var₁ (univ ⊢A₁′))
          ⊢σ = →⊢ˢʷ∷∙ (⊢ˢʷ∷-sgSubst (sucⱼ ⊢k)) ⊢cns
          ⊢cs₊ = subst-⊢∷ ⊢cs″ (⊢ˢʷ∷-⇑[] {k = 4} (∙ ⊢P₊₊) ⊢σ)
          ⊢P₊₊₊ = subst-⊢ ⊢P₊₊ (⊢ˢʷ∷-⇑[] {k = 3} (∙ ⊢-cong ⊢V₄ V₄≡) ⊢σ)
          ⊢cs₊′ = stabilityTerm
            (refl-∙ (⊢≡-refl-PE′ (PE.sym A₁≡) (univ ⊢A₁)) ∙
                    ⊢≡-refl-PE′ (PE.sym V₂≡) ⊢V₂ ∙
                    ⊢≡-refl-PE P[]≡₁ ⊢P₊₊₊)
            (⊢∷-conv-PE ⊢cs₊ P[]≡₂)
          prodrec⇒ : Γ ⊢ t ≡ prodʷ pₗ k t′ ∷ List l A → _
          prodrec⇒ = λ t≡ →
            let cons≡′ = ⊢≡∷-cons-cong (refl ⊢A) (refl ⊢h) (sym′ t≡)
                cons≡ = ⊢≡∷-conv-PE cons≡′ List≡
                ⊢cons≡prod = let open RTerm in
                  prodʷ pₗ (suc k) (VU.cons′ A k h t′) ≡˘⟨ ⊢≡∷-cons-prod ⊢A ⊢k ⊢h ⊢t′ ⟩⊢
                  cons l A h (prodʷ pₗ k t′)          ≡⟨ cons≡′ ⟩⊢∎
                  cons l A h t                        ∎
                ⊢P[]≡₂ = let open RType in
                  P [ 2 ][ prodʷ pₗ (var x1) (var x0) ]↑ [ suc k , VU.cons′ A k h t′ ]₁₀
                    ≡⟨ substCompEq P ⟩⊢≡
                  P [ consSubst (sgSubst (suc k)) (VU.cons′ A k h t′) ₛ•ₛ consSubst (wkSubst 2 idSubst) (prodʷ pₗ (var x1) (var x0)) ]
                    ≡⟨ subst-⊢≡ (refl ⊢P) (→⊢ˢʷ≡∷∙ ⊢L (refl-⊢ˢʷ≡∷ (⊢ˢʷ∷-idSubst ⊢Γ)) (⊢≡∷-conv-PE ⊢cons≡prod (PE.sym (subst-id (List l A))))) ⟩⊢∎
                  P [ cons l A h t ]₀ ∎
                ⊢P[]≡₃ = substTypeEq (refl ⊢P′) cons≡
                open RRed
            in
            prodrec r₁ pₗ q P (cons l A h (prodʷ pₗ k t′)) vrec
                ⇒⟨ conv (prodrec-subst′ ⊢P′ ⊢vr cons⇒) ⊢P[]≡₃ ⟩
            prodrec r₁ pₗ q P (prodʷ pₗ (suc k) (VU.cons′ A k h t′)) vrec
                ⇒⟨ conv (prodrec-β-⇒ ⊢P′ (sucⱼ ⊢k) ⊢cns ⊢vr) (trans (sym ⊢P[]≡₁) ⊢P[]≡₃) ⟩
            vrec [ suc k , VU.cons′ A k h t′ ]₁₀
                ≡⟨ VU.vecrec′-subst ⟩⇒
            VU.vecrec′ l (p₁ · pₗ) p₂ r₂ (q · pₗ) q (wk₂ A [ suc k , VU.cons′ A k h t′ ]₁₀)
              (P [ 4 ][ prodʷ pₗ (var x1) (var x0) ]↑ [ consSubst (sgSubst (suc k)) (VU.cons′ A k h t′) ⇑[ 2 ] ])
              (wk₂ nl [ suc k , VU.cons′ A k h t′ ]₁₀)
              (cs [ consSubst (consSubst (consSubst (wkSubst 6 idSubst)
                     (var x2)) (prodʷ pₗ (var x3) (var x1))) (var x0) ]
                  [ consSubst (sgSubst (suc k)) (VU.cons′ A k h t′) ⇑[ 4 ] ])
              (suc k) (VU.cons′ A k h t′)
                 ≡⟨ PE.cong₆ (VU.vecrec′ _ _ _ _ _ _) wk₂-[,] P[]≡₃ wk₂-[,] PE.refl PE.refl PE.refl ⟩⇒
            VU.vecrec′ l (p₁ · pₗ) p₂ r₂ (q · pₗ) q A
              (P [ consSubst (wkSubst 2 idSubst) (prod 𝕨 pₗ (var x1) (var x0)) ]) nl
              (cs [ consSubst (consSubst (consSubst (wkSubst 6 idSubst) (var x2)) (prod 𝕨 pₗ (var x3) (var x1))) (var x0) ]
                        [ consSubst (sgSubst (suc k)) (VU.cons′ A k h t′) ⇑[ 4 ] ])
              (suc k) (VU.cons′ A k h t′)
                ⇒*⟨ conv* (V.⊢⇒*∷-vecrec-β-cons PE.refl (subst↑²Type-prod ⊢P′) ⊢A ⊢nl′ ⊢cs₊′ ⊢k ⊢h ⊢t′ Π-ok) ⊢P[]≡₂ ⟩∎≡
            cs [ consSubst (consSubst (consSubst (wkSubst 6 idSubst) (var x2)) (prod 𝕨 pₗ (var x3) (var x1))) (var x0) ]
               [ consSubst (sgSubst (suc k)) (VU.cons′ A k h t′) ⇑[ 4 ] ]
               [ consSubst (consSubst (consSubst (sgSubst k) h) t′)
                  (VU.vecrec′ l (p₁ · pₗ) p₂ r₂ (q · pₗ) q A
                    (P [ 2 ][ prod 𝕨 pₗ (var x1) (var x0) ]↑) nl
                    (cs [ consSubst (consSubst (consSubst (wkSubst 6 idSubst) (var x2)) (prod 𝕨 pₗ (var x3) (var x1))) (var x0) ]
                        [ consSubst (sgSubst (suc k)) (VU.cons′ A k h t′) ⇑[ 4 ] ])
                    k t′) ]
                 ≡⟨ PE.cong₂ (λ x y → x [ consSubst (consSubst (consSubst (sgSubst k) h) t′) (VU.vecrec′ l (p₁ · pₗ) p₂ r₂ (q · pₗ) q A _ nl y k t′) ])
                     (substCompEq cs)
                     (PE.trans (substCompEq cs)
                       (substVar-to-subst (λ { x0 → PE.refl ; (_+1 x0) → PE.refl ; (x0 +2) → PE.refl ; (_+1 x +2) → PE.refl}) cs)) ⟩
            cs [ (consSubst (sgSubst (suc k)) (VU.cons′ A k h t′) ⇑[ 4 ]) ₛ•ₛ
                  consSubst (consSubst (consSubst (wkSubst 6 idSubst) (var x2)) (prod 𝕨 pₗ (var x3) (var x1))) (var x0) ]
               [ consSubst (consSubst (consSubst (sgSubst k) h) t′)
                  (VU.vecrec′ l (p₁ · pₗ) p₂ r₂ (q · pₗ) q A
                    (P [ consSubst (wkSubst 2 idSubst) (prod 𝕨 pₗ (var x1) (var x0)) ]) nl
                    (cs [ consSubst (consSubst (wkSubst 3 idSubst) (var x1)) (prodʷ pₗ (var x2) (var x0)) ⇑ ])
                    k t′) ]
                 ≡⟨ substCompEq cs ⟩
            cs [ consSubst (consSubst (consSubst (sgSubst k) h) t′)
                  (VU.vecrec′ l (p₁ · pₗ) p₂ r₂ (q · pₗ) q A
                    (P [ consSubst (wkSubst 2 idSubst) (prod 𝕨 pₗ (var x1) (var x0)) ]) nl
                    (cs [ consSubst (consSubst (wkSubst 3 idSubst) (var x1)) (prodʷ pₗ (var x2) (var x0)) ⇑ ])
                    k t′) ₛ•ₛ
                 ((consSubst (sgSubst (suc k)) (VU.cons′ A k h t′) ⇑[ 4 ]) ₛ•ₛ
                   consSubst (consSubst (consSubst (wkSubst 6 idSubst) (var x2)) (prod 𝕨 pₗ (var x3) (var x1))) (var x0)) ]
                 ≡⟨ substVar-to-subst (λ { x0 → PE.refl ; (_+1 x0) → PE.refl ; (x0 +2) → PE.refl ; (_+1 x +2) → PE.refl}) cs ⟩
            cs [ consSubst (consSubst (sgSubst h) (prodʷ pₗ k t′))
                  (VU.vecrec′ l (p₁ · pₗ) p₂ r₂ (q · pₗ) q A
                    (P [ consSubst (wkSubst 2 idSubst) (prod 𝕨 pₗ (var x1) (var x0)) ]) nl
                    (cs [ consSubst (consSubst (wkSubst 3 idSubst) (var x1)) (prodʷ pₗ (var x2) (var x0)) ⇑ ]) k t′) ] ∎
      in  (λ t⇒* → let open RRed in
            listrec l r₁ r₂ p₁ p₂ q A P nl cs (cons l A h t)                ≡⟨⟩⇒
            prodrec r₁ pₗ q P (cons l A h t) vrec                            ⇒*⟨ prodrec-subst* ⊢P′ (⊢⇒*∷-conv-PE (⊢⇒*∷-cons-subst ⊢A ⊢h t⇒*) List≡) ⊢vr ⟩
            prodrec r₁ pₗ q P (cons l A h (prodʷ pₗ k t′)) vrec              ⇒*⟨ prodrec⇒ (subset*Term t⇒*) ⟩∎
            cs [ consSubst (consSubst (sgSubst h) (prod 𝕨 pₗ k t′))
                   (VU.vecrec′ l (p₁ · pₗ) p₂ r₂ (q · pₗ) q A
                     (P [ 2 ][ prod 𝕨 pₗ (var x1) (var x0) ]↑) nl
                     (cs [ consSubst (consSubst (wkSubst 3 idSubst) (var x1))
                             (prod 𝕨 pₗ (var x2) (var x0)) ⇑ ])
                     k t′) ] ∎)
        , (λ t≡ →
            let _ , _ , ⊢p = syntacticEqTerm t≡
                ⊢p′ = ⊢∷-conv-PE ⊢p (PE.sym (wk1-sgSubst _ _))
                ⊢wkP = ⊢-cong (wkType (liftʷ (step id) (wkType (stepʷ id (univ ⊢A)) ⊢L)) ⊢P) $ begin
                  wk (lift (step id)) P                        ≡⟨ wk≡subst _ P ⟩
                  P [ toSubst (lift (step id)) ]               ≡⟨ substVar-to-subst (λ { x0 → PE.refl ; (_+1 x) → PE.refl}) P ⟩
                  P [ consSubst (wkSubst 2 idSubst) (var x0) ] ∎
                ⊢const≡ = ⊢≡∷-cons-cong (refl ⊢A) (refl ⊢h) t≡
                ⊢P[]≡ = λ u → let open RType in
                  P [ 3 ][ cons l (wk[ 3 ]′ A) (var x2) (var x1) ]↑ [ consSubst (consSubst (sgSubst h) (prodʷ pₗ k t′)) u ]
                    ≡⟨ substCompEq P ⟩⊢≡
                  P [ consSubst (consSubst (sgSubst h) (prodʷ pₗ k t′)) u ₛ•ₛ consSubst (wkSubst 3 idSubst) (cons l (wk[ 3 ]′ A) (var x2) (var x1)) ]
                    ≡⟨ substVar-to-subst (λ { x0 → cons-subst ; (_+1 x) → PE.refl}) P ⟩⊢≡
                  P [ cons l (wk[ 3 ]′ A [ consSubst (consSubst (sgSubst h) (prodʷ pₗ k t′)) u ]) h (prodʷ pₗ k t′) ]₀
                    ≡⟨ PE.cong (λ x → P [ cons l x _ _ ]₀)
                        (PE.trans (step-consSubst A) (PE.trans (step-consSubst A) (wk1-sgSubst _ _))) ⟩⊢≡
                  P [ cons l A h (prodʷ pₗ k t′) ]₀
                    ≡˘⟨ substTypeEq (refl ⊢P) ⊢const≡ ⟩⊢∎
                  P [ cons l A h t ]₀ ∎
                ⊢P[]≡′ = let open RType in
                  P [ t ]₀                                                                               ≡⟨ substTypeEq (refl ⊢P) t≡ ⟩⊢∎≡
                  P [ prodʷ pₗ k t′ ]₀                                                                   ≡⟨ substVar-to-subst (λ { x0 → PE.refl ; (_+1 x) → PE.refl}) P ⟩
                  P [ consSubst (sgSubst h) (prodʷ pₗ k t′) ₛ•ₛ consSubst (wkSubst 2 idSubst) (var x0) ] ≡˘⟨ substCompEq P ⟩
                  P [ 2 ][ var x0 ]↑ [ h , prodʷ pₗ k t′ ]₁₀                                             ∎
                open RTerm
                lr≡ =
                   listrec l r₁ r₂ p₁ p₂ q A P nl cs t
                       ≡⟨⟩⊢
                   prodrec r₁ pₗ q P t vrec
                       ≡⟨ prodrec-cong′ (refl ⊢P′) (⊢≡∷-conv-PE t≡ List≡) (refl ⊢vr) ⟩⊢
                   prodrec r₁ pₗ q P (prodʷ pₗ k t′) vrec
                       ≡⟨ conv (prodrec-β-≡ ⊢P′ ⊢k (⊢∷-conv-PE ⊢t′ V.Vec₀≡₀) ⊢vr)
                            (sym (substTypeEq (refl ⊢P) t≡)) ⟩⊢∎≡
                   vrec [ k , t′ ]₁₀
                       ≡⟨ VU.vecrec′-subst ⟩
                   VU.vecrec′ l (p₁ · pₗ) p₂ r₂ (q · pₗ) q (wk₂ A [ k , t′ ]₁₀)
                     (P [ 4 ][ prod 𝕨 pₗ (var x1) (var x0) ]↑ [ consSubst (sgSubst k) t′ ⇑[ 2 ] ])
                     (wk₂ nl [ k , t′ ]₁₀)
                     (cs [ consSubst (consSubst (consSubst (wkSubst 6 idSubst) (var x2)) (prod 𝕨 pₗ (var x3) (var x1))) (var x0) ]
                         [ consSubst (sgSubst k) t′ ⇑[ 4 ] ])
                     k t′
                       ≡⟨ PE.cong₄ (λ x y z w → VU.vecrec′ l (p₁ · pₗ) p₂ r₂ (q · pₗ) q x y z w k t′)
                           wk₂-[,] P[]≡₃ wk₂-[,] (substCompEq cs) ⟩
                   VU.vecrec′ l (p₁ · pₗ) p₂ r₂ (q · pₗ) q A (P [ 2 ][ prod 𝕨 pₗ (var x1) (var x0) ]↑) nl
                     (cs [ (consSubst (sgSubst k) t′ ⇑[ 4 ]) ₛ•ₛ
                           consSubst (consSubst (consSubst (wkSubst 6 idSubst) (var x2)) (prod 𝕨 pₗ (var x3) (var x1))) (var x0) ])
                     k t′
                       ≡⟨ PE.cong (λ x → VU.vecrec′ l (p₁ · pₗ) p₂ r₂ (q · pₗ) q A _ nl x k t′)
                            (substVar-to-subst (λ { x0 → PE.refl ; (_+1 x0) → PE.refl ; (x0 +2) → PE.refl ; (_+1 x +2) → PE.refl}) cs) ⟩
                   VU.vecrec′ l (p₁ · pₗ) p₂ r₂ (q · pₗ) q A
                     (P [ 2 ][ prod 𝕨 pₗ (var x1) (var x0) ]↑) nl
                     (cs [ consSubst (consSubst (wkSubst 3 idSubst) (var x1)) (prod 𝕨 pₗ (var x2) (var x0)) ⇑ ])
                     k t′ ∎

            in
            listrec l r₁ r₂ p₁ p₂ q A P nl cs (cons l A h t)                ≡⟨⟩⊢
            prodrec r₁ pₗ q P (cons l A h t) vrec                            ≡⟨ prodrec-cong′ (refl ⊢P′) (⊢≡∷-conv-PE ⊢const≡ List≡) (refl ⊢vr) ⟩⊢
            prodrec r₁ pₗ q P (cons l A h (prodʷ pₗ k t′)) vrec              ⇒*⟨ prodrec⇒ t≡ ⟩⊢
            cs [ consSubst (consSubst (sgSubst h) (prod 𝕨 pₗ k t′))
                   (VU.vecrec′ l (p₁ · pₗ) p₂ r₂ (q · pₗ) q A
                     (P [ 2 ][ prod 𝕨 pₗ (var x1) (var x0) ]↑) nl
                     (cs [ consSubst (consSubst (wkSubst 3 idSubst) (var x1))
                             (prod 𝕨 pₗ (var x2) (var x0)) ⇑ ])
                     k t′) ]                                                  ≡⟨ conv (subst-⊢≡∷ (refl ⊢cs) (→⊢ˢʷ≡∷∙ ⊢wkP (refl-⊢ˢʷ≡∷ (→⊢ˢʷ∷∙ (⊢ˢʷ∷-sgSubst ⊢h) ⊢p′))
                                                                                  (conv (sym′ lr≡) ⊢P[]≡′))) (⊢P[]≡ _) ⟩⊢∎
            cs [ consSubst (consSubst (sgSubst h) (prod 𝕨 pₗ k t′))
                   (listrec l r₁ r₂ p₁ p₂ q A P nl cs t) ] ∎)

opaque

  -- A typing rule for listrec

  ⊢∷-listrec :
    Γ ⊢ A ∷ U l →
    Γ »∙ List l A ⊢ P →
    Γ ⊢ nl ∷ P [ nil l A ]₀ →
    Γ »∙ A »∙ wk1 (List l A) »∙ P [ var x0 ]↑² ⊢ cs ∷ P [ 3 ][ cons l (wk[ 3 ]′ A) (var x2) (var x1) ]↑ →
    Γ ⊢ xs ∷ List l A →
    Π-allowed r₂ q →
    Γ ⊢ listrec l r₁ r₂ p₁ p₂ q A P nl cs xs ∷ P [ xs ]₀
  ⊢∷-listrec ⊢A ⊢P ⊢nl ⊢cs ⊢xs Π-ok =
    listrec-lemma ⊢A ⊢P ⊢nl ⊢cs Π-ok .proj₁ ⊢xs

opaque

  -- β-reduction for listrec for empty lists.

  ⊢⇒*∷-listrec-β-nil :
    Γ ⊢ A ∷ U l →
    Γ »∙ List l A ⊢ P →
    Γ ⊢ nl ∷ P [ nil l A ]₀ →
    Γ »∙ A »∙ wk1 (List l A) »∙ P [ var x0 ]↑² ⊢ cs ∷ P [ 3 ][ cons l (wk[ 3 ]′ A) (var x2) (var x1) ]↑ →
    Π-allowed r₂ q →
    Γ ⊢ listrec l r₁ r₂ p₁ p₂ q A P nl cs (nil l A) ⇒* nl ∷ P [ nil l A ]₀
  ⊢⇒*∷-listrec-β-nil ⊢A ⊢P ⊢nl ⊢cs Π-ok =
    listrec-lemma ⊢A ⊢P ⊢nl ⊢cs Π-ok .proj₂ .proj₁

opaque

  -- β-reduction for listrec for non-empty lists.
  -- Note that we require that the tail reduces to a pair
  -- See also ⊢≡∷-listrec-β-cons for a definitional equality that is
  -- perhaps closer to what one might expect for β-reduction.


  ⊢⇒*∷-listrec-β-cons :
    Γ ⊢ A ∷ U l →
    Γ »∙ List l A ⊢ P →
    Γ ⊢ nl ∷ P [ nil l A ]₀ →
    Γ »∙ A »∙ wk1 (List l A) »∙ P [ var x0 ]↑² ⊢ cs ∷ P [ 3 ][ cons l (wk[ 3 ]′ A) (var x2) (var x1) ]↑ →
    Γ ⊢ h ∷ A →
    Γ ⊢ k ∷ ℕ →
    Γ ⊢ t′ ∷ VU.Vec′ l A k →
    Γ ⊢ t ⇒* prodʷ pₗ k t′ ∷ List l A →
    Π-allowed r₂ q →
    Γ ⊢ listrec l r₁ r₂ p₁ p₂ q A P nl cs (cons l A h t) ⇒*
        cs [ consSubst (consSubst (sgSubst h) (prodʷ pₗ k t′))
               (VU.vecrec′ l (p₁ · pₗ) p₂ r₂ (q · pₗ) q A (P [ 2 ][ prodʷ pₗ (var x1) (var x0) ]↑) nl
                 (cs [ consSubst (consSubst (wkSubst 3 idSubst) (var x1)) (prodʷ pₗ (var x2) (var x0)) ⇑ ])
               k t′) ] ∷ P [ cons l A h t ]₀
  ⊢⇒*∷-listrec-β-cons ⊢A ⊢P ⊢nl ⊢cs ⊢h ⊢k ⊢t′ t⇒* Π-ok =
    listrec-lemma ⊢A ⊢P ⊢nl ⊢cs Π-ok .proj₂ .proj₂ ⊢h ⊢k ⊢t′ .proj₁ t⇒*

opaque

  -- A definitional equality for listrec corresponding to β-reduction for non-empty lists.

  ⊢≡∷-listrec-β-cons :
    Γ ⊢ A ∷ U l →
    Γ »∙ List l A ⊢ P →
    Γ ⊢ nl ∷ P [ nil l A ]₀ →
    Γ »∙ A »∙ wk1 (List l A) »∙ P [ var x0 ]↑² ⊢ cs ∷ P [ 3 ][ cons l (wk[ 3 ]′ A) (var x2) (var x1) ]↑ →
    Γ ⊢ h ∷ A →
    Γ ⊢ k ∷ ℕ →
    Γ ⊢ t′ ∷ VU.Vec′ l A k →
    Γ ⊢ t ≡ prodʷ pₗ k t′ ∷ List l A →
    Π-allowed r₂ q →
    Γ ⊢ listrec l r₁ r₂ p₁ p₂ q A P nl cs (cons l A h t) ≡
        cs [ consSubst (consSubst (sgSubst h) (prodʷ pₗ k t′)) (listrec l r₁ r₂ p₁ p₂ q A P nl cs t) ] ∷
        P [ cons l A h t ]₀
  ⊢≡∷-listrec-β-cons ⊢A ⊢P ⊢nl ⊢cs ⊢h ⊢k ⊢t′ t≡ Π-ok =
    listrec-lemma ⊢A ⊢P ⊢nl ⊢cs Π-ok .proj₂ .proj₂ ⊢h ⊢k ⊢t′ .proj₂ t≡
