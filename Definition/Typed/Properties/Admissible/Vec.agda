------------------------------------------------------------------------
-- Typing, equality and reduction rules related to Vec
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
import Definition.Untyped
import Definition.Untyped.Vec
import Graded.Modality
import Graded.Mode

module Definition.Typed.Properties.Admissible.Vec
  {a b} {M : Set a} {Mode : Set b}
  (open Graded.Modality M)
  (open Definition.Untyped M)
  {𝕄 : Modality}
  (open Graded.Mode Mode 𝕄)
  (𝐌 : IsMode)
  (s : Strength)
  (p : M)
  (open Definition.Untyped.Vec 𝕄 𝐌 s p)
  (open Modality 𝕄)
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  -- It is assumed that a certain unit type is allowed.
  (Unit-ok : Unit-allowed s)
  -- It is assumed that a certain Σ-type is allowed
  (Σ-ok : Σ-allowed s p 𝟘)
  where

open IsMode 𝐌

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Reduction R
open import Definition.Typed.Reasoning.Term R
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
  A A′ P k k′ h h′ t t′ nl cs xs : Term _
  Γ : Cons _ _
  p₁ p₂ p₃ q r q₁ q₂ q₃ q₄ : M
  l : Universe-level

opaque

  Vec₀≡ : Vec′ l (wk[ n ]′ A) k PE.≡ Vec′ l (wk1 A) (var x0) [ consSubst (wkSubst n idSubst) k ]
  Vec₀≡ {l} {n} {A} {k} = begin
    Vec′ l (wk[ n ]′ A) k                                       ≡⟨ PE.cong (λ x → Vec′ l x k) lemma ⟩
    Vec′ l (wk1 A [ consSubst (wkSubst n idSubst) k ]) k        ≡˘⟨ Vec′-subst ⟩
    Vec′ l (wk1 A) (var x0) [ consSubst (wkSubst n idSubst) k ] ∎
    where
    lemma : wk[ n ]′ A PE.≡ wk1 A [ consSubst (wkSubst n idSubst) k ]
    lemma = begin
      wk[ n ]′ A                                ≡˘⟨ wk[]≡wk[]′ ⟩
      wk[ n ] A                                 ≡⟨ wk[]≡[] n ⟩
      A [ wkSubst n idSubst ]                   ≡˘⟨ wk1-tail A ⟩
      wk1 A [ consSubst (wkSubst n idSubst) k ] ∎

opaque

  Vec₀≡₀ : Vec′ l A k PE.≡ Vec′ l (wk1 A) (var x0) [ k ]₀
  Vec₀≡₀ {l} {A} {k} = begin
    Vec′ l A k                     ≡˘⟨ PE.cong (λ x → Vec′ l x k) (wk-id A) ⟩
    Vec′ l (wk id A) k             ≡⟨ Vec₀≡ ⟩
    Vec′ l (wk1 A) (var x0) [ k ]₀ ∎

opaque

  ⊢Vec-tail :
    Γ ⊢ A ∷ U l →
    Γ »∙ ℕ »∙ U l ⊢ Σ⟨ s ⟩ p , 𝟘 ▷ wk₂ A ▹ var x1 ∷ U l
  ⊢Vec-tail {Γ} {A} {l} ⊢A =
    let ⊢Γ = wfTerm ⊢A
        ⊢wk₂A = wkTerm (stepʷ (step id) (Uⱼ (∙ ℕⱼ ⊢Γ))) ⊢A
    in  PE.subst ((Γ »∙ ℕ »∙ U l) ⊢ Σ⟨ s ⟩ p , 𝟘 ▷ wk₂ A ▹ var x1 ∷_)
          (PE.cong U (⊔-idem l))
          (ΠΣⱼ ⊢wk₂A (var (∙ univ ⊢wk₂A) (there here)) Σ-ok)

opaque
  unfolding Vec′

  ⊢Vec′∷U :
    Γ ⊢ A ∷ U l →
    Γ ⊢ k ∷ ℕ →
    Γ ⊢ Vec′ l A k ∷ U l
  ⊢Vec′∷U {Γ} {A} {l} ⊢A ⊢k =
    let ⊢Γ = wfTerm ⊢k
    in  natrecⱼ
          (Unitⱼ ⊢Γ Unit-ok)
          (⊢Vec-tail ⊢A)
          ⊢k

opaque

  ⊢Vec′ :
    Γ ⊢ A ∷ U l →
    Γ ⊢ k ∷ ℕ →
    Γ ⊢ Vec′ l A k
  ⊢Vec′ ⊢A ⊢k =
    univ (⊢Vec′∷U ⊢A ⊢k)

private opaque

  ⊢λVec′ :
    ⊢ Γ →
    Π-allowed 𝟙 q →
    Γ »∙ U l ⊢ lam 𝟙 (Vec′ l (var x1) (var x0)) ∷ (Π 𝟙 , q ▷ ℕ ▹ U l)
  ⊢λVec′ ⊢Γ Π-ok =
    let ⊢Γ′ = ∙ ℕⱼ (∙ Uⱼ ⊢Γ)
    in  lamⱼ (Uⱼ ⊢Γ′)
          (⊢Vec′∷U (var ⊢Γ′ (there here)) (var ⊢Γ′ here))
          Π-ok

opaque
  unfolding Vec

  ⊢Vec :
    ⊢ Γ →
    Π-allowed 𝟙 q →
    Π-allowed 𝟙 r →
    Γ ⊢ Vec l ∷ Π 𝟙 , q ▷ U l ▹ (Π 𝟙 , r ▷ ℕ ▹ U l)
  ⊢Vec ⊢Γ Π-ok₁ Π-ok₂ =
    lamⱼ (ΠΣⱼ (Uⱼ (∙ ℕⱼ (∙ Uⱼ ⊢Γ))) Π-ok₂)
      (⊢λVec′ ⊢Γ Π-ok₂)
      Π-ok₁

opaque

  ⊢Vec∘A∘k∷U :
    Γ ⊢ A ∷ U l →
    Γ ⊢ k ∷ ℕ →
    Π-allowed 𝟙 q →
    Γ ⊢ Vec l ∘⟨ 𝟙 ⟩ A ∘⟨ 𝟙 ⟩ k ∷ U l
  ⊢Vec∘A∘k∷U ⊢A ⊢k Π-ok =
    (⊢Vec (wfTerm ⊢A) Π-ok Π-ok ∘ⱼ ⊢A) ∘ⱼ ⊢k

opaque

  ⊢Vec∘A∘k :
    Γ ⊢ A ∷ U l →
    Γ ⊢ k ∷ ℕ →
    Π-allowed 𝟙 q →
    Γ ⊢ Vec l ∘⟨ 𝟙 ⟩ A ∘⟨ 𝟙 ⟩ k
  ⊢Vec∘A∘k ⊢A ⊢k Π-ok = univ (⊢Vec∘A∘k∷U ⊢A ⊢k Π-ok)

opaque
  unfolding Vec′

  ⊢Vec′-zero⇒Unit∷U :
    Γ ⊢ A ∷ U l →
    Γ ⊢ Vec′ l A zero ⇒ Unit s l ∷ U l
  ⊢Vec′-zero⇒Unit∷U ⊢A =
    let ⊢Γ = wfTerm ⊢A
    in  natrec-zero (Unitⱼ ⊢Γ Unit-ok) (⊢Vec-tail ⊢A)

opaque

  ⊢Vec′-zero⇒Unit :
    Γ ⊢ A ∷ U l →
    Γ ⊢ Vec′ l A zero ⇒ Unit s l
  ⊢Vec′-zero⇒Unit = univ ∘→ ⊢Vec′-zero⇒Unit∷U

opaque

  ⊢Vec′-zero≡Unit∷U :
    Γ ⊢ A ∷ U l →
    Γ ⊢ Vec′ l A zero ≡ Unit s l ∷ U l
  ⊢Vec′-zero≡Unit∷U = subsetTerm ∘→ ⊢Vec′-zero⇒Unit∷U

opaque

  ⊢Vec′-zero≡Unit :
    Γ ⊢ A ∷ U l →
    Γ ⊢ Vec′ l A zero ≡ Unit s l
  ⊢Vec′-zero≡Unit = subset ∘→ ⊢Vec′-zero⇒Unit

opaque
  unfolding Vec′

  ⊢Vec′-suc⇒Σ∷U :
    Γ ⊢ A ∷ U l →
    Γ ⊢ k ∷ ℕ →
    Γ ⊢ Vec′ l A (suc k) ⇒ Σ⟨ s ⟩ p , 𝟘 ▷ A ▹ wk1 (Vec′ l A k) ∷ U l
  ⊢Vec′-suc⇒Σ∷U {Γ} {A} {l} {k} ⊢A ⊢k =
    let ⊢Γ = wfTerm ⊢k
        ⊢Unit = Unitⱼ ⊢Γ Unit-ok
        ⊢wk₂A = wkTerm (stepʷ (step id) (Uⱼ (∙ ℕⱼ ⊢Γ))) ⊢A
        ⊢Σ = ΠΣⱼ ⊢wk₂A (var (∙ univ ⊢wk₂A) (there here)) Σ-ok
        ⊢Σ′ = PE.subst (Γ »∙ ℕ »∙ U l ⊢ Σ⟨ s ⟩ p , 𝟘 ▷ wk₂ A ▹ var x1 ∷_)
               (PE.cong U (⊔-idem l)) ⊢Σ
    in  flip (PE.subst (Γ ⊢ Vec′ l A (suc k) ⇒_∷ U l))
               (natrec-suc ⊢Unit ⊢Σ′ ⊢k) $ begin
         (Σ⟨ s ⟩ p , 𝟘 ▷ wk₂ A ▹ var x1) [ k , Vec′ l A k ]₁₀
           ≡⟨⟩
         Σ⟨ s ⟩ p , 𝟘 ▷ wk₂ A [ k , Vec′ l A k ]₁₀ ▹ wk1 (Vec′ l A k)
           ≡⟨ PE.cong (λ x → Σ⟨ s ⟩ p , 𝟘 ▷ x ▹ wk1 (Vec′ l A k)) wk₂-[,] ⟩
         Σ⟨ s ⟩ p , 𝟘 ▷ A ▹ wk1 (Vec′ l A k) ∎

opaque

  ⊢Vec′-suc⇒Σ :
    Γ ⊢ A ∷ U l →
    Γ ⊢ k ∷ ℕ →
    Γ ⊢ Vec′ l A (suc k) ⇒ Σ⟨ s ⟩ p , 𝟘 ▷ A ▹ wk1 (Vec′ l A k)
  ⊢Vec′-suc⇒Σ ⊢A ⊢k = univ (⊢Vec′-suc⇒Σ∷U ⊢A ⊢k)

opaque

  ⊢Vec′-suc≡Σ∷U :
    Γ ⊢ A ∷ U l →
    Γ ⊢ k ∷ ℕ →
    Γ ⊢ Vec′ l A (suc k) ≡ Σ⟨ s ⟩ p , 𝟘 ▷ A ▹ wk1 (Vec′ l A k) ∷ U l
  ⊢Vec′-suc≡Σ∷U ⊢A ⊢k = subsetTerm (⊢Vec′-suc⇒Σ∷U ⊢A ⊢k)

opaque

  ⊢Vec′-suc≡Σ :
    Γ ⊢ A ∷ U l →
    Γ ⊢ k ∷ ℕ →
    Γ ⊢ Vec′ l A (suc k) ≡ Σ⟨ s ⟩ p , 𝟘 ▷ A ▹ wk1 (Vec′ l A k)
  ⊢Vec′-suc≡Σ ⊢A ⊢k = subset (⊢Vec′-suc⇒Σ ⊢A ⊢k)

opaque
  unfolding Vec

  ⊢Vec⇒*Vec′∷U :
    Γ ⊢ A ∷ U l →
    Γ ⊢ k ∷ ℕ →
    Π-allowed 𝟙 q →
    Γ ⊢ Vec l ∘⟨ 𝟙 ⟩ A ∘⟨ 𝟙 ⟩ k ⇒* Vec′ l A k ∷ U l
  ⊢Vec⇒*Vec′∷U {A} {l} {k} ⊢A ⊢k Π-ok =
    let ⊢Γ = wfTerm ⊢k
        ⊢x0 = var (∙ ℕⱼ ⊢Γ) here
        ⊢wk1A = wkTerm (stepʷ id (ℕⱼ ⊢Γ)) ⊢A
    in  Vec l ∘⟨ 𝟙 ⟩ A ∘⟨ 𝟙 ⟩ k
          ≡⟨⟩⇒
        lam 𝟙 (lam 𝟙 (Vec′ l (var x1) (var x0))) ∘⟨ 𝟙 ⟩ A ∘⟨ 𝟙 ⟩ k
          ⇒⟨ app-subst (β-red-⇒ (⊢λVec′ ⊢Γ Π-ok) ⊢A Π-ok) ⊢k ⟩
        (lam 𝟙 (Vec′ l (var x1) (var x0)) [ A ]₀) ∘⟨ 𝟙 ⟩ k
          ≡⟨ PE.cong (λ x → lam 𝟙 x ∘⟨ 𝟙 ⟩ k) Vec′-subst ⟩⇒
        lam 𝟙 (Vec′ l (wk1 A) (var x0)) ∘⟨ 𝟙 ⟩ k
          ⇒⟨ β-red-⇒ (⊢Vec′∷U ⊢wk1A ⊢x0) ⊢k Π-ok ⟩∎≡
        Vec′ l (wk1 A) (var x0) [ k ]₀
          ≡˘⟨ Vec₀≡₀ ⟩
        Vec′ l A k ∎
opaque

  ⊢Vec⇒*Vec′ :
    Γ ⊢ A ∷ U l →
    Γ ⊢ k ∷ ℕ →
    Π-allowed 𝟙 q →
    Γ ⊢ Vec l ∘⟨ 𝟙 ⟩ A ∘⟨ 𝟙 ⟩ k ⇒* Vec′ l A k
  ⊢Vec⇒*Vec′ ⊢A ⊢k Π-ok =
    univ* (⊢Vec⇒*Vec′∷U ⊢A ⊢k Π-ok)

opaque

  ⊢Vec≡Vec′∷U :
    Γ ⊢ A ∷ U l →
    Γ ⊢ k ∷ ℕ →
    Π-allowed 𝟙 q →
    Γ ⊢ Vec l ∘⟨ 𝟙 ⟩ A ∘⟨ 𝟙 ⟩ k ≡ Vec′ l A k ∷ U l
  ⊢Vec≡Vec′∷U ⊢A ⊢k Π-ok =
    subset*Term (⊢Vec⇒*Vec′∷U ⊢A ⊢k Π-ok)

opaque

  ⊢Vec≡Vec′ :
    Γ ⊢ A ∷ U l →
    Γ ⊢ k ∷ ℕ →
    Π-allowed 𝟙 q →
    Γ ⊢ Vec l ∘⟨ 𝟙 ⟩ A ∘⟨ 𝟙 ⟩ k ≡ Vec′ l A k
  ⊢Vec≡Vec′ ⊢A ⊢k Π-ok = univ (⊢Vec≡Vec′∷U ⊢A ⊢k Π-ok)

opaque
  unfolding Vec′

  ⊢∷Vec′-cong :
    Γ ⊢ A ≡ A′ ∷ U l →
    Γ ⊢ k ≡ k′ ∷ ℕ →
    Γ ⊢ Vec′ l A k ≡ Vec′ l A′ k′ ∷ U l
  ⊢∷Vec′-cong A≡A′ k≡k′ =
    let ⊢Γ = wfEqTerm A≡A′
        ⊢A₂ = wkType (stepʷ (step id) (Uⱼ (∙ ℕⱼ ⊢Γ))) (univ (syntacticEqTerm A≡A′ .proj₂ .proj₁))
    in  natrec-cong (refl (Uⱼ (∙ ℕⱼ ⊢Γ))) (refl (Unitⱼ ⊢Γ Unit-ok))
          (⊢≡∷-conv-PE
            (ΠΣ-cong (wkEqTerm (stepʷ (step id) (Uⱼ (∙ ℕⱼ ⊢Γ))) A≡A′)
              (refl (var₁ ⊢A₂)) Σ-ok)
            (PE.cong U (⊔-idem _)))
          k≡k′

opaque

  ⊢Vec′-cong :
    Γ ⊢ A ≡ A′ ∷ U l →
    Γ ⊢ k ≡ k′ ∷ ℕ →
    Γ ⊢ Vec′ l A k ≡ Vec′ l A′ k′
  ⊢Vec′-cong A≡A′ k≡k′ = univ (⊢∷Vec′-cong A≡A′ k≡k′)

opaque
  unfolding nil′

  ⊢nil′ :
    Γ ⊢ A ∷ U l →
    Γ ⊢ nil′ l A ∷ Vec′ l A zero
  ⊢nil′ ⊢A =
    let ⊢Γ = wfTerm ⊢A
    in  conv (starⱼ ⊢Γ Unit-ok) (sym (⊢Vec′-zero≡Unit ⊢A))

opaque
  unfolding nil

  ⊢nil :
    ⊢ Γ →
    Π-allowed 𝟘 q →
    Π-allowed 𝟙 r →
    Γ ⊢ nil l ∷ Π 𝟘 , q ▷ U l ▹ (Vec l ∘⟨ 𝟙 ⟩ var x0 ∘⟨ 𝟙 ⟩ zero)
  ⊢nil ⊢Γ Π-ok₁ Π-ok₂ =
    let ⊢Γ′ = ∙ Uⱼ ⊢Γ
        ⊢x0 = var ⊢Γ′ here
        ⊢zero = zeroⱼ ⊢Γ′
    in  lamⱼ (⊢Vec∘A∘k ⊢x0 ⊢zero Π-ok₂)
          (conv (⊢nil′ (var ⊢Γ′ here))
            (sym (⊢Vec≡Vec′ ⊢x0 ⊢zero Π-ok₂)))
          Π-ok₁

opaque
  unfolding cons′

  ⊢cons′ :
    Γ ⊢ A ∷ U l →
    Γ ⊢ k ∷ ℕ →
    Γ ⊢ h ∷ A →
    Γ ⊢ t ∷ Vec′ l A k →
    Γ ⊢ cons′ A k h t ∷ Vec′ l A (suc k)
  ⊢cons′ ⊢A ⊢k ⊢h ⊢t =
    let ⊢t′ = PE.subst (_ ⊢ _ ∷_) (PE.sym (wk1-sgSubst _ _)) ⊢t
        ⊢Vec = wkType (stepʷ id (univ ⊢A)) (⊢Vec′ ⊢A ⊢k)
    in  conv (prodⱼ ⊢Vec ⊢h ⊢t′ Σ-ok)
          (sym (⊢Vec′-suc≡Σ ⊢A ⊢k))

opaque
  unfolding cons

  ⊢cons :
    ⊢ Γ →
    Π-allowed 𝟘 q₁ →
    Π-allowed 𝟘 q₂ →
    Π-allowed 𝟙 q₃ →
    Π-allowed 𝟙 q₄ →
    Γ ⊢ cons ∷ Π 𝟘 , q₁ ▷ U l ▹
               (Π 𝟘 , q₂ ▷ ℕ ▹
                (Π 𝟙 , q₃ ▷ var x1 ▹
                 (Π 𝟙 , q₄ ▷ Vec′ l (var x2) (var x1) ▹ Vec′ l (var x3) (suc (var x2)))))
  ⊢cons ⊢Γ Π-ok₁ Π-ok₂ Π-ok₃ Π-ok₄ =
    let ⊢Γ″ = ∙ univ (var (∙ ℕⱼ (∙ Uⱼ ⊢Γ)) (there here))
        ⊢Vec₀ = ⊢Vec′
                 (var ⊢Γ″ (there (there here)))
                 (var ⊢Γ″ (there here))
        ⊢Γ′ = ∙ ⊢Vec₀
        ⊢x0 = var ⊢Γ′ here
        ⊢x0′ = PE.subst (_ »∙ _ »∙ _ »∙ _ »∙ Vec′ _ _ _ ⊢ var x0 ∷_)
                 Vec′-wk ⊢x0
        ⊢x1 = var ⊢Γ′ (there here)
        ⊢x2 = var ⊢Γ′ (there (there here))
        ⊢x3 = var ⊢Γ′ (there (there (there here)))
        ⊢Vec = ⊢Vec′ ⊢x3 (sucⱼ ⊢x2)
        ⊢Π₁ = ΠΣⱼ ⊢Vec Π-ok₄
        ⊢Π₂ = ΠΣⱼ ⊢Π₁ Π-ok₃
        ⊢Π₃ = ΠΣⱼ ⊢Π₂ Π-ok₂
    in  lamⱼ ⊢Π₃
         (lamⱼ ⊢Π₂
           (lamⱼ ⊢Π₁
             (lamⱼ ⊢Vec
               (⊢cons′ ⊢x3 ⊢x2 ⊢x1 ⊢x0′) Π-ok₄)
             Π-ok₃)
           Π-ok₂)
         Π-ok₁

opaque
  unfolding cons′

  ⊢≡∷-cons′-cong :
    Γ ⊢ A ∷ U l →
    Γ ⊢ k ∷ ℕ →
    Γ ⊢ h ≡ h′ ∷ A →
    Γ ⊢ t ≡ t′ ∷ Vec′ l A k →
    Γ ⊢ cons′ A k h t ≡ cons′ A′ k′ h′ t′ ∷ Vec′ l A (suc k)
  ⊢≡∷-cons′-cong ⊢A ⊢k h≡h′ t≡t′ =
    conv (prod-cong (wkType (stepʷ id (univ ⊢A)) (⊢Vec′ ⊢A ⊢k)) h≡h′ (⊢≡∷-conv-PE t≡t′ (PE.sym (wk1-sgSubst _ _))) Σ-ok)
      (sym (⊢Vec′-suc≡Σ ⊢A ⊢k))

private opaque
  unfolding vecrec-nil

  ⊢∷-vecrec-nil′ :
    s PE.≡ 𝕨 →
    Γ »∙ ℕ »∙ Vec′ l (wk1 A) (var x0) ⊢ P →
    Γ ⊢ A ∷ U l →
    Γ ⊢ nl ∷ P [ zero , nil′ l A ]₁₀ →
    Π-allowed r q →
    Γ ⊢ vecrec-nil l r q P nl ∷ Π r , q ▷ Vec′ l A zero ▹ (P [ sgSubst zero ⇑ ]) ×
    Γ ⊢ vecrec-nil l r q P nl ∘⟨ r ⟩ nil′ l A ⇒* nl ∷ P [ zero , nil′ l A ]₁₀
  ⊢∷-vecrec-nil′ {Γ} {l} {A} {P} {nl} {r} {q} PE.refl ⊢P ⊢A ⊢nl Π-ok =
    let ⊢Γ = wfTerm ⊢nl
        ⊢zero = zeroⱼ ⊢Γ
        ⊢Vec₀ = ⊢Vec′ ⊢A ⊢zero
        ⊢Vec₀′ = PE.subst (λ x → Γ ⊢ x) Vec₀≡₀ ⊢Vec₀
        ⊢Γ′ = ∙ ⊢Vec₀
        ⊢Γ′≡ = refl-∙ (⊢Vec′-zero≡Unit ⊢A)
        ⊢wk1A = wkTerm (stepʷ id ⊢Vec₀) ⊢A
        ⊢Vec₊ = ⊢Vec′ ⊢wk1A (zeroⱼ ⊢Γ′)
        ⊢Vec₊′ = PE.subst (λ x → Γ »∙ Vec′ _ _ _ ⊢ x)
                  Vec₀≡ ⊢Vec₊
        ⊢Vec₀≡Unit = wkEq (stepʷ id ⊢Vec₀) (⊢Vec′-zero≡Unit ⊢A)
        ⊢Vec₀≡Unit′ = PE.subst (Γ »∙ Vec′ _ _ _ ⊢_≡ Unitʷ _)
                       (PE.trans Vec′-wk Vec₀≡) ⊢Vec₀≡Unit
        ⊢P₀ = subst-⊢ ⊢P (⊢ˢʷ∷-⇑ ⊢Vec₀′ (⊢ˢʷ∷-sgSubst ⊢zero))
        ⊢P₀′ = PE.subst (λ x → Γ »∙ x ⊢ _) (PE.sym Vec₀≡₀) ⊢P₀
        ⊢P₀″ = stability (refl-∙ (⊢Vec′-zero≡Unit ⊢A))
                (PE.subst (λ x → _ ⊢ x) P₀≡′ ⊢P₀′)
        ⊢P₊ = subst-⊢ ⊢P (⊢ˢʷ∷-⇑ ⊢Vec₊′ (→⊢ˢʷ∷∙
                (⊢ˢʷ∷-wk1Subst ⊢Vec₀ (⊢ˢʷ∷-idSubst ⊢Γ))
                (zeroⱼ ⊢Γ′)))
        ⊢P₊′ = stability (refl-∙ ⊢Vec₀≡Unit′) ⊢P₊
        ⊢P₊″ = stability (⊢Γ′≡ ∙ refl (Unitⱼ ⊢Γ′ Unit-ok)) ⊢P₊′
        ⊢x0 = var ⊢Γ′ here
        ⊢x0′ = conv ⊢x0 ⊢Vec₀≡Unit
        ⊢x0″ = stabilityTerm ⊢Γ′≡ ⊢x0′
        ⊢nl′ = ⊢∷-conv-PE ⊢nl (PE.sym P₊≡′)
        ⊢wk1nl = wkTerm (stepʷ id ⊢Vec₀) ⊢nl
        ⊢wk1nl′ = ⊢∷-conv-PE ⊢wk1nl P₊≡
        ⊢wk1nl″ = stabilityTerm ⊢Γ′≡ ⊢wk1nl′
        ⊢unitrec = ⊢∷-conv-PE (unitrecⱼ ⊢P₊′ ⊢x0′ ⊢wk1nl′ Unit-ok) P₀≡
     in    lamⱼ ⊢P₀′ ⊢unitrec Π-ok
         , (vecrec-nil l r q P nl ∘⟨ r ⟩ nil′ l A
            ≡⟨ PE.cong (_ ∘⟨ _ ⟩_) nil′≡star ⟩⇒
          lam r (unitrec l r q _ (var x0) (wk1 nl)) ∘⟨ r ⟩ starʷ l
            ⇒⟨ ⊢⇒∷-conv-PE (β-red-⇒ (unitrecⱼ′ ⊢P₊″ ⊢x0″ ⊢wk1nl″) (starⱼ ⊢Γ Unit-ok) Π-ok) P₊≡″ ⟩
          unitrec l r q _ (starʷ l) (wk1 nl [ starʷ l ]₀)
            ≡⟨ PE.cong (unitrec l _ _ _ _) (wk1-sgSubst _ _) ⟩⇒
          unitrec l r q _ (starʷ l) nl
            ⇒⟨ ⊢⇒∷-conv-PE (unitrec-β-⇒ ⊢P₀″ ⊢nl′) P₊≡′ ⟩∎
          nl ∎)
    where
    P₀≡ : P [ consSubst (wk1Subst idSubst) zero ⇑ ] [ var x0 ]₀ PE.≡ P [ sgSubst zero ⇑ ]
    P₀≡ = begin
      P [ consSubst (wk1Subst idSubst) zero ⇑ ] [ var x0 ]₀
        ≡⟨ substCompEq P ⟩
      P [ sgSubst (var x0) ₛ•ₛ (consSubst (wk1Subst idSubst) zero ⇑) ]
        ≡⟨ substVar-to-subst lemma P ⟩
      P [ sgSubst zero ⇑ ] ∎
      where
      lemma : ∀ {n} (x : Fin (2+ n)) →
              (sgSubst (var x0) ₛ•ₛ (consSubst (wk1Subst idSubst) zero ⇑)) x PE.≡ (sgSubst zero ⇑) x
      lemma x0 = PE.refl
      lemma (x0 +1) = PE.refl
      lemma (x +2) = PE.refl
    P₀≡′ : P [ sgSubst zero ⇑ ] PE.≡ P [ consSubst (wk1Subst idSubst) zero ⇑ ] [ sgSubst (starʷ l) ⇑ ]
    P₀≡′ = begin
      P [ sgSubst zero ⇑ ]
        ≡⟨ substVar-to-subst lemma P ⟩
      P [ (sgSubst (starʷ l) ⇑) ₛ•ₛ (consSubst (wk1Subst idSubst) zero ⇑) ]
        ≡˘⟨ substCompEq P ⟩
      P [ consSubst (wk1Subst idSubst) zero ⇑ ] [ sgSubst (starʷ l) ⇑ ] ∎
      where
      lemma : ∀ {n : Nat} (x : Fin (2+ n)) →
              (sgSubst zero ⇑) x PE.≡ ((sgSubst (starʷ l) ⇑) ₛ•ₛ (consSubst (wk1Subst idSubst) zero ⇑)) x
      lemma x0 = PE.refl
      lemma (x0 +1) = PE.refl
      lemma (x +2) = PE.refl

    P₊≡ : wk1 (P [ zero , nil′ l A ]₁₀) PE.≡ (P [ consSubst (wk1Subst idSubst) zero ⇑ ]) [ star 𝕨 l ]₀
    P₊≡ = begin
      wk1 (P [ zero , nil′ l A ]₁₀)
        ≡⟨ wk-subst P ⟩
      P [ step id •ₛ consSubst (sgSubst zero) (nil′ l A) ]
        ≡⟨ substVar-to-subst lemma P ⟩
      P [ sgSubst (starʷ l) ₛ•ₛ (consSubst (wk1Subst idSubst) zero ⇑) ]
        ≡˘⟨ substCompEq P ⟩
      (P [ consSubst (wk1Subst idSubst) zero ⇑ ]) [ starʷ l ]₀ ∎
      where
      lemma : ∀ x → (step id •ₛ consSubst (sgSubst zero) (nil′ l A)) x PE.≡
                 (sgSubst (star 𝕨 l) ₛ•ₛ (consSubst (wk1Subst idSubst) zero ⇑)) x
      lemma x0 = PE.cong wk1 nil′≡star
      lemma (x0 +1) = PE.refl
      lemma (x +2) = PE.refl
    P₊≡′ : ((P [ consSubst (wk1Subst idSubst) zero ⇑ ]) [ sgSubst (starʷ l) ⇑ ]) [ starʷ l ]₀ PE.≡ P [ zero , nil′ l A ]₁₀
    P₊≡′ = begin
      ((P [ consSubst (wk1Subst idSubst) zero ⇑ ]) [ sgSubst (starʷ l) ⇑ ]) [ starʷ l ]₀
        ≡⟨ PE.cong (_[ starʷ l ]₀) (substCompEq P) ⟩
      P [ (sgSubst (starʷ l) ⇑) ₛ•ₛ (consSubst (wk1Subst idSubst) zero ⇑) ] [ starʷ l ]₀
        ≡⟨ substCompEq P ⟩
      P [ sgSubst (starʷ l) ₛ•ₛ ((sgSubst (starʷ l) ⇑) ₛ•ₛ (consSubst (wk1Subst idSubst) zero ⇑)) ]
        ≡⟨ substVar-to-subst lemma P ⟩
      P [ zero , nil′ l A ]₁₀ ∎
      where
      lemma : ∀ x → (sgSubst (starʷ l) ₛ•ₛ ((sgSubst (starʷ l) ⇑) ₛ•ₛ (consSubst (wk1Subst idSubst) zero ⇑))) x PE.≡
                    consSubst (sgSubst zero) (nil′ l A) x
      lemma x0 = PE.sym nil′≡star
      lemma (x0 +1) = PE.refl
      lemma (x +2) = PE.refl
    P₊≡″ : ((P [ consSubst (wk1Subst idSubst) zero ⇑ ]) [ var x0 ]₀) [ starʷ l ]₀ PE.≡ P [ zero , nil′ l A ]₁₀
    P₊≡″ = begin
      ((P [ consSubst (wk1Subst idSubst) zero ⇑ ]) [ sgSubst (var x0) ]) [ starʷ l ]₀
        ≡⟨ PE.cong (_[ starʷ l ]₀) (substCompEq P) ⟩
      P [ sgSubst (var x0) ₛ•ₛ (consSubst (wk1Subst idSubst) zero ⇑) ] [ starʷ l ]₀
        ≡⟨ substCompEq P ⟩
      P [ sgSubst (starʷ l) ₛ•ₛ (sgSubst (var x0) ₛ•ₛ (consSubst (wk1Subst idSubst) zero ⇑)) ]
        ≡⟨ substVar-to-subst lemma P ⟩
      P [ zero , nil′ l A ]₁₀ ∎
      where
      lemma : ∀ x → (sgSubst (starʷ l) ₛ•ₛ (sgSubst (var x0) ₛ•ₛ (consSubst (wk1Subst idSubst) zero ⇑))) x PE.≡
                    consSubst (sgSubst zero) (nil′ l A) x
      lemma x0 = PE.sym nil′≡star
      lemma (x0 +1) = PE.refl
      lemma (x +2) = PE.refl

opaque

  ⊢∷-vecrec-nil :
    s PE.≡ 𝕨 →
    Γ »∙ ℕ »∙ Vec′ l (wk1 A) (var x0) ⊢ P →
    Γ ⊢ A ∷ U l →
    Γ ⊢ nl ∷ P [ zero , nil′ l A ]₁₀ →
    Π-allowed r q →
    Γ ⊢ vecrec-nil l r q P nl ∷ Π r , q ▷ Vec′ l A zero ▹ (P [ sgSubst zero ⇑ ])
  ⊢∷-vecrec-nil s≡𝕨 ⊢P ⊢A ⊢nl Π-ok =
    ⊢∷-vecrec-nil′ s≡𝕨 ⊢P ⊢A ⊢nl Π-ok .proj₁

opaque

  ⊢⇒*∷-vecrec-nil :
    s PE.≡ 𝕨 →
    Γ »∙ ℕ »∙ Vec′ l (wk1 A) (var x0) ⊢ P →
    Γ ⊢ A ∷ U l →
    Γ ⊢ nl ∷ P [ zero , nil′ l A ]₁₀ →
    Π-allowed r q →
    Γ ⊢ vecrec-nil l r q P nl ∘⟨ r ⟩ nil′ l A ⇒* nl ∷ P [ zero , nil′ l A ]₁₀
  ⊢⇒*∷-vecrec-nil s≡𝕨 ⊢P ⊢A ⊢nl Π-ok =
    ⊢∷-vecrec-nil′ s≡𝕨 ⊢P ⊢A ⊢nl Π-ok .proj₂

private opaque
  unfolding vecrec-cons

  ⊢∷-vecrec-cons′ :
    s PE.≡ 𝕨 →
    Γ »∙ ℕ »∙ Vec′ l (wk1 A) (var x0) ⊢ P →
    Γ ⊢ A ∷ U l →
    Γ »∙ ℕ »∙ wk1 A »∙ Vec′ l (wk₂ A) (var x1) »∙ P [ wk1Subst idSubst ⇑ ] ⊢ cs ∷
      (P [ consSubst (consSubst (wkSubst 4 idSubst) (suc (var x3))) (cons′ (wk[ 4 ]′ A) (var x3) (var x2) (var x1)) ]) →
    Π-allowed r q →
    (Γ »∙ ℕ »∙ Π r , q ▷ Vec′ l (wk1 A) (var x0) ▹ P
         ⊢ vecrec-cons r q P cs
         ∷ Π r , q ▷ Vec′ l (wk₂ A) (suc (var x1)) ▹ (P [ consSubst (consSubst (wkSubst 3 idSubst) (suc (var x2))) (var x0) ])) ×
    (∀ {k x xs IH} →
      Γ ⊢ k ∷ ℕ →
      Γ ⊢ x ∷ A →
      Γ ⊢ xs ∷ Vec′ l A k →
      Γ ⊢ IH ∷ Π r , q ▷ Vec′ l A k ▹ (P [ sgSubst k ⇑ ]) →
      Γ ⊢ (vecrec-cons r q P cs [ k , IH ]₁₀) ∘⟨ r ⟩ cons′ A k x xs ⇒*
         cs [ consSubst (consSubst (consSubst (sgSubst k) x) xs) (IH ∘⟨ r ⟩ xs) ] ∷
         P [ suc k , cons′ A k x xs ]₁₀)
  ⊢∷-vecrec-cons′ {l} {A} {P} {cs} {r} {q} PE.refl ⊢P ⊢A ⊢cs Π-ok =
    let ⊢Γ = wfTerm ⊢A
        ⊢Π = ΠΣⱼ ⊢P Π-ok
        ⊢ΓℕΠ = ∙ ⊢Π
        ⊢wk₂A = wkTerm (stepʷ (step id) ⊢Π) ⊢A
        ⊢x1 = var ⊢ΓℕΠ (there here)
        ⊢Vec₂ = ⊢Vec′ ⊢wk₂A (sucⱼ ⊢x1)
        ⊢ΓℕΠV = ∙ ⊢Vec₂
        ⊢Vec₊≡Σ = wkEq (stepʷ id ⊢Vec₂) (⊢Vec′-suc≡Σ ⊢wk₂A ⊢x1)
        ⊢Vec₊≡Σ′ = ⊢≡-congʳ ⊢Vec₊≡Σ lemma₁
        ⊢wk₃A = wkTerm (stepʷ (step (step id)) ⊢Vec₂) ⊢A
        ⊢wk₃A′ = ⊢∷-cong ⊢wk₃A (PE.sym (wk-comp _ _ _))
        ⊢Vec₃ = ⊢Vec′ ⊢wk₃A (sucⱼ (var ⊢ΓℕΠV (there (there here))))
        ⊢Vec₃′ = ⊢-cong ⊢Vec₃ lemma₂
        ⊢P₊ = subst-⊢ ⊢P (⊢ˢʷ∷-⇑ ⊢Vec₃′ (→⊢ˢʷ∷∙ (⊢ˢʷ∷-wkSubst ⊢ΓℕΠV (⊢ˢʷ∷-idSubst ⊢Γ))
                (sucⱼ (var ⊢ΓℕΠV (there (there here))))))
        ⊢P₊′ = stability (refl-∙ ⊢Vec₊≡Σ′) ⊢P₊
        ⊢x0 = var ⊢ΓℕΠV here
        ⊢x0′ = conv ⊢x0 ⊢Vec₊≡Σ
        ⊢x0″ = ⊢∷-conv-PE ⊢x0 lemma₁
        ⊢ΓℕΠVA = ∙ univ ⊢wk₃A′
        ⊢wk₄A = wkTerm (stepʷ id (univ ⊢wk₃A′)) ⊢wk₃A
        ⊢Vec₄ = ⊢Vec′ ⊢wk₄A (var ⊢ΓℕΠVA (there (there (there here))))
        ⊢Vec₄′ = ⊢-cong ⊢Vec₄ lemma₃
        ⊢ΓℕΠVAV = ∙ ⊢Vec₄′

        ⊢cs₊ = subst-⊢∷ ⊢cs (→⊢ˢʷ∷∙ (→⊢ˢʷ∷∙ (→⊢ˢʷ∷∙ (→⊢ˢʷ∷∙ (⊢ˢʷ∷-wkSubst ⊢ΓℕΠVAV (⊢ˢʷ∷-idSubst ⊢Γ))
                 (var ⊢ΓℕΠVAV (there (there (there (there here))))))
                 (⊢∷-conv-PE (var ⊢ΓℕΠVAV (there here)) lemma₈))
                 (⊢∷-conv-PE (var ⊢ΓℕΠVAV here) lemma₄))
                 (⊢∷-conv-PE (⊢∷-conv-PE (var ⊢ΓℕΠVAV (there (there (there here)))) lemma₆
                                ∘ⱼ var ⊢ΓℕΠVAV here) lemma₇))
        ⊢cs₊′ = ⊢∷-conv-PE ⊢cs₊ lemma₉
        ⊢prodrec = ⊢∷-conv-PE (prodrecⱼ ⊢P₊′ ⊢x0′ ⊢cs₊′ Σ-ok) lemma₁₀
        ⊢P₃ = subst-⊢ ⊢P (→⊢ˢʷ∷∙ (→⊢ˢʷ∷∙ (⊢ˢʷ∷-wkSubst ⊢ΓℕΠV (⊢ˢʷ∷-idSubst ⊢Γ))
                (sucⱼ (var ⊢ΓℕΠV (there (there here))))) ⊢x0″)
    in    lamⱼ ⊢P₃ ⊢prodrec Π-ok
        , λ {k} {x} {xs} {IH} ⊢k ⊢x ⊢xs ⊢IH →
          let x:xs = cons′ A k x xs
              ⊢x:xs = ⊢cons′ ⊢A ⊢k ⊢x ⊢xs
              ⊢x:xs′ = conv ⊢x:xs (⊢Vec′-suc≡Σ ⊢A ⊢k)
              ⊢xs′ = ⊢∷-conv-PE ⊢xs (PE.sym (wk1-sgSubst _ x))
              ⊢wk1A′ = wkTerm (stepʷ id (ℕⱼ ⊢Γ)) ⊢A
              ⊢Vec₀ = ⊢Vec′ ⊢A ⊢k
              ⊢wk1Vec₀ = wkType (stepʷ id (univ ⊢A)) ⊢Vec₀
              ⊢Vec₀′ = ΠΣⱼ ⊢wk1Vec₀ Σ-ok
              ⊢wk1A = wkTerm (stepʷ id ⊢Vec₀′) ⊢A
              ⊢wk1k = wkTerm (stepʷ id ⊢Vec₀′) ⊢k
              ⊢wk1suck = sucⱼ ⊢wk1k
              ⊢Vec₁ = ⊢Vec′ ⊢wk1A ⊢wk1suck
              ⊢Vec₁′ = ⊢-cong ⊢Vec₁ lemma₁₃
              ⊢ΓV = ∙ ⊢Vec₀′
              ⊢wk₂A′ = wkTerm (stepʷ (step id) (univ ⊢wk1A′)) ⊢A
              ⊢ΓℕA = ∙ univ ⊢wk1A′
              ⊢Vec₂ = ⊢Vec′ ⊢wk₂A′ (var ⊢ΓℕA (there here))
              ⊢wk₂k = wkTerm (stepʷ (step id) (univ ⊢wk1A)) ⊢k
              ⊢wk₂A″ = wkTerm (stepʷ (step id) (univ ⊢wk1A)) ⊢A
              ⊢Vec₂′ = ⊢Vec′ ⊢wk₂A″ ⊢wk₂k
              ⊢ΓℕAV = ∙ ⊢Vec₂
              ⊢Vec₁≡Σ = ⊢Vec′-suc≡Σ ⊢wk1A ⊢wk1k
              ⊢Vec₁≡Σ′ = ⊢≡-cong ⊢Vec₁≡Σ lemma₅ (PE.cong (Σʷ p , 𝟘 ▷ _ ▹_) lemma₁₆)

              ⊢IH₃ = (wkTerm (stepʷ (step (step id)) ⊢Vec₂′) ⊢IH) ∘ⱼ
                       ⊢∷-conv-PE (var (∙ ⊢Vec₂′) here)
                         (PE.trans (PE.cong wk1 (PE.sym Vec′-wk)) (wk-comp _ _ (Vec′ l A k)))
              ⊢IH₃′ = PE.subst₃ (λ x y z → _ »∙ Σʷ p , 𝟘 ▷ A ▹ wk1 (Vec′ l A k) »∙ x »∙ y ⊢ _ ∷ z)
                       (PE.sym lemma₁₇) lemma₁₈ lemma₁₉ ⊢IH₃

              ⊢P₂ = subst-⊢ {σ = consSubst (wk1Subst idSubst) (wk1 (suc k)) ⇑} ⊢P
                      (⊢ˢʷ∷-⇑ ⊢Vec₁′ (→⊢ˢʷ∷∙ (⊢ˢʷ∷-wkSubst ⊢ΓV (⊢ˢʷ∷-idSubst ⊢Γ)) ⊢wk1suck))
              ⊢P₂′ = stability (refl-∙ ⊢Vec₁≡Σ′) ⊢P₂
              ⊢cs₃ = subst-⊢∷ {σ = consSubst (consSubst (wk1Subst idSubst) (wk1 k) ⇑[ 2 ]) (wk[ 3 ]′ IH ∘⟨ r ⟩ var x0)} ⊢cs
                       (→⊢ˢʷ∷∙ (⊢ˢʷ∷-⇑[] {k = 2} ⊢ΓℕAV (→⊢ˢʷ∷∙ (⊢ˢʷ∷-wkSubst ⊢ΓV (⊢ˢʷ∷-idSubst ⊢Γ)) ⊢wk1k)) ⊢IH₃′)
              ⊢cs₃′ = PE.subst₃ (λ x y z → _ »∙ Σʷ p , 𝟘 ▷ A ▹ wk1 (Vec′ l A k) »∙ x »∙ y ⊢ cs [ _ ] ∷ z)
                        lemma₁₇ (PE.sym (PE.trans (wk-comp _ _ _) (PE.trans Vec′-wk lemma₁₈))) lemma₂₀ ⊢cs₃

              ⊢Vec₀″ = ⊢-cong (⊢Vec′ ⊢A (sucⱼ ⊢k))
                         (PE.sym (PE.trans Vec′-subst (PE.cong (λ x → Vec′ l x _) (wk1-sgSubst A _))))

              ⊢Vec₁″ = wkType (stepʷ id (univ ⊢A)) ⊢Vec₀
              ⊢IH₂ = wkTerm (stepʷ (step id) ⊢Vec₁″) ⊢IH ∘ⱼ
                       ⊢∷-conv-PE (var (∙ ⊢Vec₁″) here)
                         (wk-comp _ _ _)
              ⊢IH₂′ = PE.subst₃ (λ x y z → _ »∙ x »∙ y ⊢ _ ∷ z) (PE.sym (wk1-sgSubst _ _))
                        lemma₂₄ lemma₂₅ ⊢IH₂


              ⊢P₁ = subst-⊢ {σ = sgSubst (suc k) ⇑} ⊢P (⊢ˢʷ∷-⇑ ⊢Vec₀″ (⊢ˢʷ∷-sgSubst (sucⱼ ⊢k)))
              ⊢Vec₀≡Σ = ⊢Vec′-suc≡Σ ⊢A ⊢k
              ⊢Vec₀≡Σ′ = ⊢≡-cong ⊢Vec₀≡Σ Vec₀≡₀ PE.refl
              ⊢P₁′ = stability (refl-∙ ⊢Vec₀≡Σ′) ⊢P₁
              ⊢cs₂ = subst-⊢∷ {σ = consSubst (sgSubst k ⇑[ 2 ]) (wk₂ IH ∘⟨ r ⟩ var x0)} ⊢cs
                       (→⊢ˢʷ∷∙ (⊢ˢʷ∷-⇑[] {k = 2} ⊢ΓℕAV (⊢ˢʷ∷-sgSubst ⊢k)) ⊢IH₂′)
              ⊢cs₂′ = PE.subst₃ (λ x y z → _ »∙ x »∙ y ⊢ _ ∷ z) (wk1-sgSubst _ _)
                        (PE.sym lemma₂₄) lemma₂₆ ⊢cs₂

              d = (vecrec-cons r q P cs [ k , IH ]₁₀) ∘⟨ r ⟩ cons′ A k x xs
                      ≡⟨⟩⇒
                  (lam r $ prodrec r p q
                    (P [ consSubst (wkSubst 3 idSubst) (suc (var x2)) ⇑ ] [ consSubst (sgSubst k) IH ⇑[ 2 ] ])
                    (var x0)
                    (cs [ consSubst (consSubst (consSubst (consSubst (wkSubst 5 idSubst) (var x4)) (var x1)) (var x0)) (var x3 ∘⟨ r ⟩ var x0) ]
                        [ consSubst (sgSubst k) IH ⇑[ 3 ] ]))
                    ∘⟨ r ⟩ x:xs
                      ≡⟨ PE.cong₂ (λ x y → lam r (prodrec r p q x (var x0) y) ∘⟨ r ⟩ x:xs) lemma₁₁ lemma₁₂ ⟩⇒
                  (lam r $ prodrec r p q (P [ consSubst (wk1Subst idSubst) (wk1 (suc k)) ⇑ ]) (var x0)
                    (cs [ consSubst (consSubst (wk1Subst idSubst) (wk1 k) ⇑[ 2 ]) (wk[ 3 ]′ IH ∘⟨ r ⟩ var x0) ])) ∘⟨ r ⟩ x:xs
                      ⇒⟨ ⊢⇒∷-conv-PE (β-red-⇒ (prodrecⱼ′ ⊢P₂′ (var ⊢ΓV here) ⊢cs₃′) ⊢x:xs′ Π-ok) lemma₂₂ ⟩
                  prodrec r p q (P [ consSubst (wk1Subst idSubst) (wk1 (suc k)) ⇑ ] [ sgSubst x:xs ⇑ ]) x:xs
                    (cs [ consSubst (consSubst (wk1Subst idSubst) (wk1 k) ⇑[ 2 ]) (wk[ 3 ]′ IH ∘⟨ r ⟩ var x0) ] [ sgSubst x:xs ⇑[ 2 ] ])
                      ≡⟨ PE.cong₃ (prodrec r p q) lemma₁₄ cons′≡prod lemma₁₅ ⟩⇒
                  prodrec r p q (P [ sgSubst (suc k) ⇑ ]) (prodʷ p x xs) (cs [ consSubst (sgSubst k ⇑[ 2 ]) (wk₂ IH ∘⟨ r ⟩ var x0) ])
                      ⇒⟨  prodrec-β-⇒ ⊢P₁′ ⊢x ⊢xs′ ⊢cs₂′ ⟩∎≡
                  cs [ consSubst (sgSubst k ⇑[ 2 ]) (wk₂ IH ∘⟨ r ⟩ var x0) ] [ x , xs ]₁₀
                      ≡⟨ lemma₂₁ ⟩
                  cs [ consSubst (consSubst (consSubst (sgSubst k) x) xs) (IH ∘⟨ r ⟩ xs) ] ∎
          in  ⊢⇒*∷-conv-PE d lemma₂₃
    where
    open Tools.Reasoning.PropositionalEquality
    lemma₀ : Vec′ l (wk1 (wk₂ A)) (suc (var x2)) PE.≡ Vec′ l (wk1 A) (var x0) [ consSubst (wkSubst 3 idSubst) (suc (var x2)) ]
    lemma₀ = begin
      Vec′ l (wk1 (wk₂ A)) (suc (var x2))                                            ≡⟨ PE.cong (λ x → Vec′ l x _) lemma ⟩
      Vec′ l (wk1 A [ consSubst (wkSubst 3 idSubst) (suc (var x2)) ]) (suc (var x2)) ≡˘⟨ Vec′-subst ⟩
      Vec′ l (wk1 A) (var x0) [ consSubst (wkSubst 3 idSubst) (suc (var x2)) ]       ∎
      where
      lemma : wk1 (wk₂ A) PE.≡ wk1 A [ consSubst (wkSubst 3 idSubst) (suc (var x2)) ]
      lemma = begin
        wk1 (wk₂ A)                                            ≡˘⟨ PE.cong wk1 wk[]≡wk[]′ ⟩
        wk[ 3 ] A                                              ≡⟨ wk[]≡[] 3 ⟩
        A [ wkSubst 3 idSubst ]                                ≡˘⟨ wk1-tail A ⟩
        wk1 A [ consSubst (wkSubst 3 idSubst) (suc (var x2)) ] ∎
    lemma₁ : wk1 (Vec′ l (wk₂ A) (suc (var x1))) PE.≡ Vec′ l (wk1 A) (var x0) [ consSubst (wkSubst 3 idSubst) (suc (var x2)) ]
    lemma₁ = begin
      wk1 (Vec′ l (wk₂ A) (suc (var x1)))                                            ≡⟨ Vec′-wk ⟩
      Vec′ l (wk1 (wk₂ A)) (suc (var x2))                                            ≡⟨ lemma₀ ⟩
      Vec′ l (wk1 A) (var x0) [ consSubst (wkSubst 3 idSubst) (suc (var x2)) ]       ∎
    lemma₂ : Vec′ l (wk[ 3 ]′ A) (suc (var x2)) PE.≡ Vec′ l (wk1 A) (var x0) [ consSubst (wkSubst 3 idSubst) (suc (var x2)) ]
    lemma₂ = begin
      Vec′ l (wk[ 3 ]′ A) (suc (var x2))                                       ≡˘⟨ PE.cong (λ x → Vec′ l x _) (wk-comp _ _ A) ⟩
      Vec′ l (wk1 (wk₂ A)) (suc (var x2))                                      ≡⟨ lemma₀ ⟩
      Vec′ l (wk1 A) (var x0) [ consSubst (wkSubst 3 idSubst) (suc (var x2)) ] ∎
    lemma₃ : Vec′ l (wk1 (wk[ 3 ]′ A)) (var x3) PE.≡ wk (lift (step id)) (wk1 (Vec′ l (wk₂ A) (var x1)))
    lemma₃ = begin
      Vec′ l (wk1 (wk[ 3 ]′ A)) (var x3)                  ≡⟨ PE.cong (λ x → Vec′ l x _) (wk-comp _ _ A) ⟩
      Vec′ l (wk[ 4 ]′ A) (var x3)                        ≡˘⟨ PE.cong (λ x → Vec′ l x _) (wk-comp _ _ A) ⟩
      Vec′ l (wk₂ (wk₂ A)) (var x3)                       ≡˘⟨ Vec′-wk ⟩
      wk₂ (Vec′ l (wk₂ A) (var x1))                       ≡˘⟨ wk-comp _ _ _ ⟩
      wk (lift (step id)) (wk1 (Vec′ l (wk₂ A) (var x1))) ∎
    lemma′ : (t : Term n) → wk[ 3 ]′ t PE.≡ wk1 (wk (lift (step id)) (wk1 t))
    lemma′ t = begin
        wk[ 3 ]′ t                         ≡˘⟨ wk-comp _ _ _ ⟩
        wk (step (lift (step id))) (wk1 t) ≡˘⟨ wk-comp _ _ _ ⟩
        wk1 (wk (lift (step id)) (wk1 t))  ∎
    lemma₄ : wk1 (wk (lift (step id)) (wk1 (Vec′ l (wk₂ A) (var x1)))) PE.≡
             Vec′ l (wk₂ A) (var x1) [ consSubst (consSubst (wkSubst 5 idSubst) (var x4)) (var x1) ]
    lemma₄ = begin
      wk1 (wk (lift (step id)) (wk1 (Vec′ l (wk₂ A) (var x1))))                                ≡˘⟨ lemma′ _ ⟩
      wk[ 3 ]′ (Vec′ l (wk₂ A) (var x1))                                                       ≡⟨ Vec′-wk ⟩
      Vec′ l (wk[ 3 ]′ (wk₂ A)) (var x4)                                                       ≡⟨ PE.cong (λ x → Vec′ l x _) (wk-comp _ _ A) ⟩
      Vec′ l (wk[ 5 ]′ A) (var x4)                                                             ≡˘⟨ PE.cong (λ x → Vec′ l x _) wk[]≡wk[]′ ⟩
      Vec′ l (wk[ 5 ] A) (var x4)                                                              ≡⟨ PE.cong (λ x → Vec′ l x _) (wk[]≡[] 5) ⟩
      Vec′ l (A [ wkSubst 5 idSubst ]) (var x4)                                                ≡˘⟨ PE.cong (λ x → Vec′ l x _) (wk₂-tail A) ⟩
      Vec′ l (wk₂ A [ consSubst (consSubst (wkSubst 5 idSubst) (var x4)) (var x1) ]) (var x4)  ≡˘⟨ Vec′-subst ⟩
      Vec′ l (wk₂ A) (var x1) [ consSubst (consSubst (wkSubst 5 idSubst) (var x4)) (var x1) ]  ∎
    lemma₅ : Vec′ l (wk1 A) (suc (wk1 k)) PE.≡ Vec′ l (wk1 A) (var x0) [ consSubst (wk1Subst idSubst) (wk1 (suc k)) ]
    lemma₅ {k} = begin
      Vec′ l (wk1 A) (suc (wk1 k))                                                ≡⟨ PE.cong (λ x → Vec′ l x _) (wk≡subst _ A) ⟩
      Vec′ l (A [ wk1Subst idSubst ]) (suc (wk1 k))                               ≡˘⟨ PE.cong (λ x → Vec′ l x _) (wk1-tail A)  ⟩
      Vec′ l (wk1 A [ consSubst (wk1Subst idSubst) (wk1 (suc k)) ]) (suc (wk1 k)) ≡˘⟨ Vec′-subst ⟩
      Vec′ l (wk1 A) (var x0) [ consSubst (wk1Subst idSubst) (wk1 (suc k)) ]      ∎
    lemma₆ : wk[ 4 ] (Π r , q ▷ Vec′ l (wk1 A) (var x0) ▹ P) PE.≡
             Π r , q ▷ wk1 (wk (lift (step id)) (wk1 (Vec′ l (wk₂ A) (var x1)))) ▹ wk (lift (stepn id 4)) P
    lemma₆ = begin
      wk[ 4 ] (Π r , q ▷ Vec′ l (wk1 A) (var x0) ▹ P)                                                ≡⟨ wk[]≡wk[]′ ⟩
      wk[ 4 ]′ (Π r , q ▷ Vec′ l (wk1 A) (var x0) ▹ P)                                               ≡⟨⟩
      Π r , q ▷ wk[ 4 ]′ (Vec′ l (wk1 A) (var x0)) ▹ wk (lift (stepn id 4)) P                        ≡⟨ PE.cong (Π r , q ▷_▹ _) lemma ⟩
      Π r , q ▷ wk1 (wk (lift (step id)) (wk1 (Vec′ l (wk₂ A) (var x1)))) ▹ wk (lift (stepn id 4)) P ∎
      where
      lemma : wk[ 4 ]′ (Vec′ l (wk1 A) (var x0)) PE.≡ wk1 (wk (lift (step id)) (wk1 (Vec′ l (wk₂ A) (var x1))))
      lemma = begin
        wk[ 4 ]′ (Vec′ l (wk1 A) (var x0)) ≡˘⟨ wk-comp _ _ _ ⟩
        wk[ 3 ]′ (wk1 (Vec′ l (wk1 A) (var x0))) ≡⟨ PE.cong wk[ 3 ]′ Vec′-wk ⟩
        wk[ 3 ]′ (Vec′ l (wk2 A) (var x1)) ≡⟨ PE.cong (λ x → wk[ 3 ]′ (Vec′ l x _)) wk[]≡wk[]′ ⟩
        wk[ 3 ]′ (Vec′ l (wk₂ A) (var x1)) ≡⟨ lemma′ _ ⟩
        wk1 (wk (lift (step id)) (wk1 (Vec′ l (wk₂ A) (var x1)))) ∎
    lemma₇ : wk (lift (stepn id 4)) P [ var x0 ]₀ PE.≡
             P [ wk1Subst idSubst ⇑ ] [ consSubst (consSubst (consSubst (wkSubst 5 idSubst) (var x4)) (var x1)) (var x0) ]
    lemma₇ = begin
      wk (lift (stepn id 4)) P [ var x0 ]₀                                                                            ≡⟨ subst-wk P ⟩
      P [ sgSubst (var x0) ₛ• lift (stepn id 4) ]                                                                     ≡⟨ substVar-to-subst lemma P ⟩
      P [ consSubst (consSubst (consSubst (wkSubst 5 idSubst) (var x4)) (var x1)) (var x0) ₛ•ₛ (wk1Subst idSubst ⇑) ] ≡˘⟨ substCompEq P ⟩
      P [ wk1Subst idSubst ⇑ ] [ consSubst (consSubst (consSubst (wkSubst 5 idSubst) (var x4)) (var x1)) (var x0) ]   ∎
      where
      lemma : (x : Fin (2+ n)) → (sgSubst (var x0) ₛ• lift (stepn id 4)) x PE.≡
              (consSubst (consSubst (consSubst (wkSubst 5 idSubst) (var x4)) (var x1)) (var x0) ₛ•ₛ (wk1Subst idSubst ⇑)) x
      lemma x0 = PE.refl
      lemma (x0 +1) = PE.refl
      lemma (x +2) = PE.refl
    lemma₈ : wk[ 3 ] (wk₂ A) PE.≡ wk1 A [ consSubst (wkSubst 5 idSubst) (var x4) ]
    lemma₈ = begin
      wk[ 3 ] (wk₂ A)                                  ≡⟨ wk[]≡wk[]′ ⟩
      wk[ 3 ]′ (wk₂ A)                                 ≡⟨ wk-comp _ _ A ⟩
      wk[ 5 ]′ A                                       ≡˘⟨ wk[]≡wk[]′ ⟩
      wk[ 5 ] A                                        ≡⟨ wk[]≡[] 5 ⟩
      A [ wkSubst 5 idSubst ]                          ≡˘⟨ wk1-tail A ⟩
      wk1 A [ consSubst (wkSubst 5 idSubst) (var x4) ] ∎
    lemma₉ : P [ consSubst (consSubst (wkSubst 4 idSubst) (suc (var x3))) (cons′ (wk[ 4 ]′ A) (var x3) (var x2) (var x1)) ]
               [ consSubst (consSubst (consSubst (consSubst (wkSubst 5 idSubst) (var x4)) (var x1)) (var x0)) (var x3 ∘⟨ r ⟩ var x0) ] PE.≡
             P [ consSubst (wkSubst 3 idSubst) (suc (var x2)) ⇑ ]
               [ prodʷ p (var x1) (var x0) ]↑²
    lemma₉ = begin
      P [ consSubst (consSubst (wkSubst 4 idSubst) (suc (var x3))) (cons′ (wk[ 4 ]′ A) (var x3) (var x2) (var x1)) ]
        [ consSubst (consSubst (consSubst (consSubst (wkSubst 5 idSubst) (var x4)) (var x1)) (var x0)) (var x3 ∘⟨ r ⟩ var x0) ]
          ≡⟨ substCompEq P ⟩
      P [ consSubst (consSubst (consSubst (consSubst (wkSubst 5 idSubst) (var x4)) (var x1)) (var x0)) (var x3 ∘⟨ r ⟩ var x0) ₛ•ₛ
          consSubst (consSubst (wkSubst 4 idSubst) (suc (var x3))) (cons′ (wk[ 4 ]′ A) (var x3) (var x2) (var x1)) ]
          ≡⟨ substVar-to-subst lemma P ⟩
      P [ consSubst (wk1Subst (wk1Subst idSubst)) (prodʷ p (var x1) (var x0)) ₛ•ₛ
          (consSubst (wkSubst 3 idSubst) (suc (var x2)) ⇑) ]
          ≡˘⟨ substCompEq P ⟩
      P [ consSubst (wkSubst 3 idSubst) (suc (var x2)) ⇑ ]
        [ prodʷ p (var x1) (var x0) ]↑² ∎
      where
      lemma : ∀ x →
        (consSubst (consSubst (consSubst (consSubst (wkSubst 5 idSubst) (var x4)) (var x1)) (var x0)) (var x3 ∘⟨ r ⟩ var x0) ₛ•ₛ
         consSubst (consSubst (wkSubst 4 idSubst) (suc (var x3))) (cons′ (wk[ 4 ]′ A) (var x3) (var x2) (var x1))) x PE.≡
        (consSubst (wk1Subst (wk1Subst idSubst)) (prodʷ p (var x1) (var x0)) ₛ•ₛ
         (consSubst (wkSubst 3 idSubst) (suc (var x2)) ⇑)) x
      lemma x0 = PE.cong (_[ _ ]) cons′≡prod
      lemma (x0 +1) = PE.refl
      lemma (x +2) = PE.refl
    lemma₁₀ : P [ consSubst (wkSubst 3 idSubst) (suc (var x2)) ⇑ ] [ var x0 ]₀ PE.≡
              P [ consSubst (consSubst (wkSubst 3 idSubst) (suc (var x2))) (var x0) ]
    lemma₁₀ = begin
       P [ consSubst (wkSubst 3 idSubst) (suc (var x2)) ⇑ ] [ var x0 ]₀            ≡⟨ substCompEq P ⟩
       P [ sgSubst (var x0) ₛ•ₛ (consSubst (wkSubst 3 idSubst) (suc (var x2)) ⇑) ] ≡⟨ substVar-to-subst lemma P ⟩
       P [ consSubst (consSubst (wkSubst 3 idSubst) (suc (var x2))) (var x0)     ] ∎
       where
       lemma : (x : Fin (2+ n)) → (sgSubst (var x0) ₛ•ₛ (consSubst (wkSubst 3 idSubst) (suc (var x2)) ⇑)) x PE.≡
               (consSubst (consSubst (wkSubst 3 idSubst) (suc (var x2))) (var x0)) x
       lemma x0 = PE.refl
       lemma (x0 +1) = PE.refl
       lemma (x +2) = PE.refl
    lemma₁₁ : ∀ {t u} → P [ consSubst (wkSubst 3 idSubst) (suc (var x2)) ⇑ ] [ consSubst (sgSubst t) u ⇑[ 2 ] ] PE.≡
                        P [ consSubst (wk1Subst idSubst) (wk1 (suc t)) ⇑ ]
    lemma₁₁ {t} {u} = begin
      P [ consSubst (wkSubst 3 idSubst) (suc (var x2)) ⇑ ] [ consSubst (sgSubst t) u ⇑[ 2 ] ] ≡⟨ substCompEq P ⟩
      P [ (consSubst (sgSubst t) u ⇑[ 2 ]) ₛ•ₛ (consSubst (wkSubst 3 idSubst) (suc (var x2)) ⇑) ] ≡⟨ substVar-to-subst lemma P ⟩
      P [ consSubst (wk1Subst idSubst) (wk1 (suc t)) ⇑ ] ∎
      where
      lemma : ∀ x → ((consSubst (sgSubst t) u ⇑[ 2 ]) ₛ•ₛ (consSubst (wkSubst 3 idSubst) (suc (var x2)) ⇑)) x PE.≡
                    (consSubst (wk1Subst idSubst) (wk1 (suc t)) ⇑) x
      lemma x0 = PE.refl
      lemma (_+1 x0) = PE.refl
      lemma (x +2) = PE.refl
    lemma₁₂ : ∀ {t u} → cs [ consSubst (consSubst (consSubst (consSubst (wkSubst 5 idSubst) (var x4)) (var x1)) (var x0)) (var x3 ∘⟨ r ⟩ var x0) ]
                           [ consSubst (sgSubst t) u ⇑[ 3 ] ] PE.≡
                        cs [ consSubst (consSubst (wk1Subst idSubst) (wk1 t) ⇑[ 2 ]) (wk[ 3 ]′ u ∘⟨ r ⟩ var x0) ]
    lemma₁₂ {t} {u} = begin
      cs [ consSubst (consSubst (consSubst (consSubst (wkSubst 5 idSubst) (var x4)) (var x1)) (var x0)) (var x3 ∘⟨ r ⟩ var x0) ]
         [ consSubst (sgSubst t) u ⇑[ 3 ] ]
           ≡⟨ substCompEq cs ⟩
      cs [ (consSubst (sgSubst t) u ⇑[ 3 ]) ₛ•ₛ
           consSubst (consSubst (consSubst (consSubst (wkSubst 5 idSubst) (var x4)) (var x1)) (var x0)) (var x3 ∘⟨ r ⟩ var x0) ]
           ≡⟨ substVar-to-subst lemma cs ⟩
      cs [ consSubst (consSubst (wk1Subst idSubst) (wk1 t) ⇑[ 2 ]) (wk[ 3 ]′ u ∘⟨ r ⟩ var x0) ] ∎
      where
      lemma : ∀ x → ((consSubst (sgSubst t) u ⇑[ 3 ]) ₛ•ₛ
                      consSubst (consSubst (consSubst (consSubst (wkSubst 5 idSubst) (var x4)) (var x1)) (var x0)) (var x3 ∘⟨ r ⟩ var x0)) x PE.≡
                    (consSubst (consSubst (wk1Subst idSubst) (wk1 t) ⇑[ 2 ]) (wk[ 3 ]′ u ∘⟨ r ⟩ var x0)) x
      lemma x0 = PE.cong (_∘⟨ r ⟩ var x0) wk[]≡wk[]′
      lemma (x0 +1) = PE.refl
      lemma (x0 +2) = PE.refl
      lemma (x0 +1 +2) = PE.refl
      lemma ((x +2) +2) = PE.refl
    lemma₁₃ : Vec′ l (wk1 A) (wk1 (suc k)) PE.≡ Vec′ l (wk1 A) (var x0) [ wk1 (suc k) ]↑
    lemma₁₃ {k} = begin
      Vec′ l (wk1 A) (wk1 (suc k))                                                ≡⟨ PE.cong (λ x → Vec′ l x _) (wk≡subst (step id) A) ⟩
      Vec′ l (A [ wk1Subst idSubst ]) (wk1 (suc k))                               ≡˘⟨ PE.cong (λ x → Vec′ l x _) (wk1-tail A) ⟩
      Vec′ l (wk1 A [ consSubst (wk1Subst idSubst) (wk1 (suc k)) ]) (wk1 (suc k)) ≡⟨⟩
      Vec′ l (wk1 A [ wk1 (suc k) ]↑) (wk1 (suc k))                               ≡˘⟨ Vec′-subst ⟩
      Vec′ l (wk1 A) (var x0) [ wk1 (suc k) ]↑                                    ∎
    lemma₁₄ : ∀ {t u} → P [ consSubst (wk1Subst idSubst) (wk1 t) ⇑ ] [ sgSubst u ⇑ ] PE.≡ P [ sgSubst t ⇑ ]
    lemma₁₄ {t} {u} = begin
      P [ consSubst (wk1Subst idSubst) (wk1 t) ⇑ ] [ sgSubst u ⇑ ]     ≡⟨ substCompEq P ⟩
      P [ (sgSubst u ⇑) ₛ•ₛ (consSubst (wk1Subst idSubst) (wk1 t) ⇑) ] ≡⟨ substVar-to-subst lemma P ⟩
      P [ sgSubst t ⇑ ]                                                ∎
      where
      lemma : ∀ x → ((sgSubst u ⇑) ₛ•ₛ (consSubst (wk1Subst idSubst) (wk1 t) ⇑)) x PE.≡ (sgSubst t ⇑) x
      lemma x0 = PE.refl
      lemma (x0 +1) = PE.trans (wk1-liftSubst (wk1 t)) (PE.cong wk1 (wk1-sgSubst t u))
      lemma (x +2) = PE.refl
    lemma₁₅ : ∀ {t u v} → cs [ consSubst (consSubst (wk1Subst idSubst) (wk1 t) ⇑[ 2 ]) (wk[ 3 ]′ u ∘⟨ r ⟩ var x0) ] [ sgSubst v ⇑[ 2 ] ] PE.≡
                        cs [ consSubst (sgSubst t ⇑[ 2 ]) (wk₂ u ∘⟨ r ⟩ var x0) ]
    lemma₁₅ {t} {u} {v} = begin
      cs [ consSubst (consSubst (wk1Subst idSubst) (wk1 t) ⇑[ 2 ]) (wk[ 3 ]′ u ∘⟨ r ⟩ var x0) ] [ sgSubst v ⇑[ 2 ] ]   ≡⟨ substCompEq cs ⟩
      cs [ (sgSubst v ⇑[ 2 ]) ₛ•ₛ consSubst (consSubst (wk1Subst idSubst) (wk1 t) ⇑[ 2 ]) (wk[ 3 ]′ u ∘⟨ r ⟩ var x0) ] ≡⟨ substVar-to-subst lemma cs ⟩
      cs [ consSubst (sgSubst t ⇑[ 2 ]) (wk₂ u ∘⟨ r ⟩ var x0) ]                                                        ∎
      where
      lemma″ : ∀ {n} (u : Term n) v → wk[ 3 ] u [ sgSubst v ⇑[ 2 ] ] PE.≡ wk2 u
      lemma″ u v = begin
        wk[ 3 ] u [ sgSubst v ⇑[ 2 ] ] ≡⟨⟩
        wk1 (wk[ 2 ] u) [ sgSubst v ⇑[ 2 ] ] ≡⟨ wk1-liftSubst (wk[ 2 ] u) ⟩
        wk1 (wk[ 2 ] u [ sgSubst v ⇑ ])      ≡⟨⟩
        wk1 (wk1 (wk1 u) [ sgSubst v ⇑ ])    ≡⟨ PE.cong wk1 (wk1-liftSubst (wk1 u)) ⟩
        wk1 (wk1 ((wk1 u) [ sgSubst v ]))    ≡⟨ PE.cong wk2 (wk1-sgSubst _ _) ⟩
        wk1 (wk1 u)                          ∎
      lemma : ∀ x → ((sgSubst v ⇑[ 2 ]) ₛ•ₛ consSubst (consSubst (wk1Subst idSubst) (wk1 t) ⇑[ 2 ]) (wk[ 3 ]′ u ∘⟨ r ⟩ var x0)) x PE.≡
                    (consSubst (sgSubst t ⇑[ 2 ]) (wk₂ u ∘⟨ r ⟩ var x0)) x
      lemma x0 = PE.cong (_∘⟨ r ⟩ var x0) $ begin
        wk[ 3 ]′ u [ sgSubst v ⇑[ 2 ] ] ≡˘⟨ PE.cong (_[ sgSubst v ⇑[ 2 ] ]) (wk[]≡wk[]′ {t = u}) ⟩
        wk[ 3 ] u [ sgSubst v ⇑[ 2 ] ]  ≡⟨ lemma″ u v ⟩
        wk1 (wk1 u)                     ≡⟨ wk[]≡wk[]′ ⟩
        wk₂ u                           ∎
      lemma (x0 +1) = PE.refl
      lemma (x0 +2) = PE.refl
      lemma (x0 +1 +2) = lemma″ t v
      lemma ((x +2) +2) = PE.refl
    lemma₁₆ : wk1 (Vec′ l (wk1 A) (wk1 k)) PE.≡ wk (lift (step id)) (wk1 (Vec′ l A k))
    lemma₁₆ {k} = begin
      wk1 (Vec′ l (wk1 A) (wk1 k))               ≡˘⟨ PE.cong wk1 Vec′-wk ⟩
      wk2 (Vec′ l A k)                           ≡⟨ wk[]≡wk[]′ ⟩
      wk (lift (step id) • step id) (Vec′ l A k) ≡˘⟨ wk-comp _ _ _ ⟩
      wk (lift (step id)) (wk1 (Vec′ l A k))     ∎
    lemma₁₇ : wk1 A [ consSubst (wk1Subst idSubst) t ] PE.≡ wk1 A
    lemma₁₇ {t} = begin
      wk1 A [ consSubst (wk1Subst idSubst) t ] ≡⟨ wk1-tail A ⟩
      A [ wk1Subst idSubst ]                   ≡˘⟨ wk≡subst _ A ⟩
      wk1 A                                    ∎
    lemma₁₈ : Vec′ l (wk₂ A) (wk₂ k) PE.≡ Vec′ l (wk₂ A) (var x1) [ consSubst (wk1Subst idSubst) (wk1 k) ⇑ ]
    lemma₁₈ {k} = begin
      Vec′ l (wk₂ A) (wk₂ k)                                                            ≡⟨ PE.cong (λ x → Vec′ l x _) (wk≡subst _ A) ⟩
      Vec′ l (A [ toSubst (step (step id)) ]) (wk₂ k)                                   ≡⟨ PE.cong (λ x → Vec′ l x _) (substVar-to-subst (λ _ → PE.refl) A) ⟩
      Vec′ l (A [ (consSubst (wk1Subst idSubst) (wk1 k) ⇑) ₛ• step (step id) ]) (wk₂ k) ≡˘⟨ PE.cong₂ (Vec′ l) (subst-wk A) wk[]≡wk[]′ ⟩
      Vec′ l (wk₂ A [ consSubst (wk1Subst idSubst) (wk1 k) ⇑ ] ) (wk2 k)                ≡˘⟨ Vec′-subst ⟩
      Vec′ l (wk₂ A) (var x1) [ consSubst (wk1Subst idSubst) (wk1 k) ⇑ ]                ∎
    lemma₁₉ : wk (lift (stepn id 3)) (P [ sgSubst k ⇑ ]) [ sgSubst (var x0) ] PE.≡ P [ wk1Subst idSubst ⇑ ] [ consSubst (wk1Subst idSubst) (wk1 k) ⇑[ 2 ] ]
    lemma₁₉ {k} = begin
      wk (lift (stepn id 3)) (P [ sgSubst k ⇑ ]) [ sgSubst (var x0) ]              ≡⟨ PE.cong (_[ sgSubst (var x0) ]) (wk-subst P) ⟩
      P [ lift (stepn id 3) •ₛ (sgSubst k ⇑) ] [ sgSubst (var x0) ]                ≡⟨ substCompEq P ⟩
      P [ sgSubst (var x0) ₛ•ₛ (lift (stepn id 3) •ₛ (sgSubst k ⇑)) ]              ≡⟨ substVar-to-subst lemma P ⟩
      P [ (consSubst (wk1Subst idSubst) (wk1 k) ⇑[ 2 ]) ₛ•ₛ (wk1Subst idSubst ⇑) ] ≡˘⟨ substCompEq P ⟩
      P [ wk1Subst idSubst ⇑ ] [ consSubst (wk1Subst idSubst) (wk1 k) ⇑[ 2 ] ]     ∎
      where
      lemma : ∀ x → (sgSubst (var x0) ₛ•ₛ (lift (stepn id 3) •ₛ (sgSubst k ⇑))) x PE.≡
                    ((consSubst (wk1Subst idSubst) (wk1 k) ⇑[ 2 ]) ₛ•ₛ (wk1Subst idSubst ⇑)) x
      lemma x0 = PE.refl
      lemma (_+1 x0) = begin
        wk (lift (stepn id 3)) (wk1 k) [ var x0 ]₀ ≡⟨ PE.cong (_[ var x0 ]₀) (wk-comp _ _ k) ⟩
        wk[ 4 ]′ k [ var x0 ]₀                     ≡˘⟨ PE.cong (_[ var x0 ]₀) (wk[]≡wk[]′ {k = 4} {t = k}) ⟩
        wk[ 4 ] k [ var x0 ]₀                      ≡⟨ wk1-sgSubst _ _ ⟩
        wk[ 3 ] k                                  ∎
      lemma (x +2) = PE.refl
    lemma₂₀ : ∀ {t u} → P [ consSubst (consSubst (wkSubst 4 idSubst) (suc (var x3))) (cons′ (wk[ 4 ]′ A) (var x3) (var x2) (var x1)) ]
                          [ consSubst (consSubst (wk1Subst idSubst) (wk1 t) ⇑[ 2 ]) (wk[ 3 ]′ u ∘⟨ r ⟩ var x0) ] PE.≡
                        P [ consSubst (wk1Subst idSubst) (wk1 (suc t)) ⇑ ] [ prodʷ p (var x1) (var x0) ]↑²
    lemma₂₀ {t} {u} = begin
      P [ consSubst (consSubst (wkSubst 4 idSubst) (suc (var x3))) (cons′ (wk[ 4 ]′ A) (var x3) (var x2) (var x1)) ]
        [ consSubst (consSubst (wk1Subst idSubst) (wk1 t) ⇑[ 2 ]) (wk[ 3 ]′ u ∘⟨ r ⟩ var x0) ]
          ≡⟨ substCompEq P ⟩
      P [ consSubst (consSubst (wk1Subst idSubst) (wk1 t) ⇑[ 2 ]) (wk[ 3 ]′ u ∘⟨ r ⟩ var x0) ₛ•ₛ
          consSubst (consSubst (wkSubst 4 idSubst) (suc (var x3))) (cons′ (wk[ 4 ]′ A) (var x3) (var x2) (var x1)) ]
          ≡⟨ substVar-to-subst lemma P ⟩
      P [ consSubst (wkSubst 2 idSubst) (prodʷ p (var x1) (var x0)) ₛ•ₛ (consSubst (wk1Subst idSubst) (wk1 (suc t)) ⇑) ]
          ≡˘⟨ substCompEq P ⟩
      P [ consSubst (wk1Subst idSubst) (wk1 (suc t)) ⇑ ] [ prodʷ p (var x1) (var x0) ]↑² ∎
      where
      lemma : ∀ x → (consSubst (consSubst (wk1Subst idSubst) (wk1 t) ⇑[ 2 ]) (wk[ 3 ]′ u ∘⟨ r ⟩ var x0) ₛ•ₛ
          consSubst (consSubst (wkSubst 4 idSubst) (suc (var x3))) (cons′ (wk[ 4 ]′ A) (var x3) (var x2) (var x1))) x PE.≡
          (consSubst (wkSubst 2 idSubst) (prodʷ p (var x1) (var x0)) ₛ•ₛ (consSubst (wk1Subst idSubst) (wk1 (suc t)) ⇑)) x
      lemma x0 = PE.cong (_[ _ ]) cons′≡prod
      lemma (x0 +1) = PE.cong suc $ begin
        wk[ 3 ] t ≡⟨ wk[]≡wk[]′ ⟩
        wk₂ (wk1 t) ≡⟨ wk≡subst _ (wk1 t) ⟩
        wk1 t [ wkSubst 2 idSubst ] ≡˘⟨ wk1-tail (wk1 t) ⟩
        wk[ 2 ] t [ consSubst (wkSubst 2 idSubst) (prodʷ p (var x1) (var x0)) ] ∎
      lemma (x +2) = PE.refl
    lemma₂₁ : ∀ {u} → cs [ consSubst (sgSubst k ⇑[ 2 ]) (wk₂ u ∘⟨ r ⟩ var x0) ] [ h , t ]₁₀ PE.≡
                      cs [ consSubst (consSubst (consSubst (sgSubst k) h) t) (u ∘⟨ r ⟩ t) ]
    lemma₂₁ {k} {h} {t} {u} = begin
      cs [ consSubst (sgSubst k ⇑[ 2 ]) (wk₂ u ∘⟨ r ⟩ var x0) ] [ h , t ]₁₀ ≡⟨ substCompEq cs ⟩
      cs [ consSubst (sgSubst h) t ₛ•ₛ consSubst (sgSubst k ⇑[ 2 ]) (wk₂ u ∘⟨ r ⟩ var x0) ] ≡⟨ substVar-to-subst lemma cs ⟩
      cs [ consSubst (consSubst (consSubst (sgSubst k) h) t) (u ∘⟨ r ⟩ t) ] ∎
      where
      lemma : ∀ x → (consSubst (sgSubst h) t ₛ•ₛ consSubst (sgSubst k ⇑[ 2 ]) (wk₂ u ∘⟨ r ⟩ var x0)) x PE.≡
                    (consSubst (consSubst (consSubst (sgSubst k) h) t) (u ∘⟨ r ⟩ t)) x
      lemma x0 = PE.cong (_∘⟨ r ⟩ t) $ begin
        wk₂ u [ consSubst (sgSubst h) t ] ≡˘⟨ PE.cong (_[ consSubst (sgSubst h) t ]) (wk[]≡wk[]′ {k = 2} {t = u}) ⟩
        wk2 u [ consSubst (sgSubst h) t ] ≡⟨ wk1-tail (wk1 u) ⟩
        wk1 u [ h ]₀ ≡⟨ wk1-sgSubst _ _ ⟩
        u ∎
      lemma (x0 +1) = PE.refl
      lemma (x0 +2) = PE.refl
      lemma (x0 +1 +2) = begin
        wk2 k [ consSubst (sgSubst h) t ] ≡⟨ wk1-tail (wk1 k) ⟩
        wk1 k [ h ]₀ ≡⟨ wk1-sgSubst _ _ ⟩
        k ∎
      lemma ((x +2) +2) = PE.refl
    lemma₂₂ : P [ consSubst (wk1Subst idSubst) (wk1 (suc k)) ⇑ ] [ var x0 ]₀ [ cons′ A k h t ]₀ PE.≡
              P [ sgSubst (suc k) ⇑ ] [ prodʷ p h t ]₀
    lemma₂₂ {k} {h} {t} = begin
      P [ consSubst (wk1Subst idSubst) (wk1 (suc k)) ⇑ ] [ var x0 ]₀ [ cons′ A k h t ]₀
        ≡⟨ substCompEq (P [ consSubst (wk1Subst idSubst) (wk1 (suc k)) ⇑ ]) ⟩
      P [ consSubst (wk1Subst idSubst) (wk1 (suc k)) ⇑ ] [ sgSubst (cons′ A k h t) ₛ•ₛ sgSubst (var x0) ]
        ≡⟨ substCompEq P ⟩
      P [ sgSubst (cons′ A k h t) ₛ•ₛ sgSubst (var x0) ₛ•ₛ (consSubst (wk1Subst idSubst) (wk1 (suc k)) ⇑) ]
        ≡⟨ substVar-to-subst lemma P ⟩
      P [ sgSubst (prodʷ p h t ) ₛ•ₛ (sgSubst (suc k) ⇑) ]
        ≡˘⟨ substCompEq P ⟩
      P [ sgSubst (suc k) ⇑ ] [ prodʷ p h t ]₀ ∎
      where
      lemma : ∀ x → (sgSubst (cons′ A k h t) ₛ•ₛ sgSubst (var x0) ₛ•ₛ (consSubst (wk1Subst idSubst) (wk1 (suc k)) ⇑)) x PE.≡
                    (sgSubst (prodʷ p h t ) ₛ•ₛ (sgSubst (suc k) ⇑)) x
      lemma x0 = cons′≡prod
      lemma (x0 +1) = PE.cong suc $ begin
        wk2 k [ sgSubst (cons′ A k h t) ₛ•ₛ sgSubst (var x0) ]           ≡⟨ wk1-tail (wk1 k) ⟩
        wk1 k [ tail (sgSubst (cons′ A k h t) ₛ•ₛ sgSubst (var x0)) ]    ≡⟨ wk1-tail k ⟩
        k [ tail (tail (sgSubst (cons′ A k h t) ₛ•ₛ sgSubst (var x0))) ] ≡⟨ substVar-to-subst (λ _ → PE.refl) k ⟩
        k [ idSubst ]                                                    ≡˘⟨ wk1-tail k ⟩
        wk1 k [ prodʷ p h t ]₀                                           ∎
      lemma (x +2) = PE.refl
    lemma₂₃ : P [ sgSubst (suc k) ⇑ ] [ prodʷ p h t ]₀ PE.≡ P [ suc k , cons′ A k h t ]₁₀
    lemma₂₃ {k} {h} {t} = begin
      P [ sgSubst (suc k) ⇑ ] [ prodʷ p h t ]₀ ≡⟨ substCompEq P ⟩
      P [ sgSubst (prodʷ p h t) ₛ•ₛ (sgSubst (suc k) ⇑) ] ≡⟨ substVar-to-subst lemma P ⟩
      P [ suc k , cons′ A k h t ]₁₀ ∎
      where
      lemma : ∀ x → (sgSubst (prodʷ p h t) ₛ•ₛ (sgSubst (suc k) ⇑)) x PE.≡
                    (consSubst (sgSubst (suc k)) (cons′ A k h t)) x
      lemma x0 = PE.sym cons′≡prod
      lemma (x0 +1) = wk1-sgSubst _ _
      lemma (x +2) = PE.refl
    lemma₂₄ : wk1 (Vec′ l A k) PE.≡ Vec′ l (wk₂ A) (var x1) [ sgSubst k ⇑ ]
    lemma₂₄ {k} = begin
      wk1 (Vec′ l A k)                        ≡⟨ Vec′-wk ⟩
      Vec′ l (wk1 A) (wk1 k)                  ≡˘⟨ PE.cong (λ x → Vec′ l (wk1 x) _) (wk1-sgSubst _ _) ⟩
      Vec′ l (wk1 (wk1 A [ k ]₀)) (wk1 k)     ≡˘⟨ PE.cong (λ x → Vec′ l x _) (wk1-liftSubst (wk1 A)) ⟩
      Vec′ l (wk2 A [ sgSubst k ⇑ ]) (wk1 k)  ≡⟨ PE.cong (λ x → Vec′ l (x [ sgSubst k ⇑ ]) _) (wk[]≡wk[]′ {k = 2} {t = A}) ⟩
      Vec′ l (wk₂ A [ sgSubst k ⇑ ]) (wk1 k)  ≡˘⟨ Vec′-subst ⟩
      Vec′ l (wk₂ A) (var x1) [ sgSubst k ⇑ ] ∎
    lemma₂₅ : wk (lift (stepn id 2)) (P [ sgSubst k ⇑ ]) [ var x0 ]₀ PE.≡ P [ wk1Subst idSubst ⇑ ] [ sgSubst k ⇑[ 2 ] ]
    lemma₂₅ {k} = begin
      wk (lift (stepn id 2)) (P [ sgSubst k ⇑ ]) [ var x0 ]₀          ≡⟨ PE.cong (_[ var x0 ]₀) (wk-subst P) ⟩
      P [ lift (stepn id 2) •ₛ (sgSubst k ⇑) ] [ var x0 ]₀            ≡⟨ substCompEq P ⟩
      P [ sgSubst (var x0) ₛ•ₛ (lift (stepn id 2) •ₛ (sgSubst k ⇑)) ] ≡⟨ substVar-to-subst lemma P ⟩
      P [ (sgSubst k ⇑[ 2 ]) ₛ•ₛ (wk1Subst idSubst ⇑) ]               ≡˘⟨ substCompEq P ⟩
      P [ wk1Subst idSubst ⇑ ] [ sgSubst k ⇑[ 2 ] ]                   ∎
      where
      lemma : ∀ x → (sgSubst (var x0) ₛ•ₛ (lift (stepn id 2) •ₛ (sgSubst k ⇑))) x PE.≡
                    ((sgSubst k ⇑[ 2 ]) ₛ•ₛ (wk1Subst idSubst ⇑)) x
      lemma x0 = PE.refl
      lemma (_+1 x0) = begin
        wk (lift (step (step id))) (wk1 k) [ var x0 ]₀ ≡⟨ PE.cong (_[ var x0 ]₀) (wk-comp _ _ k) ⟩
        wk (stepn id 3) k [ var x0 ]₀                  ≡⟨ step-consSubst k ⟩
        wk₂ k [ idSubst ]                              ≡⟨ subst-id _ ⟩
        wk₂ k                                          ≡˘⟨ wk[]≡wk[]′ ⟩
        wk2 k                                          ∎
      lemma (x +2) = PE.refl
    lemma₂₆ : P [ consSubst (consSubst (wkSubst 4 idSubst) (suc (var x3))) (cons′ (wk[ 4 ]′ A) (var x3) (var x2) (var x1)) ]
                [ consSubst (sgSubst k ⇑[ 2 ]) (wk₂ t ∘⟨ r ⟩ var x0) ] PE.≡
              P [ sgSubst (suc k) ⇑ ] [ consSubst (wkSubst 2 idSubst) (prodʷ p (var x1) (var x0)) ]
    lemma₂₆ {k} {t} = begin
      P [ consSubst (consSubst (wkSubst 4 idSubst) (suc (var x3))) (cons′ (wk[ 4 ]′ A) (var x3) (var x2) (var x1)) ]
        [ consSubst (sgSubst k ⇑[ 2 ]) (wk₂ t ∘⟨ r ⟩ var x0) ]
          ≡⟨ substCompEq P ⟩
      P [ consSubst (sgSubst k ⇑[ 2 ]) (wk₂ t ∘⟨ r ⟩ var x0) ₛ•ₛ
          consSubst (consSubst (wkSubst 4 idSubst) (suc (var x3))) (cons′ (wk[ 4 ]′ A) (var x3) (var x2) (var x1)) ]
        ≡⟨ substVar-to-subst lemma P ⟩
      P [ consSubst (wkSubst 2 idSubst) (prodʷ p (var x1) (var x0)) ₛ•ₛ (sgSubst (suc k) ⇑) ]
        ≡˘⟨ substCompEq P ⟩
      P [ sgSubst (suc k) ⇑ ] [ consSubst (wkSubst 2 idSubst) (prodʷ p (var x1) (var x0)) ] ∎
      where
      lemma : ∀ x → (consSubst (sgSubst k ⇑[ 2 ]) (wk₂ t ∘⟨ r ⟩ var x0) ₛ•ₛ
                    consSubst (consSubst (wkSubst 4 idSubst) (suc (var x3))) (cons′ (wk[ 4 ]′ A) (var x3) (var x2) (var x1))) x PE.≡
                    (consSubst (wkSubst 2 idSubst) (prodʷ p (var x1) (var x0)) ₛ•ₛ (sgSubst (suc k) ⇑)) x
      lemma x0 = PE.cong (_[ _ ]) cons′≡prod
      lemma (x0 +1) = PE.cong suc $ begin
        wk2 k                                                               ≡⟨ wk[]≡wk[]′ ⟩
        wk₂ k                                                               ≡⟨ wk≡subst _ _ ⟩
        k [ wkSubst 2 idSubst ]                                             ≡˘⟨ wk1-tail k ⟩
        wk1 k [ consSubst (wkSubst 2 idSubst) (prodʷ p (var x1) (var x0)) ] ∎
      lemma (x +2) = PE.refl

opaque

  ⊢∷-vecrec-cons :
    s PE.≡ 𝕨 →
    Γ »∙ ℕ »∙ Vec′ l (wk1 A) (var x0) ⊢ P →
    Γ ⊢ A ∷ U l →
    Γ »∙ ℕ »∙ wk1 A »∙ Vec′ l (wk₂ A) (var x1) »∙ P [ wk1Subst idSubst ⇑ ] ⊢ cs ∷
      P [ consSubst (consSubst (wkSubst 4 idSubst) (suc (var x3))) (cons′ (wk[ 4 ]′ A) (var x3) (var x2) (var x1)) ] →
    Π-allowed r q →
    Γ »∙ ℕ »∙ Π r , q ▷ Vec′ l (wk1 A) (var x0) ▹ P
        ⊢ vecrec-cons r q P cs
        ∷ Π r , q ▷ Vec′ l (wk₂ A) (suc (var x1)) ▹ (P [ consSubst (consSubst (wkSubst 3 idSubst) (suc (var x2))) (var x0) ])
  ⊢∷-vecrec-cons s≡𝕨 ⊢P ⊢A ⊢cs Π-ok =
    ⊢∷-vecrec-cons′ s≡𝕨 ⊢P ⊢A ⊢cs Π-ok .proj₁

opaque

  ⊢⇒*∷-vecrec-cons :
    ∀ {IH} →
    s PE.≡ 𝕨 →
    Γ »∙ ℕ »∙ Vec′ l (wk1 A) (var x0) ⊢ P →
    Γ ⊢ A ∷ U l →
    Γ »∙ ℕ »∙ wk1 A »∙ Vec′ l (wk₂ A) (var x1) »∙ P [ wk1Subst idSubst ⇑ ] ⊢ cs ∷
      P [ consSubst (consSubst (wkSubst 4 idSubst) (suc (var x3))) (cons′ (wk[ 4 ]′ A) (var x3) (var x2) (var x1)) ] →
    Γ ⊢ k ∷ ℕ →
    Γ ⊢ h ∷ A →
    Γ ⊢ t ∷ Vec′ l A k →
    Γ ⊢ IH ∷ Π r , q ▷ Vec′ l A k ▹ (P [ sgSubst k ⇑ ]) →
    Π-allowed r q →
    Γ ⊢ (vecrec-cons r q P cs [ k , IH ]₁₀) ∘⟨ r ⟩ cons′ A k h t ⇒*
      cs [ consSubst (consSubst (consSubst (sgSubst k) h) t) (IH ∘⟨ r ⟩ t) ] ∷
      P [ suc k , cons′ A k h t ]₁₀
  ⊢⇒*∷-vecrec-cons s≡𝕨 ⊢P ⊢A ⊢cs ⊢k ⊢h ⊢t ⊢IH Π-ok =
    ⊢∷-vecrec-cons′ s≡𝕨 ⊢P ⊢A ⊢cs Π-ok .proj₂ ⊢k ⊢h ⊢t ⊢IH

private opaque
  unfolding vecrec′

  ⊢∷-vecrec″ :
    s PE.≡ 𝕨 →
    Γ »∙ ℕ »∙ Vec′ l (wk1 A) (var x0) ⊢ P →
    Γ ⊢ A ∷ U l →
    Γ ⊢ nl ∷ P [ zero , nil′ l A ]₁₀ →
    Γ »∙ ℕ »∙ wk1 A »∙ Vec′ l (wk₂ A) (var x1) »∙ P [ wk1Subst idSubst ⇑ ] ⊢ cs ∷
      (P [ consSubst (consSubst (wkSubst 4 idSubst) (suc (var x3))) (cons′ (wk[ 4 ]′ A) (var x3) (var x2) (var x1)) ]) →
    Π-allowed r q₂ →
    (∀ {k} {xs} →
       Γ ⊢ k ∷ ℕ →
       Γ ⊢ xs ∷ Vec′ l A k →
       Γ ⊢ vecrec′ l p₁ p₂ r q₁ q₂ A P nl cs k xs ∷ (P [ k , xs ]₁₀)) ×
    (Γ ⊢ vecrec′ l p₁ p₂ r q₁ q₂ A P nl cs zero (nil′ l A) ⇒* nl ∷ P [ zero , nil′ l A ]₁₀) ×
    (∀ {k} {x} {xs} →
       Γ ⊢ k ∷ ℕ →
       Γ ⊢ x ∷ A →
       Γ ⊢ xs ∷ Vec′ l A k →
       Γ ⊢ vecrec′ l p₁ p₂ r q₁ q₂ A P nl cs (suc k) (cons′ A k x xs) ⇒*
           cs [ consSubst (consSubst (consSubst (sgSubst k) x) xs) (vecrec′ l p₁ p₂ r q₁ q₂ A P nl cs k xs) ] ∷
           P [ suc k , cons′ A k x xs ]₁₀)
  ⊢∷-vecrec″ {l} {A} {P} {nl} {cs} {r} {q₂} {p₁} {p₂} {q₁} PE.refl ⊢P ⊢A ⊢nl ⊢cs Π-ok =
    let ⊢vecrec₀ = ⊢∷-vecrec-nil PE.refl ⊢P ⊢A ⊢nl Π-ok
        ⊢vecrec₀′ = ⊢∷-conv-PE ⊢vecrec₀ (PE.cong (Π _ , _ ▷_▹ _) Vec₀≡₀)
        ⊢vecrec₊ = ⊢∷-vecrec-cons PE.refl ⊢P ⊢A ⊢cs Π-ok
        ⊢vecrec₊′ = ⊢∷-conv-PE ⊢vecrec₊ (PE.cong₂ (Π _ , _ ▷_▹_) Vec₀≡
                      (substVar-to-subst lemma₁ P))
    in  (λ ⊢k ⊢xs →
          let ⊢xs′ = ⊢∷-conv-PE ⊢xs Vec₀≡₀
          in  ⊢∷-conv-PE (natrecⱼ ⊢vecrec₀′ ⊢vecrec₊′ ⊢k ∘ⱼ ⊢xs′) lemma₂)
        ,
        (vecrec′ l p₁ p₂ r q₁ q₂ A P nl cs zero (nil′ l A)              ≡⟨⟩⇒
        natrec p₁ _ p₂ _ (vecrec-nil l r q₂ P nl) _ zero ∘⟨ r ⟩ nil′ l A ⇒⟨ ⊢⇒∷-conv-PE (app-subst (⊢⇒∷-conv-PE (natrec-zero ⊢vecrec₀′ ⊢vecrec₊′) lemma₃)
                                                                            (⊢nil′ ⊢A)) lemma₂ ⟩
        vecrec-nil l r q₂ P nl ∘⟨ r ⟩ nil′ l A                           ⇒*⟨ ⊢⇒*∷-vecrec-nil PE.refl ⊢P ⊢A ⊢nl Π-ok ⟩∎
        nl                                                              ∎)
        , λ {k} {x} {xs} ⊢k ⊢x ⊢xs →
          let nr = natrec p₁ (⌜ ⌞ r ⌟ ⌝ + q₁) p₂  (Π r , q₂ ▷ Vec′ l (wk1 A) (var x0) ▹ P)
                     (vecrec-nil l r q₂ P nl) (vecrec-cons r q₂ P cs)
              IH = vecrec′ l p₁ p₂ r q₁ q₂ A P nl cs k xs
              x:xs = cons′ A k x xs
              ⊢x:xs = ⊢cons′ ⊢A ⊢k ⊢x ⊢xs
              ⊢nr = ⊢∷-conv-PE (natrecⱼ ⊢vecrec₀′ ⊢vecrec₊′ ⊢k) lemma₃
              d =
                vecrec′ l p₁ p₂ r q₁ q₂ A P nl cs (suc k) x:xs ≡⟨⟩⇒
                nr (suc k) ∘⟨ r ⟩ x:xs                                        ⇒⟨ app-subst (⊢⇒∷-conv-PE (natrec-suc ⊢vecrec₀′ ⊢vecrec₊′ ⊢k) lemma₃) ⊢x:xs ⟩
                (vecrec-cons r q₂ P cs [ k , nr k ]₁₀) ∘⟨ r ⟩ x:xs            ⇒*⟨ ⊢⇒*∷-conv-PE (⊢⇒*∷-vecrec-cons PE.refl ⊢P ⊢A ⊢cs ⊢k ⊢x ⊢xs ⊢nr Π-ok) (PE.sym lemma₂) ⟩∎
                cs [ consSubst (consSubst (consSubst (sgSubst k) x) xs) IH ] ∎
          in  ⊢⇒*∷-conv-PE d lemma₂
    where
    lemma₁ :
      (x : Fin (2+ n)) →
      (consSubst (consSubst (wkSubst 3 idSubst) (suc (var x2))) (var x0)) x PE.≡
      (consSubst (wkSubst 2 idSubst) (suc (var x1)) ⇑) x
    lemma₁ x0 = PE.refl
    lemma₁ (x0 +1) = PE.refl
    lemma₁ (x +2) = PE.refl
    lemma₂ : P [ sgSubst k ⇑ ] [ xs ]₀ PE.≡ P [ k , xs ]₁₀
    lemma₂ {k} {xs} = begin
      P [ sgSubst k ⇑ ] [ xs ]₀          ≡⟨ substCompEq P ⟩
      P [ sgSubst xs ₛ•ₛ (sgSubst k ⇑) ] ≡⟨ substVar-to-subst lemma P ⟩
      P [ k , xs ]₁₀                     ∎
      where
      lemma : ∀ x → (sgSubst xs ₛ•ₛ (sgSubst k ⇑)) x PE.≡ consSubst (sgSubst k) xs x
      lemma x0 = PE.refl
      lemma (x0 +1) = wk1-sgSubst _ _
      lemma (x +2) = PE.refl
    lemma₃ : Π r , q₂ ▷ Vec′ l (wk1 A) (var x0) ▹ P [ k ]₀ PE.≡ Π r , q₂ ▷ Vec′ l A k ▹ (P [ sgSubst k ⇑ ])
    lemma₃ = PE.cong (Π r , q₂ ▷_▹ _) (PE.trans Vec′-subst (PE.cong (λ A → Vec′ l A _) (wk1-sgSubst _ _)))

opaque

  ⊢∷-vecrec′ :
    s PE.≡ 𝕨 →
    Γ »∙ ℕ »∙ Vec′ l (wk1 A) (var x0) ⊢ P →
    Γ ⊢ A ∷ U l →
    Γ ⊢ nl ∷ P [ zero , nil′ l A ]₁₀ →
    Γ »∙ ℕ »∙ wk1 A »∙ Vec′ l (wk₂ A) (var x1) »∙ P [ wk1Subst idSubst ⇑ ] ⊢ cs ∷
      P [ consSubst (consSubst (wkSubst 4 idSubst) (suc (var x3))) (cons′ (wk[ 4 ]′ A) (var x3) (var x2) (var x1)) ] →
    Γ ⊢ k ∷ ℕ →
    Γ ⊢ xs ∷ Vec′ l A k →
    Π-allowed r q₂ →
    Γ ⊢ vecrec′ l p₁ p₂ r q₁ q₂ A P nl cs k xs ∷ P [ k , xs ]₁₀
  ⊢∷-vecrec′ s≡𝕨 ⊢P ⊢A ⊢nl ⊢cs ⊢k ⊢xs Π-ok =
    ⊢∷-vecrec″ s≡𝕨 ⊢P ⊢A ⊢nl ⊢cs Π-ok .proj₁ ⊢k ⊢xs

opaque

  ⊢⇒*∷-vecrec-β-nil :
    s PE.≡ 𝕨 →
    Γ »∙ ℕ »∙ Vec′ l (wk1 A) (var x0) ⊢ P →
    Γ ⊢ A ∷ U l →
    Γ ⊢ nl ∷ P [ zero , nil′ l A ]₁₀ →
    Γ »∙ ℕ »∙ wk1 A »∙ Vec′ l (wk₂ A) (var x1) »∙ P [ wk1Subst idSubst ⇑ ] ⊢ cs ∷
      P [ consSubst (consSubst (wkSubst 4 idSubst) (suc (var x3))) (cons′ (wk[ 4 ]′ A) (var x3) (var x2) (var x1)) ] →
    Π-allowed r q₂ →
    Γ ⊢ vecrec′ l p₁ p₂ r q₁ q₂ A P nl cs zero (nil′ l A) ⇒* nl ∷ P [ zero , nil′ l A ]₁₀
  ⊢⇒*∷-vecrec-β-nil s≡𝕨 ⊢P ⊢A ⊢nl ⊢cs Π-ok =
    ⊢∷-vecrec″ s≡𝕨 ⊢P ⊢A ⊢nl ⊢cs Π-ok .proj₂ .proj₁

opaque

  ⊢⇒*∷-vecrec-β-cons :
    s PE.≡ 𝕨 →
    Γ »∙ ℕ »∙ Vec′ l (wk1 A) (var x0) ⊢ P →
    Γ ⊢ A ∷ U l →
    Γ ⊢ nl ∷ P [ zero , nil′ l A ]₁₀ →
    Γ »∙ ℕ »∙ wk1 A »∙ Vec′ l (wk₂ A) (var x1) »∙ P [ wk1Subst idSubst ⇑ ] ⊢ cs ∷
      P [ consSubst (consSubst (wkSubst 4 idSubst) (suc (var x3))) (cons′ (wk[ 4 ]′ A) (var x3) (var x2) (var x1)) ] →
    Γ ⊢ k ∷ ℕ →
    Γ ⊢ h ∷ A →
    Γ ⊢ t ∷ Vec′ l A k →
    Π-allowed r q₂ →
    Γ ⊢ vecrec′ l p₁ p₂ r q₁ q₂ A P nl cs (suc k) (cons′ A k h t) ⇒*
        cs [ consSubst (consSubst (consSubst (sgSubst k) h) t) (vecrec′ l p₁ p₂ r q₁ q₂ A P nl cs k t) ] ∷
        P [ suc k , cons′ A k h t ]₁₀
  ⊢⇒*∷-vecrec-β-cons s≡𝕨 ⊢P ⊢A ⊢nl ⊢cs ⊢k ⊢x ⊢xs Π-ok =
    ⊢∷-vecrec″ s≡𝕨 ⊢P ⊢A ⊢nl ⊢cs Π-ok .proj₂ .proj₂ ⊢k ⊢x ⊢xs
