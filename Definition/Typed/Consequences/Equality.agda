------------------------------------------------------------------------
-- Equality lemmata.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.Equality
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Lift 𝕄
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Untyped.Whnf M type-variant
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.Inversion R
open import Definition.Typed.Syntactic R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Fundamental.Reducibility R
open import Definition.LogicalRelation.Substitution.Introductions R

open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (1+)
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Relation

private
  variable
    ∇         : DCon (Term 0) _
    Γ         : Con Term _
    A B C t u : Term _
    V         : Set a
    b         : BinderMode
    p q       : M
    s         : Strength
    l         : Universe-level

opaque

  -- If the WHNF A is judgmentally equal to U l, then A is
  -- propositionally equal to U l (given a certain assumption).

  U≡A :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    ∇ » Γ ⊢ U l ≡ A → Whnf ∇ A → A PE.≡ U l
  U≡A {Γ} {∇} {l} {A} U≡A A-whnf =    $⟨ U≡A ⟩
    ∇ » Γ ⊢ U l ≡ A                   →⟨ reducible-⊩≡ ⟩
    (∃ λ l′ → ∇ » Γ ⊩⟨ l′ ⟩ U l ≡ A)  →⟨ proj₂ ∘→ ⊩U≡⇔ .proj₁ ∘→ proj₂ ⟩
    ∇ » Γ ⊢ A ⇒* U l                  →⟨ flip whnfRed* A-whnf ⟩
    A PE.≡ U l                        □

opaque

  -- If equality reflection is allowed, then there is a WHNF A that is
  -- judgementally equal to U l but not propositionally equal to U l
  -- (given a certain assumption).

  whnf≢U :
    Equality-reflection →
    Unitʷ-allowed →
    » ∇ →
    ∃₂ λ (Γ : Con Term 1) (A : Term 1) →
      ∇ » Γ ⊢ U l ≡ A × Whnf ∇ A × A PE.≢ U l
  whnf≢U {l} ok₁ ok₂ »∇ =
    ε ∙ Id (U (1+ l)) (U l) (Unitʷ (1+ l)) ,
    Unitʷ (1+ l) ,
    univ
      (equality-reflection′ ok₁ $
       var₀ (Idⱼ′ (Uⱼ (ε »∇)) (Unitⱼ (ε »∇) ok₂))) ,
    Unitₙ ,
    (λ ())

opaque

  -- If the WHNF A is judgmentally equal to ℕ, then A is
  -- propositionally equal to ℕ (given a certain assumption).

  ℕ≡A :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    ∇ » Γ ⊢ ℕ ≡ A → Whnf ∇ A → A PE.≡ ℕ
  ℕ≡A {Γ} {∇} {A} ℕ≡A A-whnf =
                    $⟨ ℕ≡A ⟩
    ∇ » Γ ⊢ ℕ ≡ A   →⟨ ⊩ℕ≡⇔ .proj₁ ∘→ proj₂ ∘→ reducible-⊩≡ ⟩
    ∇ » Γ ⊩ℕ ℕ ≡ A  ≡⟨ PE.refl ⟩→
    ∇ » Γ ⊢ A ⇒* ℕ  →⟨ flip whnfRed* A-whnf ⟩
    A PE.≡ ℕ        □

opaque

  -- If equality reflection is allowed, then there is a WHNF A that is
  -- judgementally equal to ℕ but not propositionally equal to ℕ.

  whnf≢ℕ :
    Equality-reflection →
    » ∇ →
    ∃₂ λ (Γ : Con Term 1) (A : Term 1) →
      ∇ » Γ ⊢ ℕ ≡ A × Whnf ∇ A × A PE.≢ ℕ
  whnf≢ℕ ok »∇ =
    ε ∙ Id (U 0) ℕ Empty ,
    Empty ,
    univ
      (equality-reflection′ ok $
       var₀ (Idⱼ′ (ℕⱼ (ε »∇)) (Emptyⱼ (ε »∇)))) ,
    Emptyₙ ,
    (λ ())

opaque

  -- If the WHNF A is judgmentally equal to Empty, then A is
  -- propositionally equal to Empty (given a certain assumption).

  Empty≡A :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    ∇ » Γ ⊢ Empty ≡ A → Whnf ∇ A → A PE.≡ Empty
  Empty≡A {Γ} {∇} {A} Empty≡A A-whnf =
                            $⟨ Empty≡A ⟩
    ∇ » Γ ⊢ Empty ≡ A       →⟨ ⊩Empty≡⇔ .proj₁ ∘→ proj₂ ∘→ reducible-⊩≡ ⟩
    ∇ » Γ ⊩Empty Empty ≡ A  ≡⟨ PE.refl ⟩→
    ∇ » Γ ⊢ A ⇒* Empty      →⟨ flip whnfRed* A-whnf ⟩
    A PE.≡ Empty            □

opaque

  -- If equality reflection is allowed, then there is a WHNF A that is
  -- judgementally equal to Empty but not propositionally equal
  -- to Empty.

  whnf≢Empty :
    Equality-reflection →
    » ∇ →
    ∃₂ λ (Γ : Con Term 1) (A : Term 1) →
      ∇ » Γ ⊢ Empty ≡ A × Whnf ∇ A × A PE.≢ Empty
  whnf≢Empty ok »∇ =
    ε ∙ Id (U 0) Empty ℕ ,
    ℕ ,
    univ
      (equality-reflection′ ok $
       var₀ (Idⱼ′ (Emptyⱼ (ε »∇)) (ℕⱼ (ε »∇)))) ,
    ℕₙ ,
    (λ ())

opaque

  -- If the WHNF A is judgmentally equal to Unit s l, then A is
  -- propositionally equal to Unit s l (given a certain assumption).

  Unit≡A :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    ∇ » Γ ⊢ Unit s l ≡ A → Whnf ∇ A → A PE.≡ Unit s l
  Unit≡A {Γ} {∇} {s} {l} {A} Unit≡A A-whnf =
                                           $⟨ Unit≡A ⟩
    ∇ » Γ ⊢ Unit s l ≡ A                   →⟨ reducible-⊩≡ ⟩
    (∃ λ l′ → ∇ » Γ ⊩⟨ l′ ⟩ Unit s l ≡ A)  →⟨ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ ⊩Unit≡⇔ .proj₁ ∘→ proj₂ ⟩
    ∇ » Γ ⊢ A ⇒* Unit s l                  →⟨ flip whnfRed* A-whnf ⟩
    A PE.≡ Unit s l                        □

opaque

  -- If equality reflection is allowed, then there is a WHNF A that is
  -- judgementally equal to a unit type but not propositionally equal
  -- to any unit type (given a certain assumption).

  whnf≢Unit :
    Equality-reflection →
    Unit-allowed s →
    » ∇ →
    ∃₂ λ (Γ : Con Term 1) (A : Term 1) →
      ∇ » Γ ⊢ Unit s l ≡ A × Whnf ∇ A ×
      ¬ ∃₂ λ s l → A PE.≡ Unit s l
  whnf≢Unit {s} {l} ok₁ ok₂ »∇ =
    ε ∙ Id (U l) (Unit s l) (Id (Unit s l) (star s l) (star s l)) ,
    Id (Unit s l) (star s l) (star s l) ,
    univ
      (equality-reflection′ ok₁ $ var₀ $
       let ⊢ε = ε »∇ in
       Idⱼ′ (Unitⱼ ⊢ε ok₂) $ Idⱼ (Unitⱼ ⊢ε ok₂) (starⱼ ⊢ε ok₂) (starⱼ ⊢ε ok₂)) ,
    Idₙ ,
    (λ ())

opaque

  -- If the neutral term B is judgmentally equal to the WHNF A, then A
  -- is neutral (given a certain assumption).

  ne≡A :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Neutral No-equality-reflection ∇ B →
    ∇ » Γ ⊢ B ≡ A →
    Whnf ∇ A →
    Neutral No-equality-reflection ∇ A
  ne≡A {Γ} {∇} {B} {A} B-ne B≡A A-whnf = $⟨ B≡A ⟩
    ∇ » Γ ⊢ B ≡ A                                  →⟨ reducible-⊩≡ ⟩
    (∃ λ l → ∇ » Γ ⊩⟨ l ⟩ B ≡ A)                   →⟨ Σ.map idᶠ (Σ.map idᶠ proj₁) ∘→ ⊩ne≡⇔ B-ne .proj₁ ∘→ proj₂ ⟩
    (∃ λ C → Neutral No-equality-reflection ∇ C ×
             ∇ » Γ ⊢ A ⇒* C)                       →⟨ (λ (_ , C-ne , A⇒*C) →
                                                      PE.subst (Neutral _ ∇) (PE.sym $ whnfRed* A⇒*C A-whnf) C-ne) ⟩
    Neutral No-equality-reflection ∇ A             □

opaque

  -- If equality reflection is allowed, then there is a WHNF B that is
  -- judgementally equal (as a type) to a neutral term A but not
  -- propositionally equal to A.

  whnf≢ne :
    Equality-reflection →
    » ∇ →
    ∃₃ λ (Γ : Con Term 2) (A B : Term 2) →
      ∇ » Γ ⊢ A ≡ B × Neutral⁺ ∇ A × Whnf ∇ B × A PE.≢ B
  whnf≢ne ok »∇ =
    ε ∙ U 0 ∙ Id (U 0) (var x0) Empty ,
    var x1 ,
    Empty ,
    univ
      (equality-reflection′ ok $
       var₀ (Idⱼ′ (var₀ (Uⱼ (ε »∇))) (Emptyⱼ (∙ Uⱼ (ε »∇))))) ,
    var⁺ _ ,
    Emptyₙ ,
    (λ ())

opaque

  -- If a WHNF C is definitionally equal to ΠΣ⟨ b ⟩ p , q ▷ A ▹ B,
  -- then C has the shape ΠΣ⟨ b ⟩ p , q ▷ _ ▹ _ (given a certain
  -- assumption).

  ΠΣ≡Whnf :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    ∇ » Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ≡ C → Whnf ∇ C →
    ∃₂ λ A′ B′ → C PE.≡ ΠΣ⟨ b ⟩ p , q ▷ A′ ▹ B′
  ΠΣ≡Whnf {Γ} {∇} {b} {p} {q} {A} {B} {C} ΠΣ≡C C-whnf =  $⟨ ΠΣ≡C ⟩
    ∇ » Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ≡ C                    →⟨ reducible-⊩≡ ⟩
    (∃ λ l → ∇ » Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ≡ C)     →⟨ Σ.map idᶠ (Σ.map idᶠ proj₁) ∘→ proj₂ ∘→ proj₂ ∘→ ⊩ΠΣ≡⇔ .proj₁ ∘→ proj₂ ⟩
    (∃₂ λ A′ B′ → ∇ » Γ ⊢ C ⇒* ΠΣ⟨ b ⟩ p , q ▷ A′ ▹ B′)  →⟨ Σ.map idᶠ $ Σ.map idᶠ (flip whnfRed* C-whnf) ⟩
    (∃₂ λ A′ B′ → C PE.≡ ΠΣ⟨ b ⟩ p , q ▷ A′ ▹ B′)        □

opaque

  -- If equality reflection is allowed, then there is a WHNF C that is
  -- judgementally equal to ΠΣ⟨ b ⟩ p , q ▷ A ▹ B but not
  -- propositionally equal to any Π- or Σ-type (given a certain
  -- assumption).

  whnf≢ΠΣ :
    Equality-reflection →
    ΠΣ-allowed b p q →
    » ∇ →
    ∃₄ λ (Γ : Con Term 1) A B C →
      ∇ » Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ≡ C × Whnf ∇ C ×
      ¬ ∃₅ λ b p q A B → C PE.≡ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B
  whnf≢ΠΣ {b} {p} {q} ok₁ ok₂ »∇ =
    ε ∙ Id (U 0) (ΠΣ⟨ b ⟩ p , q ▷ ℕ ▹ ℕ) ℕ ,
    ℕ , ℕ , ℕ ,
    univ
      (equality-reflection′ ok₁ $
       let ⊢ε = ε »∇ in
       var₀ (Idⱼ′ (ΠΣⱼ (ℕⱼ ⊢ε) (ℕⱼ (∙ ℕⱼ ⊢ε)) ok₂) (ℕⱼ ⊢ε))) ,
    ℕₙ ,
    (λ ())

opaque

  -- If a WHNF A is definitionally equal to Π p , q ▷ B ▹ C, then A
  -- has the shape Π p , q ▷ _ ▹ _ (given a certain assumption).

  Π≡A :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    ∇ » Γ ⊢ Π p , q ▷ B ▹ C ≡ A → Whnf ∇ A →
    ∃₂ λ B′ C′ → A PE.≡ Π p , q ▷ B′ ▹ C′
  Π≡A = ΠΣ≡Whnf

opaque

  -- If a WHNF A is definitionally equal to Σ⟨ s ⟩ p , q ▷ B ▹ C, then
  -- A has the shape Σ⟨ s ⟩ p , q ▷ _ ▹ _ (given a certain
  -- assumption).

  Σ≡A :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    ∇ » Γ ⊢ Σ⟨ s ⟩ p , q ▷ B ▹ C ≡ A → Whnf ∇ A →
    ∃₂ λ B′ C′ → A PE.≡ Σ⟨ s ⟩ p , q ▷ B′ ▹ C′
  Σ≡A = ΠΣ≡Whnf

opaque

  -- If the WHNF B is judgmentally equal to Id A t u, then there are
  -- A′, t′ and u′ such that B is propositionally equal to Id A′ t′ u′
  -- (given a certain assumption).

  Id≡Whnf :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    ∇ » Γ ⊢ Id A t u ≡ B → Whnf ∇ B →
    ∃₃ λ A′ t′ u′ → B PE.≡ Id A′ t′ u′
  Id≡Whnf {Γ} {∇} {A} {t} {u} {B} Id≡B B-whnf =
                                                $⟨ Id≡B ⟩
    ∇ » Γ ⊢ Id A t u ≡ B                        →⟨ reducible-⊩≡ ⟩
    (∃ λ l → ∇ » Γ ⊩⟨ l ⟩ Id A t u ≡ B)         →⟨ Σ.map idᶠ (Σ.map idᶠ (Σ.map idᶠ proj₁)) ∘→ proj₂ ∘→ ⊩Id≡⇔ .proj₁ ∘→ proj₂ ⟩
    (∃₃ λ A′ t′ u′ → ∇ » Γ ⊢ B ⇒* Id A′ t′ u′)  →⟨ Σ.map idᶠ $ Σ.map idᶠ $ Σ.map idᶠ (flip whnfRed* B-whnf) ⟩
    (∃₃ λ A′ t′ u′ → B PE.≡ Id A′ t′ u′)        □

opaque

  -- If equality reflection is allowed, then there is a WHNF B that is
  -- judgementally equal to Id A t u but not propositionally equal to
  -- any identity type.

  whnf≢Id :
    Equality-reflection →
    » ∇ →
    ∃₅ λ (Γ : Con Term 1) A t u B →
      ∇ » Γ ⊢ Id A t u ≡ B × Whnf ∇ B ×
      ¬ ∃₃ λ A t u → B PE.≡ Id A t u
  whnf≢Id ok »∇ =
    ε ∙ Id (U 0) (Id ℕ zero zero) ℕ ,
    ℕ , zero , zero , ℕ ,
    univ
      (equality-reflection′ ok $
       let ⊢ε = ε »∇ in
       var₀ (Idⱼ′ (Idⱼ (ℕⱼ ⊢ε) (zeroⱼ ⊢ε) (zeroⱼ ⊢ε)) (ℕⱼ ⊢ε))) ,
    ℕₙ ,
    (λ ())

opaque

  -- If t is definitionally equal to rfl, then t reduces to rfl (given
  -- a certain assumption).

  rfl-norm :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    ∇ » Γ ⊢ t ≡ rfl ∷ A → ∇ » Γ ⊢ t ⇒* rfl ∷ A
  rfl-norm t≡rfl =
    case inversion-rfl (syntacticEqTerm t≡rfl .proj₂ .proj₂) of λ
      (_ , _ , _ , _ , A≡Id) →
    case ⊩≡∷Id⇔ .proj₁ $ proj₂ $ reducible-⊩≡∷ $
         conv t≡rfl A≡Id of λ
      (t′ , _ , t⇒*u , rfl⇒*v , _ , _ , u∼v) →
    case whnfRed*Term rfl⇒*v rflₙ of λ {
      PE.refl →
    case u∼v of λ where
      (rfl₌ _) →
        conv* t⇒*u (sym A≡Id)
      (ne _ () _) }

opaque

  -- If equality reflection is allowed, then there is a term that is
  -- judgementally equal to rfl but that does not reduce to rfl.

  rfl-not-norm :
    Equality-reflection →
    » ∇ →
    ∃₃ λ (Γ : Con Term 2) A t →
      ∇ » Γ ⊢ t ≡ rfl ∷ A × ¬ ∃₂ λ Δ B → ∇ » Δ ⊢ t ⇒* rfl ∷ B
  rfl-not-norm ok »∇ =
    let ⊢Id = Idⱼ′ (zeroⱼ (ε »∇)) (zeroⱼ (ε »∇)) in
    ε ∙ Id ℕ zero zero ∙ Id (Id ℕ zero zero) (var x0) rfl ,
    Id ℕ zero zero , var x1 ,
    (equality-reflection′ ok $
     var₀ (Idⱼ′ (var₀ ⊢Id) (rflⱼ (zeroⱼ (∙ ⊢Id))))) ,
    (λ { (_ , _ , x1⇒ ⇨ _) → neRedTerm x1⇒ (var⁺ _) })

opaque

  -- If the WHNF t is judgmentally equal to rfl, then t is
  -- propositionally equal to rfl (given a certain assumption).

  whnf≡rfl :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    ∇ » Γ ⊢ t ≡ rfl ∷ A → Whnf ∇ t → t PE.≡ rfl
  whnf≡rfl = whnfRed*Term ∘→ rfl-norm

opaque

  -- If equality reflection is allowed, then there is a WHNF t that is
  -- judgementally equal to rfl but not propositionally equal to rfl.

  whnf≢rfl :
    Equality-reflection →
    » ∇ →
    ∃₃ λ (Γ : Con Term 2) A t →
      ∇ » Γ ⊢ t ≡ rfl ∷ A × Whnf ∇ t × t PE.≢ rfl
  whnf≢rfl ok »∇ =
    let ⊢Id = Idⱼ′ (zeroⱼ (ε »∇)) (zeroⱼ (ε »∇)) in
    ε ∙ Id ℕ zero zero ∙ Id (Id ℕ zero zero) (var x0) rfl ,
    Id ℕ zero zero , var x1 ,
    (equality-reflection′ ok $
     var₀ (Idⱼ′ (var₀ ⊢Id) (rflⱼ (zeroⱼ (∙ ⊢Id))))) ,
    ne (var⁺ _) ,
    (λ ())
