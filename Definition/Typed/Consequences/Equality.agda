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
open import Definition.Untyped.Neutral M type-variant
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
    Γ         : Con Term _
    A B C l t u : Term _
    b         : BinderMode
    p q       : M
    s         : Strength

opaque

  -- If the WHNF A is judgmentally equal to Level, then A is
  -- propositionally equal to Level (given a certain assumption).

  Level≡A :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Γ ⊢ Level ≡ A → Whnf A → A PE.≡ Level
  Level≡A {Γ} {A} Level≡A A-whnf =
                $⟨ Level≡A ⟩
    Γ ⊢ Level ≡ A       →⟨ ⊩Level≡⇔ .proj₁ ∘→ proj₂ ∘→ reducible-⊩≡ ⟩
    Γ ⊩Level Level ≡ A  ≡⟨ PE.refl ⟩→
    Γ ⊢ A ⇒* Level      →⟨ flip whnfRed* A-whnf ⟩
    A PE.≡ Level        □

opaque

  -- If equality reflection is allowed and Level is a small type, then
  -- there is a WHNF A that is judgementally equal to Level but not
  -- propositionally equal to Level.

  whnf≢Level :
    Equality-reflection →
    Level-is-small →
    ∃₂ λ (Γ : Con Term 1) (A : Term 1) →
      Γ ⊢ Level ≡ A × Whnf A × A PE.≢ Level
  whnf≢Level ok Level-ok =
    ε ∙ Id (U zeroᵘ) Level Empty ,
    Empty ,
    univ
      (equality-reflection′ ok $
       var₀ (Idⱼ′ (Levelⱼ ε Level-ok) (Emptyⱼ ε))) ,
    Emptyₙ ,
    (λ ())

opaque

  -- If the WHNF A is judgmentally equal to U l, then A is
  -- propositionally equal to U l (given a certain assumption).

  U≡A :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Γ ⊢ U l ≡ A → Whnf A → ∃ λ k → A PE.≡ U k
  U≡A {Γ} {l} {A} U≡A A-whnf =    $⟨ U≡A ⟩
    Γ ⊢ U l ≡ A                   →⟨ reducible-⊩≡ ⟩
    (∃ λ l′ → Γ ⊩⟨ l′ ⟩ U l ≡ A)  →⟨ (λ (_ , U≡A) → let (_ , _ , u , d , _) = ⊩U≡⇔ .proj₁ U≡A in u , d) ⟩
    (∃ λ k → Γ ⊢ A ⇒* U k)        →⟨ Σ.map idᶠ (flip whnfRed* A-whnf) ⟩
    (∃ λ k → A PE.≡ U k)          □

opaque

  -- If equality reflection is allowed, then there is a WHNF A that is
  -- judgementally equal to a universe but not propositionally
  -- equal to any universe (given a certain assumption).

  whnf≢U :
    Equality-reflection →
    Unitʷ-allowed →
    ∃₃ λ (Γ : Con Term 1) (l : Term 1) (A : Term 1) →
      Γ ⊢ U l ≡ A × Whnf A × ¬ ∃ λ l → A PE.≡ U l
  whnf≢U ok₁ ok₂ =
    ε ∙ Id (U (sucᵘ zeroᵘ)) (U zeroᵘ) (Lift (sucᵘ zeroᵘ) Empty) ,
    zeroᵘ ,
    Lift (sucᵘ zeroᵘ) Empty ,
    univ
      (equality-reflection′ ok₁ $
       var₀ $
       Idⱼ′
         (Uⱼ (⊢zeroᵘ ε))
         (_⊢_∷_.conv (Liftⱼ′ (⊢sucᵘ (⊢zeroᵘ ε)) (Emptyⱼ ε)) $
          U-cong-⊢≡ (supᵘₗ-zeroˡ (⊢sucᵘ (⊢zeroᵘ ε))))) ,
    Liftₙ ,
    (λ ())

opaque

  -- If the WHNF A is judgmentally equal to Lift l B, then A is
  -- propositionally equal to Lift l B (given a certain assumption).

  Lift≡A :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Γ ⊢ Lift l B ≡ A → Whnf A → ∃₂ λ k C → A PE.≡ Lift k C
  Lift≡A {Γ} {l} {B} {A} Lift≡A A-whnf = $⟨ Lift≡A ⟩
    Γ ⊢ Lift l B ≡ A                     →⟨ reducible-⊩≡ ⟩
    (∃ λ l′ → Γ ⊩⟨ l′ ⟩ Lift l B ≡ A)    →⟨ (λ (_ , Lift≡A) → let _ , _ , D , _ = ⊩Lift≡⇔ .proj₁ Lift≡A in _ , _ , D) ⟩
    (∃₂ λ k C → Γ ⊢ A ⇒* Lift k C)       →⟨ Σ.map idᶠ $ Σ.map idᶠ (flip whnfRed* A-whnf) ⟩
    (∃₂ λ k C → A PE.≡ Lift k C)         □

opaque

  -- If equality reflection is allowed, then there is a WHNF A that is
  -- judgementally equal to a Lift type but not propositionally
  -- equal to any Lift type (given a certain assumption).

  whnf≢Lift :
    Equality-reflection →
    Unitʷ-allowed →
    ∃₄ λ (Γ : Con Term 1) (l : Term 1) (B : Term 1) (A : Term 1) →
      Γ ⊢ Lift l B ≡ A × Whnf A × ¬ ∃₂ λ l B → A PE.≡ Lift l B
  whnf≢Lift ok₁ ok₂ =
    ε ∙ Id (U (zeroᵘ supᵘₗ zeroᵘ)) (Lift zeroᵘ ℕ) Unitʷ ,
    zeroᵘ ,
    ℕ ,
    Unitʷ ,
    univ
      (equality-reflection′ ok₁ $
       var₀ $
       Idⱼ′ (Liftⱼ′ (⊢zeroᵘ ε) (ℕⱼ ε)) $
       _⊢_∷_.conv (Unitⱼ ε ok₂) $
       U-cong-⊢≡ (sym-⊢≡∷L (supᵘₗ-zeroˡ (⊢zeroᵘ ε)))) ,
    Unitₙ ,
    (λ ())

opaque

  -- If the WHNF A is judgmentally equal to ℕ, then A is
  -- propositionally equal to ℕ (given a certain assumption).

  ℕ≡A :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Γ ⊢ ℕ ≡ A → Whnf A → A PE.≡ ℕ
  ℕ≡A {Γ} {A} ℕ≡A A-whnf =
                $⟨ ℕ≡A ⟩
    Γ ⊢ ℕ ≡ A   →⟨ ⊩ℕ≡⇔ .proj₁ ∘→ proj₂ ∘→ reducible-⊩≡ ⟩
    Γ ⊩ℕ ℕ ≡ A  ≡⟨ PE.refl ⟩→
    Γ ⊢ A ⇒* ℕ  →⟨ flip whnfRed* A-whnf ⟩
    A PE.≡ ℕ    □

opaque

  -- If equality reflection is allowed, then there is a WHNF A that is
  -- judgementally equal to ℕ but not propositionally equal to ℕ.

  whnf≢ℕ :
    Equality-reflection →
    ∃₂ λ (Γ : Con Term 1) (A : Term 1) →
      Γ ⊢ ℕ ≡ A × Whnf A × A PE.≢ ℕ
  whnf≢ℕ ok =
    ε ∙ Id (U zeroᵘ) ℕ Empty ,
    Empty ,
    univ
      (equality-reflection′ ok $
       var₀ (Idⱼ′ (ℕⱼ ε) (Emptyⱼ ε))) ,
    Emptyₙ ,
    (λ ())

opaque

  -- If the WHNF A is judgmentally equal to Empty, then A is
  -- propositionally equal to Empty (given a certain assumption).

  Empty≡A :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Γ ⊢ Empty ≡ A → Whnf A → A PE.≡ Empty
  Empty≡A {Γ} {A} Empty≡A A-whnf =
                        $⟨ Empty≡A ⟩
    Γ ⊢ Empty ≡ A       →⟨ ⊩Empty≡⇔ .proj₁ ∘→ proj₂ ∘→ reducible-⊩≡ ⟩
    Γ ⊩Empty Empty ≡ A  ≡⟨ PE.refl ⟩→
    Γ ⊢ A ⇒* Empty      →⟨ flip whnfRed* A-whnf ⟩
    A PE.≡ Empty        □

opaque

  -- If equality reflection is allowed, then there is a WHNF A that is
  -- judgementally equal to Empty but not propositionally equal
  -- to Empty.

  whnf≢Empty :
    Equality-reflection →
    ∃₂ λ (Γ : Con Term 1) (A : Term 1) →
      Γ ⊢ Empty ≡ A × Whnf A × A PE.≢ Empty
  whnf≢Empty ok =
    ε ∙ Id (U zeroᵘ) Empty ℕ ,
    ℕ ,
    univ
      (equality-reflection′ ok $
       var₀ (Idⱼ′ (Emptyⱼ ε) (ℕⱼ ε))) ,
    ℕₙ ,
    (λ ())

opaque

  -- If the WHNF A is judgmentally equal to Unit s l, then A is
  -- propositionally equal to Unit s l (given a certain assumption).

  Unit≡A :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Γ ⊢ Unit s ≡ A → Whnf A → A PE.≡ Unit s
  Unit≡A {Γ} {s} {A} Unit≡A A-whnf =
                                       $⟨ Unit≡A ⟩
    Γ ⊢ Unit s ≡ A                   →⟨ reducible-⊩≡ ⟩
    (∃ λ l′ → Γ ⊩⟨ l′ ⟩ Unit s ≡ A)  →⟨ (λ (_ , Unit≡A) →
                                            case ⊩Unit≡⇔ .proj₁ Unit≡A of λ {
                                              (⇒Unit , ok) →
                                            ⇒Unit }) ⟩
    Γ ⊢ A ⇒* Unit s        →⟨ flip whnfRed* A-whnf ⟩
    A PE.≡ Unit s          □

opaque

  -- If equality reflection is allowed, then there is a WHNF A that is
  -- judgementally equal to a unit type but not propositionally equal
  -- to any unit type (given a certain assumption).

  whnf≢Unit :
    Equality-reflection →
    Unit-allowed s →
    ∃₃ λ (Γ : Con Term 1) (l : Term 1) (A : Term 1) →
      Γ ⊢ Unit s ≡ A × Whnf A ×
      ¬ ∃ λ s → A PE.≡ Unit s
  whnf≢Unit {s} ok₁ ok₂ =
    ε ∙ Id (U zeroᵘ) (Unit s) (Id (Unit s) (star s) (star s)) ,
    zeroᵘ ,
    Id (Unit s) (star s) (star s) ,
    univ
      (equality-reflection′ ok₁ $ var₀ $
       Idⱼ′ (Unitⱼ ε ok₂) $ Idⱼ (Unitⱼ ε ok₂) (starⱼ ε ok₂) (starⱼ ε ok₂)) ,
    Idₙ ,
    (λ ())

opaque

  -- If the neutral term B is judgmentally equal to the WHNF A, then A
  -- is neutral (given a certain assumption).

  ne≡A :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Neutral B → Γ ⊢ B ≡ A → Whnf A → Neutral A
  ne≡A {Γ} {B} {A} B-ne B≡A A-whnf =  $⟨ B≡A ⟩
    Γ ⊢ B ≡ A                         →⟨ reducible-⊩≡ ⟩
    (∃ λ l → Γ ⊩⟨ l ⟩ B ≡ A)          →⟨ Σ.map idᶠ (Σ.map idᶠ proj₁) ∘→ proj₂ ∘→ ⊩ne≡⇔ B-ne .proj₁ ∘→ proj₂ ⟩
    (∃ λ C → Neutral C × Γ ⊢ A ⇒* C)  →⟨ (λ (_ , C-ne , A⇒*C) →
                                            PE.subst Neutral (PE.sym $ whnfRed* A⇒*C A-whnf) C-ne) ⟩
    Neutral A                         □

opaque

  -- If equality reflection is allowed, then there is a WHNF B that is
  -- judgementally equal (as a type) to a neutral term A but not
  -- propositionally equal to A.

  whnf≢ne :
    Equality-reflection →
    ∃₃ λ (Γ : Con Term 2) (A B : Term 2) →
      Γ ⊢ A ≡ B × Neutral A × Whnf B × A PE.≢ B
  whnf≢ne ok =
    ε ∙ U zeroᵘ ∙ Id (U zeroᵘ) (var x0) Empty ,
    var x1 ,
    Empty ,
    univ
      (equality-reflection′ ok $
       var₀ (Idⱼ′ (var₀ (⊢U₀ ε)) (Emptyⱼ (∙ ⊢U₀ ε)))) ,
    var _ ,
    Emptyₙ ,
    (λ ())

opaque

  -- If a WHNF C is definitionally equal to ΠΣ⟨ b ⟩ p , q ▷ A ▹ B,
  -- then C has the shape ΠΣ⟨ b ⟩ p , q ▷ _ ▹ _ (given a certain
  -- assumption).

  ΠΣ≡Whnf :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ≡ C → Whnf C →
    ∃₂ λ A′ B′ → C PE.≡ ΠΣ⟨ b ⟩ p , q ▷ A′ ▹ B′
  ΠΣ≡Whnf {Γ} {b} {p} {q} {A} {B} {C} ΠΣ≡C C-whnf =  $⟨ ΠΣ≡C ⟩
    Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ≡ C                    →⟨ reducible-⊩≡ ⟩
    (∃ λ l → Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ≡ C)     →⟨ Σ.map idᶠ (Σ.map idᶠ proj₁) ∘→ proj₂ ∘→ proj₂ ∘→ ⊩ΠΣ≡⇔ .proj₁ ∘→ proj₂ ⟩
    (∃₂ λ A′ B′ → Γ ⊢ C ⇒* ΠΣ⟨ b ⟩ p , q ▷ A′ ▹ B′)  →⟨ Σ.map idᶠ $ Σ.map idᶠ (flip whnfRed* C-whnf) ⟩
    (∃₂ λ A′ B′ → C PE.≡ ΠΣ⟨ b ⟩ p , q ▷ A′ ▹ B′)    □

opaque

  -- If equality reflection is allowed, then there is a WHNF C that is
  -- judgementally equal to ΠΣ⟨ b ⟩ p , q ▷ A ▹ B but not
  -- propositionally equal to any Π- or Σ-type (given a certain
  -- assumption).

  whnf≢ΠΣ :
    Equality-reflection →
    ΠΣ-allowed b p q →
    ∃₄ λ (Γ : Con Term 1) A B C →
      Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ≡ C × Whnf C ×
      ¬ ∃₅ λ b p q A B → C PE.≡ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B
  whnf≢ΠΣ {b} {p} {q} ok₁ ok₂ =
    ε ∙ Id (U zeroᵘ) (ΠΣ⟨ b ⟩ p , q ▷ ℕ ▹ ℕ) ℕ ,
    ℕ , ℕ , ℕ ,
    univ
      (equality-reflection′ ok₁ $
       var₀ (Idⱼ′ (ΠΣⱼ (⊢zeroᵘ ε) (ℕⱼ ε) (ℕⱼ (∙ ⊢ℕ ε)) ok₂) (ℕⱼ ε))) ,
    ℕₙ ,
    (λ ())

opaque

  -- If a WHNF A is definitionally equal to Π p , q ▷ B ▹ C, then A
  -- has the shape Π p , q ▷ _ ▹ _ (given a certain assumption).

  Π≡A :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Γ ⊢ Π p , q ▷ B ▹ C ≡ A → Whnf A →
    ∃₂ λ B′ C′ → A PE.≡ Π p , q ▷ B′ ▹ C′
  Π≡A = ΠΣ≡Whnf

opaque

  -- If a WHNF A is definitionally equal to Σ⟨ s ⟩ p , q ▷ B ▹ C, then
  -- A has the shape Σ⟨ s ⟩ p , q ▷ _ ▹ _ (given a certain
  -- assumption).

  Σ≡A :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Γ ⊢ Σ⟨ s ⟩ p , q ▷ B ▹ C ≡ A → Whnf A →
    ∃₂ λ B′ C′ → A PE.≡ Σ⟨ s ⟩ p , q ▷ B′ ▹ C′
  Σ≡A = ΠΣ≡Whnf

opaque

  -- If the WHNF B is judgmentally equal to Id A t u, then there are
  -- A′, t′ and u′ such that B is propositionally equal to Id A′ t′ u′
  -- (given a certain assumption).

  Id≡Whnf :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Γ ⊢ Id A t u ≡ B → Whnf B →
    ∃₃ λ A′ t′ u′ → B PE.≡ Id A′ t′ u′
  Id≡Whnf {Γ} {A} {t} {u} {B} Id≡B B-whnf =
                                            $⟨ Id≡B ⟩
    Γ ⊢ Id A t u ≡ B                        →⟨ reducible-⊩≡ ⟩
    (∃ λ l → Γ ⊩⟨ l ⟩ Id A t u ≡ B)         →⟨ Σ.map idᶠ (Σ.map idᶠ (Σ.map idᶠ proj₁)) ∘→ proj₂ ∘→ ⊩Id≡⇔ .proj₁ ∘→ proj₂ ⟩
    (∃₃ λ A′ t′ u′ → Γ ⊢ B ⇒* Id A′ t′ u′)  →⟨ Σ.map idᶠ $ Σ.map idᶠ $ Σ.map idᶠ (flip whnfRed* B-whnf) ⟩
    (∃₃ λ A′ t′ u′ → B PE.≡ Id A′ t′ u′)    □

opaque

  -- If equality reflection is allowed, then there is a WHNF B that is
  -- judgementally equal to Id A t u but not propositionally equal to
  -- any identity type.

  whnf≢Id :
    Equality-reflection →
    ∃₅ λ (Γ : Con Term 1) A t u B →
      Γ ⊢ Id A t u ≡ B × Whnf B ×
      ¬ ∃₃ λ A t u → B PE.≡ Id A t u
  whnf≢Id ok =
    ε ∙ Id (U zeroᵘ) (Id ℕ zero zero) ℕ ,
    ℕ , zero , zero , ℕ ,
    univ
      (equality-reflection′ ok $
       var₀ (Idⱼ′ (Idⱼ (ℕⱼ ε) (zeroⱼ ε) (zeroⱼ ε)) (ℕⱼ ε))) ,
    ℕₙ ,
    (λ ())

opaque

  -- If t is definitionally equal to rfl, then t reduces to rfl (given
  -- a certain assumption).

  rfl-norm :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Γ ⊢ t ≡ rfl ∷ A → Γ ⊢ t ⇒* rfl ∷ A
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
      (ne _ _ () _) }

opaque

  -- If equality reflection is allowed, then there is a term that is
  -- judgementally equal to rfl but that does not reduce to rfl.

  rfl-not-norm :
    Equality-reflection →
    ∃₃ λ (Γ : Con Term 2) A t →
      Γ ⊢ t ≡ rfl ∷ A × ¬ ∃₂ λ Δ B → Δ ⊢ t ⇒* rfl ∷ B
  rfl-not-norm ok =
    let ⊢Id = Idⱼ′ (zeroⱼ ε) (zeroⱼ ε) in
    ε ∙ Id ℕ zero zero ∙ Id (Id ℕ zero zero) (var x0) rfl ,
    Id ℕ zero zero , var x1 ,
    (equality-reflection′ ok $
     var₀ (Idⱼ′ (var₀ ⊢Id) (rflⱼ (zeroⱼ (∙ ⊢Id))))) ,
    (λ { (_ , _ , x1⇒ ⇨ _) → neRedTerm x1⇒ (var _) })

opaque

  -- If the WHNF t is judgmentally equal to rfl, then t is
  -- propositionally equal to rfl (given a certain assumption).

  whnf≡rfl :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Γ ⊢ t ≡ rfl ∷ A → Whnf t → t PE.≡ rfl
  whnf≡rfl = whnfRed*Term ∘→ rfl-norm

opaque

  -- If equality reflection is allowed, then there is a WHNF t that is
  -- judgementally equal to rfl but not propositionally equal to rfl.

  whnf≢rfl :
    Equality-reflection →
    ∃₃ λ (Γ : Con Term 2) A t →
      Γ ⊢ t ≡ rfl ∷ A × Whnf t × t PE.≢ rfl
  whnf≢rfl ok =
    let ⊢Id = Idⱼ′ (zeroⱼ ε) (zeroⱼ ε) in
    ε ∙ Id ℕ zero zero ∙ Id (Id ℕ zero zero) (var x0) rfl ,
    Id ℕ zero zero , var x1 ,
    (equality-reflection′ ok $
     var₀ (Idⱼ′ (var₀ ⊢Id) (rflⱼ (zeroⱼ (∙ ⊢Id))))) ,
    ne! (var _) ,
    (λ ())
