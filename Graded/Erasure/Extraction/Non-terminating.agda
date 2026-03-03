------------------------------------------------------------------------
-- If the extraction function uses strict applications and removes
-- erasable arguments entirely, then it may be the case that
-- well-typed and well-resourced terms extract to terms that do not
-- terminate
------------------------------------------------------------------------

-- In "A New Extraction for Coq" Letouzey points out that uses of the
-- eliminator for the empty type False can lead to problems similar to
-- the one presented below if all logical arguments are removed
-- entirely, given that the eliminator is replaced with code that
-- throws an exception. However, the example discussed below does not
-- rely on how emptyrec is extracted, but is more similar to one in
-- Mishra-Linger's PhD thesis (see Figure 5.1).
--
-- The example looks roughly like this:
--
--   (λ^ω _. zero)
--     (λ⁰ (bot : ⊥).
--        (λ^ω+ω x. cast bot x x) (cast bot (λ^ω+ω x. cast bot x x)))
--
-- If erased arguments are removed entirely, then we end up with a
-- term like the following one:
--
--   (λ _. zero) ((λ x. x x) (λ x. x x))
--
-- If strict applications are used, then this program does not
-- terminate.

open import Graded.Modality
open import Graded.Mode.Instances.Zero-one.Variant
import Graded.Mode.Instances.Zero-one
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions

module Graded.Erasure.Extraction.Non-terminating
  {a} {M : Set a}
  {𝕄 : Modality M}
  {variant : Mode-variant 𝕄}
  (open Graded.Mode.Instances.Zero-one variant)
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions 𝕄 Zero-one-isMode)
  where

open Modality 𝕄
open Type-restrictions TR
open Usage-restrictions UR

open import Definition.Typed TR
open import Definition.Typed.Properties TR hiding (⊢cast)
open import Definition.Untyped M
open import Definition.Untyped.Identity 𝕄 hiding (cast)

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Derived.Identity UR
open import Graded.Erasure.Extraction 𝕄
open import Graded.Erasure.Extraction.Properties 𝕄
open import Graded.Erasure.Target as T using (Strictness; strict)
open import Graded.Erasure.Target.Non-terminating
open import Graded.Erasure.Target.Properties
open import Graded.Modality.Properties 𝕄
open import Graded.Usage UR
open import Graded.Usage.Properties UR
open import Graded.Usage.Properties.Zero-one variant UR

open import Tools.Bool using (Bool; true)
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.List using (List)
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
open import Tools.PropositionalEquality as PE using (_≡_; _≢_)
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation

private variable
  b           : Bool
  n           : Nat
  Γ           : Cons _ _
  A B t u     : Term _
  γ₁ γ₂ γ₃ γ₄ : Conₘ _
  p q         : M
  v           : T.Term _
  vs          : List (T.Term _)
  s           : Strictness

-- Some lemmas used below.

private module Lemmas (⊢Γ : ⊢ Γ) where opaque

  Empty⊢ℕ∷U : Γ »∙ Empty ⊢ ℕ ∷ U zeroᵘ
  Empty⊢ℕ∷U = ℕⱼ (⊢Γ ∙[ ⊢Empty ])

  Empty⊢ℕ : Γ »∙ Empty ⊢ ℕ
  Empty⊢ℕ = univ Empty⊢ℕ∷U

  Empty∙ℕ⊢ℕ∷U : Γ »∙ Empty »∙ ℕ ⊢ ℕ ∷ U zeroᵘ
  Empty∙ℕ⊢ℕ∷U = ℕⱼ (⊢Γ ∙[ ⊢Empty ] ∙[ ⊢ℕ ])

  Empty∙ℕ∙ℕ⊢ℕ∷U : Γ »∙ Empty »∙ ℕ »∙ ℕ ⊢ ℕ ∷ U zeroᵘ
  Empty∙ℕ∙ℕ⊢ℕ∷U = ℕⱼ (⊢Γ ∙[ ⊢Empty ] ∙[ ⊢ℕ ] ∙[ ⊢ℕ ])

opaque

  -- Another lemma used below.

  ▸Πℕℕ : q ≤ 𝟘 → 𝟘ᶜ {n = n} ▸[ 𝟙ᵐ ] Π p , q ▷ ℕ ▹ ℕ
  ▸Πℕℕ {q} {p} q≤𝟘 = sub
    (ΠΣₘ ℕₘ $ sub ℕₘ $ begin
        𝟘ᶜ ∙ 𝟙 · q  ≈⟨ ≈ᶜ-refl ∙ ·-identityˡ _ ⟩
        𝟘ᶜ ∙ q      ≤⟨ ≤ᶜ-refl ∙ q≤𝟘 ⟩
        𝟘ᶜ          ∎)
    (begin
       𝟘ᶜ             ≈˘⟨ +ᶜ-identityʳ _ ⟩
       𝟘ᶜ +ᶜ 𝟘ᶜ       ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
       p ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎)
    where
    open ≤ᶜ-reasoning

------------------------------------------------------------------------
-- The term former cast

opaque

  -- A cast lemma.

  cast : Term n → Term n → Term n → Term n → Term n
  cast t A B u =
    subst 𝟙 (U zeroᵘ) (var x0) A B (emptyrec 𝟘 (Id (U zeroᵘ) A B) t) u

opaque
  unfolding cast subst

  -- An extraction lemma for cast.

  erase-cast : erase′ b s (cast t A B u) ≡ erase′ b s u
  erase-cast = PE.refl

opaque
  unfolding cast

  -- A typing rule for cast.

  ⊢cast :
    Γ ⊢ t ∷ Empty →
    Γ ⊢ A ∷ U zeroᵘ →
    Γ ⊢ B ∷ U zeroᵘ →
    Γ ⊢ u ∷ A →
    Γ ⊢ cast t A B u ∷ B
  ⊢cast ⊢t ⊢A ⊢B =
    ⊢subst (univ $ var₀ $ ⊢U₀ (wfTerm ⊢t)) (emptyrecⱼ (Idⱼ′ ⊢A ⊢B) ⊢t)

opaque
  unfolding cast

  -- A usage rule for cast.

  ▸cast :
    Emptyrec-allowed 𝟙ᵐ 𝟘 →
    γ₁ ▸[ 𝟘ᵐ? ] t →
    γ₂ ▸[ 𝟙ᵐ ] A →
    γ₃ ▸[ 𝟙ᵐ ] B →
    γ₄ ▸[ 𝟙ᵐ ] u →
    ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄) ▸[ 𝟙ᵐ ] cast t A B u
  ▸cast {γ₁} {γ₂} {γ₃} {γ₄} ok ▸t ▸A ▸B ▸u =
    sub (▸subst (Uₘ zeroᵘₘ)
           (sub var $ begin
              𝟘ᶜ ∙ 𝟙 · 𝟙   ≈⟨ ≈ᶜ-refl ∙ ·-identityʳ _ ⟩
              𝟘ᶜ , x0 ≔ 𝟙  ∎)
           ▸A ▸B
           (emptyrecₘ (▸-cong (PE.sym ⌞𝟘⌟≡𝟘ᵐ?) ▸t)
              (Idₘ-generalised (Uₘ zeroᵘₘ) (▸-𝟘ᵐ? ▸A .proj₂)
                 (▸-𝟘ᵐ? ▸B .proj₂)
                 (λ _ → ∧ᶜ-decreasingˡ 𝟘ᶜ _)
                 (λ _ → ∧ᶜ-decreasingʳ _ _))
              ok)
           ▸u)
    (begin
       ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄)                   ≈˘⟨ ·ᶜ-congˡ $
                                                   ≈ᶜ-trans (+ᶜ-identityˡ _) $
                                                   +ᶜ-congˡ $
                                                   +ᶜ-congˡ $
                                                   ≈ᶜ-trans (+ᶜ-congʳ $ ·ᶜ-zeroˡ _) $
                                                   +ᶜ-identityˡ _ ⟩
       ω ·ᶜ (𝟘ᶜ +ᶜ γ₂ +ᶜ γ₃ +ᶜ 𝟘 ·ᶜ γ₁ +ᶜ γ₄)  ∎)
    where
    open ≤ᶜ-reasoning

------------------------------------------------------------------------
-- The term former λx∙xx

opaque

  -- A term that is roughly "λ x. x x".

  λx∙xx : M → Term (1+ n)
  λx∙xx p =
    lam (ω + ω) $
    cast (var x1) ℕ (Π ω , p ▷ ℕ ▹ ℕ) (var x0) ∘⟨ ω ⟩ var x0

opaque
  unfolding λx∙xx

  -- An extraction lemma for λx∙xx.

  erase-λx∙xx :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero M 𝕄 ⦄ →
    erase′ b s (λx∙xx {n = n} p) ≡
    T.lam (T.var x0 T.∘⟨ s ⟩ T.var x0)
  erase-λx∙xx {b} {s} {p} =
    erase′ b s (λx∙xx p)                                          ≡⟨ lam-≢𝟘 b (ω≢𝟘 ∘→ proj₁ ∘→ +-positive) ⟩

    T.lam
      (erase′ b s $
       cast (var x1) ℕ (Π ω , p ▷ ℕ ▹ ℕ) (var x0) ∘⟨ ω ⟩ var x0)  ≡⟨ PE.cong T.lam $ ∘-≢𝟘 ω≢𝟘 ⟩

    T.lam
      (erase′ b s
         (cast (var x1) ℕ (Π ω , p ▷ ℕ ▹ ℕ) (var x0))
         T.∘⟨ s ⟩ T.var x0)                                       ≡⟨ PE.cong (λ t → T.lam (t T.∘⟨ _ ⟩ _)) erase-cast ⟩

    T.lam (T.var x0 T.∘⟨ s ⟩ T.var x0)                            ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque
  unfolding λx∙xx

  -- A typing rule for λx∙xx.

  ⊢λx∙xx :
    Π-allowed ω p →
    Π-allowed (ω + ω) p →
    ⊢ Γ →
    Γ »∙ Empty ⊢ λx∙xx p ∷ Π (ω + ω) , p ▷ ℕ ▹ ℕ
  ⊢λx∙xx ω-ok ω+ω-ok ⊢Γ =
    lamⱼ′ ω+ω-ok $
    ⊢cast (var₁ Empty⊢ℕ) Empty∙ℕ⊢ℕ∷U
      (ΠΣⱼ (⊢zeroᵘ (∙ Empty⊢ℕ)) Empty∙ℕ⊢ℕ∷U Empty∙ℕ∙ℕ⊢ℕ∷U ω-ok)
      (var₀ Empty⊢ℕ) ∘ⱼ
    var₀ Empty⊢ℕ
    where
    open Lemmas ⊢Γ

opaque
  unfolding λx∙xx

  -- A usage rule for λx∙xx.

  ▸λx∙xx :
    Emptyrec-allowed 𝟙ᵐ 𝟘 →
    p ≤ 𝟘 →
    𝟘ᶜ ▸[ 𝟙ᵐ ] λx∙xx {n = n} p
  ▸λx∙xx {p} ok p≤𝟘 =
    lamₘ $ sub (▸cast ok var ℕₘ (▸Πℕℕ p≤𝟘) var ∘ₘ var) $ begin
      𝟘ᶜ ∙ 𝟙 · (ω + ω)                                      ≈⟨ ≈ᶜ-refl ∙ ·-identityˡ _ ⟩
      𝟘ᶜ ∙ ω + ω                                            ≈˘⟨ (≈ᶜ-trans (+ᶜ-cong (·ᶜ-zeroʳ _) (·ᶜ-zeroʳ _)) $
                                                                 +ᶜ-identityˡ _) ∙
                                                                +-cong (·-identityʳ _) ·⌜⌞⌟⌝ ⟩
      ω ·ᶜ 𝟘ᶜ +ᶜ ω ·ᶜ 𝟘ᶜ ∙ ω · 𝟙 + ω · ⌜ ⌞ ω ⌟ ⌝            ≡⟨⟩
      ω ·ᶜ (𝟘ᶜ ∙ 𝟙) +ᶜ ω ·ᶜ (𝟘ᶜ ∙ ⌜ ⌞ ω ⌟ ⌝)                ≈˘⟨ +ᶜ-congʳ $
                                                                ·ᶜ-congˡ $
                                                                ≈ᶜ-trans (+ᶜ-identityˡ _) $
                                                                +ᶜ-identityˡ _ ⟩
      ω ·ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ (𝟘ᶜ ∙ 𝟙)) +ᶜ ω ·ᶜ (𝟘ᶜ ∙ ⌜ ⌞ ω ⌟ ⌝)  ∎
    where
    open ≤ᶜ-reasoning

------------------------------------------------------------------------
-- The term former extracts-to-loop

opaque

  -- A term for which the extraction is loop s (for some s) if
  -- erasable arguments are removed entirely.

  extracts-to-loop : M → Term n
  extracts-to-loop p =
    lam 𝟘 $
    λx∙xx p ∘⟨ ω + ω ⟩ cast (var x0) (Π (ω + ω) , p ▷ ℕ ▹ ℕ) ℕ (λx∙xx p)

opaque
  unfolding extracts-to-loop loop

  -- An extraction lemma for extracts-to-loop.

  erase-extracts-to-loop :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero M 𝕄 ⦄ →
    erase′ true s (extracts-to-loop {n = n} p) ≡ loop s
  erase-extracts-to-loop {s} {p} =
    erase′ true s (extracts-to-loop p)                       ≡⟨ lam-𝟘-remove ⟩

    erase′ true s
      (λx∙xx p ∘⟨ ω + ω ⟩
       cast (var x0) (Π (ω + ω) , p ▷ ℕ ▹ ℕ) ℕ (λx∙xx p))
      T.[ loop s ]₀                                          ≡⟨ PE.cong T._[ _ ] $
                                                                ∘-≢𝟘 (ω≢𝟘 ∘→ proj₁ ∘→ +-positive) ⟩
    erase′ true s (λx∙xx p) T.∘⟨ s ⟩
      erase′ true s
        (cast (var x0) (Π (ω + ω) , p ▷ ℕ ▹ ℕ) ℕ (λx∙xx p))
      T.[ loop s ]₀                                          ≡⟨ PE.cong
                                                                  (λ t → erase′ _ _ (λx∙xx _) T.∘⟨ _ ⟩ t T.[ _ ])
                                                                  erase-cast ⟩
    erase′ true s (λx∙xx p) T.∘⟨ s ⟩
      erase′ true s (λx∙xx p)
      T.[ loop s ]₀                                          ≡⟨ PE.cong (λ t → t T.∘⟨ _ ⟩ t T.[ _ ])
                                                                erase-λx∙xx ⟩
    loop s                                                   ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque
  unfolding extracts-to-loop

  -- A typing rule for extracts-to-loop.

  ⊢extracts-to-loop :
    Π-allowed 𝟘 p →
    Π-allowed ω q →
    Π-allowed (ω + ω) q →
    ⊢ Γ →
    Γ ⊢ extracts-to-loop q ∷ Π 𝟘 , p ▷ Empty ▹ ℕ
  ⊢extracts-to-loop 𝟘-ok ω-ok ω+ω-ok ⊢Γ =
    lamⱼ′ 𝟘-ok $
    ⊢λx∙xx ω-ok ω+ω-ok ⊢Γ ∘ⱼ
    ⊢cast (var₀ (⊢Empty ⊢Γ))
      (ΠΣⱼ (⊢zeroᵘ (∙ ⊢Empty ⊢Γ)) Empty⊢ℕ∷U Empty∙ℕ⊢ℕ∷U ω+ω-ok)
      Empty⊢ℕ∷U (⊢λx∙xx ω-ok ω+ω-ok ⊢Γ)
    where
    open Lemmas ⊢Γ

opaque
  unfolding extracts-to-loop

  -- A usage rule for extracts-to-loop.

  ▸extracts-to-loop :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero M 𝕄 ⦄ →
    Emptyrec-allowed 𝟙ᵐ 𝟘 →
    p ≤ 𝟘 →
    𝟘ᶜ ▸[ 𝟙ᵐ ] extracts-to-loop {n = n} p
  ▸extracts-to-loop {p} {n} ok p≤𝟘 = lamₘ $ sub
    (▸λx∙xx′ ∘ₘ
     sub
       (▸-cong (PE.sym $ ≢𝟘→⌞⌟≡𝟙ᵐ $ ω≢𝟘 ∘→ proj₁ ∘→ +-positive) $
        ▸cast ok var (▸Πℕℕ p≤𝟘) ℕₘ ▸λx∙xx′)
     (let open ≤ᶜ-reasoning in begin
        𝟘ᶜ                     ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
        ω ·ᶜ 𝟘ᶜ                ≈˘⟨ ·ᶜ-congˡ $
                                   ≈ᶜ-trans (+ᶜ-identityˡ _) $
                                   +ᶜ-identityˡ _ ⟩
        ω ·ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ)  ∎))
    (let open ≤ᶜ-reasoning in begin
       𝟘ᶜ ∙ 𝟙 · 𝟘           ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
       𝟘ᶜ                   ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
       (ω + ω) ·ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-identityˡ _ ⟩
       𝟘ᶜ +ᶜ (ω + ω) ·ᶜ 𝟘ᶜ  ∎)
    where
    ▸λx∙xx′ : 𝟘ᶜ ▸[ 𝟙ᵐ ] λx∙xx {n = n} p
    ▸λx∙xx′ = ▸λx∙xx ok p≤𝟘

------------------------------------------------------------------------
-- The term former loops

opaque

  -- A term for which the extracted term does not terminate if
  -- erasable arguments are removed entirely and strict applications
  -- are used (if the modality's zero is well-behaved).

  loops : M → Term n
  loops p = lam ω zero ∘⟨ ω ⟩ extracts-to-loop p

opaque
  unfolding loops

  -- An extraction lemma for loops.

  erase-loops :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero M 𝕄 ⦄ →
    erase′ true s (loops {n = n} p) ≡
    T.lam T.zero T.∘⟨ s ⟩ loop s
  erase-loops {s} {p} =
    erase′ true s (lam ω zero ∘⟨ ω ⟩ extracts-to-loop p)  ≡⟨ ∘-≢𝟘 ω≢𝟘 ⟩

    erase′ true s (lam ω zero) T.∘⟨ s ⟩
    erase′ true s (extracts-to-loop p)                    ≡⟨ PE.cong₂ T._∘⟨ _ ⟩_ (lam-≢𝟘 _ ω≢𝟘)
                                                             erase-extracts-to-loop ⟩
    T.lam T.zero T.∘⟨ s ⟩ loop s                          ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque

  -- If erasable arguments are removed entirely and strict
  -- applications are used, then the extraction of loops {n = n} p
  -- "reduces forever" (if the modality's zero is well-behaved).

  loops-reduces-forever :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero M 𝕄 ⦄ →
    T.Reduces-forever {n = n} vs (erase′ true strict (loops p))
  loops-reduces-forever =
    lemma ∘→ PE.subst (flip (T._⊢_⇒*_ _) _) erase-loops
    where
    lemma :
      T.Reduces-forever {n = n} vs
        (T.lam T.zero T.∘⟨ strict ⟩ loop strict)
    lemma T.refl =
      _ , T.app-subst-arg T.lam loop⇒loop
    lemma (T.trans s ss) =
      case redDet _ s (T.app-subst-arg T.lam loop⇒loop) of λ {
        PE.refl →
      lemma ss }

opaque

  -- If erasable arguments are removed entirely and strict
  -- applications are used, then the extraction of loops p does not
  -- reduce to a value (if the modality's zero is well-behaved).

  loops-does-not-reduce-to-a-value :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero M 𝕄 ⦄ →
    T.Value v →
    ¬ vs T.⊢ erase′ true strict (loops p) ⇒* v
  loops-does-not-reduce-to-a-value =
    Reduces-forever→Value→¬⇒* loops-reduces-forever

opaque
  unfolding loops

  -- A typing rule for loops.

  ⊢loops :
    Π-allowed 𝟘 p →
    Π-allowed ω q →
    Π-allowed (ω + ω) q →
    ⊢ Γ →
    Γ ⊢ loops q ∷ ℕ
  ⊢loops 𝟘-ok ω-ok ω+ω-ok ⊢Γ =
    lamⱼ′ ω-ok (zeroⱼ (∙ ΠΣⱼ Empty⊢ℕ 𝟘-ok)) ∘ⱼ
    ⊢extracts-to-loop 𝟘-ok ω-ok ω+ω-ok ⊢Γ
    where
    open Lemmas ⊢Γ

opaque
  unfolding loops

  -- A usage rule for loops.

  ▸loops :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero M 𝕄 ⦄ →
    Emptyrec-allowed 𝟙ᵐ 𝟘 →
    p ≤ 𝟘 →
    𝟘ᶜ ▸[ 𝟙ᵐ ] loops {n = n} p
  ▸loops ok p≤𝟘 = sub
    (lamₘ
       (sub zeroₘ $ begin
          𝟘ᶜ ∙ 𝟙 · ω  ≈⟨ ≈ᶜ-refl ∙ ·-identityˡ _ ⟩
          𝟘ᶜ ∙ ω      ≤⟨ ≤ᶜ-refl ∙ ω≤𝟘 ⟩
          𝟘ᶜ          ∎) ∘ₘ
     ▸-cong (PE.sym $ ≢𝟘→⌞⌟≡𝟙ᵐ ω≢𝟘)
       (▸extracts-to-loop ok p≤𝟘))
    (begin
       𝟘ᶜ             ≈˘⟨ ≈ᶜ-trans (+ᶜ-identityˡ _) (·ᶜ-zeroʳ _) ⟩
       𝟘ᶜ +ᶜ ω ·ᶜ 𝟘ᶜ  ∎)
    where
    open ≤ᶜ-reasoning
