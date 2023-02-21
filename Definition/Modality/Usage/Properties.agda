open import Tools.Relation
open import Definition.Modality

module Definition.Modality.Usage.Properties
  {a} {M : Set a} (𝕄 : Modality M) where

open Modality 𝕄

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Context.Properties 𝕄
open import Definition.Modality.Properties 𝕄
open import Definition.Modality.Usage 𝕄
open import Definition.Mode 𝕄
open import Definition.Typed M hiding (_∙_)
open import Definition.Untyped M hiding (_∷_ ; _∙_ ; ε ; subst)
open import Definition.Usage 𝕄

open import Tools.Bool using (Bool; T)
open import Tools.Fin
open import Tools.Function
open import Tools.Nat hiding (_+_)
open import Tools.Nullary
open import Tools.Product
open import Tools.PropositionalEquality as PE
open import Tools.Sum
import Tools.Reasoning.Equivalence
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality

private
  variable
    n : Nat
    Γ : Con Term n
    t u A F : Term n
    G : Term (1+ n)
    γ δ η : Conₘ n
    p q r : M
    m m₁ m₂ m′ : Mode
    b : Bool
    ok : T b

------------------------------------------------------------------------
-- Replacing one usage mode with another

-- γ ▸[_] t respects _≡_.

▸-cong : m₁ ≡ m₂ → γ ▸[ m₁ ] t → γ ▸[ m₂ ] t
▸-cong = subst (_ ▸[_] _)

-- If 𝟙 ≈ 𝟘, then one can convert usage modes freely.

▸-𝟙≈𝟘 : 𝟙 ≈ 𝟘 → γ ▸[ m ] t → γ ▸[ m′ ] t
▸-𝟙≈𝟘 _ Uₘ =
  Uₘ
▸-𝟙≈𝟘 _ ℕₘ =
  ℕₘ
▸-𝟙≈𝟘 _ Emptyₘ =
  Emptyₘ
▸-𝟙≈𝟘 _ Unitₘ =
  Unitₘ
▸-𝟙≈𝟘 𝟙≈𝟘 (Πₘ ▸F ▸G) =
  Πₘ (▸-𝟙≈𝟘 𝟙≈𝟘 ▸F)
     (sub (▸-𝟙≈𝟘 𝟙≈𝟘 ▸G) (≈ᶜ-trivial 𝟙≈𝟘))
▸-𝟙≈𝟘 𝟙≈𝟘 (Σₘ ▸F ▸G) =
  Σₘ (▸-𝟙≈𝟘 𝟙≈𝟘 ▸F)
     (sub (▸-𝟙≈𝟘 𝟙≈𝟘 ▸G) (≈ᶜ-trivial 𝟙≈𝟘))
▸-𝟙≈𝟘 𝟙≈𝟘 var = sub
  var
  (≈ᶜ-trivial 𝟙≈𝟘)
▸-𝟙≈𝟘 𝟙≈𝟘 (lamₘ ▸t) =
  lamₘ (sub (▸-𝟙≈𝟘 𝟙≈𝟘 ▸t) (≈ᶜ-trivial 𝟙≈𝟘))
▸-𝟙≈𝟘 𝟙≈𝟘 (▸t ∘ₘ ▸u) =
  ▸-𝟙≈𝟘 𝟙≈𝟘 ▸t ∘ₘ sub (▸-𝟙≈𝟘 𝟙≈𝟘 ▸u) (≈ᶜ-trivial 𝟙≈𝟘)
▸-𝟙≈𝟘 𝟙≈𝟘 (prodᵣₘ ▸t ▸u PE.refl) =
  prodᵣₘ (▸-𝟙≈𝟘 𝟙≈𝟘 ▸t) (▸-𝟙≈𝟘 𝟙≈𝟘 ▸u) PE.refl
▸-𝟙≈𝟘 𝟙≈𝟘 (prodₚₘ ▸t ▸u) =
  prodₚₘ (▸-𝟙≈𝟘 𝟙≈𝟘 ▸t) (▸-𝟙≈𝟘 𝟙≈𝟘 ▸u)
▸-𝟙≈𝟘 𝟙≈𝟘 (fstₘ ▸t) =
  fstₘ (▸-𝟙≈𝟘 𝟙≈𝟘 ▸t)
▸-𝟙≈𝟘 𝟙≈𝟘 (sndₘ ▸t) =
  sndₘ (▸-𝟙≈𝟘 𝟙≈𝟘 ▸t)
▸-𝟙≈𝟘 𝟙≈𝟘 (prodrecₘ ▸t ▸u P) = prodrecₘ
  (▸-𝟙≈𝟘 𝟙≈𝟘 ▸t)
  (sub (▸-𝟙≈𝟘 𝟙≈𝟘 ▸u) (≈ᶜ-trivial 𝟙≈𝟘))
  P
▸-𝟙≈𝟘 _ zeroₘ =
  zeroₘ
▸-𝟙≈𝟘 𝟙≈𝟘 (sucₘ ▸t) =
  sucₘ (▸-𝟙≈𝟘 𝟙≈𝟘 ▸t)
▸-𝟙≈𝟘 𝟙≈𝟘 (natrecₘ ▸z ▸s ▸n) = natrecₘ
  (▸-𝟙≈𝟘 𝟙≈𝟘 ▸z)
  (sub (▸-𝟙≈𝟘 𝟙≈𝟘 ▸s) (≈ᶜ-trivial 𝟙≈𝟘))
  (▸-𝟙≈𝟘 𝟙≈𝟘 ▸n)
▸-𝟙≈𝟘 𝟙≈𝟘 (Emptyrecₘ ▸t) = sub
  (Emptyrecₘ (▸-𝟙≈𝟘 𝟙≈𝟘 ▸t))
  (≈ᶜ-trivial 𝟙≈𝟘)
▸-𝟙≈𝟘 _ starₘ =
  starₘ
▸-𝟙≈𝟘 𝟙≈𝟘 (sub γ▸t _) =
  sub (▸-𝟙≈𝟘 𝟙≈𝟘 γ▸t) (≈ᶜ-trivial 𝟙≈𝟘)

-- If 𝟘ᵐ is not allowed, then one can convert usage modes freely.

▸-without-𝟘ᵐ : ¬ T 𝟘ᵐ-allowed → γ ▸[ m ] t → γ ▸[ m′ ] t
▸-without-𝟘ᵐ not-ok =
  ▸-cong (Mode-propositional-without-𝟘ᵐ not-ok)

------------------------------------------------------------------------
-- The lemma ▸-· and some corollaries

-- The relation _▸[_]_ respects multiplication (in a certain sense).

▸-· : γ ▸[ m ] t → ⌜ m′ ⌝ ·ᶜ γ ▸[ m′ ·ᵐ m ] t
▸-· Uₘ =
  sub Uₘ (≤ᶜ-reflexive (·ᶜ-zeroʳ _))
▸-· ℕₘ =
  sub ℕₘ (≤ᶜ-reflexive (·ᶜ-zeroʳ _))
▸-· Emptyₘ =
  sub Emptyₘ (≤ᶜ-reflexive (·ᶜ-zeroʳ _))
▸-· Unitₘ =
  sub Unitₘ (≤ᶜ-reflexive (·ᶜ-zeroʳ _))
▸-· {m′ = m′} (Πₘ F G) = sub
  (Πₘ (▸-cong (PE.sym (·ᵐ-ᵐ·-assoc m′)) (▸-· F))
      (sub (▸-· G) (≤ᶜ-reflexive (≈ᶜ-refl ∙ ·ᵐ-·-assoc m′))))
  (≤ᶜ-reflexive (·ᶜ-distribˡ-+ᶜ _ _ _))
▸-· {m′ = m′} (Σₘ F G) = sub
  (Σₘ (▸-· F)
     (sub (▸-· G) (≤ᶜ-reflexive (≈ᶜ-refl ∙ ·ᵐ-·-assoc m′))))
  (≤ᶜ-reflexive (·ᶜ-distribˡ-+ᶜ _ _ _))
▸-· {m = m} {m′ = m′} (var {x = x}) = sub var
  (begin
     ⌜ m′ ⌝ ·ᶜ (𝟘ᶜ , x ≔ ⌜ m ⌝)    ≡˘⟨ update-distrib-·ᶜ _ _ _ _ ⟩
     ⌜ m′ ⌝ ·ᶜ 𝟘ᶜ , x ≔ ⌜ m′ ⌝ · ⌜ m ⌝  ≈⟨ update-congˡ (·ᶜ-zeroʳ _) ⟩
     𝟘ᶜ , x ≔ ⌜ m′ ⌝ · ⌜ m ⌝            ≈˘⟨ update-congʳ (⌜·ᵐ⌝ m′) ⟩
     𝟘ᶜ , x ≔ ⌜ m′ ·ᵐ m ⌝               ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-· {m′ = m′} (lamₘ t) = lamₘ
  (sub (▸-· t) (≤ᶜ-reflexive (≈ᶜ-refl ∙ ·ᵐ-·-assoc m′)))
▸-· {m′ = m′} (_∘ₘ_ {γ = γ} {δ = δ} {p = p} t u) = sub
  (▸-· t ∘ₘ ▸-cong (PE.sym (·ᵐ-ᵐ·-assoc m′)) (▸-· u))
  (begin
     ⌜ m′ ⌝ ·ᶜ (γ +ᶜ p ·ᶜ δ)          ≈⟨ ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
     ⌜ m′ ⌝ ·ᶜ γ +ᶜ ⌜ m′ ⌝ ·ᶜ p ·ᶜ δ  ≈⟨ +ᶜ-congˡ
                                           (≈ᶜ-trans (≈ᶜ-sym (·ᶜ-assoc _ _ _))
                                              (≈ᶜ-trans (·ᶜ-congʳ (⌜⌝-·-comm m′))
                                                 (·ᶜ-assoc _ _ _))) ⟩
     ⌜ m′ ⌝ ·ᶜ γ +ᶜ p ·ᶜ ⌜ m′ ⌝ ·ᶜ δ  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-· (prodᵣₘ t u PE.refl) = sub
  (prodᵣₘ (▸-· t) (▸-· u) PE.refl)
  (≤ᶜ-reflexive (·ᶜ-distribˡ-+ᶜ _ _ _))
▸-· (prodₚₘ t u) =
  prodₚₘ (▸-· t) (▸-· u)
▸-· (fstₘ t) =
  fstₘ (▸-· t)
▸-· (sndₘ t) =
  sndₘ (▸-· t)
▸-· {m′ = m′} (prodrecₘ {γ = γ} {m = m} {p = p} {δ = δ} t u P) = sub
  (prodrecₘ
     (▸-cong (PE.sym (·ᵐ-ᵐ·-assoc m′)) (▸-· t))
     (sub (▸-· u)
        (≤ᶜ-reflexive (≈ᶜ-refl ∙ ·ᵐ-·-assoc m′ ∙ ·ᵐ-·-assoc m′)))
     P)
  (begin
     ⌜ m′ ⌝ ·ᶜ (p ·ᶜ γ +ᶜ δ)          ≈⟨ ·ᶜ-distribˡ-+ᶜ _ _ _ ⟩
     ⌜ m′ ⌝ ·ᶜ p ·ᶜ γ +ᶜ ⌜ m′ ⌝ ·ᶜ δ  ≈⟨ +ᶜ-congʳ
                                           (≈ᶜ-trans (≈ᶜ-sym (·ᶜ-assoc _ _ _))
                                              (≈ᶜ-trans (·ᶜ-congʳ (⌜⌝-·-comm m′))
                                                 (·ᶜ-assoc _ _ _))) ⟩
     p ·ᶜ ⌜ m′ ⌝ ·ᶜ γ +ᶜ ⌜ m′ ⌝ ·ᶜ δ  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-· zeroₘ =
  sub zeroₘ (≤ᶜ-reflexive (·ᶜ-zeroʳ _))
▸-· (sucₘ t) =
  sucₘ (▸-· t)
▸-· {m = m} {m′ = m′}
  (natrecₘ {γ = γ} {δ = δ} {p = p} {r = r} {η = η} γ▸z δ▸s η▸n) = sub
  (natrecₘ (▸-· γ▸z)
     (sub (▸-· δ▸s)
        (≤ᶜ-reflexive (≈ᶜ-refl ∙ ·ᵐ-·-assoc m′ ∙ ·ᵐ-·-assoc m′)))
     (▸-· η▸n))
  (begin
     ⌜ m′ ⌝ ·ᶜ (γ ∧ᶜ η) ⊛ᶜ δ +ᶜ p ·ᶜ η ▷ r                                ≈⟨ ⌜⌝-·ᶜ-distribˡ-⊛ᶜ m′ ⟩
     (⌜ m′ ⌝ ·ᶜ (γ ∧ᶜ η)) ⊛ᶜ ⌜ m′ ⌝ ·ᶜ (δ +ᶜ p ·ᶜ η) ▷ r                  ≈⟨ ⊛ᶜ-cong (·ᶜ-distribˡ-∧ᶜ _ _ _) (·ᶜ-distribˡ-+ᶜ _ _ _) ≈-refl ⟩
     (⌜ m′ ⌝ ·ᶜ γ ∧ᶜ ⌜ m′ ⌝ ·ᶜ η) ⊛ᶜ ⌜ m′ ⌝ ·ᶜ δ +ᶜ ⌜ m′ ⌝ ·ᶜ p ·ᶜ η ▷ r  ≈⟨ ⊛ᵣᶜ-congˡ
                                                                               (+ᶜ-congˡ
                                                                                  (≈ᶜ-trans (≈ᶜ-sym (·ᶜ-assoc _ _ _))
                                                                                     (≈ᶜ-trans (·ᶜ-congʳ (⌜⌝-·-comm m′))
                                                                                        (·ᶜ-assoc _ _ _)))) ⟩
     (⌜ m′ ⌝ ·ᶜ γ ∧ᶜ ⌜ m′ ⌝ ·ᶜ η) ⊛ᶜ ⌜ m′ ⌝ ·ᶜ δ +ᶜ p ·ᶜ ⌜ m′ ⌝ ·ᶜ η ▷ r  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-· {m′ = m′} (Emptyrecₘ {γ = γ} {m = m} {p = p} e) = sub
  (Emptyrecₘ (▸-cong (PE.sym (·ᵐ-ᵐ·-assoc m′)) (▸-· e)))
  (begin
     ⌜ m′ ⌝ ·ᶜ p ·ᶜ γ   ≈˘⟨ ·ᶜ-assoc _ _ _ ⟩
     (⌜ m′ ⌝ · p) ·ᶜ γ  ≈⟨ ·ᶜ-congʳ (⌜⌝-·-comm m′) ⟩
     (p · ⌜ m′ ⌝) ·ᶜ γ  ≈⟨ ·ᶜ-assoc _ _ _ ⟩
     p ·ᶜ ⌜ m′ ⌝ ·ᶜ γ   ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-· starₘ =
  sub starₘ (≤ᶜ-reflexive (·ᶜ-zeroʳ _))
▸-· (sub γ▸t δ≤γ) =
  sub (▸-· γ▸t) (·ᶜ-monotoneʳ δ≤γ)

-- The relation _▸[_]_ respects multiplication (in a certain sense).

▸-·′ : γ ▸[ m ] t → ⌜ m ⌝ ·ᶜ γ ▸[ m ] t
▸-·′ ▸t = ▸-cong ·ᵐ-idem (▸-· ▸t)

-- If t is well-used, then it is well-used in the mode 𝟘ᵐ[ ok ], with
-- no usages.

▸-𝟘 : γ ▸[ m ] t → 𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] t
▸-𝟘 {γ = γ} ▸t = sub
  (▸-· ▸t)
  (begin
     𝟘ᶜ      ≈˘⟨ ·ᶜ-zeroˡ _ ⟩
     𝟘 ·ᶜ γ  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- A form of monotonicity for _▸[_]_.

▸-≤ : p ≤ q → ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ⌟ ] t → ⌜ ⌞ q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ q ⌟ ] t
▸-≤ {p = p} {q = q} {γ = γ} {t = t} p≤q ▸t with is-𝟘? p | is-𝟘? q
… | yes _  | yes _   = ▸t
… | no _   | no _    = ▸t
… | no p≉𝟘 | yes q≈𝟘 = 𝟘ᵐ?-elim
  (λ m → ⌜ m ⌝ ·ᶜ γ ▸[ m ] t)
  (sub (▸-𝟘 ▸t) (begin
     𝟘 ·ᶜ γ  ≈⟨ ·ᶜ-zeroˡ _ ⟩
     𝟘ᶜ      ∎))
  (λ _ → ▸t)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
… | yes p≈𝟘 | no q≉𝟘 = ⊥-elim (q≉𝟘 (𝟘≮ (begin
    𝟘  ≈˘⟨ p≈𝟘 ⟩
    p  ≤⟨ p≤q ⟩
    q  ∎)))
  where
  open Tools.Reasoning.PartialOrder ≤-poset

-- If t is well-used in the mode 𝟙ᵐ with usage vector γ, then t is
-- well-used in the mode ⌞ p ⌟ with some usage vector δ for which
-- p ·ᶜ γ ≈ᶜ p ·ᶜ δ.

▸[𝟙ᵐ]→▸[⌞⌟] :
  γ ▸[ 𝟙ᵐ ] t →
  ∃ λ δ → δ ▸[ ⌞ p ⌟ ] t × p ·ᶜ γ ≈ᶜ p ·ᶜ δ
▸[𝟙ᵐ]→▸[⌞⌟] {γ = γ} {p = p} ▸t = case is-𝟘? p of λ where
  (no p≉𝟘)  → (_ , ▸-cong (PE.sym (≉𝟘→⌞⌟≡𝟙ᵐ p≉𝟘)) ▸t , ≈ᶜ-refl)
  (yes p≈𝟘) → 𝟘ᵐ-allowed-elim
    (λ ok →
         _
       , ▸-cong (PE.sym (≈𝟘→⌞⌟≡𝟘ᵐ p≈𝟘)) (▸-𝟘 {ok = ok} ▸t)
       , (let open Tools.Reasoning.Equivalence Conₘ-setoid in begin
            p ·ᶜ γ   ≈⟨ ·ᶜ-congʳ p≈𝟘 ⟩
            𝟘 ·ᶜ γ   ≈⟨ ·ᶜ-zeroˡ _ ⟩
            𝟘ᶜ       ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
            p ·ᶜ 𝟘ᶜ  ∎))
    (λ not-ok → _ , ▸-without-𝟘ᵐ not-ok ▸t , ≈ᶜ-refl)

------------------------------------------------------------------------
-- Inversion lemmas

-- A kind of inversion lemma for _▸[_]_ related to multiplication.

▸-⌞·⌟ :
  ⌜ ⌞ p · q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p · q ⌟ ] t →
  (⌜ ⌞ p ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ⌟ ] t) ⊎ (⌜ ⌞ q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ q ⌟ ] t)
▸-⌞·⌟ {p = p} {q = q} {γ = γ} ▸t with is-𝟘? (p · q)
… | yes p·q≈𝟘 = case zero-product p·q≈𝟘 of λ where
    (inj₁ p≈𝟘) → inj₁ (subst (λ m → ⌜ m ⌝ ·ᶜ _ ▸[ m ] _) (lem _ p≈𝟘) ▸t)
    (inj₂ q≈𝟘) → inj₂ (subst (λ m → ⌜ m ⌝ ·ᶜ _ ▸[ m ] _) (lem _ q≈𝟘) ▸t)
  where
  lem = λ p p≈𝟘 →
    𝟘ᵐ?    ≡˘⟨ ⌞𝟘⌟≡𝟘ᵐ? ⟩
    ⌞ 𝟘 ⌟  ≡˘⟨ ⌞⌟-cong p≈𝟘 ⟩
    ⌞ p ⌟  ∎
    where
    open Tools.Reasoning.PropositionalEquality
… | no _ = inj₁ (sub (▸-cong eq (▸-· {m′ = ⌞ p ⌟} ▸t)) leq)
  where
  eq =
    ⌞ p ⌟ ·ᵐ 𝟙ᵐ  ≡⟨ ·ᵐ-identityʳ _ ⟩
    ⌞ p ⌟        ∎
    where
    open Tools.Reasoning.PropositionalEquality

  leq = begin
    ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ       ≈˘⟨ ·ᶜ-congˡ (·ᶜ-identityˡ _) ⟩
    ⌜ ⌞ p ⌟ ⌝ ·ᶜ 𝟙 ·ᶜ γ  ∎
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- If m₂ is 𝟘ᵐ[ ok ] whenever m₁ is 𝟘ᵐ[ ok ], then one can convert
-- from ⌜ m₁ ⌝ ·ᶜ γ ▸[ m₁ ] t to ⌜ m₂ ⌝ ·ᶜ γ ▸[ m₂ ] t.

▸-conv :
  (∀ ⦃ ok ⦄ → m₁ ≡ 𝟘ᵐ[ ok ] → m₂ ≡ 𝟘ᵐ[ ok ]) →
  ⌜ m₁ ⌝ ·ᶜ γ ▸[ m₁ ] t →
  ⌜ m₂ ⌝ ·ᶜ γ ▸[ m₂ ] t
▸-conv {m₁ = 𝟘ᵐ} {m₂ = 𝟘ᵐ} _ ▸t =
  ▸-cong 𝟘ᵐ-cong ▸t
▸-conv {m₁ = 𝟙ᵐ} {m₂ = 𝟙ᵐ} _ ▸t =
  ▸t
▸-conv {m₁ = 𝟘ᵐ} {m₂ = 𝟙ᵐ} 𝟘ᵐ≡𝟘ᵐ→𝟙ᵐ≡𝟘ᵐ ▸t =
  case 𝟘ᵐ≡𝟘ᵐ→𝟙ᵐ≡𝟘ᵐ PE.refl of λ ()
▸-conv {m₁ = 𝟙ᵐ} {m₂ = 𝟘ᵐ} {γ = γ} hyp ▸t = sub
  (▸-· {m′ = 𝟘ᵐ} ▸t)
  (begin
    𝟘 ·ᶜ γ       ≈˘⟨ ·ᶜ-congˡ (·ᶜ-identityˡ _) ⟩
    𝟘 ·ᶜ 𝟙 ·ᶜ γ  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- A kind of inversion lemma for _▸[_]_ related to addition.

▸-⌞+⌟ˡ :
  ⌜ ⌞ p + q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p + q ⌟ ] t →
  ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ⌟ ] t
▸-⌞+⌟ˡ = ▸-conv lemma
  where
  open Tools.Reasoning.PropositionalEquality

  lemma : ∀ ⦃ ok ⦄ → ⌞ p + q ⌟ ≡ 𝟘ᵐ[ ok ] → ⌞ p ⌟ ≡ 𝟘ᵐ[ ok ]
  lemma {p = p} {q = q} _  with is-𝟘? (p + q)
  lemma                 () | no _
  lemma {p = p}         _  | yes p+q≈𝟘 =
    ⌞ p ⌟  ≡⟨ ⌞⌟-cong (positiveˡ p+q≈𝟘) ⟩
    ⌞ 𝟘 ⌟  ≡⟨ ⌞𝟘⌟ ⟩
    𝟘ᵐ     ∎

-- A kind of inversion lemma for _▸[_]_ related to addition.

▸-⌞+⌟ʳ :
  ⌜ ⌞ p + q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p + q ⌟ ] t →
  ⌜ ⌞ q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ q ⌟ ] t
▸-⌞+⌟ʳ ▸t =
  ▸-⌞+⌟ˡ (subst (λ m → ⌜ m ⌝ ·ᶜ _ ▸[ m ] _) (⌞⌟-cong (+-comm _ _)) ▸t)

-- A kind of inversion lemma for _▸[_]_ related to the meet operation.

▸-⌞∧⌟ˡ :
  ⌜ ⌞ p ∧ q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ∧ q ⌟ ] t →
  ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ⌟ ] t
▸-⌞∧⌟ˡ = ▸-conv lemma
  where
  open Tools.Reasoning.PropositionalEquality

  lemma : ∀ ⦃ ok ⦄ → ⌞ p ∧ q ⌟ ≡ 𝟘ᵐ[ ok ] → ⌞ p ⌟ ≡ 𝟘ᵐ[ ok ]
  lemma {p = p} {q = q} _  with is-𝟘? (p ∧ q)
  lemma                 () | no _
  lemma {p = p}         _  | yes p∧q≈𝟘 =
    ⌞ p ⌟  ≡⟨ ⌞⌟-cong (∧≈𝟘ˡ p∧q≈𝟘) ⟩
    ⌞ 𝟘 ⌟  ≡⟨ ⌞𝟘⌟ ⟩
    𝟘ᵐ     ∎

-- A kind of inversion lemma for _▸[_]_ related to the meet operation.

▸-⌞∧⌟ʳ :
  ⌜ ⌞ p ∧ q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ∧ q ⌟ ] t →
  ⌜ ⌞ q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ q ⌟ ] t
▸-⌞∧⌟ʳ ▸t =
  ▸-⌞∧⌟ˡ (subst (λ m → ⌜ m ⌝ ·ᶜ _ ▸[ m ] _) (⌞⌟-cong (∧-comm _ _)) ▸t)

-- A kind of inversion lemma for _▸[_]_ related to the star operation.

▸-⌞⊛⌟ˡ :
  ⌜ ⌞ p ⊛ q ▷ r ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ⊛ q ▷ r ⌟ ] t →
  ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ⌟ ] t
▸-⌞⊛⌟ˡ = ▸-conv lemma
  where
  open Tools.Reasoning.PropositionalEquality

  lemma : ∀ ⦃ ok ⦄ → ⌞ p ⊛ q ▷ r ⌟ ≡ 𝟘ᵐ[ ok ] → ⌞ p ⌟ ≡ 𝟘ᵐ[ ok ]
  lemma {p = p} {q = q} {r = r} _  with is-𝟘? (p ⊛ q ▷ r)
  lemma                         () | no _
  lemma {p = p}                 _  | yes p⊛q▷r≈𝟘 =
    ⌞ p ⌟  ≡⟨ ⌞⌟-cong (⊛≈𝟘ˡ p⊛q▷r≈𝟘) ⟩
    ⌞ 𝟘 ⌟  ≡⟨ ⌞𝟘⌟ ⟩
    𝟘ᵐ     ∎

-- A kind of inversion lemma for _▸[_]_ related to the star operation.

▸-⌞⊛⌟ʳ :
  ⌜ ⌞ p ⊛ q ▷ r ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ⊛ q ▷ r ⌟ ] t →
  ⌜ ⌞ q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ q ⌟ ] t
▸-⌞⊛⌟ʳ = ▸-conv lemma
  where
  open Tools.Reasoning.PropositionalEquality

  lemma : ∀ ⦃ ok ⦄ → ⌞ p ⊛ q ▷ r ⌟ ≡ 𝟘ᵐ[ ok ] → ⌞ q ⌟ ≡ 𝟘ᵐ[ ok ]
  lemma {p = p} {q = q} {r = r} _  with is-𝟘? (p ⊛ q ▷ r)
  lemma                         () | no _
  lemma         {q = q}         _  | yes p⊛q▷r≈𝟘 =
    ⌞ q ⌟  ≡⟨ ⌞⌟-cong (⊛≈𝟘ʳ p⊛q▷r≈𝟘) ⟩
    ⌞ 𝟘 ⌟  ≡⟨ ⌞𝟘⌟ ⟩
    𝟘ᵐ     ∎

------------------------------------------------------------------------
-- The lemma Conₘ-interchange

-- The contents of two valid modality contexts can be freely
-- interchanged.

Conₘ-interchange :
  γ ▸[ m ] t → δ ▸[ m ] t → (x : Fin n) → (γ , x ≔ δ ⟨ x ⟩) ▸[ m ] t
Conₘ-interchange (sub γ▸t γ≤γ′) δ▸t x  = sub
  (Conₘ-interchange γ▸t δ▸t x)
  (update-monotoneˡ x γ≤γ′)
Conₘ-interchange γ▸t (sub γ′▸t δ≤γ′) x = sub
  (Conₘ-interchange γ▸t γ′▸t x)
  (update-monotoneʳ x (lookup-monotone x δ≤γ′))
Conₘ-interchange Uₘ Uₘ x =
  subst (_▸[ _ ] _) (PE.sym (update-self 𝟘ᶜ x)) Uₘ
Conₘ-interchange ℕₘ ℕₘ x =
  subst (_▸[ _ ] _) (PE.sym (update-self 𝟘ᶜ x)) ℕₘ
Conₘ-interchange Emptyₘ Emptyₘ x =
  subst (_▸[ _ ] _) (PE.sym (update-self 𝟘ᶜ x)) Emptyₘ
Conₘ-interchange Unitₘ Unitₘ x =
  subst (_▸[ _ ] _) (PE.sym (update-self 𝟘ᶜ x)) Unitₘ

Conₘ-interchange
  (Πₘ {γ = γ} {δ = δ} γ▸t δ▸u)
  (Πₘ {γ = γ′} {δ = δ′} γ′▸t δ′▸u) x =
  subst (_▸[ _ ] _)
    (begin
       (γ , x ≔ γ′ ⟨ x ⟩) +ᶜ (δ , x ≔ δ′ ⟨ x ⟩)  ≡˘⟨ update-distrib-+ᶜ γ _ _ _ x ⟩
       γ +ᶜ δ , x ≔ γ′ ⟨ x ⟩ + δ′ ⟨ x ⟩          ≡˘⟨ cong (_ , x ≔_) (lookup-distrib-+ᶜ γ′ _ _) ⟩
       γ +ᶜ δ , x ≔ (γ′ +ᶜ δ′) ⟨ x ⟩             ∎)
    (Πₘ (Conₘ-interchange γ▸t γ′▸t x)
       (Conₘ-interchange δ▸u δ′▸u (x +1)))
  where
  open Tools.Reasoning.PropositionalEquality

Conₘ-interchange (Σₘ {γ} {δ = δ} γ▸t δ▸u)
                 (Σₘ {γ′} {δ = δ′} γ′▸t δ′▸u) x =
  subst (_▸[ _ ] _) eq (Σₘ (Conₘ-interchange γ▸t γ′▸t x)
                           (Conₘ-interchange δ▸u δ′▸u (x +1)))
  where
  open Tools.Reasoning.PropositionalEquality
  eq = begin
    (γ , x ≔ γ′ ⟨ x ⟩) +ᶜ (δ , x ≔ δ′ ⟨ x ⟩)
      ≡˘⟨ update-distrib-+ᶜ γ δ _ _ x ⟩
    (γ +ᶜ δ , x ≔ γ′ ⟨ x ⟩ + δ′ ⟨ x ⟩)
      ≡˘⟨ cong ((γ +ᶜ δ) , x ≔_) (lookup-distrib-+ᶜ γ′ δ′ x) ⟩
    (γ +ᶜ δ) , x ≔ ((γ′ +ᶜ δ′) ⟨ x ⟩)        ∎

Conₘ-interchange (var {x = y}) var x = subst (_▸[ _ ] _)
  (PE.sym (update-self (𝟘ᶜ , y ≔ _) x)) var

Conₘ-interchange (lamₘ γ▸t) (lamₘ δ▸t) x = lamₘ (Conₘ-interchange γ▸t δ▸t (x +1))

Conₘ-interchange
  (_∘ₘ_ {γ = γ} {δ = δ} {p = p} γ▸t δ▸u)
  (_∘ₘ_ {γ = γ′} {δ = δ′} γ′▸t δ′▸u)
  x =
  subst (_▸[ _ ] _) eq
    (Conₘ-interchange γ▸t γ′▸t x ∘ₘ
     Conₘ-interchange δ▸u δ′▸u x)
  where
  open Tools.Reasoning.PropositionalEquality
  eq = begin
    (γ , x ≔ (γ′ ⟨ x ⟩)) +ᶜ p ·ᶜ (δ , x ≔ (δ′ ⟨ x ⟩))
       ≡˘⟨ cong (_ +ᶜ_) (update-distrib-·ᶜ δ p _ x) ⟩
    (γ , x ≔ (γ′ ⟨ x ⟩)) +ᶜ (p ·ᶜ δ , x ≔ (p · δ′ ⟨ x ⟩))
       ≡˘⟨ cong (_ +ᶜ_) (cong (_ , x ≔_) (lookup-distrib-·ᶜ δ′ p x)) ⟩
    (γ , x ≔ (γ′ ⟨ x ⟩)) +ᶜ (p ·ᶜ δ , x ≔ ((p ·ᶜ δ′) ⟨ x ⟩))
       ≡˘⟨ update-distrib-+ᶜ γ _ _ _ x ⟩
    (γ +ᶜ p ·ᶜ δ) , x ≔ γ′ ⟨ x ⟩ + (p ·ᶜ δ′) ⟨ x ⟩
       ≡˘⟨ cong (_ , x ≔_) (lookup-distrib-+ᶜ γ′ (p ·ᶜ δ′) x) ⟩
    (γ +ᶜ p ·ᶜ δ) , x ≔ (γ′ +ᶜ p ·ᶜ δ′) ⟨ x ⟩ ∎

Conₘ-interchange (prodᵣₘ {γ} {δ = δ} γ▸t γ▸t₁ PE.refl)
                 (prodᵣₘ {γ₁} {δ = δ₁} δ▸t δ▸t₁ PE.refl) x =
  prodᵣₘ (Conₘ-interchange γ▸t δ▸t x)
         (Conₘ-interchange γ▸t₁ δ▸t₁ x)
         (subst₂ _≡_ (cong (_ , _ ≔_) (PE.sym (lookup-distrib-+ᶜ γ₁ δ₁ x)))
                 (update-distrib-+ᶜ γ δ _ _ x) PE.refl)

Conₘ-interchange (prodₚₘ γ▸t γ▸u) (prodₚₘ δ▸t δ▸u) x =
  prodₚₘ (Conₘ-interchange γ▸t δ▸t x) (Conₘ-interchange γ▸u δ▸u x)

Conₘ-interchange (fstₘ γ▸t) (fstₘ δ▸t) x =
  fstₘ (Conₘ-interchange γ▸t δ▸t x)
Conₘ-interchange (sndₘ γ▸t) (sndₘ δ▸t) x =
  sndₘ (Conₘ-interchange γ▸t δ▸t x)

Conₘ-interchange
  (prodrecₘ {γ = γ} {p = p} {δ = δ} γ▸t δ▸t P)
  (prodrecₘ {γ = γ′} {δ = δ′} γ▸t₁ δ▸t₁ Q)
  x =
  subst (_▸[ _ ] _) eq
    (prodrecₘ
       (Conₘ-interchange γ▸t γ▸t₁ x)
       (Conₘ-interchange δ▸t δ▸t₁ (x +1 +1))
       Q)
  where
  open Tools.Reasoning.PropositionalEquality
  eq = begin
    p ·ᶜ (γ , x ≔ γ′ ⟨ x ⟩) +ᶜ (δ , x ≔ δ′ ⟨ x ⟩)
      ≡˘⟨ cong (_+ᶜ _) (update-distrib-·ᶜ γ p (γ′ ⟨ x ⟩) x) ⟩
    (p ·ᶜ γ , x ≔ p · γ′ ⟨ x ⟩) +ᶜ (δ , x ≔ δ′ ⟨ x ⟩)
      ≡˘⟨ update-distrib-+ᶜ (p ·ᶜ γ) δ (p · γ′ ⟨ x ⟩) (δ′ ⟨ x ⟩) x ⟩
    p ·ᶜ γ +ᶜ δ , x ≔ p · γ′ ⟨ x ⟩ + δ′ ⟨ x ⟩
      ≡˘⟨ cong (λ y → _ , x ≔ y + _) (lookup-distrib-·ᶜ γ′ p x) ⟩
    p ·ᶜ γ +ᶜ δ , x ≔ (p ·ᶜ γ′) ⟨ x ⟩ + δ′ ⟨ x ⟩
      ≡˘⟨ cong (λ y → _ , x ≔ y) (lookup-distrib-+ᶜ (p ·ᶜ γ′) δ′ x) ⟩
    p ·ᶜ γ +ᶜ δ , x ≔ (p ·ᶜ γ′ +ᶜ δ′) ⟨ x ⟩ ∎

Conₘ-interchange zeroₘ zeroₘ x           =
  subst (_▸[ _ ] _) (PE.sym (update-self 𝟘ᶜ x)) zeroₘ
Conₘ-interchange (sucₘ γ▸t) (sucₘ δ▸t) x =
  sucₘ (Conₘ-interchange γ▸t δ▸t x)

Conₘ-interchange (natrecₘ {γ = γ} {δ = δ} {p = p} {r = r} {η = η} γ▸z δ▸s η▸n)
                 (natrecₘ {γ = γ′} {δ = δ′} {η = η′} γ′▸z δ′▸s η′▸n) x =
  subst (_▸[ _ ] _) eq
    (natrecₘ
       (Conₘ-interchange γ▸z γ′▸z x)
       (Conₘ-interchange δ▸s δ′▸s (x +1 +1))
       (Conₘ-interchange η▸n η′▸n x))
  where
  open Tools.Reasoning.PropositionalEquality
  eq = let γ'  = γ , x ≔ (γ′ ⟨ x ⟩)
           δ'  = δ , x ≔ (δ′ ⟨ x ⟩)
           η'  = η , x ≔ (η′ ⟨ x ⟩)
           pη' = p ·ᶜ η , x ≔ (p · (η′ ⟨ x ⟩))
       in begin
          (γ' ∧ᶜ η') ⊛ᶜ (δ' +ᶜ p ·ᶜ η') ▷ r
            ≡˘⟨ cong (λ y → (γ' ∧ᶜ _) ⊛ᶜ (_ +ᶜ y) ▷ _)
                     (update-distrib-·ᶜ η p (η′ ⟨ x ⟩) x) ⟩
          (γ' ∧ᶜ η') ⊛ᶜ (δ' +ᶜ pη') ▷ r
            ≡˘⟨ cong (λ y → (γ' ∧ᶜ _) ⊛ᶜ (_ +ᶜ (_ , x ≔ y)) ▷ r)
                     (lookup-distrib-·ᶜ η′ p x) ⟩
          (γ' ∧ᶜ η') ⊛ᶜ (δ' +ᶜ ((p ·ᶜ η) , x ≔ ((p ·ᶜ η′) ⟨ x ⟩))) ▷ r
            ≡˘⟨ cong (λ y →  (γ' ∧ᶜ _) ⊛ᶜ y ▷ r)
                     (update-distrib-+ᶜ δ (p ·ᶜ η) (δ′ ⟨ x ⟩) ((p ·ᶜ η′) ⟨ x ⟩) x) ⟩
          (γ' ∧ᶜ η') ⊛ᶜ ((δ +ᶜ p ·ᶜ η) , x ≔ (δ′ ⟨ x ⟩ + (p ·ᶜ η′) ⟨ x ⟩)) ▷ r
            ≡˘⟨ cong₂ (λ y z → y ⊛ᶜ (_ , x ≔ z) ▷ r)
                      (update-distrib-∧ᶜ γ η (γ′ ⟨ x ⟩) (η′ ⟨ x ⟩) x)
                      (lookup-distrib-+ᶜ δ′ (p ·ᶜ η′) x)   ⟩
          ((γ ∧ᶜ η) , x ≔ (γ′ ⟨ x ⟩ ∧ η′ ⟨ x ⟩)) ⊛ᶜ ((δ +ᶜ p ·ᶜ η) , x ≔ ((δ′ +ᶜ p ·ᶜ η′) ⟨ x ⟩)) ▷ r
            ≡˘⟨ update-distrib-⊛ᶜ (γ ∧ᶜ η) (δ +ᶜ p ·ᶜ η) r
                                   ((γ′ ⟨ x ⟩) ∧ (η′ ⟨ x ⟩))
                                   ((δ′ +ᶜ p ·ᶜ η′) ⟨ x ⟩) x ⟩
          (γ ∧ᶜ η) ⊛ᶜ (δ +ᶜ p ·ᶜ η) ▷ r , x ≔ ((γ′ ⟨ x ⟩) ∧ (η′ ⟨ x ⟩)) ⊛ ((δ′ +ᶜ p ·ᶜ η′) ⟨ x ⟩) ▷ r
            ≡˘⟨ cong (λ y → _ , x ≔ y ⊛ _ ▷ _) (lookup-distrib-∧ᶜ γ′ η′ x) ⟩
          (γ ∧ᶜ η) ⊛ᶜ (δ +ᶜ p ·ᶜ η) ▷ r , x ≔ ((γ′ ∧ᶜ η′) ⟨ x ⟩) ⊛ ((δ′ +ᶜ p ·ᶜ η′) ⟨ x ⟩) ▷ r
            ≡˘⟨ cong (λ y → _ , x ≔ y) (lookup-distrib-⊛ᶜ (γ′ ∧ᶜ η′) (δ′ +ᶜ p ·ᶜ η′) r x) ⟩
          (γ ∧ᶜ η) ⊛ᶜ (δ +ᶜ (p ·ᶜ η)) ▷ r , x ≔ ((γ′ ∧ᶜ η′) ⊛ᶜ (δ′ +ᶜ (p ·ᶜ η′)) ▷ r) ⟨ x ⟩ ∎

Conₘ-interchange
  (Emptyrecₘ {γ = γ} {m = m} {p = p} γ▸t)
  (Emptyrecₘ {γ = δ} δ▸t)
  x =
  subst (_▸[ _ ] _)
    (begin
       p ·ᶜ (γ , x ≔ δ ⟨ x ⟩)       ≡˘⟨ update-distrib-·ᶜ _ _ _ _ ⟩
       p ·ᶜ γ , x ≔ p · (δ ⟨ x ⟩)   ≡˘⟨ cong (_ , _ ≔_) (lookup-distrib-·ᶜ δ _ _) ⟩
       p ·ᶜ γ , x ≔ (p ·ᶜ δ) ⟨ x ⟩  ∎)
    (Emptyrecₘ (Conₘ-interchange γ▸t δ▸t x))
  where
  open Tools.Reasoning.PropositionalEquality

Conₘ-interchange starₘ starₘ x =
  subst (_▸[ _ ] _) (PE.sym (update-self 𝟘ᶜ x)) starₘ

------------------------------------------------------------------------
-- Lemmas related to ⌈_⌉

-- ⌈_⌉ provides upper bounds for valid modality contexts: if
-- γ ▸[ m ] t, then γ ≤ᶜ ⌈ t ⌉ m.

usage-upper-bound : γ ▸[ m ] t → γ ≤ᶜ ⌈ t ⌉ m
usage-upper-bound Uₘ     = ≤ᶜ-refl
usage-upper-bound ℕₘ     = ≤ᶜ-refl
usage-upper-bound Emptyₘ = ≤ᶜ-refl
usage-upper-bound Unitₘ  = ≤ᶜ-refl

usage-upper-bound (Πₘ {G = G} ▸F ▸G) =
  +ᶜ-monotone (usage-upper-bound ▸F)
              (subst (_ ≈ᶜ_) (tailₘ-distrib-∧ᶜ (_ ∙ _) (⌈ G ⌉ _))
                     (tailₘ-cong (usage-upper-bound ▸G)))

usage-upper-bound (Σₘ {G = G} ▸F ▸G) =
  +ᶜ-monotone (usage-upper-bound ▸F)
              (subst (_ ≈ᶜ_) (tailₘ-distrib-∧ᶜ (_ ∙ _) (⌈ G ⌉ _))
                     (tailₘ-cong (usage-upper-bound ▸G)))

usage-upper-bound var = ≤ᶜ-refl

usage-upper-bound (lamₘ {t = t} ▸t) =
  subst (_ ≈ᶜ_) (tailₘ-distrib-∧ᶜ (_ ∙ _) (⌈ t ⌉ _))
    (tailₘ-cong (usage-upper-bound ▸t))

usage-upper-bound (▸t ∘ₘ ▸u) =
  +ᶜ-monotone (usage-upper-bound ▸t)
    (·ᶜ-monotoneʳ (usage-upper-bound ▸u))

usage-upper-bound (prodᵣₘ t u PE.refl) =
  +ᶜ-monotone (usage-upper-bound t) (usage-upper-bound u)
usage-upper-bound (prodₚₘ t u) =
  ≤ᶜ-trans (≤ᶜ-reflexive (≈ᶜ-sym (∧ᶜ-idem _)))
           (∧ᶜ-monotone (usage-upper-bound t) (usage-upper-bound u))
usage-upper-bound (fstₘ t) = usage-upper-bound t
usage-upper-bound (sndₘ t) = usage-upper-bound t
usage-upper-bound (prodrecₘ t u P) =
  +ᶜ-monotone (·ᶜ-monotoneʳ (usage-upper-bound t))
              (tailₘ-monotone (tailₘ-monotone (usage-upper-bound u)))

usage-upper-bound zeroₘ    = ≤ᶜ-refl
usage-upper-bound (sucₘ t) = usage-upper-bound t

usage-upper-bound (natrecₘ {z = z} {s = s} {n = n} γ▸z δ▸s η▸n) =
  ⊛ᶜ-monotone (∧ᶜ-monotone γ≤γ′ η≤η′)
               (+ᶜ-monotone (tailₘ-monotone (tailₘ-monotone δ≤δ′))
                            (·ᶜ-monotoneʳ η≤η′))
  where
  γ≤γ′ = usage-upper-bound γ▸z
  δ≤δ′ = usage-upper-bound δ▸s
  η≤η′ = usage-upper-bound η▸n

usage-upper-bound (Emptyrecₘ e) =
  ·ᶜ-monotoneʳ (usage-upper-bound e)
usage-upper-bound starₘ = ≤ᶜ-refl
usage-upper-bound (sub t x) = ≤ᶜ-trans x (usage-upper-bound t)


-- A valid modality context can be computed from a well-resourced
-- term.

usage-inf : γ ▸[ m ] t → ⌈ t ⌉ m ▸[ m ] t
usage-inf Uₘ = Uₘ
usage-inf ℕₘ = ℕₘ
usage-inf Emptyₘ = Emptyₘ
usage-inf Unitₘ = Unitₘ
usage-inf (Πₘ {G = G} γ▸F δ▸G) =
  Πₘ (usage-inf γ▸F)
     (sub (usage-inf δ▸G)
          (subst (tailₘ (⌈ G ⌉ _) ∙ _ ≤ᶜ_)
                 (headₘ-tailₘ-correct (⌈ G ⌉ _))
                 (≤ᶜ-refl ∙ headₘ-monotone (usage-upper-bound δ▸G))))
usage-inf (Σₘ {G = G} γ▸F δ▸G) =
  Σₘ (usage-inf γ▸F)
     (sub (usage-inf δ▸G)
          (subst (tailₘ (⌈ G ⌉ _) ∙ _ ≤ᶜ_)
                 (headₘ-tailₘ-correct (⌈ G ⌉ _))
                 (≤ᶜ-refl ∙ headₘ-monotone (usage-upper-bound δ▸G))))
usage-inf var = var
usage-inf (lamₘ {p = p} {t = t} γ▸t) =
  lamₘ (sub (usage-inf γ▸t)
            (PE.subst (⌈ lam p t ⌉ _ ∙ _ ≤ᶜ_)
                      (headₘ-tailₘ-correct (⌈ t ⌉ _))
                      (≤ᶜ-refl ∙ headₘ-monotone (usage-upper-bound γ▸t))))
usage-inf (γ▸t ∘ₘ γ▸t₁) = usage-inf γ▸t ∘ₘ usage-inf γ▸t₁
usage-inf (prodᵣₘ γ▸t γ▸t₁ PE.refl) = prodᵣₘ (usage-inf γ▸t) (usage-inf γ▸t₁) PE.refl
usage-inf (prodₚₘ γ▸t γ▸t₁) = prodₚₘ (sub (usage-inf γ▸t) (∧ᶜ-decreasingˡ _ _))
                                     (sub (usage-inf γ▸t₁) (∧ᶜ-decreasingʳ _ _))
usage-inf (fstₘ γ▸t) = fstₘ (usage-inf γ▸t)
usage-inf (sndₘ γ▸t) = sndₘ (usage-inf γ▸t)
usage-inf (prodrecₘ {p = p} {u = u} γ▸t δ▸u P) =
  prodrecₘ (usage-inf γ▸t)
           (sub (usage-inf δ▸u)
                (subst (tailₘ (tailₘ (⌈ u ⌉ _)) ∙ _ ∙ _ ≤ᶜ_)
                       (PE.trans
                          (cong (_∙ headₘ (⌈ u ⌉ _))
                             (headₘ-tailₘ-correct (tailₘ (⌈ u ⌉ _))))
                          (headₘ-tailₘ-correct (⌈ u ⌉ _)))
                       (≤ᶜ-refl ∙ headₘ-monotone (tailₘ-monotone (usage-upper-bound δ▸u)) ∙ headₘ-monotone (usage-upper-bound δ▸u))))
           P
usage-inf zeroₘ = zeroₘ
usage-inf (sucₘ γ▸t) = sucₘ (usage-inf γ▸t)
usage-inf (natrecₘ {s = s} γ▸z δ▸s η▸n) =
  natrecₘ (usage-inf γ▸z)
          (sub (usage-inf δ▸s)
               (subst (tailₘ (tailₘ (⌈ s ⌉ _)) ∙ _ ∙ _ ≤ᶜ_)
                      (PE.trans
                         (cong (_∙ headₘ (⌈ s ⌉ _))
                            (headₘ-tailₘ-correct (tailₘ (⌈ s ⌉ _))))
                         (headₘ-tailₘ-correct (⌈ s ⌉ _)))
                      (≤ᶜ-refl ∙ headₘ-monotone (tailₘ-monotone (usage-upper-bound δ▸s)) ∙ headₘ-monotone (usage-upper-bound δ▸s))))
          (usage-inf η▸n)
usage-inf (Emptyrecₘ γ▸t) = Emptyrecₘ (usage-inf γ▸t)
usage-inf starₘ = starₘ
usage-inf (sub γ▸t x) = usage-inf γ▸t

-- The context ⌈ t ⌉ 𝟘ᵐ[ ok ] is equivalent to 𝟘ᶜ.

⌈⌉-𝟘ᵐ : (t : Term n) → ⌈ t ⌉ 𝟘ᵐ[ ok ] ≈ᶜ 𝟘ᶜ
⌈⌉-𝟘ᵐ (var x) = begin
  𝟘ᶜ , x ≔ 𝟘  ≡⟨ 𝟘ᶜ,≔𝟘 ⟩
  𝟘ᶜ          ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
⌈⌉-𝟘ᵐ U =
  ≈ᶜ-refl
⌈⌉-𝟘ᵐ {ok = ok} (Π p , _ ▷ F ▹ G) = begin
  (⌈ F ⌉ 𝟘ᵐ[ ok ] +ᶜ tailₘ (⌈ G ⌉ 𝟘ᵐ[ ok ]))  ≈⟨ +ᶜ-cong (⌈⌉-𝟘ᵐ F) (tailₘ-cong (⌈⌉-𝟘ᵐ G)) ⟩
  𝟘ᶜ +ᶜ 𝟘ᶜ                                    ≈⟨ +ᶜ-identityʳ _ ⟩
  𝟘ᶜ                                          ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
⌈⌉-𝟘ᵐ (lam _ t) =
  tailₘ-cong (⌈⌉-𝟘ᵐ t)
⌈⌉-𝟘ᵐ {ok = ok} (t ∘⟨ p ⟩ u) = begin
  ⌈ t ⌉ 𝟘ᵐ[ ok ] +ᶜ p ·ᶜ ⌈ u ⌉ 𝟘ᵐ[ ok ]  ≈⟨ +ᶜ-cong (⌈⌉-𝟘ᵐ t) (·ᶜ-congˡ (⌈⌉-𝟘ᵐ u)) ⟩
  𝟘ᶜ +ᶜ p ·ᶜ 𝟘ᶜ                          ≈⟨ +ᶜ-congˡ (·ᶜ-zeroʳ _) ⟩
  𝟘ᶜ +ᶜ 𝟘ᶜ                               ≈⟨ +ᶜ-identityˡ _ ⟩
  𝟘ᶜ                                     ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
⌈⌉-𝟘ᵐ {ok = ok} (Σ _ ▷ F ▹ G) = begin
  ⌈ F ⌉ 𝟘ᵐ[ ok ] +ᶜ tailₘ (⌈ G ⌉ 𝟘ᵐ[ ok ])  ≈⟨ +ᶜ-cong (⌈⌉-𝟘ᵐ F) (tailₘ-cong (⌈⌉-𝟘ᵐ G)) ⟩
  𝟘ᶜ +ᶜ 𝟘ᶜ                                  ≈⟨ +ᶜ-identityˡ _ ⟩
  𝟘ᶜ                                        ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
⌈⌉-𝟘ᵐ {ok = ok} (prod Σᵣ t u) = begin
  ⌈ t ⌉ 𝟘ᵐ[ ok ] +ᶜ ⌈ u ⌉ 𝟘ᵐ[ ok ]  ≈⟨ +ᶜ-cong (⌈⌉-𝟘ᵐ t) (⌈⌉-𝟘ᵐ u) ⟩
  𝟘ᶜ +ᶜ 𝟘ᶜ                          ≈⟨ +ᶜ-identityˡ _ ⟩
  𝟘ᶜ                                ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
⌈⌉-𝟘ᵐ {ok = ok} (prod Σₚ t u) = begin
  ⌈ t ⌉ 𝟘ᵐ[ ok ] ∧ᶜ ⌈ u ⌉ 𝟘ᵐ[ ok ]  ≈⟨ ∧ᶜ-cong (⌈⌉-𝟘ᵐ t) (⌈⌉-𝟘ᵐ u) ⟩
  𝟘ᶜ ∧ᶜ 𝟘ᶜ                          ≈⟨ ∧ᶜ-idem _ ⟩
  𝟘ᶜ                                ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
⌈⌉-𝟘ᵐ (fst t) =
  ⌈⌉-𝟘ᵐ t
⌈⌉-𝟘ᵐ (snd t) =
  ⌈⌉-𝟘ᵐ t
⌈⌉-𝟘ᵐ {ok = ok} (prodrec p _ t u) = begin
  p ·ᶜ ⌈ t ⌉ 𝟘ᵐ[ ok ] +ᶜ tailₘ (tailₘ (⌈ u ⌉ 𝟘ᵐ[ ok ]))  ≈⟨ +ᶜ-cong (·ᶜ-congˡ (⌈⌉-𝟘ᵐ t)) (tailₘ-cong (tailₘ-cong (⌈⌉-𝟘ᵐ u))) ⟩
  p ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ                                          ≈⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
  𝟘ᶜ +ᶜ 𝟘ᶜ                                               ≈⟨ +ᶜ-identityˡ _ ⟩
  𝟘ᶜ                                                     ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
⌈⌉-𝟘ᵐ ℕ =
  ≈ᶜ-refl
⌈⌉-𝟘ᵐ zero =
  ≈ᶜ-refl
⌈⌉-𝟘ᵐ (suc t) =
  ⌈⌉-𝟘ᵐ t
⌈⌉-𝟘ᵐ {ok = ok} (natrec p r A z s n) = begin
  (⌈ z ⌉ 𝟘ᵐ[ ok ] ∧ᶜ ⌈ n ⌉ 𝟘ᵐ[ ok ]) ⊛ᶜ
    tailₘ (tailₘ (⌈ s ⌉ 𝟘ᵐ[ ok ])) +ᶜ p ·ᶜ ⌈ n ⌉ 𝟘ᵐ[ ok ] ▷ r  ≈⟨ ⊛ᵣᶜ-cong (∧ᶜ-cong (⌈⌉-𝟘ᵐ z) (⌈⌉-𝟘ᵐ n))
                                                                    (+ᶜ-cong (tailₘ-cong (tailₘ-cong (⌈⌉-𝟘ᵐ s)))
                                                                       (·ᶜ-congˡ (⌈⌉-𝟘ᵐ n))) ⟩
  (𝟘ᶜ ∧ᶜ 𝟘ᶜ) ⊛ᶜ 𝟘ᶜ +ᶜ p ·ᶜ 𝟘ᶜ ▷ r                              ≈⟨ ⊛ᵣᶜ-cong (∧ᶜ-idem _) (+ᶜ-identityˡ _) ⟩
  𝟘ᶜ ⊛ᶜ p ·ᶜ 𝟘ᶜ ▷ r                                            ≈⟨ ⊛ᵣᶜ-congˡ (·ᶜ-zeroʳ _) ⟩
  𝟘ᶜ ⊛ᶜ 𝟘ᶜ ▷ r                                                 ≈⟨ ⊛ᶜ-idem-𝟘ᶜ _ ⟩
  𝟘ᶜ                                                           ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
⌈⌉-𝟘ᵐ Unit =
  ≈ᶜ-refl
⌈⌉-𝟘ᵐ star =
  ≈ᶜ-refl
⌈⌉-𝟘ᵐ Empty =
  ≈ᶜ-refl
⌈⌉-𝟘ᵐ {ok = ok} (Emptyrec p _ t) = begin
  p ·ᶜ ⌈ t ⌉ 𝟘ᵐ[ ok ]  ≈⟨ ·ᶜ-congˡ (⌈⌉-𝟘ᵐ t) ⟩
  p ·ᶜ 𝟘ᶜ              ≈⟨ ·ᶜ-zeroʳ _ ⟩
  𝟘ᶜ                   ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid

-- The context ⌈ t ⌉ m does not change (up to _≈ᶜ_) if it is
-- multiplied by ⌜ m ⌝.

·-⌈⌉ : (t : Term n) → ⌜ m ⌝ ·ᶜ ⌈ t ⌉ m ≈ᶜ ⌈ t ⌉ m
·-⌈⌉ {m = 𝟘ᵐ} t = begin
  𝟘 ·ᶜ ⌈ t ⌉ 𝟘ᵐ  ≈⟨ ·ᶜ-zeroˡ _ ⟩
  𝟘ᶜ             ≈˘⟨ ⌈⌉-𝟘ᵐ t ⟩
  ⌈ t ⌉ 𝟘ᵐ       ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
·-⌈⌉ {m = 𝟙ᵐ} t = begin
  𝟙 ·ᶜ ⌈ t ⌉ 𝟙ᵐ  ≈⟨ ·ᶜ-identityˡ _ ⟩
  ⌈ t ⌉ 𝟙ᵐ       ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid

-- If γ ▸[ 𝟘ᵐ[ ok ] ] t, then γ ≤ᶜ 𝟘ᶜ.

▸-𝟘ᵐ : γ ▸[ 𝟘ᵐ[ ok ] ] t → γ ≤ᶜ 𝟘ᶜ
▸-𝟘ᵐ {γ = γ} {ok = ok} {t = t} ▸t = begin
  γ               ≤⟨ usage-upper-bound ▸t ⟩
  ⌈ t ⌉ 𝟘ᵐ[ ok ]  ≈⟨ ⌈⌉-𝟘ᵐ t ⟩
  𝟘ᶜ              ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

------------------------------------------------------------------------
-- The lemma natrec-usage

-- The context used in the usage rule for natrec satisfies the neccessary inequalities
-- (γ ∧ η) ⊛ᶜ (δ + pη) ▷ r ≤ γ and
-- (γ ∧ η) ⊛ᶜ (δ + pη) ▷ r ≤ δ + pη + r ((γ ∧ η) ⊛ᶜ (δ + pη) ▷ r) and
-- (γ ∧ η) ⊛ᶜ (δ + pη) ▷ r ≤ η

natrec-usage : (γ ∧ᶜ η) ⊛ᶜ (δ +ᶜ p ·ᶜ η) ▷ r ≤ᶜ γ
             × (γ ∧ᶜ η) ⊛ᶜ (δ +ᶜ p ·ᶜ η) ▷ r ≤ᶜ δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ (γ ∧ᶜ η) ⊛ᶜ (δ +ᶜ p ·ᶜ η) ▷ r
             × (γ ∧ᶜ η) ⊛ᶜ (δ +ᶜ p ·ᶜ η) ▷ r ≤ᶜ η
natrec-usage {γ = γ} {η} {δ} {p} {r} =
  ≤ᶜ-trans (⊛ᶜ-ineq₂ (γ ∧ᶜ η) (δ +ᶜ p ·ᶜ η) r) (∧ᶜ-decreasingˡ γ η)
  , ≤ᶜ-trans (⊛ᶜ-ineq₁ (γ ∧ᶜ η) (δ +ᶜ p ·ᶜ η) r)
             (≤ᶜ-reflexive (+ᶜ-assoc δ (p ·ᶜ η) (r ·ᶜ (γ ∧ᶜ η) ⊛ᶜ (δ +ᶜ p ·ᶜ η) ▷ r)))
  , ≤ᶜ-trans (⊛ᶜ-ineq₂ (γ ∧ᶜ η) (δ +ᶜ p ·ᶜ η) r) (∧ᶜ-decreasingʳ γ η)
