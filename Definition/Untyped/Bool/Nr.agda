------------------------------------------------------------------------
-- Booleans, defined using other types, for the theory with nr functions
------------------------------------------------------------------------

-- Typing rules for the term formers defined in this module can be
-- found in Definition.Typed.Properties.Admissible.Bool.OK and
-- Definition.Typed.Properties.Admissible.Bool, and usage rules can be
-- found in Graded.Derived.Bool.Nr.

import Graded.Modality

module Definition.Untyped.Bool.Nr
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  -- It is assumed that the modality has an nr function.
  ⦃ has-nr : Has-nr (Modality.semiring-with-meet 𝕄) ⦄
  where

private
  open module M = Modality 𝕄 using (𝟘; 𝟙; ω; _+_; _·_; _∧_)

open import Definition.Untyped M
open import Definition.Untyped.Empty 𝕄
open import Definition.Untyped.Nat 𝕄
open import Definition.Untyped.Properties M
import Definition.Untyped.Bool

open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄 hiding (has-nr)
open import Graded.Mode 𝕄

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat as N hiding (_+_)
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Reasoning.PropositionalEquality
open import Tools.Unit

private variable
  k k₁ k₂ n : Nat
  A t u v w : Term _
  σ         : Subst _ _
  ρ         : Wk _ _
  p         : M

------------------------------------------------------------------------
-- Some grades

opaque

  -- A grade used in the implementation of OK.

  OKᵍ : M
  OKᵍ = nr 𝟘 𝟘 𝟘 𝟘 𝟙

opaque

  -- A grade used in the implementation of Bool.

  Boolᵍ : M
  Boolᵍ = nr OKᵍ 𝟘 𝟘 𝟘 𝟙

opaque

  -- A grade that is used in the implementation of boolrec.

  boolrecᵍ-Π : M
  boolrecᵍ-Π = nr 𝟘 𝟙 𝟙 𝟘 𝟘

opaque

  -- A grade that is used in the implementation of boolrec.

  boolrecᵍ-nc₁ : M
  boolrecᵍ-nc₁ = nr 𝟘 𝟙 𝟘 𝟘 𝟙

opaque

  -- A grade that is used in the implementation of boolrec.

  boolrecᵍ-nc₂ : M
  boolrecᵍ-nc₂ = nr boolrecᵍ-nc₁ 𝟘 𝟘 𝟘 𝟙

opaque

  -- A function that is used in the implementation of boolrec.

  boolrecᵍ-nc₃ : M → M
  boolrecᵍ-nc₃ p = ⌜ ⌞ boolrecᵍ-Π ⌟ ⌝ · Boolᵍ + p · ω

opaque

  -- A grade that is used in the implementation of boolrec.

  boolrecᵍ-pr : M
  boolrecᵍ-pr = nr boolrecᵍ-nc₂ 𝟘 𝟘 𝟘 𝟙 ∧ boolrecᵍ-Π

------------------------------------------------------------------------
-- Some lemmas about the grades

opaque
  unfolding OKᵍ

  -- If the nr function satisfies Linearity-like-nr-for-𝟘,
  -- then OKᵍ is equal to 𝟘 ∧ 𝟙.

  OKᵍ≡ :
    Has-nr.Linearity-like-nr-for-𝟘 has-nr →
    OKᵍ ≡ 𝟘 ∧ 𝟙
  OKᵍ≡ hyp =
    nr 𝟘 𝟘 𝟘 𝟘 𝟙                 ≡⟨ hyp ⟩
    ((𝟙 ∧ 𝟘) · 𝟙 + 𝟘) ∧ (𝟙 + 𝟘)  ≡⟨ cong₂ _∧_ (M.+-identityʳ _) (M.+-identityʳ _) ⟩
    ((𝟙 ∧ 𝟘) · 𝟙) ∧ 𝟙            ≡⟨ cong (flip _∧_ _) $ M.·-identityʳ _ ⟩
    (𝟙 ∧ 𝟘) ∧ 𝟙                  ≡⟨ cong (flip _∧_ _) $ M.∧-comm _ _ ⟩
    (𝟘 ∧ 𝟙) ∧ 𝟙                  ≡⟨ M.∧-assoc _ _ _ ⟩
    𝟘 ∧ (𝟙 ∧ 𝟙)                  ≡⟨ cong (_∧_ _) $ M.∧-idem _ ⟩
    𝟘 ∧ 𝟙                        ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque
  unfolding Boolᵍ

  -- If the nr function satisfies Linearity-like-nr-for-𝟘,
  -- then Boolᵍ is equal to 𝟘 ∧ 𝟙.

  Boolᵍ≡ :
    Has-nr.Linearity-like-nr-for-𝟘 has-nr →
    Boolᵍ ≡ 𝟘 ∧ 𝟙
  Boolᵍ≡ hyp =
    nr OKᵍ 𝟘 𝟘 𝟘 𝟙                 ≡⟨ hyp ⟩
    ((𝟙 ∧ OKᵍ) · 𝟙 + 𝟘) ∧ (𝟙 + 𝟘)  ≡⟨ cong₂ _∧_ (M.+-identityʳ _) (M.+-identityʳ _) ⟩
    ((𝟙 ∧ OKᵍ) · 𝟙) ∧ 𝟙            ≡⟨ cong (flip _∧_ _) $ M.·-identityʳ _ ⟩
    (𝟙 ∧ OKᵍ) ∧ 𝟙                  ≡⟨ cong (flip _∧_ _) $ M.∧-comm _ _ ⟩
    (OKᵍ ∧ 𝟙) ∧ 𝟙                  ≡⟨ M.∧-assoc _ _ _ ⟩
    OKᵍ ∧ (𝟙 ∧ 𝟙)                  ≡⟨ cong (_∧_ _) $ M.∧-idem _ ⟩
    OKᵍ ∧ 𝟙                        ≡⟨ cong (_∧ _) $ OKᵍ≡ hyp ⟩
    (𝟘 ∧ 𝟙) ∧ 𝟙                    ≡⟨ M.∧-assoc _ _ _ ⟩
    𝟘 ∧ (𝟙 ∧ 𝟙)                    ≡⟨ cong (_∧_ _) $ M.∧-idem _ ⟩
    𝟘 ∧ 𝟙                          ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque
  unfolding boolrecᵍ-Π

  -- If the nr function satisfies Linearity-like-nr-for-𝟙,
  -- then boolrecᵍ-Π is equal to 𝟙.

  boolrecᵍ-Π≡ :
    Has-nr.Linearity-like-nr-for-𝟙 has-nr →
    boolrecᵍ-Π ≡ 𝟙
  boolrecᵍ-Π≡ hyp =
    nr 𝟘 𝟙 𝟙 𝟘 𝟘             ≡⟨ hyp ⟩
    (𝟙 + 𝟘) · 𝟘 + ω · 𝟘 + 𝟙  ≡⟨ trans (cong₂ _+_ (M.·-zeroʳ _) (cong (flip _+_ _) $ M.·-zeroʳ _)) $
                                trans (M.+-identityˡ _) $
                                M.+-identityˡ _ ⟩
    𝟙                        ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque
  unfolding boolrecᵍ-nc₁

  -- If the nr function satisfies Linearity-like-nr-for-𝟙,
  -- then boolrecᵍ-nc₁ is equal to 𝟙.

  boolrecᵍ-nc₁≡ :
    Has-nr.Linearity-like-nr-for-𝟙 has-nr →
    boolrecᵍ-nc₁ ≡ 𝟙
  boolrecᵍ-nc₁≡ hyp =
    nr 𝟘 𝟙 𝟘 𝟘 𝟙             ≡⟨ hyp ⟩
    (𝟙 + 𝟘) · 𝟙 + ω · 𝟘 + 𝟘  ≡⟨ cong₂ _+_ (cong (flip _·_ _) $ M.+-identityʳ _) (M.+-identityʳ _) ⟩
    𝟙 · 𝟙 + ω · 𝟘            ≡⟨ cong₂ _+_ (M.·-identityˡ _) (M.·-zeroʳ _) ⟩
    𝟙 + 𝟘                    ≡⟨ M.+-identityʳ _ ⟩
    𝟙                        ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque

  -- A lemma used below.

  [[𝟙∧𝟙]·𝟙+𝟘]∧[𝟙+𝟘]≡𝟙 : ((𝟙 ∧ 𝟙) · 𝟙 + 𝟘) ∧ (𝟙 + 𝟘) ≡ 𝟙
  [[𝟙∧𝟙]·𝟙+𝟘]∧[𝟙+𝟘]≡𝟙 =
    ((𝟙 ∧ 𝟙) · 𝟙 + 𝟘) ∧ (𝟙 + 𝟘)  ≡⟨ cong₂ _∧_ (M.+-identityʳ _) (M.+-identityʳ _) ⟩
    ((𝟙 ∧ 𝟙) · 𝟙) ∧ 𝟙            ≡⟨ cong (flip _∧_ _) $ M.·-identityʳ _ ⟩
    (𝟙 ∧ 𝟙) ∧ 𝟙                  ≡⟨ cong (flip _∧_ _) $ M.∧-comm _ _ ⟩
    (𝟙 ∧ 𝟙) ∧ 𝟙                  ≡⟨ M.∧-assoc _ _ _ ⟩
    𝟙 ∧ (𝟙 ∧ 𝟙)                  ≡⟨ cong (_∧_ _) $ M.∧-idem _ ⟩
    𝟙 ∧ 𝟙                        ≡⟨ M.∧-idem _ ⟩
    𝟙                            ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque
  unfolding boolrecᵍ-nc₂

  -- If the nr function satisfies Linearity-like-nr-for-𝟘
  -- and Linearity-like-nr-for-𝟙, then boolrecᵍ-nc₂ is equal to 𝟙.

  boolrecᵍ-nc₂≡ :
    Has-nr.Linearity-like-nr-for-𝟘 has-nr →
    Has-nr.Linearity-like-nr-for-𝟙 has-nr →
    boolrecᵍ-nc₂ ≡ 𝟙
  boolrecᵍ-nc₂≡ hyp₁ hyp₂ =
    nr boolrecᵍ-nc₁ 𝟘 𝟘 𝟘 𝟙      ≡⟨ cong (λ p → nr p _ _ _ _) $ boolrecᵍ-nc₁≡ hyp₂ ⟩
    nr 𝟙 𝟘 𝟘 𝟘 𝟙                 ≡⟨ hyp₁ ⟩
    ((𝟙 ∧ 𝟙) · 𝟙 + 𝟘) ∧ (𝟙 + 𝟘)  ≡⟨ [[𝟙∧𝟙]·𝟙+𝟘]∧[𝟙+𝟘]≡𝟙 ⟩
    𝟙                            ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque
  unfolding boolrecᵍ-pr

  -- If the nr function satisfies Linearity-like-nr-for-𝟘
  -- and Linearity-like-nr-for-𝟙, then boolrecᵍ-pr is equal to 𝟙.

  boolrecᵍ-pr≡ :
    Has-nr.Linearity-like-nr-for-𝟘 has-nr →
    Has-nr.Linearity-like-nr-for-𝟙 has-nr →
    boolrecᵍ-pr ≡ 𝟙
  boolrecᵍ-pr≡ hyp₁ hyp₂ =
    nr boolrecᵍ-nc₂ 𝟘 𝟘 𝟘 𝟙 ∧ boolrecᵍ-Π  ≡⟨ cong₂ _∧_
                                               (cong (λ p → nr p _ _ _ _) $ boolrecᵍ-nc₂≡ hyp₁ hyp₂)
                                               (boolrecᵍ-Π≡ hyp₂) ⟩
    nr 𝟙 𝟘 𝟘 𝟘 𝟙 ∧ 𝟙                      ≡⟨ cong (flip _∧_ _) hyp₁ ⟩
    (((𝟙 ∧ 𝟙) · 𝟙 + 𝟘) ∧ (𝟙 + 𝟘)) ∧ 𝟙     ≡⟨ cong (flip _∧_ _) [[𝟙∧𝟙]·𝟙+𝟘]∧[𝟙+𝟘]≡𝟙 ⟩
    𝟙 ∧ 𝟙                                 ≡⟨ M.∧-idem _ ⟩
    𝟙                                     ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque
  unfolding boolrecᵍ-pr

  -- If the modality's zero is well-behaved, then boolrecᵍ-pr is
  -- non-zero.

  boolrecᵍ-pr≢𝟘 :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero M.semiring-with-meet ⦄ →
    boolrecᵍ-pr ≢ 𝟘
  boolrecᵍ-pr≢𝟘 =
    nr boolrecᵍ-nc₂ 𝟘 𝟘 𝟘 𝟙 ∧ boolrecᵍ-Π ≡ 𝟘  →⟨ ∧-positiveˡ ⟩
    nr boolrecᵍ-nc₂ 𝟘 𝟘 𝟘 𝟙 ≡ 𝟘               →⟨ proj₂ ∘→ proj₂ ∘→ nr-positive ⟩
    𝟙 ≡ 𝟘                                     →⟨ non-trivial ⟩
    ⊥                                         □

------------------------------------------------------------------------
-- Term formers

private module B = Definition.Untyped.Bool 𝕄 ω Boolᵍ OKᵍ

-- Export some term formers from Definition.Untyped.Bool

open B using (OK; Bool; true; false; Targetᵇʳ) public

opaque
  unfolding B.boolrec

  -- An eliminator for Bool.

  boolrec : M → Term (1+ n) → Term n → Term n → Term n → Term n
  boolrec p A t u v =
    B.boolrec boolrecᵍ-pr boolrecᵍ-nc₁ boolrecᵍ-nc₂ (boolrecᵍ-nc₃ p) boolrecᵍ-Π p A t u v

------------------------------------------------------------------------
-- Unfolding, substitution and weakening lemmas

-- Export lemmas from Definition.Untyped.Bool

open B using
  (Targetᵇʳ≡; OK-[]; Bool-[]; true-[]; false-[];
   Targetᵇʳ-[⇑]; Targetᵇʳ-+-[⇑]; Targetᵇʳ-[₀⇑]; Targetᵇʳ-[↑⇑]; Targetᵇʳ-[,⇑];
   wk-OK; wk-Bool; wk-true; wk-false; wk-liftn-Targetᵇʳ; Targetᵇʳ-wk[]′)
   public

opaque
  unfolding boolrec

  -- A substitution lemma for boolrec.

  boolrec-[] :
    boolrec p A t u v [ σ ] ≡
    boolrec p (A [ σ ⇑ ]) (t [ σ ]) (u [ σ ]) (v [ σ ])
  boolrec-[] {v} = B.boolrec-[] {v = v}

opaque
  unfolding boolrec

  -- A weakening lemma for boolrec.

  wk-boolrec :
    wk ρ (boolrec p A t u v) ≡
    boolrec p (wk (lift ρ) A) (wk ρ t) (wk ρ u) (wk ρ v)
  wk-boolrec = B.wk-boolrec
