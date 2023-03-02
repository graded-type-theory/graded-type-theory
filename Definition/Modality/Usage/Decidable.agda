{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- The usage relation can be decided (given certain assumptions)
------------------------------------------------------------------------

open import Definition.Modality
open import Tools.Nullary
open import Tools.Relation

module Definition.Modality.Usage.Decidable
  {a ℓ} {M′ : Setoid a ℓ} (𝕄 : Modality M′)
  (open Setoid M′ renaming (Carrier to M)) (open Modality 𝕄)
  -- Equality is assumed to be decidable for M.
  (_≟_ : Decidable (_≈_))
  -- The Prodrec relation is assumed to be decidable.
  (Prodrec? : ∀ p → Dec (Prodrec p))
  where

open import Definition.Untyped M

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Context.Properties 𝕄
open import Definition.Modality.Usage 𝕄
open import Definition.Modality.Usage.Inversion 𝕄
open import Definition.Modality.Usage.Properties 𝕄

open import Tools.Nat hiding (_≟_)
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    γ : Conₘ n
    t : Term n
    p q : M

_≤?_ : Decidable _≤_
p ≤? q = p ≟ p ∧ q

_≤ᶜ?_ : Decidable (_≤ᶜ_ {n = n})
ε ≤ᶜ? ε = yes ε
(γ ∙ p) ≤ᶜ? (δ ∙ q) with γ ≤ᶜ? δ | p ≤? q
... | _ | no p≰q = no λ { (γ≤δ ∙ p≤q) → p≰q p≤q}
... | no γ≰δ | _ = no λ { (γ≤δ ∙ p≤q) → γ≰δ γ≤δ}
... | yes γ≤δ | yes p≤q = yes (γ≤δ ∙ p≤q)

sub′ : γ ▸ t → p ≤ headₘ γ → tailₘ γ ∙ p ▸ t
sub′ {γ = γ} {t = t} γ▸t p≤q =
  sub (PE.subst (λ γ → γ ▸ t) (PE.sym (headₘ-tailₘ-correct γ)) γ▸t)
      (≤ᶜ-refl ∙ p≤q)

sub″ : γ ▸ t → p ≤ headₘ γ → q ≤ headₘ (tailₘ γ) → tailₘ (tailₘ γ) ∙ q ∙ p ▸ t
sub″ {γ = γ} {t = t} γ▸t p≤p′ q≤q′ =
  sub (PE.subst (λ γ → γ ▸ t) (PE.sym (PE.trans (PE.cong (λ δ → δ ∙ headₘ γ)
                                                         (headₘ-tailₘ-correct (tailₘ γ)))
                                                (headₘ-tailₘ-correct γ))) γ▸t)
      (≤ᶜ-refl ∙ q≤q′ ∙ p≤p′)


⌈⌉▸?_ : (t : Term n) → Dec (⌈ t ⌉ ▸ t)
-- True cases
⌈⌉▸? U = yes Uₘ
⌈⌉▸? ℕ = yes ℕₘ
⌈⌉▸? Empty = yes Emptyₘ
⌈⌉▸? Unit = yes Unitₘ
⌈⌉▸? zero = yes zeroₘ
⌈⌉▸? star = yes starₘ
⌈⌉▸? (var x) = yes var

-- Inspective cases

⌈⌉▸? (Π p , q ▷ F ▹ G)
  with ⌈⌉▸? F | ⌈⌉▸? G
... | no ¬F | _ = no λ γ▸Π →
  let invUsageΠΣ δ▸F _ _ = inv-usage-Π γ▸Π
  in  ¬F (usage-inf δ▸F)
... | _ | no ¬G = no λ γ▸Π →
  let invUsageΠΣ _ δ▸G _ = inv-usage-Π γ▸Π
  in  ¬G (usage-inf δ▸G)
... | yes ▸F | yes ▸G with q ≤? headₘ ⌈ G ⌉
... | yes q≤q′ = yes (Πₘ ▸F (sub′ ▸G q≤q′))
... | no q≰q′ = no λ γ▸Π →
  let invUsageΠΣ _ δ▸G _ = inv-usage-Π γ▸Π
  in  q≰q′ (headₘ-monotone (usage-upper-bound δ▸G))

⌈⌉▸? (Σ⟨ _ ⟩ q ▷ F ▹ G)
  with ⌈⌉▸? F | ⌈⌉▸? G
... | no ¬F | _ = no λ γ▸Σ →
  let invUsageΠΣ δ▸F _ _ = inv-usage-Σ γ▸Σ
  in  ¬F (usage-inf δ▸F)
... | _ | no ¬G = no λ γ▸Σ →
  let invUsageΠΣ _ δ▸G _ = inv-usage-Σ γ▸Σ
  in  ¬G (usage-inf δ▸G)
... | yes ▸F | yes ▸G with q ≤? headₘ ⌈ G ⌉
... | yes q≤q′ = yes (Σₘ ▸F (sub′ ▸G q≤q′))
... | no q≰q′ = no λ γ▸Σ →
  let invUsageΠΣ _ δ▸G _ = inv-usage-Σ γ▸Σ
  in  q≰q′ (headₘ-monotone (usage-upper-bound δ▸G))

⌈⌉▸? (lam p t) with ⌈⌉▸? t
... | no ¬t = no λ γ▸λt →
  let invUsageLam δ▸t _ = inv-usage-lam γ▸λt
  in  ¬t (usage-inf δ▸t)
... | yes ▸t with p ≤? headₘ ⌈ t ⌉
... | yes p≤p′ = yes (lamₘ (sub′ ▸t p≤p′))
... | no p≰p′ = no λ γ▸λt →
  let invUsageLam δ▸t _ = inv-usage-lam γ▸λt
  in  p≰p′ (headₘ-monotone (usage-upper-bound δ▸t))

⌈⌉▸? (t ∘ u) with ⌈⌉▸? t | ⌈⌉▸? u
... | no ¬t | _ = no λ γ▸tu →
  let invUsageApp δ▸t _ _ = inv-usage-app γ▸tu
  in  ¬t (usage-inf δ▸t)
... | _ | no ¬u = no λ γ▸tu →
  let invUsageApp _ δ▸u _ = inv-usage-app γ▸tu
  in  ¬u (usage-inf δ▸u)
... | yes ▸t | yes ▸u = yes (▸t ∘ₘ ▸u)

⌈⌉▸? (prodᵣ t u) with ⌈⌉▸? t | ⌈⌉▸? u
... | no ¬t | _ = no λ γ▸tu →
  let invUsageProdᵣ δ▸t _ _ = inv-usage-prodᵣ γ▸tu
  in  ¬t (usage-inf δ▸t)
... | _ | no ¬u = no λ γ▸tu →
  let invUsageProdᵣ _ δ▸u _ = inv-usage-prodᵣ γ▸tu
  in  ¬u (usage-inf δ▸u)
... | yes ▸t | yes ▸u = yes (prodᵣₘ ▸t ▸u)

⌈⌉▸? (prodₚ t u) with ⌈⌉▸? t | ⌈⌉▸? u
... | no ¬t | _ = no λ γ▸tu →
  let invUsageProdₚ δ▸t _ _ = inv-usage-prodₚ γ▸tu
  in  ¬t (usage-inf δ▸t)
... | _ | no ¬u = no λ γ▸tu →
  let invUsageProdₚ _ δ▸u _ = inv-usage-prodₚ γ▸tu
  in  ¬u (usage-inf δ▸u)
... | yes ▸t | yes ▸u =
  yes (prodₚₘ (sub ▸t (∧ᶜ-decreasingˡ ⌈ t ⌉ ⌈ u ⌉))
              (sub ▸u (∧ᶜ-decreasingʳ ⌈ t ⌉ ⌈ u ⌉)))

⌈⌉▸? (fst t) with ⌈⌉▸? t
... | no ¬t = no λ γ▸t₁ →
  let invUsageProj δ▸t _ = inv-usage-fst γ▸t₁
  in  ¬t (usage-inf δ▸t)
... | yes ▸t = yes (fstₘ ▸t)

⌈⌉▸? (snd t) with ⌈⌉▸? t
... | no ¬t = no λ γ▸t₁ →
  let invUsageProj δ▸t _ = inv-usage-snd γ▸t₁
  in  ¬t (usage-inf δ▸t)
... | yes ▸t = yes (sndₘ ▸t)

⌈⌉▸? (suc t) with ⌈⌉▸? t
... | no ¬t = no λ γ▸t₁ →
  let invUsageSuc δ▸t _ = inv-usage-suc γ▸t₁
  in  ¬t (usage-inf δ▸t)
... | yes ▸t = yes (sucₘ ▸t)

⌈⌉▸? (prodrec p q A t u) with Prodrec? p | ⌈⌉▸? A | ⌈⌉▸? t | ⌈⌉▸? u
... | no ¬P | _ | _ | _ = no λ γ▸pr →
  let invUsageProdrec _ _ _ P _ = inv-usage-prodrec γ▸pr
  in  ¬P P
... | _ | no ¬A | _ | _ = no λ γ▸pr →
  let invUsageProdrec _ _ δ▸A _ _ = inv-usage-prodrec γ▸pr
  in  ¬A (usage-inf δ▸A)
... | _ | _ | no ¬t | _ = no λ γ▸pr →
  let invUsageProdrec δ▸t _ _ _ _ = inv-usage-prodrec γ▸pr
  in  ¬t (usage-inf δ▸t)
... | _ | _ | _ | no ¬u = no λ γ▸pr →
  let invUsageProdrec _ δ▸u _ _ _ = inv-usage-prodrec γ▸pr
  in  ¬u (usage-inf δ▸u)
... | yes P | yes ▸A | yes ▸t | yes ▸u
  with p ≤? headₘ ⌈ u ⌉ | p ≤? headₘ (tailₘ ⌈ u ⌉) | q ≤? headₘ ⌈ A ⌉
... | no p≰p₁ | _ | _ = no λ γ▸pr →
  let invUsageProdrec _ δ▸u _ _ _ = inv-usage-prodrec γ▸pr
  in  p≰p₁ (headₘ-monotone (usage-upper-bound δ▸u))
... | _ | no p≰p₂ | _ = no λ γ▸pr →
  let invUsageProdrec _ δ▸u _ _ _ = inv-usage-prodrec γ▸pr
  in  p≰p₂ (headₘ-monotone (tailₘ-monotone (usage-upper-bound δ▸u)))
... | _ | _ | no q≰q′ = no λ γ▸pr →
  let invUsageProdrec _ _ δ▸A _ _ = inv-usage-prodrec γ▸pr
  in  q≰q′ (headₘ-monotone (usage-upper-bound δ▸A))
... | yes p≤p₁ | yes p≤p₂ | yes q≤q′ =
  yes (prodrecₘ ▸t (sub″ ▸u p≤p₁ p≤p₂)
                (sub′ ▸A q≤q′) P)

⌈⌉▸? (natrec p q r A z s n) with ⌈⌉▸? A | ⌈⌉▸? z | ⌈⌉▸? s | ⌈⌉▸? n
... | no ¬A | _ | _ | _ = no λ γ▸nr →
  let invUsageNatrec _ _ _ δ▸A _ = inv-usage-natrec γ▸nr
  in  ¬A (usage-inf δ▸A)
... | _ | no ¬z | _ | _ = no λ γ▸nr →
  let invUsageNatrec δ▸z _ _ _ _ = inv-usage-natrec γ▸nr
  in  ¬z (usage-inf δ▸z)
... | _ | _ | no ¬s | _ = no λ γ▸nr →
  let invUsageNatrec _ δ▸s _ _ _ = inv-usage-natrec γ▸nr
  in  ¬s (usage-inf δ▸s)
... | _ | _ | _ | no ¬n = no λ γ▸nr →
  let invUsageNatrec _ _ δ▸n _ _ = inv-usage-natrec γ▸nr
  in  ¬n (usage-inf δ▸n)
... | yes ▸A | yes ▸z | yes ▸s | yes ▸n
  with p ≤? headₘ (tailₘ ⌈ s ⌉) | q ≤? headₘ ⌈ A ⌉ | r ≤? headₘ ⌈ s ⌉
... | _ | _ | no r≰r′ = no λ γ▸nr →
  let invUsageNatrec _ δ▸s _ _ _ = inv-usage-natrec γ▸nr
  in  r≰r′ (headₘ-monotone (usage-upper-bound δ▸s))
... | _ | no q≰q′ | _ =  no λ γ▸nr →
  let invUsageNatrec _ _ _ δ▸A _ = inv-usage-natrec γ▸nr
  in  q≰q′ (headₘ-monotone (usage-upper-bound δ▸A))
... | no p≰p′ | _ | _ =  no λ γ▸nr →
  let invUsageNatrec _ δ▸s _ _ _ = inv-usage-natrec γ▸nr
  in  p≰p′ (headₘ-monotone (tailₘ-monotone (usage-upper-bound δ▸s)))
... | yes p≤p′ | yes q≤q′ | yes r≤r′ =
  yes (natrecₘ ▸z (sub″ ▸s r≤r′ p≤p′) ▸n (sub′ ▸A q≤q′))

⌈⌉▸? (Emptyrec p A t) with ⌈⌉▸? A | ⌈⌉▸? t
... | _ | no ¬t =  no λ γ▸er →
  let invUsageEmptyrec δ▸t _ _ = inv-usage-Emptyrec γ▸er
  in  ¬t (usage-inf δ▸t)
... | no ¬A | _ = no λ γ▸er →
  let invUsageEmptyrec _ δ▸A _ = inv-usage-Emptyrec γ▸er
  in  ¬A (usage-inf δ▸A)
... | yes ▸A | yes ▸t = yes (Emptyrecₘ ▸t ▸A)


_▸?_ : (γ : Conₘ n) (t : Term n) → Dec (γ ▸ t)
γ ▸? t with ⌈⌉▸? t
... | no ¬t = no (λ γ▸t → ¬t (usage-inf γ▸t))
... | yes ▸t with γ ≤ᶜ? ⌈ t ⌉
... | no γ≰γ′ = no (λ γ▸t → γ≰γ′ (usage-upper-bound γ▸t))
... | yes γ≤γ′ = yes (sub ▸t γ≤γ′)
