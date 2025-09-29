------------------------------------------------------------------------
-- A translation that can modify occurrences of []-cong and/or J
--
-- Possibilities include removing []-cong and removing J 𝟘 𝟘, see
-- Graded.Modify-box-cong-or-J.Configuration.
------------------------------------------------------------------------

import Definition.Typed.Restrictions
import Graded.Modality
import Graded.Modify-box-cong-or-J.Configuration
import Graded.Usage.Restrictions

module Graded.Modify-box-cong-or-J
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (open Definition.Typed.Restrictions 𝕄)
  (open Graded.Usage.Restrictions 𝕄)
  {TRₛ : Type-restrictions}
  {URₛ : Usage-restrictions}
  (open Graded.Modify-box-cong-or-J.Configuration TRₛ URₛ)
  -- A record that configures the translation.
  (conf : Configuration)
  where

open Configuration conf
open Modality 𝕄

open import Definition.Typed.Properties TRₜ hiding ([]-cong′)

open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Graded.Context 𝕄
open import Graded.Erasure.Extraction 𝕄
import Graded.Erasure.SucRed
import Graded.Erasure.Target as T
open import Graded.Mode 𝕄
open import Graded.Usage.Erased-matches
open import Graded.Usage.Restrictions.Natrec 𝕄

open import Tools.Bool
open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation

private
  module Sₛ = Graded.Erasure.SucRed TRₛ
  module Sₜ = Graded.Erasure.SucRed TRₜ

private variable
  b         : Bool
  α k n     : Nat
  x         : Fin _
  ∇ ∇₁ ∇₂   : DCon _ _
  φ φ₁ φ₂   : Unfolding _
  Δ         : Con _ _
  Γ         : Cons _ _
  ρ         : Wk _ _
  σ         : Subst _ _
  A B t u v : Term _
  γ         : Conₘ _
  m         : Mode
  s         : T.Strictness

------------------------------------------------------------------------
-- The translation

opaque

  -- The translation.

  tr : Term n → Term n
  tr (var x) =
    var x
  tr (defn α) =
    defn α
  tr (U l) =
    U l
  tr Empty =
    Empty
  tr (emptyrec p A t) =
    emptyrec p (tr A) (tr t)
  tr (Unit s l) =
    Unit s l
  tr (star s l) =
    star s l
  tr (unitrec l p q A t u) =
    unitrec l p q (tr A) (tr t) (tr u)
  tr (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B) =
    ΠΣ⟨ b ⟩ p , q ▷ tr A ▹ tr B
  tr (lam p t) =
    lam p (tr t)
  tr (t ∘⟨ p ⟩ u) =
    tr t ∘⟨ p ⟩ tr u
  tr (prod s p t u) =
    prod s p (tr t) (tr u)
  tr (fst p t) =
    fst p (tr t)
  tr (snd p t) =
    snd p (tr t)
  tr (prodrec r p q A t u) =
    prodrec r p q (tr A) (tr t) (tr u)
  tr ℕ =
    ℕ
  tr zero =
    zero
  tr (suc t) =
    suc (tr t)
  tr (natrec p q r A t u v) =
    natrec p q r (tr A) (tr t) (tr u) (tr v)
  tr (Id A t u) =
    Id (tr A) (tr t) (tr u)
  tr rfl =
    rfl
  tr (J p q A t B u v w) =
    J′ p q (tr A) (tr t) (tr B) (tr u) (tr v) (tr w)
  tr (K p A t B u v) =
    K p (tr A) (tr t) (tr B) (tr u) (tr v)
  tr ([]-cong s A t u v) =
    []-cong′ s (tr A) (tr t) (tr u) (tr v)

------------------------------------------------------------------------
-- Some simple lemmas

opaque
  unfolding tr

  -- The translation of sucᵏ n is sucᵏ n.

  tr-sucᵏ : tr {n = k} (sucᵏ n) PE.≡ sucᵏ n
  tr-sucᵏ {n = 0}    = PE.refl
  tr-sucᵏ {n = 1+ _} = PE.cong suc tr-sucᵏ

opaque
  unfolding tr

  -- If []-cong and J are both replaced by themselves, then the
  -- translation does not change anything.

  tr-id :
    (∀ {n s} {A t u v : Term n} →
     []-cong′ s A t u v PE.≡ []-cong s A t u v) →
    (∀ {n p q} {A t : Term n} {B u v w} →
     J′ p q A t B u v w PE.≡ J p q A t B u v w) →
    tr t PE.≡ t
  tr-id []-cong′≡[]-cong J′≡J = tr-id′ _
    where
    tr-id′ : (t : Term n) → tr t PE.≡ t
    tr-id′ = λ where
      (var _) →
        PE.refl
      (defn _) →
        PE.refl
      (U _) →
        PE.refl
      Empty →
        PE.refl
      (emptyrec _ A t) →
        PE.cong₂ (emptyrec _) (tr-id′ A) (tr-id′ t)
      (Unit _ _) →
        PE.refl
      (star _ _) →
        PE.refl
      (unitrec _ _ _ A t u) →
        PE.cong₃ (unitrec _ _ _) (tr-id′ A) (tr-id′ t) (tr-id′ u)
      (ΠΣ⟨ _ ⟩ _ , _ ▷ A ▹ B) →
        PE.cong₂ (ΠΣ⟨ _ ⟩ _ , _ ▷_▹_) (tr-id′ A) (tr-id′ B)
      (lam _ t) →
        PE.cong (lam _) (tr-id′ t)
      (t ∘⟨ _ ⟩ u) →
        PE.cong₂ (_∘⟨ _ ⟩_) (tr-id′ t) (tr-id′ u)
      (prod _ _ t u) →
        PE.cong₂ (prod _ _) (tr-id′ t) (tr-id′ u)
      (fst _ t) →
        PE.cong (fst _) (tr-id′ t)
      (snd _ t) →
        PE.cong (snd _) (tr-id′ t)
      (prodrec _ _ _ A t u) →
        PE.cong₃ (prodrec _ _ _) (tr-id′ A) (tr-id′ t) (tr-id′ u)
      ℕ →
        PE.refl
      zero →
        PE.refl
      (suc t) →
        PE.cong suc (tr-id′ t)
      (natrec _ _ _ A t u v) →
        PE.cong₄ (natrec _ _ _) (tr-id′ A) (tr-id′ t) (tr-id′ u)
          (tr-id′ v)
      (Id A t u) →
        PE.cong₃ Id (tr-id′ A) (tr-id′ t) (tr-id′ u)
      rfl →
        PE.refl
      (J p q A t B u v w) →
        let open Tools.Reasoning.PropositionalEquality in
        J′ p q (tr A) (tr t) (tr B) (tr u) (tr v) (tr w)  ≡⟨ PE.cong₆ (J′ _ _) (tr-id′ A) (tr-id′ t) (tr-id′ B) (tr-id′ u) (tr-id′ v) (tr-id′ w) ⟩
        J′ p q A t B u v w                                ≡⟨ J′≡J ⟩
        J p q A t B u v w                                 ∎
      (K _ A t B u v) →
        PE.cong₅ (K _) (tr-id′ A) (tr-id′ t) (tr-id′ B)
          (tr-id′ u) (tr-id′ v)
      ([]-cong s A t u v) →
        let open Tools.Reasoning.PropositionalEquality in
        []-cong′ s (tr A) (tr t) (tr u) (tr v)  ≡⟨ PE.cong₄ ([]-cong′ _) (tr-id′ A) (tr-id′ t) (tr-id′ u) (tr-id′ v) ⟩
        []-cong′ s A t u v                      ≡⟨ []-cong′≡[]-cong ⟩
        []-cong s A t u v                       ∎

------------------------------------------------------------------------
-- A weakening lemma

opaque
  unfolding tr

  -- Translation commutes with weakening.

  tr-wk : ∀ t → tr (wk ρ t) PE.≡ wk ρ (tr t)
  tr-wk {ρ} = λ where
    (var _) →
      PE.refl
    (defn _) →
      PE.refl
    (U _) →
      PE.refl
    Empty →
      PE.refl
    (emptyrec _ A t) →
      PE.cong₂ (emptyrec _) (tr-wk A) (tr-wk t)
    (Unit _ _) →
      PE.refl
    (star _ _) →
      PE.refl
    (unitrec _ _ _ A t u) →
      PE.cong₃ (unitrec _ _ _) (tr-wk A) (tr-wk t) (tr-wk u)
    (ΠΣ⟨ _ ⟩ _ , _ ▷ A ▹ B) →
      PE.cong₂ (ΠΣ⟨ _ ⟩ _ , _ ▷_▹_) (tr-wk A) (tr-wk B)
    (lam _ t) →
      PE.cong (lam _) (tr-wk t)
    (t ∘⟨ _ ⟩ u) →
      PE.cong₂ (_∘⟨ _ ⟩_) (tr-wk t) (tr-wk u)
    (prod _ _ t u) →
      PE.cong₂ (prod _ _) (tr-wk t) (tr-wk u)
    (fst _ t) →
      PE.cong (fst _) (tr-wk t)
    (snd _ t) →
      PE.cong (snd _) (tr-wk t)
    (prodrec _ _ _ A t u) →
      PE.cong₃ (prodrec _ _ _) (tr-wk A) (tr-wk t) (tr-wk u)
    ℕ →
      PE.refl
    zero →
      PE.refl
    (suc t) →
      PE.cong suc (tr-wk t)
    (natrec _ _ _ A t u v) →
      PE.cong₄ (natrec _ _ _) (tr-wk A) (tr-wk t) (tr-wk u)
        (tr-wk v)
    (Id A t u) →
      PE.cong₃ Id (tr-wk A) (tr-wk t) (tr-wk u)
    rfl →
      PE.refl
    (J p q A t B u v w) →
      let open Tools.Reasoning.PropositionalEquality in
      J′ p q (tr (wk ρ A)) (tr (wk ρ t)) (tr (wk (liftn ρ 2) B))
        (tr (wk ρ u)) (tr (wk ρ v)) (tr (wk ρ w))                 ≡⟨ PE.cong₆ (J′ _ _) (tr-wk A) (tr-wk t)
                                                                       (tr-wk B) (tr-wk u) (tr-wk v) (tr-wk w) ⟩
      J′ p q (wk ρ (tr A)) (wk ρ (tr t)) (wk (liftn ρ 2) (tr B))
        (wk ρ (tr u)) (wk ρ (tr v)) (wk ρ (tr w))                 ≡˘⟨ wk-J′ ⟩

      wk ρ (J′ p q (tr A) (tr t) (tr B) (tr u) (tr v) (tr w))     ∎
    (K _ A t B u v) →
      PE.cong₅ (K _) (tr-wk A) (tr-wk t) (tr-wk B)
        (tr-wk u) (tr-wk v)
    ([]-cong s A t u v) →
      let open Tools.Reasoning.PropositionalEquality in
      []-cong′ s (tr (wk ρ A)) (tr (wk ρ t)) (tr (wk ρ u)) (tr (wk ρ v))  ≡⟨ PE.cong₄ ([]-cong′ _) (tr-wk A) (tr-wk t) (tr-wk u) (tr-wk v) ⟩
      []-cong′ s (wk ρ (tr A)) (wk ρ (tr t)) (wk ρ (tr u)) (wk ρ (tr v))  ≡˘⟨ wk-[]-cong′ ⟩
      wk ρ ([]-cong′ s (tr A) (tr t) (tr u) (tr v))                       ∎

------------------------------------------------------------------------
-- Some substitution lemmas

opaque
 unfolding tr
 mutual

  -- Translation commutes with substitution.

  tr-[] : ∀ t → tr (t [ σ ]) PE.≡ tr t [ tr ∘→ σ ]
  tr-[] {σ} = λ where
    (var _) →
      PE.refl
    (defn _) →
      PE.refl
    (U _) →
      PE.refl
    Empty →
      PE.refl
    (emptyrec _ A t) →
      PE.cong₂ (emptyrec _) (tr-[] A) (tr-[] t)
    (Unit _ _) →
      PE.refl
    (star _ _) →
      PE.refl
    (unitrec _ _ _ A t u) →
      PE.cong₃ (unitrec _ _ _) (tr-[⇑] A) (tr-[] t)
        (tr-[] u)
    (ΠΣ⟨ _ ⟩ _ , _ ▷ A ▹ B) →
      PE.cong₂ (ΠΣ⟨ _ ⟩ _ , _ ▷_▹_) (tr-[] A) (tr-[⇑] B)
    (lam _ t) →
      PE.cong (lam _) (tr-[⇑] t)
    (t ∘⟨ _ ⟩ u) →
      PE.cong₂ (_∘⟨ _ ⟩_) (tr-[] t) (tr-[] u)
    (prod _ _ t u) →
      PE.cong₂ (prod _ _) (tr-[] t) (tr-[] u)
    (fst _ t) →
      PE.cong (fst _) (tr-[] t)
    (snd _ t) →
      PE.cong (snd _) (tr-[] t)
    (prodrec _ _ _ A t u) →
      PE.cong₃ (prodrec _ _ _) (tr-[⇑] A) (tr-[] t)
        (tr-[⇑²] u)
    ℕ →
      PE.refl
    zero →
      PE.refl
    (suc t) →
      PE.cong suc (tr-[] t)
    (natrec _ _ _ A t u v) →
      PE.cong₄ (natrec _ _ _) (tr-[⇑] A) (tr-[] t)
        (tr-[⇑²] u) (tr-[] v)
    (Id A t u) →
      PE.cong₃ Id (tr-[] A) (tr-[] t) (tr-[] u)
    rfl →
      PE.refl
    (J p q A t B u v w) →
      let open Tools.Reasoning.PropositionalEquality in
      J′ p q (tr (A [ σ ])) (tr (t [ σ ])) (tr (B [ σ ⇑[ 2 ] ]))
        (tr (u [ σ ])) (tr (v [ σ ])) (tr (w [ σ ]))                ≡⟨ PE.cong₆ (J′ _ _) (tr-[] A) (tr-[] t) (tr-[⇑²] B)
                                                                         (tr-[] u) (tr-[] v) (tr-[] w) ⟩
      J′ p q (tr A [ tr ∘→ σ ]) (tr t [ tr ∘→ σ ])
        (tr B [ (tr ∘→ σ) ⇑[ 2 ] ]) (tr u [ tr ∘→ σ ])
        (tr v [ tr ∘→ σ ]) (tr w [ tr ∘→ σ ])                       ≡˘⟨ J′-[] ⟩

      J′ p q (tr A) (tr t) (tr B) (tr u) (tr v) (tr w) [ tr ∘→ σ ]  ∎
    (K _ A t B u v) →
      PE.cong₅ (K _) (tr-[] A) (tr-[] t) (tr-[⇑] B)
        (tr-[] u) (tr-[] v)
    ([]-cong s A t u v) →
      let open Tools.Reasoning.PropositionalEquality in
      []-cong′ s (tr (A [ σ ])) (tr (t [ σ ])) (tr (u [ σ ]))
        (tr (v [ σ ]))                                         ≡⟨ PE.cong₄ ([]-cong′ _) (tr-[] A) (tr-[] t) (tr-[] u) (tr-[] v) ⟩

      []-cong′ s (tr A [ tr ∘→ σ ]) (tr t [ tr ∘→ σ ])
        (tr u [ tr ∘→ σ ]) (tr v [ tr ∘→ σ ])                  ≡˘⟨ []-cong′-[] ⟩

      []-cong′ s (tr A) (tr t) (tr u) (tr v) [ tr ∘→ σ ]       ∎

  -- A variant of tr-[].

  tr-[⇑] : ∀ t → tr (t [ σ ⇑ ]) PE.≡ tr t [ (tr ∘→ σ) ⇑ ]
  tr-[⇑] {σ} t =
    tr (t [ σ ⇑ ])        ≡⟨ tr-[] t ⟩
    tr t [ tr ∘→ σ ⇑ ]    ≡⟨ (flip substVar-to-subst (tr t) λ where
                                x0     → PE.refl
                                (x +1) → tr-wk (σ x)) ⟩
    tr t [ (tr ∘→ σ) ⇑ ]  ∎
    where
    open Tools.Reasoning.PropositionalEquality

  -- A variant of tr-[].

  tr-[⇑²] : ∀ t → tr (t [ σ ⇑[ 2 ] ]) PE.≡ tr t [ (tr ∘→ σ) ⇑[ 2 ] ]
  tr-[⇑²] {σ} t =
    tr (t [ σ ⇑[ 2 ] ])        ≡⟨ tr-[] t ⟩

    tr t [ tr ∘→ σ ⇑[ 2 ] ]    ≡⟨ (flip substVar-to-subst (tr t) λ {
                                     x0        → PE.refl;
                                     (x0 +1)   → PE.refl;
                                     (x +1 +1) →
      tr (wk[ 2 ] (σ x))               ≡⟨ PE.cong tr $ wk[]≡wk[]′ {t = σ _} ⟩
      tr (wk[ 2 ]′ (σ x))              ≡⟨ tr-wk (σ x) ⟩
      wk[ 2 ]′ (tr (σ x))              ≡˘⟨ wk[]≡wk[]′ ⟩
      wk[ 2 ] (tr (σ x))               ∎ }) ⟩

    tr t [ (tr ∘→ σ) ⇑[ 2 ] ]  ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque
  unfolding tr

  -- A variant of tr-[].

  tr-[]₀ : ∀ t → tr (t [ u ]₀) PE.≡ tr t [ tr u ]₀
  tr-[]₀ {u} t =
    tr (t [ sgSubst u ])      ≡⟨ tr-[] t ⟩
    tr t [ tr ∘→ sgSubst u ]  ≡⟨ (flip substVar-to-subst (tr t) λ where
                                    x0     → PE.refl
                                    (_ +1) → PE.refl) ⟩
    tr t [ sgSubst (tr u) ]   ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque
  unfolding tr

  -- A variant of tr-[].

  tr-[]₁₀ : ∀ t → tr (t [ u , v ]₁₀) PE.≡ tr t [ tr u , tr v ]₁₀
  tr-[]₁₀ {u} {v} t =
    tr (t [ consSubst (sgSubst u) v ])          ≡⟨ tr-[] t ⟩
    tr t [ tr ∘→ consSubst (sgSubst u) v ]      ≡⟨ (flip substVar-to-subst (tr t) λ where
                                                      x0        → PE.refl
                                                      (x0 +1)   → PE.refl
                                                      (_ +1 +1) → PE.refl) ⟩
    tr t [ consSubst (sgSubst (tr u)) (tr v) ]  ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque
  unfolding tr

  -- A variant of tr-[].

  tr-[]↑² : ∀ t → tr (t [ u ]↑²) PE.≡ tr t [ tr u ]↑²
  tr-[]↑² {u} t =
    tr (t [ consSubst (wkSubst 2 idSubst) u ])      ≡⟨ tr-[] t ⟩
    tr t [ tr ∘→ consSubst (wkSubst 2 idSubst) u ]  ≡⟨ (flip substVar-to-subst (tr t) λ where
                                                          x0     → PE.refl
                                                          (_ +1) → PE.refl) ⟩
    tr t [ consSubst (wkSubst 2 idSubst) (tr u) ]   ∎
    where
    open Tools.Reasoning.PropositionalEquality

------------------------------------------------------------------------
-- The translation is usage-preserving

opaque
  unfolding tr

  -- The translation is usage-preserving.

  tr-▸ : γ Uₛ.▸[ m ] t → γ Uₜ.▸[ m ] tr t
  tr-▸ {m} = λ where
    (Uₛ.sub t δ≤γ) →
      Uₜ.sub (tr-▸ t) δ≤γ
    Uₛ.var →
      Uₜ.var
    Uₛ.defn →
      Uₜ.defn
    Uₛ.Uₘ →
      Uₜ.Uₘ
    Uₛ.Emptyₘ →
      Uₜ.Emptyₘ
    (Uₛ.emptyrecₘ t A ok) →
      Uₜ.emptyrecₘ (tr-▸ t) (tr-▸ A) (Emptyrec-allowed-→ m ok)
    Uₛ.Unitₘ →
      Uₜ.Unitₘ
    (Uₛ.starˢₘ ok) →
      Uₜ.starˢₘ (ok ∘→ (_∘→ Starˢ-sink-→))
    Uₛ.starʷₘ →
      Uₜ.starʷₘ
    (Uₛ.unitrecₘ t u A ok) →
      Uₜ.unitrecₘ (tr-▸ t) (tr-▸ u) (tr-▸ A) (Unitrec-allowed-→ m ok)
    (Uₛ.ΠΣₘ A B) →
      Uₜ.ΠΣₘ (tr-▸ A) (tr-▸ B)
    (Uₛ.lamₘ t) →
      Uₜ.lamₘ (tr-▸ t)
    (t Uₛ.∘ₘ u) →
      tr-▸ t Uₜ.∘ₘ tr-▸ u
    (Uₛ.prodˢₘ t u) →
      Uₜ.prodˢₘ (tr-▸ t) (tr-▸ u)
    (Uₛ.fstₘ m t PE.refl ok) →
      Uₜ.fstₘ m (tr-▸ t) PE.refl ok
    (Uₛ.sndₘ t) →
      Uₜ.sndₘ (tr-▸ t)
    (Uₛ.prodʷₘ t u) →
      Uₜ.prodʷₘ (tr-▸ t) (tr-▸ u)
    (Uₛ.prodrecₘ t u A ok) →
      Uₜ.prodrecₘ (tr-▸ t) (tr-▸ u) (tr-▸ A) (Prodrec-allowed-→ m ok)
    Uₛ.ℕₘ →
      Uₜ.ℕₘ
    Uₛ.zeroₘ →
      Uₜ.zeroₘ
    (Uₛ.sucₘ t) →
      Uₜ.sucₘ (tr-▸ t)
    (Uₛ.natrecₘ ⦃ has-nr ⦄ t u v A) →
      PE.subst (Uₜ._▸[ _ ] _)
        (PE.cong (λ has-nr → nrᶜ ⦃ has-nr = has-nr ⦄ _ _ _ _ _) $
         let lemma :
               {m₁ m₂ : Natrec-mode}
               (eq : m₁ PE.≡ m₂) {has-nr : Natrec-mode-has-nr m₁} →
               Natrec-mode-Has-nr
                 (PE.subst Natrec-mode-has-nr eq has-nr) PE.≡
               Natrec-mode-Has-nr has-nr
             lemma = λ { PE.refl → PE.refl }
        in
        lemma natrec-mode-≡) $
      Uₜ.natrecₘ
        ⦃ has-nr = PE.subst Natrec-mode-has-nr natrec-mode-≡ has-nr ⦄
        (tr-▸ t) (tr-▸ u) (tr-▸ v) (tr-▸ A)
    (Uₛ.natrec-no-nrₘ ⦃ no-nr ⦄ t u v A ok₁ ok₂ ok₃ ok₄) →
      Uₜ.natrec-no-nrₘ
        ⦃ no-nr = PE.subst Natrec-mode-no-nr natrec-mode-≡ no-nr ⦄
        (tr-▸ t) (tr-▸ u) (tr-▸ v) (tr-▸ A) ok₁ ok₂ ok₃ ok₄
    (Uₛ.natrec-no-nr-glbₘ ⦃ no-nr ⦄ t u v A ok₁ ok₂) →
      Uₜ.natrec-no-nr-glbₘ
        ⦃ no-nr = PE.subst Natrec-mode-no-nr-glb natrec-mode-≡ no-nr ⦄
        (tr-▸ t) (tr-▸ u) (tr-▸ v) (tr-▸ A) ok₁ ok₂
    (Uₛ.Idₘ not-erased A t u) →
      Uₜ.Idₘ (not-erased ∘→ Id-erased-⇔ .proj₂) (tr-▸ A) (tr-▸ t)
        (tr-▸ u)
    (Uₛ.Id₀ₘ erased A t u) →
      Uₜ.Id₀ₘ (Id-erased-⇔ .proj₁ erased) (tr-▸ A) (tr-▸ t) (tr-▸ u)
    Uₛ.rflₘ →
      Uₜ.rflₘ
    (Uₛ.Jₘ ok₁ ok₂ A t B u v w) →
      ▸J′ ok₁ ok₂ (tr-▸ A) (tr-▸ t) (tr-▸ B) (tr-▸ u) (tr-▸ v) (tr-▸ w)
    (Uₛ.J₀ₘ₁ ok PE.refl PE.refl A t B u v w) →
      ▸J′₀₁ ok (tr-▸ A) (tr-▸ t) (tr-▸ B) (tr-▸ u) (tr-▸ v) (tr-▸ w)
    (Uₛ.J₀ₘ₂ ok A t B u v w) →
      ▸J′₀₂ ok (tr-▸ A) (tr-▸ t) (tr-▸ B) (tr-▸ u) (tr-▸ v) (tr-▸ w)
    (Uₛ.Kₘ ok₁ ok₂ A t B u v) →
      Uₜ.Kₘ (PE.subst (_≤ᵉᵐ _) erased-matches-for-K-≡ ok₁)
        (ok₂ ∘→ PE.trans erased-matches-for-K-≡) (tr-▸ A) (tr-▸ t)
        (tr-▸ B) (tr-▸ u) (tr-▸ v)
    (Uₛ.K₀ₘ₁ ok₁ ok₂ A t B u v) →
      Uₜ.K₀ₘ₁ (PE.trans (PE.sym erased-matches-for-K-≡) ok₁) ok₂
        (tr-▸ A) (tr-▸ t) (tr-▸ B) (tr-▸ u) (tr-▸ v)
    (Uₛ.K₀ₘ₂ ok A t B u v) →
      Uₜ.K₀ₘ₂ (PE.trans (PE.sym erased-matches-for-K-≡) ok) (tr-▸ A)
        (tr-▸ t) (tr-▸ B) (tr-▸ u) (tr-▸ v)
    (Uₛ.[]-congₘ A t u v ok) →
      ▸[]-cong′ ok (tr-▸ A) (tr-▸ t) (tr-▸ u) (tr-▸ v)

opaque

  -- A variant of tr-▸ for ▸[_]_.

  tr-▸-DCon : Uₛ.▸[ m ] ∇ → Uₜ.▸[ m ] map-DCon tr ∇
  tr-▸-DCon ▸∇ α↦t =
    case lemma α↦t of λ {
      (_ , _ , PE.refl , PE.refl , α↦) →
    tr-▸ (▸∇ α↦) }
    where
    lemma :
      α ↦ t ∷ A ∈ map-DCon tr ∇ →
      ∃₂ λ t′ A′ → t PE.≡ tr t′ × A PE.≡ tr A′ × α ↦ t′ ∷ A′ ∈ ∇
    lemma {∇ = ε}                 ()
    lemma {∇ = ∇ ∙⟨ _ ⟩[ _ ∷ _ ]} here =
      _ , _ , PE.refl , PE.refl , here
    lemma {∇ = ∇ ∙⟨ _ ⟩[ _ ∷ _ ]} (there α↦) =
      Σ.map idᶠ (Σ.map idᶠ (Σ.map idᶠ (Σ.map idᶠ there))) (lemma α↦)

------------------------------------------------------------------------
-- The translation is type-preserving

opaque

  -- A preservation lemma for _∷_∈_.

  tr-∷∈ : x Tₛ.∷ A ∈ Δ → x Tₜ.∷ tr A ∈ map-Con tr Δ
  tr-∷∈ = λ where
    (Tₛ.here {A}) →
      PE.subst (flip (Tₜ._∷_∈_ _) _) (PE.sym $ tr-wk A)
        Tₜ.here
    (Tₛ.there {A} x∈) →
      PE.subst (flip (Tₜ._∷_∈_ _) _) (PE.sym $ tr-wk A) $
      Tₜ.there (tr-∷∈ x∈)

opaque

  -- A preservation lemma for _↦∷_∈_.

  tr-↦∈ : α ↦∷ A ∈ ∇ → α ↦∷ tr A ∈ map-DCon tr ∇
  tr-↦∈ = λ where
    here       → here
    (there α↦) → there (tr-↦∈ α↦)

opaque

  -- A preservation lemma for _↦_∷_∈_.

  tr-↦∷∈ : α ↦ t ∷ A ∈ ∇ → α ↦ tr t ∷ tr A ∈ map-DCon tr ∇
  tr-↦∷∈ = λ where
    here       → here
    (there α↦) → there (tr-↦∷∈ α↦)

opaque

  -- A preservation lemma for _»_↜_.

  tr-»↜ : φ Tₛ.» ∇₂ ↜ ∇₁ → φ Tₜ.» map-DCon tr ∇₂ ↜ map-DCon tr ∇₁
  tr-»↜ = λ where
      Tₛ.ε →
        Tₜ.ε
      (∇₂↜∇₁ Tₛ.⁰) →
        tr-»↜ ∇₂↜∇₁ Tₜ.⁰
      (∇₂↜∇₁ Tₛ.¹ᵒ) →
        PE.subst (Tₜ._» _ ↜ _) lemma (tr-»↜ ∇₂↜∇₁) Tₜ.¹ᵒ
      (∇₂↜∇₁ Tₛ.¹ᵗ) →
        tr-»↜ ∇₂↜∇₁ Tₜ.¹ᵗ
    where
    lemma : φ₁ Tₛ.⊔ᵒᵗ φ₂ PE.≡ φ₁ Tₜ.⊔ᵒᵗ φ₂
    lemma rewrite unfolding-mode-≡ = PE.refl

opaque
 unfolding tr
 mutual

  -- A preservation lemma for »_.

  tr-» : Tₛ.» ∇ → Tₜ.» map-DCon tr ∇
  tr-» = λ where
    Tₛ.ε →
      Tₜ.ε
    Tₛ.∙ᵒ⟨ ok , ∇′↜∇ ⟩[ ⊢t ∷ ⊢A ] →
      Tₜ.∙ᵒ⟨ Opacity-allowed-→ ok , tr-»↜ ∇′↜∇ ⟩[ tr-⊢∷ ⊢t ∷ tr-⊢ ⊢A ]
    Tₛ.∙ᵗ[ ⊢t ] →
      Tₜ.∙ᵗ[ tr-⊢∷ ⊢t ]

  -- A preservation lemma for ⊢_.

  tr-⊢′ : Tₛ.⊢ Γ → Tₜ.⊢ map-Cons tr Γ
  tr-⊢′ = λ where
    (Tₛ.ε »∇) →
      Tₜ.ε (tr-» »∇)
    (Tₛ.∙ ⊢A) →
      Tₜ.∙ tr-⊢ ⊢A

  -- A preservation lemma for _⊢_.

  tr-⊢ : Γ Tₛ.⊢ A → map-Cons tr Γ Tₜ.⊢ tr A
  tr-⊢ = λ where
    (Tₛ.Uⱼ ⊢Γ) →
      Tₜ.Uⱼ (tr-⊢′ ⊢Γ)
    (Tₛ.univ ⊢A) →
      Tₜ.univ (tr-⊢∷ ⊢A)
    (Tₛ.Emptyⱼ ⊢Γ) →
      Tₜ.Emptyⱼ (tr-⊢′ ⊢Γ)
    (Tₛ.Unitⱼ ⊢Γ ok) →
      Tₜ.Unitⱼ (tr-⊢′ ⊢Γ) (Unit-allowed-→ ok)
    (Tₛ.ΠΣⱼ ⊢B ok) →
      Tₜ.ΠΣⱼ (tr-⊢ ⊢B) (ΠΣ-allowed-→ ok)
    (Tₛ.ℕⱼ ⊢Γ) →
      Tₜ.ℕⱼ (tr-⊢′ ⊢Γ)
    (Tₛ.Idⱼ _ ⊢t ⊢u) →
      Idⱼ′ (tr-⊢∷ ⊢t) (tr-⊢∷ ⊢u)

  -- A preservation lemma for _⊢_∷_.

  tr-⊢∷ : Γ Tₛ.⊢ t ∷ A → map-Cons tr Γ Tₜ.⊢ tr t ∷ tr A
  tr-⊢∷ = λ where
    (Tₛ.conv ⊢t A≡B) →
      Tₜ.conv (tr-⊢∷ ⊢t) (tr-⊢≡ A≡B)
    (Tₛ.var ⊢Γ x∈) →
      Tₜ.var (tr-⊢′ ⊢Γ) (tr-∷∈ x∈)
    (Tₛ.defn {A′} ⊢Γ α∈ PE.refl) →
      Tₜ.defn (tr-⊢′ ⊢Γ) (tr-↦∈ α∈) (tr-wk A′)
    (Tₛ.Uⱼ ⊢Γ) →
      Tₜ.Uⱼ (tr-⊢′ ⊢Γ)
    (Tₛ.Emptyⱼ ⊢Γ) →
      Tₜ.Emptyⱼ (tr-⊢′ ⊢Γ)
    (Tₛ.emptyrecⱼ ⊢A ⊢t) →
      Tₜ.emptyrecⱼ (tr-⊢ ⊢A) (tr-⊢∷ ⊢t)
    (Tₛ.Unitⱼ ⊢Γ ok) →
      Tₜ.Unitⱼ (tr-⊢′ ⊢Γ) (Unit-allowed-→ ok)
    (Tₛ.starⱼ ⊢Γ ok) →
      Tₜ.starⱼ (tr-⊢′ ⊢Γ) (Unit-allowed-→ ok)
    (Tₛ.unitrecⱼ {A} ⊢A ⊢t ⊢u _) →
      PE.subst (Tₜ._⊢_∷_ _ _) (PE.sym $ tr-[]₀ A) $
      unitrecⱼ′ (tr-⊢ ⊢A) (tr-⊢∷ ⊢t)
        (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ A) $
         tr-⊢∷ ⊢u)
    (Tₛ.ΠΣⱼ ⊢A ⊢B ok) →
      Tₜ.ΠΣⱼ (tr-⊢∷ ⊢A) (tr-⊢∷ ⊢B) (ΠΣ-allowed-→ ok)
    (Tₛ.lamⱼ _ ⊢t ok) →
      lamⱼ′ (ΠΣ-allowed-→ ok) (tr-⊢∷ ⊢t)
    (Tₛ._∘ⱼ_ {G = B} ⊢t ⊢u) →
      PE.subst (Tₜ._⊢_∷_ _ _) (PE.sym $ tr-[]₀ B) $
      tr-⊢∷ ⊢t Tₜ.∘ⱼ tr-⊢∷ ⊢u
    (Tₛ.prodⱼ {G = B} ⊢B ⊢t ⊢u ok) →
      Tₜ.prodⱼ (tr-⊢ ⊢B) (tr-⊢∷ ⊢t)
        (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ B) $
         tr-⊢∷ ⊢u)
        (ΠΣ-allowed-→ ok)
    (Tₛ.fstⱼ _ ⊢t) →
      fstⱼ′ (tr-⊢∷ ⊢t)
    (Tₛ.sndⱼ {G = B} _ ⊢t) →
      PE.subst (Tₜ._⊢_∷_ _ _) (PE.sym $ tr-[]₀ B) $
      sndⱼ′ (tr-⊢∷ ⊢t)
    (Tₛ.prodrecⱼ {A = C} ⊢C ⊢t ⊢u _) →
      PE.subst (Tₜ._⊢_∷_ _ _) (PE.sym $ tr-[]₀ C) $
      prodrecⱼ′ (tr-⊢ ⊢C) (tr-⊢∷ ⊢t)
        (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]↑² C) $
         tr-⊢∷ ⊢u)
    (Tₛ.ℕⱼ ⊢Γ) →
      Tₜ.ℕⱼ (tr-⊢′ ⊢Γ)
    (Tₛ.zeroⱼ ⊢Γ) →
      Tₜ.zeroⱼ (tr-⊢′ ⊢Γ)
    (Tₛ.sucⱼ ⊢t) →
      Tₜ.sucⱼ (tr-⊢∷ ⊢t)
    (Tₛ.natrecⱼ {A} ⊢t ⊢u ⊢v) →
      PE.subst (Tₜ._⊢_∷_ _ _) (PE.sym $ tr-[]₀ A) $
      Tₜ.natrecⱼ
        (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ A) $
         tr-⊢∷ ⊢t)
        (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]↑² A) $
         tr-⊢∷ ⊢u)
        (tr-⊢∷ ⊢v)
    (Tₛ.Idⱼ ⊢A ⊢t ⊢u) →
      Tₜ.Idⱼ (tr-⊢∷ ⊢A) (tr-⊢∷ ⊢t) (tr-⊢∷ ⊢u)
    (Tₛ.rflⱼ ⊢t) →
      Tₜ.rflⱼ (tr-⊢∷ ⊢t)
    (Tₛ.Jⱼ {t} {A} {B} _ ⊢B ⊢u _ ⊢w) →
      PE.subst (Tₜ._⊢_∷_ _ _) (PE.sym $ tr-[]₁₀ B) $
      ⊢J′
        (PE.subst (flip Tₜ._⊢_ _)
           (PE.cong (_»_ _) $ PE.cong (_∙_ _) $
            PE.cong₃ Id (tr-wk A) (tr-wk t) PE.refl) $
         tr-⊢ ⊢B)
        (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₁₀ B) $
         tr-⊢∷ ⊢u)
        (tr-⊢∷ ⊢w)
    (Tₛ.Kⱼ {B} ⊢B ⊢u ⊢v ok) →
      PE.subst (Tₜ._⊢_∷_ _ _) (PE.sym $ tr-[]₀ B) $
      Tₜ.Kⱼ (tr-⊢ ⊢B)
        (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ B) $
         tr-⊢∷ ⊢u)
        (tr-⊢∷ ⊢v) (K-allowed-→ ok)
    (Tₛ.[]-congⱼ _ _ _ ⊢v ok) →
      ⊢[]-cong′ ok (tr-⊢∷ ⊢v)

  -- A preservation lemma for _⊢_≡_.

  tr-⊢≡ :
    Γ Tₛ.⊢ A ≡ B → map-Cons tr Γ Tₜ.⊢ tr A ≡ tr B
  tr-⊢≡ = λ where
    (Tₛ.refl ⊢A) →
      Tₜ.refl (tr-⊢ ⊢A)
    (Tₛ.sym A₁≡A₂) →
      Tₜ.sym (tr-⊢≡ A₁≡A₂)
    (Tₛ.trans A₁≡A₂ A₂≡A₃) →
      Tₜ.trans (tr-⊢≡ A₁≡A₂) (tr-⊢≡ A₂≡A₃)
    (Tₛ.univ A₁≡A₂) →
      Tₜ.univ (tr-⊢≡∷ A₁≡A₂)
    (Tₛ.ΠΣ-cong A₁≡A₂ B₁≡B₂ ok) →
      Tₜ.ΠΣ-cong (tr-⊢≡ A₁≡A₂) (tr-⊢≡ B₁≡B₂) (ΠΣ-allowed-→ ok)
    (Tₛ.Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) →
      Tₜ.Id-cong (tr-⊢≡ A₁≡A₂) (tr-⊢≡∷ t₁≡t₂) (tr-⊢≡∷ u₁≡u₂)

  -- A preservation lemma for _⊢_≡_∷_.

  tr-⊢≡∷ :
    Γ Tₛ.⊢ t ≡ u ∷ A →
    map-Cons tr Γ Tₜ.⊢ tr t ≡ tr u ∷ tr A
  tr-⊢≡∷ = λ where
    (Tₛ.conv t₁≡t₂ A₁≡A₂) →
      Tₜ.conv (tr-⊢≡∷ t₁≡t₂) (tr-⊢≡ A₁≡A₂)
    (Tₛ.refl ⊢t) →
      Tₜ.refl (tr-⊢∷ ⊢t)
    (Tₛ.sym _ t₁≡t₂) →
      sym′ (tr-⊢≡∷ t₁≡t₂)
    (Tₛ.trans t₁≡t₂ t₂≡t₃) →
      Tₜ.trans (tr-⊢≡∷ t₁≡t₂) (tr-⊢≡∷ t₂≡t₃)
    (Tₛ.δ-red {t′} {A′} ⊢Γ α∈ PE.refl PE.refl) →
      Tₜ.δ-red (tr-⊢′ ⊢Γ) (tr-↦∷∈ α∈) (tr-wk A′) (tr-wk t′)
    (Tₛ.emptyrec-cong A₁≡A₂ t₁≡t₂) →
      Tₜ.emptyrec-cong (tr-⊢≡ A₁≡A₂) (tr-⊢≡∷ t₁≡t₂)
    (Tₛ.η-unit ⊢t₁ ⊢t₂ ok) →
      Tₜ.η-unit (tr-⊢∷ ⊢t₁) (tr-⊢∷ ⊢t₂) (Unit-with-η-⇔ .proj₁ ok)
    (Tₛ.unitrec-cong {A = A₁} A₁≡A₂ t₁≡t₂ u₁≡u₂ _ _) →
      PE.subst (Tₜ._⊢_≡_∷_ _ _ _) (PE.sym $ tr-[]₀ A₁) $
      unitrec-cong′ (tr-⊢≡ A₁≡A₂) (tr-⊢≡∷ t₁≡t₂)
        (PE.subst (Tₜ._⊢_≡_∷_ _ _ _) (tr-[]₀ A₁) $
         tr-⊢≡∷ u₁≡u₂)
    (Tₛ.unitrec-β {A} ⊢A ⊢t _ _) →
      PE.subst (Tₜ._⊢_≡_∷_ _ _ _) (PE.sym $ tr-[]₀ A) $
      unitrec-β-≡ (tr-⊢ ⊢A)
        (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ A) $
         tr-⊢∷ ⊢t)
    (Tₛ.unitrec-β-η {A} ⊢A ⊢t ⊢u ok η) →
      PE.subst (Tₜ._⊢_≡_∷_ _ _ _) (PE.sym $ tr-[]₀ A) $
      Tₜ.unitrec-β-η (tr-⊢ ⊢A) (tr-⊢∷ ⊢t)
        (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ A) $
         tr-⊢∷ ⊢u)
        (Unit-allowed-→ ok) (Unitʷ-η-⇔ .proj₁ η)
    (Tₛ.ΠΣ-cong A₁≡A₂ B₁≡B₂ ok) →
      Tₜ.ΠΣ-cong (tr-⊢≡∷ A₁≡A₂) (tr-⊢≡∷ B₁≡B₂) (ΠΣ-allowed-→ ok)
    (Tₛ.app-cong {G = B} t₁≡t₂ u₁≡u₂) →
      PE.subst (Tₜ._⊢_≡_∷_ _ _ _) (PE.sym $ tr-[]₀ B) $
      Tₜ.app-cong (tr-⊢≡∷ t₁≡t₂) (tr-⊢≡∷ u₁≡u₂)
    (Tₛ.β-red {G = B} {t} _ ⊢t ⊢u PE.refl ok) →
      PE.subst₂ (Tₜ._⊢_≡_∷_ _ _)
        (PE.sym $ tr-[]₀ t) (PE.sym $ tr-[]₀ B) $
      β-red-≡ (tr-⊢∷ ⊢t) (tr-⊢∷ ⊢u) (ΠΣ-allowed-→ ok)
    (Tₛ.η-eq {f = t₁} {g = t₂} _ ⊢t₁ ⊢t₂ t₁∘0≡t₂∘0 _) →
      η-eq′ (tr-⊢∷ ⊢t₁) (tr-⊢∷ ⊢t₂)
        (PE.subst₃ (Tₜ._⊢_≡_∷_ _)
           (PE.cong (_∘⟨ _ ⟩ _) (tr-wk t₁))
           (PE.cong (_∘⟨ _ ⟩ _) (tr-wk t₂)) PE.refl $
         tr-⊢≡∷ t₁∘0≡t₂∘0)
    (Tₛ.prod-cong {G = B} ⊢B t₁≡t₂ u₁≡u₂ ok) →
      Tₜ.prod-cong (tr-⊢ ⊢B) (tr-⊢≡∷ t₁≡t₂)
        (PE.subst (Tₜ._⊢_≡_∷_ _ _ _) (tr-[]₀ B) $
         tr-⊢≡∷ u₁≡u₂)
        (ΠΣ-allowed-→ ok)
    (Tₛ.fst-cong _ t₁≡t₂) →
      fst-cong′ (tr-⊢≡∷ t₁≡t₂)
    (Tₛ.Σ-β₁ {G = B} ⊢B ⊢t ⊢u eq ok) →
      Tₜ.Σ-β₁ (tr-⊢ ⊢B) (tr-⊢∷ ⊢t)
        (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ B) $
         tr-⊢∷ ⊢u)
        eq (ΠΣ-allowed-→ ok)
    (Tₛ.snd-cong {G = B} _ t₁≡t₂) →
      PE.subst (Tₜ._⊢_≡_∷_ _ _ _) (PE.sym $ tr-[]₀ B) $
      snd-cong′ (tr-⊢≡∷ t₁≡t₂)
    (Tₛ.Σ-β₂ {G = B} ⊢B ⊢t ⊢u eq ok) →
      PE.subst (Tₜ._⊢_≡_∷_ _ _ _) (PE.sym $ tr-[]₀ B) $
      Tₜ.Σ-β₂ (tr-⊢ ⊢B) (tr-⊢∷ ⊢t)
        (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ B) $
         tr-⊢∷ ⊢u)
        eq (ΠΣ-allowed-→ ok)
    (Tₛ.Σ-η {G = B} _ ⊢t₁ ⊢t₂ fst-t₁≡fst-t₂ snd-t₁≡snd-t₂ _) →
      Σ-η′ (tr-⊢∷ ⊢t₁) (tr-⊢∷ ⊢t₂) (tr-⊢≡∷ fst-t₁≡fst-t₂)
        (PE.subst (Tₜ._⊢_≡_∷_ _ _ _) (tr-[]₀ B) $
         tr-⊢≡∷ snd-t₁≡snd-t₂)
    (Tₛ.prodrec-cong {A = C₁} C₁≡C₂ t₁≡t₂ u₁≡u₂ _) →
      PE.subst (Tₜ._⊢_≡_∷_ _ _ _) (PE.sym $ tr-[]₀ C₁) $
      prodrec-cong′ (tr-⊢≡ C₁≡C₂) (tr-⊢≡∷ t₁≡t₂)
        (PE.subst (Tₜ._⊢_≡_∷_ _ _ _) (tr-[]↑² C₁) $
         tr-⊢≡∷ u₁≡u₂)
    (Tₛ.prodrec-β {G = B} {A = C} {u} ⊢C ⊢t ⊢u ⊢v eq ok) →
      PE.subst₂ (Tₜ._⊢_≡_∷_ _ _)
        (PE.sym $ tr-[]₁₀ u) (PE.sym $ tr-[]₀ C) $
      Tₜ.prodrec-β (tr-⊢ ⊢C) (tr-⊢∷ ⊢t)
        (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ B) $
         tr-⊢∷ ⊢u)
        (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]↑² C) $
         tr-⊢∷ ⊢v)
        eq (ΠΣ-allowed-→ ok)
    (Tₛ.suc-cong t₁≡t₂) →
      Tₜ.suc-cong (tr-⊢≡∷ t₁≡t₂)
    (Tₛ.natrec-cong {A = A₁} A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂) →
      PE.subst (Tₜ._⊢_≡_∷_ _ _ _) (PE.sym $ tr-[]₀ A₁) $
      Tₜ.natrec-cong (tr-⊢≡ A₁≡A₂)
        (PE.subst (Tₜ._⊢_≡_∷_ _ _ _) (tr-[]₀ A₁) $
         tr-⊢≡∷ t₁≡t₂)
        (PE.subst (Tₜ._⊢_≡_∷_ _ _ _) (tr-[]↑² A₁) $
         tr-⊢≡∷ u₁≡u₂)
        (tr-⊢≡∷ v₁≡v₂)
    (Tₛ.natrec-zero {A} ⊢t ⊢u) →
      PE.subst (Tₜ._⊢_≡_∷_ _ _ _) (PE.sym $ tr-[]₀ A) $
      Tₜ.natrec-zero
        (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ A) $
         tr-⊢∷ ⊢t)
        (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]↑² A) $
         tr-⊢∷ ⊢u)
    (Tₛ.natrec-suc {A} {s = u} ⊢t ⊢u ⊢v) →
      PE.subst₂ (Tₜ._⊢_≡_∷_ _ _)
        (PE.sym $ tr-[]₁₀ u) (PE.sym $ tr-[]₀ A) $
      Tₜ.natrec-suc
        (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ A) $
         tr-⊢∷ ⊢t)
        (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]↑² A) $
         tr-⊢∷ ⊢u)
        (tr-⊢∷ ⊢v)
    (Tₛ.Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) →
      Tₜ.Id-cong (tr-⊢≡∷ A₁≡A₂) (tr-⊢≡∷ t₁≡t₂) (tr-⊢≡∷ u₁≡u₂)
    (Tₛ.J-cong {A₁} {t₁} {B₁} A₁≡A₂ _ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁≡w₂) →
      PE.subst (Tₜ._⊢_≡_∷_ _ _ _) (PE.sym $ tr-[]₁₀ B₁) $
      J′-cong (tr-⊢≡ A₁≡A₂) (tr-⊢≡∷ t₁≡t₂)
        (PE.subst₃ Tₜ._⊢_≡_
           (PE.cong (_»_ _) $ PE.cong (_∙_ _) $
            PE.cong₃ Id (tr-wk A₁) (tr-wk t₁) PE.refl)
           PE.refl PE.refl $
         tr-⊢≡ B₁≡B₂)
        (PE.subst (Tₜ._⊢_≡_∷_ _ _ _) (tr-[]₁₀ B₁) $
         tr-⊢≡∷ u₁≡u₂)
        (tr-⊢≡∷ v₁≡v₂) (tr-⊢≡∷ w₁≡w₂)
    (Tₛ.J-β {t} {A} {B} ⊢t ⊢B ⊢u PE.refl) →
      PE.subst (Tₜ._⊢_≡_∷_ _ _ _) (PE.sym $ tr-[]₁₀ B) $
      J′-β-≡ (tr-⊢∷ ⊢t)
        (PE.subst (flip Tₜ._⊢_ _)
           (PE.cong (_»_ _) $ PE.cong (_∙_ _) $
            PE.cong₃ Id (tr-wk A) (tr-wk t) PE.refl) $
         tr-⊢ ⊢B)
        (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₁₀ B) $
         tr-⊢∷ ⊢u)
    (Tₛ.K-cong {B₁} A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ ok) →
      PE.subst (Tₜ._⊢_≡_∷_ _ _ _) (PE.sym $ tr-[]₀ B₁) $
      Tₜ.K-cong (tr-⊢≡ A₁≡A₂) (tr-⊢≡∷ t₁≡t₂) (tr-⊢≡ B₁≡B₂)
        (PE.subst (Tₜ._⊢_≡_∷_ _ _ _) (tr-[]₀ B₁) $
         tr-⊢≡∷ u₁≡u₂)
        (tr-⊢≡∷ v₁≡v₂) (K-allowed-→ ok)
    (Tₛ.K-β {B} ⊢B ⊢u ok) →
      PE.subst (Tₜ._⊢_≡_∷_ _ _ _) (PE.sym $ tr-[]₀ B) $
      Tₜ.K-β (tr-⊢ ⊢B)
        (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ B) $
         tr-⊢∷ ⊢u)
        (K-allowed-→ ok)
    (Tₛ.[]-cong-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ ok) →
      []-cong′-cong ok (tr-⊢≡ A₁≡A₂) (tr-⊢≡∷ t₁≡t₂) (tr-⊢≡∷ u₁≡u₂)
        (tr-⊢≡∷ v₁≡v₂)
    (Tₛ.[]-cong-β ⊢t PE.refl ok) →
      []-cong′-β-≡ ok (tr-⊢∷ ⊢t)
    (Tₛ.equality-reflection ok _ ⊢v) →
      equality-reflection′ (Equality-reflection-→ ok) (tr-⊢∷ ⊢v)

------------------------------------------------------------------------
-- The translation might preserve reduction

-- The translation preserves (many-step) reduction if
-- preservation-of-reduction is true.

module _ (pres : T preservation-of-reduction) where

  opaque
    unfolding tr

    -- A preservation lemma for _⊢_⇒_∷_.

    tr-⊢⇒∷ :
      Γ Tₛ.⊢ t ⇒ u ∷ A →
      map-Cons tr Γ Tₜ.⊢ tr t ⇒* tr u ∷ tr A
    tr-⊢⇒∷ = λ where
      (Tₛ.conv t⇒t′ A≡B) →
        conv* (tr-⊢⇒∷ t⇒t′) (tr-⊢≡ A≡B)
      (Tₛ.δ-red {t′} {A′} ⊢Γ α↦ PE.refl PE.refl) →
        redMany (Tₜ.δ-red (tr-⊢′ ⊢Γ) (tr-↦∷∈ α↦) (tr-wk A′) (tr-wk t′))
      (Tₛ.emptyrec-subst ⊢A t⇒t′) →
        emptyrec-subst* (tr-⊢⇒∷ t⇒t′) (tr-⊢ ⊢A)
      (Tₛ.unitrec-subst {A} ⊢A ⊢u t⇒t′ _ no-η) →
        PE.subst (Tₜ._⊢_⇒*_∷_ _ _ _) (PE.sym $ tr-[]₀ A) $
        unitrec-subst* (tr-⊢⇒∷ t⇒t′) (tr-⊢ ⊢A)
          (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ A) $
           tr-⊢∷ ⊢u)
          (no-η ∘→ Unitʷ-η-⇔ .proj₂)
      (Tₛ.unitrec-β {A} ⊢A ⊢u _ _) →
        PE.subst (Tₜ._⊢_⇒*_∷_ _ _ _) (PE.sym $ tr-[]₀ A) $
        redMany $
        unitrec-β-⇒ (tr-⊢ ⊢A)
          (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ A) $
           tr-⊢∷ ⊢u)
      (Tₛ.unitrec-β-η {A} ⊢A ⊢t ⊢u ok η) →
        PE.subst (Tₜ._⊢_⇒*_∷_ _ _ _) (PE.sym $ tr-[]₀ A) $
        redMany $
        Tₜ.unitrec-β-η (tr-⊢ ⊢A) (tr-⊢∷ ⊢t)
          (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ A) $
           tr-⊢∷ ⊢u)
          (Unit-allowed-→ ok) (Unitʷ-η-⇔ .proj₁ η)
      (Tₛ.app-subst {G = B} t⇒t′ ⊢u) →
        PE.subst (Tₜ._⊢_⇒*_∷_ _ _ _) (PE.sym $ tr-[]₀ B) $
        app-subst* (tr-⊢⇒∷ t⇒t′) (tr-⊢∷ ⊢u)
      (Tₛ.β-red {G = B} {t} _ ⊢t ⊢u PE.refl ok) →
        PE.subst₂ (Tₜ._⊢_⇒*_∷_ _ _)
          (PE.sym $ tr-[]₀ t) (PE.sym $ tr-[]₀ B) $
        redMany $
        β-red-⇒ (tr-⊢∷ ⊢t) (tr-⊢∷ ⊢u) (ΠΣ-allowed-→ ok)
      (Tₛ.fst-subst _ t⇒t′) →
        fst-subst* (tr-⊢⇒∷ t⇒t′)
      (Tₛ.Σ-β₁ {G = B} ⊢B ⊢t ⊢u eq ok) →
        redMany $
        Tₜ.Σ-β₁ (tr-⊢ ⊢B) (tr-⊢∷ ⊢t)
          (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ B) $
           tr-⊢∷ ⊢u)
          eq (ΠΣ-allowed-→ ok)
      (Tₛ.snd-subst {G = B} _ t⇒t′) →
        PE.subst (Tₜ._⊢_⇒*_∷_ _ _ _) (PE.sym $ tr-[]₀ B) $
        snd-subst* (tr-⊢⇒∷ t⇒t′)
      (Tₛ.Σ-β₂ {G = B} ⊢B ⊢t ⊢u eq ok) →
        PE.subst (Tₜ._⊢_⇒*_∷_ _ _ _) (PE.sym $ tr-[]₀ B) $
        redMany $
        Tₜ.Σ-β₂ (tr-⊢ ⊢B) (tr-⊢∷ ⊢t)
          (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ B) $
           tr-⊢∷ ⊢u)
          eq (ΠΣ-allowed-→ ok)
      (Tₛ.prodrec-subst {A = C} ⊢C ⊢u t⇒t′ _) →
        PE.subst (Tₜ._⊢_⇒*_∷_ _ _ _) (PE.sym $ tr-[]₀ C) $
        prodrec-subst* (tr-⊢ ⊢C) (tr-⊢⇒∷ t⇒t′)
          (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]↑² C) $
           tr-⊢∷ ⊢u)
      (Tₛ.prodrec-β {G = B} {A = C} {u} ⊢C ⊢t ⊢u ⊢v PE.refl _) →
        PE.subst₂ (Tₜ._⊢_⇒*_∷_ _ _)
          (PE.sym $ tr-[]₁₀ u) (PE.sym $ tr-[]₀ C) $
        redMany $
        prodrec-β-⇒ (tr-⊢ ⊢C) (tr-⊢∷ ⊢t)
          (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ B) $
           tr-⊢∷ ⊢u)
          (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]↑² C) $
           tr-⊢∷ ⊢v)
      (Tₛ.natrec-subst {A} ⊢t ⊢u v⇒v′) →
        PE.subst (Tₜ._⊢_⇒*_∷_ _ _ _) (PE.sym $ tr-[]₀ A) $
        natrec-subst*
          (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ A) $
           tr-⊢∷ ⊢t)
          (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]↑² A) $
           tr-⊢∷ ⊢u)
          (tr-⊢⇒∷ v⇒v′)
      (Tₛ.natrec-zero {A} ⊢t ⊢u) →
        PE.subst (Tₜ._⊢_⇒*_∷_ _ _ _) (PE.sym $ tr-[]₀ A) $
        redMany $
        Tₜ.natrec-zero
          (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ A) $
           tr-⊢∷ ⊢t)
          (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]↑² A) $
           tr-⊢∷ ⊢u)
      (Tₛ.natrec-suc {A} {s = u} ⊢t ⊢u ⊢v) →
        PE.subst₂ (Tₜ._⊢_⇒*_∷_ _ _)
          (PE.sym $ tr-[]₁₀ u) (PE.sym $ tr-[]₀ A) $
        redMany $
        Tₜ.natrec-suc
          (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ A) $
           tr-⊢∷ ⊢t)
          (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]↑² A) $
           tr-⊢∷ ⊢u)
          (tr-⊢∷ ⊢v)
      (Tₛ.J-subst {t} {A} {B} ⊢t ⊢B ⊢u ⊢v w⇒w′) →
        PE.subst (Tₜ._⊢_⇒*_∷_ _ _ _) (PE.sym $ tr-[]₁₀ B) $
        J′-subst* pres
          (PE.subst (flip Tₜ._⊢_ _)
             (PE.cong (_»_ _) $ PE.cong (_∙_ _) $
              PE.cong₃ Id (tr-wk A) (tr-wk t) PE.refl) $
           tr-⊢ ⊢B)
          (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₁₀ B) $
           tr-⊢∷ ⊢u)
          (tr-⊢⇒∷ w⇒w′)
      (Tₛ.J-β {t} {A} {B} _ _ t≡t′ ⊢B _ ⊢u) →
        PE.subst (Tₜ._⊢_⇒*_∷_ _ _ _) (PE.sym $ tr-[]₁₀ B) $
        J′-β-⇒* pres (tr-⊢≡∷ t≡t′)
          (PE.subst (flip Tₜ._⊢_ _)
             (PE.cong (_»_ _) $ PE.cong (_∙_ _) $
              PE.cong₃ Id (tr-wk A) (tr-wk t) PE.refl) $
           tr-⊢ ⊢B)
          (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₁₀ B) $
           tr-⊢∷ ⊢u)
      (Tₛ.K-subst {B} ⊢B ⊢u v⇒v′ ok) →
        PE.subst (Tₜ._⊢_⇒*_∷_ _ _ _) (PE.sym $ tr-[]₀ B) $
        K-subst* (tr-⊢ ⊢B)
          (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ B) $
           tr-⊢∷ ⊢u)
          (tr-⊢⇒∷ v⇒v′) (K-allowed-→ ok)
      (Tₛ.K-β {B} ⊢B ⊢u ok) →
        PE.subst (Tₜ._⊢_⇒*_∷_ _ _ _) (PE.sym $ tr-[]₀ B) $
        redMany $
        Tₜ.K-β (tr-⊢ ⊢B)
          (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ B) $
           tr-⊢∷ ⊢u)
          (K-allowed-→ ok)
      (Tₛ.[]-cong-subst _ _ _ v⇒v′ ok) →
        []-cong′-subst* pres ok (tr-⊢⇒∷ v⇒v′)
      (Tₛ.[]-cong-β _ _ _ t≡t′ ok) →
        []-cong′-β-⇒* pres ok (tr-⊢≡∷ t≡t′)

  opaque

    -- A preservation lemma for _⊢_⇒*_∷_.

    tr-⊢⇒*∷ :
      Γ Tₛ.⊢ t ⇒* u ∷ A →
      map-Cons tr Γ Tₜ.⊢ tr t ⇒* tr u ∷ tr A
    tr-⊢⇒*∷ = λ where
      (Tₛ.id ⊢t) →
        Tₜ.id (tr-⊢∷ ⊢t)
      (t⇒u Tₛ.⇨ u⇒*v) →
        tr-⊢⇒∷ t⇒u ⇨∷* tr-⊢⇒*∷ u⇒*v

  opaque
    unfolding tr

    -- A preservation lemma for _⊢_⇒_.

    tr-⊢⇒ :
      Γ Tₛ.⊢ A ⇒ B →
      map-Cons tr Γ Tₜ.⊢ tr A ⇒* tr B
    tr-⊢⇒ = λ where
      (Tₛ.univ A⇒B) → univ* (tr-⊢⇒∷ A⇒B)

  opaque

    -- A preservation lemma for _⊢_⇒*_.

    tr-⊢⇒* :
      Γ Tₛ.⊢ A ⇒* B →
      map-Cons tr Γ Tₜ.⊢ tr A ⇒* tr B
    tr-⊢⇒* = λ where
      (Tₛ.id ⊢A) →
        Tₜ.id (tr-⊢ ⊢A)
      (A⇒B Tₛ.⇨ B⇒*C) →
        tr-⊢⇒ A⇒B ⇨* tr-⊢⇒* B⇒*C

  opaque
    unfolding tr

    -- A preservation lemma for _⊢_⇒ˢ_∷ℕ.

    tr-⊢⇒ˢ∷ℕ :
      Γ Sₛ.⊢ t ⇒ˢ u ∷ℕ →
      map-Cons tr Γ Sₜ.⊢ tr t ⇒ˢ* tr u ∷ℕ
    tr-⊢⇒ˢ∷ℕ = λ where
      (Sₛ.whred t⇒u) →
        Sₜ.whred* (tr-⊢⇒∷ t⇒u)
      (Sₛ.sucred t⇒ˢu) →
        Sₜ.sucred* (tr-⊢⇒ˢ∷ℕ t⇒ˢu)

  opaque
    unfolding tr

    -- A preservation lemma for _⊢_⇒ˢ*_∷ℕ.

    tr-⊢⇒ˢ*∷ℕ :
      Γ Sₛ.⊢ t ⇒ˢ* u ∷ℕ →
      map-Cons tr Γ Sₜ.⊢ tr t ⇒ˢ* tr u ∷ℕ
    tr-⊢⇒ˢ*∷ℕ = λ where
      (Sₛ.id ⊢t) →
        Sₜ.id (tr-⊢∷ ⊢t)
      (t⇒u Sₛ.⇨ˢ u⇒*v) →
        Sₜ.⇒ˢ*∷ℕ-trans (tr-⊢⇒ˢ∷ℕ t⇒u) (tr-⊢⇒ˢ*∷ℕ u⇒*v)

------------------------------------------------------------------------
-- The translation does not affect extraction

opaque
  unfolding tr

  -- The result of extraction is not affected by translation.

  erase-tr : (t : Term n) → erase′ b s (tr t) PE.≡ erase′ b s t
  erase-tr (var _) =
    PE.refl
  erase-tr (defn _) =
    PE.refl
  erase-tr (U _) =
    PE.refl
  erase-tr Empty =
    PE.refl
  erase-tr (emptyrec _ _ _) =
    PE.refl
  erase-tr (Unit _ _) =
    PE.refl
  erase-tr (star _ _) =
    PE.refl
  erase-tr (unitrec _ p _ _ t u) with is-𝟘? p
  … | no _ =
    PE.cong₂ T.unitrec (erase-tr t) (erase-tr u)
  … | yes _ =
    erase-tr u
  erase-tr (ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _) =
    PE.refl
  erase-tr {b = false} (lam _ t) =
    PE.cong T.lam (erase-tr t)
  erase-tr {b = true} (lam p t) with is-𝟘? p
  … | no _ =
    PE.cong T.lam (erase-tr t)
  … | yes _ =
    PE.cong T._[ _ ]₀ (erase-tr t)
  erase-tr (t ∘⟨ p ⟩ u) with is-𝟘? p
  … | no _ =
    PE.cong₂ T._∘⟨ _ ⟩_ (erase-tr t) (erase-tr u)
  … | yes _ =
    PE.cong (app-𝟘′ _ _) (erase-tr t)
  erase-tr (prod _ p t u) with is-𝟘? p
  … | no _ =
    PE.cong₂ T.prod⟨ _ ⟩ (erase-tr t) (erase-tr u)
  … | yes _ =
    erase-tr u
  erase-tr (fst p t) with is-𝟘? p
  … | no _ =
    PE.cong T.fst (erase-tr t)
  … | yes _ =
    PE.refl
  erase-tr (snd p t) with is-𝟘? p
  … | no _ =
    PE.cong T.snd (erase-tr t)
  … | yes _ =
    erase-tr t
  erase-tr (prodrec r _ _ _ t u) with is-𝟘? r
  … | no _ =
    PE.cong₂ (erase-prodrecω _ _) (erase-tr t) (erase-tr u)
  … | yes _ =
    PE.cong T._[ _ , _ ]₁₀ (erase-tr u)
  erase-tr ℕ =
    PE.refl
  erase-tr zero =
    PE.refl
  erase-tr (suc t) =
    PE.cong T.suc⟨ _ ⟩ (erase-tr t)
  erase-tr (natrec _ _ _ _ t u v) =
    PE.cong₃ T.natrec (erase-tr t) (erase-tr u) (erase-tr v)
  erase-tr (Id A t u) =
    PE.refl
  erase-tr rfl =
    PE.refl
  erase-tr {b} {s} (J p q A t B u v w) =
    let open Tools.Reasoning.PropositionalEquality in
    erase′ b s (J′ p q (tr A) (tr t) (tr B) (tr u) (tr v) (tr w))  ≡⟨ erase-J′ ⟩
    erase′ b s (tr u)                                              ≡⟨ erase-tr u ⟩
    erase′ b s u                                                   ≡⟨⟩
    erase′ b s (J p q A t B u v w)                                 ∎
  erase-tr (K _ _ _ _ u _) =
    erase-tr u
  erase-tr {b} {s} ([]-cong str A t u v) =
    let open Tools.Reasoning.PropositionalEquality in
    erase′ b s ([]-cong′ str (tr A) (tr t) (tr u) (tr v))  ≡⟨ erase-[]-cong′ ⟩
    loop? s                                                ≡⟨⟩
    erase′ b s ([]-cong str A t u v)                       ∎
