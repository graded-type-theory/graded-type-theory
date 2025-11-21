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

import Definition.Typed
open import Definition.Typed.Inversion TRₛ
import Definition.Typed.Properties

open import Definition.Untyped M
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Properties M
import Definition.Untyped.Sup

open import Graded.Context 𝕄
open import Graded.Erasure.Extraction 𝕄
import Graded.Erasure.SucRed
import Graded.Erasure.Target as T
open import Graded.Mode 𝕄
open import Graded.Usage.Erased-matches
open import Graded.Usage.Restrictions.Natrec 𝕄

open import Tools.Bool
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum

private
  module Sₛ  = Graded.Erasure.SucRed TRₛ
  module Sₜ  = Graded.Erasure.SucRed TRₜ
  module TPₛ = Definition.Typed.Properties TRₛ
  module TPₜ = Definition.Typed.Properties TRₜ
  module USₛ = Definition.Untyped.Sup TRₛ
  module USₜ = Definition.Untyped.Sup TRₜ

private variable
  b                 : Bool
  α k n             : Nat
  x                 : Fin _
  ∇ ∇₁ ∇₂           : DCon _ _
  φ φ₁ φ₂           : Unfolding _
  Δ                 : Con _ _
  Γ                 : Cons _ _
  ρ                 : Wk _ _
  σ                 : Subst _ _
  A B l l₁ l₂ t u v : Term _
  s                 : Strength
  γ                 : Conₘ _
  m                 : Mode
  str               : T.Strictness

------------------------------------------------------------------------
-- The translation

opaque

  -- The translation.

  tr : Term n → Term n
  tr (var x) =
    var x
  tr (defn α) =
    defn α
  tr Level =
    Level
  tr zeroᵘ =
    zeroᵘ
  tr (sucᵘ l) =
    sucᵘ (tr l)
  tr (l₁ supᵘ l₂) =
    tr l₁ supᵘ tr l₂
  tr (U l) =
    U (tr l)
  tr (Lift l A) =
    Lift (tr l) (tr A)
  tr (lift t) =
    lift (tr t)
  tr (lower t) =
    lower (tr t)
  tr Empty =
    Empty
  tr (emptyrec p A t) =
    emptyrec p (tr A) (tr t)
  tr (Unit s) =
    Unit s
  tr (star s) =
    star s
  tr (unitrec p q A t u) =
    unitrec p q (tr A) (tr t) (tr u)
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
  tr ([]-cong s l A t u v) =
    []-cong′ s (tr l) (tr A) (tr t) (tr u) (tr v)

opaque

  private

    -- A function used to implement tr-DCon.

    tr-DCon′ : Bool → DCon (Term 0) n → DCon (Term 0) n
    tr-DCon′ b =
      if b
      then glassify ∘→ map-DCon tr
      else map-DCon tr

  -- Translation of definition contexts.

  tr-DCon : DCon (Term 0) n → DCon (Term 0) n
  tr-DCon = tr-DCon′ glassification

opaque

  -- Translation of context pairs.

  tr-Cons : Cons k n → Cons k n
  tr-Cons (∇ » Γ) = tr-DCon ∇ » map-Con tr Γ

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

  -- Translation leaves level literals unchanged.

  Level-literal→tr-id : Level-literal l → tr l PE.≡ l
  Level-literal→tr-id zeroᵘ        = PE.refl
  Level-literal→tr-id (sucᵘ l-lit) =
    PE.cong sucᵘ (Level-literal→tr-id l-lit)

opaque

  -- The translation of a level literal is a level literal.

  tr-Level-literal : Level-literal l → Level-literal (tr l)
  tr-Level-literal l-lit =
    PE.subst Level-literal (PE.sym $ Level-literal→tr-id l-lit) l-lit

opaque
  unfolding tr

  -- Translation commutes with _supᵘₗ′_ for level literals.

  tr-supᵘₗ′ :
    Level-literal l₁ → Level-literal l₂ →
    tr (l₁ supᵘₗ′ l₂) PE.≡ tr l₁ supᵘₗ′ tr l₂
  tr-supᵘₗ′ {l₁} {l₂} l₁-lit l₂-lit =
    tr (l₁ supᵘₗ′ l₂)   ≡⟨ Level-literal→tr-id $ Level-literal-supᵘₗ′⇔ .proj₂ (l₁-lit , l₂-lit) ⟩
    l₁ supᵘₗ′ l₂        ≡˘⟨ PE.cong₂ _supᵘₗ′_ (Level-literal→tr-id l₁-lit) (Level-literal→tr-id l₂-lit) ⟩
    tr l₁ supᵘₗ′ tr l₂  ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque
  unfolding tr

  -- Translation commutes with _supᵘₗ_ for well-typed levels.

  tr-supᵘₗ :
    Γ Tₛ.⊢ l₁ ∷Level → Γ Tₛ.⊢ l₂ ∷Level →
    tr (l₁ USₛ.supᵘₗ l₂) PE.≡ tr l₁ USₜ.supᵘₗ tr l₂
  tr-supᵘₗ {l₁} {l₂} ⊢l₁ ⊢l₂
    with TRₛ.Level-allowed? | TRₜ.Level-allowed?
  … | yes ok₁ | yes ok₂ =
    tr (l₁ USₛ.supᵘₗ l₂)   ≡⟨ PE.cong tr $ USₛ.supᵘₗ≡supᵘ ok₁ ⟩
    tr (l₁ supᵘ l₂)        ≡⟨⟩
    tr l₁ supᵘ tr l₂       ≡˘⟨ USₜ.supᵘₗ≡supᵘ ok₂ ⟩
    tr l₁ USₜ.supᵘₗ tr l₂  ∎
    where
    open Tools.Reasoning.PropositionalEquality
  … | no not-ok₁ | no not-ok₂ =
    tr (l₁ USₛ.supᵘₗ l₂)   ≡⟨ PE.cong tr $ USₛ.supᵘₗ≡supᵘₗ′ not-ok₁ ⟩
    tr (l₁ supᵘₗ′ l₂)      ≡⟨ tr-supᵘₗ′ (inversion-∷Level ⊢l₁ .proj₂ not-ok₁ .proj₂)
                                (inversion-∷Level ⊢l₂ .proj₂ not-ok₁ .proj₂) ⟩
    tr l₁ supᵘₗ′ tr l₂     ≡˘⟨ USₜ.supᵘₗ≡supᵘₗ′ not-ok₂ ⟩
    tr l₁ USₜ.supᵘₗ tr l₂  ∎
    where
    open Tools.Reasoning.PropositionalEquality
  … | yes ok₁ | no not-ok₂ =
    ⊥-elim (not-ok₂ (Level-allowed-⇔ .proj₁ ok₁))
  … | no not-ok₁ | yes ok₂ =
    ⊥-elim (not-ok₁ (Level-allowed-⇔ .proj₂ ok₂))

-- Some lemmas proved under the assumption that []-cong and J are both
-- replaced by themselves.

module _
  ([]-cong′≡[]-cong :
     ∀ {n s} {l A t u v : Term n} →
     []-cong′ s l A t u v PE.≡ []-cong s l A t u v)
  (J′≡J :
     ∀ {n p q} {A t : Term n} {B u v w} →
     J′ p q A t B u v w PE.≡ J p q A t B u v w)
  where

  opaque
    unfolding tr

    -- The translation does not change anything.

    tr-id : tr t PE.≡ t
    tr-id = tr-id′ _
      where
      tr-id′ : (t : Term n) → tr t PE.≡ t
      tr-id′ = λ where
        (var _) →
          PE.refl
        (defn _) →
          PE.refl
        Level →
          PE.refl
        zeroᵘ →
          PE.refl
        (sucᵘ l) →
          PE.cong sucᵘ tr-id
        (l₁ supᵘ l₂) →
          PE.cong₂ _supᵘ_ tr-id tr-id
        (U l) →
          PE.cong U (tr-id′ l)
        (Lift l A) →
          PE.cong₂ Lift tr-id tr-id
        (lift t) →
          PE.cong lift tr-id
        (lower t) →
          PE.cong lower tr-id
        Empty →
          PE.refl
        (emptyrec _ A t) →
          PE.cong₂ (emptyrec _) (tr-id′ A) (tr-id′ t)
        (Unit _) →
          PE.refl
        (star _) →
          PE.refl
        (unitrec _ _ A t u) →
          PE.cong₃ (unitrec _ _) (tr-id′ A) (tr-id′ t) (tr-id′ u)
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
        ([]-cong s l A t u v) →
          let open Tools.Reasoning.PropositionalEquality in
          []-cong′ s (tr l) (tr A) (tr t) (tr u) (tr v)  ≡⟨ PE.cong₅ ([]-cong′ _) (tr-id′ l) (tr-id′ A) (tr-id′ t) (tr-id′ u) (tr-id′ v) ⟩
          []-cong′ s l A t u v                           ≡⟨ []-cong′≡[]-cong ⟩
          []-cong s l A t u v                            ∎

  opaque

    -- The function map-Con (λ {n = n} → tr {n = n}) does not change
    -- anything.

    map-Con-tr-id : map-Con (λ {n = n} → tr {n = n}) Δ PE.≡ Δ
    map-Con-tr-id {Δ = ε} =
      PE.refl
    map-Con-tr-id {Δ = _ ∙ _} =
      PE.cong₂ _∙_ map-Con-tr-id tr-id

  opaque

    -- The function map-DCon tr does not change anything.

    map-DCon-tr-id : map-DCon tr ∇ PE.≡ ∇
    map-DCon-tr-id {∇ = ε} =
      PE.refl
    map-DCon-tr-id {∇ = _ ∙!} =
      PE.cong₃ _∙⟨ _ ⟩[_∷_] map-DCon-tr-id tr-id tr-id

  opaque
    unfolding tr-DCon

    -- The function tr-DCon is either pointwise equal to glassify or
    -- to the identity function.

    tr-DCon-glassify-id :
      tr-DCon ∇ PE.≡ (if glassification then glassify ∇ else ∇)
    tr-DCon-glassify-id with glassification
    … | true  = PE.cong glassify map-DCon-tr-id
    … | false = map-DCon-tr-id

  opaque
    unfolding tr-Cons

    -- A variant of tr-DCon-glassify-id for tr-Cons.

    tr-Cons-glassify-id :
      tr-Cons (∇ » Δ) PE.≡
      (if glassification then glassify ∇ else ∇) » Δ
    tr-Cons-glassify-id = PE.cong₂ _»_ tr-DCon-glassify-id map-Con-tr-id

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
    Level →
      PE.refl
    zeroᵘ →
      PE.refl
    (sucᵘ l) →
      PE.cong sucᵘ (tr-wk l)
    (l₁ supᵘ l₂) →
      PE.cong₂ _supᵘ_ (tr-wk l₁) (tr-wk l₂)
    (U l) →
      PE.cong U (tr-wk l)
    (Lift l A) →
      PE.cong₂ Lift (tr-wk l) (tr-wk A)
    (lift t) →
      PE.cong lift (tr-wk t)
    (lower t) →
      PE.cong lower (tr-wk t)
    Empty →
      PE.refl
    (emptyrec _ A t) →
      PE.cong₂ (emptyrec _) (tr-wk A) (tr-wk t)
    (Unit _) →
      PE.refl
    (star _) →
      PE.refl
    (unitrec _ _ A t u) →
      PE.cong₃ (unitrec _ _) (tr-wk A) (tr-wk t) (tr-wk u)
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
    ([]-cong s l A t u v) →
      let open Tools.Reasoning.PropositionalEquality in
      []-cong′ s (tr (wk ρ l)) (tr (wk ρ A)) (tr (wk ρ t)) (tr (wk ρ u))
        (tr (wk ρ v))                                                     ≡⟨ PE.cong₅ ([]-cong′ _)
                                                                               (tr-wk l) (tr-wk A) (tr-wk t) (tr-wk u) (tr-wk v) ⟩
      []-cong′ s (wk ρ (tr l)) (wk ρ (tr A)) (wk ρ (tr t)) (wk ρ (tr u))
        (wk ρ (tr v))                                                     ≡˘⟨ wk-[]-cong′ ⟩

      wk ρ ([]-cong′ s (tr l) (tr A) (tr t) (tr u) (tr v))                ∎

private opaque
  unfolding tr Erased.Erased Erased.[_]

  -- A lemma related to tr, Id, Erased and [_].

  tr-Id-Erased-[]-[] :
    let open Erased s in
    Id (Erased (tr l) (tr A)) [ tr t ] ([ tr u ]) PE.≡
    tr (Id (Erased l A) [ t ] ([ u ]))
  tr-Id-Erased-[]-[] {s} {l} =
    PE.cong₃ Id
      (PE.cong (Σ⟨ s ⟩ 𝟘 , 𝟘 ▷_▹_ _) $ PE.sym $ tr-wk (Lift l (Unit _)))
      PE.refl PE.refl

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
    Level →
      PE.refl
    zeroᵘ →
      PE.refl
    (sucᵘ l) →
      PE.cong sucᵘ (tr-[] l)
    (l₁ supᵘ l₂) →
      PE.cong₂ _supᵘ_ (tr-[] l₁) (tr-[] l₂)
    (U l) →
      PE.cong U (tr-[] l)
    (Lift l A) →
      PE.cong₂ Lift (tr-[] l) (tr-[] A)
    (lift t) →
      PE.cong lift (tr-[] t)
    (lower t) →
      PE.cong lower (tr-[] t)
    Empty →
      PE.refl
    (emptyrec _ A t) →
      PE.cong₂ (emptyrec _) (tr-[] A) (tr-[] t)
    (Unit _) →
      PE.refl
    (star _) →
      PE.refl
    (unitrec _ _ A t u) →
      PE.cong₃ (unitrec _ _) (tr-[⇑] A) (tr-[] t) (tr-[] u)
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
    ([]-cong s l A t u v) →
      let open Tools.Reasoning.PropositionalEquality in
      []-cong′ s (tr (l [ σ ])) (tr (A [ σ ])) (tr (t [ σ ]))
        (tr (u [ σ ])) (tr (v [ σ ]))                             ≡⟨ PE.cong₅ ([]-cong′ _) (tr-[] l) (tr-[] A) (tr-[] t) (tr-[] u) (tr-[] v) ⟩

      []-cong′ s (tr l [ tr ∘→ σ ]) (tr A [ tr ∘→ σ ])
        (tr t [ tr ∘→ σ ]) (tr u [ tr ∘→ σ ]) (tr v [ tr ∘→ σ ])  ≡˘⟨ []-cong′-[] ⟩

      []-cong′ s (tr l) (tr A) (tr t) (tr u) (tr v) [ tr ∘→ σ ]   ∎

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
    Uₛ.Levelₘ →
      Uₜ.Levelₘ
    Uₛ.zeroᵘₘ →
      Uₜ.zeroᵘₘ
    (Uₛ.sucᵘₘ l) →
      Uₜ.sucᵘₘ (tr-▸ l)
    (Uₛ.supᵘₘ l₁ l₂) →
      Uₜ.supᵘₘ (tr-▸ l₁) (tr-▸ l₂)
    (Uₛ.Uₘ l) →
      Uₜ.Uₘ (tr-▸ l)
    (Uₛ.Liftₘ l A) →
      Uₜ.Liftₘ (tr-▸ l) (tr-▸ A)
    (Uₛ.liftₘ t) →
      Uₜ.liftₘ (tr-▸ t)
    (Uₛ.lowerₘ t) →
      Uₜ.lowerₘ (tr-▸ t)
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
    (Uₛ.[]-congₘ l A t u v ok) →
      ▸[]-cong′ ok (tr-▸ l) (tr-▸ A) (tr-▸ t) (tr-▸ u) (tr-▸ v)

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
    lemma {∇ = ε}    ()
    lemma {∇ = ∇ ∙!} here =
      _ , _ , PE.refl , PE.refl , here
    lemma {∇ = ∇ ∙!} (there α↦) =
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
  unfolding tr-DCon

  -- A preservation lemma for _↦∷_∈_.

  tr-↦∈ : α ↦∷ A ∈ ∇ → α ↦∷ tr A ∈ tr-DCon ∇
  tr-↦∈ = tr-↦∈′ glassification
    where
    tr-↦∈′ : ∀ b → α ↦∷ A ∈ ∇ → α ↦∷ tr A ∈ tr-DCon′ b ∇
    tr-↦∈′ true  here       = here
    tr-↦∈′ false here       = here
    tr-↦∈′ true  (there α↦) = there (tr-↦∈′ true  α↦)
    tr-↦∈′ false (there α↦) = there (tr-↦∈′ false α↦)

opaque
  unfolding tr-DCon

  -- A preservation lemma for _↦_∷_∈_.

  tr-↦∷∈ : α ↦ t ∷ A ∈ ∇ → α ↦ tr t ∷ tr A ∈ tr-DCon ∇
  tr-↦∷∈ = tr-↦∷∈′ glassification
    where
    tr-↦∷∈′ : ∀ b → α ↦ t ∷ A ∈ ∇ → α ↦ tr t ∷ tr A ∈ tr-DCon′ b ∇
    tr-↦∷∈′ true  here       = here
    tr-↦∷∈′ false here       = here
    tr-↦∷∈′ true  (there α↦) = there (tr-↦∷∈′ true  α↦)
    tr-↦∷∈′ false (there α↦) = there (tr-↦∷∈′ false α↦)

opaque
  unfolding Definition.Typed.Trans Definition.Typed._⊔ᵒᵗ_

  -- Trans commutes with map-DCon.

  tr-Trans : map-DCon tr (Tₛ.Trans φ ∇) PE.≡ Tₜ.Trans φ (map-DCon tr ∇)
  tr-Trans {∇ = ε} =
    PE.refl
  tr-Trans {∇ = _ ∙⟨ tra ⟩!} =
    PE.cong _∙! tr-Trans
  tr-Trans {φ = _ ⁰} {∇ = ∇ ∙⟨ opa _ ⟩!} =
    PE.cong _∙! tr-Trans
  tr-Trans {φ = _ ¹} {∇ = ∇ ∙⟨ opa _ ⟩!} rewrite unfolding-mode-≡ =
    PE.cong _∙! tr-Trans

opaque
 unfolding tr tr-DCon tr-Cons
 mutual

  -- A preservation lemma for »_.

  tr-» : Tₛ.» ∇ → Tₜ.» tr-DCon ∇
  tr-» = tr-»′ _ PE.refl
    where
    tr-»′ : ∀ b → glassification PE.≡ b → Tₛ.» ∇ → Tₜ.» tr-DCon′ b ∇
    tr-»′ true _ Tₛ.ε =
      Tₜ.ε
    tr-»′ false _ Tₛ.ε =
      Tₜ.ε
    tr-»′ true PE.refl (Tₛ.∙ᵒ⟨_⟩[_∷_] {φ} {∇} ok ⊢t ⊢A) =
      Tₜ.∙ᵗ[
        PE.subst₃ Tₜ._⊢_∷_
          (PE.cong (_» _)
             (glassify (map-DCon tr (Tₛ.Trans φ ∇))  ≡⟨ glassify-map-DCon ⟩
              map-DCon tr (glassify (Tₛ.Trans φ ∇))  ≡⟨ PE.cong (map-DCon _) TPₛ.glassify-factor ⟩
              map-DCon tr (glassify ∇)               ≡˘⟨ glassify-map-DCon ⟩
              glassify (map-DCon tr ∇)               ∎))
          PE.refl PE.refl $
        tr-⊢∷ ⊢t
      ]
      where
      open Tools.Reasoning.PropositionalEquality
    tr-»′ false PE.refl Tₛ.∙ᵒ⟨ ok ⟩[ ⊢t ∷ ⊢A ] =
      Tₜ.∙ᵒ⟨ Opacity-allowed-→ (λ ()) ok
      ⟩[ PE.subst₃ Tₜ._⊢_∷_
          (PE.cong (_» _) tr-Trans) PE.refl PE.refl $
         tr-⊢∷ ⊢t
      ∷ tr-⊢ ⊢A
      ]
    tr-»′ true PE.refl Tₛ.∙ᵗ[ ⊢t ] =
      Tₜ.∙ᵗ[ tr-⊢∷ ⊢t ]
    tr-»′ false PE.refl Tₛ.∙ᵗ[ ⊢t ] =
      Tₜ.∙ᵗ[ tr-⊢∷ ⊢t ]

  -- A preservation lemma for ⊢_.

  tr-⊢′ : Tₛ.⊢ Γ → Tₜ.⊢ tr-Cons Γ
  tr-⊢′ = λ where
    (Tₛ.ε »∇) →
      Tₜ.ε (tr-» »∇)
    (Tₛ.∙ ⊢A) →
      Tₜ.∙ tr-⊢ ⊢A

  -- A preservation lemma for _⊢_.

  tr-⊢ : Γ Tₛ.⊢ A → tr-Cons Γ Tₜ.⊢ tr A
  tr-⊢ = λ where
    (Tₛ.Levelⱼ ok ⊢Γ) →
      TPₜ.Levelⱼ′
        (Level-allowed-⇔ .proj₁ (TRₛ.Level-allowed⇔⊎ .proj₂ (inj₂ ok)))
        (tr-⊢′ ⊢Γ)
    (Tₛ.univ ⊢A) →
      Tₜ.univ (tr-⊢∷ ⊢A)
    (Tₛ.Liftⱼ ⊢l ⊢A) →
      Tₜ.Liftⱼ (tr-⊢∷L ⊢l) (tr-⊢ ⊢A)
    (Tₛ.ΠΣⱼ ⊢B ok) →
      Tₜ.ΠΣⱼ (tr-⊢ ⊢B) (ΠΣ-allowed-→ ok)
    (Tₛ.Idⱼ _ ⊢t ⊢u) →
      TPₜ.Idⱼ′ (tr-⊢∷ ⊢t) (tr-⊢∷ ⊢u)

  -- A preservation lemma for _⊢_∷_.

  tr-⊢∷ : Γ Tₛ.⊢ t ∷ A → tr-Cons Γ Tₜ.⊢ tr t ∷ tr A
  tr-⊢∷ = λ where
    (Tₛ.conv ⊢t A≡B) →
      Tₜ.conv (tr-⊢∷ ⊢t) (tr-⊢≡ A≡B)
    (Tₛ.var ⊢Γ x∈) →
      Tₜ.var (tr-⊢′ ⊢Γ) (tr-∷∈ x∈)
    (Tₛ.defn {A′} ⊢Γ α∈ PE.refl) →
      Tₜ.defn (tr-⊢′ ⊢Γ) (tr-↦∈ α∈) (tr-wk A′)
    (Tₛ.Levelⱼ ⊢Γ ok) →
      Tₜ.Levelⱼ (tr-⊢′ ⊢Γ) (Level-is-small-→ ok)
    (Tₛ.zeroᵘⱼ ok ⊢Γ) →
      Tₜ.zeroᵘⱼ (Level-allowed-⇔ .proj₁ ok) (tr-⊢′ ⊢Γ)
    (Tₛ.sucᵘⱼ ⊢l) →
      Tₜ.sucᵘⱼ (tr-⊢∷ ⊢l)
    (Tₛ.supᵘⱼ ⊢l₁ ⊢l₂) →
      Tₜ.supᵘⱼ (tr-⊢∷ ⊢l₁) (tr-⊢∷ ⊢l₂)
    (Tₛ.Uⱼ ⊢l) →
      Tₜ.Uⱼ (tr-⊢∷L ⊢l)
    (Tₛ.Liftⱼ ⊢l₁ ⊢l₂ ⊢A) →
      PE.subst (Tₜ._⊢_∷_ _ _) (PE.cong U $ PE.sym $ tr-supᵘₗ ⊢l₁ ⊢l₂) $
      TPₜ.Liftⱼ′ (tr-⊢∷L ⊢l₂) (tr-⊢∷ ⊢A)
    (Tₛ.liftⱼ ⊢l _ ⊢t) →
      TPₜ.liftⱼ′ (tr-⊢∷L ⊢l) (tr-⊢∷ ⊢t)
    (Tₛ.lowerⱼ ⊢t) →
      Tₜ.lowerⱼ (tr-⊢∷ ⊢t)
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
      TPₜ.unitrecⱼ′ (tr-⊢ ⊢A) (tr-⊢∷ ⊢t)
        (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ A) $
         tr-⊢∷ ⊢u)
    (Tₛ.ΠΣⱼ {l} ⊢l ⊢A ⊢B ok) →
      Tₜ.ΠΣⱼ (tr-⊢∷L ⊢l) (tr-⊢∷ ⊢A)
        (PE.subst (Tₜ._⊢_∷_ _ _) (tr-wk (U l)) $
         tr-⊢∷ ⊢B)
        (ΠΣ-allowed-→ ok)
    (Tₛ.lamⱼ _ ⊢t ok) →
      TPₜ.lamⱼ′ (ΠΣ-allowed-→ ok) (tr-⊢∷ ⊢t)
    (Tₛ._∘ⱼ_ {G = B} ⊢t ⊢u) →
      PE.subst (Tₜ._⊢_∷_ _ _) (PE.sym $ tr-[]₀ B) $
      tr-⊢∷ ⊢t Tₜ.∘ⱼ tr-⊢∷ ⊢u
    (Tₛ.prodⱼ {G = B} ⊢B ⊢t ⊢u ok) →
      Tₜ.prodⱼ (tr-⊢ ⊢B) (tr-⊢∷ ⊢t)
        (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ B) $
         tr-⊢∷ ⊢u)
        (ΠΣ-allowed-→ ok)
    (Tₛ.fstⱼ _ ⊢t) →
      TPₜ.fstⱼ′ (tr-⊢∷ ⊢t)
    (Tₛ.sndⱼ {G = B} _ ⊢t) →
      PE.subst (Tₜ._⊢_∷_ _ _) (PE.sym $ tr-[]₀ B) $
      TPₜ.sndⱼ′ (tr-⊢∷ ⊢t)
    (Tₛ.prodrecⱼ {A = C} ⊢C ⊢t ⊢u _) →
      PE.subst (Tₜ._⊢_∷_ _ _) (PE.sym $ tr-[]₀ C) $
      TPₜ.prodrecⱼ′ (tr-⊢ ⊢C) (tr-⊢∷ ⊢t)
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
    (Tₛ.[]-congⱼ ⊢l _ _ _ ⊢v ok) →
      PE.subst (Tₜ._⊢_∷_ _ _) tr-Id-Erased-[]-[] $
      ⊢[]-cong′ ok (tr-⊢∷L ⊢l) (tr-⊢∷ ⊢v)

  -- A preservation lemma for _⊢_∷Level.

  tr-⊢∷L : Γ Tₛ.⊢ l ∷Level → tr-Cons Γ Tₜ.⊢ tr l ∷Level
  tr-⊢∷L = λ where
    (Tₛ.term ok ⊢l) →
      Tₜ.term (Level-allowed-⇔ .proj₁ ok) (tr-⊢∷ ⊢l)
    (Tₛ.literal not-ok ⊢Γ l-lit) →
      Tₜ.literal (not-ok ∘→ Level-allowed-⇔ .proj₂) (tr-⊢′ ⊢Γ)
        (tr-Level-literal l-lit)

  -- A preservation lemma for _⊢_≡_.

  tr-⊢≡ : Γ Tₛ.⊢ A ≡ B → tr-Cons Γ Tₜ.⊢ tr A ≡ tr B
  tr-⊢≡ = λ where
    (Tₛ.refl ⊢A) →
      Tₜ.refl (tr-⊢ ⊢A)
    (Tₛ.sym A₁≡A₂) →
      Tₜ.sym (tr-⊢≡ A₁≡A₂)
    (Tₛ.trans A₁≡A₂ A₂≡A₃) →
      Tₜ.trans (tr-⊢≡ A₁≡A₂) (tr-⊢≡ A₂≡A₃)
    (Tₛ.U-cong l₁≡l₂) →
      Tₜ.U-cong (tr-⊢≡∷ l₁≡l₂)
    (Tₛ.univ A₁≡A₂) →
      Tₜ.univ (tr-⊢≡∷ A₁≡A₂)
    (Tₛ.Lift-cong l₁≡l₂ A₁≡A₂) →
      Tₜ.Lift-cong (tr-⊢≡∷L l₁≡l₂) (tr-⊢≡ A₁≡A₂)
    (Tₛ.ΠΣ-cong A₁≡A₂ B₁≡B₂ ok) →
      Tₜ.ΠΣ-cong (tr-⊢≡ A₁≡A₂) (tr-⊢≡ B₁≡B₂) (ΠΣ-allowed-→ ok)
    (Tₛ.Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) →
      Tₜ.Id-cong (tr-⊢≡ A₁≡A₂) (tr-⊢≡∷ t₁≡t₂) (tr-⊢≡∷ u₁≡u₂)

  -- A preservation lemma for _⊢_≡_∷_.

  tr-⊢≡∷ : Γ Tₛ.⊢ t ≡ u ∷ A → tr-Cons Γ Tₜ.⊢ tr t ≡ tr u ∷ tr A
  tr-⊢≡∷ = λ where
    (Tₛ.conv t₁≡t₂ A₁≡A₂) →
      Tₜ.conv (tr-⊢≡∷ t₁≡t₂) (tr-⊢≡ A₁≡A₂)
    (Tₛ.refl ⊢t) →
      Tₜ.refl (tr-⊢∷ ⊢t)
    (Tₛ.sym _ t₁≡t₂) →
      TPₜ.sym′ (tr-⊢≡∷ t₁≡t₂)
    (Tₛ.trans t₁≡t₂ t₂≡t₃) →
      Tₜ.trans (tr-⊢≡∷ t₁≡t₂) (tr-⊢≡∷ t₂≡t₃)
    (Tₛ.δ-red {t′} {A′} ⊢Γ α∈ PE.refl PE.refl) →
      Tₜ.δ-red (tr-⊢′ ⊢Γ) (tr-↦∷∈ α∈) (tr-wk A′) (tr-wk t′)
    (Tₛ.sucᵘ-cong l₁≡l₂) →
      Tₜ.sucᵘ-cong (tr-⊢≡∷ l₁≡l₂)
    (Tₛ.supᵘ-cong l₁₁≡l₂₁ l₁₂≡l₂₂) →
      Tₜ.supᵘ-cong (tr-⊢≡∷ l₁₁≡l₂₁) (tr-⊢≡∷ l₁₂≡l₂₂)
    (Tₛ.supᵘ-zeroˡ ⊢l) →
      Tₜ.supᵘ-zeroˡ (tr-⊢∷ ⊢l)
    (Tₛ.supᵘ-sucᵘ ⊢l₁ ⊢l₂) →
      Tₜ.supᵘ-sucᵘ (tr-⊢∷ ⊢l₁) (tr-⊢∷ ⊢l₂)
    (Tₛ.supᵘ-assoc ⊢l₁ ⊢l₂ ⊢l₃) →
      Tₜ.supᵘ-assoc (tr-⊢∷ ⊢l₁) (tr-⊢∷ ⊢l₂) (tr-⊢∷ ⊢l₃)
    (Tₛ.supᵘ-comm ⊢l₁ ⊢l₂) →
      Tₜ.supᵘ-comm (tr-⊢∷ ⊢l₁) (tr-⊢∷ ⊢l₂)
    (Tₛ.supᵘ-idem ⊢l) →
      Tₜ.supᵘ-idem (tr-⊢∷ ⊢l)
    (Tₛ.supᵘ-sub ⊢l) →
      Tₜ.supᵘ-sub (tr-⊢∷ ⊢l)
    (Tₛ.U-cong l₁≡l₂) →
      Tₜ.U-cong (tr-⊢≡∷ l₁≡l₂)
    (Tₛ.Lift-cong ⊢l₁ ⊢l₂₁ l₂₁≡l₂₂ A₁≡A₂) →
      PE.subst (Tₜ._⊢_≡_∷_ _ _ _)
        (PE.cong U $ PE.sym $ tr-supᵘₗ ⊢l₁ ⊢l₂₁) $
      TPₜ.Lift-cong′ (tr-⊢≡∷L l₂₁≡l₂₂) (tr-⊢≡∷ A₁≡A₂)
    (Tₛ.lower-cong t₁≡t₂) →
      Tₜ.lower-cong (tr-⊢≡∷ t₁≡t₂)
    (Tₛ.Lift-β _ ⊢t) →
      TPₜ.Lift-β′ (tr-⊢∷ ⊢t)
    (Tₛ.Lift-η _ _ ⊢t₁ ⊢t₂ lower-t₁≡lower-t₂) →
      TPₜ.Lift-η′ (tr-⊢∷ ⊢t₁) (tr-⊢∷ ⊢t₂) (tr-⊢≡∷ lower-t₁≡lower-t₂)
    (Tₛ.emptyrec-cong A₁≡A₂ t₁≡t₂) →
      Tₜ.emptyrec-cong (tr-⊢≡ A₁≡A₂) (tr-⊢≡∷ t₁≡t₂)
    (Tₛ.η-unit ⊢t₁ ⊢t₂ ok) →
      Tₜ.η-unit (tr-⊢∷ ⊢t₁) (tr-⊢∷ ⊢t₂) (Unit-with-η-⇔ .proj₁ ok)
    (Tₛ.unitrec-cong {A = A₁} A₁≡A₂ t₁≡t₂ u₁≡u₂ _ _) →
      PE.subst (Tₜ._⊢_≡_∷_ _ _ _) (PE.sym $ tr-[]₀ A₁) $
      TPₜ.unitrec-cong′ (tr-⊢≡ A₁≡A₂) (tr-⊢≡∷ t₁≡t₂)
        (PE.subst (Tₜ._⊢_≡_∷_ _ _ _) (tr-[]₀ A₁) $
         tr-⊢≡∷ u₁≡u₂)
    (Tₛ.unitrec-β {A} ⊢A ⊢t _ _) →
      PE.subst (Tₜ._⊢_≡_∷_ _ _ _) (PE.sym $ tr-[]₀ A) $
      TPₜ.unitrec-β-≡ (tr-⊢ ⊢A)
        (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ A) $
         tr-⊢∷ ⊢t)
    (Tₛ.unitrec-β-η {A} ⊢A ⊢t ⊢u ok η) →
      PE.subst (Tₜ._⊢_≡_∷_ _ _ _) (PE.sym $ tr-[]₀ A) $
      Tₜ.unitrec-β-η (tr-⊢ ⊢A) (tr-⊢∷ ⊢t)
        (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ A) $
         tr-⊢∷ ⊢u)
        (Unit-allowed-→ ok) (Unitʷ-η-⇔ .proj₁ η)
    (Tₛ.ΠΣ-cong {l} ⊢l A₁≡A₂ B₁≡B₂ ok) →
      Tₜ.ΠΣ-cong (tr-⊢∷L ⊢l) (tr-⊢≡∷ A₁≡A₂)
        (PE.subst (Tₜ._⊢_≡_∷_ _ _ _) (tr-wk (U l)) $
         tr-⊢≡∷ B₁≡B₂)
        (ΠΣ-allowed-→ ok)
    (Tₛ.app-cong {G = B} t₁≡t₂ u₁≡u₂) →
      PE.subst (Tₜ._⊢_≡_∷_ _ _ _) (PE.sym $ tr-[]₀ B) $
      Tₜ.app-cong (tr-⊢≡∷ t₁≡t₂) (tr-⊢≡∷ u₁≡u₂)
    (Tₛ.β-red {G = B} {t} _ ⊢t ⊢u PE.refl ok) →
      PE.subst₂ (Tₜ._⊢_≡_∷_ _ _)
        (PE.sym $ tr-[]₀ t) (PE.sym $ tr-[]₀ B) $
      TPₜ.β-red-≡ (tr-⊢∷ ⊢t) (tr-⊢∷ ⊢u) (ΠΣ-allowed-→ ok)
    (Tₛ.η-eq {f = t₁} {g = t₂} _ ⊢t₁ ⊢t₂ t₁∘0≡t₂∘0 _) →
      TPₜ.η-eq′ (tr-⊢∷ ⊢t₁) (tr-⊢∷ ⊢t₂)
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
      TPₜ.fst-cong′ (tr-⊢≡∷ t₁≡t₂)
    (Tₛ.Σ-β₁ {G = B} ⊢B ⊢t ⊢u eq ok) →
      Tₜ.Σ-β₁ (tr-⊢ ⊢B) (tr-⊢∷ ⊢t)
        (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ B) $
         tr-⊢∷ ⊢u)
        eq (ΠΣ-allowed-→ ok)
    (Tₛ.snd-cong {G = B} _ t₁≡t₂) →
      PE.subst (Tₜ._⊢_≡_∷_ _ _ _) (PE.sym $ tr-[]₀ B) $
      TPₜ.snd-cong′ (tr-⊢≡∷ t₁≡t₂)
    (Tₛ.Σ-β₂ {G = B} ⊢B ⊢t ⊢u eq ok) →
      PE.subst (Tₜ._⊢_≡_∷_ _ _ _) (PE.sym $ tr-[]₀ B) $
      Tₜ.Σ-β₂ (tr-⊢ ⊢B) (tr-⊢∷ ⊢t)
        (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ B) $
         tr-⊢∷ ⊢u)
        eq (ΠΣ-allowed-→ ok)
    (Tₛ.Σ-η {G = B} _ ⊢t₁ ⊢t₂ fst-t₁≡fst-t₂ snd-t₁≡snd-t₂ _) →
      TPₜ.Σ-η′ (tr-⊢∷ ⊢t₁) (tr-⊢∷ ⊢t₂) (tr-⊢≡∷ fst-t₁≡fst-t₂)
        (PE.subst (Tₜ._⊢_≡_∷_ _ _ _) (tr-[]₀ B) $
         tr-⊢≡∷ snd-t₁≡snd-t₂)
    (Tₛ.prodrec-cong {A = C₁} C₁≡C₂ t₁≡t₂ u₁≡u₂ _) →
      PE.subst (Tₜ._⊢_≡_∷_ _ _ _) (PE.sym $ tr-[]₀ C₁) $
      TPₜ.prodrec-cong′ (tr-⊢≡ C₁≡C₂) (tr-⊢≡∷ t₁≡t₂)
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
    (Tₛ.[]-cong-cong l₁≡l₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ ok) →
      PE.subst (Tₜ._⊢_≡_∷_ _ _ _) tr-Id-Erased-[]-[] $
      []-cong′-cong ok (tr-⊢≡∷L l₁≡l₂) (tr-⊢≡ A₁≡A₂) (tr-⊢≡∷ t₁≡t₂)
        (tr-⊢≡∷ u₁≡u₂) (tr-⊢≡∷ v₁≡v₂)
    (Tₛ.[]-cong-β ⊢l ⊢t PE.refl ok) →
      PE.subst (Tₜ._⊢_≡_∷_ _ _ _) tr-Id-Erased-[]-[] $
      []-cong′-β-≡ ok (tr-⊢∷L ⊢l) (tr-⊢∷ ⊢t)
    (Tₛ.equality-reflection ok _ ⊢v) →
      TPₜ.equality-reflection′ (Equality-reflection-→ ok) (tr-⊢∷ ⊢v)

  -- A preservation lemma for _⊢_≡_∷Level.

  tr-⊢≡∷L : Γ Tₛ.⊢ l₁ ≡ l₂ ∷Level → tr-Cons Γ Tₜ.⊢ tr l₁ ≡ tr l₂ ∷Level
  tr-⊢≡∷L = λ where
    (Tₛ.term ok l₁≡l₂) →
      Tₜ.term (Level-allowed-⇔ .proj₁ ok) (tr-⊢≡∷ l₁≡l₂)
    (Tₛ.literal not-ok ⊢Γ l-lit) →
      Tₜ.literal (not-ok ∘→ Level-allowed-⇔ .proj₂) (tr-⊢′ ⊢Γ)
        (tr-Level-literal l-lit)

------------------------------------------------------------------------
-- The translation might preserve reduction

-- The translation preserves (many-step) reduction if
-- preservation-of-reduction is true.

module _ (pres : T preservation-of-reduction) where

  opaque
    unfolding tr tr-Cons

    -- A preservation lemma for _⊢_⇒_∷_.

    tr-⊢⇒∷ : Γ Tₛ.⊢ t ⇒ u ∷ A → tr-Cons Γ Tₜ.⊢ tr t ⇒* tr u ∷ tr A
    tr-⊢⇒∷ = λ where
      (Tₛ.conv t⇒t′ A≡B) →
        TPₜ.conv* (tr-⊢⇒∷ t⇒t′) (tr-⊢≡ A≡B)
      (Tₛ.δ-red {t′} {A′} ⊢Γ α↦ PE.refl PE.refl) →
        TPₜ.redMany $
        Tₜ.δ-red (tr-⊢′ ⊢Γ) (tr-↦∷∈ α↦) (tr-wk A′) (tr-wk t′)
      (Tₛ.supᵘ-substˡ l₁⇒l₁′ ⊢l₂) →
        TPₜ.supᵘ-substˡ* (tr-⊢⇒∷ l₁⇒l₁′) (tr-⊢∷ ⊢l₂)
      (Tₛ.supᵘ-substʳ ⊢l₁ l₂⇒l₂′) →
        TPₜ.supᵘ-substʳ* (tr-⊢∷ ⊢l₁) (tr-⊢⇒∷ l₂⇒l₂′)
      (Tₛ.supᵘ-zeroˡ ⊢l) →
        TPₜ.redMany $
        Tₜ.supᵘ-zeroˡ (tr-⊢∷ ⊢l)
      (Tₛ.supᵘ-zeroʳ ⊢l) →
        TPₜ.redMany $
        Tₜ.supᵘ-zeroʳ (tr-⊢∷ ⊢l)
      (Tₛ.supᵘ-sucᵘ ⊢l₁ ⊢l₂) →
        TPₜ.redMany $
        Tₜ.supᵘ-sucᵘ (tr-⊢∷ ⊢l₁) (tr-⊢∷ ⊢l₂)
      (Tₛ.lower-subst t⇒t′) →
        TPₜ.lower-subst* (tr-⊢⇒∷ t⇒t′)
      (Tₛ.Lift-β _ ⊢t) →
        TPₜ.redMany $
        TPₜ.Lift-β⇒ (tr-⊢∷ ⊢t)
      (Tₛ.emptyrec-subst ⊢A t⇒t′) →
        TPₜ.emptyrec-subst* (tr-⊢⇒∷ t⇒t′) (tr-⊢ ⊢A)
      (Tₛ.unitrec-subst {A} ⊢A ⊢u t⇒t′ _ no-η) →
        PE.subst (Tₜ._⊢_⇒*_∷_ _ _ _) (PE.sym $ tr-[]₀ A) $
        TPₜ.unitrec-subst* (tr-⊢⇒∷ t⇒t′) (tr-⊢ ⊢A)
          (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ A) $
           tr-⊢∷ ⊢u)
          (no-η ∘→ Unitʷ-η-⇔ .proj₂)
      (Tₛ.unitrec-β {A} ⊢A ⊢u _ _) →
        PE.subst (Tₜ._⊢_⇒*_∷_ _ _ _) (PE.sym $ tr-[]₀ A) $
        TPₜ.redMany $
        TPₜ.unitrec-β-⇒ (tr-⊢ ⊢A)
          (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ A) $
           tr-⊢∷ ⊢u)
      (Tₛ.unitrec-β-η {A} ⊢A ⊢t ⊢u ok η) →
        PE.subst (Tₜ._⊢_⇒*_∷_ _ _ _) (PE.sym $ tr-[]₀ A) $
        TPₜ.redMany $
        Tₜ.unitrec-β-η (tr-⊢ ⊢A) (tr-⊢∷ ⊢t)
          (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ A) $
           tr-⊢∷ ⊢u)
          (Unit-allowed-→ ok) (Unitʷ-η-⇔ .proj₁ η)
      (Tₛ.app-subst {G = B} t⇒t′ ⊢u) →
        PE.subst (Tₜ._⊢_⇒*_∷_ _ _ _) (PE.sym $ tr-[]₀ B) $
        TPₜ.app-subst* (tr-⊢⇒∷ t⇒t′) (tr-⊢∷ ⊢u)
      (Tₛ.β-red {G = B} {t} _ ⊢t ⊢u PE.refl ok) →
        PE.subst₂ (Tₜ._⊢_⇒*_∷_ _ _)
          (PE.sym $ tr-[]₀ t) (PE.sym $ tr-[]₀ B) $
        TPₜ.redMany $
        TPₜ.β-red-⇒ (tr-⊢∷ ⊢t) (tr-⊢∷ ⊢u) (ΠΣ-allowed-→ ok)
      (Tₛ.fst-subst _ t⇒t′) →
        TPₜ.fst-subst* (tr-⊢⇒∷ t⇒t′)
      (Tₛ.Σ-β₁ {G = B} ⊢B ⊢t ⊢u eq ok) →
        TPₜ.redMany $
        Tₜ.Σ-β₁ (tr-⊢ ⊢B) (tr-⊢∷ ⊢t)
          (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ B) $
           tr-⊢∷ ⊢u)
          eq (ΠΣ-allowed-→ ok)
      (Tₛ.snd-subst {G = B} _ t⇒t′) →
        PE.subst (Tₜ._⊢_⇒*_∷_ _ _ _) (PE.sym $ tr-[]₀ B) $
        TPₜ.snd-subst* (tr-⊢⇒∷ t⇒t′)
      (Tₛ.Σ-β₂ {G = B} ⊢B ⊢t ⊢u eq ok) →
        PE.subst (Tₜ._⊢_⇒*_∷_ _ _ _) (PE.sym $ tr-[]₀ B) $
        TPₜ.redMany $
        Tₜ.Σ-β₂ (tr-⊢ ⊢B) (tr-⊢∷ ⊢t)
          (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ B) $
           tr-⊢∷ ⊢u)
          eq (ΠΣ-allowed-→ ok)
      (Tₛ.prodrec-subst {A = C} ⊢C ⊢u t⇒t′ _) →
        PE.subst (Tₜ._⊢_⇒*_∷_ _ _ _) (PE.sym $ tr-[]₀ C) $
        TPₜ.prodrec-subst* (tr-⊢ ⊢C) (tr-⊢⇒∷ t⇒t′)
          (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]↑² C) $
           tr-⊢∷ ⊢u)
      (Tₛ.prodrec-β {G = B} {A = C} {u} ⊢C ⊢t ⊢u ⊢v PE.refl _) →
        PE.subst₂ (Tₜ._⊢_⇒*_∷_ _ _)
          (PE.sym $ tr-[]₁₀ u) (PE.sym $ tr-[]₀ C) $
        TPₜ.redMany $
        TPₜ.prodrec-β-⇒ (tr-⊢ ⊢C) (tr-⊢∷ ⊢t)
          (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ B) $
           tr-⊢∷ ⊢u)
          (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]↑² C) $
           tr-⊢∷ ⊢v)
      (Tₛ.natrec-subst {A} ⊢t ⊢u v⇒v′) →
        PE.subst (Tₜ._⊢_⇒*_∷_ _ _ _) (PE.sym $ tr-[]₀ A) $
        TPₜ.natrec-subst*
          (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ A) $
           tr-⊢∷ ⊢t)
          (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]↑² A) $
           tr-⊢∷ ⊢u)
          (tr-⊢⇒∷ v⇒v′)
      (Tₛ.natrec-zero {A} ⊢t ⊢u) →
        PE.subst (Tₜ._⊢_⇒*_∷_ _ _ _) (PE.sym $ tr-[]₀ A) $
        TPₜ.redMany $
        Tₜ.natrec-zero
          (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ A) $
           tr-⊢∷ ⊢t)
          (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]↑² A) $
           tr-⊢∷ ⊢u)
      (Tₛ.natrec-suc {A} {s = u} ⊢t ⊢u ⊢v) →
        PE.subst₂ (Tₜ._⊢_⇒*_∷_ _ _)
          (PE.sym $ tr-[]₁₀ u) (PE.sym $ tr-[]₀ A) $
        TPₜ.redMany $
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
        TPₜ.K-subst* (tr-⊢ ⊢B)
          (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ B) $
           tr-⊢∷ ⊢u)
          (tr-⊢⇒∷ v⇒v′) (K-allowed-→ ok)
      (Tₛ.K-β {B} ⊢B ⊢u ok) →
        PE.subst (Tₜ._⊢_⇒*_∷_ _ _ _) (PE.sym $ tr-[]₀ B) $
        TPₜ.redMany $
        Tₜ.K-β (tr-⊢ ⊢B)
          (PE.subst (Tₜ._⊢_∷_ _ _) (tr-[]₀ B) $
           tr-⊢∷ ⊢u)
          (K-allowed-→ ok)
      (Tₛ.[]-cong-subst ⊢l v⇒v′ ok) →
        PE.subst (Tₜ._⊢_⇒*_∷_ _ _ _) tr-Id-Erased-[]-[] $
        []-cong′-subst* pres ok (tr-⊢∷L ⊢l) (tr-⊢⇒∷ v⇒v′)
      (Tₛ.[]-cong-β ⊢l t≡t′ ok) →
        PE.subst (Tₜ._⊢_⇒*_∷_ _ _ _) tr-Id-Erased-[]-[] $
        []-cong′-β-⇒* pres ok (tr-⊢∷L ⊢l) (tr-⊢≡∷ t≡t′)

  opaque

    -- A preservation lemma for _⊢_⇒*_∷_.

    tr-⊢⇒*∷ : Γ Tₛ.⊢ t ⇒* u ∷ A → tr-Cons Γ Tₜ.⊢ tr t ⇒* tr u ∷ tr A
    tr-⊢⇒*∷ = λ where
      (Tₛ.id ⊢t) →
        Tₜ.id (tr-⊢∷ ⊢t)
      (t⇒u Tₛ.⇨ u⇒*v) →
        tr-⊢⇒∷ t⇒u TPₜ.⇨∷* tr-⊢⇒*∷ u⇒*v

  opaque
    unfolding tr

    -- A preservation lemma for _⊢_⇒_.

    tr-⊢⇒ : Γ Tₛ.⊢ A ⇒ B → tr-Cons Γ Tₜ.⊢ tr A ⇒* tr B
    tr-⊢⇒ = λ where
      (Tₛ.univ A⇒B) → TPₜ.univ* (tr-⊢⇒∷ A⇒B)

  opaque

    -- A preservation lemma for _⊢_⇒*_.

    tr-⊢⇒* : Γ Tₛ.⊢ A ⇒* B → tr-Cons Γ Tₜ.⊢ tr A ⇒* tr B
    tr-⊢⇒* = λ where
      (Tₛ.id ⊢A) →
        Tₜ.id (tr-⊢ ⊢A)
      (A⇒B Tₛ.⇨ B⇒*C) →
        tr-⊢⇒ A⇒B TPₜ.⇨* tr-⊢⇒* B⇒*C

  opaque
    unfolding tr

    -- A preservation lemma for _⊢_⇒ˢ_∷ℕ.

    tr-⊢⇒ˢ∷ℕ : Γ Sₛ.⊢ t ⇒ˢ u ∷ℕ → tr-Cons Γ Sₜ.⊢ tr t ⇒ˢ* tr u ∷ℕ
    tr-⊢⇒ˢ∷ℕ = λ where
      (Sₛ.whred t⇒u) →
        Sₜ.whred* (tr-⊢⇒∷ t⇒u)
      (Sₛ.sucred t⇒ˢu) →
        Sₜ.sucred* (tr-⊢⇒ˢ∷ℕ t⇒ˢu)

  opaque
    unfolding tr

    -- A preservation lemma for _⊢_⇒ˢ*_∷ℕ.

    tr-⊢⇒ˢ*∷ℕ : Γ Sₛ.⊢ t ⇒ˢ* u ∷ℕ → tr-Cons Γ Sₜ.⊢ tr t ⇒ˢ* tr u ∷ℕ
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

  erase-tr : (t : Term n) → erase′ b str (tr t) PE.≡ erase′ b str t
  erase-tr (var _) =
    PE.refl
  erase-tr (defn _) =
    PE.refl
  erase-tr Level =
    PE.refl
  erase-tr zeroᵘ =
    PE.refl
  erase-tr (sucᵘ _) =
    PE.refl
  erase-tr (_ supᵘ _) =
    PE.refl
  erase-tr (U _) =
    PE.refl
  erase-tr (Lift _ _) =
    PE.refl
  erase-tr (lift t) =
    erase-tr t
  erase-tr (lower t) =
    erase-tr t
  erase-tr Empty =
    PE.refl
  erase-tr (emptyrec _ _ _) =
    PE.refl
  erase-tr (Unit _) =
    PE.refl
  erase-tr (star _) =
    PE.refl
  erase-tr (unitrec p _ _ t u) with is-𝟘? p
  … | no _ =
    PE.cong₂ T.unitrec (erase-tr t) (erase-tr u)
  … | yes _ =
    erase-tr u
  erase-tr (ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _) =
    PE.refl
  erase-tr (lam p _) with is-𝟘? p
  erase-tr (lam _ t) | no _ =
    PE.cong T.lam (erase-tr t)
  erase-tr {b = true} (lam _ t) | yes _ =
    PE.cong T._[ _ ]₀ (erase-tr t)
  erase-tr {b = false} (lam _ t) | yes _ =
    PE.cong T.lam (erase-tr t)
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
  erase-tr {b} {str} (J p q A t B u v w) =
    let open Tools.Reasoning.PropositionalEquality in
    erase′ b str (J′ p q (tr A) (tr t) (tr B) (tr u) (tr v) (tr w))  ≡⟨ erase-J′ ⟩
    erase′ b str (tr u)                                              ≡⟨ erase-tr u ⟩
    erase′ b str u                                                   ≡⟨⟩
    erase′ b str (J p q A t B u v w)                                 ∎
  erase-tr (K _ _ _ _ u _) =
    erase-tr u
  erase-tr {b} {str} ([]-cong s l A t u v) =
    let open Tools.Reasoning.PropositionalEquality in
    erase′ b str ([]-cong′ s (tr l) (tr A) (tr t) (tr u) (tr v))  ≡⟨ erase-[]-cong′ ⟩
    loop? str                                                     ≡⟨⟩
    erase′ b str ([]-cong s l A t u v)                            ∎
