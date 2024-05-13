------------------------------------------------------------------------
-- Validity of emptyrec.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Emptyrec
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}

open import Definition.Untyped M as U hiding (wk)
open import Definition.Typed R
import Definition.Typed.Weakening R as T
open import Definition.Typed.Properties R
open import Definition.Typed.RedSteps R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Properties R
import Definition.LogicalRelation.Substitution.Irrelevance R as S
open import Definition.LogicalRelation.Substitution.Reflexivity R
open import Definition.LogicalRelation.Substitution.Introductions.Empty R

open import Tools.Product
open import Tools.Nat

import Tools.PropositionalEquality as PE

private
  variable
    m n : Nat
    Γ : Con Term n
    Δ : Con Term m
    p p′ : M

-- Empty elimination closure reduction (requires reducible terms and equality).
emptyrec-subst* : ∀ {C n n′ l}
              → Γ ⊢ C
              → Γ ⊢ n ⇒* n′ ∷ Empty
              → ([Empty] : Γ ⊩⟨ l ⟩ Empty)
              → Γ ⊩⟨ l ⟩ n′ ∷ Empty / [Empty]
              → Γ ⊢ emptyrec p C n ⇒* emptyrec p C n′ ∷ C
emptyrec-subst* C (id x) [Empty] [n′] = id (emptyrecⱼ C x)
emptyrec-subst* {p = p} C (x ⇨ n⇒n′) [Empty] [n′] =
  let q , w = redSubst*Term n⇒n′ [Empty] [n′]
      a , s = redSubstTerm x [Empty] q
  in  emptyrec-subst C x ⇨ conv* (emptyrec-subst* C n⇒n′ [Empty] [n′]) (refl C)

-- Reducibility of empty elimination under a valid substitution.
emptyrecTerm : ∀ {F n σ l}
             ([Γ]  : ⊩ᵛ Γ)
             ([F]  : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
             (⊢Δ   : ⊢ Δ)
             ([σ]  : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
             ([σn] : Δ ⊩⟨ l ⟩ n ∷ Empty / Emptyᵣ (idRed:*: (Emptyⱼ ⊢Δ)))
           → Δ ⊩⟨ l ⟩ emptyrec p (F [ σ ]) n
               ∷ F [ σ ]
               / proj₁ (unwrap [F] ⊢Δ [σ])
emptyrecTerm {Γ = Γ} {Δ = Δ} {F = F} {n} {σ} {l} [Γ] [F] ⊢Δ [σ]
           (Emptyₜ m d n≡n (ne (neNfₜ neM ⊢m m≡m))) =
  let [Empty] = Emptyᵛ {l = l} [Γ]
      [σEmpty] = proj₁ (unwrap [Empty] ⊢Δ [σ])
      [σm] = neuTerm [σEmpty] neM ⊢m m≡m
      [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
      ⊢F = escape [σF]
      ⊢F≡F = escapeEq [σF] (reflEq [σF])
      emptyrecM = neuTerm [σF] (emptyrecₙ neM) (emptyrecⱼ ⊢F ⊢m)
                        (~-emptyrec ⊢F≡F m≡m)
      reduction = emptyrec-subst* ⊢F (redₜ d) [σEmpty] [σm]
  in proj₁ (redSubst*Term reduction [σF] emptyrecM)


-- Reducibility of empty elimination congruence under a valid substitution equality.
emptyrec-congTerm : ∀ {F F′ n m σ σ′ l}
                  ([Γ]      : ⊩ᵛ Γ)
                  ([F]      : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
                  ([F′]     : Γ ⊩ᵛ⟨ l ⟩ F′ / [Γ])
                  ([F≡F′]   : Γ ⊩ᵛ⟨ l ⟩ F ≡ F′ / [Γ] / [F])
                  (⊢Δ       : ⊢ Δ)
                  ([σ]      : Δ ⊩ˢ σ  ∷ Γ / [Γ] / ⊢Δ)
                  ([σ′]     : Δ ⊩ˢ σ′ ∷ Γ / [Γ] / ⊢Δ)
                  ([σ≡σ′]   : Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ])
                  ([σn]     : Δ ⊩⟨ l ⟩ n ∷ Empty / Emptyᵣ (idRed:*: (Emptyⱼ ⊢Δ)))
                  ([σm]     : Δ ⊩⟨ l ⟩ m ∷ Empty / Emptyᵣ (idRed:*: (Emptyⱼ ⊢Δ)))
                  ([σn≡σm]  : Δ ⊩⟨ l ⟩ n ≡ m ∷ Empty / Emptyᵣ (idRed:*: (Emptyⱼ ⊢Δ)))
                → Δ ⊩⟨ l ⟩ emptyrec p (F [ σ ]) n
                    ≡ emptyrec p (F′ [ σ′ ]) m
                    ∷ F [ σ ]
                    / proj₁ (unwrap [F] ⊢Δ [σ])
emptyrec-congTerm {Γ = Γ} {Δ = Δ} {p = p} {F} {F′} {n} {m} {σ} {σ′} {l}
                [Γ] [F] [F′] [F≡F′]
                ⊢Δ [σ] [σ′] [σ≡σ′]
                (Emptyₜ n′ d n≡n (ne (neNfₜ neN′ ⊢n′ n≡n₁)))
                (Emptyₜ m′ d′ m≡m (ne (neNfₜ neM′ ⊢m′ m≡m₁)))
                (Emptyₜ₌ n″ m″ d₁ d₁′ t≡u (ne (neNfₜ₌ x₂ x₃ prop₂))) =
  let n″≡n′ = whrDet*Term (redₜ d₁ , ne x₂) (redₜ d , ne neN′)
      m″≡m′ = whrDet*Term (redₜ d₁′ , ne x₃) (redₜ d′ , ne neM′)
      [Empty] = Emptyᵛ {l = l} [Γ]
      [σEmpty] = proj₁ (unwrap [Empty] ⊢Δ [σ])
      [σ′Empty] = proj₁ (unwrap [Empty] ⊢Δ [σ′])
      [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
      [σ′F] = proj₁ (unwrap [F] ⊢Δ [σ′])
      [σ′F′] = proj₁ (unwrap [F′] ⊢Δ [σ′])
      [σn′] = neuTerm [σEmpty] neN′ ⊢n′ n≡n₁
      [σ′m′] = neuTerm [σ′Empty] neM′ ⊢m′ m≡m₁
      ⊢F = escape [σF]
      ⊢F≡F = escapeEq [σF] (reflEq [σF])
      ⊢F′ = escape [σ′F′]
      ⊢F′≡F′ = escapeEq [σ′F′] (reflEq [σ′F′])
      ⊢σF≡σ′F = escapeEq [σF] (proj₂ (unwrap [F] ⊢Δ [σ]) [σ′] [σ≡σ′])
      ⊢σ′F≡σ′F′ = escapeEq [σ′F] ([F≡F′] ⊢Δ [σ′])
      ⊢F≡F′ = ≅-trans ⊢σF≡σ′F ⊢σ′F≡σ′F′
      [σF≡σ′F] = proj₂ (unwrap [F] ⊢Δ [σ]) [σ′] [σ≡σ′]
      [σ′F≡σ′F′] = [F≡F′] ⊢Δ [σ′]
      [σF≡σ′F′] = transEq [σF] [σ′F] [σ′F′] [σF≡σ′F] [σ′F≡σ′F′]
      emptyrecN = neuTerm [σF] (emptyrecₙ neN′) (emptyrecⱼ ⊢F ⊢n′)
                        (~-emptyrec ⊢F≡F n≡n₁)
      emptyrecM = neuTerm [σ′F′] (emptyrecₙ neM′) (emptyrecⱼ ⊢F′ ⊢m′)
                        (~-emptyrec ⊢F′≡F′ m≡m₁)
      emptyrecN≡M =
          (neuEqTerm [σF] (emptyrecₙ neN′) (emptyrecₙ neM′)
                     (emptyrecⱼ ⊢F ⊢n′)
                     (conv (emptyrecⱼ ⊢F′ ⊢m′)
                            (sym (≅-eq (escapeEq [σF]
                              (transEq [σF] [σ′F] [σ′F′] [σF≡σ′F] [σ′F≡σ′F′])))))
                     (~-emptyrec ⊢F≡F′
                               (PE.subst₂ (λ x y → _ ⊢ x ~ y ∷ _)
                                          n″≡n′ m″≡m′ prop₂)))
      reduction₁ = emptyrec-subst* ⊢F (redₜ d) [σEmpty] [σn′]
      reduction₂ = emptyrec-subst* ⊢F′ (redₜ d′) [σ′Empty] [σ′m′]
      eq₁ = proj₂ (redSubst*Term reduction₁ [σF] emptyrecN)
      eq₂ = proj₂ (redSubst*Term reduction₂ [σ′F′] emptyrecM)
  in  transEqTerm [σF] eq₁
                 (transEqTerm [σF] emptyrecN≡M
                              (convEqTerm₂ [σF] [σ′F′] [σF≡σ′F′]
                                           (symEqTerm [σ′F′] eq₂)))

-- Validity of empty elimination.
emptyrecᵛ : ∀ {F n l} ([Γ] : ⊩ᵛ Γ)
          ([Empty]  : Γ ⊩ᵛ⟨ l ⟩ Empty / [Γ])
          ([F]  : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
        → ([n] : Γ ⊩ᵛ⟨ l ⟩ n ∷ Empty / [Γ] / [Empty])
        → Γ ⊩ᵛ⟨ l ⟩ emptyrec p F n ∷ F / [Γ] / [F]
emptyrecᵛ {F = F} {n} {l = l} [Γ] [Empty] [F] [n]
        {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [σn] = irrelevanceTerm {l′ = l} (proj₁ (unwrap [Empty] ⊢Δ [σ]))
                             (Emptyᵣ (idRed:*: (Emptyⱼ ⊢Δ))) (proj₁ ([n] ⊢Δ [σ]))
  in emptyrecTerm {F = F} [Γ] [F] ⊢Δ [σ] [σn]
    , λ {σ'} [σ′] [σ≡σ′] →
      let [σ′n] = irrelevanceTerm {l′ = l} (proj₁ (unwrap [Empty] ⊢Δ [σ′]))
                                  (Emptyᵣ (idRed:*: (Emptyⱼ ⊢Δ))) (proj₁ ([n] ⊢Δ [σ′]))
          [σn≡σ′n] = irrelevanceEqTerm {l′ = l} (proj₁ (unwrap [Empty] ⊢Δ [σ]))
                                       (Emptyᵣ (idRed:*: (Emptyⱼ ⊢Δ)))
                                       (proj₂ ([n] ⊢Δ [σ]) [σ′] [σ≡σ′])
          congTerm = emptyrec-congTerm {F = F} {F′ = F} [Γ] [F] [F] (reflᵛ {A = F} {l = l} [Γ] [F])
                       ⊢Δ [σ] [σ′] [σ≡σ′] [σn] [σ′n] [σn≡σ′n]
      in congTerm

-- Validity of empty elimination congruence.
emptyrec-congᵛ : ∀ {F F′ n n′ l} ([Γ] : ⊩ᵛ Γ)
          ([Empty]  : Γ ⊩ᵛ⟨ l ⟩ Empty / [Γ])
          ([F]  : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
          ([F′]  : Γ ⊩ᵛ⟨ l ⟩ F′ / [Γ])
          ([F≡F′]  : Γ ⊩ᵛ⟨ l ⟩ F ≡ F′ / [Γ] / [F])
          ([n] : Γ ⊩ᵛ⟨ l ⟩ n ∷ Empty / [Γ] / [Empty])
          ([n′] : Γ ⊩ᵛ⟨ l ⟩ n′ ∷ Empty / [Γ] / [Empty])
          ([n≡n′] : Γ ⊩ᵛ⟨ l ⟩ n ≡ n′ ∷ Empty / [Γ] / [Empty])
        → Γ ⊩ᵛ⟨ l ⟩ emptyrec p F n ≡ emptyrec p F′ n′ ∷ F / [Γ] / [F]
emptyrec-congᵛ {F = F} {F′} {n} {n′} {l = l}
             [Γ] [Empty] [F] [F′] [F≡F′]
             [n] [n′] [n≡n′] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [σn] = irrelevanceTerm {l′ = l} (proj₁ (unwrap [Empty] ⊢Δ [σ]))
                             (Emptyᵣ (idRed:*: (Emptyⱼ ⊢Δ))) (proj₁ ([n] ⊢Δ [σ]))
      [σn′] = irrelevanceTerm {l′ = l} (proj₁ (unwrap [Empty] ⊢Δ [σ]))
                             (Emptyᵣ (idRed:*: (Emptyⱼ ⊢Δ))) (proj₁ ([n′] ⊢Δ [σ]))
      [σn≡σn′] = irrelevanceEqTerm {l′ = l} (proj₁ (unwrap [Empty] ⊢Δ [σ]))
                                   (Emptyᵣ (idRed:*: (Emptyⱼ ⊢Δ))) ([n≡n′] ⊢Δ [σ])
      congTerm = emptyrec-congTerm {F = F} {F′} [Γ] [F] [F′] [F≡F′]
                   ⊢Δ [σ] [σ] (reflSubst [Γ] ⊢Δ [σ]) [σn] [σn′] [σn≡σn′]
  in congTerm
