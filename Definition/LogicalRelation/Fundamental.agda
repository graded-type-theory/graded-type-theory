------------------------------------------------------------------------
-- The fundamental lemma of the logical relation for validity.
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Fundamental
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped M hiding (_∷_) renaming (_[_,_] to _[_,,_])
open import Definition.Untyped.Properties M

open import Definition.Typed R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Escape R
open import Definition.LogicalRelation.Substitution.Properties R
open import Definition.LogicalRelation.Substitution.Conversion R
open import Definition.LogicalRelation.Substitution.Reduction R
open import Definition.LogicalRelation.Substitution.Reflexivity R
open import Definition.LogicalRelation.Substitution.Introductions R hiding (fundamentalVar)
import Definition.LogicalRelation.Substitution.Introductions.Erased R
  as Erased
import Definition.LogicalRelation.Substitution.Irrelevance R as S
open import Definition.LogicalRelation.Substitution.Weakening R

import Graded.Derived.Erased.Untyped 𝕄 as E

open import Tools.Fin
open import Tools.Function
open import Tools.Level
open import Tools.Product
open import Tools.Unit
open import Tools.Nat
import Tools.PropositionalEquality as PE

private
  variable
    m n : Nat
    Γ : Con Term n
    Δ : Con Term m
    σ σ′ : Subst m n
    A A₁ A₂ t t₁ t₂ : Term _
    ⊩Γ : ⊩ᵛ _

open import Definition.LogicalRelation.Substitution.Introductions.Var R using (fundamentalVar) public

mutual
  -- Fundamental theorem for contexts.
  valid : ⊢ Γ → ⊩ᵛ Γ
  valid ε = ε
  valid (⊢Γ ∙ A) = let [Γ] , [A] = fundamental A in [Γ] ∙ [A]


  -- Fundamental theorem for types.
  fundamental : ∀ {A} (⊢A : Γ ⊢ A) → Σ (⊩ᵛ Γ) (λ [Γ] → Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ])
  fundamental (ℕⱼ x) = valid x , ℕᵛ (valid x)
  fundamental (Emptyⱼ x) = valid x , Emptyᵛ (valid x)
  fundamental (Unitⱼ x ok) = valid x , Unitᵛ (valid x) ok
  fundamental (Uⱼ x) = valid x , Uᵛ (valid x)
  fundamental (ΠΣⱼ ⊢F ⊢G ok)
    with fundamental ⊢F | fundamental ⊢G
  … | [Γ] , [F] | [Γ∙F] , [G] =
    [Γ] , ΠΣᵛ [Γ] [F] (S.irrelevance [Γ∙F] ([Γ] ∙ [F]) [G]) ok
  fundamental (Idⱼ ⊢t ⊢u) =
    case fundamentalTerm ⊢t of λ {
      (⊩Γ , ⊩A , ⊩t) →
    ⊩Γ , Idᵛ ⊩A ⊩t (fundamentalTerm′ ⊩A ⊢u) }
  fundamental (univ {A} ⊢A) with fundamentalTerm ⊢A
  fundamental (univ {A} ⊢A) | [Γ] , [U] , [A] =
    [Γ] , univᵛ {A = A} [Γ] [U] [A]

  -- Fundamental theorem for type equality.
  fundamentalEq : ∀ {A B} → Γ ⊢ A ≡ B
    → ∃  λ ([Γ] : ⊩ᵛ Γ)
    → ∃₂ λ ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ]) ([B] : Γ ⊩ᵛ⟨ ¹ ⟩ B / [Γ])
    → Γ ⊩ᵛ⟨ ¹ ⟩ A ≡ B / [Γ] / [A]
  fundamentalEq (univ {A} {B} x) with fundamentalTermEq x
  fundamentalEq (univ {A} {B} x) | [Γ] , modelsTermEq [U] [t] [u] [t≡u] =
    let [A] = univᵛ {A = A} [Γ] [U] [t]
        [B] = univᵛ {A = B} [Γ] [U] [u]
    in  [Γ] , [A] , [B]
    ,   (λ ⊢Δ [σ] → univEqEq (proj₁ (unwrap [U] ⊢Δ [σ]))
                             (proj₁ (unwrap [A] ⊢Δ [σ]))
                             ([t≡u] ⊢Δ [σ]))
  fundamentalEq (refl D) =
    let [Γ] , [B] = fundamental D
    in  [Γ] , [B] , [B] , (λ ⊢Δ [σ] → reflEq (proj₁ (unwrap [B] ⊢Δ [σ])))
  fundamentalEq (sym A≡B) with fundamentalEq A≡B
  fundamentalEq (sym A≡B) | [Γ] , [B] , [A] , [B≡A] =
    [Γ] , [A] , [B]
        , (λ ⊢Δ [σ] → symEq (proj₁ (unwrap [B] ⊢Δ [σ]))
                            (proj₁ (unwrap [A] ⊢Δ [σ]))
                            ([B≡A] ⊢Δ [σ]))
  fundamentalEq (trans A≡B₁ B₁≡B)
    with fundamentalEq A≡B₁ | fundamentalEq B₁≡B
  fundamentalEq (trans {C = B} A≡B B≡C) | [Γ] , [A] , [B₁] , [A≡B₁]
    | [Γ]₁ , [B₁]₁ , [B] , [B₁≡B] =
      [Γ] , [A] , S.irrelevance {A = B} [Γ]₁ [Γ] [B]
          , (λ ⊢Δ [σ] →
               let [σ]′ = S.irrelevanceSubst [Γ] [Γ]₁ ⊢Δ ⊢Δ [σ]
               in  transEq (proj₁ (unwrap [A] ⊢Δ [σ])) (proj₁ (unwrap [B₁] ⊢Δ [σ]))
                           (proj₁ (unwrap [B] ⊢Δ [σ]′)) ([A≡B₁] ⊢Δ [σ])
                           (irrelevanceEq (proj₁ (unwrap [B₁]₁ ⊢Δ [σ]′))
                                          (proj₁ (unwrap [B₁] ⊢Δ [σ]))
                                          ([B₁≡B] ⊢Δ [σ]′)))
  fundamentalEq (ΠΣ-cong {F = F} {H} {G} {E} {b = BMΠ} ⊢F A≡B A≡B₁ ok)
    with fundamentalEq A≡B | fundamentalEq A≡B₁
  … | [Γ] , [F] , [H] , [F≡H] | [Γ]₁ , [G] , [E] , [G≡E] =
      let [G]′ = S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]
          [E]′ = S.irrelevanceLift {A = E} {F = F} {H = H} [Γ] [F] [H] [F≡H]
                                   (S.irrelevance {A = E} [Γ]₁ ([Γ] ∙ [F]) [E])
          [G≡E]′ = S.irrelevanceEq {A = G} {B = E} [Γ]₁
                                   ([Γ] ∙ [F]) [G] [G]′ [G≡E]
      in  [Γ]
      ,   Πᵛ [Γ] [F] [G]′ ok
      ,   Πᵛ [Γ] [H] [E]′ ok
      ,   Π-congᵛ [Γ] [F] [G]′ [H] [E]′ [F≡H] [G≡E]′ ok
  fundamentalEq (ΠΣ-cong {F = F} {H} {G} {E} {b = BMΣ _} ⊢F A≡B A≡B₁ ok)
    with fundamentalEq A≡B | fundamentalEq A≡B₁
  … | [Γ] , [F] , [H] , [F≡H] | [Γ]₁ , [G] , [E] , [G≡E] =
      let [G]′ = S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]
          [E]′ = S.irrelevanceLift {A = E} {F = F} {H = H} [Γ] [F] [H] [F≡H]
                                   (S.irrelevance {A = E} [Γ]₁ ([Γ] ∙ [F]) [E])
          [G≡E]′ = S.irrelevanceEq {A = G} {B = E} [Γ]₁
                                   ([Γ] ∙ [F]) [G] [G]′ [G≡E]
      in  [Γ]
      ,   Σᵛ {F = F} {G} [Γ] [F] [G]′ ok
      ,   Σᵛ {F = H} {E} [Γ] [H] [E]′ ok
      ,   Σ-congᵛ {F = F} {G} {H} {E}
            [Γ] [F] [G]′ [H] [E]′ [F≡H] [G≡E]′ ok
  fundamentalEq (Id-cong {t₂} {u₂} A₁≡A₂ t₁≡t₂ u₁≡u₂) =
    case fundamentalEq A₁≡A₂ of λ {
      (⊩Γ , ⊩A₁ , ⊩A₂ , A₁≡A₂) →
    case fundamentalTermEq″ ⊩A₁ ⊩A₂ A₁≡A₂ t₁≡t₂ of λ {
      (⊩t₁ , _ , ⊩t₂ , t₁≡t₂) →
    case fundamentalTermEq″ ⊩A₁ ⊩A₂ A₁≡A₂ u₁≡u₂ of λ {
      (⊩u₁ , _ , ⊩u₂ , u₁≡u₂) →
      ⊩Γ
    , Idᵛ ⊩A₁ ⊩t₁ ⊩u₁
    , Idᵛ ⊩A₂ ⊩t₂ ⊩u₂
    , Id-congᵛ t₂ u₂ ⊩A₂ ⊩t₂ ⊩u₂ A₁≡A₂ t₁≡t₂ u₁≡u₂
    }}}

  -- Fundamental theorem for terms.
  fundamentalTerm : ∀ {A t} → Γ ⊢ t ∷ A
    → ∃ λ ([Γ] : ⊩ᵛ Γ)
    → ∃ λ ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ])
    → Γ ⊩ᵛ⟨ ¹ ⟩ t ∷ A / [Γ] / [A]
  fundamentalTerm (ℕⱼ x) = valid x , Uᵛ (valid x) , ℕᵗᵛ (valid x)
  fundamentalTerm (Emptyⱼ x) = valid x , Uᵛ (valid x) , Emptyᵗᵛ (valid x)
  fundamentalTerm (Unitⱼ x ok) =
    valid x , Uᵛ (valid x) , Unitᵗᵛ (valid x) ok
  fundamentalTerm (ΠΣⱼ {F = F} {G} {b = BMΠ} ⊢F ⊢G ok)
    with fundamentalTerm ⊢F | fundamentalTerm ⊢G
  ... | [Γ] , [U] , [F]ₜ | [Γ]₁ , [U]₁ , [G]ₜ =
    let [F]   = univᵛ {A = F} [Γ] [U] [F]ₜ
        [U]′  = S.irrelevance {A = U} [Γ]₁ ([Γ] ∙ [F]) [U]₁
        [F]ₜ′ = S.irrelevanceTerm {A = U} {t = F} [Γ] [Γ] [U] (Uᵛ [Γ]) [F]ₜ
        [G]ₜ′ = S.irrelevanceTerm {A = U} {t = G} [Γ]₁ ([Γ] ∙ [F]) [U]₁ [U]′ [G]ₜ
    in  [Γ] , [U]
    ,   S.irrelevanceTerm {A = U} {t = Π _ , _ ▷ F ▹ G} [Γ] [Γ] (Uᵛ [Γ]) [U]
                          (Πᵗᵛ {F = F} {G} [Γ] [F] [U]′ [F]ₜ′ [G]ₜ′ ok)
  fundamentalTerm (ΠΣⱼ {F = F} {G} {b = BMΣ _} ⊢F ⊢G ok)
    with fundamentalTerm ⊢F | fundamentalTerm ⊢G
  ... | [Γ] , [U] , [F]ₜ | [Γ]₁ , [U]₁ , [G]ₜ =
    let [F]   = univᵛ {A = F} [Γ] [U] [F]ₜ
        [U]′  = S.irrelevance {A = U} [Γ]₁ ([Γ] ∙ [F]) [U]₁
        [F]ₜ′ = S.irrelevanceTerm {A = U} {t = F} [Γ] [Γ] [U] (Uᵛ [Γ]) [F]ₜ
        [G]ₜ′ = S.irrelevanceTerm {A = U} {t = G} [Γ]₁ ([Γ] ∙ [F]) [U]₁ [U]′ [G]ₜ
    in  [Γ] , [U]
    ,   S.irrelevanceTerm
          {A = U} {t = Σ _ , _ ▷ F ▹ G} [Γ] [Γ] (Uᵛ [Γ]) [U]
          (Σᵗᵛ {F = F} {G} [Γ] [F] [U]′ [F]ₜ′ [G]ₜ′ ok)
  fundamentalTerm (var ⊢Γ x∷A) = valid ⊢Γ , fundamentalVar x∷A (valid ⊢Γ)
  fundamentalTerm (lamⱼ {F = F} {t} {G} ⊢F ⊢t ok)
    with fundamental ⊢F | fundamentalTerm ⊢t
  ... | [Γ] , [F] | [Γ]₁ , [G] , [t] =
    let [G]′ = S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]
        [t]′ = S.irrelevanceTerm {A = G} {t = t} [Γ]₁ ([Γ] ∙ [F]) [G] [G]′ [t]
    in  [Γ] , Πᵛ [Γ] [F] [G]′ ok
    ,   lamᵛ {F = F} {G} {t} [Γ] [F] [G]′ [t]′ ok
  fundamentalTerm (_∘ⱼ_ {t = g} {F} {G} {u = a} Dt Du)
    with fundamentalTerm Dt | fundamentalTerm Du
  ... | [Γ] , [ΠFG] , [t] | [Γ]₁ , [F] , [u] =
    let [ΠFG]′ = S.irrelevance {A = Π _ , _ ▷ F ▹ G} [Γ] [Γ]₁ [ΠFG]
        [t]′ = S.irrelevanceTerm {A = Π _ , _ ▷ F ▹ G} {t = g} [Γ] [Γ]₁ [ΠFG] [ΠFG]′ [t]
        [G[t]] = substSΠ {F = F} {G} {a} BΠ! [Γ]₁ [F] [ΠFG]′ [u]
        [t∘u] = appᵛ {F = F} {G} {g} {a} [Γ]₁ [F] [ΠFG]′ [t]′ [u]
    in  [Γ]₁ , [G[t]] , [t∘u]
  fundamentalTerm (prodⱼ {F = F} {G} {t} {u} ⊢F ⊢G ⊢t ⊢u ok)
    with fundamentalTerm ⊢t | fundamental ⊢G | fundamentalTerm ⊢u
  ... | [Γ] , [F] , [t] | [Γ]₁ , [G] | [Γ]₂ , [Gt] , [u] =
    let [G]′ = S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]
        [u]′ = S.irrelevanceTerm {A = G [ t ]₀} {t = u} [Γ]₂ [Γ] [Gt]
                                 (substS {F = F} {G} [Γ] [F] [G]′ [t]) [u]
    in    [Γ]
        , Σᵛ {F = F} {G} [Γ] [F] [G]′ ok
        , prodᵛ {F = F} {G} {t} {u} [Γ] [F] [G]′ [t] [u]′ ok
  fundamentalTerm (fstⱼ {F = F} {G} {t} ⊢F ⊢G ⊢t) with
    fundamental ⊢F | fundamental ⊢G | fundamentalTerm ⊢t
  ... | [Γ] , [F] | [Γ]₁ , [G]₁ | [Γ]₂ , [ΣFG]₂ , [t]₂ =
    let ok = ⊩ᵛΠΣ→ΠΣ-allowed [ΣFG]₂
        [G] = S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]₁

        [t] = S.irrelevanceTerm {A = Σ _ , _ ▷ F ▹ G} {t = t}
                [Γ]₂ [Γ] [ΣFG]₂ (Σᵛ {F = F} {G} [Γ] [F] [G] ok) [t]₂
        [fst] = fstᵛ {F = F} {G} {t} [Γ] [F] [G] ok [t]
    in  [Γ] , [F] , [fst]
  fundamentalTerm (sndⱼ {F = F} {G} {t} ⊢F ⊢G ⊢t) with
    fundamental ⊢F | fundamental ⊢G | fundamentalTerm ⊢t
  ... | [Γ] , [F] | [Γ]₁ , [G]₁ | [Γ]₂ , [ΣFG]₂ , [t]₂ =
    let ok = ⊩ᵛΠΣ→ΠΣ-allowed [ΣFG]₂
        [G] = S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]₁

        [t] = S.irrelevanceTerm {A = Σ _ , _ ▷ F ▹ G} {t = t}
                [Γ]₂ [Γ] [ΣFG]₂ (Σᵛ {F = F} {G} [Γ] [F] [G] ok) [t]₂
        [fst] = fstᵛ {F = F} {G} {t} [Γ] [F] [G] ok [t]
        [Gfst] = substS {F = F} {G} [Γ] [F] [G] [fst]
        [snd] = sndᵛ {F = F} {G} [Γ] [F] [G] ok [t]
    in  [Γ] , [Gfst] , [snd]
  fundamentalTerm (zeroⱼ x) = valid x , ℕᵛ (valid x) , zeroᵛ {l = ¹} (valid x)
  fundamentalTerm (sucⱼ {n} t) with fundamentalTerm t
  fundamentalTerm (sucⱼ {n} t) | [Γ] , [ℕ] , [n] =
    [Γ] , [ℕ] , sucᵛ {n = n} [Γ] [ℕ] [n]
  fundamentalTerm (natrecⱼ {A = G} {z} {s} {n = n} ⊢G ⊢z ⊢s ⊢n)
    with fundamental ⊢G | fundamentalTerm ⊢z | fundamentalTerm ⊢s
       | fundamentalTerm ⊢n
  ... | [Γ] , [G] | [Γ]₁ , [G₀] , [z] | [Γ]₂ , [G₊] , [s] | [Γ]₃ , [ℕ] , [n] =
    let [Γ]′ = [Γ]₃
        [G]′ = S.irrelevance {A = G} [Γ] ([Γ]′ ∙ [ℕ]) [G]
        [G₀]′ = S.irrelevance {A = G [ zero ]₀} [Γ]₁ [Γ]′ [G₀]
        [G₊]′ = S.irrelevance {A = G [ (suc (var x1)) ]↑²} [Γ]₂ ([Γ]′ ∙ [ℕ] ∙ [G]′) [G₊]
        [Gₙ]′ = substS {F = ℕ} {G = G} {t = n} [Γ]′ [ℕ] [G]′ [n]
        [z]′ = S.irrelevanceTerm {A = G [ zero ]₀} {t = z} [Γ]₁ [Γ]′
                                 [G₀] [G₀]′ [z]
        [s]′ = S.irrelevanceTerm {A = G [ (suc (var x1)) ]↑²} {t = s} [Γ]₂ ([Γ]′ ∙ [ℕ] ∙ [G]′) [G₊] [G₊]′ [s]
    in [Γ]′ , [Gₙ]′
    , (natrecᵛ {F = G} {z} {s} {n} [Γ]′ [ℕ] [G]′ [G₀]′ [G₊]′ [Gₙ]′ [z]′ [s]′ [n])
  fundamentalTerm (emptyrecⱼ {A} {t = n} ⊢A ⊢n)
    with fundamental ⊢A | fundamentalTerm ⊢n
  ... | [Γ] , [A] | [Γ]′ , [Empty] , [n] =
    let [A]′ = S.irrelevance {A = A} [Γ] [Γ]′ [A]
    in [Γ]′ , [A]′ , emptyrecᵛ {F = A} {n} [Γ]′ [Empty] [A]′ [n]
  fundamentalTerm (starⱼ x ok) =
    valid x , Unitᵛ (valid x) ok , starᵛ {l = ¹} (valid x) ok
  fundamentalTerm (conv {t} {A} {B} ⊢t A′≡A)
    with fundamentalTerm ⊢t | fundamentalEq A′≡A
  fundamentalTerm (conv {t} {A} {B} ⊢t A′≡A) | [Γ] , [A′] , [t]
    | [Γ]₁ , [A′]₁ , [A] , [A′≡A] =
      let [Γ]′ = [Γ]₁
          [t]′ = S.irrelevanceTerm {A = A} {t = t} [Γ] [Γ]′ [A′] [A′]₁ [t]
      in  [Γ]′ , [A]
      ,   convᵛ {t = t} {A} {B} [Γ]′ [A′]₁ [A] [A′≡A] [t]′
  fundamentalTerm (prodrecⱼ ⊢F ⊢G ⊢A ⊢t ⊢u _)
    with fundamental ⊢F | fundamental ⊢G | fundamental ⊢A | fundamentalTerm ⊢t | fundamentalTerm ⊢u
  fundamentalTerm
    (prodrecⱼ {F = F} {G} {q′ = q} {A} {t = t} {u} {r = r}
       ⊢F ⊢G ⊢t ⊢A ⊢u _)
    | [Γ] , [F] | [Γ]₁ , [G] | [Γ]₂ , [A]
    | [Γ]₃ , [Σ] , [t] | [Γ]₄ , [A₊] , [u] =
      let [G]′ = S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]
          [Σ]′ = S.irrelevance {A = Σ _ , q ▷ F ▹ G} [Γ]₃ [Γ] [Σ]
          [A]′ = S.irrelevance {A = A} [Γ]₂ ([Γ] ∙ [Σ]′) [A]
          [A₊]′ = S.irrelevance {A = A [ prod! (var (x0 +1)) (var x0) ]↑²}
                                [Γ]₄ ([Γ] ∙ [F] ∙ [G]′) [A₊]
          [t]′ = S.irrelevanceTerm
                   {A = Σ _ , q ▷ F ▹ G} {t = t} [Γ]₃ [Γ] [Σ] [Σ]′ [t]
          [u]′ = S.irrelevanceTerm {A = A [ prod! (var (x0 +1)) (var x0) ]↑²} {t = u}
                                   [Γ]₄ ([Γ] ∙ [F] ∙ [G]′) [A₊] [A₊]′ [u]
          [Aₜ] = substS {F = Σ _ , q ▷ F ▹ G} {A} {t} [Γ] [Σ]′ [A]′ [t]′
          [prodrec] = prodrecᵛ {r = r} {F = F} {G} {A} {t} {u}
                        [Γ] [F] [G]′ [Σ]′ [A]′ [A₊]′ [Aₜ] [t]′ [u]′
      in  [Γ] , [Aₜ] , [prodrec]
  fundamentalTerm (unitrecⱼ {t = t} {u = u} ⊢A ⊢t ⊢u ok)
    with fundamentalTerm ⊢u | fundamentalTerm ⊢t | fundamental ⊢A
  ... | [Γ] , [A₊]′ , [u]′ | [Γ]₁ , [Unit]₁ , [t]₁ | [Γ]₂ , [A]₂ =
    let [Unit] = Unitᵛ [Γ] ok
        [t] = S.irrelevanceTerm {t = t} [Γ]₁ [Γ] [Unit]₁ [Unit] [t]₁
        [A] = S.irrelevance [Γ]₂ ([Γ] ∙ [Unit]) [A]₂
        [A₊] = substS [Γ] [Unit] [A] (starᵛ {l = ¹} [Γ] ok)
        [u] = S.irrelevanceTerm {t = u} [Γ] [Γ] [A₊]′ [A₊] [u]′
        [ur] = unitrecᵛ {t = t} {u = u} [Γ] ok [A] [t] [u]
        [Aₜ] = substS {t = t} [Γ] [Unit] [A] [t]
    in  [Γ] , [Aₜ] , [ur]
  fundamentalTerm (Idⱼ {t} {u} ⊢A ⊢t ⊢u) =
    case fundamentalTerm ⊢t of λ {
      (⊩Γ , ⊩A , ⊩t) →
    let ⊩U = Uᵛ ⊩Γ in
      ⊩Γ
    , ⊩U
    , (λ {_ _ _} →
         Idᵗᵛ t u ⊩A (fundamentalTerm′ ⊩U ⊢A) ⊩t
           (fundamentalTerm′ ⊩A ⊢u)) }
  fundamentalTerm (rflⱼ ⊢t) =
    case fundamentalTerm ⊢t of λ {
      (⊩Γ , ⊩A , ⊩t) →
      ⊩Γ
    , Idᵛ ⊩A ⊩t ⊩t
    , rflᵛ }
  fundamentalTerm (Jⱼ {t} {u} {w} ⊢A ⊢t ⊢B ⊢u ⊢v ⊢w) =
    case fundamental ⊢A of λ {
      (⊩Γ , ⊩A) →
    let ⊩wk1-A = wk1ᵛ _ ⊩A ⊩A in
    case (λ {k Δ σ} →
            fundamentalTerm′ ⊩A ⊢t
              {k = k} {Δ = Δ} {σ = σ}) of λ {
      ⊩t →
    case (λ {k Δ σ} →
            fundamentalTerm′ ⊩A ⊢v
              {k = k} {Δ = Δ} {σ = σ}) of λ {
      ⊩v →
    case (λ {k Δ σ} →
            fundamentalTerm′ (Idᵛ ⊩A ⊩t ⊩v) ⊢w
              {k = k} {Δ = Δ} {σ = σ}) of λ {
      ⊩w →
    case PE.subst (_ ⊩ᵛ⟨ ¹ ⟩_/ ⊩Γ) (≡Id-wk1-wk1-0[]₀ {t = t})
           (Idᵛ ⊩A ⊩t ⊩t) of λ {
      ⊩Id →
    case PE.subst (_ ⊩ᵛ⟨ ¹ ⟩_/ ⊩Γ) (≡Id-wk1-wk1-0[]₀ {t = t})
           (Idᵛ ⊩A ⊩t ⊩v) of λ {
      ⊩Id′ →
    case fundamental′ ⊢B of λ {
      ⊩B →
    case substD ⊩v ⊩Id′
           (S.irrelevanceTerm′ {t = w} ≡Id-wk1-wk1-0[]₀ _ _
              (Idᵛ ⊩A ⊩t ⊩v) ⊩Id′ ⊩w)
           ⊩B of λ {
      ⊩B[v,w] →
    case substD
           {⊩B = Idᵛ ⊩wk1-A (wk1Termᵛ t ⊩A ⊩A ⊩t) (varᵛ here _ ⊩wk1-A)}
           ⊩t ⊩Id
           (S.irrelevanceTerm′ {t = rfl} ≡Id-wk1-wk1-0[]₀ _ _
              (Idᵛ ⊩A ⊩t ⊩t) ⊩Id rflᵛ)
           ⊩B of λ {
      ⊩B[t,rfl] →
      ⊩Γ
    , ⊩B[v,w]
    , (λ {_ _ _} →
         Jᵛ u ⊩B ⊩B[t,rfl] ⊩B[v,w]
           (fundamentalTerm′ ⊩B[t,rfl] ⊢u) ⊩w) }}}}}}}}}
  fundamentalTerm (Kⱼ {u} {v} ⊢t ⊢B ⊢u ⊢v ok) =
    case fundamentalTerm ⊢t of λ {
      (⊩Γ , ⊩A , ⊩t) →
    let ⊩Id = Idᵛ ⊩A ⊩t ⊩t in
    case fundamental′ ⊢B of λ {
      ⊩B →
    case (λ {k Δ σ} →
            fundamentalTerm′ ⊩Id ⊢v
              {k = k} {Δ = Δ} {σ = σ}) of λ {
      ⊩v →
    case substS {t = rfl} _ ⊩Id ⊩B rflᵛ of λ {
      ⊩B[rfl] →
    case substS {t = v} _ ⊩Id ⊩B ⊩v of λ {
      ⊩B[v] →
      ⊩Γ
    , ⊩B[v]
    , (λ {_ _ _} →
         Kᵛ u ok ⊩B ⊩B[rfl]
           (fundamentalTerm′ ⊩B[rfl] ⊢u) ⊩v ⊩B[v]) }}}}}
  fundamentalTerm ([]-congⱼ {t} {u} {v} ⊢t ⊢u ⊢v ok) =
    case fundamentalTerm ⊢t of λ {
      (⊩Γ , ⊩A , ⊩t) →
    let ⊩u = fundamentalTerm′ ⊩A ⊢u in
      ⊩Γ
    , Idᵛ (Erasedᵛ ⊩A) ([]ᵛ t ⊩t) ([]ᵛ u ⊩u)
    , []-congᵛ v (fundamentalTerm′ (Idᵛ ⊩A ⊩t ⊩u) ⊢v)
    }
    where
    open Erased ([]-cong→Erased ok) hiding ([]-congᵛ)

  -- Fundamental theorem for term equality.
  fundamentalTermEq : ∀ {A t t′} → Γ ⊢ t ≡ t′ ∷ A
                    → ∃ λ ([Γ] : ⊩ᵛ Γ) →
                      [ Γ ⊩ᵛ⟨ ¹ ⟩ t ≡ t′ ∷ A / [Γ] ]
  fundamentalTermEq (refl D) with fundamentalTerm D
  ... | [Γ] , [A] , [t] =
    [Γ] , modelsTermEq [A] [t] [t]
                       (λ ⊢Δ [σ] → reflEqTerm (proj₁ (unwrap [A] ⊢Δ [σ]))
                                              (proj₁ ([t] ⊢Δ [σ])))
  fundamentalTermEq (sym D) with fundamentalTermEq D
  fundamentalTermEq (sym D) | [Γ] , modelsTermEq [A] [t′] [t] [t′≡t] =
    [Γ] , modelsTermEq [A] [t] [t′]
                       (λ ⊢Δ [σ] → symEqTerm (proj₁ (unwrap [A] ⊢Δ [σ]))
                                             ([t′≡t] ⊢Δ [σ]))
  fundamentalTermEq (trans t≡u u≡t′)
    with fundamentalTermEq t≡u | fundamentalTermEq u≡t′
  fundamentalTermEq (trans {A} {v = r} t≡u u≡t′)
    | [Γ] , modelsTermEq [A] [t] [u] [t≡u]
    | [Γ]₁ , modelsTermEq [A]₁ [t]₁ [u]₁ [t≡u]₁ =
      let [r]′ = S.irrelevanceTerm {A = A} {t = r} [Γ]₁ [Γ] [A]₁ [A] [u]₁
      in  [Γ] , modelsTermEq [A] [t] [r]′
                  (λ ⊢Δ [σ] →
                     let [σ]′ = S.irrelevanceSubst [Γ] [Γ]₁ ⊢Δ ⊢Δ [σ]
                         [t≡u]₁′ = irrelevanceEqTerm (proj₁ (unwrap [A]₁ ⊢Δ [σ]′))
                                                     (proj₁ (unwrap [A] ⊢Δ [σ]))
                                                     ([t≡u]₁ ⊢Δ [σ]′)
                     in  transEqTerm (proj₁ (unwrap [A] ⊢Δ [σ]))
                                     ([t≡u] ⊢Δ [σ]) [t≡u]₁′)
  fundamentalTermEq (conv {t} {u} {A} {B} t≡u A′≡A)
    with fundamentalTermEq t≡u | fundamentalEq A′≡A
  fundamentalTermEq (conv {t} {u} {A} {B} t≡u A′≡A)
    | [Γ] , modelsTermEq [A′] [t] [u] [t≡u] | [Γ]₁ , [A′]₁ , [A] , [A′≡A] =
      let [t]′ = S.irrelevanceTerm {A = A} {t = t} [Γ] [Γ]₁ [A′] [A′]₁ [t]
          [u]′ = S.irrelevanceTerm {A = A} {t = u} [Γ] [Γ]₁ [A′] [A′]₁ [u]
          [t]″ = convᵛ {t = t} {A} {B} [Γ]₁ [A′]₁ [A] [A′≡A] [t]′
          [u]″ = convᵛ {t = u} {A} {B} [Γ]₁ [A′]₁ [A] [A′≡A] [u]′
      in  [Γ]₁
      ,   modelsTermEq [A] [t]″ [u]″
            (λ ⊢Δ [σ] →
               let [σ]′ = S.irrelevanceSubst [Γ]₁ [Γ] ⊢Δ ⊢Δ [σ]
                   [t≡u]′ = irrelevanceEqTerm (proj₁ (unwrap [A′] ⊢Δ [σ]′))
                                              (proj₁ (unwrap [A′]₁ ⊢Δ [σ]))
                                              ([t≡u] ⊢Δ [σ]′)
               in  convEqTerm₁ (proj₁ (unwrap [A′]₁ ⊢Δ [σ])) (proj₁ (unwrap [A] ⊢Δ [σ]))
                               ([A′≡A] ⊢Δ [σ]) [t≡u]′)
  fundamentalTermEq
    (ΠΣ-cong {F = F} {H} {G} {E = E} {b = BMΠ} ⊢F F≡H G≡E ok)
    with fundamental ⊢F | fundamentalTermEq F≡H | fundamentalTermEq G≡E
  ... | [Γ] , [F] | [Γ]₁ , modelsTermEq [U] [F]ₜ [H]ₜ [F≡H]ₜ
      | [Γ]₂ , modelsTermEq [U]₁ [G]ₜ [E]ₜ [G≡E]ₜ =
    let [U]′  = Uᵛ [Γ]
        [F]ₜ′ = S.irrelevanceTerm {A = U} {t = F} [Γ]₁ [Γ] [U] [U]′ [F]ₜ
        [H]ₜ′ = S.irrelevanceTerm {A = U} {t = H} [Γ]₁ [Γ] [U] [U]′ [H]ₜ
        [F]′  = S.irrelevance {A = F} [Γ] [Γ]₁ [F]
        [H]   = univᵛ {A = H} [Γ] [U]′ [H]ₜ′
        [F≡H] = S.irrelevanceEq {A = F} {B = H} [Γ]₁ [Γ] [F]′ [F]
                  (univEqᵛ {A = F} {H} [Γ]₁ [U] [F]′ [F≡H]ₜ)
        [U]₁′ = Uᵛ (_∙_ {A = F} [Γ] [F])
        [U]₂′ = Uᵛ (_∙_ {A = H} [Γ] [H])
        [G]ₜ′ = S.irrelevanceTerm {A = U} {t = G} [Γ]₂ ([Γ] ∙ [F])
                                  [U]₁ [U]₁′ [G]ₜ
        [E]ₜ′ = S.irrelevanceTermLift {A = U} {F = F} {H = H} {t = E}
                                      [Γ] [F] [H] [F≡H] [U]₁′
                  (S.irrelevanceTerm {A = U} {t = E} [Γ]₂ ([Γ] ∙ [F]) [U]₁ [U]₁′ [E]ₜ)
        [F≡H]ₜ′ = S.irrelevanceEqTerm {A = U} {t = F} {u = H}
                                      [Γ]₁ [Γ] [U] (Uᵛ [Γ]) [F≡H]ₜ
        [G≡E]ₜ′ = S.irrelevanceEqTerm {A = U} {t = G} {u = E} [Γ]₂
                                      (_∙_ {A = F} [Γ] [F]) [U]₁ [U]₁′ [G≡E]ₜ
    in  [Γ]
    ,   modelsTermEq
          [U]′
          (Πᵗᵛ {F = F} {G} [Γ] [F] [U]₁′ [F]ₜ′ [G]ₜ′ ok)
          (Πᵗᵛ {F = H} {E} [Γ] [H] [U]₂′ [H]ₜ′ [E]ₜ′ ok)
          (Π-congᵗᵛ {F = F} {H} {G} {E} [Γ] [F] [H] [U]₁′ [U]₂′
             [F]ₜ′ [G]ₜ′ [H]ₜ′ [E]ₜ′ [F≡H]ₜ′ [G≡E]ₜ′ ok)
  fundamentalTermEq
    (ΠΣ-cong {F = F} {H = H} {G = G} {E = E} {b = BMΣ _} ⊢F F≡H G≡E ok)
    with fundamental ⊢F | fundamentalTermEq F≡H | fundamentalTermEq G≡E
  ... | [Γ] , [F] | [Γ]₁ , modelsTermEq [U] [F]ₜ [H]ₜ [F≡H]ₜ
      | [Γ]₂ , modelsTermEq [U]₁ [G]ₜ [E]ₜ [G≡E]ₜ =
    let [U]′  = Uᵛ [Γ]
        [F]ₜ′ = S.irrelevanceTerm {A = U} {t = F} [Γ]₁ [Γ] [U] [U]′ [F]ₜ
        [H]ₜ′ = S.irrelevanceTerm {A = U} {t = H} [Γ]₁ [Γ] [U] [U]′ [H]ₜ
        [F]′  = S.irrelevance {A = F} [Γ] [Γ]₁ [F]
        [H]   = univᵛ {A = H} [Γ] [U]′ [H]ₜ′
        [F≡H] = S.irrelevanceEq {A = F} {B = H} [Γ]₁ [Γ] [F]′ [F]
                  (univEqᵛ {A = F} {H} [Γ]₁ [U] [F]′ [F≡H]ₜ)
        [U]₁′ = Uᵛ (_∙_ {A = F} [Γ] [F])
        [U]₂′ = Uᵛ (_∙_ {A = H} [Γ] [H])
        [G]ₜ′ = S.irrelevanceTerm {A = U} {t = G} [Γ]₂ ([Γ] ∙ [F])
                                  [U]₁ [U]₁′ [G]ₜ
        [E]ₜ′ = S.irrelevanceTermLift {A = U} {F = F} {H = H} {t = E}
                                      [Γ] [F] [H] [F≡H] [U]₁′
                  (S.irrelevanceTerm {A = U} {t = E} [Γ]₂ ([Γ] ∙ [F]) [U]₁ [U]₁′ [E]ₜ)
        [F≡H]ₜ′ = S.irrelevanceEqTerm {A = U} {t = F} {u = H}
                                      [Γ]₁ [Γ] [U] (Uᵛ [Γ]) [F≡H]ₜ
        [G≡E]ₜ′ = S.irrelevanceEqTerm {A = U} {t = G} {u = E} [Γ]₂
                                      (_∙_ {A = F} [Γ] [F]) [U]₁ [U]₁′ [G≡E]ₜ
    in  [Γ]
    ,   modelsTermEq
          [U]′
          (Σᵗᵛ {F = F} {G} [Γ] [F] [U]₁′ [F]ₜ′ [G]ₜ′ ok)
          (Σᵗᵛ {F = H} {E} [Γ] [H] [U]₂′ [H]ₜ′ [E]ₜ′ ok)
          (Σ-congᵗᵛ {F = F} {G} {H} {E} [Γ] [F] [H] [U]₁′ [U]₂′
                    [F]ₜ′ [G]ₜ′ [H]ₜ′ [E]ₜ′ [F≡H]ₜ′ [G≡E]ₜ′ ok)
  fundamentalTermEq
    (app-cong {f = f} {g} {F = F} {G} {a = a} {b} f≡g a≡b)
    with fundamentalTermEq f≡g | fundamentalTermEq a≡b
  ... | [Γ] , modelsTermEq [ΠFG] [f] [g] [f≡g]
      | [Γ]₁ , modelsTermEq [F] [a] [b] [a≡b] =
    let [ΠFG]′ = S.irrelevance {A = Π _ , _ ▷ F ▹ G} [Γ] [Γ]₁ [ΠFG]
        [f]′ = S.irrelevanceTerm {A = Π _ , _ ▷ F ▹ G} {t = f} [Γ] [Γ]₁ [ΠFG] [ΠFG]′ [f]
        [g]′ = S.irrelevanceTerm {A = Π _ , _ ▷ F ▹ G} {t = g} [Γ] [Γ]₁ [ΠFG] [ΠFG]′ [g]
        [f≡g]′ = S.irrelevanceEqTerm {A = Π _ , _ ▷ F ▹ G} {t = f} {u = g}
                                     [Γ] [Γ]₁ [ΠFG] [ΠFG]′ [f≡g]
        [G[a]] = substSΠ {F = F} {G} {a} BΠ! [Γ]₁ [F] [ΠFG]′ [a]
        [G[b]] = substSΠ {F = F} {G} {b} BΠ! [Γ]₁ [F] [ΠFG]′ [b]
        [G[a]≡G[b]] = substSΠEq {F = F} {G} {F} {G} {a} {b} BΠ! [Γ]₁ [F] [F] [ΠFG]′
                                [ΠFG]′ (reflᵛ {A = Π _ , _ ▷ F ▹ G} [Γ]₁ [ΠFG]′) [a] [b] [a≡b]
    in  [Γ]₁ , modelsTermEq [G[a]]
                            (appᵛ {F = F} {G} {f} {a} [Γ]₁ [F] [ΠFG]′ [f]′ [a])
                            (conv₂ᵛ {t = g ∘ b} {G [ a ]₀} {G [ b ]₀} [Γ]₁
                                    [G[a]] [G[b]] [G[a]≡G[b]]
                                    (appᵛ {F = F} {G} {g} {b}
                                          [Γ]₁ [F] [ΠFG]′ [g]′ [b]))
                            (app-congᵛ {F = F} {G} {f} {g} {a} {b}
                                       [Γ]₁ [F] [ΠFG]′ [f≡g]′ [a]
                                       [b] [a≡b])
  fundamentalTermEq
    (β-red {F = F} {G} {t = b} {a} {p = p} {p′ = q} ⊢F ⊢G ⊢b ⊢a p≡p′ ok)
    with fundamental ⊢F | fundamentalTerm ⊢b | fundamentalTerm ⊢a
  ... | [Γ] , [F] | [Γ]₁ , [G] , [b] | [Γ]₂ , [F]₁ , [a] =
    let [G]′ = S.irrelevance {A = G} [Γ]₁ ([Γ]₂ ∙ [F]₁) [G]
        [b]′ = S.irrelevanceTerm {A = G} {t = b} [Γ]₁ ([Γ]₂ ∙ [F]₁) [G] [G]′ [b]
        [G[a]] = substS {F = F} {G} {a} [Γ]₂ [F]₁ [G]′ [a]
        [b[a]] = substSTerm {F = F} {G} {a} {b} [Γ]₂ [F]₁ [G]′ [b]′ [a]
        [lam] , [eq] =
          redSubstTermᵛ {A = G [ a ]₀} {lam p b ∘⟨ q ⟩ a} {b [ a ]₀} [Γ]₂
            (λ {_} {Δ} {σ} ⊢Δ [σ] →
               let [liftσ] = liftSubstS {F = F} [Γ]₂ ⊢Δ [F]₁ [σ]
                   ⊢σF = escape (proj₁ (unwrap [F]₁ ⊢Δ [σ]))
                   ⊢σG = escape (proj₁ (unwrap [G]′ (⊢Δ ∙ ⊢σF) (liftSubstS {F = F} [Γ]₂ ⊢Δ [F]₁ [σ])))
                   ⊢σb = escapeTerm (proj₁ (unwrap [G]′ (⊢Δ ∙ ⊢σF) [liftσ]))
                                       (proj₁ ([b]′ (⊢Δ ∙ ⊢σF) [liftσ]))
                   ⊢σa = escapeTerm (proj₁ (unwrap [F]₁ ⊢Δ [σ]))
                                       (proj₁ ([a] ⊢Δ [σ]))
               in  PE.subst₂ (λ x y → _ ⊢ lam _ b ∘ a [ σ ] ⇒ x ∷ y)
                             (PE.sym (singleSubstLift b a))
                             (PE.sym (singleSubstLift G a))
                             (β-red ⊢σF ⊢σG ⊢σb ⊢σa p≡p′ ok))
                         [G[a]] [b[a]]
    in  [Γ]₂ , modelsTermEq [G[a]] [lam] [b[a]] [eq]
  fundamentalTermEq (η-eq {F = F} {f = f} {G = G} {g} ⊢F ⊢t ⊢t′ t≡t′)
    with fundamental ⊢F | fundamentalTerm ⊢t
       | fundamentalTerm ⊢t′ | fundamentalTermEq t≡t′
  ... | [Γ] , [F] | [Γ]₁ , [ΠFG] , [t] | [Γ]₂ , [ΠFG]₁ , [t′]
      | [Γ]₃ , modelsTermEq [G] [t0] [t′0] [t0≡t′0] =
    let ok = ⊩ᵛΠΣ→ΠΣ-allowed [ΠFG]
        [F]′ = S.irrelevance {A = F} [Γ] [Γ]₁ [F]
        [G]′ = S.irrelevance {A = G} [Γ]₃ ([Γ]₁ ∙ [F]′) [G]
        [t′]′ = S.irrelevanceTerm {A = Π _ , _ ▷ F ▹ G} {t = g}
                                  [Γ]₂ [Γ]₁ [ΠFG]₁ [ΠFG] [t′]
        [ΠFG]″ = Πᵛ {F = F} {G} [Γ]₁ [F]′ [G]′ ok
        [t]″ = S.irrelevanceTerm {A = Π _ , _ ▷ F ▹ G} {t = f}
                                  [Γ]₁ [Γ]₁ [ΠFG] [ΠFG]″ [t]
        [t′]″ = S.irrelevanceTerm {A = Π _ , _ ▷ F ▹ G} {t = g}
                                   [Γ]₂ [Γ]₁ [ΠFG]₁ [ΠFG]″ [t′]
        [t0≡t′0]′ = S.irrelevanceEqTerm {A = G} {t = wk1 f ∘ var x0}
                                        {u = wk1 g ∘ var x0}
                                        [Γ]₃ ([Γ]₁ ∙ [F]′) [G] [G]′ [t0≡t′0]
        [t≡t′] = η-eqᵛ {f = f} {g} {F} {G}
                   [Γ]₁ [F]′ [G]′ ok [t]″ [t′]″ [t0≡t′0]′
        [t≡t′]′ = S.irrelevanceEqTerm {A = Π _ , _ ▷ F ▹ G} {t = f} {u = g}
                                      [Γ]₁ [Γ]₁ [ΠFG]″ [ΠFG] [t≡t′]
    in  [Γ]₁ , modelsTermEq [ΠFG] [t] [t′]′ [t≡t′]′
  fundamentalTermEq (suc-cong x) with fundamentalTermEq x
  fundamentalTermEq (suc-cong {m = t} {n = u} x)
    | [Γ] , modelsTermEq [A] [t] [u] [t≡u] =
      let [suct] = sucᵛ {n = t} [Γ] [A] [t]
          [sucu] = sucᵛ {n = u} [Γ] [A] [u]
      in  [Γ] , modelsTermEq [A] [suct] [sucu]
                             (λ ⊢Δ [σ] →
                                sucEqTerm (proj₁ (unwrap [A] ⊢Δ [σ])) ([t≡u] ⊢Δ [σ]))
  fundamentalTermEq (natrec-cong ⊢F F≡F′ z≡z′ s≡s′ n≡n′)
    with fundamentalEq F≡F′ |
         fundamentalTermEq z≡z′      |
         fundamentalTermEq s≡s′      |
         fundamentalTermEq n≡n′
  fundamentalTermEq
    (natrec-cong
       {A = F} {A′ = F′} {z = z} {z′ = z′} {s = s} {s′ = s′}
       {n′ = n′} {p = p} {q = q} {r = r} {n = n}
       ⊢F F≡F′ z≡z′ s≡s′ n≡n′) |
    [Γ]  , [F] , [F′] , [F≡F′] |
    [Γ]₁ , modelsTermEq [F₀] [z] [z′] [z≡z′] |
    [Γ]₂ , modelsTermEq [F₊] [s] [s′] [s≡s′] |
    [Γ]₃ , modelsTermEq [ℕ] [n] [n′] [n≡n′] =
      let sType = F [ suc (var x1) ]↑²
          s′Type = F′ [ suc (var x1) ]↑²
          [0] = S.irrelevanceTerm {l = ¹} {A = ℕ} {t = zero}
                                  [Γ]₃ [Γ]₃ (ℕᵛ [Γ]₃) [ℕ] (zeroᵛ {l = ¹} [Γ]₃)
          [F]′ = S.irrelevance {A = F} [Γ] ([Γ]₃ ∙ [ℕ]) [F]
          [F]″ = S.irrelevance {A = F} [Γ] ([Γ]₃ ∙ ℕᵛ [Γ]₃) [F]
          [F₀]′ = S.irrelevance {A = F [ zero ]₀} [Γ]₁ [Γ]₃ [F₀]
          [F₊]′ = S.irrelevance {A = sType} [Γ]₂ ([Γ]₃ ∙ [ℕ] ∙ [F]′) [F₊]
          [Fₙ]′ = substS {F = ℕ} {F} {n} [Γ]₃ [ℕ] [F]′ [n]
          [F′]′ = S.irrelevance {A = F′} [Γ] ([Γ]₃ ∙ [ℕ]) [F′]
          [F′]″ = S.irrelevance {A = F′} [Γ] ([Γ]₃ ∙ ℕᵛ [Γ]₃) [F′]
          [F₀]″ = substS {F = ℕ} {F} {zero} [Γ]₃ [ℕ] [F]′ [0]
          [F′₀]′ = substS {F = ℕ} {F′} {zero} [Γ]₃ [ℕ] [F′]′ [0]

          [F₊]″ = subst↑²S-suc [Γ]₃ [F]″
          [F′₊]″ = subst↑²S-suc [Γ]₃ [F′]″
          [F′₊]′ = S.irrelevance ([Γ]₃ ∙ ℕᵛ [Γ]₃ ∙ [F′]″) ([Γ]₃ ∙ [ℕ] ∙ [F′]′) [F′₊]″
          [F′ₙ′]′ = substS {F = ℕ} {F′} {n′} [Γ]₃ [ℕ] [F′]′ [n′]
          [ℕ≡ℕ] = reflᵛ {A = ℕ} [Γ]₃ [ℕ]
          [0≡0] = reflᵗᵛ {A = ℕ} {zero} [Γ]₃ [ℕ] [0]
          [F≡F′]′ = S.irrelevanceEq {A = F} {B = F′}
                                    [Γ] ([Γ]₃ ∙ [ℕ]) [F] [F]′ [F≡F′]
          [F≡F′]″ = S.irrelevanceEq {A = F} {B = F′}
                                    [Γ] ([Γ]₃ ∙ ℕᵛ [Γ]₃) [F] [F]″ [F≡F′]
          [F₀≡F′₀] = substSEq {F = ℕ} {ℕ} {F} {F′} {zero} {zero}
                              [Γ]₃ [ℕ] [ℕ] [ℕ≡ℕ]
                              [F]′ [F′]′ [F≡F′]′ [0] [0] [0≡0]
          [F₀≡F′₀]′ = S.irrelevanceEq {A = F [ zero ]₀} {B = F′ [ zero ]₀}
                                      [Γ]₃ [Γ]₃ [F₀]″ [F₀]′ [F₀≡F′₀]
          [F₊≡F′₊]″ = subst↑²SEq-suc [Γ]₃ [F]″ [F′]″ [F≡F′]″
          [F₊≡F′₊]′ = S.irrelevanceEq {B = F′ [ suc (var x1) ]↑²}
                                      ([Γ]₃ ∙ ℕᵛ [Γ]₃ ∙ [F]″) ([Γ]₃ ∙ [ℕ] ∙ [F]′)
                                      [F₊]″ [F₊]′ [F₊≡F′₊]″

          [F₊≡F′₊]‴ = subst↑²SEq-suc′ [Γ]₃ [F]″ [F′]″ [F≡F′]″
          [F₊]‴ = subst↑²S-suc′ [Γ]₃ [F′]″ [F]″
          [F₊≡F′₊]⁗ = S.irrelevanceEq {B = F′ [ suc (var x1) ]↑²}
                                      ([Γ]₃ ∙ ℕᵛ [Γ]₃ ∙ [F′]″)
                                      ([Γ]₃ ∙ [ℕ] ∙ [F′]′) [F₊]‴
                                      (S.irrelevanceLift ([Γ]₃ ∙ [ℕ]) [F]′ [F′]′ [F≡F′]′ [F₊]′)
                                      [F₊≡F′₊]‴
          [Fₙ≡F′ₙ′]′ = substSEq {F = ℕ} {ℕ} {F} {F′} {n} {n′}
                                [Γ]₃ [ℕ] [ℕ] [ℕ≡ℕ] [F]′ [F′]′ [F≡F′]′
                                [n] [n′] [n≡n′]
          [z]′ = S.irrelevanceTerm {A = F [ zero ]₀} {t = z}
                                   [Γ]₁ [Γ]₃ [F₀] [F₀]′ [z]
          [z′]′ = convᵛ {t = z′} {F [ zero ]₀} {F′ [ zero ]₀}
                        [Γ]₃ [F₀]′ [F′₀]′ [F₀≡F′₀]′
                        (S.irrelevanceTerm {A = F [ zero ]₀} {t = z′}
                                           [Γ]₁ [Γ]₃ [F₀] [F₀]′ [z′])
          [z≡z′]′ = S.irrelevanceEqTerm {A = F [ zero ]₀} {t = z} {u = z′}
                                        [Γ]₁ [Γ]₃ [F₀] [F₀]′ [z≡z′]
          [s]′ = S.irrelevanceTerm {A = sType} {t = s} [Γ]₂ ([Γ]₃ ∙ [ℕ] ∙ [F]′) [F₊] [F₊]′ [s]
          [s′]′ = S.irrelevanceTerm {A = sType} {t = s′} [Γ]₂
                                    (_∙_ {A = F} (_∙_ {A = ℕ} [Γ]₃ [ℕ]) [F]′)
                                    [F₊] [F₊]′ [s′]
          [s′]″ = S.irrelevanceTermLift {A = sType} {F = F} {H = F′} {t = s′}
                                        (_∙_ {A = ℕ} [Γ]₃ [ℕ]) [F]′ [F′]′ [F≡F′]′ [F₊]′ [s′]′
          [s′]″ = convᵛ {t = s′} {sType} {s′Type} (_∙_ {A = F′} (_∙_ {A = ℕ} [Γ]₃ [ℕ]) [F′]′)
                        (S.irrelevanceLift {A = sType} {F = F} {H = F′} (_∙_ {A = ℕ} [Γ]₃ [ℕ]) [F]′ [F′]′ [F≡F′]′ [F₊]′)
                        [F′₊]′ [F₊≡F′₊]⁗ [s′]″
          [s≡s′]′ = S.irrelevanceEqTerm {A = sType} {t = s} {u = s′}
                                        [Γ]₂ ([Γ]₃ ∙ [ℕ] ∙ [F]′) [F₊] [F₊]′ [s≡s′]
      in  [Γ]₃
      ,   modelsTermEq [Fₙ]′
                       (natrecᵛ {F = F} {z = z} {s = s} {n = n}
                                [Γ]₃ [ℕ] [F]′ [F₀]′ [F₊]′ [Fₙ]′ [z]′ [s]′ [n])
                       (conv₂ᵛ {t = natrec _ _ _ F′ z′ s′ n′} {F [ n ]₀} {F′ [ n′ ]₀}
                               [Γ]₃ [Fₙ]′ [F′ₙ′]′ [Fₙ≡F′ₙ′]′
                               (natrecᵛ {F = F′} {z = z′} {s = s′} {n = n′}
                                        [Γ]₃ [ℕ] [F′]′ [F′₀]′ [F′₊]′ [F′ₙ′]′
                                        [z′]′ [s′]″ [n′]))
                       (natrec-congᵛ {F = F} {F′ = F′} {z = z} {z′ = z′}
                                     {s = s} {s′ = s′} {n = n} {n′ = n′}
                                     [Γ]₃ [ℕ] [F]′ [F′]′ [F≡F′]′
                                     [F₀]′ [F′₀]′ [F₀≡F′₀]′
                                     [F₊]′ [F′₊]′ [F₊≡F′₊]′ [Fₙ]′
                                     [z]′ [z′]′ [z≡z′]′
                                     [s]′ [s′]″ [s≡s′]′ [n] [n′] [n≡n′])
  fundamentalTermEq (natrec-zero ⊢F ⊢z ⊢s)
    with fundamental ⊢F | fundamentalTerm ⊢z | fundamentalTerm ⊢s
  fundamentalTermEq
    (natrec-zero {A = F} {z = z} {s = s} {p = p} {q = q} {r = r}
       ⊢F ⊢z ⊢s)
    | [Γ] , [F] | [Γ]₁ , [F₀] , [z] | [Γ]₂ , [F₊] , [s] =
    let sType = F [ suc (var x1) ]↑²
        [Γ]′ = [Γ]₁
        [ℕ]′ = ℕᵛ {l = ¹} [Γ]′
        [F]′ = S.irrelevance {A = F} [Γ] ([Γ]′ ∙ [ℕ]′) [F]
        [ΓℕF]′ = _∙_ {A = F} (_∙_ {A = ℕ} [Γ]′ [ℕ]′) [F]′
        [F₊]′ = S.irrelevance {A = sType} [Γ]₂ [ΓℕF]′ [F₊]
        [s]′ = S.irrelevanceTerm {A = sType} {t = s} [Γ]₂ [ΓℕF]′ [F₊] [F₊]′ [s]
        d , r =
          redSubstTermᵛ {A = F [ zero ]₀} {natrec p q r F z s zero} {z} [Γ]′
            (λ {_} {Δ} {σ} ⊢Δ [σ] →
               let ⊢ℕ = escape (proj₁ (unwrap [ℕ]′ ⊢Δ [σ]))
                   ⊢F = escape (proj₁ (unwrap [F]′ (⊢Δ ∙ ⊢ℕ)
                                               (liftSubstS {F = ℕ}
                                                           [Γ]′ ⊢Δ [ℕ]′ [σ])))
                   ⊢z = PE.subst (λ x → Δ ⊢ z [ σ ] ∷ x)
                                 (singleSubstLift F zero)
                                 (escapeTerm (proj₁ (unwrap [F₀] ⊢Δ [σ]))
                                                (proj₁ ([z] ⊢Δ [σ])))
                   ⊢Δℕ = ⊢Δ ∙ ℕⱼ ⊢Δ
                   [σ⇑⇑] = liftSubstS {F = F} (_∙_ {A = ℕ} [Γ]′ [ℕ]′) ⊢Δℕ [F]′
                                      (liftSubstS {F = ℕ} [Γ]′ ⊢Δ [ℕ]′ [σ])
                   ⊢s = PE.subst (λ x → Δ ∙ ℕ ∙ F [ liftSubst σ ] ⊢ s [ liftSubstn σ 2 ] ∷ x)
                                 (natrecSucCase σ F)
                                 (escapeTerm (proj₁ (unwrap [F₊]′ (⊢Δℕ ∙ ⊢F) [σ⇑⇑]))
                                             (proj₁ ([s]′ (⊢Δℕ ∙ ⊢F) [σ⇑⇑])))
               in PE.subst (λ x → Δ ⊢ natrec p q r F z s zero [ σ ]
                                    ⇒ z [ σ ] ∷ x)
                           (PE.sym (singleSubstLift F zero))
                           (natrec-zero ⊢F ⊢z ⊢s))
                        [F₀] [z]
    in  [Γ]′ , modelsTermEq [F₀] d [z] r
  fundamentalTermEq
    {Γ = Γ}
    (natrec-suc {A = F} {z = z} {s = s} {p = p} {q = q} {r = r} {n = n}
       ⊢F ⊢z ⊢s ⊢n)
    with fundamentalTerm ⊢n | fundamental ⊢F
       | fundamentalTerm ⊢z | fundamentalTerm ⊢s
  ... | [Γ] , [ℕ] , [n] | [Γ]₁ , [F] | [Γ]₂ , [F₀] , [z] | [Γ]₃ , [F₊] , [s] =
    let [sucn] = sucᵛ {n = n} [Γ] [ℕ] [n]
        [F₀]′ = S.irrelevance {A = F [ zero ]₀} [Γ]₂ [Γ] [F₀]
        [z]′ = S.irrelevanceTerm {A = F [ zero ]₀} {t = z}
                                 [Γ]₂ [Γ] [F₀] [F₀]′ [z]
        [F]′ = S.irrelevance {A = F} [Γ]₁ ([Γ] ∙ [ℕ]) [F]
        [F[sucn]] = substS {F = ℕ} {F} {suc n} [Γ] [ℕ] [F]′ [sucn]
        [Fₙ]′ = substS {F = ℕ} {F} {n} [Γ] [ℕ] [F]′ [n]
        [ΓℕF] = _∙_ {A = F} (_∙_ {A = ℕ} [Γ] [ℕ]) [F]′
        [F₊]′ = S.irrelevance {A = F [ suc (var x1) ]↑²} [Γ]₃ [ΓℕF] [F₊]
        [s]′ = S.irrelevanceTerm {A = F [ suc (var x1) ]↑²} {t = s} [Γ]₃ [ΓℕF] [F₊] [F₊]′ [s]
        [natrecₙ] = natrecᵛ {p = p} {r = r} {F = F} {z} {s} {n}
                            [Γ] [ℕ] [F]′ [F₀]′ [F₊]′ [Fₙ]′ [z]′ [s]′ [n]
        [s₊] : Γ ⊩ᵛ⟨ ¹ ⟩ s [ n ,, natrec p q r F z s n ] ∷ F [ suc n ]₀ / [Γ] / [F[sucn]]
        [s₊] = (λ {k : Nat} {Δ : Con Term k} {σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ) →
                            let [σn] = proj₁ ([n] ⊢Δ [σ])
                                [σnatrecₙ] = proj₁ ([natrecₙ] ⊢Δ [σ])
                                [σFₙ] = proj₁ (unwrap [Fₙ]′ ⊢Δ [σ])
                                [σFₙ]′ = irrelevance′ {A′ = F [ consSubst σ (n [ σ ]) ]}
                                                      (PE.trans (singleSubstLift F n) (singleSubstComp (n [ σ ]) σ F)) [σFₙ]
                                [σnatrecₙ]′ = irrelevanceTerm′ (PE.trans (singleSubstLift F n) (singleSubstComp (n [ σ ]) σ F))
                                                               [σFₙ] (proj₁ (unwrap [F]′ ⊢Δ ([σ] , [σn]))) [σnatrecₙ]
                                [σ₊] = ([σ] , [σn]) , [σnatrecₙ]′
                                [σ₊s] = proj₁ ([s]′ {σ = consSubst (consSubst σ (n [ σ ])) (natrec p q r F z s n [ σ ])} ⊢Δ [σ₊])
                                [σ₊s]′ = irrelevanceTerm″ (PE.trans (sucCaseSubstEq F) (PE.sym (singleSubstLift F (suc n))))
                                                          (PE.trans (substVar-to-subst (λ { x0 → PE.refl
                                                                                          ; (x0 +1) → PE.refl
                                                                                          ; (x +1 +1) → PE.refl})
                                                                                       s)
                                                                    (PE.sym (substCompEq {σ′ = consSubst (sgSubst n) (natrec p q r F z s n)} {σ = σ} s)))
                                                          (proj₁ (unwrap [F₊] ⊢Δ (S.irrelevanceSubst ([Γ] ∙ [ℕ] ∙ [F]′) [Γ]₃ ⊢Δ ⊢Δ [σ₊])))
                                                          (proj₁ (unwrap [F[sucn]] ⊢Δ [σ])) [σ₊s]
                            in  [σ₊s]′ , (λ {σ′} [σ′] [σ≡σ′] →
                                let
                                    [σ′n] = proj₁ ([n] ⊢Δ [σ′])
                                    [σ′natrecₙ] = proj₁ ([natrecₙ] ⊢Δ [σ′])
                                    [σ′natrecₙ]′ = irrelevanceTerm′ (PE.trans (singleSubstLift F n) (singleSubstComp (n [ σ′ ]) σ′ F))
                                                                    (proj₁ (unwrap (substS {F = ℕ} {G = F} {t = n} [Γ] [ℕ] [F]′ [n]) ⊢Δ [σ′]))
                                                                    (proj₁ (unwrap  [F]′ ⊢Δ ([σ′] , proj₁ ([n] ⊢Δ [σ′])))) [σ′natrecₙ]
                                    [σ′₊] = ([σ′] , [σ′n]) , [σ′natrecₙ]′
                                    [σnr≡σ′nr] = proj₂ ([natrecₙ] ⊢Δ [σ]) [σ′] [σ≡σ′]
                                    [σ₊s≡σ′₊s] = proj₂ ([s]′ {σ = consSubst (consSubst σ (n [ σ ])) (natrec p q r F z s n [ σ ])}
                                                             ⊢Δ [σ₊])
                                                       {σ′ = consSubst (consSubst σ′ (n [ σ′ ])) (natrec p q r F z s n [ σ′ ])}
                                                       [σ′₊] (([σ≡σ′] , (proj₂ ([n] ⊢Δ [σ]) [σ′] [σ≡σ′])) ,
                                                             irrelevanceEqTerm′ (PE.trans (singleSubstLift F n) (singleSubstComp (n [ σ ]) σ F))
                                                                                (proj₁ (unwrap [Fₙ]′ ⊢Δ [σ])) (proj₁ (unwrap [F]′ ⊢Δ ([σ] , proj₁ ([n] ⊢Δ [σ]))))
                                                                                [σnr≡σ′nr])
                                in  irrelevanceEqTerm″ (PE.trans (substVar-to-subst (λ { x0 → PE.refl
                                                                                       ; (x0 +1) → PE.refl
                                                                                       ; (x +1 +1) → PE.refl}) s)
                                                                 (PE.sym (substCompEq s)))
                                                       (PE.trans (substVar-to-subst (λ { x0 → PE.refl
                                                                                       ; (x0 +1) → PE.refl
                                                                                       ; (x +1 +1) → PE.refl}) s)
                                                                 (PE.sym (substCompEq s)))
                                                       (PE.trans (sucCaseSubstEq F) (PE.sym (singleSubstLift F (suc n))))
                                                       (proj₁ (unwrap [F₊]′ ⊢Δ (([σ] , proj₁ ([n] ⊢Δ [σ]))
                                                                              , irrelevanceTerm′ (PE.trans (singleSubstLift F n)
                                                                                                           (singleSubstComp (n [ σ ]) σ F))
                                                                                                 (proj₁ (unwrap [Fₙ]′ ⊢Δ [σ])) (proj₁ (unwrap [F]′ ⊢Δ ([σ] , proj₁ ([n] ⊢Δ [σ]))))
                                                                                                 [σnatrecₙ])))
                                                                                                 (proj₁ (unwrap [F[sucn]] ⊢Δ [σ])) [σ₊s≡σ′₊s]))
        [natrecₛₙ] , [nr≡s₊] =
          redSubstTermᵛ {A = F [ suc n ]₀} {natrec p q r F z s (suc n)}
            {s [ n ,, natrec p q r F z s n ]}
            [Γ]
            (λ {k Δ σ} ⊢Δ [σ] →
              let [σℕ] = proj₁ (unwrap [ℕ] ⊢Δ [σ])
                  ⊢ℕ = escape [σℕ]
                  [σn] = proj₁ ([n] ⊢Δ [σ])
                  [σF] = proj₁ $
                         unwrap [F]′ {σ = liftSubst σ} (⊢Δ ∙ ⊢ℕ)
                           (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ])
                  ⊢F = escape [σF]
                  [σF₀] = proj₁ (unwrap [F₀]′ ⊢Δ [σ])
                  [σF₀]′ = irrelevance′ (singleSubstLift F zero) [σF₀]
                  [σ⇑⇑] = liftSubstS
                            {F = F} (_∙_ {A = ℕ} [Γ] [ℕ]) (⊢Δ ∙ ⊢ℕ) [F]′
                            (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ])
                  [σF₊] = proj₁ $
                          unwrap [F₊]′ {σ = liftSubstn σ 2}
                            (⊢Δ ∙ ⊢ℕ ∙ ⊢F) [σ⇑⇑]
                  [σF₊]′ = irrelevance′ (natrecSucCase σ F) [σF₊]
                  [σz] = proj₁ ([z]′ ⊢Δ [σ])
                  [σz]′ = irrelevanceTerm′ (singleSubstLift F zero)
                            [σF₀] [σF₀]′ [σz]

                  [σs] = proj₁ $
                         [s]′ {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢ℕ ∙ ⊢F) [σ⇑⇑]
                  [σs]′ = irrelevanceTerm′ (natrecSucCase σ F)
                            [σF₊] [σF₊]′ [σs]
                  ⊢n = escapeTerm [σℕ] [σn]
                  ⊢F = escape [σF]
                  ⊢z = escapeTerm [σF₀]′ [σz]′
                  ⊢s = escapeTerm [σF₊]′ [σs]′
                  red = natrec-suc {p = p} {r = r} ⊢F ⊢z ⊢s ⊢n
              in  PE.subst₂
                    (Δ ⊢ natrec p q r F z s (suc n) [ σ ] ⇒_∷_)
                    (PE.trans
                       (doubleSubstComp s (n [ σ ])
                          (natrec p q r F z s n [ σ ]) σ)
                       (PE.trans
                          (substVar-to-subst
                             (λ { x0        → PE.refl
                                ; (x0 +1)   → PE.refl
                                ; (x +1 +1) → PE.refl
                                })
                             s)
                          (PE.sym (substCompEq s))))
                    (PE.sym (singleSubstLift F (suc n)))
                    red)
            [F[sucn]] [s₊]

    in  [Γ] , modelsTermEq [F[sucn]] [natrecₛₙ] [s₊] [nr≡s₊]
  fundamentalTermEq (emptyrec-cong F≡F′ n≡n′)
    with fundamentalEq F≡F′ |
         fundamentalTermEq n≡n′
  fundamentalTermEq (emptyrec-cong {A = F} {B = F′} {t = n} {u = n′}
                                 F≡F′ n≡n′) |
    [Γ]  , [F] , [F′] , [F≡F′] |
    [Γ]′ , modelsTermEq [Empty] [n] [n′] [n≡n′] =
    let [F]′ = S.irrelevance {A = F} [Γ] [Γ]′ [F]
        [F′]′ = S.irrelevance {A = F′} [Γ] [Γ]′ [F′]
        [F≡F′]′ = S.irrelevanceEq {A = F} {B = F′} [Γ] [Γ]′ [F] [F]′ [F≡F′]
    in [Γ]′
      , modelsTermEq [F]′ (emptyrecᵛ {F = F} {n} [Γ]′ [Empty] [F]′ [n])
                     (conv₂ᵛ {t = emptyrec _ F′ n′} {F} {F′} [Γ]′ [F]′ [F′]′ [F≡F′]′
                       (emptyrecᵛ {F = F′} {n′} [Γ]′ [Empty] [F′]′ [n′]))
                     (emptyrec-congᵛ {F = F} {F′} {n} {n′}
                       [Γ]′ [Empty] [F]′ [F′]′ [F≡F′]′
                       [n] [n′] [n≡n′])
  fundamentalTermEq (η-unit {t = e} {t′ = e'} ⊢e ⊢e')
    with fundamentalTerm ⊢e | fundamentalTerm ⊢e'
  ... | [Γ] , [Unit] , [e] | [Γ]' , [Unit]' , [e'] =
    let [e'] = S.irrelevanceTerm {A = Unitˢ} {t = e'} [Γ]' [Γ] [Unit]' [Unit] [e']
    in  [Γ] , modelsTermEq [Unit] [e] [e'] (η-unitᵛ {e = e} {e' = e'} [Γ] [Unit] [e] [e'])
  fundamentalTermEq (fst-cong {F = F} {G} {t = t} {t′} ⊢F ⊢G t≡t′)
    with fundamentalTermEq t≡t′ | fundamental ⊢F | fundamental ⊢G
  ... | [Γ] , modelsTermEq [ΣFG] [t] [t′] [t≡t′] | [Γ]₁ , [F]₁ | [Γ]₂ , [G]₂ =
    let ok = ⊩ᵛΠΣ→ΠΣ-allowed [ΣFG]
        [F] = S.irrelevance {A = F} [Γ]₁ [Γ] [F]₁
        [G] = S.irrelevance {A = G} [Γ]₂ ([Γ] ∙ [F]) [G]₂

        [t]′ = S.irrelevanceTerm {A = Σ _ , _ ▷ F ▹ G} {t = t} [Γ] [Γ]
                                 [ΣFG] (Σᵛ {F = F} {G} [Γ] [F] [G] ok)
                                 [t]
        [t′]′ = S.irrelevanceTerm {A = Σ _ , _ ▷ F ▹ G} {t = t′} [Γ] [Γ]
                                  [ΣFG] (Σᵛ {F = F} {G} [Γ] [F] [G] ok)
                                  [t′]
        [t≡t′]′ = S.irrelevanceEqTerm
                    {A = Σ _ , _ ▷ F ▹ G} {t = t} {u = t′} [Γ] [Γ]
                    [ΣFG] (Σᵛ {F = F} {G} [Γ] [F] [G] ok)
                    [t≡t′]

        [fstt] = fstᵛ {F = F} {G} {t} [Γ] [F] [G] ok [t]′
        [fstt′] = fstᵛ {F = F} {G} {t′} [Γ] [F] [G] ok [t′]′
        [fst≡] = fst-congᵛ {F = F} {G} {t} {t′}
                   [Γ] [F] [G] ok [t]′ [t′]′ [t≡t′]′
    in  [Γ] , modelsTermEq [F] [fstt] [fstt′] [fst≡]
  fundamentalTermEq
    {Γ = Γ} (snd-cong {F} {G} {t} {u = t′} ⊢F ⊢G t≡t′)
    with fundamentalTermEq t≡t′ | fundamental ⊢F | fundamental ⊢G
  ... | [Γ] , modelsTermEq [ΣFG] [t] [t′] [t≡t′] | [Γ]₁ , [F]₁ | [Γ]₂ , [G]₂ =
    let ok = ⊩ᵛΠΣ→ΠΣ-allowed [ΣFG]
        [F] = S.irrelevance {A = F} [Γ]₁ [Γ] [F]₁
        [G] = S.irrelevance {A = G} [Γ]₂ ([Γ] ∙ [F]) [G]₂

        [t]Σ = S.irrelevanceTerm {A = Σ _ , _ ▷ F ▹ G} {t = t} [Γ] [Γ]
                                 [ΣFG] (Σᵛ {F = F} {G} [Γ] [F] [G] ok)
                                 [t]
        [t′]Σ = S.irrelevanceTerm {A = Σ _ , _ ▷ F ▹ G} {t = t′} [Γ] [Γ]
                                  [ΣFG] (Σᵛ {F = F} {G} [Γ] [F] [G] ok)
                                  [t′]
        [t≡t′]Σ = S.irrelevanceEqTerm
                    {A = Σ _ , _ ▷ F ▹ G} {t = t} {u = t′} [Γ] [Γ]
                    [ΣFG] (Σᵛ {F = F} {G} [Γ] [F] [G] ok)
                    [t≡t′]

        [fst] = fstᵛ {F = F} {G} {t} [Γ] [F] [G] ok [t]Σ
        [fst′] = fstᵛ {F = F} {G} {t′} [Γ] [F] [G] ok [t′]Σ
        [fst≡] = fst-congᵛ {F = F} {G} {t} {t′}
                   [Γ] [F] [G] ok [t]Σ [t′]Σ [t≡t′]Σ
        [Gfst] = substS {F = F} {G} [Γ] [F] [G] [fst]
        [Gfst′] = substS {F = F} {G} [Γ] [F] [G] [fst′]
        [Gfst≡] = substSEq {F = F} {F′ = F} {G = G} {G′ = G}
                           {t = fst _ t} {t′ = fst _ t′} [Γ]
                           [F] [F] (reflᵛ {A = F} [Γ] [F])
                           [G] [G] (reflᵛ {Γ = Γ ∙ F} {A = G} ([Γ] ∙ [F]) [G])
                           [fst] [fst′] [fst≡]
        [snd] = sndᵛ {F = F} {G} {t} [Γ] [F] [G] ok [t]Σ
        [snd′]fst′ = sndᵛ {F = F} {G} {t′} [Γ] [F] [G] ok [t′]Σ
        [snd′]fst = conv₂ᵛ {t = snd _ t′}
                           {A = G [ fst _ t ]₀} {B = G [ fst _ t′ ]₀}
                           [Γ] [Gfst] [Gfst′] [Gfst≡] [snd′]fst′
        [snd≡] = snd-congᵛ {F = F} {G} {t} {t′}
                   [Γ] [F] [G] ok [t]Σ [t′]Σ [t≡t′]Σ
    in  [Γ] , modelsTermEq [Gfst] [snd] [snd′]fst [snd≡]
  fundamentalTermEq
    {Γ = Γ} (prod-cong {F = F} {G} {t} {t′} {u} {u′} ⊢F ⊢G t≡t′ u≡u′ ok)
    with fundamental ⊢F | fundamental ⊢G |
         fundamentalTermEq t≡t′ | fundamentalTermEq u≡u′
  ... | [Γ] , [F] | [Γ]₂ , [G]₂
      | [Γ]₃ , modelsTermEq [F]₃ [t]₃ [t′]₃ [t≡t′]₃
      | [Γ]₄ , modelsTermEq [Gt]₄ [u]₄ [u′]₄ [u≡u′]₄ =
    let [G] = S.irrelevance {A = G} [Γ]₂ ([Γ] ∙ [F]) [G]₂
        [Σ] = Σᵛ {F = F} {G} [Γ] [F] [G] ok
        [t] = S.irrelevanceTerm {A = F} {t = t} [Γ]₃ [Γ] [F]₃ [F] [t]₃
        [t′] = S.irrelevanceTerm {A = F} {t = t′} [Γ]₃ [Γ] [F]₃ [F] [t′]₃
        [t≡t′] = S.irrelevanceEqTerm {A = F} {t = t} {u = t′} [Γ]₃ [Γ] [F]₃ [F] [t≡t′]₃
        [Gt] = substS {F = F} {G = G} {t = t} [Γ] [F] [G] [t]
        [Gt′] = substS {F = F} {G = G} {t = t′} [Γ] [F] [G] [t′]
        [u] = S.irrelevanceTerm {A = G [ t ]₀} {t = u} [Γ]₄ [Γ] [Gt]₄ [Gt] [u]₄
        [u′] = S.irrelevanceTerm {A = G [ t ]₀} {t = u′} [Γ]₄ [Γ] [Gt]₄ [Gt] [u′]₄
        [u≡u′] = S.irrelevanceEqTerm {A = G [ t ]₀} {t = u} {u = u′} [Γ]₄ [Γ] [Gt]₄ [Gt] [u≡u′]₄

        [prod] = prodᵛ {F = F} {G} {t} {u} [Γ] [F] [G] [t] [u] ok
        [Gt≡Gt′] = substSEq {F = F} {F} {G} {G} {t} {t′}
                            [Γ] [F] [F] (reflᵛ {A = F} [Γ] [F])
                            [G] [G] (reflᵛ {A = G} (_∙_ {A = F} [Γ] [F]) [G])
                            [t] [t′] [t≡t′]
        [u′]′ = convᵛ {t = u′} {A = G [ t ]₀} {B = G [ t′ ]₀} [Γ] [Gt] [Gt′] [Gt≡Gt′] [u′]
        [prod′] = prodᵛ {F = F} {G} {t′} {u′} [Γ] [F] [G] [t′] [u′]′ ok
        [prod≡] = prod-congᵛ {F = F} {G} {t} {t′} {u} {u′}
                    [Γ] [F] [G] [t] [t′] [t≡t′] [u] [u′]′ [u≡u′] ok
    in  [Γ] , modelsTermEq [Σ] [prod] [prod′] [prod≡]
  fundamentalTermEq
    (Σ-β₁ {F = F} {G} {t} {u} {p = p} ⊢F ⊢G ⊢t ⊢u PE.refl ok)
    with fundamentalTerm ⊢t | fundamental ⊢G | fundamentalTerm ⊢u
  ... | [Γ] , [F] , [t] | [Γ]₁ , [G]₁ | [Γ]₂ , [Gt]₂ , [u]₂ =
    let [G] = S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]₁
        [u] = S.irrelevanceTerm {A = G [ t ]₀} {t = u} [Γ]₂ [Γ]
                                [Gt]₂ (substS {F = F} {G} [Γ] [F] [G] [t])
                                [u]₂

        [prod] = prodᵛ {F = F} {G} {t} {u} [Γ] [F] [G] [t] [u] ok
        [fst] = fstᵛ {F = F} {G} {prod! t u} [Γ] [F] [G] ok [prod]
        [fst≡t] = Σ-β₁ᵛ {F = F} {G} {t} {u} [Γ] [F] [G] [t] [u] ok
    in  [Γ] , modelsTermEq [F] [fst] [t] [fst≡t]
  fundamentalTermEq
    {Γ = Γ} (Σ-β₂ {F = F} {G} {t} {u} {p = p} ⊢F ⊢G ⊢t ⊢u PE.refl ok)
    with fundamentalTerm ⊢t | fundamental ⊢G | fundamentalTerm ⊢u
  ... | [Γ] , [F] , [t] | [Γ]₁ , [G]₁ | [Γ]₂ , [Gt]₂ , [u]₂ =
    let [G] = S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]₁
        [Gt] = substS {F = F} {G} [Γ] [F] [G] [t]
        [u] = S.irrelevanceTerm {A = G [ t ]₀} {t = u} [Γ]₂ [Γ]
                                [Gt]₂ [Gt]
                                [u]₂

        [prod] = prodᵛ {F = F} {G} {t} {u} [Γ] [F] [G] [t] [u] ok
        [fst] = fstᵛ {F = F} {G} {prod! t u} [Γ] [F] [G] ok [prod]
        [fst≡t] = Σ-β₁ᵛ {F = F} {G} {t} {u} [Γ] [F] [G] [t] [u] ok

        [Gfst≡Gt] = substSEq {F = F} {F′ = F} {G = G} {G′ = G}
                             {t = fst _ (prodˢ _ t u)} {t′ = t} [Γ]
                             [F] [F] (reflᵛ {A = F} [Γ] [F])
                             [G] [G] (reflᵛ {Γ = Γ ∙ F} {A = G} ([Γ] ∙ [F]) [G])
                             [fst] [t] [fst≡t]

        [Gfst] = substS {F = F} {G} [Γ] [F] [G] [fst]
        [snd] = sndᵛ {F = F} {G} {prod! t u} [Γ] [F] [G] ok [prod]
        [snd≡u] = Σ-β₂ᵛ {F = F} {G} {t} {u} [Γ] [F] [G] [t] [u] ok

        [u]fst = conv₂ᵛ {t = u}
                        {A = G [ fst _ (prodˢ _ t u) ]₀} {B = G [ t ]₀}
                        [Γ] [Gfst] [Gt] [Gfst≡Gt] [u]
    in  [Γ] , modelsTermEq [Gfst] [snd] [u]fst [snd≡u]
  fundamentalTermEq
    (Σ-η {F = F} {G} {t = p} {u = r} ⊢F ⊢G ⊢p ⊢r fst≡ snd≡)
    with fundamentalTerm ⊢p | fundamentalTerm ⊢r |
         fundamental ⊢F | fundamental ⊢G |
         fundamentalTermEq fst≡ | fundamentalTermEq snd≡
  ... | [Γ] , [ΣFG]₀ , [p]₀ | [Γ]₁ , [ΣFG]₁ , [r]₁
      | [Γ]₂ , [F]₂ | [Γ]₃ , [G]₃
      | [Γ]₄ , modelsTermEq [F]₄ [fstp]₄ [fstr]₄ [fst≡]₄
      | [Γ]₅ , modelsTermEq [Gfstp]₅ [sndp]₅ [sndr]₅ [snd≡]₅ =
    let ok = ⊩ᵛΠΣ→ΠΣ-allowed [ΣFG]₀
        [F] = S.irrelevance {A = F} [Γ]₂ [Γ] [F]₂
        [G] = S.irrelevance {A = G} [Γ]₃ ([Γ] ∙ [F]) [G]₃
        [ΣFG] = Σᵛ {F = F} {G} [Γ] [F] [G] ok
        [p] = S.irrelevanceTerm {A = Σ _ , _ ▷ F ▹ G} {t = p} [Γ] [Γ]
                                [ΣFG]₀ [ΣFG]
                                [p]₀
        [r] = S.irrelevanceTerm {A = Σ _ , _ ▷ F ▹ G} {t = r} [Γ]₁ [Γ]
                                [ΣFG]₁ [ΣFG]
                                [r]₁

        [fst≡] = S.irrelevanceEqTerm
                   {A = F} {t = fst _ p} {u = fst _ r} [Γ]₄ [Γ]
                   [F]₄ [F]
                   [fst≡]₄

        [Gfstp] = substS {F = F} {G} [Γ] [F] [G]
                    (fstᵛ {F = F} {G} {p} [Γ] [F] [G] ok [p])
        [snd≡] = S.irrelevanceEqTerm
                  {A = G [ fst _ p ]₀}
                  {t = snd _ p} {u = snd _ r} [Γ]₅ [Γ]
                  [Gfstp]₅ [Gfstp]
                  [snd≡]₅

        [p≡r] = Σ-ηᵛ {F = F} {G} {p} {r}
                     [Γ] [F] [G] ok [p] [r] [fst≡] [snd≡]
    in  [Γ] , modelsTermEq [ΣFG] [p] [r] [p≡r]
  fundamentalTermEq
    (prodrec-cong
       {F = F} {G} {q′ = q} {A} {A′} {t = t} {t′} {u} {u′} {r = r}
       ⊢F ⊢G ⊢A≡A′ ⊢t≡t′ ⊢u≡u′ ok)
    with fundamental ⊢F | fundamental ⊢G | fundamentalEq ⊢A≡A′ |
         fundamentalTermEq ⊢t≡t′ | fundamentalTermEq ⊢u≡u′
  ... | [Γ] , [F] | [Γ]₁ , [G] | [Γ]₂ , [A] , [A′] , [A≡A′]
      | [Γ]₃ , modelsTermEq [Σ] [t] [t′] [t≡t′]
      | [Γ]₄ , modelsTermEq [A₊] [u] [u′] [u≡u′] =
    let [G]′ = S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]
        [Σ]′ = S.irrelevance {A = Σ _ , q ▷ F ▹ G} [Γ]₃ [Γ] [Σ]
        [A]′ = S.irrelevance {A = A} [Γ]₂ ([Γ] ∙ [Σ]′) [A]
        [A′]′ = S.irrelevance {A = A′} [Γ]₂ ([Γ] ∙ [Σ]′) [A′]
        [A≡A′]′ = S.irrelevanceEq {A = A} {B = A′} [Γ]₂ ([Γ] ∙ [Σ]′) [A] [A]′ [A≡A′]
        [t]′ = S.irrelevanceTerm {A = Σ _ , q ▷ F ▹ G} {t = t}
                 [Γ]₃ [Γ] [Σ] [Σ]′ [t]
        [t′]′ = S.irrelevanceTerm {A = Σ _ , q ▷ F ▹ G} {t = t′}
                  [Γ]₃ [Γ] [Σ] [Σ]′ [t′]
        [t≡t′]′ = S.irrelevanceEqTerm
                    {A = Σ _ , q ▷ F ▹ G} {t = t} {u = t′}
                    [Γ]₃ [Γ] [Σ] [Σ]′ [t≡t′]
        A₊ = A [ prod! (var (x0 +1)) (var x0) ]↑²
        A′₊ = A′ [ prod! (var (x0 +1)) (var x0) ]↑²
        [A₊]′ = S.irrelevance {A = A₊} [Γ]₄ ([Γ] ∙ [F] ∙ [G]′) [A₊]
        [A′₊] = subst↑²S-prod {F = F} {G} {A′} [Γ] [F] [G]′ [Σ]′ [A′]′ ok
        [A₊≡A′₊] = subst↑²SEq-prod {F = F} {G} {A} {A′} [Γ] [F] [G]′ [Σ]′
                     [A]′ [A′]′ [A≡A′]′ [A₊]′ ok
        [u]′ = S.irrelevanceTerm {A = A₊} {t = u} [Γ]₄ ([Γ] ∙ [F] ∙ [G]′) [A₊] [A₊]′ [u]
        [u′]′ = S.irrelevanceTerm {A = A₊} {t = u′} [Γ]₄ ([Γ] ∙ [F] ∙ [G]′) [A₊] [A₊]′ [u′]
        [u′]″ = convᵛ {t = u′} {A₊} {A′₊} (_∙_ {A = G} (_∙_ {A = F} [Γ] [F]) [G]′) [A₊]′ [A′₊] [A₊≡A′₊] [u′]′
        [u≡u′]′ = S.irrelevanceEqTerm {A = A₊} {t = u} {u = u′} [Γ]₄ ([Γ] ∙ [F] ∙ [G]′) [A₊] [A₊]′ [u≡u′]
        [Aₜ] = substS {F = Σ _ , q ▷ F ▹ G} {A} {t} [Γ] [Σ]′ [A]′ [t]′
        [A′ₜ′] = substS {F = Σ _ , q ▷ F ▹ G} {A′} {t′}
                  [Γ] [Σ]′ [A′]′ [t′]′
        [pr] = prodrecᵛ {q = q} {r = r} {F = F} {G} {A} {t} {u}
                 [Γ] [F] [G]′ [Σ]′ [A]′ [A₊]′ [Aₜ] [t]′ [u]′
        [pr′] = prodrecᵛ {q = q} {r = r} {F = F} {G} {A′} {t′} {u′}
                  [Γ] [F] [G]′ [Σ]′ [A′]′ [A′₊] [A′ₜ′] [t′]′ [u′]″
        [Aₜ≡A′ₜ′] = substSEq
          {F = Σ _ , q ▷ F ▹ G} {Σ _ , q ▷ F ▹ G} {A} {A′} {t} {t′}
          [Γ] [Σ]′ [Σ]′ (reflᵛ {A = Σ _ , q ▷ F ▹ G} [Γ] [Σ]′)
          [A]′ [A′]′ [A≡A′]′ [t]′ [t′]′ [t≡t′]′
        [pr′]′ = conv₂ᵛ
          {t = prodrec _ _ _ A′ t′ u′} {A = A [ t ]₀} {B = A′ [ t′ ]₀}
          [Γ] [Aₜ] [A′ₜ′] [Aₜ≡A′ₜ′] [pr′]
        [F≡F] = reflᵛ {A = F} [Γ] [F]
        [G≡G] = reflᵛ {A = G} (_∙_ {A = F} [Γ] [F]) [G]′
        [Σ≡Σ]′ = reflᵛ {A = Σ _ , q ▷ F ▹ G} [Γ] [Σ]′
        [pr≡pr′] = prodrec-congᵛ
          {r = r} {F = F} {F} {G} {G} {A} {A′} {t} {t′} {u} {u′}
          [Γ] [F] [F] [F≡F] [G]′ [G]′ [G≡G] [Σ]′ [Σ]′ [Σ≡Σ]′
          [A]′ [A′]′ [A≡A′]′ [A₊]′ [A′₊] [A₊≡A′₊]
          [Aₜ] [t]′ [t′]′ [t≡t′]′ [u]′ [u′]″ [u≡u′]′
    in  [Γ] , modelsTermEq [Aₜ] [pr] [pr′]′ [pr≡pr′]
  fundamentalTermEq
    (prodrec-β {F = F} {G} {q′ = q} {A} {t = t} {t′} {u} {r = r}
       ⊢F ⊢G ⊢A ⊢t ⊢t′ ⊢u PE.refl ok)
    with fundamental ⊢F | fundamental ⊢G | fundamental ⊢A |
         fundamentalTerm ⊢t | fundamentalTerm ⊢t′ |
         fundamentalTerm ⊢u
  ... | [Γ] , [F] | [Γ]₁ , [G]₁ | [Γ]₂ , [A]₂
      | [Γ]₃ , [F]₃ , [t]₃ | [Γ]₄ , [G[t]]₄ , [t′]₄
      | [Γ]₅ , [A₊]₅ , [u]₅ =
    let [G] = S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]₁
        [Σ] = Σᵛ {F = F} {G} [Γ] [F] [G] ok
        [A] = S.irrelevance {A = A} [Γ]₂ ([Γ] ∙ [Σ]) [A]₂
        [t] = S.irrelevanceTerm {A = F} {t = t} [Γ]₃ [Γ] [F]₃ [F] [t]₃
        [G[t]] = substS {F = F} {G} {t} [Γ] [F] [G] [t]
        [t′] = S.irrelevanceTerm {A = G [ t ]₀} {t = t′} [Γ]₄ [Γ] [G[t]]₄ [G[t]] [t′]₄
        A₊ = A [ prod! (var (x0 +1)) (var x0) ]↑²
        [ΓF] = _∙_ {A = F} [Γ] [F]
        [ΓFG] = _∙_ {A = G} [ΓF] [G]
        [A₊] = S.irrelevance {A = A₊} [Γ]₅ [ΓFG] [A₊]₅
        [u] = S.irrelevanceTerm {A = A₊} {t = u} [Γ]₅ [ΓFG] [A₊]₅ [A₊] [u]₅

        [p] = prodᵛ {F = F} {G} {t} {t′} [Γ] [F] [G] [t] [t′] ok
        [A[p]] = substS {F = Σ _ , _ ▷ F ▹ G} {A} {prod! t t′}
                   [Γ] [Σ] [A] [p]
        [pr] = prodrecᵛ {F = F} {G} {A} {prod! t t′} {u}
                 [Γ] [F] [G] [Σ] [A] [A₊] [A[p]] [p] [u]
        [u₊] = subst↑²STerm {F = F} {G} {A} {t} {t′} {u} [Γ] [F] [G] [Σ] [A] [A₊] [A[p]] [t] [t′] [u]

    in  [Γ] , modelsTermEq [A[p]] [pr] [u₊] λ {_} {Δ} {σ} ⊢Δ [σ] →
      let [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
          ⊢σF = escape [σF]
          [⇑σ] = liftSubstS {σ = σ} {F = F} [Γ] ⊢Δ [F] [σ]
          [σG] = proj₁ (unwrap [G] {σ = liftSubst σ} (⊢Δ ∙ ⊢σF) [⇑σ])
          ⊢σG = escape [σG]
          [σt] = proj₁ ([t] ⊢Δ [σ])
          ⊢σt = escapeTerm [σF] [σt]
          [σt′] = proj₁ ([t′] ⊢Δ [σ])
          [σG[t]] = proj₁ (unwrap [G[t]] ⊢Δ [σ])
          ⊢σt′ = PE.subst (λ x → Δ ⊢ t′ [ σ ] ∷ x) (singleSubstLift G t) (escapeTerm [σG[t]] [σt′])
          [⇑σ]′ = liftSubstS {σ = σ} {F = Σ _ , q ▷ F ▹ G}
                    [Γ] ⊢Δ [Σ] [σ]
          [σΣ] = proj₁ (unwrap [Σ] ⊢Δ [σ])
          ⊢σΣ = escape [σΣ]
          [σA] = proj₁ (unwrap [A] {σ = liftSubst σ} (⊢Δ ∙ ⊢σΣ) [⇑σ]′)
          ⊢σA = escape [σA]
          [⇑²σ] = liftSubstS {σ = liftSubst σ} {F = G} [ΓF] (⊢Δ ∙ ⊢σF) [G] [⇑σ]
          [σu] = proj₁ ([u] {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢σF ∙ ⊢σG) [⇑²σ])
          [σA₊] = proj₁ (unwrap [A₊] {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢σF ∙ ⊢σG) [⇑²σ])
          ⊢σu = PE.subst (λ x → Δ ∙ _ ∙ _ ⊢ _ ∷ x) (subst-β-prodrec A σ) (escapeTerm [σA₊] [σu])
          red : Δ ⊢ prodrec r _ _ A (prod! t t′) u [ σ ] ⇒ _ ∷ _
          red = prodrec-β ⊢σF ⊢σG ⊢σA ⊢σt ⊢σt′ ⊢σu PE.refl ok
          [σA[p]] = proj₁ (unwrap [A[p]] ⊢Δ [σ])
          [σA[p]]′ = irrelevance′ (singleSubstLift A (prod! t t′)) [σA[p]]
          [σu₊] = proj₁ ([u₊] ⊢Δ [σ])
          [σu₊]′ = irrelevanceTerm″ (singleSubstLift A (prod! t t′))
                                    (PE.sym (PE.trans (doubleSubstComp u (t [ σ ]) (t′ [ σ ]) σ)
                                                      (PE.trans (substVar-to-subst (λ {x0 → PE.refl; (x0 +1) → PE.refl; (x +1 +1) → PE.refl}) u)
                                                                (PE.sym (substCompEq u)))))
                                    [σA[p]] [σA[p]]′ [σu₊]
          _ , [pr≡u₊] = redSubstTerm red [σA[p]]′ [σu₊]′
      in  irrelevanceEqTerm″ PE.refl
                             (PE.trans (doubleSubstComp u (t [ σ ]) (t′ [ σ ]) σ)
                                       (PE.trans (substVar-to-subst (λ{x0 → PE.refl; (x0 +1) → PE.refl; (x +1 +1) → PE.refl}) u)
                                                 (PE.sym (substCompEq u))))
                             (PE.sym (singleSubstLift A (prod! t t′))) [σA[p]]′ [σA[p]] [pr≡u₊]
  fundamentalTermEq (unitrec-cong {A = A} {A′} {t} {t′} {u} {u′} ⊢A≡A′ ⊢t≡t′ ⊢u≡u′ ok)
    with fundamentalTermEq ⊢u≡u′ | fundamentalTermEq ⊢t≡t′ | fundamentalEq ⊢A≡A′
  ... | [Γ] , modelsTermEq [A₊]′ [u]′ [u′]′ [u≡u′]′
      | [Γ]₁ , modelsTermEq [Unit]₁ [t]₁ [t′]₁ [t≡t′]₁
      | [Γ]₂ , [A]₂ , [A′]₂ , [A≡A′]₂ =
    let [Unit] = Unitᵛ [Γ] ok
        [A] = S.irrelevance [Γ]₂ ([Γ] ∙ [Unit]) [A]₂
        [A′] = S.irrelevance [Γ]₂ ([Γ] ∙ [Unit]) [A′]₂
        [A≡A′] = S.irrelevanceEq {B = A′} [Γ]₂ ([Γ] ∙ [Unit]) [A]₂ [A] [A≡A′]₂
        [t] = S.irrelevanceTerm {t = t} [Γ]₁ [Γ] [Unit]₁ [Unit] [t]₁
        [t′] = S.irrelevanceTerm {t = t′} [Γ]₁ [Γ] [Unit]₁ [Unit] [t′]₁
        [t≡t′] = S.irrelevanceEqTerm {t = t} {t′} [Γ]₁ [Γ] [Unit]₁ [Unit] [t≡t′]₁
        [star] = starᵛ {l = ¹} [Γ] ok
        [A₊] = substS [Γ] [Unit] [A] [star]
        [A′₊] = substS {t = starʷ} [Γ] [Unit] [A′] [star]
        [u] = S.irrelevanceTerm {t = u} [Γ] [Γ] [A₊]′ [A₊] [u]′
        [u′] = S.irrelevanceTerm {t = u′} [Γ] [Γ] [A₊]′ [A₊] [u′]′
        [u≡u′] = S.irrelevanceEqTerm {t = u} {u′} [Γ] [Γ] [A₊]′ [A₊] [u≡u′]′
        [Aₜ] = substS [Γ] [Unit] [A] [t]
        [A′ₜ′] = substS [Γ] [Unit] [A′] [t′]
        [urₜ] = unitrecᵛ {t = t} {u} [Γ] ok [A] [t] [u]
        [A₊≡A′₊] = substSEq {t = starʷ} {starʷ} [Γ] [Unit] [Unit] (reflᵛ [Γ] [Unit])
                            [A] [A′] [A≡A′] [star] [star] (reflᵗᵛ {t = starʷ} [Γ] [Unit] [star])
        [u′]′ = convᵛ {t = u′} [Γ] [A₊] [A′₊] [A₊≡A′₊] [u′]
        [urₜ′]′ = unitrecᵛ {t = t′} {u′} [Γ] ok [A′] [t′] [u′]′
        [At≡A′t′] = substSEq {t = t} {t′} [Γ] [Unit] [Unit] (reflᵛ [Γ] [Unit])
                             [A] [A′] [A≡A′] [t] [t′] [t≡t′]
        [urₜ′] = conv₂ᵛ {t = unitrec _ _ A′ t′ u′} [Γ] [Aₜ] [A′ₜ′] [At≡A′t′] [urₜ′]′
        [urₜ≡urₜ′] = unitrec-congᵛ {t = t} {t′} {u} {u′} [Γ] ok [A] [A′] [A≡A′]
                                   [t] [t′] [t≡t′] [u] [u′] [u≡u′]
    in  [Γ] , modelsTermEq [Aₜ] [urₜ] [urₜ′] [urₜ≡urₜ′]
  fundamentalTermEq {Γ = Γ} (unitrec-β {A} {u} ⊢A ⊢u ok)
    with fundamentalTerm ⊢u | fundamental ⊢A
  ... | [Γ] , [A₊] , [u] | [Γ]₁ , [A]₁ =
    let [Unit] = Unitᵛ {l = ¹} [Γ] ok
        [star] = starᵛ {l = ¹} [Γ] ok
        [A] = S.irrelevance [Γ]₁ ([Γ] ∙ [Unit]) [A]₁
        red : Γ ⊩ᵛ unitrec _ _ A starʷ u ⇒ u ∷ A [ starʷ ]₀ / [Γ]
        red = λ {_} {Δ} {σ} ⊢Δ [σ] →
          let [⇑σ] = liftSubstS [Γ] ⊢Δ [Unit] [σ]
              [σA] = proj₁ (unwrap [A] {σ = liftSubst σ} (⊢Δ ∙ Unitⱼ ⊢Δ ok) [⇑σ])
              [σA₊] = proj₁ (unwrap [A₊] ⊢Δ [σ])
              [σu] = proj₁ ([u] ⊢Δ [σ])
              ⊢σA = escape [σA]
              ⊢σu = escapeTerm [σA₊] [σu]
              ⊢σu′ = PE.subst (λ x → Δ ⊢ u [ σ ] ∷ x)
                              (singleSubstLift A starʷ) ⊢σu
          in  PE.subst (λ x → Δ ⊢ (unitrec _ _ A starʷ u) [ σ ] ⇒ _ ∷ x)
                       (PE.sym (singleSubstLift A starʷ))
                       (unitrec-β ⊢σA ⊢σu′ ok)
        [ur₊] , [ur₊≡u] = redSubstTermᵛ {t = unitrec _ _ A starʷ u} {u} [Γ] red [A₊] [u]
    in  [Γ] , modelsTermEq [A₊] [ur₊] [u] [ur₊≡u]
  fundamentalTermEq
    (Id-cong {A₁} {A₂} {t₁} {t₂} {u₁} {u₂} A₁≡A₂ t₁≡t₂ u₁≡u₂) =
    case fundamentalTermEq A₁≡A₂ of λ {
      (⊩Γ , _) →
    let ⊩U = Uᵛ ⊩Γ in
    case fundamentalTermEq′ ⊩U A₁≡A₂ of λ {
      (⊩A₁∷U , ⊩A₂∷U , A₁≡A₂∷U) →
    case univᵛ {A = A₁} _ ⊩U ⊩A₁∷U of λ {
      ⊩A₁ →
    case univᵛ {A = A₂} _ ⊩U ⊩A₂∷U of λ {
      ⊩A₂ →
    case (λ {k Δ σ} →
            univEqᵛ {B = A₂} _ ⊩U ⊩A₁ A₁≡A₂∷U
              {k = k} {Δ = Δ} {σ = σ}) of λ {
      A₁≡A₂ →
    case fundamentalTermEq″ ⊩A₁ ⊩A₂ A₁≡A₂ t₁≡t₂ of λ {
      (⊩t₁ , _ , ⊩t₂ , t₁≡t₂) →
    case fundamentalTermEq″ ⊩A₁ ⊩A₂ A₁≡A₂ u₁≡u₂ of λ {
      (⊩u₁ , _ , ⊩u₂ , u₁≡u₂) →
      ⊩Γ
    , modelsTermEq
        (Uᵛ ⊩Γ)
        (Idᵗᵛ t₁ u₁ ⊩A₁ ⊩A₁∷U ⊩t₁ ⊩u₁)
        (Idᵗᵛ t₂ u₂ ⊩A₂ ⊩A₂∷U ⊩t₂ ⊩u₂)
        (Id-congᵗᵛ t₁ t₂ u₁ u₂
           ⊩A₁ ⊩A₂ ⊩A₁∷U ⊩A₂∷U ⊩t₁ ⊩t₂ ⊩u₁ ⊩u₂
           A₁≡A₂∷U t₁≡t₂ u₁≡u₂) }}}}}}}
  fundamentalTermEq
    (J-cong {A₂} {t₁} {t₂} {B₂} {u₁} {u₂} {v₂} {w₁} {w₂}
       _ A₁≡A₂ _ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁≡w₂) =
    case fundamentalEq A₁≡A₂ of λ {
      (⊩Γ , ⊩A₁ , ⊩A₂ , ⊩A₁≡A₂) →
    let ⊩wk1-A₁ = wk1ᵛ _ ⊩A₁ ⊩A₁
        ⊩wk1-A₂ = wk1ᵛ _ ⊩A₂ ⊩A₂
    in
    case fundamentalTermEq″ ⊩A₁ ⊩A₂ ⊩A₁≡A₂ t₁≡t₂ of λ {
      (⊩t₁ , _ , ⊩t₂ , ⊩t₁≡t₂) →
    case fundamentalEq′ B₁≡B₂ of λ {
      (⊩B₁ , ⊩B₂ , ⊩B₁≡B₂) →
    case (λ {k Δ σ} →
            varᵛ here _ ⊩wk1-A₁
              {k = k} {Δ = Δ} {σ = σ}) of λ {
      ⊩0₁ →
    case (λ {k Δ σ} →
            wk1Eqᵛ {B = A₂} _ ⊩A₁ ⊩A₁ ⊩A₁≡A₂
              {k = k} {Δ = Δ} {σ = σ}) of λ {
      ⊩wk1-A₁≡wk1-A₂ →
    case fundamentalTermEq″ ⊩A₁ ⊩A₂ ⊩A₁≡A₂ v₁≡v₂ of λ {
      (⊩v₁ , _ , ⊩v₂ , ⊩v₁≡v₂) →
    case fundamentalTermEq″
           (Idᵛ ⊩A₁ ⊩t₁ ⊩v₁) (Idᵛ {t = t₂} {u = v₂} ⊩A₂ ⊩t₂ ⊩v₂)
           (Id-congᵛ t₂ v₂ ⊩A₂ ⊩t₂ ⊩v₂ ⊩A₁≡A₂ ⊩t₁≡t₂ ⊩v₁≡v₂)
           w₁≡w₂ of λ {
      (⊩w₁ , _ , ⊩w₂ , ⊩w₁≡w₂) →
    let ⊩Id-t₁-t₁ = Idᵛ ⊩A₁ ⊩t₁ ⊩t₁
        ⊩Id-t₂-t₂ = Idᵛ ⊩A₂ ⊩t₂ ⊩t₂
        ⊩Id-t₁-v₁ = Idᵛ ⊩A₁ ⊩t₁ ⊩v₁
        ⊩Id-t₂-v₂ = Idᵛ ⊩A₂ ⊩t₂ ⊩v₂
    in
    case Idᵛ ⊩wk1-A₂ (wk1Termᵛ t₂ ⊩A₂ ⊩A₂ ⊩t₂)
           (varᵛ here _ ⊩wk1-A₂) of λ {
      ⊩Id-wk1-t₂-0 →
    case (λ {k Δ σ} →
            Id-congᵛ (wk1 t₂) (var x0) (wk1ᵛ _ ⊩A₁ ⊩A₂)
              (wk1Termᵛ t₂ ⊩A₂ ⊩A₁ ⊩t₂)
              (convᵛ _ ⊩wk1-A₁ (wk1ᵛ _ ⊩A₁ ⊩A₂) ⊩wk1-A₁≡wk1-A₂ ⊩0₁)
              ⊩wk1-A₁≡wk1-A₂
              (wk1EqTermᵛ t₁ t₂ ⊩t₁≡t₂)
              (reflᵗᵛ _ ⊩wk1-A₁ ⊩0₁)
              {k = k} {Δ = Δ} {σ = σ}) of λ {
      ⊩Id₁≡Id₂ →
    case S.irrelevanceLift₂ {⊩B₂ = ⊩Id-wk1-t₂-0}
           ⊩A₁≡A₂ ⊩Id₁≡Id₂ ⊩B₂ of λ {
      ⊩B₂ →
    case PE.subst (_ ⊩ᵛ⟨ ¹ ⟩_/ ⊩Γ) ≡Id-wk1-wk1-0[]₀ ⊩Id-t₁-t₁ of λ {
      ⊩Id-t₁-t₁′ →
    case PE.subst (_ ⊩ᵛ⟨ ¹ ⟩_/ ⊩Γ) ≡Id-wk1-wk1-0[]₀ ⊩Id-t₂-t₂ of λ {
      ⊩Id-t₂-t₂′ →
    case PE.subst (_ ⊩ᵛ⟨ ¹ ⟩_/ ⊩Γ) ≡Id-wk1-wk1-0[]₀ ⊩Id-t₁-v₁ of λ {
      ⊩Id-t₁-v₁′ →
    case PE.subst (_ ⊩ᵛ⟨ ¹ ⟩_/ ⊩Γ) ≡Id-wk1-wk1-0[]₀ ⊩Id-t₂-v₂ of λ {
      ⊩Id-t₂-v₂′ →
    case substD ⊩v₁ ⊩Id-t₁-v₁′
           (S.irrelevanceTerm′ {t = w₁} ≡Id-wk1-wk1-0[]₀ _ _
              ⊩Id-t₁-v₁ ⊩Id-t₁-v₁′ ⊩w₁)
           ⊩B₁ of λ {
      ⊩B₁[v₁,w₁] →
    case substD {u = w₂} ⊩v₂ ⊩Id-t₂-v₂′
           (S.irrelevanceTerm′ {t = w₂} ≡Id-wk1-wk1-0[]₀ _ _
              ⊩Id-t₂-v₂ ⊩Id-t₂-v₂′ ⊩w₂)
           ⊩B₂ of λ {
      ⊩B₂[v₂,w₂] →
    case (λ {k Δ σ} →
            substDEq {⊩t₁ = ⊩v₁} {⊩B₁[t₁] = ⊩Id-t₁-v₁′}
              {⊩u₁ =
                 S.irrelevanceTerm′ {t = w₁} ≡Id-wk1-wk1-0[]₀ _ _
                   ⊩Id-t₁-v₁ ⊩Id-t₁-v₁′ ⊩w₁}
              {⊩C₁ = ⊩B₁} ⊩A₁≡A₂ ⊩Id₁≡Id₂ ⊩v₂ ⊩v₁≡v₂ ⊩Id-t₂-v₂′
              (S.irrelevanceTerm′ {t = w₂} ≡Id-wk1-wk1-0[]₀ _ _
                 ⊩Id-t₂-v₂ ⊩Id-t₂-v₂′ ⊩w₂)
              (S.irrelevanceEqTerm′ w₁ w₂ ≡Id-wk1-wk1-0[]₀
                 ⊩Id-t₁-v₁ ⊩Id-t₁-v₁′ ⊩w₁≡w₂)
              ⊩B₁[v₁,w₁] ⊩B₂ ⊩B₁≡B₂
              {k = k} {Δ = Δ} {σ = σ}) of λ {
      ⊩B₁[v₁,w₁]≡B₂[v₂,w₂] →
    case substD
           ⊩t₁ ⊩Id-t₁-t₁′
           (S.irrelevanceTerm′ {t = rfl} ≡Id-wk1-wk1-0[]₀ _ _
              ⊩Id-t₁-t₁ ⊩Id-t₁-t₁′ rflᵛ)
           ⊩B₁ of λ {
      ⊩B₁[t₁,rfl] →
    case substD ⊩t₂ ⊩Id-t₂-t₂′
           (S.irrelevanceTerm′ {t = rfl} ≡Id-wk1-wk1-0[]₀ _ _
              ⊩Id-t₂-t₂ ⊩Id-t₂-t₂′ rflᵛ)
           ⊩B₂ of λ {
      ⊩B₂[t₂,rfl] →
    case (λ {k Δ σ} →
            substDEq
              {⊩B₁ =
                 Idᵛ ⊩wk1-A₁ (wk1Termᵛ t₁ ⊩A₁ ⊩A₁ ⊩t₁)
                   (varᵛ here _ ⊩wk1-A₁)}
              {⊩t₁ = ⊩t₁} {⊩B₁[t₁] = ⊩Id-t₁-t₁′}
              {⊩u₁ =
                 S.irrelevanceTerm′ {t = rfl} ≡Id-wk1-wk1-0[]₀ _ _
                   ⊩Id-t₁-t₁ ⊩Id-t₁-t₁′ rflᵛ}
              {⊩C₁ = ⊩B₁}
              ⊩A₁≡A₂ ⊩Id₁≡Id₂ ⊩t₂ ⊩t₁≡t₂ ⊩Id-t₂-t₂′
              (S.irrelevanceTerm′ {t = rfl} ≡Id-wk1-wk1-0[]₀ _ _
                 ⊩Id-t₂-t₂ ⊩Id-t₂-t₂′ rflᵛ)
              (S.irrelevanceEqTerm′ rfl rfl ≡Id-wk1-wk1-0[]₀
                 ⊩Id-t₁-t₁ ⊩Id-t₁-t₁′ rfl-congᵛ)
              ⊩B₁[t₁,rfl] ⊩B₂ ⊩B₁≡B₂
              {k = k} {Δ = Δ} {σ = σ}) of λ {
      ⊩B₁[t₁,rfl]≡B₂[t₂,rfl] →
    case fundamentalTermEq″ ⊩B₁[t₁,rfl] ⊩B₂[t₂,rfl]
           ⊩B₁[t₁,rfl]≡B₂[t₂,rfl] u₁≡u₂ of λ {
      (⊩u₁ , _ , ⊩u₂ , ⊩u₁≡u₂) →
      ⊩Γ
    , modelsTermEq
        ⊩B₁[v₁,w₁]
        (Jᵛ u₁ ⊩B₁ ⊩B₁[t₁,rfl] ⊩B₁[v₁,w₁] ⊩u₁ ⊩w₁)
        (conv₂ᵛ {t = J _ _ A₂ t₂ B₂ u₂ v₂ w₂} _
           ⊩B₁[v₁,w₁] ⊩B₂[v₂,w₂] ⊩B₁[v₁,w₁]≡B₂[v₂,w₂]
           (Jᵛ u₂ ⊩B₂ ⊩B₂[t₂,rfl] ⊩B₂[v₂,w₂] ⊩u₂ ⊩w₂))
        (J-congᵛ u₁ u₂ w₂ ⊩A₁≡A₂ ⊩t₁≡t₂
           ⊩B₁ ⊩B₂ ⊩B₁≡B₂ ⊩B₁[t₁,rfl] ⊩B₂[t₂,rfl] ⊩B₁[v₁,w₁]
           ⊩u₁ ⊩u₂ ⊩u₁≡u₂ ⊩v₁≡v₂ ⊩w₁ ⊩w₂ ⊩w₁≡w₂) }}}}}}}}}}}}}}}}}}}}}
  fundamentalTermEq
    (K-cong {A₂} {t₂} {B₂} {u₁} {u₂} {v₂}
       A₁≡A₂ _ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ ok) =
    case fundamentalEq A₁≡A₂ of λ {
      (_ , ⊩A₁ , ⊩A₂ , A₁≡A₂) →
    case fundamentalTermEq″ ⊩A₁ ⊩A₂ A₁≡A₂ t₁≡t₂ of λ {
      (⊩t₁ , _ , ⊩t₂ , t₁≡t₂) →
    let ⊩Id₁ = Idᵛ ⊩A₁ ⊩t₁ ⊩t₁
        ⊩Id₂ = Idᵛ {t = t₂} {u = t₂} ⊩A₂ ⊩t₂ ⊩t₂
    in
    case (λ {k Δ σ} →
            Id-congᵛ t₂ t₂ ⊩A₂ ⊩t₂ ⊩t₂ A₁≡A₂ t₁≡t₂ t₁≡t₂
              {k = k} {Δ = Δ} {σ = σ}) of λ {
      Id₁≡Id₂ →
    case fundamentalEq′ B₁≡B₂ of λ {
      (⊩B₁ , ⊩B₂ , B₁≡B₂) →
    case S.irrelevanceLift _ _ _ Id₁≡Id₂ ⊩B₂ of λ {
      ⊩B₂ →
    let ⊩B₁[rfl] = substS {t = rfl} _ ⊩Id₁ ⊩B₁ rflᵛ in
    case substS {t = rfl} _ ⊩Id₂ ⊩B₂ rflᵛ of λ {
      ⊩B₂[rfl] →
    case fundamentalTermEq″
           ⊩B₁[rfl] ⊩B₂[rfl]
           (substSEq _ ⊩Id₁ ⊩Id₂ Id₁≡Id₂ ⊩B₁ ⊩B₂ B₁≡B₂
              rflᵛ rflᵛ rfl-congᵛ)
           u₁≡u₂ of λ {
      (⊩u₁ , _ , ⊩u₂ , u₁≡u₂) →
    case fundamentalTermEq″ ⊩Id₁ ⊩Id₂ Id₁≡Id₂ v₁≡v₂ of λ {
      (⊩v₁ , _ , ⊩v₂ , v₁≡v₂) →
    let ⊩B₁[v₁] = substS _ ⊩Id₁ ⊩B₁ ⊩v₁ in
    case substS _ ⊩Id₂ ⊩B₂ ⊩v₂ of λ {
      ⊩B₂[v₂] →
      _
    , modelsTermEq
        ⊩B₁[v₁]
        (Kᵛ u₁ ok ⊩B₁ ⊩B₁[rfl] ⊩u₁ ⊩v₁ ⊩B₁[v₁])
        (conv₂ᵛ {t = K _ A₂ t₂ B₂ u₂ v₂} _ ⊩B₁[v₁] ⊩B₂[v₂]
           (substSEq _ ⊩Id₁ ⊩Id₂ Id₁≡Id₂ ⊩B₁ ⊩B₂ B₁≡B₂ ⊩v₁ ⊩v₂ v₁≡v₂)
           (Kᵛ {v = v₂} u₂ ok ⊩B₂ ⊩B₂[rfl] ⊩u₂ ⊩v₂ ⊩B₂[v₂]))
        (K-congᵛ ok u₁ u₂ v₂
           A₁≡A₂ t₁≡t₂ ⊩B₁ ⊩B₂ B₁≡B₂ ⊩B₁[rfl] ⊩B₂[rfl]
           ⊩u₁ ⊩u₂ u₁≡u₂ ⊩v₁ ⊩v₂ v₁≡v₂
           ⊩B₁[v₁]) }}}}}}}}}
  fundamentalTermEq
    ([]-cong-cong {A₂} {t₁} {t₂} {u₁} {u₂} {v₁} {v₂} {k}
       A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ ok) =
    case fundamentalEq A₁≡A₂ of λ {
      (⊩Γ , ⊩A₁ , ⊩A₂ , ⊩A₁≡A₂) →
    case fundamentalTermEq″ ⊩A₁ ⊩A₂ ⊩A₁≡A₂ t₁≡t₂ of λ {
      (⊩t₁ , ⊩t₂′ , ⊩t₂ , ⊩t₁≡t₂) →
    case fundamentalTermEq″ ⊩A₁ ⊩A₂ ⊩A₁≡A₂ u₁≡u₂ of λ {
      (⊩u₁ , ⊩u₂′ , ⊩u₂ , ⊩u₁≡u₂) →
    case fundamentalTermEq″
           (Idᵛ ⊩A₁ ⊩t₁ ⊩u₁)
           (Idᵛ {t = t₂} {u = u₂} ⊩A₂ ⊩t₂ ⊩u₂)
           (Id-congᵛ t₂ u₂ ⊩A₂ ⊩t₂ ⊩u₂ ⊩A₁≡A₂ ⊩t₁≡t₂ ⊩u₁≡u₂)
           v₁≡v₂ of λ {
      (⊩v₁ , _ , ⊩v₂ , ⊩v₁≡v₂) →
      ⊩Γ
    , modelsTermEq
        (Idᵛ (Erasedᵛ ⊩A₁) ([]ᵛ t₁ ⊩t₁) ([]ᵛ u₁ ⊩u₁))
        ([]-congᵛ v₁ ⊩v₁)
        (conv₂ᵛ {t = []-cong k A₂ t₂ u₂ v₂} _
           (Idᵛ (Erasedᵛ ⊩A₁) ([]ᵛ t₁ ⊩t₁) ([]ᵛ u₁ ⊩u₁))
           (Idᵛ (Erasedᵛ ⊩A₂) ([]ᵛ t₂ ⊩t₂) ([]ᵛ u₂ ⊩u₂))
           (Id-congᵛ
              ([ t₂ ]) ([ u₂ ]) (Erasedᵛ ⊩A₂) ([]ᵛ t₂ ⊩t₂) ([]ᵛ u₂ ⊩u₂)
              (Erased-congᵛ ⊩A₂ ⊩A₁≡A₂)
              ([]-congᵛ′ t₁ t₂ ⊩t₁ ⊩t₂′ ⊩t₁≡t₂)
              ([]-congᵛ′ u₁ u₂ ⊩u₁ ⊩u₂′ ⊩u₁≡u₂))
           ([]-congᵛ v₂ ⊩v₂))
        ([]-cong-congᵛ t₂ u₂ v₁ v₂
           ⊩A₂ ⊩A₁≡A₂ ⊩t₂ ⊩t₁≡t₂ ⊩u₂ ⊩u₁≡u₂ ⊩v₁≡v₂) }}}}
    where
    open Erased ([]-cong→Erased ok) renaming ([]-congᵛ to []-congᵛ′)
    open E k
  fundamentalTermEq (J-β {t} {u} ⊢A ⊢t ⊢B ⊢u PE.refl) =
    case fundamental ⊢A of λ {
      (⊩Γ , ⊩A) →
    let ⊩wk1-A = wk1ᵛ _ ⊩A ⊩A in
    case (λ {k Δ σ} →
            fundamentalTerm′ ⊩A ⊢t
              {k = k} {Δ = Δ} {σ = σ}) of λ {
      ⊩t →
    case fundamental′ ⊢B of λ {
      ⊩B →
    case PE.subst (_ ⊩ᵛ⟨ ¹ ⟩_/ ⊩Γ) (≡Id-wk1-wk1-0[]₀ {t = t})
           (Idᵛ ⊩A ⊩t ⊩t) of λ {
      ⊩Id →
    case substD ⊩t ⊩Id
           (S.irrelevanceTerm′ {t = rfl} ≡Id-wk1-wk1-0[]₀ _ _
              (Idᵛ ⊩A ⊩t ⊩t) ⊩Id rflᵛ)
           ⊩B of λ {
      ⊩B[t,rfl] →
    case (λ {k Δ σ} →
            fundamentalTerm′ ⊩B[t,rfl] ⊢u
              {k = k} {Δ = Δ} {σ = σ}) of λ {
      ⊩u →
      ⊩Γ
    , modelsTermEq
        ⊩B[t,rfl]
        (Jᵛ {⊩t = ⊩t} u ⊩B ⊩B[t,rfl] ⊩B[t,rfl] ⊩u rflᵛ)
        ⊩u
        (J-βᵛ
           {⊩Id = Idᵛ ⊩wk1-A (wk1Termᵛ t ⊩A ⊩A ⊩t) (varᵛ here _ ⊩wk1-A)}
           u ⊩t ⊩B ⊩B[t,rfl] ⊩u) }}}}}}
  fundamentalTermEq (K-β {u} ⊢t ⊢B ⊢u ok) =
    case fundamentalTerm ⊢t of λ {
      (⊩Γ , ⊩A , ⊩t) →
    let ⊩Id = Idᵛ ⊩A ⊩t ⊩t in
    case fundamental′ {⊩Γ = _ ∙ ⊩Id} ⊢B of λ {
      ⊩B →
    case substS {t = rfl} _ ⊩Id ⊩B rflᵛ of λ {
      ⊩B[rfl] →
    case (λ {k Δ σ} →
            fundamentalTerm′ ⊩B[rfl] ⊢u
              {k = k} {Δ = Δ} {σ = σ}) of λ {
      ⊩u →
     ⊩Γ
    , modelsTermEq
        ⊩B[rfl]
        (Kᵛ u ok ⊩B ⊩B[rfl] ⊩u rflᵛ ⊩B[rfl])
        ⊩u
        (K-βᵛ u ok ⊩B ⊩B[rfl] ⊩u) }}}}
  fundamentalTermEq ([]-cong-β {t = t} ⊢t PE.refl ok) =
    case fundamentalTerm ⊢t of λ {
      (⊩Γ , ⊩A , ⊩t) →
      ⊩Γ
    , modelsTermEq
        (Idᵛ (Erasedᵛ ⊩A) ([]ᵛ t ⊩t) ([]ᵛ t ⊩t))
        ([]-congᵛ rfl rflᵛ)
        rflᵛ
        []-cong-βᵛ }
    where
    open Erased ([]-cong→Erased ok) hiding ([]-congᵛ)

  -- A variant of fundamental which can be used if "⊩Γ" is known.

  fundamental′ : Γ ⊢ A → Γ ⊩ᵛ⟨ ¹ ⟩ A / ⊩Γ
  fundamental′ ⊢A =
    case fundamental ⊢A of λ {
      (_ , ⊩A) →
    S.irrelevance _ _ ⊩A }

  -- A variant of fundamentalEq.

  fundamentalEq′ :
    Γ ⊢ A₁ ≡ A₂ →
    ∃ λ (⊩A₁ : Γ ⊩ᵛ⟨ ¹ ⟩ A₁ / ⊩Γ) →
    Γ ⊩ᵛ⟨ ¹ ⟩ A₂ / ⊩Γ ×
    Γ ⊩ᵛ⟨ ¹ ⟩ A₁ ≡ A₂ / ⊩Γ / ⊩A₁
  fundamentalEq′ {A₂} A₁≡A₂ =
    case fundamentalEq A₁≡A₂ of λ {
      (_ , ⊩A₁′ , ⊩A₂ , ⊩A₁≡A₂) →
    case S.irrelevance _ _ ⊩A₁′ of λ {
      ⊩A₁ →
      ⊩A₁
    , S.irrelevance _ _ ⊩A₂
    , S.irrelevanceEq {B = A₂} _ _ ⊩A₁′ ⊩A₁ ⊩A₁≡A₂ }}

  -- A variant of fundamentalTerm.

  fundamentalTerm′ :
    (⊩A : Γ ⊩ᵛ⟨ ¹ ⟩ A / ⊩Γ) →
    Γ ⊢ t ∷ A →
    Γ ⊩ᵛ⟨ ¹ ⟩ t ∷ A / ⊩Γ / ⊩A
  fundamentalTerm′ {t} ⊩A ⊢t =
    case fundamentalTerm ⊢t of λ {
      (_ , ⊩A′ , ⊩t) →
    S.irrelevanceTerm {t = t} _ _ ⊩A′ ⊩A ⊩t }

  -- A variant of fundamentalTermEq.

  fundamentalTermEq′ :
    (⊩A : Γ ⊩ᵛ⟨ ¹ ⟩ A / ⊩Γ) →
    Γ ⊢ t₁ ≡ t₂ ∷ A →
    Γ ⊩ᵛ⟨ ¹ ⟩ t₁ ∷ A / ⊩Γ / ⊩A ×
    Γ ⊩ᵛ⟨ ¹ ⟩ t₂ ∷ A / ⊩Γ / ⊩A ×
    Γ ⊩ᵛ⟨ ¹ ⟩ t₁ ≡ t₂ ∷ A / ⊩Γ / ⊩A
  fundamentalTermEq′ ⊩A t₁≡t₂ =
    case fundamentalTermEq″ ⊩A ⊩A (reflᵛ _ ⊩A) t₁≡t₂ of λ {
      (⊩t₁ , ⊩t₂ , _ , t₁≡t₂) →
    ⊩t₁ , ⊩t₂ , t₁≡t₂ }

  -- Another variant of fundamentalTermEq.

  fundamentalTermEq″ :
    (⊩A₁ : Γ ⊩ᵛ⟨ ¹ ⟩ A₁ / ⊩Γ)
    (⊩A₂ : Γ ⊩ᵛ⟨ ¹ ⟩ A₂ / ⊩Γ) →
    Γ ⊩ᵛ⟨ ¹ ⟩ A₁ ≡ A₂ / ⊩Γ / ⊩A₁ →
    Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
    Γ ⊩ᵛ⟨ ¹ ⟩ t₁ ∷ A₁ / ⊩Γ / ⊩A₁ ×
    Γ ⊩ᵛ⟨ ¹ ⟩ t₂ ∷ A₁ / ⊩Γ / ⊩A₁ ×
    Γ ⊩ᵛ⟨ ¹ ⟩ t₂ ∷ A₂ / ⊩Γ / ⊩A₂ ×
    Γ ⊩ᵛ⟨ ¹ ⟩ t₁ ≡ t₂ ∷ A₁ / ⊩Γ / ⊩A₁
  fundamentalTermEq″ {t₁} {t₂} ⊩A₁ ⊩A₂ A₁≡A₂ t₁≡t₂ =
    case fundamentalTermEq t₁≡t₂ of λ {
      (_ , modelsTermEq ⊩A ⊩t₁ ⊩t₂ ⊩t₁≡t₂) →
    case (λ {k Δ σ} →
            S.irrelevanceTerm {t = t₂} _ _ ⊩A ⊩A₁ ⊩t₂
              {k = k} {Δ = Δ} {σ = σ}) of λ {
      ⊩t₂ →
      S.irrelevanceTerm {t = t₁} _ _ ⊩A ⊩A₁ ⊩t₁
    , ⊩t₂
    , convᵛ {t = t₂} _ ⊩A₁ ⊩A₂ A₁≡A₂ ⊩t₂
    , S.irrelevanceEqTerm {t = t₁} {u = t₂} _ _ ⊩A ⊩A₁ ⊩t₁≡t₂ }}

-- Fundamental theorem for substitutions.
fundamentalSubst : (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ)
      → Δ ⊢ˢ σ ∷ Γ
      → ∃ λ [Γ] → Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ
fundamentalSubst ε ⊢Δ [σ] = ε , lift tt
fundamentalSubst (⊢Γ ∙ ⊢A) ⊢Δ ([tailσ] , [headσ]) =
  let [Γ] , [A] = fundamental ⊢A
      [Δ] , [A]′ , [t] = fundamentalTerm [headσ]
      [Γ]′ , [σ] = fundamentalSubst ⊢Γ ⊢Δ [tailσ]
      [tailσ]′ = S.irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ]
      [idA]  = proj₁ (unwrap [A]′ (soundContext [Δ]) (idSubstS [Δ]))
      [idA]′ = proj₁ (unwrap [A] ⊢Δ [tailσ]′)
      [idt]  = proj₁ ([t] (soundContext [Δ]) (idSubstS [Δ]))
  in  [Γ] ∙ [A] , ([tailσ]′
  ,   irrelevanceTerm″ (subst-id _) (subst-id _) [idA] [idA]′ [idt])

-- Fundamental theorem for substitution equality.
fundamentalSubstEq : (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ)
      → Δ ⊢ˢ σ ≡ σ′ ∷ Γ
      → ∃₂ λ [Γ] [σ]
      → ∃  λ ([σ′] : Δ ⊩ˢ σ′ ∷ Γ / [Γ] / ⊢Δ)
      → Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ]
fundamentalSubstEq ε ⊢Δ σ = ε , lift tt , lift tt , lift tt
fundamentalSubstEq (⊢Γ ∙ ⊢A) ⊢Δ (tailσ≡σ′ , headσ≡σ′) =
  let [Γ] , [A] = fundamental ⊢A
      [Γ]′ , [tailσ] , [tailσ′] , [tailσ≡σ′] = fundamentalSubstEq ⊢Γ ⊢Δ tailσ≡σ′
      [Δ] , modelsTermEq [A]′ [t] [t′] [t≡t′] = fundamentalTermEq headσ≡σ′
      [tailσ]′ = S.irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [tailσ]
      [tailσ′]′ = S.irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [tailσ′]
      [tailσ≡σ′]′ = S.irrelevanceSubstEq [Γ]′ [Γ] ⊢Δ ⊢Δ [tailσ] [tailσ]′ [tailσ≡σ′]
      [idA]  = proj₁ (unwrap [A]′ (soundContext [Δ]) (idSubstS [Δ]))
      [idA]′ = proj₁ (unwrap [A] ⊢Δ [tailσ]′)
      [idA]″ = proj₁ (unwrap [A] ⊢Δ [tailσ′]′)
      [idt]  = proj₁ ([t] (soundContext [Δ]) (idSubstS [Δ]))
      [idt′] = proj₁ ([t′] (soundContext [Δ]) (idSubstS [Δ]))
      [idt≡t′]  = [t≡t′] (soundContext [Δ]) (idSubstS [Δ])
  in  [Γ] ∙ [A]
  ,   ([tailσ]′ , irrelevanceTerm″ (subst-id _) (subst-id _) [idA] [idA]′ [idt])
  ,   ([tailσ′]′ , convTerm₁ [idA]′ [idA]″
                             (proj₂ (unwrap [A] ⊢Δ [tailσ]′) [tailσ′]′ [tailσ≡σ′]′)
                             (irrelevanceTerm″ (subst-id _) (subst-id _)
                                                [idA] [idA]′ [idt′]))
  ,   ([tailσ≡σ′]′ , irrelevanceEqTerm″ (subst-id _) (subst-id _) (subst-id _)
                                         [idA] [idA]′ [idt≡t′])
