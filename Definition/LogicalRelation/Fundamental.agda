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

open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Definition.Typed R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Escape R
open import Definition.LogicalRelation.Substitution.Properties R
open import Definition.LogicalRelation.Substitution.Conversion R
open import Definition.LogicalRelation.Substitution.Reduction R
open import Definition.LogicalRelation.Substitution.Reflexivity R
open import Definition.LogicalRelation.Substitution.Introductions R
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
open import Tools.Nat using (Nat)
import Tools.PropositionalEquality as PE

private
  variable
    m n : Nat
    Γ : Con Term n
    Δ : Con Term m
    σ σ₁ σ₂ σ′ : Subst m n
    A A₁ A₂ B t t₁ t₂ u : Term _
    ⊩Γ : ⊩ᵛ _

opaque
 unfolding _⊩ᵛ⟨_⟩_ _⊩ᵛ⟨_⟩_≡_ _⊩ᵛ⟨_⟩_∷_ _⊩ᵛ⟨_⟩_≡_∷_

 mutual
  -- Fundamental theorem for contexts.
  valid : ⊢ Γ → ⊩ᵛ Γ
  valid ε = ε
  valid (⊢Γ ∙ A) = let [Γ] , [A] = fundamental A in [Γ] ∙ [A]


  -- Fundamental theorem for types.
  fundamental : ∀ {A} (⊢A : Γ ⊢ A) → Σ (⊩ᵛ Γ) (λ [Γ] → Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ])
  fundamental (ℕⱼ ⊢Γ) =
    ℕᵛ (valid ⊢Γ)
  fundamental (Emptyⱼ x) = valid x , Emptyᵛ (valid x)
  fundamental (Unitⱼ ⊢Γ ok) =
    Unitᵛ (valid ⊢Γ) ok
  fundamental (Uⱼ ⊢Γ) =
    ⊩ᵛU (valid ⊢Γ)
  fundamental (ΠΣⱼ ⊢F ⊢G ok)
    with fundamental ⊢F | fundamental ⊢G
  … | [Γ] , [F] | [Γ∙F] , [G] =
    [Γ] , ΠΣᵛ [Γ] [F] (S.irrelevance [Γ∙F] ([Γ] ∙ [F]) [G]) ok
  fundamental (Idⱼ ⊢t ⊢u) =
    Idᵛ (fundamentalTerm ⊢t) (fundamentalTerm ⊢u)
  fundamental (univ ⊢A) =
    ⊩ᵛ∷U→⊩ᵛ (fundamentalTerm ⊢A)

  -- Fundamental theorem for type equality.
  fundamentalEq : ∀ {A B} → Γ ⊢ A ≡ B
    → ∃  λ ([Γ] : ⊩ᵛ Γ)
    → ∃₂ λ ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ]) ([B] : Γ ⊩ᵛ⟨ ¹ ⟩ B / [Γ])
    → Γ ⊩ᵛ⟨ ¹ ⟩ A ≡ B / [Γ] / [A]
  fundamentalEq (univ A≡B) =
    ⊩ᵛ≡∷U→⊩ᵛ≡ (fundamentalTermEq A≡B)
  fundamentalEq (refl ⊢A) =
    refl-⊩ᵛ≡ (fundamental ⊢A)
  fundamentalEq (sym A≡B) =
    sym-⊩ᵛ≡ (fundamentalEq A≡B)
  fundamentalEq (trans A≡B B≡C) =
    trans-⊩ᵛ≡ (fundamentalEq A≡B) (fundamentalEq B≡C)
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
  fundamentalEq (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) =
    Id-congᵛ (fundamentalEq A₁≡A₂) (fundamentalTermEq t₁≡t₂)
      (fundamentalTermEq u₁≡u₂)

  -- Fundamental theorem for terms.
  fundamentalTerm : ∀ {A t} → Γ ⊢ t ∷ A
    → ∃ λ ([Γ] : ⊩ᵛ Γ)
    → ∃ λ ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ])
    → Γ ⊩ᵛ⟨ ¹ ⟩ t ∷ A / [Γ] / [A]
  fundamentalTerm (ℕⱼ ⊢Γ) =
    ℕᵗᵛ (valid ⊢Γ)
  fundamentalTerm (Emptyⱼ x) = valid x , Uᵛ (valid x) , Emptyᵗᵛ (valid x)
  fundamentalTerm (Unitⱼ ⊢Γ ok) =
    Unitᵗᵛ (valid ⊢Γ) ok
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
  fundamentalTerm (var ⊢Γ x∈Γ) =
    emb-⊩ᵛ∷ ≤¹ (varᵛ x∈Γ (valid ⊢Γ) .proj₂)
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
  fundamentalTerm (zeroⱼ ⊢Γ) =
    zeroᵛ (valid ⊢Γ)
  fundamentalTerm (sucⱼ {n = t} ⊢t) =
    sucᵛ {t = t} (fundamentalTerm ⊢t)
  fundamentalTerm (natrecⱼ {z = t} {s = u} ⊢A ⊢t ⊢u ⊢v) =
    natrecᵛ {t = t} {u = u} (fundamental ⊢A) (fundamentalTerm ⊢t)
      (fundamentalTerm ⊢u) (fundamentalTerm ⊢v)
  fundamentalTerm (emptyrecⱼ {A} {t = n} ⊢A ⊢n)
    with fundamental ⊢A | fundamentalTerm ⊢n
  ... | [Γ] , [A] | [Γ]′ , [Empty] , [n] =
    let [A]′ = S.irrelevance {A = A} [Γ] [Γ]′ [A]
    in [Γ]′ , [A]′ , emptyrecᵛ {F = A} {n} [Γ]′ [Empty] [A]′ [n]
  fundamentalTerm (starⱼ ⊢Γ ok) =
    starᵛ (valid ⊢Γ) ok
  fundamentalTerm (conv {t} ⊢t A≡B) =
    conv-⊩ᵛ∷ {t = t} (fundamentalEq A≡B) (fundamentalTerm ⊢t)
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
  fundamentalTerm (unitrecⱼ {u} ⊢A ⊢t ⊢u _) =
    unitrecᵛ {u = u} (fundamental ⊢A) (fundamentalTerm ⊢t)
      (fundamentalTerm ⊢u)
  fundamentalTerm (Idⱼ {t} {u} ⊢A ⊢t ⊢u) =
    Idᵗᵛ {t = t} {u = u} (fundamentalTerm ⊢A) (fundamentalTerm ⊢t)
      (fundamentalTerm ⊢u)
  fundamentalTerm (rflⱼ ⊢t) =
    rflᵛ (fundamentalTerm ⊢t)
  fundamentalTerm (Jⱼ {u} _ _ ⊢B ⊢u _ ⊢w) =
    Jᵛ {u = u} (fundamental ⊢B) (fundamentalTerm ⊢u)
      (fundamentalTerm ⊢w)
  fundamentalTerm (Kⱼ {u} _ ⊢B ⊢u ⊢v ok) =
    Kᵛ {u = u} ok (fundamental ⊢B) (fundamentalTerm ⊢u)
      (fundamentalTerm ⊢v)
  fundamentalTerm ([]-congⱼ {v} ⊢t ⊢u ⊢v ok) =
    []-congᵛ {v = v} ok (fundamentalTerm ⊢v)

  -- Fundamental theorem for term equality.
  fundamentalTermEq : ∀ {A t t′} → Γ ⊢ t ≡ t′ ∷ A
                    → ∃ λ ([Γ] : ⊩ᵛ Γ) →
                      [ Γ ⊩ᵛ⟨ ¹ ⟩ t ≡ t′ ∷ A / [Γ] ]
  fundamentalTermEq (refl ⊢t) =
    refl-⊩ᵛ≡∷ (fundamentalTerm ⊢t)
  fundamentalTermEq (sym t≡u) =
    sym-⊩ᵛ≡∷ (fundamentalTermEq t≡u)
  fundamentalTermEq (trans t≡u u≡v) =
    trans-⊩ᵛ≡∷ (fundamentalTermEq t≡u) (fundamentalTermEq u≡v)
  fundamentalTermEq (conv t≡u A≡B) =
    conv-⊩ᵛ≡∷ (fundamentalEq A≡B) (fundamentalTermEq t≡u)
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
  fundamentalTermEq (suc-cong t≡u) =
    suc-congᵛ (fundamentalTermEq t≡u)
  fundamentalTermEq (natrec-cong _ A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂) =
    natrec-congᵛ (fundamentalEq A₁≡A₂) (fundamentalTermEq t₁≡t₂)
      (fundamentalTermEq u₁≡u₂) (fundamentalTermEq v₁≡v₂)
  fundamentalTermEq (natrec-zero ⊢A ⊢t ⊢u) =
    natrec-zeroᵛ (fundamental ⊢A) (fundamentalTerm ⊢t)
      (fundamentalTerm ⊢u)
  fundamentalTermEq (natrec-suc ⊢A ⊢t ⊢u ⊢v) =
    natrec-sucᵛ (fundamental ⊢A) (fundamentalTerm ⊢t)
      (fundamentalTerm ⊢u) (fundamentalTerm ⊢v)
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
  fundamentalTermEq (η-unit ⊢t ⊢u) =
    η-unitᵛ (fundamentalTerm ⊢t) (fundamentalTerm ⊢u)
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
                                                      (PE.trans (substVar-to-subst (λ {x0 → PE.refl; (x0 +1) → PE.refl; (x +2) → PE.refl}) u)
                                                                (PE.sym (substCompEq u)))))
                                    [σA[p]] [σA[p]]′ [σu₊]
          _ , [pr≡u₊] = redSubstTerm red [σA[p]]′ [σu₊]′
      in  irrelevanceEqTerm″ PE.refl
                             (PE.trans (doubleSubstComp u (t [ σ ]) (t′ [ σ ]) σ)
                                       (PE.trans (substVar-to-subst (λ{x0 → PE.refl; (x0 +1) → PE.refl; (x +2) → PE.refl}) u)
                                                 (PE.sym (substCompEq u))))
                             (PE.sym (singleSubstLift A (prod! t t′))) [σA[p]]′ [σA[p]] [pr≡u₊]
  fundamentalTermEq (unitrec-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ _) =
    unitrec-congᵛ (fundamentalEq A₁≡A₂) (fundamentalTermEq t₁≡t₂)
      (fundamentalTermEq u₁≡u₂)
  fundamentalTermEq (unitrec-β ⊢A ⊢u _) =
    unitrec-βᵛ (fundamental ⊢A) (fundamentalTerm ⊢u)
  fundamentalTermEq (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) =
    Id-congᵗᵛ (fundamentalTermEq A₁≡A₂) (fundamentalTermEq t₁≡t₂)
      (fundamentalTermEq u₁≡u₂)
  fundamentalTermEq (J-cong _ A₁≡A₂ _ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁≡w₂) =
    J-congᵛ (fundamentalEq A₁≡A₂) (fundamentalTermEq t₁≡t₂)
      (fundamentalEq B₁≡B₂) (fundamentalTermEq u₁≡u₂)
      (fundamentalTermEq v₁≡v₂) (fundamentalTermEq w₁≡w₂)
  fundamentalTermEq (K-cong A₁≡A₂ _ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ ok) =
    K-congᵛ ok (fundamentalEq A₁≡A₂) (fundamentalTermEq t₁≡t₂)
      (fundamentalEq B₁≡B₂) (fundamentalTermEq u₁≡u₂)
      (fundamentalTermEq v₁≡v₂)
  fundamentalTermEq ([]-cong-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ ok) =
    []-cong-congᵛ ok (fundamentalEq A₁≡A₂) (fundamentalTermEq t₁≡t₂)
      (fundamentalTermEq u₁≡u₂) (fundamentalTermEq v₁≡v₂)
  fundamentalTermEq (J-β _ ⊢t ⊢B ⊢u PE.refl) =
    J-βᵛ (fundamentalTerm ⊢t) (fundamental ⊢B) (fundamentalTerm ⊢u)
  fundamentalTermEq (K-β _ ⊢B ⊢u ok) =
    K-βᵛ ok (fundamental ⊢B) (fundamentalTerm ⊢u)
  fundamentalTermEq ([]-cong-β ⊢t PE.refl ok) =
    []-cong-βᵛ ok (fundamentalTerm ⊢t)

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

opaque
  unfolding _⊩ᵛ⟨_⟩_

  -- A variant of fundamental.

  fundamental-⊩ᵛ : Γ ⊢ A → Γ ⊩ᵛ⟨ ¹ ⟩ A
  fundamental-⊩ᵛ = fundamental

opaque
  unfolding _⊩ᵛ⟨_⟩_≡_

  -- A variant of fundamentalEq.

  fundamental-⊩ᵛ≡ : Γ ⊢ A ≡ B → Γ ⊩ᵛ⟨ ¹ ⟩ A ≡ B
  fundamental-⊩ᵛ≡ = fundamentalEq

opaque
  unfolding _⊩ᵛ⟨_⟩_∷_

  -- A variant of fundamentalTerm.

  fundamental-⊩ᵛ∷ : Γ ⊢ t ∷ A → Γ ⊩ᵛ⟨ ¹ ⟩ t ∷ A
  fundamental-⊩ᵛ∷ = fundamentalTerm

opaque
  unfolding _⊩ᵛ⟨_⟩_≡_∷_

  -- A variant of fundamentalTermEq.

  fundamental-⊩ᵛ≡∷ : Γ ⊢ t ≡ u ∷ A → Γ ⊩ᵛ⟨ ¹ ⟩ t ≡ u ∷ A
  fundamental-⊩ᵛ≡∷ = fundamentalTermEq

opaque
  unfolding _⊩ˢ_∷_

  -- A variant of fundamentalSubst.

  fundamental-⊩ˢ∷ : ⊢ Δ → ⊢ Γ → Δ ⊢ˢ σ ∷ Γ → Δ ⊩ˢ σ ∷ Γ
  fundamental-⊩ˢ∷ ⊢Δ ⊢Γ ⊢σ =
    case fundamentalSubst ⊢Γ ⊢Δ ⊢σ of λ
      (_ , ⊩σ) →
    _ , _ , ⊩σ

opaque
  unfolding _⊩ˢ_≡_∷_

  -- A variant of fundamentalSubstEq.

  fundamental-⊩ˢ≡∷ : ⊢ Δ → ⊢ Γ → Δ ⊢ˢ σ₁ ≡ σ₂ ∷ Γ → Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ
  fundamental-⊩ˢ≡∷ ⊢Δ ⊢Γ σ₁≡σ₂ =
    case fundamentalSubstEq ⊢Γ ⊢Δ σ₁≡σ₂ of λ
      (_ , σ₁≡σ₂) →
    _ , _ , σ₁≡σ₂
