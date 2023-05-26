------------------------------------------------------------------------
-- Validity of the first projection.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions

module Definition.LogicalRelation.Substitution.Introductions.Fst
  {a} {M : Set a}
  (R : Type-restrictions M)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped M as U hiding (Wk; wk; _∷_)
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Weakening R as Wk hiding (wk; wkTerm; wkEqTerm)
open import Definition.Typed.RedSteps R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Introductions.Pi R

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n   : Nat
    Γ   : Con Term n
    p q : M

-- Reducibility of fst with a specific typing derivation
fst′ : ∀ {F G t l l′}
       ([F] : Γ ⊩⟨ l′ ⟩ F)
       ([ΣFG] : Γ ⊩⟨ l ⟩B⟨ BΣ Σₚ p q ⟩ Σₚ p , q ▷ F ▹ G)
       ([t] : Γ ⊩⟨ l ⟩ t ∷ Σ p , q ▷ F ▹ G / B-intr BΣ! [ΣFG])
       → Γ ⊩⟨ l′ ⟩ fst p t ∷ F / [F]
fst′
  {Γ = Γ} {q = q} {F = F} {t = t} [F]
  (noemb [Σ]@(Bᵣ F' G' D ⊢F ⊢G A≡A [F'] [G'] G-ext _))
  [t]@(Σₜ p d p≅p prodP propP)
  with B-PE-injectivity BΣ! BΣ! (whnfRed* (red D) ΠΣₙ)
... | PE.refl , PE.refl , _ =
  let [fstp]′ = proj₁ propP
      [fstp] : Γ ⊩⟨ _ ⟩ fst _ p ∷ F / [F]
      [fstp] = irrelevanceTerm′ (wk-id F)
                                ([F'] id (wf ⊢F)) [F]
                                [fstp]′
  in  proj₁ (redSubst*Term (fst-subst* (redₜ d) ⊢F ⊢G)
                           [F] [fstp])
fst′ {Γ = Γ} {t = t} {l = l} [F] (emb 0<1 x) [t] = fst′ [F] x [t]

-- Reducibility of fst with a general typing derivation
fst″ : ∀ {F G t l l′}
       ([F] : Γ ⊩⟨ l′ ⟩ F)
       ([ΣFG] : Γ ⊩⟨ l ⟩ Σₚ p , q ▷ F ▹ G)
       ([t] : Γ ⊩⟨ l ⟩ t ∷ Σₚ _ , _ ▷ F ▹ G / [ΣFG])
       → Γ ⊩⟨ l′ ⟩ fst p t ∷ F / [F]
fst″ {Γ = Γ} {t = t} {l = l} [F] [ΣFG] [t] =
  let [t]′ = irrelevanceTerm [ΣFG] (B-intr BΣ! (Σ-elim [ΣFG])) [t]
  in  fst′ [F] (Σ-elim [ΣFG]) [t]′

fst-cong′ :
  ∀ {F G t t′ l l′}
  ([F] : Γ ⊩⟨ l′ ⟩ F)
  ([ΣFG] : Γ ⊩⟨ l ⟩B⟨ BΣ Σₚ p q ⟩ Σₚ p , q ▷ F ▹ G)
  ([t≡t′] : Γ ⊩⟨ l ⟩ t ≡ t′ ∷ Σ p , q ▷ F ▹ G / B-intr BΣ! [ΣFG]) →
  Γ ⊩⟨ l′ ⟩ fst p t ≡ fst p t′ ∷ F / [F]
fst-cong′ {Γ = Γ} {q = q} {F = F} {G = G} [F]
          [ΣFG]@(noemb [Σ]@(Bᵣ F' G' D ⊢F ⊢G A≡A [F'] [G'] G-ext _))
          [t≡t′]@(Σₜ₌ p p′ d d′ prodP prodP′ p≅p′ [t] [t′] prop)
          with B-PE-injectivity BΣ! BΣ! (whnfRed* (red D) ΠΣₙ)
... | PE.refl , PE.refl , _ =
  let ⊢Γ = wf ⊢F
      [F]′ = [F'] id ⊢Γ
      [fstp] , [fstr] , [fst≡] , [snd≡] = prop
      [fstp]′ = irrelevanceTerm′ (wk-id F) [F]′ [F] [fstp]
      [fstr]′ = irrelevanceTerm′ (wk-id F) [F]′ [F] [fstr]
      [fst≡]′ = irrelevanceEqTerm′ (wk-id F) [F]′ [F] [fst≡]
      [fstt≡fstp] = proj₂ (redSubst*Term (fst-subst* (redₜ d) ⊢F ⊢G) [F] [fstp]′)
      [fstt′≡fstp′] = proj₂ (redSubst*Term (fst-subst* (redₜ d′) ⊢F ⊢G) [F] [fstr]′)
  in  transEqTerm [F] [fstt≡fstp] (transEqTerm [F] [fst≡]′ (symEqTerm [F] [fstt′≡fstp′]))
fst-cong′ [F] (emb 0<1 x) = fst-cong′ [F] x

-- Reducibility of congruence of fst
fst-cong″ : ∀ {F G t t′ l l′}
            ([F] : Γ ⊩⟨ l′ ⟩ F)
            ([ΣFG] : Γ ⊩⟨ l ⟩ Σₚ p , q ▷ F ▹ G)
            ([t≡t′] : Γ ⊩⟨ l ⟩ t ≡ t′ ∷ Σₚ _ , _ ▷ F ▹ G / [ΣFG])
            → Γ ⊩⟨ l′ ⟩ fst p t ≡ fst p t′ ∷ F / [F]
fst-cong″ {F = F} {G} [F] [ΣFG] [t≡t′] =
  let [t≡t′] = irrelevanceEqTerm [ΣFG] (B-intr BΣ! (Σ-elim [ΣFG])) [t≡t′]
  in  fst-cong′ [F] (Σ-elim [ΣFG]) [t≡t′]

fst-congᵛ :
  ∀ {F G t t′ l}
  ([Γ] : ⊩ᵛ Γ)
  ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
  ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
  (ok : Σₚ-restriction p)
  ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Σₚ p , q ▷ F ▹ G / [Γ] / Σᵛ [Γ] [F] [G] ok)
  ([t′] : Γ ⊩ᵛ⟨ l ⟩ t′ ∷ Σₚ p , q ▷ F ▹ G / [Γ] / Σᵛ [Γ] [F] [G] ok)
  ([t≡t′] : Γ ⊩ᵛ⟨ l ⟩ t ≡ t′ ∷ Σₚ p , q ▷ F ▹ G / [Γ] /
              Σᵛ [Γ] [F] [G] ok) →
  Γ ⊩ᵛ⟨ l ⟩ fst p t ≡ fst p t′ ∷ F / [Γ] / [F]
fst-congᵛ {F = F} {G} [Γ] [F] [G] ok [t] [t′] [t≡t′] ⊢Δ [σ] =
  let [ΣFG] = Σᵛ {F = F} {G} [Γ] [F] [G] ok
      ⊩σF = proj₁ (unwrap [F] ⊢Δ [σ])
      ⊩σΣFG = proj₁ (unwrap [ΣFG] ⊢Δ [σ])
      ⊩σt≡t′ = [t≡t′] ⊢Δ [σ]
  in  fst-cong″ ⊩σF ⊩σΣFG ⊩σt≡t′

-- Validity of first projection
fstᵛ : ∀ {Γ : Con Term n} {F : Term n} {G t l}
       ([Γ] : ⊩ᵛ Γ)
       ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
       ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
       (ok : Σₚ-restriction p)
       ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Σₚ p , q ▷ F ▹ G / [Γ] / Σᵛ [Γ] [F] [G] ok)
       → Γ ⊩ᵛ⟨ l ⟩ fst p t ∷ F / [Γ] / [F]
fstᵛ {Γ = Γ} {F} {G} {t} {l} [Γ] [F] [G] ok [t] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [ΣFG] = Σᵛ {F = F} {G} [Γ] [F] [G] ok
      σfst :
        ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ) →
        Δ ⊩⟨ l ⟩ subst σ (fst _ t) ∷ subst σ F /
          proj₁ (unwrap [F] ⊢Δ [σ])
      σfst {Δ} {σ} ⊢Δ [σ] =
        let ⊩σF = proj₁ (unwrap [F] ⊢Δ [σ])
            ⊩σΣFG = proj₁ (unwrap [ΣFG] ⊢Δ [σ])
            ⊩σt = proj₁ ([t] ⊢Δ [σ])
        in  fst″ ⊩σF ⊩σΣFG ⊩σt

  in  σfst ⊢Δ [σ] ,
      (λ {σ′} [σ′] [σ≡σ′] →
        let [σF] = proj₁ (unwrap [F] ⊢Δ [σ])
            [σΣFG] = proj₁ (unwrap [ΣFG] ⊢Δ [σ])
            [σt≡σ′t] = proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′]
        in  fst-cong″ [σF] [σΣFG] [σt≡σ′t])
