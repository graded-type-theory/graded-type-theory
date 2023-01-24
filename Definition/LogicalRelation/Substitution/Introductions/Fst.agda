{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation
open import Tools.Relation

module Definition.LogicalRelation.Substitution.Introductions.Fst {a ℓ} (M′ : Setoid a ℓ)
                                                                 {{eqrel : EqRelSet M′}} where
open EqRelSet {{...}}
open Setoid M′ using () renaming (Carrier to M)

open import Definition.Untyped M as U hiding (Wk; wk; _∷_)
open import Definition.Untyped.Properties M
open import Definition.Typed M′
open import Definition.Typed.Properties M′
open import Definition.Typed.Weakening M′ as Wk hiding (wk; wkTerm; wkEqTerm)
open import Definition.Typed.RedSteps M′
open import Definition.LogicalRelation M′
open import Definition.LogicalRelation.ShapeView M′
open import Definition.LogicalRelation.Irrelevance M′
open import Definition.LogicalRelation.Properties M′
open import Definition.LogicalRelation.Substitution M′
open import Definition.LogicalRelation.Substitution.Introductions.Pi M′

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    q : M

-- Reducibility of fst with a specific typing derivation
fst′ : ∀ {F G t l l′}
       ([F] : Γ ⊩⟨ l′ ⟩ F)
       ([ΣFG] : Γ ⊩⟨ l ⟩B⟨ BΣ Σₚ q ⟩ Σₚ q ▷ F ▹ G)
       ([t] : Γ ⊩⟨ l ⟩ t ∷ Σ q ▷ F ▹ G / B-intr BΣ! [ΣFG])
       → Γ ⊩⟨ l′ ⟩ fst t ∷ F / [F]
fst′ {Γ = Γ} {q = q} {F = F} {t = t} [F] (noemb [Σ]@(Bᵣ F' G' D ⊢F ⊢G A≡A [F'] [G'] G-ext))
     [t]@(Σₜ p d p≅p prodP propP) with B-PE-injectivity BΣ! BΣ! (whnfRed* (red D) Σₙ)
... | PE.refl , PE.refl , _ =
  let [fstp]′ = proj₁ propP
      [fstp] : Γ ⊩⟨ _ ⟩ fst p ∷ F / [F]
      [fstp] = irrelevanceTerm′ (wk-id F)
                                ([F'] id (wf ⊢F)) [F]
                                [fstp]′
  in  proj₁ (redSubst*Term (fst-subst* (redₜ d) ⊢F ⊢G)
                           [F] [fstp])
fst′ {Γ = Γ} {t = t} {l = l} [F] (emb 0<1 x) [t] = fst′ [F] x [t]

-- Reducibility of fst with a general typing derivation
fst″ : ∀ {F G t l l′}
       ([F] : Γ ⊩⟨ l′ ⟩ F)
       ([ΣFG] : Γ ⊩⟨ l ⟩ Σ q ▷ F ▹ G)
       ([t] : Γ ⊩⟨ l ⟩ t ∷ Σ _ ▷ F ▹ G / [ΣFG])
       → Γ ⊩⟨ l′ ⟩ fst t ∷ F / [F]
fst″ {Γ = Γ} {t = t} {l = l} [F] [ΣFG] [t] =
  let [t]′ = irrelevanceTerm [ΣFG] (B-intr BΣ! (Σ-elim [ΣFG])) [t]
  in  fst′ [F] (Σ-elim [ΣFG]) [t]′

fst-cong′ : ∀ {F G t t′ l l′}
            ([F] : Γ ⊩⟨ l′ ⟩ F)
            ([ΣFG] : Γ ⊩⟨ l ⟩B⟨ BΣ Σₚ q ⟩ Σₚ q ▷ F ▹ G)
            ([t≡t′] : Γ ⊩⟨ l ⟩ t ≡ t′ ∷ Σ q ▷ F ▹ G / B-intr BΣ! [ΣFG])
            → Γ ⊩⟨ l′ ⟩ fst t ≡ fst t′ ∷ F / [F]
fst-cong′ {Γ = Γ} {q = q} {F = F} {G = G} [F]
          [ΣFG]@(noemb [Σ]@(Bᵣ F' G' D ⊢F ⊢G A≡A [F'] [G'] G-ext))
          [t≡t′]@(Σₜ₌ p p′ d d′ prodP prodP′ p≅p′ [t] [t′] prop)
          with B-PE-injectivity BΣ! BΣ! (whnfRed* (red D) Σₙ)
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
            ([ΣFG] : Γ ⊩⟨ l ⟩ Σ q ▷ F ▹ G)
            ([t≡t′] : Γ ⊩⟨ l ⟩ t ≡ t′ ∷ Σ _ ▷ F ▹ G / [ΣFG])
            → Γ ⊩⟨ l′ ⟩ fst t ≡ fst t′ ∷ F / [F]
fst-cong″ {F = F} {G} [F] [ΣFG] [t≡t′] =
  let [t≡t′] = irrelevanceEqTerm [ΣFG] (B-intr BΣ! (Σ-elim [ΣFG])) [t≡t′]
  in  fst-cong′ [F] (Σ-elim [ΣFG]) [t≡t′]

fst-congᵛ : ∀ {F G t t′ l}
            ([Γ] : ⊩ᵛ Γ)
            ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
            ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
            ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Σₚ q ▷ F ▹ G / [Γ] / Σᵛ {F = F} {G} [Γ] [F] [G])
            ([t′] : Γ ⊩ᵛ⟨ l ⟩ t′ ∷ Σₚ q ▷ F ▹ G / [Γ] / Σᵛ {F = F} {G} [Γ] [F] [G])
            ([t≡t′] : Γ ⊩ᵛ⟨ l ⟩ t ≡ t′ ∷ Σ q ▷ F ▹ G / [Γ] / Σᵛ {F = F} {G} [Γ] [F] [G])
          → Γ ⊩ᵛ⟨ l ⟩ fst t ≡ fst t′ ∷ F / [Γ] / [F]
fst-congᵛ {F = F} {G} [Γ] [F] [G] [t] [t′] [t≡t′] ⊢Δ [σ] =
  let [ΣFG] = Σᵛ {F = F} {G} [Γ] [F] [G]
      ⊩σF = proj₁ (unwrap [F] ⊢Δ [σ])
      ⊩σΣFG = proj₁ (unwrap [ΣFG] ⊢Δ [σ])
      ⊩σt≡t′ = [t≡t′] ⊢Δ [σ]
  in  fst-cong″ ⊩σF ⊩σΣFG ⊩σt≡t′

-- Validity of first projection
fstᵛ : ∀ {Γ : Con Term n} {F : Term n} {G t l}
       ([Γ] : ⊩ᵛ Γ)
       ([F] : Γ ⊩ᵛ⟨ l ⟩ F / [Γ])
       ([G] : Γ ∙ F ⊩ᵛ⟨ l ⟩ G / [Γ] ∙ [F])
       ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Σ q ▷ F ▹ G / [Γ] / Σᵛ {F = F} {G} [Γ] [F] [G])
       → Γ ⊩ᵛ⟨ l ⟩ fst t ∷ F / [Γ] / [F]
fstᵛ {Γ = Γ} {F} {G} {t} {l} [Γ] [F] [G] [t] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [ΣFG] = Σᵛ {F = F} {G} [Γ] [F] [G]
      σfst : ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
           → Δ ⊩⟨ l ⟩ subst σ (fst t) ∷ subst σ F / proj₁ (unwrap [F] ⊢Δ [σ])
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
