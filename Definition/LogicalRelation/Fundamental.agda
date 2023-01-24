{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation
open import Tools.Level
open import Tools.Relation

module Definition.LogicalRelation.Fundamental {a ℓ} (M′ : Setoid a ℓ)
                                              {{eqrel : EqRelSet M′}} where
open EqRelSet {{...}}
open Setoid M′ using () renaming (Carrier to M; refl to ≈-refl)

open import Definition.Untyped M hiding (_∷_) renaming (_[_,_] to _[_,,_])
open import Definition.Untyped.Properties M
import Definition.Untyped.BindingType M′ as BT

open import Definition.Typed M′
open import Definition.LogicalRelation M′
open import Definition.LogicalRelation.Irrelevance M′
open import Definition.LogicalRelation.Properties M′
open import Definition.LogicalRelation.Substitution M′
open import Definition.LogicalRelation.Substitution.Properties M′
open import Definition.LogicalRelation.Substitution.Conversion M′
open import Definition.LogicalRelation.Substitution.Reduction M′
open import Definition.LogicalRelation.Substitution.Reflexivity M′
open import Definition.LogicalRelation.Substitution.Introductions M′
open import Definition.LogicalRelation.Substitution.Weakening M′
import Definition.LogicalRelation.Substitution.Irrelevance M′ as S


open import Tools.Fin
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

mutual
  -- Fundamental theorem for contexts.
  valid : ⊢ Γ → ⊩ᵛ Γ
  valid ε = ε
  valid (⊢Γ ∙ A) = let [Γ] , [A] = fundamental A in [Γ] ∙ [A]


  -- Fundamental theorem for types.
  fundamental : ∀ {A} (⊢A : Γ ⊢ A) → Σ (⊩ᵛ Γ) (λ [Γ] → Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ])
  fundamental (ℕⱼ x) = valid x , ℕᵛ (valid x)
  fundamental (Emptyⱼ x) = valid x , Emptyᵛ (valid x)
  fundamental (Unitⱼ x) = valid x , Unitᵛ (valid x)
  fundamental (Uⱼ x) = valid x , Uᵛ (valid x)
  fundamental (Πⱼ_▹_ {F} {G} ⊢F ⊢G) with fundamental ⊢F | fundamental ⊢G
  fundamental (Πⱼ_▹_ {F} {G} ⊢F ⊢G) | [Γ] , [F] | [Γ∙F] , [G] =
    [Γ] , Πᵛ {F = F} {G} [Γ] [F] (S.irrelevance {A = G} [Γ∙F] ([Γ] ∙ [F]) [G])
  fundamental (Σⱼ_▹_ {F} {G} ⊢F ⊢G) with fundamental ⊢F | fundamental ⊢G
  fundamental (Σⱼ_▹_ {F} {G} ⊢F ⊢G) | [Γ] , [F] | [Γ∙F] , [G] =
    [Γ] , Σᵛ {F = F} {G} [Γ] [F] (S.irrelevance {A = G} [Γ∙F] ([Γ] ∙ [F]) [G])
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
  fundamentalEq (trans {A} {B₁} {B} A≡B₁ B₁≡B)
    with fundamentalEq A≡B₁ | fundamentalEq B₁≡B
  fundamentalEq (trans {A} {B₁} {B} A≡B B≡C) | [Γ] , [A] , [B₁] , [A≡B₁]
    | [Γ]₁ , [B₁]₁ , [B] , [B₁≡B] =
      [Γ] , [A] , S.irrelevance {A = B} [Γ]₁ [Γ] [B]
          , (λ ⊢Δ [σ] →
               let [σ]′ = S.irrelevanceSubst [Γ] [Γ]₁ ⊢Δ ⊢Δ [σ]
               in  transEq (proj₁ (unwrap [A] ⊢Δ [σ])) (proj₁ (unwrap [B₁] ⊢Δ [σ]))
                           (proj₁ (unwrap [B] ⊢Δ [σ]′)) ([A≡B₁] ⊢Δ [σ])
                           (irrelevanceEq (proj₁ (unwrap [B₁]₁ ⊢Δ [σ]′))
                                          (proj₁ (unwrap [B₁] ⊢Δ [σ]))
                                          ([B₁≡B] ⊢Δ [σ]′)))
  fundamentalEq (Π-cong {F = F} {H} {G} {E} ⊢F A≡B A≡B₁ p≈p′ q≈q′)
    with fundamentalEq A≡B | fundamentalEq A≡B₁
  fundamentalEq (Π-cong {F = F} {H} {G} {E} ⊢F A≡B A≡B₁ p≈p′ q≈q′) | [Γ] , [F] , [H] , [F≡H]
    | [Γ]₁ , [G] , [E] , [G≡E] =
      let [G]′ = S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]
          [E]′ = S.irrelevanceLift {A = E} {F = F} {H = H} [Γ] [F] [H] [F≡H]
                                   (S.irrelevance {A = E} [Γ]₁ ([Γ] ∙ [F]) [E])
          [G≡E]′ = S.irrelevanceEq {A = G} {B = E} [Γ]₁
                                   ([Γ] ∙ [F]) [G] [G]′ [G≡E]
      in  [Γ]
      ,   Πᵛ {F = F} {G} [Γ] [F] [G]′
      ,   Πᵛ {F = H} {E} [Γ] [H] [E]′
      ,   Π-congᵛ {F = F} {G} {H} {E} [Γ] [F] [G]′ [H] [E]′ [F≡H] [G≡E]′ (BT.Π≋Π p≈p′ q≈q′)
  fundamentalEq (Σ-cong {F = F} {H} {G} {E} ⊢F A≡B A≡B₁ q≈q′)
    with fundamentalEq A≡B | fundamentalEq A≡B₁
  fundamentalEq (Σ-cong {F = F} {H} {G} {E} ⊢F A≡B A≡B₁ q≈q′) | [Γ] , [F] , [H] , [F≡H]
    | [Γ]₁ , [G] , [E] , [G≡E] =
      let [G]′ = S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]
          [E]′ = S.irrelevanceLift {A = E} {F = F} {H = H} [Γ] [F] [H] [F≡H]
                                   (S.irrelevance {A = E} [Γ]₁ ([Γ] ∙ [F]) [E])
          [G≡E]′ = S.irrelevanceEq {A = G} {B = E} [Γ]₁
                                   ([Γ] ∙ [F]) [G] [G]′ [G≡E]
      in  [Γ]
      ,   Σᵛ {F = F} {G} [Γ] [F] [G]′
      ,   Σᵛ {F = H} {E} [Γ] [H] [E]′
      ,   Σ-congᵛ {F = F} {G} {H} {E} [Γ] [F] [G]′ [H] [E]′ [F≡H] [G≡E]′ (BT.Σ≋Σ q≈q′)

  -- Fundamental theorem for variables.
  fundamentalVar : ∀ {A x}
                 → x ∷ A ∈ Γ
                 → ([Γ] : ⊩ᵛ Γ)
                 → ∃ λ ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ])
                 → Γ ⊩ᵛ⟨ ¹ ⟩ var x ∷ A / [Γ] / [A]
  fundamentalVar here (_∙_ {A = A} {l = l} [Γ] [A]) =
    (wrap λ ⊢Δ [σ] →
       let [σA]  = proj₁ (unwrap [A] ⊢Δ (proj₁ [σ]))
           [σA′] = maybeEmb (irrelevance′ (PE.sym (subst-wk A)) [σA])
       in  [σA′]
       ,   (λ [σ′] [σ≡σ′] →
              irrelevanceEq″ (PE.sym (subst-wk A)) (PE.sym (subst-wk A))
                              [σA] [σA′] (proj₂ (unwrap [A] ⊢Δ (proj₁ [σ]))
                                                (proj₁ [σ′]) (proj₁ [σ≡σ′]))))
    , (λ ⊢Δ [σ] →
         let [σA]  = proj₁ (unwrap [A] ⊢Δ (proj₁ [σ]))
             [σA′] = maybeEmb (irrelevance′ (PE.sym (subst-wk A)) [σA])
         in  irrelevanceTerm′ (PE.sym (subst-wk A)) [σA] [σA′] (proj₂ [σ])
         ,   (λ [σ′] [σ≡σ′] → irrelevanceEqTerm′ (PE.sym (subst-wk A))
                                                 [σA] [σA′] (proj₂ [σ≡σ′])))
  fundamentalVar (there {A = A} h) ([Γ] ∙ [B]) =
    (wrap λ ⊢Δ [σ] →
       let [h]   = unwrap (proj₁ (fundamentalVar h [Γ])) ⊢Δ (proj₁ [σ])
           [σA]  = proj₁ [h]
           [σA′] = irrelevance′ (PE.sym (subst-wk A)) [σA]
       in  [σA′]
       ,   (λ [σ′] [σ≡σ′] →
              irrelevanceEq″ (PE.sym (subst-wk A)) (PE.sym (subst-wk A))
                              [σA] [σA′]
                              (proj₂ [h] (proj₁ [σ′]) (proj₁ [σ≡σ′]))))
    , (λ ⊢Δ [σ] →
         let [h]   = unwrap (proj₁ (fundamentalVar h [Γ])) ⊢Δ (proj₁ [σ])
             [σA]  = proj₁ [h]
             [σA′] = irrelevance′ (PE.sym (subst-wk A)) [σA]
             [h′] = (proj₂ (fundamentalVar h [Γ])) ⊢Δ (proj₁ [σ])
         in  irrelevanceTerm′ (PE.sym (subst-wk A)) [σA] [σA′] (proj₁ [h′])
         ,   (λ [σ′] [σ≡σ′] →
                irrelevanceEqTerm′ (PE.sym (subst-wk A)) [σA] [σA′]
                                   (proj₂ [h′] (proj₁ [σ′]) (proj₁ [σ≡σ′]))))

  -- Fundamental theorem for terms.
  fundamentalTerm : ∀ {A t} → Γ ⊢ t ∷ A
    → ∃ λ ([Γ] : ⊩ᵛ Γ)
    → ∃ λ ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ])
    → Γ ⊩ᵛ⟨ ¹ ⟩ t ∷ A / [Γ] / [A]
  fundamentalTerm (ℕⱼ x) = valid x , Uᵛ (valid x) , ℕᵗᵛ (valid x)
  fundamentalTerm (Emptyⱼ x) = valid x , Uᵛ (valid x) , Emptyᵗᵛ (valid x)
  fundamentalTerm (Unitⱼ x) = valid x , Uᵛ (valid x) , Unitᵗᵛ (valid x)
  fundamentalTerm (Πⱼ_▹_ {F = F} {G} ⊢F ⊢G)
    with fundamentalTerm ⊢F | fundamentalTerm ⊢G
  ... | [Γ] , [U] , [F]ₜ | [Γ]₁ , [U]₁ , [G]ₜ =
    let [F]   = univᵛ {A = F} [Γ] [U] [F]ₜ
        [U]′  = S.irrelevance {A = U} [Γ]₁ ([Γ] ∙ [F]) [U]₁
        [F]ₜ′ = S.irrelevanceTerm {A = U} {t = F} [Γ] [Γ] [U] (Uᵛ [Γ]) [F]ₜ
        [G]ₜ′ = S.irrelevanceTerm {A = U} {t = G} [Γ]₁ ([Γ] ∙ [F]) [U]₁ [U]′ [G]ₜ
    in  [Γ] , [U]
    ,   S.irrelevanceTerm {A = U} {t = Π _ , _ ▷ F ▹ G} [Γ] [Γ] (Uᵛ [Γ]) [U]
                          (Πᵗᵛ {F = F} {G} [Γ] [F] [U]′ [F]ₜ′ [G]ₜ′)
  fundamentalTerm (Σⱼ_▹_ {F = F} {G} ⊢F ⊢G)
    with fundamentalTerm ⊢F | fundamentalTerm ⊢G
  ... | [Γ] , [U] , [F]ₜ | [Γ]₁ , [U]₁ , [G]ₜ =
    let [F]   = univᵛ {A = F} [Γ] [U] [F]ₜ
        [U]′  = S.irrelevance {A = U} [Γ]₁ ([Γ] ∙ [F]) [U]₁
        [F]ₜ′ = S.irrelevanceTerm {A = U} {t = F} [Γ] [Γ] [U] (Uᵛ [Γ]) [F]ₜ
        [G]ₜ′ = S.irrelevanceTerm {A = U} {t = G} [Γ]₁ ([Γ] ∙ [F]) [U]₁ [U]′ [G]ₜ
    in  [Γ] , [U]
    ,   S.irrelevanceTerm {A = U} {t = Σ _ ▷ F ▹ G} [Γ] [Γ] (Uᵛ [Γ]) [U]
                          (Σᵗᵛ {F = F} {G} [Γ] [F] [U]′ [F]ₜ′ [G]ₜ′)
  fundamentalTerm (var ⊢Γ x∷A) = valid ⊢Γ , fundamentalVar x∷A (valid ⊢Γ)
  fundamentalTerm (lamⱼ {F = F} {G} {t} ⊢F ⊢t)
    with fundamental ⊢F | fundamentalTerm ⊢t
  ... | [Γ] , [F] | [Γ]₁ , [G] , [t] =
    let [G]′ = S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]
        [t]′ = S.irrelevanceTerm {A = G} {t = t} [Γ]₁ ([Γ] ∙ [F]) [G] [G]′ [t]
    in  [Γ] , Πᵛ {F = F} {G} [Γ] [F] [G]′
    ,   lamᵛ {F = F} {G} {t} [Γ] [F] [G]′ [t]′
  fundamentalTerm (_∘ⱼ_ {g = g} {a} {F} {G} Dt Du)
    with fundamentalTerm Dt | fundamentalTerm Du
  ... | [Γ] , [ΠFG] , [t] | [Γ]₁ , [F] , [u] =
    let [ΠFG]′ = S.irrelevance {A = Π _ , _ ▷ F ▹ G} [Γ] [Γ]₁ [ΠFG]
        [t]′ = S.irrelevanceTerm {A = Π _ , _ ▷ F ▹ G} {t = g} [Γ] [Γ]₁ [ΠFG] [ΠFG]′ [t]
        [G[t]] = substSΠ {F = F} {G} {a} BΠ! [Γ]₁ [F] [ΠFG]′ [u]
        [t∘u] = appᵛ {F = F} {G} {g} {a} [Γ]₁ [F] [ΠFG]′ [t]′ [u] ≈-refl
    in  [Γ]₁ , [G[t]] , [t∘u]
  fundamentalTerm (prodⱼ {F = F} {G} {t} {u} ⊢F ⊢G ⊢t ⊢u) with
    fundamentalTerm ⊢t | fundamental ⊢G | fundamentalTerm ⊢u
  ... | [Γ] , [F] , [t] | [Γ]₁ , [G] | [Γ]₂ , [Gt] , [u] =
    let [G]′ = S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]
        [u]′ = S.irrelevanceTerm {A = G [ t ]} {t = u} [Γ]₂ [Γ] [Gt] (substS {F = F} {G} [Γ] [F] [G]′ [t]) [u]
    in  [Γ] , Σᵛ {F = F} {G} [Γ] [F] [G]′ , prodᵛ {F = F} {G} {t} {u} [Γ] [F] [G]′ [t] [u]′
  fundamentalTerm (fstⱼ {F = F} {G} {t} ⊢F ⊢G ⊢t) with
    fundamental ⊢F | fundamental ⊢G | fundamentalTerm ⊢t
  ... | [Γ] , [F] | [Γ]₁ , [G]₁ | [Γ]₂ , [ΣFG]₂ , [t]₂ =
    let [G] = S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]₁

        [t] = S.irrelevanceTerm {A = Σ _ ▷ F ▹ G} {t = t} [Γ]₂ [Γ]
                                [ΣFG]₂ (Σᵛ {F = F} {G} [Γ] [F] [G]) [t]₂
        [fst] = fstᵛ {F = F} {G} {t} [Γ] [F] [G] [t]
    in  [Γ] , [F] , [fst]
  fundamentalTerm (sndⱼ {F = F} {G} {t} ⊢F ⊢G ⊢t) with
    fundamental ⊢F | fundamental ⊢G | fundamentalTerm ⊢t
  ... | [Γ] , [F] | [Γ]₁ , [G]₁ | [Γ]₂ , [ΣFG]₂ , [t]₂ =
    let [G] = S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]₁

        [t] = S.irrelevanceTerm {A = Σ _ ▷ F ▹ G} {t = t} [Γ]₂ [Γ]
                                [ΣFG]₂ (Σᵛ {F = F} {G} [Γ] [F] [G]) [t]₂
        [fst] = fstᵛ {F = F} {G} {t} [Γ] [F] [G] [t]
        [Gfst] = substS {F = F} {G} [Γ] [F] [G] [fst]
        [snd] = sndᵛ {F = F} {G} [Γ] [F] [G] [t]
    in  [Γ] , [Gfst] , [snd]
  fundamentalTerm (zeroⱼ x) = valid x , ℕᵛ (valid x) , zeroᵛ {l = ¹} (valid x)
  fundamentalTerm (sucⱼ {n} t) with fundamentalTerm t
  fundamentalTerm (sucⱼ {n} t) | [Γ] , [ℕ] , [n] =
    [Γ] , [ℕ] , sucᵛ {n = n} [Γ] [ℕ] [n]
  fundamentalTerm (natrecⱼ {G = G} {s} {z} {n} ⊢G ⊢z ⊢s ⊢n)
    with fundamental ⊢G | fundamentalTerm ⊢z | fundamentalTerm ⊢s
       | fundamentalTerm ⊢n
  ... | [Γ] , [G] | [Γ]₁ , [G₀] , [z] | [Γ]₂ , [G₊] , [s] | [Γ]₃ , [ℕ] , [n] =
    let [Γ]′ = [Γ]₃
        [G]′ = S.irrelevance {A = G} [Γ] ([Γ]′ ∙ [ℕ]) [G]
        [G₀]′ = S.irrelevance {A = G [ zero ]} [Γ]₁ [Γ]′ [G₀]
        [G₊]′ = S.irrelevance {A = wk1 (G [ (suc (var x0)) ]↑)} [Γ]₂ ([Γ]′ ∙ [ℕ] ∙ [G]′) [G₊]
        [Gₙ]′ = substS {F = ℕ} {G = G} {t = n} [Γ]′ [ℕ] [G]′ [n]
        [z]′ = S.irrelevanceTerm {A = G [ zero ]} {t = z} [Γ]₁ [Γ]′
                                 [G₀] [G₀]′ [z]
        [s]′ = S.irrelevanceTerm {A = wk1 (G [ (suc (var x0)) ]↑)} {t = s} [Γ]₂ ([Γ]′ ∙ [ℕ] ∙ [G]′) [G₊] [G₊]′ [s]
    in [Γ]′ , [Gₙ]′
    , (natrecᵛ {F = G} {z} {s} {n} [Γ]′ [ℕ] [G]′ [G₀]′ [G₊]′ [Gₙ]′ [z]′ [s]′ [n])
  fundamentalTerm (Emptyrecⱼ {A = A} {n} ⊢A ⊢n)
    with fundamental ⊢A | fundamentalTerm ⊢n
  ... | [Γ] , [A] | [Γ]′ , [Empty] , [n] =
    let [A]′ = S.irrelevance {A = A} [Γ] [Γ]′ [A]
    in [Γ]′ , [A]′ , Emptyrecᵛ {F = A} {n} [Γ]′ [Empty] [A]′ [n]
  fundamentalTerm (starⱼ x) = valid x , Unitᵛ (valid x) , starᵛ {l = ¹} (valid x)
  fundamentalTerm (conv {t} {A} {B} ⊢t A′≡A)
    with fundamentalTerm ⊢t | fundamentalEq A′≡A
  fundamentalTerm (conv {t} {A} {B} ⊢t A′≡A) | [Γ] , [A′] , [t]
    | [Γ]₁ , [A′]₁ , [A] , [A′≡A] =
      let [Γ]′ = [Γ]₁
          [t]′ = S.irrelevanceTerm {A = A} {t = t} [Γ] [Γ]′ [A′] [A′]₁ [t]
      in  [Γ]′ , [A]
      ,   convᵛ {t = t} {A} {B} [Γ]′ [A′]₁ [A] [A′≡A] [t]′
  fundamentalTerm (prodrecⱼ ⊢F ⊢G ⊢A ⊢t ⊢u)
    with fundamental ⊢F | fundamental ⊢G | fundamental ⊢A | fundamentalTerm ⊢t | fundamentalTerm ⊢u
  fundamentalTerm (prodrecⱼ {q = q} {p = p} {t = t} {u} {F} {G} {A} ⊢F ⊢G ⊢t ⊢A ⊢u)
    | [Γ] , [F] | [Γ]₁ , [G] | [Γ]₂ , [A]
    | [Γ]₃ , [Σ] , [t] | [Γ]₄ , [A₊] , [u] =
      let [G]′ = S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]
          [Σ]′ = S.irrelevance {A = Σ q ▷ F ▹ G} [Γ]₃ [Γ] [Σ]
          [A]′ = S.irrelevance {A = A} [Γ]₂ ([Γ] ∙ [Σ]′) [A]
          [A₊]′ = S.irrelevance {A = A [ prod! (var (x0 +1)) (var x0) ]↑²}
                                [Γ]₄ ([Γ] ∙ [F] ∙ [G]′) [A₊]
          [t]′ = S.irrelevanceTerm {A = Σ q ▷ F ▹ G} {t = t} [Γ]₃ [Γ] [Σ] [Σ]′ [t]
          [u]′ = S.irrelevanceTerm {A = A [ prod! (var (x0 +1)) (var x0) ]↑²} {t = u}
                                   [Γ]₄ ([Γ] ∙ [F] ∙ [G]′) [A₊] [A₊]′ [u]
          [Aₜ] = substS {F = Σ q ▷ F ▹ G} {A} {t} [Γ] [Σ]′ [A]′ [t]′
          [prodrec] = prodrecᵛ {p = p} {F = F} {G} {A} {t} {u} [Γ] [F] [G]′ [Σ]′ [A]′ [A₊]′ [Aₜ] [t]′ [u]′
      in  [Γ] , [Aₜ] , [prodrec]

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
  fundamentalTermEq (trans {t} {u} {r} {A} t≡u u≡t′)
    with fundamentalTermEq t≡u | fundamentalTermEq u≡t′
  fundamentalTermEq (trans {t} {u} {r} {A} t≡u u≡t′)
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
  fundamentalTermEq (conv {A} {B} {t} {u} t≡u A′≡A)
    with fundamentalTermEq t≡u | fundamentalEq A′≡A
  fundamentalTermEq (conv {A} {B} {t} {u} t≡u A′≡A)
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
  fundamentalTermEq (Π-cong {E = E} {F} {G} {H} ⊢F F≡H G≡E p≈p′ q≈q′)
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
          (Πᵗᵛ {F = F} {G} [Γ] [F] [U]₁′ [F]ₜ′ [G]ₜ′)
          (Πᵗᵛ {F = H} {E} [Γ] [H] [U]₂′ [H]ₜ′ [E]ₜ′)
          (Π-congᵗᵛ {F = F} {G} {H} {E} [Γ] [F] [H] [U]₁′ [U]₂′
                    [F]ₜ′ [G]ₜ′ [H]ₜ′ [E]ₜ′ [F≡H]ₜ′ [G≡E]ₜ′ (BT.Π≋Π p≈p′ q≈q′))
  fundamentalTermEq (Σ-cong {E = E} {F = F} {G = G} {H = H} ⊢F F≡H G≡E q≈q′)
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
          (Σᵗᵛ {F = F} {G} [Γ] [F] [U]₁′ [F]ₜ′ [G]ₜ′)
          (Σᵗᵛ {F = H} {E} [Γ] [H] [U]₂′ [H]ₜ′ [E]ₜ′)
          (Σ-congᵗᵛ {F = F} {G} {H} {E} [Γ] [F] [H] [U]₁′ [U]₂′
                    [F]ₜ′ [G]ₜ′ [H]ₜ′ [E]ₜ′ [F≡H]ₜ′ [G≡E]ₜ′ (BT.Σ≋Σ q≈q′))
  fundamentalTermEq (app-cong {a = a} {b} {f} {g} {F} {G} f≡g a≡b p≈p₁ p≈p₂)
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
                            (appᵛ {F = F} {G} {f} {a} [Γ]₁ [F] [ΠFG]′ [f]′ [a] p≈p₁)
                            (conv₂ᵛ {t = g ∘ b} {G [ a ]} {G [ b ]} [Γ]₁
                                    [G[a]] [G[b]] [G[a]≡G[b]]
                                    (appᵛ {F = F} {G} {g} {b}
                                          [Γ]₁ [F] [ΠFG]′ [g]′ [b] p≈p₂))
                            (app-congᵛ {F = F} {G} {f} {g} {a} {b}
                                       [Γ]₁ [F] [ΠFG]′ [f≡g]′ [a]
                                       [b] [a≡b] p≈p₁ p≈p₂)
  fundamentalTermEq (β-red {p = p} {p′ = q} {a = a} {b} {F} {G} ⊢F ⊢G ⊢b ⊢a p≈p′)
    with fundamental ⊢F | fundamentalTerm ⊢b | fundamentalTerm ⊢a
  ... | [Γ] , [F] | [Γ]₁ , [G] , [b] | [Γ]₂ , [F]₁ , [a] =
    let [G]′ = S.irrelevance {A = G} [Γ]₁ ([Γ]₂ ∙ [F]₁) [G]
        [b]′ = S.irrelevanceTerm {A = G} {t = b} [Γ]₁ ([Γ]₂ ∙ [F]₁) [G] [G]′ [b]
        [G[a]] = substS {F = F} {G} {a} [Γ]₂ [F]₁ [G]′ [a]
        [b[a]] = substSTerm {F = F} {G} {a} {b} [Γ]₂ [F]₁ [G]′ [b]′ [a]
        [lam] , [eq] =
          redSubstTermᵛ {A = G [ a ]} {lam p b ∘⟨ q ⟩ a} {b [ a ]} [Γ]₂
            (λ {_} {Δ} {σ} ⊢Δ [σ] →
               let [liftσ] = liftSubstS {F = F} [Γ]₂ ⊢Δ [F]₁ [σ]
                   ⊢σF = escape (proj₁ (unwrap [F]₁ ⊢Δ [σ]))
                   ⊢σG = escape (proj₁ (unwrap [G]′ (⊢Δ ∙ ⊢σF) (liftSubstS {F = F} [Γ]₂ ⊢Δ [F]₁ [σ])))
                   ⊢σb = escapeTerm (proj₁ (unwrap [G]′ (⊢Δ ∙ ⊢σF) [liftσ]))
                                       (proj₁ ([b]′ (⊢Δ ∙ ⊢σF) [liftσ]))
                   ⊢σa = escapeTerm (proj₁ (unwrap [F]₁ ⊢Δ [σ]))
                                       (proj₁ ([a] ⊢Δ [σ]))
               in  PE.subst₂ (λ x y → _ ⊢ (lam _ (subst (liftSubst σ) b))
                                          ∘ (subst σ a) ⇒ x ∷ y)
                             (PE.sym (singleSubstLift b a))
                             (PE.sym (singleSubstLift G a))
                             (β-red ⊢σF ⊢σG ⊢σb ⊢σa p≈p′))
                         [G[a]] [b[a]]
    in  [Γ]₂ , modelsTermEq [G[a]] [lam] [b[a]] [eq]
  fundamentalTermEq (η-eq {f = f} {g} {F} {G} ⊢F ⊢t ⊢t′ t≡t′) with
    fundamental ⊢F | fundamentalTerm ⊢t |
    fundamentalTerm ⊢t′ | fundamentalTermEq (t≡t′ ≈-refl ≈-refl)
  ... | [Γ] , [F] | [Γ]₁ , [ΠFG] , [t] | [Γ]₂ , [ΠFG]₁ , [t′]
      | [Γ]₃ , modelsTermEq [G] [t0] [t′0] [t0≡t′0] =
    let [F]′ = S.irrelevance {A = F} [Γ] [Γ]₁ [F]
        [G]′ = S.irrelevance {A = G} [Γ]₃ ([Γ]₁ ∙ [F]′) [G]
        [t′]′ = S.irrelevanceTerm {A = Π _ , _ ▷ F ▹ G} {t = g}
                                  [Γ]₂ [Γ]₁ [ΠFG]₁ [ΠFG] [t′]
        [ΠFG]″ = Πᵛ {F = F} {G} [Γ]₁ [F]′ [G]′
        [t]″ = S.irrelevanceTerm {A = Π _ , _ ▷ F ▹ G} {t = f}
                                  [Γ]₁ [Γ]₁ [ΠFG] [ΠFG]″ [t]
        [t′]″ = S.irrelevanceTerm {A = Π _ , _ ▷ F ▹ G} {t = g}
                                   [Γ]₂ [Γ]₁ [ΠFG]₁ [ΠFG]″ [t′]
        [t0≡t′0]′ = S.irrelevanceEqTerm {A = G} {t = wk1 f ∘ var x0}
                                        {u = wk1 g ∘ var x0}
                                        [Γ]₃ ([Γ]₁ ∙ [F]′) [G] [G]′ [t0≡t′0]
        [t≡t′] =  η-eqᵛ {f = f} {g} {F} {G} [Γ]₁ [F]′ [G]′ [t]″ [t′]″ ≈-refl ≈-refl [t0≡t′0]′
        [t≡t′]′ = S.irrelevanceEqTerm {A = Π _ , _ ▷ F ▹ G} {t = f} {u = g}
                                      [Γ]₁ [Γ]₁ [ΠFG]″ [ΠFG] [t≡t′]
    in  [Γ]₁ , modelsTermEq [ΠFG] [t] [t′]′ [t≡t′]′
  fundamentalTermEq (suc-cong x) with fundamentalTermEq x
  fundamentalTermEq (suc-cong {t} {u} x)
    | [Γ] , modelsTermEq [A] [t] [u] [t≡u] =
      let [suct] = sucᵛ {n = t} [Γ] [A] [t]
          [sucu] = sucᵛ {n = u} [Γ] [A] [u]
      in  [Γ] , modelsTermEq [A] [suct] [sucu]
                             (λ ⊢Δ [σ] →
                                sucEqTerm (proj₁ (unwrap [A] ⊢Δ [σ])) ([t≡u] ⊢Δ [σ]))
  fundamentalTermEq (natrec-cong {z = z} {z′} {s} {s′} {n} {n′} {F} {F′}
                                 ⊢F F≡F′ z≡z′ s≡s′ n≡n′ p≈p′ r≈r′)
    with fundamentalEq F≡F′ |
         fundamentalTermEq z≡z′      |
         fundamentalTermEq s≡s′      |
         fundamentalTermEq n≡n′
  fundamentalTermEq (natrec-cong {p = p} {r = r} {z = z} {z′ = z′} {s = s} {s′ = s′}
                                 {n = n} {n′ = n′} {F = F} {F′ = F′}
                                 ⊢F F≡F′ z≡z′ s≡s′ n≡n′ p≈p′ r≈r′) |
    [Γ]  , [F] , [F′] , [F≡F′] |
    [Γ]₁ , modelsTermEq [F₀] [z] [z′] [z≡z′] |
    [Γ]₂ , modelsTermEq [F₊] [s] [s′] [s≡s′] |
    [Γ]₃ , modelsTermEq [ℕ] [n] [n′] [n≡n′] =
      let sType = wk1 (F [ suc (var x0) ]↑)
          s′Type = wk1 (F′ [ suc (var x0) ]↑)
          [0] = S.irrelevanceTerm {l = ¹} {A = ℕ} {t = zero}
                                  [Γ]₃ [Γ]₃ (ℕᵛ [Γ]₃) [ℕ] (zeroᵛ {l = ¹} [Γ]₃)
          [F]′ = S.irrelevance {A = F} [Γ] ([Γ]₃ ∙ [ℕ]) [F]
          [F₀]′ = S.irrelevance {A = F [ zero ]} [Γ]₁ [Γ]₃ [F₀]
          [F₊]′ = S.irrelevance {A = sType} [Γ]₂ ([Γ]₃ ∙ [ℕ] ∙ [F]′) [F₊]
          [Fₙ]′ = substS {F = ℕ} {F} {n} [Γ]₃ [ℕ] [F]′ [n]
          [F′]′ = S.irrelevance {A = F′} [Γ] ([Γ]₃ ∙ [ℕ]) [F′]
          [F₀]″ = substS {F = ℕ} {F} {zero} [Γ]₃ [ℕ] [F]′ [0]
          [F′₀]′ = substS {F = ℕ} {F′} {zero} [Γ]₃ [ℕ] [F′]′ [0]
          [ℕ]′ , [x0] = fundamentalVar {A = ℕ} here ([Γ]₃ ∙ [ℕ])
          [↑ℕ] = wk1ᵛ {A = ℕ} {F = ℕ} [Γ]₃ [ℕ] [ℕ]
          [x0]′ = S.irrelevanceTerm {A = ℕ} {t = var x0}
                                    (_∙_ {A = ℕ} [Γ]₃ [ℕ]) (_∙_ {A = ℕ} [Γ]₃ [ℕ])
                                    [ℕ]′ [↑ℕ] (λ {k Δ σ} → [x0] {σ = σ})
          [sucx0] = sucᵛ {n = var x0} (_∙_ {A = ℕ} [Γ]₃ [ℕ]) [↑ℕ] (λ {k Δ σ} → [x0]′ {σ = σ})
          [Fₓ] = subst↑S {F = ℕ} {G = F} {t = suc (var x0)} [Γ]₃ [ℕ] [F]′
                         (λ {k Δ σ} → [sucx0] {σ = σ})
          [F′ₓ] = subst↑S {F = ℕ} {G = F′} {t = suc (var x0)} [Γ]₃ [ℕ] [F′]′
                          (λ {k Δ σ} → [sucx0] {σ = σ})
          [F′₊]′ = wk1ᵛ {A = F′ [ suc (var x0) ]↑} {F = F′} (_∙_ {A = ℕ} [Γ]₃ [ℕ]) [F′]′ [F′ₓ]
          [F′ₙ′]′ = substS {F = ℕ} {F′} {n′} [Γ]₃ [ℕ] [F′]′ [n′]
          [ℕ≡ℕ] = reflᵛ {A = ℕ} [Γ]₃ [ℕ]
          [0≡0] = reflᵗᵛ {A = ℕ} {zero} [Γ]₃ [ℕ] [0]
          [F≡F′]′ = S.irrelevanceEq {A = F} {B = F′}
                                    [Γ] ([Γ]₃ ∙ [ℕ]) [F] [F]′ [F≡F′]
          [F₀≡F′₀] = substSEq {F = ℕ} {ℕ} {F} {F′} {zero} {zero}
                              [Γ]₃ [ℕ] [ℕ] [ℕ≡ℕ]
                              [F]′ [F′]′ [F≡F′]′ [0] [0] [0≡0]
          [F₀≡F′₀]′ = S.irrelevanceEq {A = F [ zero ]} {B = F′ [ zero ]}
                                      [Γ]₃ [Γ]₃ [F₀]″ [F₀]′ [F₀≡F′₀]
          [Fₓ≡F′ₓ] = subst↑SEq {F = ℕ} {G = F} {G′ = F′}
                               {t = suc (var x0)} {t′ = suc (var x0)}
                               [Γ]₃ [ℕ] [F]′ [F′]′ [F≡F′]′
                               (λ {k Δ σ} → [sucx0] {σ = σ})
                               (λ {k Δ σ} → [sucx0] {σ = σ})
                               (λ {k Δ σ} → reflᵗᵛ {A = ℕ} {t = suc (var x0)}
                                                   (_∙_ {A = ℕ} [Γ]₃ [ℕ]) [ℕ]′
                                                   (λ {k Δ σ} →  [sucx0] {σ = σ}) {σ = σ})
          [F₊≡F′₊] = wk1Eqᵛ {A = F [ suc (var x0) ]↑} {B = F′ [ suc (var x0) ]↑} {F = F}
                            (_∙_ {A = ℕ} [Γ]₃ [ℕ]) [F]′ [Fₓ] [Fₓ≡F′ₓ]
          [F₊≡F′₊]′ = S.irrelevanceEq {A = sType} {B = s′Type}
                                      ((_∙_ {A = F} (_∙_ {A = ℕ} [Γ]₃ [ℕ]) [F]′))
                                      (_∙_ {A = F} (_∙_ {A = ℕ} [Γ]₃ [ℕ]) [F]′)
                                      (wk1ᵛ {A = F [ suc (var x0) ]↑} {F = F} (_∙_ {A = ℕ} [Γ]₃ [ℕ]) [F]′ [Fₓ])
                                      [F₊]′ [F₊≡F′₊]
          [F₊≡F′₊]″ = wk1Eqᵛ {A = F [ suc (var x0) ]↑} {B = F′ [ suc (var x0) ]↑} {F = F′}
                             (_∙_ {A = ℕ} [Γ]₃ [ℕ]) [F′]′ [Fₓ] [Fₓ≡F′ₓ]
          [F₊≡F′₊]‴ = S.irrelevanceEq {A = sType} {B = s′Type}
                                      ((_∙_ {A = F′} (_∙_ {A = ℕ} [Γ]₃ [ℕ]) [F′]′))
                                      (_∙_ {A = F′} (_∙_ {A = ℕ} [Γ]₃ [ℕ]) [F′]′)
                                      (wk1ᵛ {A = F [ suc (var x0) ]↑} {F = F′} (_∙_ {A = ℕ} [Γ]₃ [ℕ]) [F′]′ [Fₓ])
                                      (S.irrelevanceLift {A = sType} {F = F} {H = F′}
                                                         (_∙_ {A = ℕ} [Γ]₃ [ℕ])
                                                         [F]′ [F′]′ [F≡F′]′ [F₊]′) [F₊≡F′₊]″
          [Fₙ≡F′ₙ′]′ = substSEq {F = ℕ} {ℕ} {F} {F′} {n} {n′}
                                [Γ]₃ [ℕ] [ℕ] [ℕ≡ℕ] [F]′ [F′]′ [F≡F′]′
                                [n] [n′] [n≡n′]
          [z]′ = S.irrelevanceTerm {A = F [ zero ]} {t = z}
                                   [Γ]₁ [Γ]₃ [F₀] [F₀]′ [z]
          [z′]′ = convᵛ {t = z′} {F [ zero ]} {F′ [ zero ]}
                        [Γ]₃ [F₀]′ [F′₀]′ [F₀≡F′₀]′
                        (S.irrelevanceTerm {A = F [ zero ]} {t = z′}
                                           [Γ]₁ [Γ]₃ [F₀] [F₀]′ [z′])
          [z≡z′]′ = S.irrelevanceEqTerm {A = F [ zero ]} {t = z} {u = z′}
                                        [Γ]₁ [Γ]₃ [F₀] [F₀]′ [z≡z′]
          [s]′ = S.irrelevanceTerm {A = sType} {t = s} [Γ]₂ ([Γ]₃ ∙ [ℕ] ∙ [F]′) [F₊] [F₊]′ [s]
          [s′]′ = S.irrelevanceTerm {A = sType} {t = s′} [Γ]₂
                                    (_∙_ {A = F} (_∙_ {A = ℕ} [Γ]₃ [ℕ]) [F]′)
                                    [F₊] [F₊]′ [s′]
          [s′]″ = S.irrelevanceTermLift {A = sType} {F = F} {H = F′} {t = s′}
                                        (_∙_ {A = ℕ} [Γ]₃ [ℕ]) [F]′ [F′]′ [F≡F′]′ [F₊]′ [s′]′
          [s′]″ = convᵛ {t = s′} {sType} {s′Type} (_∙_ {A = F′} (_∙_ {A = ℕ} [Γ]₃ [ℕ]) [F′]′)
                        (S.irrelevanceLift {A = sType} {F = F} {H = F′} (_∙_ {A = ℕ} [Γ]₃ [ℕ]) [F]′ [F′]′ [F≡F′]′ [F₊]′)
                        [F′₊]′ [F₊≡F′₊]‴ [s′]″
          [s≡s′]′ = S.irrelevanceEqTerm {A = sType} {t = s} {u = s′}
                                        [Γ]₂ ([Γ]₃ ∙ [ℕ] ∙ [F]′) [F₊] [F₊]′ [s≡s′]
      in  [Γ]₃
      ,   modelsTermEq [Fₙ]′
                       (natrecᵛ {F = F} {z = z} {s = s} {n = n}
                                [Γ]₃ [ℕ] [F]′ [F₀]′ [F₊]′ [Fₙ]′ [z]′ [s]′ [n])
                       (conv₂ᵛ {t = natrec _ _ F′ z′ s′ n′} {F [ n ]} {F′ [ n′ ]}
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
                                     [s]′ [s′]″ [s≡s′]′ [n] [n′] [n≡n′] p≈p′ r≈r′)
  fundamentalTermEq (natrec-zero {z} {s} {F} ⊢F ⊢z ⊢s)
    with fundamental ⊢F | fundamentalTerm ⊢z | fundamentalTerm ⊢s
  fundamentalTermEq (natrec-zero {p = p} {r = r} {z = z} {s = s} {F = F} ⊢F ⊢z ⊢s) | [Γ] , [F]
    | [Γ]₁ , [F₀] , [z] | [Γ]₂ , [F₊] , [s] =
    let sType = wk1 (F [ suc (var x0) ]↑)
        [Γ]′ = [Γ]₁
        [ℕ]′ = ℕᵛ {l = ¹} [Γ]′
        [F]′ = S.irrelevance {A = F} [Γ] ([Γ]′ ∙ [ℕ]′) [F]
        [ΓℕF]′ = _∙_ {A = F} (_∙_ {A = ℕ} [Γ]′ [ℕ]′) [F]′
        [F₊]′ = S.irrelevance {A = sType} [Γ]₂ [ΓℕF]′ [F₊]
        [s]′ = S.irrelevanceTerm {A = sType} {t = s} [Γ]₂ [ΓℕF]′ [F₊] [F₊]′ [s]
        d , r =
          redSubstTermᵛ {A = F [ zero ]} {natrec p r F z s zero} {z} [Γ]′
            (λ {_} {Δ} {σ} ⊢Δ [σ] →
               let ⊢ℕ = escape (proj₁ (unwrap [ℕ]′ ⊢Δ [σ]))
                   ⊢F = escape (proj₁ (unwrap [F]′ (⊢Δ ∙ ⊢ℕ)
                                               (liftSubstS {F = ℕ}
                                                           [Γ]′ ⊢Δ [ℕ]′ [σ])))
                   ⊢z = PE.subst (λ x → Δ ⊢ subst σ z ∷ x)
                                 (singleSubstLift F zero)
                                 (escapeTerm (proj₁ (unwrap [F₀] ⊢Δ [σ]))
                                                (proj₁ ([z] ⊢Δ [σ])))
                   ⊢Δℕ = ⊢Δ ∙ ℕⱼ ⊢Δ
                   [σ⇑⇑] = liftSubstS {F = F} (_∙_ {A = ℕ} [Γ]′ [ℕ]′) ⊢Δℕ [F]′
                                      (liftSubstS {F = ℕ} [Γ]′ ⊢Δ [ℕ]′ [σ])
                   ⊢s = PE.subst (λ x → Δ ∙ ℕ ∙ (subst (liftSubst σ) F) ⊢ subst (liftSubstn σ 2) s ∷ x)
                                 (natrecSucCase σ F)
                                 (escapeTerm (proj₁ (unwrap [F₊]′ (⊢Δℕ ∙ ⊢F) [σ⇑⇑]))
                                             (proj₁ ([s]′ (⊢Δℕ ∙ ⊢F) [σ⇑⇑])))
               in PE.subst (λ x → Δ ⊢ subst σ (natrec p r F z s zero)
                                    ⇒ subst σ z ∷ x)
                           (PE.sym (singleSubstLift F zero))
                           (natrec-zero ⊢F ⊢z ⊢s))
                        [F₀] [z]
    in  [Γ]′ , modelsTermEq [F₀] d [z] r
  fundamentalTermEq {Γ = Γ} (natrec-suc {p = p} {r = r} {n = n} {z = z} {s = s} {F = F} ⊢n ⊢F ⊢z ⊢s)
    with fundamentalTerm ⊢n | fundamental ⊢F
       | fundamentalTerm ⊢z | fundamentalTerm ⊢s
  ... | [Γ] , [ℕ] , [n] | [Γ]₁ , [F] | [Γ]₂ , [F₀] , [z] | [Γ]₃ , [F₊] , [s] =
    let [sucn] = sucᵛ {n = n} [Γ] [ℕ] [n]
        [F₀]′ = S.irrelevance {A = F [ zero ]} [Γ]₂ [Γ] [F₀]
        [z]′ = S.irrelevanceTerm {A = F [ zero ]} {t = z}
                                 [Γ]₂ [Γ] [F₀] [F₀]′ [z]
        [F]′ = S.irrelevance {A = F} [Γ]₁ ([Γ] ∙ [ℕ]) [F]
        [F[sucn]] = substS {F = ℕ} {F} {suc n} [Γ] [ℕ] [F]′ [sucn]
        [Fₙ]′ = substS {F = ℕ} {F} {n} [Γ] [ℕ] [F]′ [n]
        [ΓℕF] = _∙_ {A = F} (_∙_ {A = ℕ} [Γ] [ℕ]) [F]′
        [F₊]′ = S.irrelevance {A = wk1 (F [ suc (var x0) ]↑)} [Γ]₃ [ΓℕF] [F₊]
        [s]′ = S.irrelevanceTerm {A = wk1 (F [ suc (var x0) ]↑)} {t = s} [Γ]₃ [ΓℕF] [F₊] [F₊]′ [s]
        [natrecₙ] = natrecᵛ {p = p} {r = r} {F = F} {z} {s} {n}
                            [Γ] [ℕ] [F]′ [F₀]′ [F₊]′ [Fₙ]′ [z]′ [s]′ [n]
        [s₊] : Γ ⊩ᵛ⟨ ¹ ⟩ subst (consSubst (consSubst idSubst n) (natrec p r F z s n)) s ∷ F [ suc n ] / [Γ] / [F[sucn]]
        [s₊] = (λ {k : Nat} {Δ : Con Term k} {σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ) →
                            let [σn] = proj₁ ([n] ⊢Δ [σ])
                                [σnatrecₙ] = proj₁ ([natrecₙ] ⊢Δ [σ])
                                [σFₙ] = proj₁ (unwrap [Fₙ]′ ⊢Δ [σ])
                                [σFₙ]′ = irrelevance′ {A′ = subst (consSubst σ (subst σ n)) F}
                                                      (PE.trans (singleSubstLift F n) (singleSubstComp (subst σ n) σ F)) [σFₙ]
                                [σnatrecₙ]′ = irrelevanceTerm′ (PE.trans (singleSubstLift F n) (singleSubstComp (subst σ n) σ F))
                                                               [σFₙ] (proj₁ (unwrap [F]′ ⊢Δ ([σ] , [σn]))) [σnatrecₙ]
                                [σ₊] = ([σ] , [σn]) , [σnatrecₙ]′
                                [σ₊s] = proj₁ ([s]′ {σ = consSubst (consSubst σ (subst σ n)) (subst σ (natrec p r F z s n))} ⊢Δ [σ₊])
                                [σ₊s]′ = irrelevanceTerm″ (PE.trans (sucCaseSubstEq F) (PE.sym (singleSubstLift F (suc n))))
                                                          (PE.trans (substVar-to-subst (λ { x0 → PE.refl
                                                                                          ; (x0 +1) → PE.refl
                                                                                          ; (x +1 +1) → PE.refl})
                                                                                       s)
                                                                    (PE.sym (substCompEq {σ = σ} {σ′ = consSubst (consSubst idSubst n) (natrec p r F z s n)} s)))
                                                          (proj₁ (unwrap [F₊] ⊢Δ (S.irrelevanceSubst ([Γ] ∙ [ℕ] ∙ [F]′) [Γ]₃ ⊢Δ ⊢Δ [σ₊])))
                                                          (proj₁ (unwrap [F[sucn]] ⊢Δ [σ])) [σ₊s]
                            in  [σ₊s]′ , (λ {σ′} [σ′] [σ≡σ′] →
                                let
                                    [σ′n] = proj₁ ([n] ⊢Δ [σ′])
                                    [σ′natrecₙ] = proj₁ ([natrecₙ] ⊢Δ [σ′])
                                    [σ′natrecₙ]′ = irrelevanceTerm′ (PE.trans (singleSubstLift F n) (singleSubstComp (subst σ′ n) σ′ F))
                                                                    (proj₁ (unwrap (substS {F = ℕ} {G = F} {t = n} [Γ] [ℕ] [F]′ [n]) ⊢Δ [σ′]))
                                                                    (proj₁ (unwrap [F]′ ⊢Δ ([σ′] , proj₁ ([n] ⊢Δ [σ′])))) [σ′natrecₙ]
                                    [σ′₊] = ([σ′] , [σ′n]) , [σ′natrecₙ]′
                                    [σnr≡σ′nr] = proj₂ ([natrecₙ] ⊢Δ [σ]) [σ′] [σ≡σ′]
                                    [σ₊s≡σ′₊s] = proj₂ ([s]′ {σ = consSubst (consSubst σ (subst σ n)) (subst σ (natrec p r F z s n))}
                                                             ⊢Δ [σ₊])
                                                       {σ′ = consSubst (consSubst σ′ (subst σ′ n)) (subst σ′ (natrec p r F z s n))}
                                                       [σ′₊] (([σ≡σ′] , (proj₂ ([n] ⊢Δ [σ]) [σ′] [σ≡σ′])) ,
                                                             irrelevanceEqTerm′ (PE.trans (singleSubstLift F n) (singleSubstComp (subst σ n) σ F))
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
                                                                                                           (singleSubstComp (subst σ n) σ F))
                                                                                                 (proj₁ (unwrap [Fₙ]′ ⊢Δ [σ])) (proj₁ (unwrap [F]′ ⊢Δ ([σ] , proj₁ ([n] ⊢Δ [σ]))))
                                                                                                 [σnatrecₙ])))
                                                                                                 (proj₁ (unwrap [F[sucn]] ⊢Δ [σ])) [σ₊s≡σ′₊s]))
        [natrecₛₙ] , [nr≡s₊] = redSubstTermᵛ {A = F [ suc n ]} {natrec p r F z s (suc n)}
                                            {subst (consSubst (consSubst idSubst n) (natrec p r F z s n)) s}
                                            [Γ] (λ {k Δ σ} ⊢Δ [σ] →
                                                  let [σℕ] = proj₁ (unwrap [ℕ] ⊢Δ [σ])
                                                      ⊢ℕ = escape [σℕ]
                                                      [σn] = proj₁ ([n] ⊢Δ [σ])
                                                      [σF] = proj₁ (unwrap [F]′ {σ = liftSubst σ} (⊢Δ ∙ ⊢ℕ)
                                                                         (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ]))
                                                      ⊢F = escape [σF]
                                                      [σF₀] = proj₁ (unwrap [F₀]′ ⊢Δ [σ])
                                                      [σF₀]′ = irrelevance′ (singleSubstLift F zero) [σF₀]
                                                      [σ⇑⇑] = liftSubstS {F = F} (_∙_ {A = ℕ} [Γ] [ℕ]) (⊢Δ ∙ ⊢ℕ) [F]′
                                                                         (liftSubstS {F = ℕ} [Γ] ⊢Δ [ℕ] [σ])
                                                      [σF₊] = proj₁ (unwrap [F₊]′ {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢ℕ ∙ ⊢F) [σ⇑⇑])
                                                      [σF₊]′ = irrelevance′ (natrecSucCase σ F) [σF₊]
                                                      [σz] = proj₁ ([z]′ ⊢Δ [σ])
                                                      [σz]′ = irrelevanceTerm′ (singleSubstLift F zero) [σF₀] [σF₀]′ [σz]

                                                      [σs] = proj₁ ([s]′ {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢ℕ ∙ ⊢F) [σ⇑⇑])
                                                      [σs]′ = irrelevanceTerm′ (natrecSucCase σ F) [σF₊] [σF₊]′ [σs]
                                                      ⊢n = escapeTerm [σℕ] [σn]
                                                      ⊢F = escape [σF]
                                                      ⊢z = escapeTerm [σF₀]′ [σz]′
                                                      ⊢s = escapeTerm [σF₊]′ [σs]′
                                                      red = natrec-suc {p = p} {r = r} ⊢n ⊢F ⊢z ⊢s
                                                  in  PE.subst₂ (λ u A → Δ ⊢ subst σ (natrec p r F z s (suc n)) ⇒ u ∷ A)
                                                                (PE.trans (doubleSubstComp s (subst σ n) (subst σ (natrec p r F z s n)) σ)
                                                                          (PE.trans (substVar-to-subst (λ { x0 → PE.refl
                                                                                                          ; (x0 +1) → PE.refl
                                                                                                          ; (x +1 +1) → PE.refl}) s)
                                                                                    (PE.sym (substCompEq s))))
                                                                (PE.sym (singleSubstLift F (suc n)))
                                                                red)
                                            [F[sucn]] [s₊]

    in  [Γ] , modelsTermEq [F[sucn]] [natrecₛₙ] [s₊] [nr≡s₊]
  fundamentalTermEq (Emptyrec-cong {A = F} {F′} {n} {n′}
                                 F≡F′ n≡n′ p≈p′)
    with fundamentalEq F≡F′ |
         fundamentalTermEq n≡n′
  fundamentalTermEq (Emptyrec-cong {A = F} {F′} {n} {n′}
                                 F≡F′ n≡n′ p≈p′) |
    [Γ]  , [F] , [F′] , [F≡F′] |
    [Γ]′ , modelsTermEq [Empty] [n] [n′] [n≡n′] =
    let [F]′ = S.irrelevance {A = F} [Γ] [Γ]′ [F]
        [F′]′ = S.irrelevance {A = F′} [Γ] [Γ]′ [F′]
        [F≡F′]′ = S.irrelevanceEq {A = F} {B = F′} [Γ] [Γ]′ [F] [F]′ [F≡F′]
    in [Γ]′
      , modelsTermEq [F]′ (Emptyrecᵛ {F = F} {n} [Γ]′ [Empty] [F]′ [n])
                     (conv₂ᵛ {t = Emptyrec _ F′ n′} {F} {F′} [Γ]′ [F]′ [F′]′ [F≡F′]′
                       (Emptyrecᵛ {F = F′} {n′} [Γ]′ [Empty] [F′]′ [n′]))
                     (Emptyrec-congᵛ {F = F} {F′} {n} {n′}
                       [Γ]′ [Empty] [F]′ [F′]′ [F≡F′]′
                       [n] [n′] [n≡n′] p≈p′)
  fundamentalTermEq (η-unit {e} {e'} ⊢e ⊢e')
    with fundamentalTerm ⊢e | fundamentalTerm ⊢e'
  ... | [Γ] , [Unit] , [e] | [Γ]' , [Unit]' , [e'] =
    let [e'] = S.irrelevanceTerm {A = Unit} {t = e'} [Γ]' [Γ] [Unit]' [Unit] [e']
    in  [Γ] , modelsTermEq [Unit] [e] [e'] (η-unitᵛ {e = e} {e' = e'} [Γ] [Unit] [e] [e'])
  fundamentalTermEq (fst-cong {t = t} {t′} {F} {G} ⊢F ⊢G t≡t′)
    with fundamentalTermEq t≡t′ | fundamental ⊢F | fundamental ⊢G
  ... | [Γ] , modelsTermEq [ΣFG] [t] [t′] [t≡t′] | [Γ]₁ , [F]₁ | [Γ]₂ , [G]₂ =
    let [F] = S.irrelevance {A = F} [Γ]₁ [Γ] [F]₁
        [G] = S.irrelevance {A = G} [Γ]₂ ([Γ] ∙ [F]) [G]₂

        [t]′ = S.irrelevanceTerm {A = Σ _ ▷ F ▹ G} {t = t} [Γ] [Γ]
                                 [ΣFG] (Σᵛ {F = F} {G} [Γ] [F] [G])
                                 [t]
        [t′]′ = S.irrelevanceTerm {A = Σ _ ▷ F ▹ G} {t = t′} [Γ] [Γ]
                                  [ΣFG] (Σᵛ {F = F} {G} [Γ] [F] [G])
                                  [t′]
        [t≡t′]′ = S.irrelevanceEqTerm {A = Σ _ ▷ F ▹ G} {t = t} {u = t′} [Γ] [Γ]
                                      [ΣFG] (Σᵛ {F = F} {G} [Γ] [F] [G])
                                      [t≡t′]

        [fstt] = fstᵛ {F = F} {G} {t} [Γ] [F] [G] [t]′
        [fstt′] = fstᵛ {F = F} {G} {t′} [Γ] [F] [G] [t′]′
        [fst≡] = fst-congᵛ {F = F} {G} {t} {t′} [Γ] [F] [G] [t]′ [t′]′ [t≡t′]′
    in  [Γ] , modelsTermEq [F] [fstt] [fstt′] [fst≡]
  fundamentalTermEq {Γ = Γ} (snd-cong {t = t} {t′} {F} {G} ⊢F ⊢G t≡t′)
    with fundamentalTermEq t≡t′ | fundamental ⊢F | fundamental ⊢G
  ... | [Γ] , modelsTermEq [ΣFG] [t] [t′] [t≡t′] | [Γ]₁ , [F]₁ | [Γ]₂ , [G]₂ =
    let [F] = S.irrelevance {A = F} [Γ]₁ [Γ] [F]₁
        [G] = S.irrelevance {A = G} [Γ]₂ ([Γ] ∙ [F]) [G]₂

        [t]Σ = S.irrelevanceTerm {A = Σ _ ▷ F ▹ G} {t = t} [Γ] [Γ]
                                 [ΣFG] (Σᵛ {F = F} {G} [Γ] [F] [G])
                                 [t]
        [t′]Σ = S.irrelevanceTerm {A = Σ _ ▷ F ▹ G} {t = t′} [Γ] [Γ]
                                  [ΣFG] (Σᵛ {F = F} {G} [Γ] [F] [G])
                                  [t′]
        [t≡t′]Σ = S.irrelevanceEqTerm {A = Σ _ ▷ F ▹ G} {t = t} {u = t′} [Γ] [Γ]
                                      [ΣFG] (Σᵛ {F = F} {G} [Γ] [F] [G])
                                      [t≡t′]

        [fst] = fstᵛ {F = F} {G} {t} [Γ] [F] [G] [t]Σ
        [fst′] = fstᵛ {F = F} {G} {t′} [Γ] [F] [G] [t′]Σ
        [fst≡] = fst-congᵛ {F = F} {G} {t} {t′} [Γ] [F] [G] [t]Σ [t′]Σ [t≡t′]Σ
        [Gfst] = substS {F = F} {G} [Γ] [F] [G] [fst]
        [Gfst′] = substS {F = F} {G} [Γ] [F] [G] [fst′]
        [Gfst≡] = substSEq {F = F} {F′ = F} {G = G} {G′ = G} {t = fst t} {t′ = fst t′} [Γ]
                           [F] [F] (reflᵛ {A = F} [Γ] [F])
                           [G] [G] (reflᵛ {Γ = Γ ∙ F} {A = G} ([Γ] ∙ [F]) [G])
                           [fst] [fst′] [fst≡]
        [snd] = sndᵛ {F = F} {G} {t} [Γ] [F] [G] [t]Σ
        [snd′]fst′ = sndᵛ {F = F} {G} {t′} [Γ] [F] [G] [t′]Σ
        [snd′]fst = conv₂ᵛ {t = snd t′} {A = G [ fst t ]} {B = G [ fst t′ ]}
                           [Γ] [Gfst] [Gfst′] [Gfst≡] [snd′]fst′
        [snd≡] = snd-congᵛ {F = F} {G} {t} {t′} [Γ] [F] [G] [t]Σ [t′]Σ [t≡t′]Σ
    in  [Γ] , modelsTermEq [Gfst] [snd] [snd′]fst [snd≡]
  fundamentalTermEq {Γ = Γ} (prod-cong {F = F} {G} {t} {t′} {u} {u′} ⊢F ⊢G t≡t′ u≡u′)
    with fundamental ⊢F | fundamental ⊢G |
         fundamentalTermEq t≡t′ | fundamentalTermEq u≡u′
  ... | [Γ] , [F] | [Γ]₂ , [G]₂
      | [Γ]₃ , modelsTermEq [F]₃ [t]₃ [t′]₃ [t≡t′]₃
      | [Γ]₄ , modelsTermEq [Gt]₄ [u]₄ [u′]₄ [u≡u′]₄ =
    let [G] = S.irrelevance {A = G} [Γ]₂ ([Γ] ∙ [F]) [G]₂
        [Σ] = Σᵛ {F = F} {G} [Γ] [F] [G]
        [t] = S.irrelevanceTerm {A = F} {t = t} [Γ]₃ [Γ] [F]₃ [F] [t]₃
        [t′] = S.irrelevanceTerm {A = F} {t = t′} [Γ]₃ [Γ] [F]₃ [F] [t′]₃
        [t≡t′] = S.irrelevanceEqTerm {A = F} {t = t} {u = t′} [Γ]₃ [Γ] [F]₃ [F] [t≡t′]₃
        [Gt] = substS {F = F} {G = G} {t = t} [Γ] [F] [G] [t]
        [Gt′] = substS {F = F} {G = G} {t = t′} [Γ] [F] [G] [t′]
        [u] = S.irrelevanceTerm {A = G [ t ]} {t = u} [Γ]₄ [Γ] [Gt]₄ [Gt] [u]₄
        [u′] = S.irrelevanceTerm {A = G [ t ]} {t = u′} [Γ]₄ [Γ] [Gt]₄ [Gt] [u′]₄
        [u≡u′] = S.irrelevanceEqTerm {A = G [ t ]} {t = u} {u = u′} [Γ]₄ [Γ] [Gt]₄ [Gt] [u≡u′]₄

        [prod] = prodᵛ {F = F} {G} {t} {u} [Γ] [F] [G] [t] [u]
        [Gt≡Gt′] = substSEq {F = F} {F} {G} {G} {t} {t′}
                            [Γ] [F] [F] (reflᵛ {A = F} [Γ] [F])
                            [G] [G] (reflᵛ {A = G} (_∙_ {A = F} [Γ] [F]) [G])
                            [t] [t′] [t≡t′]
        [u′]′ = convᵛ {t = u′} {A = G [ t ]} {B = G [ t′ ]} [Γ] [Gt] [Gt′] [Gt≡Gt′] [u′]
        [prod′] = prodᵛ {F = F} {G} {t′} {u′} [Γ] [F] [G] [t′] [u′]′
        [prod≡] = prod-congᵛ {F = F} {G} {t} {t′} {u} {u′} [Γ] [F] [G] [t] [t′] [t≡t′] [u] [u′]′ [u≡u′]
    in  [Γ] , modelsTermEq [Σ] [prod] [prod′] [prod≡]
  fundamentalTermEq (Σ-β₁ {q = q} {F = F} {G} {t} {u} ⊢F ⊢G ⊢t ⊢u ⊢p)
    with fundamentalTerm ⊢t | fundamental ⊢G | fundamentalTerm ⊢u
  ... | [Γ] , [F] , [t] | [Γ]₁ , [G]₁ | [Γ]₂ , [Gt]₂ , [u]₂ =
    let [G] = S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]₁
        [u] = S.irrelevanceTerm {A = G [ t ]} {t = u} [Γ]₂ [Γ]
                                [Gt]₂ (substS {F = F} {G} [Γ] [F] [G] [t])
                                [u]₂

        [prod] = prodᵛ {q = q} {F = F} {G} {t} {u} [Γ] [F] [G] [t] [u]
        [fst] = fstᵛ {F = F} {G} {prod! t u} [Γ] [F] [G] [prod]
        [fst≡t] = Σ-β₁ᵛ {F = F} {G} {t} {u} {q = q} [Γ] [F] [G] [t] [u]
    in  [Γ] , modelsTermEq [F] [fst] [t] [fst≡t]
  fundamentalTermEq {Γ = Γ} (Σ-β₂ {q = q} {F = F} {G} {t} {u} ⊢F ⊢G ⊢t ⊢u ⊢p)
    with fundamentalTerm ⊢t | fundamental ⊢G | fundamentalTerm ⊢u
  ... | [Γ] , [F] , [t] | [Γ]₁ , [G]₁ | [Γ]₂ , [Gt]₂ , [u]₂ =
    let [G] = S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]₁
        [Gt] = substS {F = F} {G} [Γ] [F] [G] [t]
        [u] = S.irrelevanceTerm {A = G [ t ]} {t = u} [Γ]₂ [Γ]
                                [Gt]₂ [Gt]
                                [u]₂

        [prod] = prodᵛ {q = q} {F = F} {G} {t} {u} [Γ] [F] [G] [t] [u]
        [fst] = fstᵛ {F = F} {G} {prod! t u} [Γ] [F] [G] [prod]
        [fst≡t] = Σ-β₁ᵛ {F = F} {G} {t} {u} {q = q} [Γ] [F] [G] [t] [u]

        [Gfst≡Gt] = substSEq {F = F} {F′ = F} {G = G} {G′ = G} {t = fst (prodₚ t u)} {t′ = t} [Γ]
                             [F] [F] (reflᵛ {A = F} [Γ] [F])
                             [G] [G] (reflᵛ {Γ = Γ ∙ F} {A = G} ([Γ] ∙ [F]) [G])
                             [fst] [t] [fst≡t]

        [Gfst] = substS {F = F} {G} [Γ] [F] [G] [fst]
        [snd] = sndᵛ {F = F} {G} {prod! t u} [Γ] [F] [G] [prod]
        [snd≡u] = Σ-β₂ᵛ {F = F} {G} {t} {u} [Γ] [F] [G] [t] [u]

        [u]fst = conv₂ᵛ {t = u} {A = G [ fst (prodₚ t u) ]} {B = G [ t ]}
                        [Γ] [Gfst] [Gt] [Gfst≡Gt] [u]
    in  [Γ] , modelsTermEq [Gfst] [snd] [u]fst [snd≡u]
  fundamentalTermEq (Σ-η {t = p} {r} {F} {G} ⊢F ⊢G ⊢p ⊢r fst≡ snd≡)
    with fundamentalTerm ⊢p | fundamentalTerm ⊢r |
         fundamental ⊢F | fundamental ⊢G |
         fundamentalTermEq fst≡ | fundamentalTermEq snd≡
  ... | [Γ] , [ΣFG]₀ , [p]₀ | [Γ]₁ , [ΣFG]₁ , [r]₁
      | [Γ]₂ , [F]₂ | [Γ]₃ , [G]₃
      | [Γ]₄ , modelsTermEq [F]₄ [fstp]₄ [fstr]₄ [fst≡]₄
      | [Γ]₅ , modelsTermEq [Gfstp]₅ [sndp]₅ [sndr]₅ [snd≡]₅ =
    let [F] = S.irrelevance {A = F} [Γ]₂ [Γ] [F]₂
        [G] = S.irrelevance {A = G} [Γ]₃ ([Γ] ∙ [F]) [G]₃
        [ΣFG] = Σᵛ {F = F} {G} [Γ] [F] [G]
        [p] = S.irrelevanceTerm {A = Σ _ ▷ F ▹ G} {t = p} [Γ] [Γ]
                                [ΣFG]₀ [ΣFG]
                                [p]₀
        [r] = S.irrelevanceTerm {A = Σ _ ▷ F ▹ G} {t = r} [Γ]₁ [Γ]
                                [ΣFG]₁ [ΣFG]
                                [r]₁

        [fst≡] = S.irrelevanceEqTerm {A = F} {t = fst p} {u = fst r} [Γ]₄ [Γ]
                                     [F]₄ [F]
                                     [fst≡]₄

        [Gfstp] = substS {F = F} {G} [Γ] [F] [G] (fstᵛ {F = F} {G} {p} [Γ] [F] [G] [p])
        [snd≡] = S.irrelevanceEqTerm {A = G [ fst p ]} {t = snd p} {u = snd r} [Γ]₅ [Γ]
                                     [Gfstp]₅ [Gfstp]
                                     [snd≡]₅

        [p≡r] = Σ-ηᵛ {F = F} {G} {p} {r}
                     [Γ] [F] [G] [p] [r] [fst≡] [snd≡]
    in  [Γ] , modelsTermEq [ΣFG] [p] [r] [p≡r]
  fundamentalTermEq (prodrec-cong {q = q} {p = p} {p′ = p′} {t = t} {t′} {u} {u′} {F} {G} {A} {A′}
                                  ⊢F ⊢G ⊢A≡A′ ⊢t≡t′ ⊢u≡u′ p≈p′)
    with fundamental ⊢F | fundamental ⊢G | fundamentalEq ⊢A≡A′ |
         fundamentalTermEq ⊢t≡t′ | fundamentalTermEq ⊢u≡u′
  ... | [Γ] , [F] | [Γ]₁ , [G] | [Γ]₂ , [A] , [A′] , [A≡A′]
      | [Γ]₃ , modelsTermEq [Σ] [t] [t′] [t≡t′]
      | [Γ]₄ , modelsTermEq [A₊] [u] [u′] [u≡u′] =
    let [G]′ = S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]
        [Σ]′ = S.irrelevance {A = Σ q ▷ F ▹ G} [Γ]₃ [Γ] [Σ]
        [A]′ = S.irrelevance {A = A} [Γ]₂ ([Γ] ∙ [Σ]′) [A]
        [A′]′ = S.irrelevance {A = A′} [Γ]₂ ([Γ] ∙ [Σ]′) [A′]
        [A≡A′]′ = S.irrelevanceEq {A = A} {B = A′} [Γ]₂ ([Γ] ∙ [Σ]′) [A] [A]′ [A≡A′]
        [t]′ = S.irrelevanceTerm {A = Σ q ▷ F ▹ G} {t = t} [Γ]₃ [Γ] [Σ] [Σ]′ [t]
        [t′]′ = S.irrelevanceTerm {A = Σ q ▷ F ▹ G} {t = t′} [Γ]₃ [Γ] [Σ] [Σ]′ [t′]
        [t≡t′]′ = S.irrelevanceEqTerm {A = Σ q ▷ F ▹ G} {t = t} {u = t′} [Γ]₃ [Γ] [Σ] [Σ]′ [t≡t′]
        A₊ = A [ prod! (var (x0 +1)) (var x0) ]↑²
        A′₊ = A′ [ prod! (var (x0 +1)) (var x0) ]↑²
        [A₊]′ = S.irrelevance {A = A₊} [Γ]₄ ([Γ] ∙ [F] ∙ [G]′) [A₊]
        [A′₊] = subst↑²S {F = F} {G} {A′} [Γ] [F] [G]′ [Σ]′ [A′]′
        [A₊≡A′₊] = subst↑²SEq {F = F} {G} {A} {A′} [Γ] [F] [G]′ [Σ]′ [A]′ [A′]′ [A≡A′]′ [A₊]′
        [u]′ = S.irrelevanceTerm {A = A₊} {t = u} [Γ]₄ ([Γ] ∙ [F] ∙ [G]′) [A₊] [A₊]′ [u]
        [u′]′ = S.irrelevanceTerm {A = A₊} {t = u′} [Γ]₄ ([Γ] ∙ [F] ∙ [G]′) [A₊] [A₊]′ [u′]
        [u′]″ = convᵛ {t = u′} {A₊} {A′₊} (_∙_ {A = G} (_∙_ {A = F} [Γ] [F]) [G]′) [A₊]′ [A′₊] [A₊≡A′₊] [u′]′
        [u≡u′]′ = S.irrelevanceEqTerm {A = A₊} {t = u} {u = u′} [Γ]₄ ([Γ] ∙ [F] ∙ [G]′) [A₊] [A₊]′ [u≡u′]
        [Aₜ] = substS {F = Σ q ▷ F ▹ G} {A} {t} [Γ] [Σ]′ [A]′ [t]′
        [A′ₜ′] = substS {F = Σ q ▷ F ▹ G} {A′} {t′} [Γ] [Σ]′ [A′]′ [t′]′
        [pr] = prodrecᵛ {q = q} {p = p} {F = F} {G} {A} {t} {u} [Γ] [F] [G]′ [Σ]′ [A]′ [A₊]′ [Aₜ] [t]′ [u]′
        [pr′] = prodrecᵛ {q = q} {p = p′} {F = F} {G} {A′} {t′} {u′} [Γ] [F] [G]′ [Σ]′ [A′]′ [A′₊] [A′ₜ′] [t′]′ [u′]″
        [Aₜ≡A′ₜ′] = substSEq {F = Σ q ▷ F ▹ G} {Σ q ▷ F ▹ G} {A} {A′} {t} {t′}
                           [Γ] [Σ]′ [Σ]′ (reflᵛ {A = Σ q ▷ F ▹ G} [Γ] [Σ]′)
                           [A]′ [A′]′ [A≡A′]′ [t]′ [t′]′ [t≡t′]′
        [pr′]′ = conv₂ᵛ {t = prodrec _ A′ t′ u′} {A = A [ t ]} {B = A′ [ t′ ]} [Γ] [Aₜ] [A′ₜ′] [Aₜ≡A′ₜ′] [pr′]
        [F≡F] = reflᵛ {A = F} [Γ] [F]
        [G≡G] = reflᵛ {A = G} (_∙_ {A = F} [Γ] [F]) [G]′
        [Σ≡Σ]′ = reflᵛ {A = Σ q ▷ F ▹ G} [Γ] [Σ]′
        [pr≡pr′] = prodrec-congᵛ {p = p} {F = F} {F} {G} {G} {A} {A′} {t} {t′} {u} {u′}
                                 [Γ] [F] [F] [F≡F] [G]′ [G]′ [G≡G] [Σ]′ [Σ]′ [Σ≡Σ]′
                                 [A]′ [A′]′ [A≡A′]′ [A₊]′ [A′₊] [A₊≡A′₊]
                                 [Aₜ] [t]′ [t′]′ [t≡t′]′ [u]′ [u′]″ [u≡u′]′ p≈p′
    in  [Γ] , modelsTermEq [Aₜ] [pr] [pr′]′ [pr≡pr′]
  fundamentalTermEq (prodrec-β {q = q} {p = p} {t = t} {t′} {u} {F} {G} {A} ⊢F ⊢G ⊢A ⊢t ⊢t′ ⊢u)
    with fundamental ⊢F | fundamental ⊢G | fundamental ⊢A |
         fundamentalTerm ⊢t | fundamentalTerm ⊢t′ |
         fundamentalTerm ⊢u
  ... | [Γ] , [F] | [Γ]₁ , [G]₁ | [Γ]₂ , [A]₂
      | [Γ]₃ , [F]₃ , [t]₃ | [Γ]₄ , [G[t]]₄ , [t′]₄
      | [Γ]₅ , [A₊]₅ , [u]₅ =
    let [G] = S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]₁
        [Σ] = Σᵛ {F = F} {G} [Γ] [F] [G]
        [A] = S.irrelevance {A = A} [Γ]₂ ([Γ] ∙ [Σ]) [A]₂
        [t] = S.irrelevanceTerm {A = F} {t = t} [Γ]₃ [Γ] [F]₃ [F] [t]₃
        [G[t]] = substS {F = F} {G} {t} [Γ] [F] [G] [t]
        [t′] = S.irrelevanceTerm {A = G [ t ]} {t = t′} [Γ]₄ [Γ] [G[t]]₄ [G[t]] [t′]₄
        A₊ = A [ prod! (var (x0 +1)) (var x0) ]↑²
        [ΓF] = _∙_ {A = F} [Γ] [F]
        [ΓFG] = _∙_ {A = G} [ΓF] [G]
        [A₊] = S.irrelevance {A = A₊} [Γ]₅ [ΓFG] [A₊]₅
        [u] = S.irrelevanceTerm {A = A₊} {t = u} [Γ]₅ [ΓFG] [A₊]₅ [A₊] [u]₅

        [p] = prodᵛ {F = F} {G} {t} {t′} [Γ] [F] [G] [t] [t′]
        [A[p]] = substS {F = Σ _ ▷ F ▹ G} {A} {prod! t t′} [Γ] [Σ] [A] [p]
        [pr] = prodrecᵛ {F = F} {G} {A} {prod! t t′} {u} [Γ] [F] [G] [Σ] [A] [A₊] [A[p]] [p] [u]
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
          ⊢σt′ = PE.subst (λ x → Δ ⊢ subst σ t′ ∷ x) (singleSubstLift G t) (escapeTerm [σG[t]] [σt′])
          [⇑σ]′ = liftSubstS {σ = σ} {F = Σ q ▷ F ▹ G} [Γ] ⊢Δ [Σ] [σ]
          [σΣ] = proj₁ (unwrap [Σ] ⊢Δ [σ])
          ⊢σΣ = escape [σΣ]
          [σA] = proj₁ (unwrap [A] {σ = liftSubst σ} (⊢Δ ∙ ⊢σΣ) [⇑σ]′)
          ⊢σA = escape [σA]
          [⇑²σ] = liftSubstS {σ = liftSubst σ} {F = G} [ΓF] (⊢Δ ∙ ⊢σF) [G] [⇑σ]
          [σu] = proj₁ ([u] {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢σF ∙ ⊢σG) [⇑²σ])
          [σA₊] = proj₁ (unwrap [A₊] {σ = liftSubstn σ 2} (⊢Δ ∙ ⊢σF ∙ ⊢σG) [⇑²σ])
          ⊢σu = PE.subst (λ x → Δ ∙ _ ∙ _ ⊢ _ ∷ x) (subst-β-prodrec A σ) (escapeTerm [σA₊] [σu])
          red : Δ ⊢ subst σ (prodrec p A (prod! t t′) u) ⇒ _ ∷ _
          red = prodrec-β ⊢σF ⊢σG ⊢σA ⊢σt ⊢σt′ ⊢σu
          [σA[p]] = proj₁ (unwrap [A[p]] ⊢Δ [σ])
          [σA[p]]′ = irrelevance′ (singleSubstLift A (prod! t t′)) [σA[p]]
          [σu₊] = proj₁ ([u₊] ⊢Δ [σ])
          [σu₊]′ = irrelevanceTerm″ (singleSubstLift A (prod! t t′))
                                    (PE.sym (PE.trans (doubleSubstComp u (subst σ t) (subst σ t′) σ)
                                                      (PE.trans (substVar-to-subst (λ {x0 → PE.refl; (x0 +1) → PE.refl; (x +1 +1) → PE.refl}) u)
                                                                (PE.sym (substCompEq u)))))
                                    [σA[p]] [σA[p]]′ [σu₊]
          _ , [pr≡u₊] = redSubstTerm red [σA[p]]′ [σu₊]′
      in  irrelevanceEqTerm″ PE.refl
                             (PE.trans (doubleSubstComp u (subst σ t) (subst σ t′) σ)
                                       (PE.trans (substVar-to-subst (λ{x0 → PE.refl; (x0 +1) → PE.refl; (x +1 +1) → PE.refl}) u)
                                                 (PE.sym (substCompEq u))))
                             (PE.sym (singleSubstLift A (prod! t t′))) [σA[p]]′ [σA[p]] [pr≡u₊]


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
