------------------------------------------------------------------------
-- Validity of the unit type.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Unit
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped M hiding (_∷_)
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.RedSteps R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Conversion R
open import Definition.LogicalRelation.Substitution.Escape R
open import Definition.LogicalRelation.Substitution.Properties R
open import Definition.LogicalRelation.Substitution.Reflexivity R
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst R
open import Definition.LogicalRelation.Substitution.Introductions.Universe R
open import Definition.LogicalRelation.Irrelevance R

open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ Δ : Con Term n
    σ σ′ : Subst _ _
    s : SigmaMode
    l : TypeLevel
    A A′ t t′ u u′ : Term n
    p q : M

-- Validity of the Unit type.
Unitᵛ :
  ∀ {l} ([Γ] : ⊩ᵛ Γ) → Unit-allowed s → Γ ⊩ᵛ⟨ l ⟩ Unit s / [Γ]
Unitᵛ _ ok =
  wrap λ ⊢Δ _ →
    Unitᵣ (Unitₜ (idRed:*: (Unitⱼ ⊢Δ ok)) ok)
  , λ _ _ → id (Unitⱼ ⊢Δ ok)

-- Validity of the Unit type as a term.
Unitᵗᵛ :
  ([Γ] : ⊩ᵛ Γ) →
  Unit-allowed s →
  Γ ⊩ᵛ⟨ ¹ ⟩ Unit s ∷ U / [Γ] / Uᵛ [Γ]
Unitᵗᵛ _ ok ⊢Δ _ =
    Uₜ Unit! (idRedTerm:*: ⊢Unit) Unitₙ Unit≅Unit [Unit]
  , (λ _ _ →
       Uₜ₌ Unit! Unit! (idRedTerm:*: ⊢Unit) (idRedTerm:*: ⊢Unit)
         Unitₙ Unitₙ Unit≅Unit [Unit] [Unit] (id ⊢Unit′))
  where
  ⊢Unit     = Unitⱼ ⊢Δ ok
  ⊢Unit′    = univ ⊢Unit
  Unit≅Unit = ≅ₜ-Unitrefl ⊢Δ ok
  [Unit]    = Unitᵣ (Unitₜ (idRed:*: ⊢Unit′) ok)

-- Validity of star.
starᵛ :
  ∀ {l} ([Γ] : ⊩ᵛ Γ) (ok : Unit-allowed s) →
  Γ ⊩ᵛ⟨ l ⟩ star s ∷ Unit s / [Γ] / Unitᵛ [Γ] ok
starᵛ {l = l} [Γ] ok ⊢Δ [σ] =
  [star] , λ _ _ → reflEqTerm [Unit] [star]
  where
  ⊢star = starⱼ ⊢Δ ok
  [Unit] = proj₁ (unwrap {l = l} (Unitᵛ [Γ] ok) ⊢Δ [σ])
  [star] = Unitₜ star! (idRedTerm:*: ⊢star)
                 (≅ₜ-starrefl ⊢Δ ok) starᵣ

-- Validity of η-unit.
η-unitᵛ : ∀ {l e e'} ([Γ] : ⊩ᵛ Γ)
  ([Unit] : Γ ⊩ᵛ⟨ l ⟩ Unitˢ / [Γ])
  ([e] : Γ ⊩ᵛ⟨ l ⟩ e ∷ Unitˢ / [Γ] / [Unit])
  ([e'] : Γ ⊩ᵛ⟨ l ⟩ e' ∷ Unitˢ / [Γ] / [Unit])
  → Γ ⊩ᵛ⟨ l ⟩ e ≡ e' ∷ Unitˢ / [Γ] / [Unit]
η-unitᵛ {Γ = Γ} {l} {e} {e'} [Γ] [Unit] [e] [e'] {Δ = Δ} {σ} ⊢Δ [σ] =
  let J = proj₁ (unwrap [Unit] ⊢Δ [σ])
      [σe] = proj₁ ([e] ⊢Δ [σ])
      [σe'] = proj₁ ([e'] ⊢Δ [σ])
      ok = ⊩ᵛUnit→Unit-allowed [Unit]
      UnitJ : Δ ⊩⟨ l ⟩ Unitˢ
      UnitJ = Unitᵣ (Unitₜ (idRed:*: (Unitⱼ ⊢Δ ok)) ok)
      [σe] = irrelevanceTerm J UnitJ [σe]
      [σe'] = irrelevanceTerm J UnitJ [σe']
      ⊢σe = escapeTerm UnitJ [σe]
      ⊢σe' = escapeTerm UnitJ [σe']
  in  irrelevanceEqTerm UnitJ J (Unitₜ₌ ⊢σe ⊢σe')

private

  unitrec-subst* : ([Γ] : ⊩ᵛ Γ)
                   (ok : Unitʷ-allowed)
                   (⊢Δ : ⊢ Δ)
                   ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
                   ([A] : Γ ∙ Unitʷ ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ Unitᵛ {l = l} [Γ] ok)
                   ([t′] : Δ ⊩⟨ l ⟩ t′ ∷ Unitʷ / proj₁ (unwrap (Unitᵛ [Γ] ok) ⊢Δ [σ]))
                 → Δ ⊢ u [ σ ] ∷ A [ liftSubst σ ] [ starʷ ]₀
                 → Δ ⊢ t ⇒* t′ ∷ Unitʷ
                 → Δ ⊢ unitrec p q (A [ liftSubst σ ]) t (u [ σ ]) ⇒*
                       unitrec p q (A [ liftSubst σ ]) t′ (u [ σ ]) ∷ A [ liftSubst σ ] [ t ]₀
  unitrec-subst* {σ = σ} {l = l} [Γ] ok ⊢Δ [σ] [A] [t′] ⊢σu (id x) =
    let [Unit] = Unitᵛ {l = l} [Γ] ok
        [⇑σ] = liftSubstS [Γ] ⊢Δ [Unit] [σ]
        [σA] = proj₁ (unwrap [A] {σ = liftSubst σ} (⊢Δ ∙ Unitⱼ ⊢Δ ok) [⇑σ])
        ⊢σA = escape [σA]
    in  id (unitrecⱼ ⊢σA x ⊢σu ok)
  unitrec-subst* {σ = σ} {l = l} {A = A} {t′ = t′} {u = u} {t = t}
                 [Γ] ok ⊢Δ [σ] [A] [t′] ⊢σu (x ⇨ d) =
    let [Unit] = Unitᵛ {l = l} [Γ] ok
        [σUnit] = proj₁ (unwrap [Unit] ⊢Δ [σ])
        [⇑σ] = liftSubstS [Γ] ⊢Δ [Unit] [σ]
        [σA] = proj₁ (unwrap [A] {σ = liftSubst σ} (⊢Δ ∙ Unitⱼ ⊢Δ ok) [⇑σ])
        ⊢σA = escape [σA]
        [t₁] , [t₁≡t′] = redSubst*Term d [σUnit] [t′]
        [t] , [t≡t₁] = redSubstTerm x [σUnit] [t₁]
        [At₁] = proj₁ (unwrap [A] ⊢Δ ([σ] , [t₁]))
        At₁≡At = proj₂ (unwrap [A] {σ = consSubst σ _} ⊢Δ ([σ] , [t₁]))
                       {σ′ = consSubst σ _} ([σ] , [t])
                       (reflSubst [Γ] ⊢Δ [σ] , symEqTerm [σUnit] [t≡t₁])
        ⊢At₁≡At = PE.subst₂ (_ ⊢_≡_) (PE.sym (singleSubstComp _ σ A))
                            (PE.sym (singleSubstComp t σ A))
                            (≅-eq (escapeEq [At₁] At₁≡At))
        d′ = unitrec-subst* {u = u} [Γ] ok ⊢Δ [σ] [A] [t′] ⊢σu d
    in  unitrec-subst ⊢σA ⊢σu x ok ⇨ conv* d′ ⊢At₁≡At

  [Unitʷ]-prop→Unit-prop : [Unitʷ]-prop Γ t u → Γ ⊢ t ∷ Unitʷ → Γ ⊢ u ∷ Unitʷ
                         → Unit-prop Γ Σᵣ t × Unit-prop Γ Σᵣ u
  [Unitʷ]-prop→Unit-prop starᵣ _ _ = starᵣ , starᵣ
  [Unitʷ]-prop→Unit-prop (ne (neNfₜ₌ neK neM k≡m)) ⊢t ⊢u =
      ne (neNfₜ neK ⊢t (~-trans k≡m (~-sym k≡m)))
    , ne (neNfₜ neM ⊢u (~-trans (~-sym k≡m) k≡m))



unitrecᵛ′ : {Γ : Con Term n}
            ([Γ] : ⊩ᵛ Γ)
            (ok : Unitʷ-allowed)
          → let [Unit] = Unitᵛ [Γ] ok in
            ([A] : Γ ∙ Unitʷ ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [Unit])
            ([A′] : Γ ∙ Unitʷ ⊩ᵛ⟨ l ⟩ A′ / [Γ] ∙ [Unit])
            ([A≡A′] : Γ ∙ Unitʷ ⊩ᵛ⟨ l ⟩ A ≡ A′ / [Γ] ∙ [Unit] / [A])
            ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Unitʷ / [Γ] / [Unit])
            ([t′] : Γ ⊩ᵛ⟨ l ⟩ t′ ∷ Unitʷ / [Γ] / [Unit])
            ([t≡t′] : Γ ⊩ᵛ⟨ l ⟩ t ≡ t′ ∷ Unitʷ / [Γ] / [Unit])
          → let [A₊] = substS [Γ] [Unit] [A] (starᵛ {l = l} [Γ] ok)
                [A′₊] = substS [Γ] [Unit] [A′] (starᵛ {l = l} [Γ] ok) in
            ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ A [ starʷ ]₀ / [Γ] / [A₊])
            ([u′] : Γ ⊩ᵛ⟨ l ⟩ u′ ∷ A′ [ starʷ ]₀ / [Γ] / [A′₊])
            ([u≡u′] : Γ ⊩ᵛ⟨ l ⟩ u ≡ u′ ∷ A [ starʷ ]₀ / [Γ] / [A₊])
            (⊢Δ : ⊢ Δ)
            ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
            ([σ′] : Δ ⊩ˢ σ′ ∷ Γ / [Γ] / ⊢Δ)
            ([σ≡σ′] : Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ])
          → ∃ λ [Aₜ] → Δ ⊩⟨ l ⟩ (unitrec p q A t u) [ σ ] ∷ A [ t ]₀ [ σ ] / [Aₜ]
                     × Δ ⊩⟨ l ⟩ (unitrec p q A t u) [ σ ] ≡ (unitrec p q A′ t′ u′) [ σ′ ]
                              ∷ A [ t ]₀ [ σ ] / [Aₜ]
unitrecᵛ′ {n} {l} {A} {A′} {t} {t′} {u} {u′} {m} {Δ} {σ} {σ′} {Γ}
          [Γ] ok [A] [A′] [A≡A′] [t] [t′] [t≡t′]
          [u] [u′] [u≡u′] ⊢Δ [σ] [σ′] [σ≡σ′] =
  let [Unit] = Unitᵛ [Γ] ok
      [σUnit] = proj₁ (unwrap [Unit] ⊢Δ [σ])
      [star] = starᵛ {l = l} [Γ] ok
      [σstar] = proj₁ ([star] ⊢Δ [σ])

      [⇑σ] = liftSubstS [Γ] ⊢Δ [Unit] [σ]
      [σA] = proj₁ (unwrap [A] {σ = liftSubst σ} (⊢Δ ∙ Unitⱼ ⊢Δ ok) [⇑σ])
      ⊢σA = escape [σA]
      [A₊] = substS [Γ] [Unit] [A] [star]
      [σA₊]′ = proj₁ (unwrap [A₊] ⊢Δ [σ])
      [σA₊] = irrelevance′ (singleSubstLift A starʷ) [σA₊]′
      [σu]′ = proj₁ ([u] ⊢Δ [σ])
      [σu] = irrelevanceTerm′ (singleSubstLift A starʷ) [σA₊]′ [σA₊] [σu]′
      ⊢σu = escapeTerm [σA₊] [σu]
      [Aₜ] = proj₁ (unwrap (substS {t = t} [Γ] [Unit] [A] [t]) ⊢Δ [σ])
      [σ≡σ] = reflSubst [Γ] ⊢Δ [σ]

      [⇑σ′] = liftSubstS [Γ] ⊢Δ [Unit] [σ′]
      [σ′A′] = proj₁ (unwrap [A′] {σ = liftSubst σ′} (⊢Δ ∙ Unitⱼ ⊢Δ ok) [⇑σ′])
      ⊢σ′A′ = escape [σ′A′]
      [A′₊] = substS [Γ] [Unit] [A′] [star]
      [σ′A′₊]′ = proj₁ (unwrap [A′₊] ⊢Δ [σ′])
      [σ′A′₊] = irrelevance′ (singleSubstLift A′ starʷ) [σ′A′₊]′
      [σ′u′]′ = proj₁ ([u′] ⊢Δ [σ′])
      [σ′u′] = irrelevanceTerm′ (singleSubstLift A′ starʷ) [σ′A′₊]′ [σ′A′₊] [σ′u′]′
      ⊢σ′u′ = escapeTerm [σ′A′₊] [σ′u′]
      [σ′≡σ′] = reflSubst [Γ] ⊢Δ [σ′]

      [σt≡σ′t] = proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′]
      [σ′t≡σ′t′] = [t≡t′] ⊢Δ [σ′]
      [σt≡σ′t′] = transEqTerm [σUnit] [σt≡σ′t] [σ′t≡σ′t′]
      [σu≡σ′u]′ = proj₂ ([u] ⊢Δ [σ]) [σ′] [σ≡σ′]
      [σ′u≡σ′u′]′ = [u≡u′] ⊢Δ [σ′]

  in  [Aₜ] , (case [σt≡σ′t′] of λ where
    (Unitₜ₌ k k′ d d′ k≡k′ prop) →
      let ⊢k = ⊢u-redₜ d
          ⊢k′ = ⊢u-redₜ d′
          k-prop , k′-prop = [Unitʷ]-prop→Unit-prop prop ⊢k ⊢k′
          [k] = Unitₜ k (idRedTerm:*: ⊢k) (≅ₜ-trans k≡k′ (≅ₜ-sym k≡k′)) k-prop
          [k′] = Unitₜ k′ (idRedTerm:*: ⊢k′) (≅ₜ-trans (≅ₜ-sym k≡k′) k≡k′) k′-prop
          [k≡k′] = Unitₜ₌ k k′ (idRedTerm:*: ⊢k)
                          (idRedTerm:*: ⊢k′) k≡k′ prop
          red₁ = unitrec-subst* {u = u} [Γ] ok ⊢Δ [σ] [A] [k] ⊢σu (redₜ d)
          red₂ = unitrec-subst* {u = u′} [Γ] ok ⊢Δ [σ′] [A′] [k′] ⊢σ′u′ (redₜ d′)

          [σt] , [σt≡k] = redSubst*Term (redₜ d) [σUnit] [k]
          [σ′t′] , [σ′t′≡k′] = redSubst*Term (redₜ d′) [σUnit] [k′]

          [σAt]′ = proj₁ (unwrap [A] {σ = consSubst σ _} ⊢Δ ([σ] , [σt]))
          [σAt] = irrelevance′ (PE.sym (singleSubstComp _ σ A)) [σAt]′
          [σAt≡σAk]′ = proj₂ (unwrap [A] {σ = consSubst σ _} ⊢Δ ([σ] , [σt]))
                             {σ′ = consSubst σ k} ([σ] , [k])
                             ([σ≡σ] , [σt≡k])
          [σAt≡σAk] = irrelevanceEq″ (PE.sym (singleSubstComp _ σ A))
                                     (PE.sym (singleSubstComp k σ A))
                                     [σAt]′ [σAt] [σAt≡σAk]′
          ⊢σAt≡σAk = ≅-eq (escapeEq [σAt] [σAt≡σAk])

          [σ′A′t′]′ = proj₁ (unwrap [A′] {σ = consSubst σ′ _} ⊢Δ ([σ′] , [σ′t′]))
          [σ′A′t′] = irrelevance′ (PE.sym (singleSubstComp _ σ′ A′)) [σ′A′t′]′
          [σ′A′t′≡σ′A′k′]′ = proj₂ (unwrap [A′] {σ = consSubst σ′ _} ⊢Δ ([σ′] , [σ′t′]))
                                   {σ′ = consSubst σ′ k′} ([σ′] , [k′])
                                   ([σ′≡σ′] , [σ′t′≡k′])
          [σ′A′t′≡σ′A′k′] = irrelevanceEq″ (PE.sym (singleSubstComp _ σ′ A′))
                                           (PE.sym (singleSubstComp k′ σ′ A′))
                                           [σ′A′t′]′ [σ′A′t′] [σ′A′t′≡σ′A′k′]′
          ⊢σ′A′t′≡σ′A′k′ = ≅-eq (escapeEq [σ′A′t′] [σ′A′t′≡σ′A′k′])

          [σAk]′ = proj₁ (unwrap [A] {σ = consSubst σ k} ⊢Δ ([σ] , [k]))
          [σAk≡σ′Ak′]′ = proj₂ (unwrap [A] {σ = consSubst σ k} ⊢Δ ([σ] , [k]))
                               {σ′ = consSubst σ′ k′} ([σ′] , [k′])
                               ([σ≡σ′] , [k≡k′])
      in  case prop of λ where
        starᵣ → -- k≡star, k′≡star
          let red₃ = unitrec-β ⊢σA ⊢σu ok ⇨ id ⊢σu
              red = red₁ ⇨∷* conv* red₃ (sym ⊢σAt≡σAk)
              [σu]″ = convTerm₂ [σAt] [σA₊] [σAt≡σAk] [σu]
              [urₜ]′ , [urₜ≡u]′ = redSubst*Term red [σAt] [σu]″
              [urₜ] = irrelevanceTerm′ (PE.sym (singleSubstLift A t))
                                       [σAt] [Aₜ] [urₜ]′
              [urₜ≡u] = irrelevanceEqTerm′ (PE.sym (singleSubstLift A t))
                                           [σAt] [Aₜ] [urₜ≡u]′

              red₄ = unitrec-β ⊢σ′A′ ⊢σ′u′ ok ⇨ id ⊢σ′u′
              red′ = red₂ ⇨∷* conv* red₄ (sym ⊢σ′A′t′≡σ′A′k′)
              [σ′u′]″ = convTerm₂ [σ′A′t′] [σ′A′₊] [σ′A′t′≡σ′A′k′] [σ′u′]
              [urₜ′]′ , [urₜ′≡u′]′ = redSubst*Term red′ [σ′A′t′] [σ′u′]″

              [σAt≡σA*] = irrelevanceEq″ (substConsId A) (substConsId A)
                                         [σAt]′ [Aₜ] [σAt≡σAk]′
              [σu≡σ′u] = convEqTerm₂ [Aₜ] [σA₊]′ [σAt≡σA*] [σu≡σ′u]′
              [σ′A₊] = proj₁ (unwrap [A₊] ⊢Δ [σ′])

              [σA*≡σ′A*] = irrelevanceEq″ (substConsId A) (substConsId A)
                                          [σAk]′ [σA₊]′ [σAk≡σ′Ak′]′
              [σAt≡σ′A*] = transEq [Aₜ] [σA₊]′ [σ′A₊] [σAt≡σA*] [σA*≡σ′A*]
              [σ′u≡σ′u′] = convEqTerm₂ [Aₜ] [σ′A₊] [σAt≡σ′A*] [σ′u≡σ′u′]′

              [σ′A*]′ = proj₁ (unwrap [A] {σ = consSubst σ′ starʷ} ⊢Δ ([σ′] , [σstar]))
              [σ′A*≡σ′A′*]′ = [A≡A′] {σ = consSubst σ′ starʷ} ⊢Δ ([σ′] , [σstar])
              [σ′A*≡σ′A′*] = irrelevanceEq″ (substConsId A) (substConsId A′)
                                            [σ′A*]′ [σ′A₊] [σ′A*≡σ′A′*]′
              [σ′A′t′≡σ′A′*] = irrelevanceEq″ (PE.sym (singleSubstComp _ σ′ A′))
                                              (substConsId {t = starʷ} A′)
                                              [σ′A′t′]′ [σ′A′t′] [σ′A′t′≡σ′A′k′]′
              [σAt≡σ′A′t′] = transEq [Aₜ] [σ′A₊] [σ′A′t′] [σAt≡σ′A*]
                              (transEq [σ′A₊] [σ′A′₊]′ [σ′A′t′] [σ′A*≡σ′A′*]
                                (symEq [σ′A′t′] [σ′A′₊]′ [σ′A′t′≡σ′A′*]))
              [urₜ′≡u′] = convEqTerm₂ [Aₜ] [σ′A′t′] [σAt≡σ′A′t′] [urₜ′≡u′]′

          in  [urₜ] , transEqTerm [Aₜ] [urₜ≡u]
                        (transEqTerm [Aₜ] [σu≡σ′u]
                        (transEqTerm [Aₜ] [σ′u≡σ′u′]
                          (symEqTerm [Aₜ] [urₜ′≡u′])))
        (ne (neNfₜ₌ neK neK′ k~k′)) →
          let ⊢urₖ = unitrecⱼ ⊢σA ⊢k ⊢σu ok
              ⊢σA≅σA = escapeEq [σA] (reflEq [σA])
              ⊢σu≅σu = escapeTermEq [σA₊] (reflEqTerm [σA₊] [σu])
              k~k = ~-trans k~k′ (~-sym k~k′)
              [σAk] = irrelevance′ (PE.sym (singleSubstComp k σ A)) [σAk]′
              [urₖ]′ = neuTerm [σAk] (unitrecₙ neK) ⊢urₖ
                               (~-unitrec ⊢σA≅σA k~k ⊢σu≅σu ok)
              [urₖ] = convTerm₂ [σAt] [σAk] [σAt≡σAk] [urₖ]′
              [urₜ]′ , [urₜ≡urₖ]′ = redSubst*Term red₁ [σAt] [urₖ]
              [urₜ] = irrelevanceTerm′ (PE.sym (singleSubstLift A t))
                                       [σAt] [Aₜ] [urₜ]′
              [urₜ≡urₖ] = irrelevanceEqTerm′ (PE.sym (singleSubstLift A t))
                                             [σAt] [Aₜ] [urₜ≡urₖ]′

              ⊢urₖ′ = unitrecⱼ ⊢σ′A′ ⊢k′ ⊢σ′u′ ok
              ⊢σ′A′≅σ′A′ = escapeEq [σ′A′] (reflEq [σ′A′])
              ⊢σ′u′≅σ′u′ = escapeTermEq [σ′A′₊] (reflEqTerm [σ′A′₊] [σ′u′])
              k′~k′ = ~-trans (~-sym k~k′) k~k′
              [σ′A′k′]′ = proj₁ (unwrap [A′] {σ = consSubst σ′ k′} ⊢Δ ([σ′] , [k′]))
              [σ′A′k′] = irrelevance′ (PE.sym (singleSubstComp k′ σ′ A′)) [σ′A′k′]′
              [urₖ′]′ = neuTerm [σ′A′k′] (unitrecₙ neK′) ⊢urₖ′
                                (~-unitrec ⊢σ′A′≅σ′A′ k′~k′ ⊢σ′u′≅σ′u′ ok)
              [urₖ′] = convTerm₂ [σ′A′t′] [σ′A′k′] [σ′A′t′≡σ′A′k′] [urₖ′]′
              [urₜ′] , [urₜ′≡urₖ′]′ = redSubst*Term red₂ [σ′A′t′] [urₖ′]
              [σ′Ak′≡σ′A′k′]′ = [A≡A′] {σ = consSubst σ′ k′} ⊢Δ ([σ′] , [k′])
              [σ′Ak′] = proj₁ (unwrap [A] {σ = consSubst σ′ k′} ⊢Δ ([σ′] , [k′]))
              [σAk≡σ′A′k′]′ = transEq [σAk]′ [σ′Ak′] [σ′A′k′]′ [σAk≡σ′Ak′]′ [σ′Ak′≡σ′A′k′]′
              [σAk≡σ′A′k′] = irrelevanceEq″ (PE.sym (singleSubstComp k σ A))
                                            (PE.sym (singleSubstComp k′ σ′ A′))
                                            [σAk]′ [σAk] [σAk≡σ′A′k′]′
              [σAt≡σ′A′t′]′ = transEq [σAt] [σAk] [σ′A′t′] [σAt≡σAk]
                               (transEq [σAk] [σ′A′k′] [σ′A′t′] [σAk≡σ′A′k′]
                                 (symEq [σ′A′t′] [σ′A′k′] [σ′A′t′≡σ′A′k′]))
              [σAt≡σ′A′t′] = irrelevanceEq′ (PE.sym (singleSubstLift A _))
                                            [σAt] [Aₜ] [σAt≡σ′A′t′]′
              [urₜ′≡urₖ′] = convEqTerm₂ [Aₜ] [σ′A′t′] [σAt≡σ′A′t′] [urₜ′≡urₖ′]′

              [⇑σ≡⇑σ′] = liftSubstSEq [Γ] ⊢Δ [Unit] [σ] [σ≡σ′]
              [σ′A] = proj₁ (unwrap [A] {σ = liftSubst σ′} (⊢Δ ∙ Unitⱼ ⊢Δ ok) [⇑σ′])
              [σA≡σ′A] = proj₂ (unwrap [A] {σ = liftSubst σ} (⊢Δ ∙ Unitⱼ ⊢Δ ok) [⇑σ])
                               {σ′ = liftSubst σ′} [⇑σ′] [⇑σ≡⇑σ′]
              [σ′A≡σ′A′] = [A≡A′] {σ = liftSubst σ′} (⊢Δ ∙ Unitⱼ ⊢Δ ok) [⇑σ′]
              [σA≡σ′A′] = transEq [σA] [σ′A] [σ′A′] [σA≡σ′A] [σ′A≡σ′A′]
              ⊢σA≅σ′A′ = escapeEq [σA] [σA≡σ′A′]
              [σ′A₊]′ = proj₁ (unwrap [A₊] ⊢Δ [σ′])
              [σA₊≡σ′A₊] = proj₂ (unwrap [A₊] ⊢Δ [σ]) [σ′] [σ≡σ′]
              [σ′u≡σ′u′]″ = convEqTerm₂ [σA₊]′ [σ′A₊]′ [σA₊≡σ′A₊] [σ′u≡σ′u′]′
              [σu≡σ′u′]′ = transEqTerm [σA₊]′ [σu≡σ′u]′ [σ′u≡σ′u′]″
              [σu≡σ′u′] = irrelevanceEqTerm′ (singleSubstLift A _)
                                             [σA₊]′ [σA₊] [σu≡σ′u′]′
              ⊢σu≅σ′u′ = escapeTermEq [σA₊] [σu≡σ′u′]

              urₖ~urₖ′ = ~-unitrec ⊢σA≅σ′A′ k~k′ ⊢σu≅σ′u′ ok
              ⊢σAk≅σ′A′k′ = ≅-eq (escapeEq [σAk] [σAk≡σ′A′k′])
              [urₖ≡urₖ′]′ = neuEqTerm [σAk] (unitrecₙ neK) (unitrecₙ neK′)
                                      ⊢urₖ (conv ⊢urₖ′ (sym ⊢σAk≅σ′A′k′)) urₖ~urₖ′
              [σAt≡σAk]″ = irrelevanceEq′ (PE.sym (singleSubstLift A _))
                                          [σAt] [Aₜ] [σAt≡σAk]
              [urₖ≡urₖ′] = convEqTerm₂ [Aₜ] [σAk] [σAt≡σAk]″ [urₖ≡urₖ′]′

          in  [urₜ] , transEqTerm [Aₜ] [urₜ≡urₖ]
                       (transEqTerm [Aₜ] [urₖ≡urₖ′] (symEqTerm [Aₜ] [urₜ′≡urₖ′])))

unitrecᵛ : {Γ : Con Term n}
         → ([Γ] : ⊩ᵛ Γ)
           (ok : Unitʷ-allowed)
         → let [Unit] = Unitᵛ [Γ] ok in
           ([A] : Γ ∙ Unitʷ ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [Unit])
           ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Unitʷ / [Γ] / [Unit])
           ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ A [ starʷ ]₀ / [Γ]
                / substS [Γ] [Unit] [A] (starᵛ {l = l} [Γ] ok))
         → Γ ⊩ᵛ⟨ l ⟩ unitrec p q A t u ∷ A [ t ]₀ / [Γ] / substS [Γ] [Unit] [A] [t]
unitrecᵛ {n} {l} {A} {t} {u} {Γ} [Γ] ok [A] [t] [u] {k} {Δ} {σ} ⊢Δ [σ] =
  let [Unit] = Unitᵛ [Γ] ok
      [A≡A] = reflᵛ ([Γ] ∙ [Unit]) [A]
      [t≡t] = reflᵗᵛ {t = t} [Γ] [Unit] [t]
      [u≡u] = reflᵗᵛ {t = u} [Γ] (substS [Γ] [Unit] [A] (starᵛ {l = l} [Γ] ok)) [u]
      [σ≡σ] = reflSubst [Γ] ⊢Δ [σ]
      _ , [ur] , _ = unitrecᵛ′ {t = t} {t} {u} {u} [Γ] ok [A] [A] [A≡A]
                                  [t] [t] [t≡t] [u] [u] [u≡u] ⊢Δ [σ] [σ] [σ≡σ]
  in  [ur] , λ [σ′] [σ≡σ′] →
    proj₂ (proj₂ (unitrecᵛ′ {t = t} {t} {u} {u} [Γ] ok [A] [A] [A≡A]
                            [t] [t] [t≡t] [u] [u] [u≡u] ⊢Δ [σ] [σ′] [σ≡σ′]))

unitrec-congᵛ : {Γ : Con Term n}
                ([Γ] : ⊩ᵛ Γ)
                (ok : Unitʷ-allowed)
              → let [Unit] = Unitᵛ [Γ] ok in
                ([A] : Γ ∙ Unitʷ ⊩ᵛ⟨ l ⟩ A / [Γ] ∙ [Unit])
                ([A′] : Γ ∙ Unitʷ ⊩ᵛ⟨ l ⟩ A′ / [Γ] ∙ [Unit])
                ([A≡A′] : Γ ∙ Unitʷ ⊩ᵛ⟨ l ⟩ A ≡ A′ / [Γ] ∙ [Unit] / [A])
                ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Unitʷ / [Γ] / [Unit])
                ([t′] : Γ ⊩ᵛ⟨ l ⟩ t′ ∷ Unitʷ / [Γ] / [Unit])
                ([t≡t′] : Γ ⊩ᵛ⟨ l ⟩ t ≡ t′ ∷ Unitʷ / [Γ] / [Unit])
              → let [A₊] = substS [Γ] [Unit] [A] (starᵛ {l = l} [Γ] ok) in
                ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ A [ starʷ ]₀ / [Γ] / [A₊])
                ([u′] : Γ ⊩ᵛ⟨ l ⟩ u′ ∷ A [ starʷ ]₀ / [Γ] / [A₊])
                ([u≡u′] : Γ ⊩ᵛ⟨ l ⟩ u ≡ u′ ∷ A [ starʷ ]₀ / [Γ] / [A₊])
              → Γ ⊩ᵛ⟨ l ⟩ unitrec p q A t u ≡ unitrec p q A′ t′ u′ ∷ A [ t ]₀ / [Γ] / substS [Γ] [Unit] [A] [t]
unitrec-congᵛ {n} {l} {A} {A′} {t} {t′} {u} {u′} {Γ}
              [Γ] ok [A] [A′] [A≡A′] [t] [t′] [t≡t′]
              [u] [u′] [u≡u′] {k} {Δ} {σ} ⊢Δ [σ] =
  let [Unit] = Unitᵛ [Γ] ok
      [star] = starᵛ {l = l} [Γ] ok
      [Unit≡Unit] = reflᵛ [Γ] [Unit]
      [star≡star] = reflᵗᵛ {t = starʷ} [Γ] [Unit] [star]
      [A₊] = substS [Γ] [Unit] [A] [star]
      [A′₊] = substS [Γ] [Unit] [A′] [star]
      [A₊≡A′₊] = substSEq {t = starʷ} {starʷ} [Γ] [Unit] [Unit] [Unit≡Unit]
                          [A] [A′] [A≡A′] [star] [star] [star≡star]
      [u′]′ = convᵛ {t = u′} [Γ] [A₊] [A′₊] [A₊≡A′₊] [u′]
  in  proj₂ (proj₂ (unitrecᵛ′ {t = t} {t′} {u} {u′} [Γ] ok [A] [A′] [A≡A′]
                              [t] [t′] [t≡t′] [u] [u′]′ [u≡u′] ⊢Δ [σ] [σ]
                              (reflSubst [Γ] ⊢Δ [σ])))
