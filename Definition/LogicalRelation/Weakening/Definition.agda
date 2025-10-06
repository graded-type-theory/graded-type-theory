------------------------------------------------------------------------
-- Weakening of the definition context for the logical relation
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Weakening.Definition
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Unary R
open import Definition.LogicalRelation.Weakening.Restricted R

open import Definition.Typed R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Weakening.Definition R as W
  hiding (defn-wk; defn-wkTerm; defn-wkEq; defn-wkEqTerm)

open import Definition.Untyped M
open import Definition.Untyped.Whnf M type-variant

open import Tools.Function
open import Tools.Level
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    ℓ : Level
    ∇ ∇′ : DCon (Term 0) _
    Γ : Con Term _
    t u A B : Term _
    l : Universe-level
    s : Strength

opaque

  defn-wkTermNe : » ∇′ ⊇ ∇ → ∇ » Γ ⊩neNf t ∷ A → ∇′ » Γ ⊩neNf t ∷ A
  defn-wkTermNe ξ⊇ (neNfₜ neK k≡k) =
    neNfₜ (defn-wkNeutral ξ⊇ neK) (~-defn-wk ξ⊇ k≡k)

opaque mutual

  defn-wkTermℕ : » ∇′ ⊇ ∇ → ∇ » Γ ⊩ℕ t ∷ℕ → ∇′ » Γ ⊩ℕ t ∷ℕ
  defn-wkTermℕ ξ⊇ (ℕₜ n d n≡n prop) =
    ℕₜ n (defn-wkRed*Term ξ⊇ d) (≅ₜ-defn-wk ξ⊇ n≡n) (defn-wkNatural-prop ξ⊇ prop)

  defn-wkNatural-prop :
    » ∇′ ⊇ ∇ → Natural-prop (∇ » Γ) t → Natural-prop (∇′ » Γ) t
  defn-wkNatural-prop ξ⊇ (sucᵣ n) = sucᵣ (defn-wkTermℕ ξ⊇ n)
  defn-wkNatural-prop ξ⊇ zeroᵣ    = zeroᵣ
  defn-wkNatural-prop ξ⊇ (ne nf)  = ne (defn-wkTermNe ξ⊇ nf)

opaque

  defn-wkUnit-prop′ :
    » ∇′ ⊇ ∇ → Unit-prop′ (∇ » Γ) l s t → Unit-prop′ (∇′ » Γ) l s t
  defn-wkUnit-prop′ ξ⊇ starᵣ   = starᵣ
  defn-wkUnit-prop′ ξ⊇ (ne nf) = ne (defn-wkTermNe ξ⊇ nf)

opaque

  defn-wkUnit-prop :
    » ∇′ ⊇ ∇ → Unit-prop (∇ » Γ) l s t → Unit-prop (∇′ » Γ) l s t
  defn-wkUnit-prop ξ⊇ (Unitₜʷ prop no-η) =
    Unitₜʷ (defn-wkUnit-prop′ ξ⊇ prop) no-η
  defn-wkUnit-prop ξ⊇ (Unitₜˢ η) =
    Unitₜˢ η

opaque

  defn-wkEqTermNe :
    » ∇′ ⊇ ∇ → ∇ » Γ ⊩neNf t ≡ u ∷ A → ∇′ » Γ ⊩neNf t ≡ u ∷ A
  defn-wkEqTermNe ξ⊇ (neNfₜ₌ neK neM k≡m) =
    neNfₜ₌ (defn-wkNeutral ξ⊇ neK) (defn-wkNeutral ξ⊇ neM) (~-defn-wk ξ⊇ k≡m)

opaque mutual

  defn-wkEqTermℕ : » ∇′ ⊇ ∇ → ∇ » Γ ⊩ℕ t ≡ u ∷ℕ → ∇′ » Γ ⊩ℕ t ≡ u ∷ℕ
  defn-wkEqTermℕ ξ⊇ (ℕₜ₌ k k′ d d′ k≡k′ prop) =
    ℕₜ₌ k k′ (defn-wkRed*Term ξ⊇ d) (defn-wkRed*Term ξ⊇ d′)
        (≅ₜ-defn-wk ξ⊇ k≡k′) (defn-wk[Natural]-prop ξ⊇ prop)

  defn-wk[Natural]-prop :
    » ∇′ ⊇ ∇ →
    [Natural]-prop (∇ » Γ) t u → [Natural]-prop (∇′ » Γ) t u
  defn-wk[Natural]-prop ξ⊇ (sucᵣ [n≡n′]) = sucᵣ (defn-wkEqTermℕ ξ⊇ [n≡n′])
  defn-wk[Natural]-prop ξ⊇ zeroᵣ         = zeroᵣ
  defn-wk[Natural]-prop ξ⊇ (ne nf)       = ne (defn-wkEqTermNe ξ⊇ nf)

opaque

  defn-wk[Unitʷ]-prop :
    » ∇′ ⊇ ∇ →
    [Unitʷ]-prop (∇ » Γ) l t u → [Unitʷ]-prop (∇′ » Γ) l t u
  defn-wk[Unitʷ]-prop ξ⊇ starᵣ   = starᵣ
  defn-wk[Unitʷ]-prop ξ⊇ (ne nf) = ne (defn-wkEqTermNe ξ⊇ nf)

opaque

  defn-wk[Unit]-prop :
    » ∇′ ⊇ ∇ →
    [Unit]-prop (∇ » Γ) l s t u → [Unit]-prop (∇′ » Γ) l s t u
  defn-wk[Unit]-prop ξ⊇ (Unitₜ₌ʷ prop no-η) =
    Unitₜ₌ʷ (defn-wk[Unitʷ]-prop ξ⊇ prop) no-η
  defn-wk[Unit]-prop ξ⊇ (Unitₜ₌ˢ η) =
    Unitₜ₌ˢ η

opaque

  defn-wkEqTermUnit :
    » ∇′ ⊇ ∇ →
    ∇ » Γ ⊩Unit⟨ l , s ⟩ t ≡ u ∷Unit →
    ∇′ » Γ ⊩Unit⟨ l , s ⟩ t ≡ u ∷Unit
  defn-wkEqTermUnit ξ⊇ (Unitₜ₌ _ _ ↘u₁ ↘u₂ prop) =
    Unitₜ₌ _ _ (defn-wkRed↘Term ξ⊇ ↘u₁) (defn-wkRed↘Term ξ⊇ ↘u₂)
      (defn-wk[Unit]-prop ξ⊇ prop)

private

  _•ᵈ→_ :
    ∀ {κ} {∇ : DCon (Term 0) κ} →
    {P : ∀ {κ′} {∇′ : DCon (Term 0) κ′}
       → ([ξ] : » ∇′ ⊇ ∇) → Set ℓ} →
    ∀ {κ*} {∇* : DCon (Term 0) κ*} →
    ([ξ*] : » ∇* ⊇ ∇) →
    (∀ {κ′} {∇′ : DCon (Term 0) κ′}
     → ([ξ] : » ∇′ ⊇ ∇) → P [ξ]) →
    (∀ {κ′} {∇′ : DCon (Term 0) κ′}
     → ([ξ] : » ∇′ ⊇ ∇*) → P (»⊇-trans [ξ] [ξ*]))
  [ξ*] •ᵈ→ f = λ [ξ] → f (»⊇-trans [ξ] [ξ*])

opaque
 unfolding »⊇-trans
 mutual

  defn-wk :
    » ∇′ ⊇ ∇ →
    ∇ » Γ ⊩⟨ l ⟩ A →
    ∇′ » Γ ⊩⟨ l ⟩ A
  defn-wk ξ⊇ (Uᵣ′ l′ l< D) = Uᵣ′ l′ l< (defn-wkRed* ξ⊇ D)
  defn-wk ξ⊇ (ℕᵣ D) = ℕᵣ (defn-wkRed* ξ⊇ D)
  defn-wk ξ⊇ (Emptyᵣ D) = Emptyᵣ (defn-wkRed* ξ⊇ D)
  defn-wk ξ⊇ (Unitᵣ′ _ ≤l D ok) = Unitᵣ′ _ ≤l (defn-wkRed* ξ⊇ D) ok
  defn-wk ξ⊇ (ne′ K* D neK K≡K) =
    ne′ K* (defn-wkRed* ξ⊇ D) (defn-wkNeutral ξ⊇ neK) (≅-defn-wk ξ⊇ K≡K)
  defn-wk ξ⊇ (Bᵣ′ W F G D A≡A [F] [G] G-ext ok) =
    Bᵣ′ W F G (defn-wkRed* ξ⊇ D) (≅-defn-wk ξ⊇ A≡A)
        (ξ⊇ •ᵈ→ [F]) (ξ⊇ •ᵈ→ [G]) (ξ⊇ •ᵈ→ G-ext) ok
  defn-wk ξ⊇ (Idᵣ ⊩A) = Idᵣ (record
    { ⇒*Id = defn-wkRed* ξ⊇ ⇒*Id
    ; ⊩Ty  = defn-wk ξ⊇ ⊩Ty
    ; ⊩lhs = defn-wkTerm ξ⊇ ⊩Ty ⊩lhs
    ; ⊩rhs = defn-wkTerm ξ⊇ ⊩Ty ⊩rhs
    })
    where
    open _⊩ₗId_ ⊩A

  defn-wkTerm :
    (ξ⊇ : » ∇′ ⊇ ∇) →
    ([A] : ∇ » Γ ⊩⟨ l ⟩ A) →
    ∇ » Γ ⊩⟨ l ⟩ t ∷ A / [A] →
    ∇′ » Γ ⊩⟨ l ⟩ t ∷ A / defn-wk ξ⊇ [A]
  defn-wkTerm = defn-wkEqTerm

  defn-wkEq :
    (ξ⊇ : » ∇′ ⊇ ∇) →
    ([A] : ∇ » Γ ⊩⟨ l ⟩ A) →
    ∇ » Γ ⊩⟨ l ⟩ A ≡ B / [A] →
    ∇′ » Γ ⊩⟨ l ⟩ A ≡ B / defn-wk ξ⊇ [A]
  defn-wkEq ξ⊇ (Uᵣ′ l′ <l D) A≡B = defn-wkRed* ξ⊇ A≡B
  defn-wkEq ξ⊇ (ℕᵣ D) A≡B = defn-wkRed* ξ⊇ A≡B
  defn-wkEq ξ⊇ (Emptyᵣ D) A≡B = defn-wkRed* ξ⊇ A≡B
  defn-wkEq ξ⊇ (Unitᵣ′ _ _ _ _) A≡B = defn-wkRed* ξ⊇ A≡B
  defn-wkEq ξ⊇ (ne′ K* D neK K≡K) (ne₌ M D′ neM K≡M) =
    ne₌ M (defn-wkRed* ξ⊇ D′) (defn-wkNeutral ξ⊇ neM) (≅-defn-wk ξ⊇ K≡M)
  defn-wkEq ξ⊇ (Bᵣ′ W F G D A≡A [F] [G] G-ext ok)
            (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
    B₌ F′ G′ (defn-wkRed* ξ⊇ D′)
             (≅-defn-wk ξ⊇ A≡B)
             (ξ⊇ •ᵈ→ [F≡F′])
             (ξ⊇ •ᵈ→ [G≡G′])
  defn-wkEq ξ⊇ (Idᵣ ⊩A) A≡B =
    Id₌′ (defn-wkRed* ξ⊇ ⇒*Id′)
         (defn-wkEq ξ⊇ ⊩Ty Ty≡Ty′)
         (defn-wkEqTerm ξ⊇ ⊩Ty lhs≡lhs′)
         (defn-wkEqTerm ξ⊇ ⊩Ty rhs≡rhs′)
    where
    open _⊩ₗId_ ⊩A
    open _⊩ₗId_≡_/_ A≡B

  defn-wkEqTerm :
    (ξ⊇ : » ∇′ ⊇ ∇) →
    ([A] : ∇ » Γ ⊩⟨ l ⟩ A) →
    ∇ » Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A] →
    ∇′ » Γ ⊩⟨ l ⟩ t ≡ u ∷ A / defn-wk ξ⊇ [A]
  defn-wkEqTerm ξ⊇ (Uᵣ′ l′ ≤ᵘ-refl D)
                (Uₜ₌ A B d d′ typeA typeB A≡B [t] [u] [t≡u]) =
    Uₜ₌ A B (defn-wkRed*Term ξ⊇ d)
            (defn-wkRed*Term ξ⊇ d′)
            (defn-wkType ξ⊇ typeA)
            (defn-wkType ξ⊇ typeB)
            (≅ₜ-defn-wk ξ⊇ A≡B)
            (defn-wk ξ⊇ [t])
            (defn-wk ξ⊇ [u])
            (defn-wkEq ξ⊇ [t] [t≡u])
  defn-wkEqTerm ξ⊇ [A]@(Uᵣ′ l′ (≤ᵘ-step l<) D)
                (Uₜ₌ A B d d′ typeA typeB A≡B [t] [u] [t≡u]) =
    let [A]′ = Uᵣ′ l′ l< D
        t≡u′ = Uₜ₌ A B d d′ typeA typeB A≡B [t] [u] [t≡u]
    in  irrelevanceEqTerm (defn-wk ξ⊇ [A]′)
                          (defn-wk ξ⊇ [A])
                          (defn-wkEqTerm ξ⊇ [A]′ t≡u′)
  defn-wkEqTerm ξ⊇ (ℕᵣ D) A≡B = defn-wkEqTermℕ ξ⊇ A≡B
  defn-wkEqTerm ξ⊇ (Emptyᵣ D) (Emptyₜ₌ k k′ d d′ k≡k′ (ne nf)) =
    Emptyₜ₌ k k′ (defn-wkRed*Term ξ⊇ d)
                 (defn-wkRed*Term ξ⊇ d′)
                 (≅ₜ-defn-wk ξ⊇ k≡k′)
                 (ne (defn-wkEqTermNe ξ⊇ nf))
  defn-wkEqTerm ξ⊇ (Unitᵣ′ _ _ _ _) t≡u = defn-wkEqTermUnit ξ⊇ t≡u
  defn-wkEqTerm ξ⊇ (ne′ K* D neK K≡K) (neₜ₌ k m d d′ nf) =
    neₜ₌ k m (defn-wkRed*Term ξ⊇ d)
             (defn-wkRed*Term ξ⊇ d′)
             (defn-wkEqTermNe ξ⊇ nf)
  defn-wkEqTerm ξ⊇ [A]@(Πᵣ′ F G D A≡A [F] [G] G-ext ok)
                (Πₜ₌ f g d d′ funcF funcG f≡g [f≡g]) =
    Πₜ₌ f g (defn-wkRed*Term ξ⊇ d)
            (defn-wkRed*Term ξ⊇ d′)
            (defn-wkFunction ξ⊇ funcF)
            (defn-wkFunction ξ⊇ funcG)
            (≅ₜ-defn-wk ξ⊇ f≡g)
            (ξ⊇ •ᵈ→ [f≡g])
  defn-wkEqTerm ξ⊇ [A]@(Bᵣ′ BΣˢ F G D A≡A [F] [G] G-ext ok)
                (Σₜ₌ p r d d′ pProd rProd p≅r
                     ([fstp] , [fstr] , [fst≡] , [snd≡])) =
    let id-Γ = id (wfEq (≅-eq A≡A))
        id-Γ′ = id (wfEq (≅-eq (≅-defn-wk ξ⊇ A≡A)))
        [Fid] = [F] id id-Γ
        [Fid]′ = [F] ξ⊇ id-Γ′
        [fstp]′ = irrelevanceTerm (defn-wk ξ⊇ [Fid]) [Fid]′
                                  (defn-wkTerm ξ⊇ [Fid] [fstp])
        [fstr]′ = irrelevanceTerm (defn-wk ξ⊇ [Fid]) [Fid]′
                                  (defn-wkTerm ξ⊇ [Fid] [fstr])
        [fst≡]′ = irrelevanceEqTerm (defn-wk ξ⊇ [Fid]) [Fid]′
                                    (defn-wkEqTerm ξ⊇ [Fid] [fst≡])
        [Gid] = [G] id id-Γ [fstp]
        [snd≡]′ = irrelevanceEqTerm (defn-wk ξ⊇ [Gid]) ([G] ξ⊇ id-Γ′ [fstp]′)
                                    (defn-wkEqTerm ξ⊇ [Gid] [snd≡])
    in  Σₜ₌ p r (defn-wkRed*Term ξ⊇ d)
                (defn-wkRed*Term ξ⊇ d′)
                (defn-wkProduct ξ⊇ pProd)
                (defn-wkProduct ξ⊇ rProd)
                (≅ₜ-defn-wk ξ⊇ p≅r)
                ([fstp]′ , [fstr]′ , [fst≡]′ , [snd≡]′)
  defn-wkEqTerm ξ⊇ [A]@(Bᵣ′ BΣʷ F G D A≡A [F] [G] G-ext ok)
    (Σₜ₌ p r d d′ prodₙ prodₙ p≅r
       (eq , eq′ , eq″ , eq‴ , [p₁] , [r₁] , [fst≡] , [snd≡])) =
    let id-Γ = id (wfEq (≅-eq A≡A))
        id-Γ′ = id (wfEq (≅-eq (≅-defn-wk ξ⊇ A≡A)))
        [Fid] = [F] id id-Γ
        [Fid]′ = [F] ξ⊇ id-Γ′
        [p₁]′ = irrelevanceTerm (defn-wk ξ⊇ [Fid]) [Fid]′
                                (defn-wkTerm ξ⊇ [Fid] [p₁])
        [r₁]′ = irrelevanceTerm (defn-wk ξ⊇ [Fid]) [Fid]′
                                (defn-wkTerm ξ⊇ [Fid] [r₁])
        [fst≡]′ = irrelevanceEqTerm (defn-wk ξ⊇ [Fid]) [Fid]′
                                    (defn-wkEqTerm ξ⊇ [Fid] [fst≡])
        [Gidp] = [G] id id-Γ [p₁]
        [Gidp]′ = [G] ξ⊇ id-Γ′ [p₁]′
        [Gidr] = [G] id id-Γ [r₁]
        [snd≡]′ = irrelevanceEqTerm (defn-wk ξ⊇ [Gidp]) [Gidp]′
                                    (defn-wkEqTerm ξ⊇ [Gidp] [snd≡])
    in  Σₜ₌ p r (defn-wkRed*Term ξ⊇ d)
                (defn-wkRed*Term ξ⊇ d′)
                prodₙ prodₙ
                (≅ₜ-defn-wk ξ⊇ p≅r)
                (eq , eq′ , eq″ , eq‴ , [p₁]′ , [r₁]′ ,
                 [fst≡]′ , [snd≡]′)
  defn-wkEqTerm ξ⊇ [A]@(Bᵣ′ BΣʷ F G D A≡A [F] [G] G-ext ok)
                (Σₜ₌ p r d d′ (ne b) (ne b′) p≅r p~r) =
    Σₜ₌ p r (defn-wkRed*Term ξ⊇ d)
            (defn-wkRed*Term ξ⊇ d′)
            (ne (defn-wkNeutral ξ⊇ b))
            (ne (defn-wkNeutral ξ⊇ b′))
            (≅ₜ-defn-wk ξ⊇ p≅r)
            (~-defn-wk ξ⊇ p~r)
  defn-wkEqTerm ξ⊇ (Bᵣ BΣʷ record{}) (Σₜ₌ _ _ _ _ prodₙ  (ne b) _ ())
  defn-wkEqTerm ξ⊇ (Bᵣ BΣʷ record{}) (Σₜ₌ _ _ _ _ (ne b) prodₙ  _ ())
  defn-wkEqTerm ξ⊇ (Idᵣ ⊩A) (t′ , u′ , d , d′ , prop) =
    let prop′ = case prop of λ where
                  (rflₙ , rflₙ , lhs≡rhs) →
                    rflₙ , rflₙ , defn-wkEqTerm ξ⊇ ⊩Ty lhs≡rhs
                  (ne b , ne b′ , t′~u′) →
                    ne (defn-wkNeutral ξ⊇ b) ,
                    ne (defn-wkNeutral ξ⊇ b′) ,
                    ~-defn-wk ξ⊇ t′~u′
                  (rflₙ , ne b , ())
                  (ne b , rflₙ , ())
    in  (t′ , u′ , defn-wkRed*Term ξ⊇ d , defn-wkRed*Term ξ⊇ d′ , prop′)
    where
    open _⊩ₗId_ ⊩A
