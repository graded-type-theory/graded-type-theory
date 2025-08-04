------------------------------------------------------------------------
-- The predicate Names<
------------------------------------------------------------------------

module Definition.Untyped.Names-below {a} (M : Set a) where

open import Definition.Untyped M

open import Tools.Empty
open import Tools.Fin
open import Tools.Nat
open import Tools.Relation

private variable
  α k m n       : Nat
  x             : Fin _
  ∇             : DCon (Term 0) _
  ρ             : Wk _ _
  σ             : Subst _ _
  A B C t u v w : Term _
  l             : Universe-level
  b             : BinderMode
  s             : Strength
  p q r         : M

------------------------------------------------------------------------
-- Names< and some related definitions

-- Names< m t holds if every name α in t satisfies α < m.

data Names< (m : Nat) : Term n → Set a where
  var :
    Names< m (var x)
  defn :
    α < m → Names< m {n = n} (defn α)
  U :
    Names< m {n = n} (U l)
  Empty :
    Names< m {n = n} Empty
  emptyrec :
    Names< m A → Names< m t → Names< m (emptyrec p A t)
  Unit :
    Names< m {n = n} (Unit s l)
  star :
    Names< m {n = n} (star s l)
  unitrec :
    Names< m A → Names< m t → Names< m u →
    Names< m (unitrec l p q A t u)
  ΠΣ :
    Names< m A → Names< m B → Names< m (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B)
  lam :
    Names< m t → Names< m (lam p t)
  app :
    Names< m t → Names< m u → Names< m (t ∘⟨ p ⟩ u)
  prod :
    Names< m t → Names< m u → Names< m (prod s p t u)
  fst :
    Names< m t → Names< m (fst p t)
  snd :
    Names< m t → Names< m (snd p t)
  prodrec :
    Names< m C → Names< m t → Names< m u →
    Names< m (prodrec r p q C t u)
  ℕ :
    Names< m {n = n} ℕ
  zero :
    Names< m {n = n} zero
  suc :
    Names< m t → Names< m (suc t)
  natrec :
    Names< m A → Names< m t → Names< m u → Names< m v →
    Names< m (natrec p q r A t u v)
  Id :
    Names< m A → Names< m t → Names< m u → Names< m (Id A t u)
  rfl :
    Names< m {n = n} rfl
  J :
    Names< m A → Names< m t → Names< m B → Names< m u → Names< m v →
    Names< m w → Names< m (J p q A t B u v w)
  K :
    Names< m A → Names< m t → Names< m B → Names< m u → Names< m v →
    Names< m (K p A t B u v)
  []-cong :
    Names< m A → Names< m t → Names< m u → Names< m v →
    Names< m ([]-cong s A t u v)

-- No-names t means that there are no names in t.

No-names : Term n → Set a
No-names = Names< 0

-- A variant of Names< for substitutions.

Names<ˢ : Nat → Subst m n → Set a
Names<ˢ n σ = ∀ x → Names< n (σ x)

------------------------------------------------------------------------
-- Weakening lemmas

opaque

  -- Names< n is closed under weakening.

  Names<-wk : Names< n t → Names< n (wk ρ t)
  Names<-wk var =
    var
  Names<-wk (defn <n) =
    defn <n
  Names<-wk U =
    U
  Names<-wk Empty =
    Empty
  Names<-wk (emptyrec <n₁ <n₂) =
    emptyrec (Names<-wk <n₁) (Names<-wk <n₂)
  Names<-wk Unit =
    Unit
  Names<-wk star =
    star
  Names<-wk (unitrec <n₁ <n₂ <n₃) =
    unitrec (Names<-wk <n₁) (Names<-wk <n₂) (Names<-wk <n₃)
  Names<-wk (ΠΣ <n₁ <n₂) =
    ΠΣ (Names<-wk <n₁) (Names<-wk <n₂)
  Names<-wk (lam <n) =
    lam (Names<-wk <n)
  Names<-wk (app <n₁ <n₂) =
    app (Names<-wk <n₁) (Names<-wk <n₂)
  Names<-wk (prod <n₁ <n₂) =
    prod (Names<-wk <n₁) (Names<-wk <n₂)
  Names<-wk (fst <n) =
    fst (Names<-wk <n)
  Names<-wk (snd <n) =
    snd (Names<-wk <n)
  Names<-wk (prodrec <n₁ <n₂ <n₃) =
    prodrec (Names<-wk <n₁) (Names<-wk <n₂) (Names<-wk <n₃)
  Names<-wk ℕ =
    ℕ
  Names<-wk zero =
    zero
  Names<-wk (suc <n) =
    suc (Names<-wk <n)
  Names<-wk (natrec <n₁ <n₂ <n₃ <n₄) =
    natrec (Names<-wk <n₁) (Names<-wk <n₂) (Names<-wk <n₃)
      (Names<-wk <n₄)
  Names<-wk (Id <n₁ <n₂ <n₃) =
    Id (Names<-wk <n₁) (Names<-wk <n₂) (Names<-wk <n₃)
  Names<-wk rfl =
    rfl
  Names<-wk (J <n₁ <n₂ <n₃ <n₄ <n₅ <n₆) =
    J (Names<-wk <n₁) (Names<-wk <n₂) (Names<-wk <n₃)
      (Names<-wk <n₄) (Names<-wk <n₅) (Names<-wk <n₆)
  Names<-wk (K <n₁ <n₂ <n₃ <n₄ <n₅) =
    K (Names<-wk <n₁) (Names<-wk <n₂) (Names<-wk <n₃)
      (Names<-wk <n₄) (Names<-wk <n₅)
  Names<-wk ([]-cong <n₁ <n₂ <n₃ <n₄) =
    []-cong (Names<-wk <n₁) (Names<-wk <n₂) (Names<-wk <n₃)
      (Names<-wk <n₄)

opaque

  -- Names< n is closed under removal of weakening.

  Names<-wk→ : Names< n (wk ρ t) → Names< n t
  Names<-wk→ {t = var _} var =
    var
  Names<-wk→ {t = defn _} (defn <n) =
    defn <n
  Names<-wk→ {t = U _} U =
    U
  Names<-wk→ {t = Empty} Empty =
    Empty
  Names<-wk→ {t = emptyrec _ _ _} (emptyrec <n₁ <n₂) =
    emptyrec (Names<-wk→ <n₁) (Names<-wk→ <n₂)
  Names<-wk→ {t = Unit _ _} Unit =
    Unit
  Names<-wk→ {t = star _ _} star =
    star
  Names<-wk→ {t = unitrec _ _ _ _ _ _} (unitrec <n₁ <n₂ <n₃) =
    unitrec (Names<-wk→ <n₁) (Names<-wk→ <n₂) (Names<-wk→ <n₃)
  Names<-wk→ {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} (ΠΣ <n₁ <n₂) =
    ΠΣ (Names<-wk→ <n₁) (Names<-wk→ <n₂)
  Names<-wk→ {t = lam _ _} (lam <n) =
    lam (Names<-wk→ <n)
  Names<-wk→ {t = _ ∘⟨ _ ⟩ _} (app <n₁ <n₂) =
    app (Names<-wk→ <n₁) (Names<-wk→ <n₂)
  Names<-wk→ {t = prod _ _ _ _} (prod <n₁ <n₂) =
    prod (Names<-wk→ <n₁) (Names<-wk→ <n₂)
  Names<-wk→ {t = fst _ _} (fst <n) =
    fst (Names<-wk→ <n)
  Names<-wk→ {t = snd _ _} (snd <n) =
    snd (Names<-wk→ <n)
  Names<-wk→ {t = prodrec _ _ _ _ _ _} (prodrec <n₁ <n₂ <n₃) =
    prodrec (Names<-wk→ <n₁) (Names<-wk→ <n₂) (Names<-wk→ <n₃)
  Names<-wk→ {t = ℕ} ℕ =
    ℕ
  Names<-wk→ {t = zero} zero =
    zero
  Names<-wk→ {t = suc _} (suc <n) =
    suc (Names<-wk→ <n)
  Names<-wk→ {t = natrec _ _ _ _ _ _ _} (natrec <n₁ <n₂ <n₃ <n₄) =
    natrec (Names<-wk→ <n₁) (Names<-wk→ <n₂) (Names<-wk→ <n₃)
      (Names<-wk→ <n₄)
  Names<-wk→ {t = Id _ _ _} (Id <n₁ <n₂ <n₃) =
    Id (Names<-wk→ <n₁) (Names<-wk→ <n₂) (Names<-wk→ <n₃)
  Names<-wk→ {t = rfl} rfl =
    rfl
  Names<-wk→ {t = J _ _ _ _ _ _ _ _} (J <n₁ <n₂ <n₃ <n₄ <n₅ <n₆) =
    J (Names<-wk→ <n₁) (Names<-wk→ <n₂) (Names<-wk→ <n₃)
      (Names<-wk→ <n₄) (Names<-wk→ <n₅) (Names<-wk→ <n₆)
  Names<-wk→ {t = K _ _ _ _ _ _} (K <n₁ <n₂ <n₃ <n₄ <n₅) =
    K (Names<-wk→ <n₁) (Names<-wk→ <n₂) (Names<-wk→ <n₃)
      (Names<-wk→ <n₄) (Names<-wk→ <n₅)
  Names<-wk→ {t = []-cong _ _ _ _ _} ([]-cong <n₁ <n₂ <n₃ <n₄) =
    []-cong (Names<-wk→ <n₁) (Names<-wk→ <n₂) (Names<-wk→ <n₃)
      (Names<-wk→ <n₄)

------------------------------------------------------------------------
-- Substitution lemmas

opaque

  -- Names<ˢ holds for idSubst.

  Names<ˢ-idSubst : Names<ˢ m (idSubst {n = n})
  Names<ˢ-idSubst _ = var

opaque

  -- Names<ˢ n holds for consSubst if Names<ˢ n and Names< n hold for
  -- the arguments.

  Names<ˢ-consSubst :
    Names<ˢ n σ → Names< n t → Names<ˢ n (consSubst σ t)
  Names<ˢ-consSubst _    t-<n x0     = t-<n
  Names<ˢ-consSubst σ-<n _    (x +1) = σ-<n x

opaque

  -- Names<ˢ n holds for sgSubst t if Names< n holds for t.

  Names<ˢ-sgSubst : Names< n t → Names<ˢ n (sgSubst t)
  Names<ˢ-sgSubst t-<n = Names<ˢ-consSubst Names<ˢ-idSubst t-<n

opaque

  -- Names<ˢ n is closed under lifting.

  Names<ˢ-⇑ : Names<ˢ n σ → Names<ˢ n (σ ⇑[ k ])
  Names<ˢ-⇑ {k = Nat.zero}  <n x      = <n x
  Names<ˢ-⇑ {k = Nat.suc _} _  x0     = var
  Names<ˢ-⇑ {k = Nat.suc k} <n (x +1) = Names<-wk (Names<ˢ-⇑ <n x)

opaque

  -- A substitution lemma for Names</Names<ˢ.

  Names<-[] : Names< n t → Names<ˢ n σ → Names< n (t [ σ ])
  Names<-[] var σ-<n =
    σ-<n _
  Names<-[] (defn <n) _ =
    defn <n
  Names<-[] U _ =
    U
  Names<-[] Empty _ =
    Empty
  Names<-[] (emptyrec A-<n t-<n) σ-<n =
    emptyrec (Names<-[] A-<n σ-<n) (Names<-[] t-<n σ-<n)
  Names<-[] Unit _ =
    Unit
  Names<-[] star _ =
    star
  Names<-[] (unitrec A-<n t-<n u-<n) σ-<n =
    unitrec (Names<-[] A-<n (Names<ˢ-⇑ σ-<n)) (Names<-[] t-<n σ-<n)
      (Names<-[] u-<n σ-<n)
  Names<-[] (ΠΣ A-<n B-<n) σ-<n =
    ΠΣ (Names<-[] A-<n σ-<n) (Names<-[] B-<n (Names<ˢ-⇑ σ-<n))
  Names<-[] (lam t-<n) σ-<n =
    lam (Names<-[] t-<n (Names<ˢ-⇑ σ-<n))
  Names<-[] (app t-<n u-<n) σ-<n =
    app (Names<-[] t-<n σ-<n) (Names<-[] u-<n σ-<n)
  Names<-[] (prod t-<n u-<n) σ-<n =
    prod (Names<-[] t-<n σ-<n) (Names<-[] u-<n σ-<n)
  Names<-[] (fst t-<n) σ-<n =
    fst (Names<-[] t-<n σ-<n)
  Names<-[] (snd t-<n) σ-<n =
    snd (Names<-[] t-<n σ-<n)
  Names<-[] (prodrec C-<n t-<n u-<n) σ-<n =
    prodrec (Names<-[] C-<n (Names<ˢ-⇑ σ-<n)) (Names<-[] t-<n σ-<n)
      (Names<-[] u-<n (Names<ˢ-⇑ σ-<n))
  Names<-[] ℕ _ =
    ℕ
  Names<-[] zero _ =
    zero
  Names<-[] (suc t-<n) σ-<n =
    suc (Names<-[] t-<n σ-<n)
  Names<-[] (natrec A-<n t-<n u-<n v-<n) σ-<n =
    natrec (Names<-[] A-<n (Names<ˢ-⇑ σ-<n)) (Names<-[] t-<n σ-<n)
      (Names<-[] u-<n (Names<ˢ-⇑ σ-<n)) (Names<-[] v-<n σ-<n)
  Names<-[] (Id A-<n t-<n u-<n) σ-<n =
    Id (Names<-[] A-<n σ-<n) (Names<-[] t-<n σ-<n)
      (Names<-[] u-<n σ-<n)
  Names<-[] rfl _ =
    rfl
  Names<-[] (J A-<n t-<n B-<n u-<n v-<n w-<n) σ-<n =
    J (Names<-[] A-<n σ-<n) (Names<-[] t-<n σ-<n)
      (Names<-[] B-<n (Names<ˢ-⇑ σ-<n)) (Names<-[] u-<n σ-<n)
      (Names<-[] v-<n σ-<n) (Names<-[] w-<n σ-<n)
  Names<-[] (K A-<n t-<n B-<n u-<n v-<n) σ-<n =
    K (Names<-[] A-<n σ-<n) (Names<-[] t-<n σ-<n)
      (Names<-[] B-<n (Names<ˢ-⇑ σ-<n)) (Names<-[] u-<n σ-<n)
      (Names<-[] v-<n σ-<n)
  Names<-[] ([]-cong A-<n t-<n u-<n v-<n) σ-<n =
    []-cong (Names<-[] A-<n σ-<n) (Names<-[] t-<n σ-<n)
      (Names<-[] u-<n σ-<n) (Names<-[] v-<n σ-<n)

opaque

  -- A special case of Names<-[].

  Names<-[]₀ : Names< n t → Names< n u → Names< n (t [ u ]₀)
  Names<-[]₀ t-<n u-<n = Names<-[] t-<n (Names<ˢ-sgSubst u-<n)

opaque

  -- A special case of Names<-[].

  Names<-[]₁₀ :
    Names< n t → Names< n u → Names< n v → Names< n (t [ u , v ]₁₀)
  Names<-[]₁₀ t-<n u-<n v-<n =
    Names<-[] t-<n (Names<ˢ-consSubst (Names<ˢ-sgSubst u-<n) v-<n)

opaque

  -- If all names in t [ σ ] are bounded by n, then all names in t are
  -- bounded by n.

  Names<-[]→ : Names< n (t [ σ ]) → Names< n t
  Names<-[]→ {t = var _} _ =
    var
  Names<-[]→ {t = defn _} (defn <n) =
    defn <n
  Names<-[]→ {t = U _} U =
    U
  Names<-[]→ {t = Empty} Empty =
    Empty
  Names<-[]→ {t = emptyrec _ _ _} (emptyrec <n₁ <n₂) =
    emptyrec (Names<-[]→ <n₁) (Names<-[]→ <n₂)
  Names<-[]→ {t = Unit _ _} Unit =
    Unit
  Names<-[]→ {t = star _ _} star =
    star
  Names<-[]→ {t = unitrec _ _ _ _ _ _} (unitrec <n₁ <n₂ <n₃) =
    unitrec (Names<-[]→ <n₁) (Names<-[]→ <n₂) (Names<-[]→ <n₃)
  Names<-[]→ {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} (ΠΣ <n₁ <n₂) =
    ΠΣ (Names<-[]→ <n₁) (Names<-[]→ <n₂)
  Names<-[]→ {t = lam _ _} (lam <n) =
    lam (Names<-[]→ <n)
  Names<-[]→ {t = _ ∘⟨ _ ⟩ _} (app <n₁ <n₂) =
    app (Names<-[]→ <n₁) (Names<-[]→ <n₂)
  Names<-[]→ {t = prod _ _ _ _} (prod <n₁ <n₂) =
    prod (Names<-[]→ <n₁) (Names<-[]→ <n₂)
  Names<-[]→ {t = fst _ _} (fst <n) =
    fst (Names<-[]→ <n)
  Names<-[]→ {t = snd _ _} (snd <n) =
    snd (Names<-[]→ <n)
  Names<-[]→ {t = prodrec _ _ _ _ _ _} (prodrec <n₁ <n₂ <n₃) =
    prodrec (Names<-[]→ <n₁) (Names<-[]→ <n₂) (Names<-[]→ <n₃)
  Names<-[]→ {t = ℕ} ℕ =
    ℕ
  Names<-[]→ {t = zero} zero =
    zero
  Names<-[]→ {t = suc _} (suc <n) =
    suc (Names<-[]→ <n)
  Names<-[]→ {t = natrec _ _ _ _ _ _ _} (natrec <n₁ <n₂ <n₃ <n₄) =
    natrec (Names<-[]→ <n₁) (Names<-[]→ <n₂) (Names<-[]→ <n₃)
      (Names<-[]→ <n₄)
  Names<-[]→ {t = Id _ _ _} (Id <n₁ <n₂ <n₃) =
    Id (Names<-[]→ <n₁) (Names<-[]→ <n₂) (Names<-[]→ <n₃)
  Names<-[]→ {t = rfl} rfl =
    rfl
  Names<-[]→ {t = J _ _ _ _ _ _ _ _} (J <n₁ <n₂ <n₃ <n₄ <n₅ <n₆) =
    J (Names<-[]→ <n₁) (Names<-[]→ <n₂) (Names<-[]→ <n₃)
      (Names<-[]→ <n₄) (Names<-[]→ <n₅) (Names<-[]→ <n₆)
  Names<-[]→ {t = K _ _ _ _ _ _} (K <n₁ <n₂ <n₃ <n₄ <n₅) =
    K (Names<-[]→ <n₁) (Names<-[]→ <n₂) (Names<-[]→ <n₃)
      (Names<-[]→ <n₄) (Names<-[]→ <n₅)
  Names<-[]→ {t = []-cong _ _ _ _ _} ([]-cong <n₁ <n₂ <n₃ <n₄) =
    []-cong (Names<-[]→ <n₁) (Names<-[]→ <n₂) (Names<-[]→ <n₃)
      (Names<-[]→ <n₄)

------------------------------------------------------------------------
-- More lemmas

opaque

  -- Names< is upwards closed.

  Names<-upwards-closed : m ≤ n → Names< m t → Names< n t
  Names<-upwards-closed {m} {n} m≤n = lemma
    where
    lemma : Names< m t → Names< n t
    lemma var =
      var
    lemma (defn <m) =
      defn (≤-trans <m m≤n)
    lemma U =
      U
    lemma Empty =
      Empty
    lemma (emptyrec A-<n t-<n) =
      emptyrec (lemma A-<n) (lemma t-<n)
    lemma Unit =
      Unit
    lemma star =
      star
    lemma (unitrec A-<n t-<n u-<n) =
      unitrec (lemma A-<n) (lemma t-<n) (lemma u-<n)
    lemma (ΠΣ A-<n B-<n) =
      ΠΣ (lemma A-<n) (lemma B-<n)
    lemma (lam t-<n) =
      lam (lemma t-<n)
    lemma (app t-<n u-<n) =
      app (lemma t-<n) (lemma u-<n)
    lemma (prod t-<n u-<n) =
      prod (lemma t-<n) (lemma u-<n)
    lemma (fst t-<n) =
      fst (lemma t-<n)
    lemma (snd t-<n) =
      snd (lemma t-<n)
    lemma (prodrec C-<n t-<n u-<n) =
      prodrec (lemma C-<n) (lemma t-<n) (lemma u-<n)
    lemma ℕ =
      ℕ
    lemma zero =
      zero
    lemma (suc t-<n) =
      suc (lemma t-<n)
    lemma (natrec A-<n t-<n u-<n v-<n) =
      natrec (lemma A-<n) (lemma t-<n) (lemma u-<n) (lemma v-<n)
    lemma (Id A-<n t-<n u-<n) =
      Id (lemma A-<n) (lemma t-<n) (lemma u-<n)
    lemma rfl =
      rfl
    lemma (J A-<n t-<n B-<n u-<n v-<n w-<n) =
      J (lemma A-<n) (lemma t-<n) (lemma B-<n) (lemma u-<n) (lemma v-<n)
        (lemma w-<n)
    lemma (K A-<n t-<n B-<n u-<n v-<n) =
      K (lemma A-<n) (lemma t-<n) (lemma B-<n) (lemma u-<n) (lemma v-<n)
    lemma ([]-cong A-<n t-<n u-<n v-<n) =
      []-cong (lemma A-<n) (lemma t-<n) (lemma u-<n) (lemma v-<n)

opaque
 unfolding inline
 mutual

  -- There are no names in inline-< ∇ p.

  No-names-inline-< :
    (∇ : DCon (Term 0) n) (p : m <′ n) → No-names (inline-< ∇ p)
  No-names-inline-< ε m<0 =
    ⊥-elim (n≮0 (<′⇒< m<0))
  No-names-inline-< (_ ∙⟨ _ ⟩[ t ∷ _ ]) (≤′-reflexive _) =
    No-names-inline t
  No-names-inline-< (∇ ∙⟨ _ ⟩[ _ ∷ _ ]) (≤′-step m<n) =
    No-names-inline-< ∇ m<n

  -- There are no names in inline-Nat ∇ α.

  No-names-inline-Nat :
    (∇ : DCon (Term 0) n) (α : Nat) → No-names (inline-Nat ∇ α)
  No-names-inline-Nat {n} ∇ α with α <′? n
  … | yes α<n = No-names-inline-< ∇ α<n
  … | no _    = ℕ

  -- There are no names in inline ∇ t.

  No-names-inline : (t : Term n) → No-names (inline ∇ t)
  No-names-inline (var _) =
    var
  No-names-inline {∇} (defn α) =
    Names<-wk (No-names-inline-Nat ∇ α)
  No-names-inline (U _) =
    U
  No-names-inline (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B) =
    ΠΣ (No-names-inline A) (No-names-inline B)
  No-names-inline (lam p t) =
    lam (No-names-inline t)
  No-names-inline (t ∘⟨ p ⟩ u) =
    app (No-names-inline t) (No-names-inline u)
  No-names-inline (prod s p t u) =
    prod (No-names-inline t) (No-names-inline u)
  No-names-inline (fst p t) =
    fst (No-names-inline t)
  No-names-inline (snd p t) =
    snd (No-names-inline t)
  No-names-inline (prodrec r p q A t u) =
    prodrec (No-names-inline A) (No-names-inline t) (No-names-inline u)
  No-names-inline ℕ =
    ℕ
  No-names-inline zero =
    zero
  No-names-inline (suc t) =
    suc (No-names-inline t)
  No-names-inline (natrec p q r A t u v) =
    natrec (No-names-inline A) (No-names-inline t) (No-names-inline u)
      (No-names-inline v)
  No-names-inline (Unit _ _) =
    Unit
  No-names-inline (star _ _) =
    star
  No-names-inline (unitrec l p q A t u) =
    unitrec (No-names-inline A) (No-names-inline t) (No-names-inline u)
  No-names-inline Empty =
    Empty
  No-names-inline (emptyrec p A t) =
    emptyrec (No-names-inline A) (No-names-inline t)
  No-names-inline (Id A t u) =
    Id (No-names-inline A) (No-names-inline t) (No-names-inline u)
  No-names-inline rfl =
    rfl
  No-names-inline (J p q A t B u v w) =
    J (No-names-inline A) (No-names-inline t) (No-names-inline B)
      (No-names-inline u) (No-names-inline v) (No-names-inline w)
  No-names-inline (K p A t B u v) =
    K (No-names-inline A) (No-names-inline t) (No-names-inline B)
      (No-names-inline u) (No-names-inline v)
  No-names-inline ([]-cong s A t u v) =
    []-cong (No-names-inline A) (No-names-inline t) (No-names-inline u)
      (No-names-inline v)
