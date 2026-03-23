------------------------------------------------------------------------
-- Canonicity theorems for natural numbers and the empty type
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
import Definition.Untyped
open import Graded.Modality

module Definition.Typed.Consequences.Canonicity
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  (open Definition.Untyped M)
  {m} {∇ : DCon (Term 0) m}
  where

open Type-restrictions R

open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Neutral.Atomic M type-variant
open import Definition.Untyped.Properties M

open import Definition.Typed R
import Definition.Typed.Consequences.Inequality R as I
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Syntactic R
open import Definition.Typed.Well-formed R
open import Definition.Typed.EqRelInstance R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Substitution.Introductions R
open import Definition.LogicalRelation.Fundamental.Reducibility R
open import Definition.LogicalRelation.Unary R

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum as ⊎
open import Tools.Vec using (ε)

private
  variable
    α n     : Nat
    x       : Fin _
    V       : Set _
    A t u v : Term _
    l       : Lvl _
    Δ       : Con _ _
    Γ       : Cons _ _

opaque

  -- Canonicity for natural numbers.

  canonicity : ∇ » ε ⊢ t ∷ ℕ → ∃ λ n → glassify ∇ » ε ⊢ t ≡ sucⁿ n ∷ ℕ
  canonicity {t} ⊢t = $⟨ ⊢t ⟩
    ∇ » ε ⊢ t ∷ ℕ                              →⟨ glassify-⊢ ⟩
    glassify ∇ » ε ⊢ t ∷ ℕ                     →⟨ ⊩∷ℕ⇔ .proj₁ ∘→ proj₂ ∘→ reducible-⊩∷ ⦃ inc = ε ⦄ ⟩
    glassify ∇ » ε ⊩ℕ t ∷ℕ                     →⟨ lemma ⟩
    (∃ λ n → glassify ∇ » ε ⊢ t ≡ sucⁿ n ∷ ℕ)  □
    where
    lemma : glassify ∇ » ε ⊩ℕ u ∷ℕ → ∃ λ n → glassify ∇ » ε ⊢ u ≡ sucⁿ n ∷ ℕ
    lemma (ℕₜ v u⇒*v _ ⊩v) =
      Σ.map idᶠ (trans (subset*Term u⇒*v))
        (case ⊩v of λ where
           (ne (neNfₜ u-ne _)) → ⊥-elim (glass-closed-no-ne (ne⁻ u-ne))
           zeroᵣ               → 0 , refl (zeroⱼ (wf (glassify-⊢ ⊢t)))
           (sucᵣ ⊩u)           → Σ.map 1+ suc-cong (lemma ⊩u))

-- Only-Level-or-U Δ holds if Δ is a context that only contains
-- assumptions where the type is (syntactically) Level or U t for some
-- t.

data Only-Level-or-U : Con Term n → Set a where
  ε       : Only-Level-or-U ε
  _∙Level : Only-Level-or-U Δ → Only-Level-or-U (Δ ∙ Level)
  _∙U     : Only-Level-or-U Δ → Only-Level-or-U (Δ ∙ U l)

opaque

  -- If x ∷ A ∈ Δ and Δ satisfies Only-Level-or-U, then A is equal to
  -- either Level or U t (for some t).

  Only-Level-or-U→∈→≡Level⊎≡U :
    Only-Level-or-U Δ → x ∷ A ∈ Δ → A PE.≡ Level ⊎ ∃ λ t → A PE.≡ U t
  Only-Level-or-U→∈→≡Level⊎≡U ε          ()
  Only-Level-or-U→∈→≡Level⊎≡U (_ ∙Level) here =
    inj₁ PE.refl
  Only-Level-or-U→∈→≡Level⊎≡U (_ ∙U) here =
    inj₂ (_ , PE.refl)
  Only-Level-or-U→∈→≡Level⊎≡U (only ∙Level) (there x∈) =
    ⊎.map (PE.cong wk1) (Σ.map _ (PE.cong wk1)) $
    Only-Level-or-U→∈→≡Level⊎≡U only x∈
  Only-Level-or-U→∈→≡Level⊎≡U (only ∙U) (there x∈) =
    ⊎.map (PE.cong wk1) (Σ.map _ (PE.cong wk1)) $
    Only-Level-or-U→∈→≡Level⊎≡U only x∈

opaque

  -- If the neutral term t has type A with respect to a transparent
  -- context Γ that only contains level or universe assumptions, then
  -- A is definitionally equal to Level or some universe, and t is a
  -- variable or an application of _supᵘ_ (assuming that equality
  -- reflection is not allowed).

  Only-Level-or-U→Neutral→≡Level⊎≡U :
    ⦃ ok : No-equality-reflection ⦄ →
    Transparent (Γ .defs) → Only-Level-or-U (Γ .vars) →
    Γ ⊢ t ∷ A → Neutral V (Γ .defs) t →
    (Γ ⊢ A ≡ Level ⊎ ∃ λ u → Γ ⊢ A ≡ U u) ×
    ((∃ λ x → t PE.≡ var x) ⊎ (∃₂ λ u v → t PE.≡ u supᵘ v))
  Only-Level-or-U→Neutral→≡Level⊎≡U _ only ⊢x (var _ _) =
    let _ , x∈ , A≡ = inversion-var ⊢x in
    ⊎.map (flip (PE.subst (_⊢_≡_ _ _)) A≡)
      (Σ.map idᶠ (flip (PE.subst (_⊢_≡_ _ _)) A≡))
      (Only-Level-or-U→∈→≡Level⊎≡U only x∈) ,
    inj₁ (_ , PE.refl)
  Only-Level-or-U→Neutral→≡Level⊎≡U tr only _ (defn α↦) =
    ⊥-elim $ glass-↦⊘∈ $ PE.subst (_↦⊘∷_∈_ _ _) tr α↦
  Only-Level-or-U→Neutral→≡Level⊎≡U _ _ ⊢supᵘ (supᵘˡₙ _) =
    let _ , _ , A≡ = inversion-supᵘ ⊢supᵘ in
    inj₁ A≡ ,
    inj₂ (_ , _ , PE.refl)
  Only-Level-or-U→Neutral→≡Level⊎≡U _ _ ⊢supᵘ (supᵘʳₙ _) =
    let _ , _ , A≡ = inversion-supᵘ ⊢supᵘ in
    inj₁ A≡ ,
    inj₂ (_ , _ , PE.refl)
  Only-Level-or-U→Neutral→≡Level⊎≡U tr only ⊢lower (lowerₙ t-ne) =
    let _ , _ , ⊢t , A≡ = inversion-lower ⊢lower
        Lift≡ , _       =
          Only-Level-or-U→Neutral→≡Level⊎≡U tr only ⊢t t-ne
    in
    case Lift≡ of λ where
      (inj₁ ≡Level) →
        ⊥-elim $ I.Lift≢Level ⦃ ok = possibly-nonempty ⦄ ≡Level
      (inj₂ (_ , ≡U)) →
        ⊥-elim $ I.U≢Liftⱼ ⦃ ok = possibly-nonempty ⦄ (sym ≡U)
  Only-Level-or-U→Neutral→≡Level⊎≡U tr only ⊢app (∘ₙ t-ne) =
    let _ , _ , _ , ⊢t , _ , A≡ = inversion-app ⊢app
        Π≡ , _                  =
          Only-Level-or-U→Neutral→≡Level⊎≡U tr only ⊢t t-ne
    in
    case Π≡ of λ where
      (inj₁ ≡Level) →
        ⊥-elim $ I.Level≢ΠΣⱼ ⦃ ok = possibly-nonempty ⦄ (sym ≡Level)
      (inj₂ (_ , ≡U)) →
        ⊥-elim $ I.U≢ΠΣⱼ ⦃ ok = possibly-nonempty ⦄ (sym ≡U)
  Only-Level-or-U→Neutral→≡Level⊎≡U tr only ⊢fst (fstₙ t-ne) =
    let _ , _ , _ , _ , _ , ⊢t , A≡ = inversion-fst ⊢fst
        Σ≡ , _                      =
          Only-Level-or-U→Neutral→≡Level⊎≡U tr only ⊢t t-ne
    in
    case Σ≡ of λ where
      (inj₁ ≡Level) →
        ⊥-elim $ I.Level≢ΠΣⱼ ⦃ ok = possibly-nonempty ⦄ (sym ≡Level)
      (inj₂ (_ , ≡U)) →
        ⊥-elim $ I.U≢ΠΣⱼ ⦃ ok = possibly-nonempty ⦄ (sym ≡U)
  Only-Level-or-U→Neutral→≡Level⊎≡U tr only ⊢snd (sndₙ t-ne) =
    let _ , _ , _ , _ , _ , ⊢t , A≡ = inversion-snd ⊢snd
        Σ≡ , _                      =
          Only-Level-or-U→Neutral→≡Level⊎≡U tr only ⊢t t-ne
    in
    case Σ≡ of λ where
      (inj₁ ≡Level) →
        ⊥-elim $ I.Level≢ΠΣⱼ ⦃ ok = possibly-nonempty ⦄ (sym ≡Level)
      (inj₂ (_ , ≡U)) →
        ⊥-elim $ I.U≢ΠΣⱼ ⦃ ok = possibly-nonempty ⦄ (sym ≡U)
  Only-Level-or-U→Neutral→≡Level⊎≡U tr only ⊢nr (natrecₙ t-ne) =
    let _ , _ , _ , ⊢t , A≡ = inversion-natrec ⊢nr
        ℕ≡ , _              =
          Only-Level-or-U→Neutral→≡Level⊎≡U tr only ⊢t t-ne
    in
    case ℕ≡ of λ where
      (inj₁ ≡Level) →
        ⊥-elim $ I.Level≢ℕ ⦃ ok = possibly-nonempty ⦄ (sym ≡Level)
      (inj₂ (_ , ≡U)) →
        ⊥-elim $ I.U≢ℕ ⦃ ok = possibly-nonempty ⦄ (sym ≡U)
  Only-Level-or-U→Neutral→≡Level⊎≡U tr only ⊢pr (prodrecₙ t-ne) =
    let _ , _ , _ , _ , _ , _ , ⊢t , _ , A≡ = inversion-prodrec ⊢pr
        Σ≡ , _                              =
          Only-Level-or-U→Neutral→≡Level⊎≡U tr only ⊢t t-ne
    in
    case Σ≡ of λ where
      (inj₁ ≡Level) →
        ⊥-elim $ I.Level≢ΠΣⱼ ⦃ ok = possibly-nonempty ⦄ (sym ≡Level)
      (inj₂ (_ , ≡U)) →
        ⊥-elim $ I.U≢ΠΣⱼ ⦃ ok = possibly-nonempty ⦄ (sym ≡U)
  Only-Level-or-U→Neutral→≡Level⊎≡U tr only ⊢er (emptyrecₙ t-ne) =
    let _ , ⊢t , A≡ = inversion-emptyrec ⊢er
        Empty≡ , _  = Only-Level-or-U→Neutral→≡Level⊎≡U tr only ⊢t t-ne
    in
    case Empty≡ of λ where
      (inj₁ ≡Level) →
        ⊥-elim $ I.Level≢Empty ⦃ ok = possibly-nonempty ⦄ (sym ≡Level)
      (inj₂ (_ , ≡U)) →
        ⊥-elim $ I.U≢Emptyⱼ ⦃ ok = possibly-nonempty ⦄ (sym ≡U)
  Only-Level-or-U→Neutral→≡Level⊎≡U tr only ⊢ur (unitrecₙ _ t-ne) =
    let _ , ⊢t , _ , A≡ = inversion-unitrec ⊢ur
        Unit≡ , _       =
          Only-Level-or-U→Neutral→≡Level⊎≡U tr only ⊢t t-ne
    in
    case Unit≡ of λ where
      (inj₁ ≡Level) →
        ⊥-elim $ I.Level≢Unitⱼ ⦃ ok = possibly-nonempty ⦄ (sym ≡Level)
      (inj₂ (_ , ≡U)) →
        ⊥-elim $ I.U≢Unitⱼ ⦃ ok = possibly-nonempty ⦄ (sym ≡U)
  Only-Level-or-U→Neutral→≡Level⊎≡U tr only ⊢J (Jₙ t-ne) =
    let _ , _ , _ , _ , _ , ⊢t , A≡ = inversion-J ⊢J
        Id≡ , _                     =
          Only-Level-or-U→Neutral→≡Level⊎≡U tr only ⊢t t-ne
    in
    case Id≡ of λ where
      (inj₁ ≡Level) →
        ⊥-elim $ I.Level≢Id ⦃ ok = possibly-nonempty ⦄ (sym ≡Level)
      (inj₂ (_ , ≡U)) →
        ⊥-elim $ I.Id≢U ⦃ ok = possibly-nonempty ⦄ ≡U
  Only-Level-or-U→Neutral→≡Level⊎≡U tr only ⊢K (Kₙ t-ne) =
    let _ , _ , _ , _ , ⊢t , _ , A≡ = inversion-K ⊢K
        Id≡ , _                     =
          Only-Level-or-U→Neutral→≡Level⊎≡U tr only ⊢t t-ne
    in
    case Id≡ of λ where
      (inj₁ ≡Level) →
        ⊥-elim $ I.Level≢Id ⦃ ok = possibly-nonempty ⦄ (sym ≡Level)
      (inj₂ (_ , ≡U)) →
        ⊥-elim $ I.Id≢U ⦃ ok = possibly-nonempty ⦄ ≡U
  Only-Level-or-U→Neutral→≡Level⊎≡U tr only ⊢bc ([]-congₙ t-ne) =
    let _ , _ , _ , _ , ⊢t , _ , A≡ = inversion-[]-cong ⊢bc
        Id≡ , _                     =
          Only-Level-or-U→Neutral→≡Level⊎≡U tr only ⊢t t-ne
    in
    case Id≡ of λ where
      (inj₁ ≡Level) →
        ⊥-elim $ I.Level≢Id ⦃ ok = possibly-nonempty ⦄ (sym ≡Level)
      (inj₂ (_ , ≡U)) →
        ⊥-elim $ I.Id≢U ⦃ ok = possibly-nonempty ⦄ ≡U

opaque

  -- Canonicity for natural numbers for transparent contexts Γ that
  -- satisfy Only-Level-or-U (Γ .vars) (under the assumption that
  -- equality reflection is not allowed).
  --
  -- This lemma is similar to a conjecture in "Type Theory with
  -- Explicit Universe Polymorphism" by Bezem, Coquand, Dybjer and
  -- Escardó (that conjecture restricts the contexts to only contain
  -- level variables).

  canonicity-Only-Level-or-U :
    ⦃ ok : No-equality-reflection ⦄ →
    Transparent (Γ .defs) → Only-Level-or-U (Γ .vars) →
    Γ ⊢ t ∷ ℕ → ∃ λ n → Γ ⊢ t ≡ sucⁿ n ∷ ℕ
  canonicity-Only-Level-or-U {Γ} tr only ⊢t =
    lemma $ ⊩∷ℕ⇔ .proj₁ $
    reducible-⊩∷ ⦃ inc = possibly-nonempty ⦄ ⊢t .proj₂
    where
    lemma : Γ ⊩ℕ u ∷ℕ → ∃ λ n → Γ ⊢ u ≡ sucⁿ n ∷ ℕ
    lemma (ℕₜ v u⇒*v _ ⊩v) =
      Σ.map idᶠ (trans (subset*Term u⇒*v))
        (case ⊩v of λ where
           zeroᵣ                 → 0 , refl (zeroⱼ (wf ⊢t))
           (sucᵣ ⊩u)             → Σ.map 1+ suc-cong (lemma ⊩u)
           (ne (neNfₜ u-ne u≡u)) →
             let _ , ⊢u , _ = wf-⊢≡∷ u≡u in
             case Only-Level-or-U→Neutral→≡Level⊎≡U
                    tr only ⊢u (ne⁻ u-ne) .proj₁ of λ where
               (inj₁ ≡Level) →
                 ⊥-elim $ I.Level≢ℕ ⦃ ok = possibly-nonempty ⦄ $
                 sym ≡Level
               (inj₂ (_ , ≡U)) →
                 ⊥-elim $ I.U≢ℕ ⦃ ok = possibly-nonempty ⦄ (sym ≡U))

opaque

  -- Canonicity for the empty type in glass contexts.

  ¬Empty′ : ¬ glassify ∇ » ε ⊢ t ∷ Empty
  ¬Empty′ {t} =
    glassify ∇ » ε ⊢ t ∷ Empty      →⟨ ⊩∷Empty⇔ .proj₁ ∘→ proj₂ ∘→ reducible-⊩∷ ⦃ inc = ε ⦄ ⟩
    glassify ∇ » ε ⊩Empty t ∷Empty  →⟨ (λ { (Emptyₜ _ _ _ (ne (neNfₜ u-ne _))) →
                                            glass-closed-no-ne (ne⁻ u-ne) }) ⟩
    ⊥                               □

opaque

  -- Canonicity for the empty type.

  ¬Empty : ¬ ∇ » ε ⊢ t ∷ Empty
  ¬Empty = ¬Empty′ ∘→ glassify-⊢

opaque

  -- There can be no well-typed definition of the empty type.

  ¬defn-Empty′ : » ∇ → α ↦∷ A ∈ ∇ → ¬ ∇ » ε ⊢ A ≡ Empty
  ¬defn-Empty′ »∇ α↦∷A A≡Empty = ¬Empty′ $
      conv (wf-↦∷∈ (glassify-↦∈′ α↦∷A .proj₂) (glassify-» »∇)) (glassify-⊢ A≡Empty)

opaque

  -- There can be no well-typed definition annotated with the empty type.

  ¬defn-Empty : » ∇ → ¬ α ↦∷ Empty ∈ ∇
  ¬defn-Empty »∇ α↦∷Empty =
    ¬defn-Empty′ »∇ α↦∷Empty (refl (⊢Empty (ε »∇)))

opaque

  -- Every closed equality proof reduces to rfl.

  ε⊢⇒*rfl∷Id : ∇ » ε ⊢ v ∷ Id A t u → glassify ∇ » ε ⊢ v ⇒* rfl ∷ Id A t u
  ε⊢⇒*rfl∷Id ⊢v =
    case ⊩∷Id⇔ .proj₁ $
         reducible-⊩∷ ⦃ inc = ε ⦄ (glassify-⊢ ⊢v) .proj₂ of λ
      (_ , v⇒*w , _ , _ , rest) →
    case rest of λ where
      (rflᵣ _)    → v⇒*w
      (ne w-ne _) → ⊥-elim $ glass-closed-no-ne (ne⁻ w-ne)

opaque

  -- If Id A t u is inhabited in the empty context, then t is
  -- definitionally equal to u at type A.

  ε⊢∷Id→ε⊢≡∷ : ∇ » ε ⊢ v ∷ Id A t u → glassify ∇ » ε ⊢ t ≡ u ∷ A
  ε⊢∷Id→ε⊢≡∷ {v} {A} {t} {u} =
    ∇ » ε ⊢ v ∷ Id A t u                  →⟨ ε⊢⇒*rfl∷Id ⟩
    glassify ∇ » ε ⊢ v ⇒* rfl ∷ Id A t u  →⟨ proj₂ ∘→ proj₂ ∘→ syntacticEqTerm ∘→ subset*Term ⟩
    glassify ∇ » ε ⊢ rfl ∷ Id A t u       →⟨ inversion-rfl-Id ⦃ ok = ε ⦄ ⟩
    glassify ∇ » ε ⊢ t ≡ u ∷ A            □

opaque
  unfolding Trans

  -- In a non-glass empty context, Id A t u being inhabited is not
  -- sufficient to conclude definitional equality.

  ε⊢∷Id↛ε⊢≡∷ :
    Opacity-allowed →
    ∃₅ λ (∇ : DCon (Term 0) 2) A t u v →
    ∇ » ε ⊢ v ∷ Id A t u × ¬ ∇ » ε ⊢ t ≡ u ∷ A
  ε⊢∷Id↛ε⊢≡∷ ok =
    let ∇ = ε ∙⟨ opa ε     ⟩[ zero ∷ ℕ ]
              ∙⟨ opa (ε ¹) ⟩[ rfl  ∷ Id ℕ zero (defn 0) ]
        ⊢ε = ε ∙ᵒ⟨ ok ⟩[ zeroⱼ εε ∷ ⊢ℕ εε ]
        ⊢εᵗ = ε ∙ᵗ[ zeroⱼ εε ]
        ⊢Id = Idⱼ (⊢ℕ ⊢ε) (zeroⱼ ⊢ε) (defn ⊢ε here PE.refl)
        ⊢α₀ = defn ⊢εᵗ here PE.refl
        ⊢rfl = conv (rflⱼ ⊢α₀)
                    (Id-cong (refl (⊢ℕ ⊢εᵗ))
                             (δ-red ⊢εᵗ here PE.refl PE.refl)
                             (refl ⊢α₀))
        ⊢α₁ = defn (ε ∙ᵒ⟨ ok ⟩[ ⊢rfl ∷ ⊢Id ]) here PE.refl
        not = I.zero≢ne ⦃ ok = ε ⦄ _ (defn⁺ (there here))
    in  ∇ , ℕ , zero , defn 0 , defn 1 , ⊢α₁ , not
