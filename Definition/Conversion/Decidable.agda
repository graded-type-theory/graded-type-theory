------------------------------------------------------------------------
-- The algorithmic equality is decidable (in the absence of equality
-- reflection)
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality
import Tools.PropositionalEquality as PE
open import Tools.Relation

module Definition.Conversion.Decidable
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  (_≟_ : Decidable (PE._≡_ {A = M}))
  ⦃ no-equality-reflection : No-equality-reflection ⦄
  where

open import Definition.Untyped M
open import Definition.Untyped.Allowed-literal R
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Neutral.Atomic M type-variant
open import Definition.Untyped.Properties M
open import Definition.Untyped.Whnf M type-variant
open import Definition.Typed R
open import Definition.Typed.EqRelInstance R using (eqRelInstance)
open import Definition.Typed.EqualityRelation.Instance R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Type R
open import Definition.Typed.Stability R
open import Definition.Typed.Substitution R
open import Definition.Typed.Well-formed R
open import Definition.Conversion R
open import Definition.Conversion.Level R
open import Definition.Conversion.Inversion R
open import Definition.Conversion.Whnf R
open import Definition.Conversion.Soundness R
open import Definition.Conversion.Symmetry R
open import Definition.Conversion.Transitivity R
open import Definition.Conversion.Stability R
open import Definition.Conversion.Conversion R
open import Definition.Conversion.Lift R
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Consequences.Reduction R
open import Definition.Typed.Consequences.Equality R
open import Definition.Typed.Consequences.NeTypeEq R

open import Tools.Bool
open import Tools.Fin
open import Tools.Function
open import Tools.List hiding (_∷_)
open import Tools.Nat using (Nat; _≤?_) renaming (_≟_ to _≟⁺_)
open import Tools.Product
open import Tools.Empty
open import Tools.Sum using (inj₁; inj₂; _⊎-dec_)

private
  variable
    κ ℓ n : Nat
    ∇ : DCon (Term 0) κ
    Δ Η : Con Term ℓ
    Γ : Cons _ _
    A A₁ A₂ A′ B B₁ B₂ B′ C₁ C₂ t t₁ t₂ t′ u u₁ u₂ v₁ v₂ w₁ w₂ : Term _
    l l′ l₁ l₁′ l₂ l₂′ l₃ : Lvl _
    b₁ b₂ : BinderMode
    s₁ s₂ : Strength
    p p₁ p₂ p′ q q₁ q₂ q′ q′₁ q′₂ r₁ r₂ : M
    d : Bool

------------------------------------------------------------------------
-- Private definitions

private opaque

  -- Some lemmas used below.

  ~↓→∷ : Γ ⊢ t ~ u ↓ A → Γ ⊢ t ∷ A
  ~↓→∷ = proj₁ ∘→ proj₂ ∘→ wf-⊢ ∘→ soundness~↓

  ~∷→∷ : Γ ⊢ t ~ u ∷ A → Γ ⊢ t ∷ A
  ~∷→∷ = proj₁ ∘→ proj₂ ∘→ wf-⊢ ∘→ soundness~∷

  [conv↓]∷→∷ : Γ ⊢ t [conv↓] u ∷ A → Γ ⊢ t ∷ A
  [conv↓]∷→∷ = proj₁ ∘→ proj₂ ∘→ wf-⊢ ∘→ soundnessConv↓Term

  ~↓→∷→Whnf×≡ : Γ ⊢ t ~ u ↓ A → Γ ⊢ t ∷ B → Γ ⊢ B ≡ A × Whnf (Γ .defs) A
  ~↓→∷→Whnf×≡ t~u ⊢t =
    let A-whnf , t-ne , _ = ne~↓ t~u in
    neTypeEq (ne⁻ t-ne) ⊢t (~↓→∷ t~u) , A-whnf

  ~∷→∷→~∷ : Γ ⊢ t ~ u ∷ A → Γ ⊢ t ∷ B → Γ ⊢ t ~ u ∷ B
  ~∷→∷→~∷ t~u ⊢t =
    let t-ne , _ = ne~∷ t~u
        ⊢t∷A = ~∷→∷ t~u
    in
    conv~∷ (reflConEq (wf ⊢t∷A)) (neTypeEq (ne⁻ t-ne) ⊢t∷A ⊢t) t~u

private opaque

  -- A lemma used below.

  [conv↓]∷ℕ→~↓ℕ :
    Γ ⊢ t ~ t′ ↓ ℕ →
    Γ ⊢ t [conv↓] u ∷ ℕ →
    Γ ⊢ t ~ u ↓ ℕ
  [conv↓]∷ℕ→~↓ℕ ([~] _ _ t~t′) t≡u =
    case inv-[conv↓]∷-ℕ t≡u of λ where
      (inj₁ t~u)                          → t~u
      (inj₂ (inj₁ (PE.refl , _)))         → ⊥-elim (inv-zero~ t~t′)
      (inj₂ (inj₂ (_ , _ , PE.refl , _))) → ⊥-elim (inv-suc~ t~t′)

private opaque

  -- A lemma used below.

  [conv↓]∷Σʷ→~↓ :
    Γ ⊢ t ~ t′ ↓ Σʷ p′ , q′ ▷ A′ ▹ B′ →
    Γ ⊢ t [conv↓] u ∷ Σʷ p , q ▷ A ▹ B →
    ∃ λ C → Γ ⊢ t ~ u ↓ C
  [conv↓]∷Σʷ→~↓ ([~] _ _ t~t′) t≡u =
    case inv-[conv↓]∷-Σʷ t≡u of λ where
      (inj₁ (_ , _ , _ , _ , t~u))         → _ , t~u
      (inj₂ (_ , _ , _ , _ , PE.refl , _)) → ⊥-elim (inv-prod~ t~t′)

private opaque

  -- A lemma used below.

  ≡starʷ→~↓Unitʷ→Unitʷ-η :
    Γ ⊢ t ~ u ↓ Unitʷ →
    Γ ⊢ t [conv↓] starʷ ∷ Unitʷ →
    Unitʷ-η
  ≡starʷ→~↓Unitʷ→Unitʷ-η ([~] _ _ t~u) t≡star =
    case inv-[conv↓]∷-Unitʷ t≡star of λ where
      (inj₂ (η , _))                       → η
      (inj₁ (no-η , inj₁ ([~] _ _ ~star))) → ⊥-elim (inv-~star ~star)
      (inj₁ (no-η , inj₂ (PE.refl , _)))   → ⊥-elim (inv-star~ t~u)

private opaque

  -- A lemma used below.

  dec~↑-lower-cong :
    Γ ⊢ t ∷ Lift l A →
    Dec (∃ λ C → Γ ⊢ t ~ u ↓ C) →
    Dec (∃ λ C → Γ ⊢ lower t ~ lower u ↑ C)
  dec~↑-lower-cong ⊢t (yes (_ , t~u)) =
    yes $
      case uncurry Lift≡A (~↓→∷→Whnf×≡ t~u ⊢t) of λ {
        (_ , _ , PE.refl) →
      _ , lower-cong t~u }
  dec~↑-lower-cong _ (no not-equal) =
    no λ (_ , lower-t~lower-u) →
    case inv-lower~ lower-t~lower-u of λ {
      (_ , _ , PE.refl , t~) →
    not-equal (_ , t~) }

private opaque

  -- A lemma used below.

  dec~↑-app-cong :
    Γ ⊢ t₁ ∷ Π p₁ , q₁ ▷ A₁ ▹ B₁ →
    Γ ⊢ u₁ ∷ Π p₂ , q₂ ▷ A₂ ▹ B₂ →
    Dec (∃ λ C → Γ ⊢ t₁ ~ u₁ ↓ C) →
    (Γ ⊢ A₁ ≡ A₂ → Dec (Γ ⊢ t₂ [conv↑] u₂ ∷ A₁)) →
    Dec (∃ λ C → Γ ⊢ t₁ ∘⟨ p₁ ⟩ t₂ ~ u₁ ∘⟨ p₂ ⟩ u₂ ↑ C)
  dec~↑-app-cong
    {p₁} {q₁} {A₁} {B₁} {p₂} {q₂} {A₂} {B₂}
    ⊢t₁ ⊢u₁ (yes (C , t₁~u₁)) dec₂ =
    let C-whnf , t₁-ne , u₁-ne = ne~↓ t₁~u₁
        _ , ⊢t₁′ , ⊢u₁′        = wf-⊢ (soundness~↓ t₁~u₁)
        Π≡C                    = neTypeEq (ne⁻ t₁-ne) ⊢t₁ ⊢t₁′
        A₁≡A₂ , _ , p₁≡p₂ , _  =
          ΠΣ-injectivity
            (Π p₁ , q₁ ▷ A₁ ▹ B₁  ≡⟨ Π≡C ⟩⊢
             C                    ≡˘⟨ neTypeEq (ne⁻ u₁-ne) ⊢u₁ ⊢u₁′ ⟩⊢∎
             Π p₂ , q₂ ▷ A₂ ▹ B₂  ∎)
    in
    case dec₂ A₁≡A₂ of λ where
      (yes t₂≡u₂) →
        yes $
        let _ , _ , C≡Π = ΠΣ≡Whnf Π≡C C-whnf in
          _
        , PE.subst (flip (_⊢_~_↑_ _ _) _)
            (PE.cong (_ ∘⟨_⟩ _) p₁≡p₂)
            (app-cong (PE.subst (_⊢_~_↓_ _ _ _) C≡Π t₁~u₁)
               (convConv↑Term
                  (ΠΣ-injectivity (PE.subst (_⊢_≡_ _ _) C≡Π Π≡C) .proj₁)
                  t₂≡u₂))
      (no t₂≢u₂) →
        no λ (_ , t~u) →
        let _ , _ , _ , _ , _ , _ , u≡∘ , t₁~ , t₂≡ = inv-∘~ t~u
            _ , _ , ≡u₂                             =
              ∘-PE-injectivity (PE.sym u≡∘)
            Π≡Π = neTypeEq (ne⁻ t₁-ne) ⊢t₁ (~↓→∷ t₁~)
        in
        t₂≢u₂ $
        convConv↑Term (sym (ΠΣ-injectivity Π≡Π .proj₁)) $
        PE.subst (flip (_⊢_[conv↑]_∷_ _ _) _) ≡u₂ t₂≡
  dec~↑-app-cong _ _ (no ¬t₁~u₁) _ =
    no λ (_ , t~u) →
    let _ , _ , _ , _ , _ , _ , u≡∘ , t₁~ , _ = inv-∘~ t~u
        _ , ≡u₁ , _                           =
          ∘-PE-injectivity (PE.sym u≡∘)
    in
    ¬t₁~u₁ (_ , PE.subst (flip (_⊢_~_↓_ _ _) _) ≡u₁ t₁~)

private opaque

  -- A lemma used below.

  dec~↑-fst-cong :
    Γ ⊢ t ∷ Σˢ p , q ▷ A ▹ B →
    Dec (p PE.≡ p′ × ∃ λ C → Γ ⊢ t ~ u ↓ C) →
    Dec (∃ λ C → Γ ⊢ fst p t ~ fst p′ u ↑ C)
  dec~↑-fst-cong ⊢t (yes (PE.refl , _ , t~u)) =
    yes $
    let _ , _ , C≡Σ = uncurry ΠΣ≡Whnf (~↓→∷→Whnf×≡ t~u ⊢t) in
    _ , fst-cong (PE.subst (_⊢_~_↓_ _ _ _) C≡Σ t~u)
  dec~↑-fst-cong _ (no not-both-equal) =
    no λ (_ , fst-t~fst-u) →
    case inv-fst~ fst-t~fst-u of λ {
      (_ , _ , _ , PE.refl , t~) →
    not-both-equal (PE.refl , _ , t~) }

private opaque

  -- A lemma used below.

  dec~↑-snd-cong :
    Γ ⊢ t ∷ Σˢ p , q ▷ A ▹ B →
    Dec (p PE.≡ p′ × ∃ λ C → Γ ⊢ t ~ u ↓ C) →
    Dec (∃ λ C → Γ ⊢ snd p t ~ snd p′ u ↑ C)
  dec~↑-snd-cong ⊢t (yes (PE.refl , _ , t~u)) =
    yes $
    let _ , _ , C≡Σ = uncurry ΠΣ≡Whnf (~↓→∷→Whnf×≡ t~u ⊢t) in
    _ , snd-cong (PE.subst (_⊢_~_↓_ _ _ _) C≡Σ t~u)
  dec~↑-snd-cong _ (no not-both-equal) =
    no λ (_ , snd-t~snd-u) →
    case inv-snd~ snd-t~snd-u of λ {
      (_ , _ , _ , _ , _ , PE.refl , t~) →
    not-both-equal (PE.refl , _ , t~) }

private opaque

  -- A lemma used below.

  dec~↑-prodrec-cong :
    ∇ » Δ ⊢ t₁ ∷ Σʷ p₁ , q₁ ▷ A₁ ▹ B₁ →
    ∇ » Δ ⊢ t₂ ∷ Σʷ p₂ , q₂ ▷ A₂ ▹ B₂ →
    Dec
      (r₁ PE.≡ r₂ × q′₁ PE.≡ q′₂ ×
       ∃ λ D → ∇ » Δ ⊢ t₁ ~ t₂ ↓ D) →
    (∇ »⊢ Δ ∙ Σʷ p₁ , q₁ ▷ A₁ ▹ B₁ ≡ Δ ∙ Σʷ p₂ , q₂ ▷ A₂ ▹ B₂ →
     Dec (∇ » Δ ∙ Σʷ p₁ , q₁ ▷ A₁ ▹ B₁ ⊢ C₁ [conv↑] C₂)) →
    (∇ »⊢ Δ ∙ A₂ ∙ B₂ ≡ Δ ∙ A₁ ∙ B₁ →
     ∇ » Δ ∙ A₂ ∙ B₂ ⊢ C₂ [ prodʷ p₂ (var x1) (var x0) ]↑² ≡
       C₁ [ prodʷ p₁ (var x1) (var x0) ]↑² →
     Dec
       (∇ » Δ ∙ A₁ ∙ B₁ ⊢ u₁ [conv↑] u₂ ∷
          C₁ [ prodʷ p₁ (var x1) (var x0) ]↑²)) →
    Dec
      (∃ λ D →
       ∇ » Δ ⊢ prodrec r₁ p₁ q′₁ C₁ t₁ u₁ ~ prodrec r₂ p₂ q′₂ C₂ t₂ u₂ ↑ D)
  dec~↑-prodrec-cong
    {p₁} {q₁} {A₁} {B₁} {p₂} {q₂} {A₂} {B₂}
    ⊢t₁ ⊢t₂ (yes (PE.refl , PE.refl , D , t₁~t₂)) dec₁ dec₃ =
    let D-whnf , t₁-ne , t₂-ne = ne~↓ t₁~t₂
        _ , ⊢t₁′ , ⊢t₂′        = wf-⊢ (soundness~↓ t₁~t₂)
        Σ₁≡D                   = neTypeEq (ne⁻ t₁-ne) ⊢t₁ ⊢t₁′
        Σ₁≡Σ₂                  =
          Σʷ p₁ , q₁ ▷ A₁ ▹ B₁  ≡⟨ Σ₁≡D ⟩⊢
          D                     ≡⟨ neTypeEq (ne⁻ t₂-ne) ⊢t₂′ ⊢t₂ ⟩⊢∎
          Σʷ p₂ , q₂ ▷ A₂ ▹ B₂  ∎
        A₁≡A₂ , B₁≡B₂ , p₁≡p₂ , _ =
          ΠΣ-injectivity-no-equality-reflection Σ₁≡Σ₂
        ΔA₁B₁≡ΔA₂B₂ = refl-∙ A₁≡A₂ _»⊢_≡_.∙ B₁≡B₂
    in
    case p₁≡p₂ of λ {
      PE.refl →
    case (dec₁ (refl-∙ Σ₁≡Σ₂)
            ×-dec′ λ C₁≡C₂ →
          dec₃
            (symConEq ΔA₁B₁≡ΔA₂B₂)
             (_⊢_≡_.sym $
              stability ΔA₁B₁≡ΔA₂B₂ $
              subst↑²TypeEq-prod (soundnessConv↑ C₁≡C₂))) of λ where
      (yes (C₁≡C₂ , u₁≡u₂)) →
        yes $
        case ΠΣ≡Whnf Σ₁≡D D-whnf of λ {
          (_ , _ , PE.refl) →
        let A₁≡ , B₁≡ , _ =
              ΠΣ-injectivity-no-equality-reflection Σ₁≡D
        in
          _
        , prodrec-cong (stabilityConv↑ (refl-∙ Σ₁≡D) C₁≡C₂) t₁~t₂
            (stabilityConv↑Term (refl-∙ A₁≡ ∙ B₁≡) u₁≡u₂) }
      (no not-both-equal) →
        no λ (_ , pr~pr) →
        let _ , _ , _ , _ , _ , _ , _ , pr≡pr , C₁≡ , t₁~ , u₁≡ =
              inv-prodrec~ pr~pr
            ≡A₁ , ≡B₁ , _ =
              ΠΣ-injectivity-no-equality-reflection
                (neTypeEq (ne⁻ t₁-ne) (~↓→∷ t₁~) ⊢t₁)
            _ , _ , _ , ≡C₂ , _ , ≡u₂ =
              prodrec-PE-injectivity (PE.sym pr≡pr)
        in
        not-both-equal
          ( stabilityConv↑
              (refl-∙ (neTypeEq (ne⁻ t₁-ne) (~↓→∷ t₁~) ⊢t₁))
              (PE.subst (_⊢_[conv↑]_ _ _) ≡C₂ C₁≡)
          , stabilityConv↑Term (refl-∙ ≡A₁ ∙ ≡B₁)
              (PE.subst (flip (_⊢_[conv↑]_∷_ _ _) _) ≡u₂ u₁≡)
          ) }
  dec~↑-prodrec-cong _ _ (no not-all-equal) _ _ =
    no λ (_ , pr~pr) →
    let _ , _ , _ , _ , _ , _ , _ , pr≡pr , _ , t₁~ , _ =
          inv-prodrec~ pr~pr
        r₁≡r₂ , _ , q′₁≡q′₂ , _ , ≡t₂ , _ =
          prodrec-PE-injectivity (PE.sym pr≡pr)
    in
    not-all-equal
      ( r₁≡r₂
      , q′₁≡q′₂
      , _ , PE.subst (flip (_⊢_~_↓_ _ _) _) ≡t₂ t₁~
      )

private opaque

  -- A lemma used below.

  dec~↑-emptyrec-cong :
    Γ ⊢ t₁ ∷ Empty →
    Dec
      (p₁ PE.≡ p₂ ×
       Γ ⊢ A₁ [conv↑] A₂ ×
       ∃ λ B → Γ ⊢ t₁ ~ t₂ ↓ B) →
    Dec (∃ λ B → Γ ⊢ emptyrec p₁ A₁ t₁ ~ emptyrec p₂ A₂ t₂ ↑ B)
  dec~↑-emptyrec-cong ⊢t₁ (yes (PE.refl , A₁≡A₂ , _ , t₁~t₂)) =
    yes $
    case uncurry Empty≡A (~↓→∷→Whnf×≡ t₁~t₂ ⊢t₁) of λ {
      PE.refl →
    _ , emptyrec-cong A₁≡A₂ t₁~t₂ }
  dec~↑-emptyrec-cong _ (no not-all-equal) =
    no λ (_ , er~er) →
    let _ , _ , _ , er≡er , A₁≡ , t₁~ = inv-emptyrec~ er~er
        p₁≡p₂ , ≡A₂ , ≡t₂             =
          emptyrec-PE-injectivity (PE.sym er≡er)
    in
    not-all-equal
      ( p₁≡p₂
      , PE.subst (_⊢_[conv↑]_ _ _) ≡A₂ A₁≡
      , _ , PE.subst (flip (_⊢_~_↓_ _ _) _) ≡t₂ t₁~
      )

private opaque

  -- A lemma used below.

  dec~↑-unitrec-cong :
    ¬ Unitʷ-η →
    ∇ » Δ ⊢ t₁ ∷ Unitʷ →
    Dec (p₁ PE.≡ p₂ × q₁ PE.≡ q₂ × ∃ λ B → ∇ » Δ ⊢ t₁ ~ t₂ ↓ B) →
    Dec (∇ » Δ ∙ Unitʷ ⊢ A₁ [conv↑] A₂) →
    (∇ » Δ ⊢ A₁ [ starʷ ]₀ ≡ A₂ [ starʷ ]₀ →
     Dec (∇ » Δ ⊢ u₁ [conv↑] u₂ ∷ A₁ [ starʷ ]₀)) →
    Dec
      (∃ λ B →
       ∇ » Δ ⊢ unitrec p₁ q₁ A₁ t₁ u₁ ~ unitrec p₂ q₂ A₂ t₂ u₂ ↑ B)
  dec~↑-unitrec-cong
    no-η ⊢t₁ (yes (PE.refl , PE.refl , _ , t₁~t₂)) dec₁ dec₂ =
    let ok = inversion-Unit (wf-⊢ ⊢t₁)
        ⊢Γ = wf ⊢t₁
    in case
      (dec₁ ×-dec′ λ A₁≡A₂ →
       dec₂ (subst-⊢≡₀ (soundnessConv↑ A₁≡A₂) (refl (starⱼ ⊢Γ ok))))
      of λ where
      (yes (A₁≡A₂ , u₁≡u₂)) →
        let B≡Unit = uncurry Unit≡A (~↓→∷→Whnf×≡ t₁~t₂ ⊢t₁) in
        yes $
        _ ,
        unitrec-cong A₁≡A₂ (PE.subst (_⊢_~_↓_ _ _ _) B≡Unit t₁~t₂) u₁≡u₂
          no-η
      (no not-both-equal) →
        no λ (_ , ur~ur) →
        case inv-unitrec~ ur~ur of λ
          (_ , _ , _ , _ , ur≡ur , A₁≡ , _ , u₁≡ , _) →
        case unitrec-PE-injectivity (PE.sym ur≡ur) of λ {
          (_ , _ , PE.refl , _ , PE.refl) →
        not-both-equal (A₁≡ , u₁≡) }
  dec~↑-unitrec-cong _ _ (no not-all-equal) _ _ =
    no λ (_ , ur~ur) →
    case inv-unitrec~ ur~ur of λ
      (_ , _ , _ , _ , ur≡ur , _ , t₁~ , _) →
    case unitrec-PE-injectivity (PE.sym ur≡ur) of λ {
      (p₁≡p₂ , q₁≡q₂ , PE.refl , PE.refl , _) →
    not-all-equal (p₁≡p₂ , q₁≡q₂ , _ , t₁~) }

private opaque

  -- A lemma used below.

  dec~↑-natrec-cong :
    ∇ » Δ ⊢ v₁ ∷ ℕ →
    Dec
      (p₁ PE.≡ p₂ × q₁ PE.≡ q₂ × r₁ PE.≡ r₂ ×
       ∇ » Δ ∙ ℕ ⊢ A₁ [conv↑] A₂ ×
       ∃ λ B → ∇ » Δ ⊢ v₁ ~ v₂ ↓ B) →
    (∇ » Δ ⊢ A₁ [ zero ]₀ ≡ A₂ [ zero ]₀ →
     Dec (∇ » Δ ⊢ t₁ [conv↑] t₂ ∷ A₁ [ zero ]₀)) →
    (∇ »⊢ Δ ∙ ℕ ∙ A₂ ≡ Δ ∙ ℕ ∙ A₁ →
     ∇ » Δ ∙ ℕ ∙ A₂ ⊢ A₂ [ suc (var x1) ]↑² ≡ A₁ [ suc (var x1) ]↑² →
     Dec (∇ » Δ ∙ ℕ ∙ A₁ ⊢ u₁ [conv↑] u₂ ∷ A₁ [ suc (var x1) ]↑²)) →
    Dec
      (∃ λ B →
       ∇ » Δ ⊢ natrec p₁ q₁ r₁ A₁ t₁ u₁ v₁ ~
         natrec p₂ q₂ r₂ A₂ t₂ u₂ v₂ ↑ B)
  dec~↑-natrec-cong
    ⊢v₁ (yes (PE.refl , PE.refl , PE.refl , A₁≡A₂ , _ , v₁~v₂)) dec₁
    dec₂ =
    case
      (let A₁≡A₂     = soundnessConv↑ A₁≡A₂
           ⊢Δ        = wf ⊢v₁
           ΔℕA₁≡ΔℕA₂ = refl-∙ (sym A₁≡A₂)
       in
       dec₁ (subst-⊢≡₀ A₁≡A₂ (refl (zeroⱼ ⊢Δ)))
         ×-dec
       dec₂ ΔℕA₁≡ΔℕA₂
         (stability (symConEq ΔℕA₁≡ΔℕA₂) $ sym $ sucCong A₁≡A₂))
      of λ where
      (yes (t₁≡t₂ , u₁≡u₂)) →
        yes $
        let B≡ℕ = uncurry ℕ≡A (~↓→∷→Whnf×≡ v₁~v₂ ⊢v₁) in
          _
        , natrec-cong A₁≡A₂ t₁≡t₂ u₁≡u₂
            (PE.subst (_⊢_~_↓_ _ _ _) B≡ℕ v₁~v₂)
      (no not-both-equal) →
        no λ (_ , nr~nr) →
        let _ , _ , _ , _ , _ , nr≡nr , _ , t₁≡ , u₁≡ , _ =
              inv-natrec~ nr~nr
            _ , _ , _ , _ , ≡t₂ , ≡u₂ , _ =
              natrec-PE-injectivity (PE.sym nr≡nr)
        in
        not-both-equal
          ( PE.subst (flip (_⊢_[conv↑]_∷_ _ _) _) ≡t₂ t₁≡
          , PE.subst (flip (_⊢_[conv↑]_∷_ _ _) _) ≡u₂ u₁≡
          )
  dec~↑-natrec-cong _ (no not-all-equal) _ _ =
    no λ (_ , nr~nr) →
    let _ , _ , _ , _ , _ , nr≡nr , A₁≡ , _ , _ , v₁~ =
          inv-natrec~ nr~nr
        p₁≡p₂ , q₁≡q₂ , r₁≡r₂ , ≡A₂ , _ , _ , ≡v₂ =
          natrec-PE-injectivity (PE.sym nr≡nr)
    in
    not-all-equal
      ( p₁≡p₂
      , q₁≡q₂
      , r₁≡r₂
      , PE.subst (_⊢_[conv↑]_ _ _) ≡A₂ A₁≡
      , _ , PE.subst (flip (_⊢_~_↓_ _ _) _) ≡v₂ v₁~
      )

private opaque

  -- A lemma used below.

  dec~↑-J-cong :
    ∇ » Δ ⊢ w₁ ∷ Id A₁ t₁ v₁ →
    Dec
      (p₁ PE.≡ p₂ × q₁ PE.≡ q₂ ×
       ∇ » Δ ⊢ A₁ [conv↑] A₂ ×
       ∃ λ C → ∇ » Δ ⊢ w₁ ~ w₂ ↓ C) →
    (∇ » Δ ⊢ A₁ ≡ A₂ → Dec (∇ » Δ ⊢ t₁ [conv↑] t₂ ∷ A₁)) →
    (∇ »⊢ Δ ∙ A₁ ∙ Id (wk1 A₁) (wk1 t₁) (var x0) ≡
       Δ ∙ A₂ ∙ Id (wk1 A₂) (wk1 t₂) (var x0) →
     Dec (∇ » Δ ∙ A₁ ∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊢ B₁ [conv↑] B₂)) →
    (∇ » Δ ⊢ B₁ [ t₁ , rfl ]₁₀ ≡ B₂ [ t₂ , rfl ]₁₀ →
     Dec (∇ » Δ ⊢ u₁ [conv↑] u₂ ∷ B₁ [ t₁ , rfl ]₁₀)) →
    (∇ » Δ ⊢ A₁ ≡ A₂ → Dec (∇ » Δ ⊢ v₁ [conv↑] v₂ ∷ A₁)) →
    Dec
      (∃ λ C →
       ∇ » Δ ⊢ J p₁ q₁ A₁ t₁ B₁ u₁ v₁ w₁ ~ J p₂ q₂ A₂ t₂ B₂ u₂ v₂ w₂ ↑ C)
  dec~↑-J-cong _ (no not-all-equal) _ _ _ _ =
    no λ (_ , J~J) →
    let _ , _ , _ , _ , _ , _ , _ , _ , J≡J , A₁≡ , _ , _ , _ , _ ,
          w₁~ , _ = inv-J~ J~J
        p₁≡p₂ , q₁≡q₂ , ≡A₂ , _ , _ , _ , _ , ≡w₂ =
          J-PE-injectivity (PE.sym J≡J)
    in
    not-all-equal
      ( p₁≡p₂
      , q₁≡q₂
      , PE.subst (_⊢_[conv↑]_ _ _) ≡A₂ A₁≡
      , _ , PE.subst (flip (_⊢_~_↓_ _ _) _) ≡w₂ w₁~
      )
  dec~↑-J-cong
    ⊢w₁ (yes (PE.refl , PE.refl , A₁≡A₂ , _ , w₁~w₂))
    dec₁ dec₂ dec₃ dec₄ =
    case
      (let A₁≡A₂ = soundnessConv↑ A₁≡A₂ in
       dec₁ A₁≡A₂
         ×-dec′ λ t₁≡t₂ →
       let t₁≡t₂ = soundnessConv↑Term t₁≡t₂ in
       dec₂ (J-motive-context-cong′ A₁≡A₂ t₁≡t₂)
         ×-dec′ λ B₁≡B₂ →
       dec₃ (J-motive-rfl-cong (soundnessConv↑ B₁≡B₂) t₁≡t₂)
         ×-dec
       dec₄ A₁≡A₂)
      of λ where
      (yes (t₁≡t₂ , B₁≡B₂ , u₁≡u₂ , v₁≡v₂)) →
        yes $
          _
        , J-cong A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁~w₂
            (neTypeEq (ne⁻ (ne~↓ w₁~w₂ .proj₂ .proj₁)) (~↓→∷ w₁~w₂) ⊢w₁)
      (no not-all-equal) →
        no λ (_ , J~J) →
        let _ , _ , _ , _ , _ , _ , _ , _ , J≡J , _ , t₁≡ , B₁≡ , u₁≡ ,
              v₁≡ , _ = inv-J~ J~J
            _ , _ , _ , ≡t₂ , ≡B₂ , ≡u₂ , ≡v₂ , _ =
              J-PE-injectivity (PE.sym J≡J)
        in
        not-all-equal
          ( PE.subst (flip (_⊢_[conv↑]_∷_ _ _) _) ≡t₂ t₁≡
          , PE.subst (_⊢_[conv↑]_ _ _) ≡B₂ B₁≡
          , PE.subst (flip (_⊢_[conv↑]_∷_ _ _) _) ≡u₂ u₁≡
          , PE.subst (flip (_⊢_[conv↑]_∷_ _ _) _) ≡v₂ v₁≡
          )

private opaque

  -- A lemma used below.

  dec~↑-K-cong :
    K-allowed →
    ∇ » Δ ⊢ v₁ ∷ Id A₁ t₁ t₁ →
    Dec
      (p₁ PE.≡ p₂ ×
       ∇ » Δ ⊢ A₁ [conv↑] A₂ ×
       ∃ λ C → ∇ » Δ ⊢ v₁ ~ v₂ ↓ C) →
    (∇ » Δ ⊢ A₁ ≡ A₂ → Dec (∇ » Δ ⊢ t₁ [conv↑] t₂ ∷ A₁)) →
    (∇ »⊢ Δ ∙ Id A₁ t₁ t₁ ≡ Δ ∙ Id A₂ t₂ t₂ →
     Dec (∇ » Δ ∙ Id A₁ t₁ t₁ ⊢ B₁ [conv↑] B₂)) →
    (∇ » Δ ⊢ B₁ [ rfl ]₀ ≡ B₂ [ rfl ]₀ →
     Dec (∇ » Δ ⊢ u₁ [conv↑] u₂ ∷ B₁ [ rfl ]₀)) →
    Dec (∃ λ C → ∇ » Δ ⊢ K p₁ A₁ t₁ B₁ u₁ v₁ ~ K p₂ A₂ t₂ B₂ u₂ v₂ ↑ C)
  dec~↑-K-cong _ _ (no not-all-equal) _ _ _ =
    no λ (_ , K~K) →
    let _ , _ , _ , _ , _ , _ , _ , K≡K , A₁≡ , _ , _ , _ , v₁~ , _ =
          inv-K~ K~K
        p₁≡p₂ , ≡A₂ , _ , _ , _ , ≡v₂ = K-PE-injectivity (PE.sym K≡K)
    in
    not-all-equal
      ( p₁≡p₂
      , PE.subst (_⊢_[conv↑]_ _ _) ≡A₂ A₁≡
      , _ , PE.subst (flip (_⊢_~_↓_ _ _) _) ≡v₂ v₁~
      )
  dec~↑-K-cong
    ok ⊢v₁ (yes (PE.refl , A₁≡A₂ , _ , v₁~v₂)) dec₁ dec₂ dec₃ =
    case
      (let A₁≡A₂ = soundnessConv↑ A₁≡A₂ in
       dec₁ A₁≡A₂
         ×-dec′ λ t₁≡t₂ →
       let t₁≡t₂ = soundnessConv↑Term t₁≡t₂ in
       dec₂ (K-motive-context-cong′ A₁≡A₂ t₁≡t₂)
         ×-dec′ λ B₁≡B₂ →
       dec₃ (K-motive-rfl-cong (soundnessConv↑ B₁≡B₂)))
      of λ where
      (yes (t₁≡t₂ , B₁≡B₂ , u₁≡u₂)) →
        yes $
          _
        , K-cong A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁~v₂
            (neTypeEq (ne⁻ (ne~↓ v₁~v₂ .proj₂ .proj₁)) (~↓→∷ v₁~v₂) ⊢v₁)
            ok
      (no not-all-equal) →
        no λ (_ , K~K) →
        let _ , _ , _ , _ , _ , _ , _ , K≡K , _ , t₁≡ , B₁≡ , u₁≡ , _ =
              inv-K~ K~K
            _ , _ , ≡t₂ , ≡B₂ , ≡u₂ , _ = K-PE-injectivity (PE.sym K≡K)
        in
        not-all-equal
          ( PE.subst (flip (_⊢_[conv↑]_∷_ _ _) _) ≡t₂ t₁≡
          , PE.subst (_⊢_[conv↑]_ _ _) ≡B₂ B₁≡
          , PE.subst (flip (_⊢_[conv↑]_∷_ _ _) _) ≡u₂ u₁≡
          )

private opaque

  -- A lemma used below.

  dec~↑-[]-cong-cong :
    let open Erased s₁ in
    []-cong-allowed s₁ →
    Γ ⊢ v₁ ∷ Id A₁ t₁ u₁ →
    Dec
      (s₁ PE.≡ s₂ ×
       Γ ⊢ l₁ [conv↑] l₂ ∷Level ×
       Γ ⊢ A₁ [conv↑] A₂ ×
       ∃ λ B → Γ ⊢ v₁ ~ v₂ ↓ B) →
    (Γ ⊢ A₁ ≡ A₂ → Dec (Γ ⊢ t₁ [conv↑] t₂ ∷ A₁)) →
    (Γ ⊢ A₁ ≡ A₂ → Dec (Γ ⊢ u₁ [conv↑] u₂ ∷ A₁)) →
    Dec
      (∃ λ B →
       Γ ⊢ []-cong s₁ l₁ A₁ t₁ u₁ v₁ ~ []-cong s₂ l₂ A₂ t₂ u₂ v₂ ↑ B)
  dec~↑-[]-cong-cong
    ok ⊢v₁ (yes (PE.refl , l₁≡l₂ , A₁≡A₂ , _ , v₁~v₂)) dec₁ dec₂ =
    case
       (let A₁≡A₂ = soundnessConv↑ A₁≡A₂ in
        dec₁ A₁≡A₂ ×-dec dec₂ A₁≡A₂)
      of λ where
      (yes (t₁≡t₂ , u₁≡u₂)) →
        yes $
          _
        , []-cong-cong l₁≡l₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁~v₂
            (neTypeEq (ne⁻ (ne~↓ v₁~v₂ .proj₂ .proj₁)) (~↓→∷ v₁~v₂) ⊢v₁)
            ok
      (no not-both-equal) →
        no λ (_ , bc~bc) →
        let _ , _ , _ , _ , _ , _ , _ , bc≡bc , _ , _ , t₁≡ , u₁≡ , _ =
              inv-[]-cong~ bc~bc
            _ , _ , _ , ≡t₂ , ≡u₂ , _ =
              []-cong-PE-injectivity (PE.sym bc≡bc)
        in
        not-both-equal
          ( PE.subst (flip (_⊢_[conv↑]_∷_ _ _) _) ≡t₂ t₁≡
          , PE.subst (flip (_⊢_[conv↑]_∷_ _ _) _) ≡u₂ u₁≡
          )
  dec~↑-[]-cong-cong _ _ (no not-all-equal) _ _ =
    no λ (_ , bc~bc) →
    let _ , _ , _ , _ , _ , _ , _ , bc≡bc , l₁≡ , A₁≡ , _ , _ , v₁~ , _ =
          inv-[]-cong~ bc~bc
        s₁≡s₂ , ≡l₂ , ≡A₂ , _ , _ , ≡v₂ =
          []-cong-PE-injectivity (PE.sym bc≡bc)
    in
    not-all-equal
      ( s₁≡s₂
      , PE.subst (_⊢_[conv↑]_∷Level _ _) ≡l₂ l₁≡
      , PE.subst (_⊢_[conv↑]_ _ _) ≡A₂ A₁≡
      , _ , PE.subst (flip (_⊢_~_↓_ _ _) _) ≡v₂ v₁~
      )

private opaque

  -- A lemma used below.

  decConv↓-ΠΣ :
    ΠΣ-allowed b₁ p₁ q₁ →
    Dec
      (b₁ PE.≡ b₂ × p₁ PE.≡ p₂ × q₁ PE.≡ q₂ ×
       ∇ » Δ ⊢ A₁ [conv↑] A₂) →
    (∇ »⊢ Δ ∙ A₁ ≡ Δ ∙ A₂ → Dec (∇ » Δ ∙ A₁ ⊢ B₁ [conv↑] B₂)) →
    Dec
      (∇ » Δ ⊢ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ [conv↓]
         ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂)
  decConv↓-ΠΣ ok (yes (PE.refl , PE.refl , PE.refl , A₁≡A₂)) dec =
    case dec (refl-∙ (soundnessConv↑ A₁≡A₂)) of λ where
      (yes B₁≡B₂) → yes (ΠΣ-cong A₁≡A₂ B₁≡B₂ ok)
      (no B₁≢B₂)  →
        no λ ΠΣ≡ΠΣ →
        let _ , _ , ΠΣ≡ΠΣ , _ , B₁≡ = inv-[conv↓]-ΠΣ ΠΣ≡ΠΣ
            _ , _ , _ , _ , ≡B₂     = ΠΣ-PE-injectivity (PE.sym ΠΣ≡ΠΣ)
        in
        B₁≢B₂ (PE.subst (_⊢_[conv↑]_ _ _) ≡B₂ B₁≡)
  decConv↓-ΠΣ _ (no not-all-equal) _ =
    no λ ΠΣ≡ΠΣ →
    let _ , _ , ΠΣ≡ΠΣ , A₁≡ , _         = inv-[conv↓]-ΠΣ ΠΣ≡ΠΣ
        b₁≡b₂ , p₁≡p₂ , q₁≡q₂ , ≡A₂ , _ =
          ΠΣ-PE-injectivity (PE.sym ΠΣ≡ΠΣ)
    in
    not-all-equal
      ( b₁≡b₂
      , p₁≡p₂
      , q₁≡q₂
      , PE.subst (_⊢_[conv↑]_ _ _) ≡A₂ A₁≡
      )

private opaque

  -- A lemma used below.

  decConv↓-Id :
    Dec (Γ ⊢ A₁ [conv↑] A₂) →
    (Γ ⊢ A₂ ≡ A₁ → Dec (Γ ⊢ t₁ [conv↑] t₂ ∷ A₁)) →
    (Γ ⊢ A₂ ≡ A₁ → Dec (Γ ⊢ u₁ [conv↑] u₂ ∷ A₁)) →
    Dec (Γ ⊢ Id A₁ t₁ u₁ [conv↓] Id A₂ t₂ u₂)
  decConv↓-Id (yes A₁≡A₂) dec₁ dec₂ =
    let A₂≡A₁ = _⊢_≡_.sym (soundnessConv↑ A₁≡A₂) in
    case dec₁ A₂≡A₁ ×-dec dec₂ A₂≡A₁ of λ where
      (yes (t₁≡t₂ , u₁≡u₂)) → yes (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂)
      (no not-both-equal)   →
        no λ Id≡Id →
        let _ , _ , _ , Id≡Id , _ , t₁≡ , u₁≡ = inv-[conv↓]-Id Id≡Id
            _ , ≡t₂ , ≡u₂                     =
              Id-PE-injectivity (PE.sym Id≡Id)
        in
        not-both-equal
          ( PE.subst (flip (_⊢_[conv↑]_∷_ _ _) _) ≡t₂ t₁≡
          , PE.subst (flip (_⊢_[conv↑]_∷_ _ _) _) ≡u₂ u₁≡
          )
  decConv↓-Id (no A₁≢A₂) _ _ =
    no λ Id≡Id →
    let _ , _ , _ , Id≡Id , A₁≡ , _ = inv-[conv↓]-Id Id≡Id
        ≡A₂ , _                     = Id-PE-injectivity (PE.sym Id≡Id)
    in
    A₁≢A₂ (PE.subst (_⊢_[conv↑]_ _ _) ≡A₂ A₁≡)

------------------------------------------------------------------------
-- Public definitions

mutual
  -- Decidability of algorithmic equality of neutral terms.
  dec~↑ : ∀ {k l R T k′ l′}
        → Γ ⊢ k ~ k′ ↑ R → Γ ⊢ l ~ l′ ↑ T
        → Dec (∃ λ A → Γ ⊢ k ~ l ↑ A)
  dec~↑ (var-refl {x} ⊢x _) u~ = case inv-~-var u~ of λ where
    (inj₁ (y , PE.refl , _)) → case x ≟ⱽ y of λ where
      (yes x≡y) → yes (_ , var-refl ⊢x x≡y)
      (no x≢y)  → no (x≢y ∘→ var-PE-injectivity ∘→ inv-~var ∘→ proj₂)
    (inj₂ (u≢var , _)) → no (u≢var ∘→ (_ ,_) ∘→ inv-var~ ∘→ proj₂)
  dec~↑ (defn-refl {α} ⊢α α↦⊘ _) u~ = case inv-~-defn u~ of λ where
    (inj₁ (β , _ , _ , PE.refl , _)) → case α ≟⁺ β of λ where
      (yes α≡β) → yes (_ , defn-refl ⊢α α↦⊘ α≡β)
      (no α≢β)  → no (α≢β ∘→ defn-PE-injectivity ∘→ inv-~defn ∘→ proj₂)
    (inj₂ (u≢defn , _)) → no (u≢defn ∘→ (_ ,_) ∘→ inv-defn~ ∘→ proj₂)
  dec~↑ (lower-cong t′~) u~ = case inv-~-lower u~ of λ where
    (inj₁ (_ , _ , _ , PE.refl , PE.refl , u′~)) →
      dec~↑-lower-cong (~↓→∷ t′~) (dec~↓ t′~ u′~)
    (inj₂ (u≢lower , _)) →
      no λ (_ , t~u) →
      let _ , _ , u≡lower , _ = inv-lower~ t~u in
      u≢lower (_ , u≡lower)
  dec~↑ (app-cong t₁~ t₂≡) u~ = case inv-~-∘ u~ of λ where
    (inj₁
       (_ , _ , _ , _ , _ , _ , _ , _ , _ ,
        PE.refl , _ , u₁~ , u₂≡)) →
      dec~↑-app-cong (~↓→∷ t₁~) (~↓→∷ u₁~) (dec~↓ t₁~ u₁~)
        (λ B₁≡C₁ → decConv↑TermConv B₁≡C₁ t₂≡ u₂≡)
    (inj₂ (u≢∘ , _)) →
      no λ (_ , t~u) →
      let _ , _ , _ , _ , _ , _ , u≡∘ , _ = inv-∘~ t~u in
      u≢∘ (_ , _ , _ , u≡∘)
  dec~↑ (fst-cong t′~) u~ = case inv-~-fst u~ of λ where
    (inj₁ (_ , _ , _ , _ , _ , PE.refl , _ , u′~)) →
      dec~↑-fst-cong (~↓→∷ t′~) (_ ≟ _ ×-dec dec~↓ t′~ u′~)
    (inj₂ (u≢fst , _)) →
      no λ (_ , t~u) →
      let _ , _ , _ , u≡fst , _ = inv-fst~ t~u in
      u≢fst (_ , _ , u≡fst)
  dec~↑ (snd-cong t′~) u~ = case inv-~-snd u~ of λ where
    (inj₁ (_ , _ , _ , _ , _ , _ , _ , PE.refl , _ , u′~)) →
      dec~↑-snd-cong (~↓→∷ t′~) (_ ≟ _ ×-dec dec~↓ t′~ u′~)
    (inj₂ (u≢snd , _)) →
      no λ (_ , t~u) →
      let _ , _ , _ , _ , _ , u≡snd , _ = inv-snd~ t~u in
      u≢snd (_ , _ , u≡snd)
  dec~↑ (prodrec-cong B≡ t₁~ t₂≡) u~ = case inv-~-prodrec u~ of λ where
    (inj₁
       (_ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ ,
        PE.refl , _ , C≡ , u₁~ , u₂≡)) →
      dec~↑-prodrec-cong (~↓→∷ t₁~) (~↓→∷ u₁~)
        (_ ≟ _ ×-dec _ ≟ _ ×-dec dec~↓ t₁~ u₁~)
        (λ eq → decConv↑′ eq B≡ C≡)
        (λ eq₁ eq₂ → decConv↑Term t₂≡ (convConv↑Term′ eq₁ eq₂ u₂≡))
    (inj₂ (u≢pr , _)) →
      no λ (_ , t~u) →
      let _ , _ , _ , _ , _ , _ , _ , u≡pr , _ = inv-prodrec~ t~u in
      u≢pr (_ , _ , _ , _ , _ , _ , u≡pr)
  dec~↑ (emptyrec-cong B≡ t′~) u~ = case inv-~-emptyrec u~ of λ where
    (inj₁ (_ , _ , _ , _ , PE.refl , _ , C≡ , u′~)) →
      dec~↑-emptyrec-cong (~↓→∷ t′~)
        (_ ≟ _ ×-dec decConv↑ B≡ C≡ ×-dec dec~↓ t′~ u′~)
    (inj₂ (u≢er , _)) →
      no λ (_ , t~u) →
      let _ , _ , _ , u≡er , _ = inv-emptyrec~ t~u in
      u≢er (_ , _ , _ , u≡er)
  dec~↑ (unitrec-cong B≡ t₁~ t₂≡ no-η) u~ =
    case inv-~-unitrec u~ of λ where
      (inj₁
         (_ , _ , _ , _ , _ , _ , _ , _ , _ ,
          PE.refl , _ , C≡ , u₁~ , u₂≡ , _)) →
        dec~↑-unitrec-cong no-η (~↓→∷ t₁~)
          (_ ≟ _ ×-dec _ ≟ _ ×-dec dec~↓ t₁~ u₁~)
          (decConv↑ B≡ C≡)
          (λ eq → decConv↑TermConv eq t₂≡ u₂≡)
      (inj₂ (u≢ur , _)) →
        no λ (_ , t~u) →
        let _ , _ , _ , _ , u≡ur , _ = inv-unitrec~ t~u in
        u≢ur (_ , _ , _ , _ , _ , u≡ur)
  dec~↑ (natrec-cong B≡ t₁≡ t₂≡ t₃~) u~ =
    case inv-~-natrec u~ of λ where
      (inj₁
         (_ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ ,
          PE.refl , _ , C≡ , u₁≡ , u₂≡ , u₃~)) →
        dec~↑-natrec-cong (~↓→∷ t₃~)
          (_ ≟ _ ×-dec _ ≟ _ ×-dec _ ≟ _ ×-dec decConv↑ B≡ C≡ ×-dec
           dec~↓ t₃~ u₃~)
          (λ eq → decConv↑TermConv eq t₁≡ u₁≡)
          (λ eq₁ eq₂ → decConv↑Term t₂≡ (convConv↑Term′ eq₁ eq₂ u₂≡))
      (inj₂ (u≢nr , _)) →
        no λ (_ , t~u) →
        let _ , _ , _ , _ , _ , u≡nr , _ = inv-natrec~ t~u in
        u≢nr (_ , _ , _ , _ , _ , _ , _ , u≡nr)
  dec~↑ (J-cong B₁≡ t₁≡ B₂≡ t₂≡ t₃≡ t₄~ B₃≡Id) u~ =
    case inv-~-J u~ of λ where
      (inj₁
         (_ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ ,
          _ , PE.refl , _ ,
          C₁≡ , u₁≡ , C₂≡ , u₂≡ , u₃≡ , u₄~ , _)) →
        dec~↑-J-cong (conv (~↓→∷ t₄~) B₃≡Id)
          (_ ≟ _ ×-dec _ ≟ _ ×-dec decConv↑ B₁≡ C₁≡ ×-dec dec~↓ t₄~ u₄~)
          (λ eq → decConv↑TermConv eq t₁≡ u₁≡)
          (λ eq → decConv↑′ eq B₂≡ C₂≡)
          (λ eq → decConv↑TermConv eq t₂≡ u₂≡)
          (λ eq → decConv↑TermConv eq t₃≡ u₃≡)
      (inj₂ (u≢J , _)) →
        no λ (_ , t~u) →
        let _ , _ , _ , _ , _ , _ , _ , _ , u≡J , _ = inv-J~ t~u in
        u≢J (_ , _ , _ , _ , _ , _ , _ , _ , u≡J)
  dec~↑ (K-cong B₁≡ t₁≡ B₂≡ t₂≡ t₃~ B₃≡Id ok) u~ =
    case inv-~-K u~ of λ where
      (inj₁
         (_ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ ,
          PE.refl , _ , C₁≡ , u₁≡ , C₂≡ , u₂≡ , u₃~ , _)) →
        dec~↑-K-cong ok (conv (~↓→∷ t₃~) B₃≡Id)
          (_ ≟ _ ×-dec decConv↑ B₁≡ C₁≡ ×-dec dec~↓ t₃~ u₃~)
          (λ eq → decConv↑TermConv eq t₁≡ u₁≡)
          (λ eq → decConv↑′ eq B₂≡ C₂≡)
          (λ eq → decConv↑TermConv eq t₂≡ u₂≡)
      (inj₂ (u≢K , _)) →
        no λ (_ , t~u) →
        let _ , _ , _ , _ , _ , _ , _ , u≡K , _ = inv-K~ t~u in
        u≢K (_ , _ , _ , _ , _ , _ , u≡K)
  dec~↑ ([]-cong-cong t₁≡ B₁≡ t₂≡ t₃≡ t₄~ B₂≡Id ok) u~ =
    case inv-~-[]-cong u~ of λ where
      (inj₁
         (_ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ ,
          PE.refl , PE.refl , _ , u₁≡ , C₁≡ , u₂≡ , u₃≡ , u₄~ , _)) →
        let ⊢t₄ = ~↓→∷ t₄~ in
        dec~↑-[]-cong-cong ok (conv ⊢t₄ B₂≡Id)
          (decStrength _ _ ×-dec decConv↑Level t₁≡ u₁≡ ×-dec
           decConv↑ B₁≡ C₁≡ ×-dec dec~↓ t₄~ u₄~)
          (λ eq → decConv↑TermConv eq t₂≡ u₂≡)
          (λ eq → decConv↑TermConv eq t₃≡ u₃≡)
      (inj₂ (u≢bc , _)) →
        no λ (_ , t~u) →
        let _ , _ , _ , _ , _ , _ , _ , u≡bc , _ = inv-[]-cong~ t~u in
        u≢bc (_ , _ , _ , _ , _ , _ , u≡bc)

  dec~↑′ : ∀ {k l R T}
        → ∇ »⊢ Δ ≡ Η
        → ∇ » Δ ⊢ k ~ k ↑ R → ∇ » Η ⊢ l ~ l ↑ T
        → Dec (∃ λ A → ∇ » Δ ⊢ k ~ l ↑ A)
  dec~↑′ Δ≡Η k~k l~l = dec~↑ k~k (stability~↑ (symConEq Δ≡Η) l~l)

  -- Decidability of algorithmic equality of neutral terms with types in WHNF.
  dec~↓ : ∀ {k l R T k′ l′}
        → Γ ⊢ k ~ k′ ↓ R → Γ ⊢ l ~ l′ ↓ T
        → Dec (∃ λ A → Γ ⊢ k ~ l ↓ A)
  dec~↓ ([~] _ _ k~l) ([~] _ _ k~l₁) with dec~↑ k~l k~l₁
  dec~↓ ([~] _ _ k~l) ([~] _ _ k~l₁) | yes (B , k~l₂) =
    let ⊢B , _ , _ = wf-⊢ (soundness~↑ k~l₂)
        C , whnfC , D′ = whNorm ⊢B
    in  yes (C , [~] B (D′ , whnfC) k~l₂)
  dec~↓ ([~] _ _ k~l) ([~] _ _ k~l₁) | no ¬p =
    no (λ { (_ , [~] A₃ _ k~l₂) → ¬p (A₃ , k~l₂) })

  dec~∷ : ∀ {k l R T k′ l′}
        → Γ ⊢ k ~ k′ ∷ R → Γ ⊢ l ~ l′ ∷ T
        → Dec (Γ ⊢ k ~ l ∷ R)
  dec~∷ x@(↑ A≡B k~↑l) y@(↑ A≡B₁ k~↑l₁) = Dec-map
    ( (λ (_ , z) → ~∷→∷→~∷ (↑ (refl (wf-⊢ (soundness~↑ z) .proj₁)) z) (~∷→∷ x))
    , λ (↑ _ z) → _ , z)
    (dec~↑ k~↑l k~↑l₁)

  -- Decidability of algorithmic equality of types.
  decConv↑ : ∀ {A B A′ B′}
           → Γ ⊢ A [conv↑] A′ → Γ ⊢ B [conv↑] B′
           → Dec (Γ ⊢ A [conv↑] B)
  decConv↑ ([↑] A′ B′ D D′ A′<>B′)
               ([↑] A″ B″ D₁ D″ A′<>B″)
           with decConv↓ A′<>B′ A′<>B″
  decConv↑ ([↑] A′ B′ D D′ A′<>B′)
               ([↑] A″ B″ D₁ D″ A′<>B″) | yes p =
    yes ([↑] A′ A″ D D₁ p)
  decConv↑ ([↑] A′ B′ D D′ A′<>B′)
               ([↑] A″ B″ D₁ D″ A′<>B″) | no ¬p =
    no (λ { ([↑] A‴ B‴ D₂ D‴ A′<>B‴) →
        let A‴≡B′ = whrDet* D₂ D
            B‴≡B″ = whrDet* D‴ D₁
        in
        ¬p (PE.subst₂ (λ x y → _ ⊢ x [conv↓] y) A‴≡B′ B‴≡B″ A′<>B‴) })

  decConv↑′ : ∀ {A B A′ B′}
            → ∇ »⊢ Δ ≡ Η
            → ∇ » Δ ⊢ A [conv↑] A′ → ∇ » Η ⊢ B [conv↑] B′
            → Dec (∇ » Δ ⊢ A [conv↑] B)
  decConv↑′ Δ≡Η A B = decConv↑ A (stabilityConv↑ (symConEq Δ≡Η) B)

  -- Decidability of algorithmic equality of types in WHNF.
  decConv↓ : ∀ {A B A′ B′}
           → Γ ⊢ A [conv↓] A′ → Γ ⊢ B [conv↓] B′
           → Dec (Γ ⊢ A [conv↓] B)
  decConv↓ (ne A~) B≡ =
    let _ , A-ne , _ = ne~↓ A~ in
    case inv-[conv↓]-ne′ B≡ of λ where
      (inj₁ (_ , B~)) →
        case dec~↓ A~ B~ of λ where
          (yes (_ , A~B)) →
            yes $ ne $
            let C-whnf , _ = ne~↓ A~B
                U≡A′       = neTypeEq (ne⁻ A-ne) (~↓→∷ A~) (~↓→∷ A~B)
            in
            PE.subst (_⊢_~_↓_ _ _ _) (U≡A U≡A′ C-whnf .proj₂) A~B
          (no ¬A~B) →
            no (¬A~B ∘→ (_ ,_) ∘→ proj₂ ∘→ inv-[conv↓]-ne (ne⁻ A-ne))
      (inj₂ (¬-B-ne , _)) →
        no λ A≡B →
        ¬-B-ne $ ne⁻ $
        ne~↓ (inv-[conv↓]-ne (ne⁻ A-ne) A≡B .proj₂) .proj₂ .proj₂
  decConv↓ Level≡Level@(Level-refl _ _) B≡ =
    case inv-[conv↓]-Level′ B≡ of λ where
      (inj₁ (PE.refl , _)) → yes Level≡Level
      (inj₂ (B≢Level , _)) → no (B≢Level ∘→ inv-[conv↓]-Level)
  decConv↓ (Lift-cong l₁≡l₂ A≡A′) B≡ =
    case inv-[conv↓]-Lift′ B≡ of λ where
      (inj₁ (_ , _ , _ , _ , PE.refl , PE.refl , l₂≡l₃ , A′≡A″)) →
        case decConv↑Level l₁≡l₂ l₂≡l₃ ×-dec
             decConv↑ A≡A′ A′≡A″ of λ where
          (yes (l₁≡l₃ , A≡A″)) → yes (Lift-cong l₁≡l₃ A≡A″)
          (no not-both-equal) → no λ Lift≡Lift →
            case inv-[conv↓]-Lift Lift≡Lift of λ {
              (_ , _ , PE.refl , l₁≡l₃ , A≡A″) →
            not-both-equal (l₁≡l₃ , A≡A″) }
      (inj₂ (B≢Lift , _)) → no λ Lift≡B →
        let _ , _ , B≡Lift , _ = inv-[conv↓]-Lift Lift≡B
        in B≢Lift (_ , _ , B≡Lift)
  decConv↓ (U-cong l₁≡l₂) B≡ =
    case inv-[conv↓]-U′ B≡ of λ where
      (inj₁ (l₃ , l₄ , PE.refl , PE.refl , l₃≡l₄)) →
        case decConv↑Level l₁≡l₂ l₃≡l₄ of λ where
          (yes l₁≡l₃) → yes (U-cong l₁≡l₃)
          (no l₁≢l₃) → no λ U≡U →
            case inv-[conv↓]-U U≡U of λ where
              (_ , PE.refl , z) → l₁≢l₃ z
      (inj₂ (B≢U , _)) → no λ U≡B →
        let _ , eq , _ = inv-[conv↓]-U U≡B
        in B≢U (_ , eq)
  decConv↓ (ΠΣ-cong A₁≡ A₂≡ ok) B≡ =
    case inv-[conv↓]-ΠΣ′ B≡ of λ where
      (inj₁
         (_ , _ , _ , _ , _ , _ , _ , PE.refl , PE.refl , B₁≡ , B₂≡)) →
        decConv↓-ΠΣ ok
          (decBinderMode _ _ ×-dec _ ≟ _ ×-dec _ ≟ _ ×-dec
           decConv↑ A₁≡ B₁≡)
          (λ eq → decConv↑′ eq A₂≡ B₂≡)
      (inj₂ (B≢ΠΣ , _)) →
        no λ ΠΣ≡B →
        let _ , _ , B≡ΠΣ , _ = inv-[conv↓]-ΠΣ ΠΣ≡B in
        B≢ΠΣ (_ , _ , _ , _ , _ , B≡ΠΣ)
  decConv↓ Empty≡Empty@(Empty-refl _) B≡ =
    case inv-[conv↓]-Empty′ B≡ of λ where
      (inj₁ (PE.refl , _)) → yes Empty≡Empty
      (inj₂ (B≢Empty , _)) → no (B≢Empty ∘→ inv-[conv↓]-Empty)
  decConv↓ (Unit-refl {s = s} x ok) B≡ =
    case inv-[conv↓]-Unit′ B≡ of λ where
      (inj₁ (s′ , PE.refl , PE.refl)) →
        case decStrength s s′ of λ where
          (yes PE.refl) → yes (Unit-refl x ok)
          (no not-both-equal) → no λ Unit≡Unit →
            case inv-[conv↓]-Unit Unit≡Unit of λ {
              PE.refl →
            not-both-equal PE.refl }
      (inj₂ (B≢Unit , _)) →
        no λ Unit≡B →
          let B≡ = inv-[conv↓]-Unit Unit≡B
          in B≢Unit (_ , B≡)
  decConv↓ ℕ≡ℕ@(ℕ-refl _) B≡ =
    case inv-[conv↓]-ℕ′ B≡ of λ where
      (inj₁ (PE.refl , _)) → yes ℕ≡ℕ
      (inj₂ (B≢ℕ , _))     → no (B≢ℕ ∘→ inv-[conv↓]-ℕ)
  decConv↓ (Id-cong A′≡ t₁≡ t₂≡) B≡ =
    case inv-[conv↓]-Id′ B≡ of λ where
      (inj₁
         (_ , _ , _ , _ , _ , _ ,
          PE.refl , PE.refl , B′≡ , u₁≡ , u₂≡)) →
        decConv↓-Id (decConv↑ A′≡ B′≡)
          (λ A′≡B′ → decConv↑Term t₁≡ (convConv↑Term A′≡B′ u₁≡))
          (λ A′≡B′ → decConv↑Term t₂≡ (convConv↑Term A′≡B′ u₂≡))
      (inj₂ (B≢Id , _)) →
        no λ Id≡B →
        let _ , _ , _ , B≡Id , _ = inv-[conv↓]-Id Id≡B in
        B≢Id (_ , _ , _ , B≡Id)

  -- Decidability of algorithmic equality of terms.
  decConv↑Term : ∀ {t u A t′ u′}
               → Γ ⊢ t [conv↑] t′ ∷ A → Γ ⊢ u [conv↑] u′ ∷ A
               → Dec (Γ ⊢ t [conv↑] u ∷ A)
  decConv↑Term ([↑]ₜ B t′ u′ D d d′ t<>u)
               ([↑]ₜ B₁ t″ u″ D₁ d₁ d″ t<>u₁)
               rewrite whrDet* D D₁
                 with decConv↓Term t<>u t<>u₁
  decConv↑Term ([↑]ₜ B t′ u′ D d d′ t<>u)
               ([↑]ₜ B₁ t″ u″ D₁ d₁ d″ t<>u₁)
               | yes p = yes ([↑]ₜ B₁ t′ t″ D₁ d d₁ p)
  decConv↑Term ([↑]ₜ B t′ u′ D d d′ t<>u)
               ([↑]ₜ B₁ t″ u″ D₁ d₁ d″ t<>u₁)
               | no ¬p =
    no (λ { ([↑]ₜ B₂ t‴ u‴ D₂ d₂ d‴ t<>u₂) →
        let B₂≡B₁ = whrDet* D₂ D₁
            t‴≡u′ = whrDet*Term d₂
                      (PE.subst (_⊢_↘_∷_ _ _ _) (PE.sym B₂≡B₁) d)
            u‴≡u″ = whrDet*Term d‴
                      (PE.subst (_⊢_↘_∷_ _ _ _) (PE.sym B₂≡B₁) d₁)
        in  ¬p (PE.subst₃ (λ x y z → _ ⊢ x [conv↓] y ∷ z)
                          t‴≡u′ u‴≡u″ B₂≡B₁ t<>u₂)})

  decConv↑Term′ : ∀ {t u A}
                → ∇ »⊢ Δ ≡ Η
                → ∇ » Δ ⊢ t [conv↑] t ∷ A → ∇ » Η ⊢ u [conv↑] u ∷ A
                → Dec (∇ » Δ ⊢ t [conv↑] u ∷ A)
  decConv↑Term′ Δ≡Η t u =
    decConv↑Term t (stabilityConv↑Term (symConEq Δ≡Η) u)

  -- Decidability for _⊢_[conv↑]_∷Level.
  decConv↑Level :
    Γ ⊢ l₁ [conv↑] l₁′ ∷Level → Γ ⊢ l₂ [conv↑] l₂′ ∷Level →
    Dec (Γ ⊢ l₁ [conv↑] l₂ ∷Level)
  decConv↑Level (term okᴸ l₁≡) (term _ l₂≡) =
    case decConv↑Term l₁≡ l₂≡ of λ where
      (yes l₁≡l₂) → yes (term okᴸ l₁≡l₂)
      (no l₁≢l₂)  → no λ where
        (term _ l₁≡l₂)   → l₁≢l₂ l₁≡l₂
        (literal ok _ _) → Level-allowed→Allowed-literal→ okᴸ ok
  decConv↑Level (term okᴸ _) (literal ok _ _)
    with Allowed-literal→Infinite okᴸ ok
  … | ωᵘ+ = no (λ { (literal _ _ ()) })
  decConv↑Level (literal ok _ _) (term okᴸ _)
    with Allowed-literal→Infinite okᴸ ok
  … | ωᵘ+ = no (λ { (literal _ _ ()) })
  decConv↑Level (literal! ok₁ ⊢Γ) (literal! ok₂ _) =
    let l₁-lit = Allowed-literal→Level-literal ok₁
        l₂-lit = Allowed-literal→Level-literal ok₂
    in
    case l₁-lit ≟L l₂-lit of λ where
      (yes PE.refl) →
        yes (literal! ok₁ ⊢Γ)
      (no l₁≢l₂) → no λ where
        (literal! _ _) → l₁≢l₂ PE.refl
        (term okᴸ _)   → Level-allowed→Allowed-literal→ okᴸ ok₁

  -- Decidability of algorithmic equality of terms in WHNF.
  decConv↓Term : ∀ {t u A t′ u′}
               → Γ ⊢ t [conv↓] t′ ∷ A → Γ ⊢ u [conv↓] u′ ∷ A
               → Dec (Γ ⊢ t [conv↓] u ∷ A)
  decConv↓Term (ne-ins ⊢t _ A-ne t~) u≡ =
    let _ , u~ = inv-[conv↓]∷-ne A-ne u≡ in
    case dec~↓ t~ u~ of λ where
      (yes (_ , t~u)) → yes (ne-ins ⊢t ([conv↓]∷→∷ u≡) A-ne t~u)
      (no ¬t~u)       → no (¬t~u ∘→ inv-[conv↓]∷-ne A-ne)
  decConv↓Term (Level-ins x) u≡ =
    let u≡ = inv-[conv↓]∷-Level u≡
    in Dec-map (Level-ins , inv-[conv↓]∷-Level) (decConv↓Level x u≡)
  decConv↓Term (univ ⊢A _ A≡) B≡ =
    case decConv↓ A≡ (inv-[conv↓]∷-U B≡) of λ where
      (yes A≡B) → yes (univ ⊢A ([conv↓]∷→∷ B≡) A≡B)
      (no A≢B)  → no (A≢B ∘→ inv-[conv↓]∷-U)
  decConv↓Term (Lift-η ⊢t _ wt _ lt≡lt′) u≡ =
    let ⊢u , _ , wu , _ , lu≡lu′ = inv-[conv↓]∷-Lift u≡
    in case decConv↑Term lt≡lt′ lu≡lu′ of λ where
      (yes lt≡lu) → yes (Lift-η ⊢t ⊢u wt wu lt≡lu)
      (no lt≢lu) → no λ t≡u →
        let _ , _ , _ , _ , lt≡lu = inv-[conv↓]∷-Lift t≡u
        in lt≢lu lt≡lu
  decConv↓Term (η-eq ⊢t _ t-fun _ t0≡) u≡ =
    let u-fun , _ , u0≡ = inv-[conv↓]∷-Π u≡ in
    case decConv↑Term t0≡ u0≡ of λ where
      (yes t0≡u0) → yes (η-eq ⊢t ([conv↓]∷→∷ u≡) t-fun u-fun t0≡u0)
      (no t0≢u0)  →
        no λ t≡u →
        let _ , _ , t0≡u0 = inv-[conv↓]∷-Π t≡u in
        t0≢u0 t0≡u0
  decConv↓Term (Σ-η ⊢t _ t-prod _ fst-t≡ snd-t≡) u≡ =
    let u-prod , _ , fst-u≡ , snd-u≡ = inv-[conv↓]∷-Σˢ u≡ in
    case
      (decConv↑Term fst-t≡ fst-u≡
         ×-dec′ λ fst-t≡fst-u →
       decConv↑TermConv
         (subst-⊢≡₀ (inversion-ΠΣ (wf-⊢ ⊢t) .proj₂ .proj₁)
            (soundnessConv↑Term fst-t≡fst-u))
         snd-t≡ snd-u≡)
      of λ where
      (yes (fst-t≡fst-u , snd-t≡snd-u)) →
        yes $
        Σ-η ⊢t ([conv↓]∷→∷ u≡) t-prod u-prod fst-t≡fst-u snd-t≡snd-u
      (no not-both-equal) →
        no λ t≡u →
        let _ , _ , fst-t≡fst-u , snd-t≡snd-u = inv-[conv↓]∷-Σˢ t≡u in
        not-both-equal (fst-t≡fst-u , snd-t≡snd-u)
  decConv↓Term (Σʷ-ins ⊢t _ t~) u≡ = case inv-[conv↓]∷-Σʷ u≡ of λ where
    (inj₁ (_ , _ , _ , _ , u~)) →
      case dec~↓ t~ u~ of λ where
        (yes (_ , t~u)) →
          yes $
          Σʷ-ins ⊢t ([conv↓]∷→∷ u≡) $
          PE.subst (_⊢_~_↓_ _ _ _)
            (uncurry Σ≡A (~↓→∷→Whnf×≡ t~u ⊢t) .proj₂ .proj₂) t~u
        (no ¬t~u) → no (¬t~u ∘→ [conv↓]∷Σʷ→~↓ t~)
    (inj₂ (_ , _ , _ , _ , PE.refl , _)) →
      no λ t≡prod →
      let _ , [~] _ _ ~prod = [conv↓]∷Σʷ→~↓ t~ t≡prod in
      inv-~prod ~prod
  decConv↓Term (prod-cong ⊢B t₁≡ t₂≡ ok) u≡ =
    case inv-[conv↓]∷-Σʷ u≡ of λ where
      (inj₁ (_ , _ , _ , _ , u~)) →
        no λ prod≡u →
        let _ , [~] _ _ ~prod =
              [conv↓]∷Σʷ→~↓ u~ (symConv↓Term′ prod≡u)
        in
        inv-~prod ~prod
      (inj₂ (_ , _ , _ , _ , PE.refl , _ , u₁≡ , u₂≡)) →
        case
          (decConv↑Term t₁≡ u₁≡
             ×-dec′ λ t₁≡u₁ →
           decConv↑TermConv
             (subst-⊢≡₀ ⊢B (soundnessConv↑Term t₁≡u₁))
             t₂≡ u₂≡)
          of λ where
          (yes (t₁≡u₁ , t₂≡u₂)) → yes (prod-cong ⊢B t₁≡u₁ t₂≡u₂ ok)
          (no not-both-equal)   →
            no λ t≡u →
            let _ , _ , _ , t₁≡u₁ , t₂≡u₂ , _ = prod-cong⁻¹ t≡u in
            not-both-equal (t₁≡u₁ , t₂≡u₂)
  decConv↓Term (Empty-ins t~) u≡ =
    case dec~↓ t~ (inv-[conv↓]∷-Empty u≡) of λ where
      (yes (_ , t~u)) →
        yes $ Empty-ins $
        PE.subst (_⊢_~_↓_ _ _ _)
          (uncurry Empty≡A (~↓→∷→Whnf×≡ t~u (~↓→∷ t~))) t~u
      (no ¬t~u) → no (¬t~u ∘→ (_ ,_) ∘→ inv-[conv↓]∷-Empty)
  decConv↓Term (Unitʷ-ins no-η t~) u≡ =
    case inv-[conv↓]∷-Unitʷ u≡ of λ where
      (inj₁ (_ , inj₁ u~)) → case dec~↓ t~ u~ of λ where
        (yes (_ , t~u)) →
          yes $ Unitʷ-ins no-η $
          PE.subst (_⊢_~_↓_ _ _ _)
            (uncurry Unit≡A (~↓→∷→Whnf×≡ t~u (~↓→∷ t~))) t~u
        (no ¬t~u) →
          no λ t≡u →
          case inv-[conv↓]∷-Unitʷ t≡u of λ where
            (inj₁ (_ , inj₁ t~u))           → ¬t~u (_ , t~u)
            (inj₁ (_ , inj₂ (PE.refl , _))) →
              let [~] _ _ t~ = t~ in
              inv-star~ t~
            (inj₂ (η , _)) → no-η η
      (inj₁ (_ , inj₂ (PE.refl , _))) →
        no (no-η ∘→ ≡starʷ→~↓Unitʷ→Unitʷ-η t~)
      (inj₂ (η , _)) → ⊥-elim (no-η η)
  decConv↓Term (η-unit ⊢t _ t-whnf _ η) u≡ =
    case inv-[conv↓]∷-Unit u≡ of λ where
      (inj₁ (η , u-whnf , _)) →
        yes (η-unit ⊢t ([conv↓]∷→∷ u≡) t-whnf u-whnf η)
      (inj₂ (no-η , _)) → ⊥-elim (no-η η)
  decConv↓Term (starʷ-refl y ok no-η) u≡ =
    case inv-[conv↓]∷-Unitʷ u≡ of λ where
      (inj₁ (_ , inj₂ (PE.refl , PE.refl))) →
        yes (starʷ-refl y ok no-η)
      (inj₁ (_ , inj₁ u~))            →
        no λ ⋆≡ → no-η (≡starʷ→~↓Unitʷ→Unitʷ-η u~ (symConv↓Term′ ⋆≡))
      (inj₂ (η , _)) → ⊥-elim (no-η η)
  decConv↓Term (ℕ-ins t~) u≡ = case inv-[conv↓]∷-ℕ u≡ of λ where
    (inj₁ u~) → case dec~↓ t~ u~ of λ where
      (yes (A , t~u)) →
        yes $ ℕ-ins $
        PE.subst (_⊢_~_↓_ _ _ _)
          (uncurry ℕ≡A (~↓→∷→Whnf×≡ t~u (~↓→∷ t~))) t~u
      (no ¬t~u) → no (¬t~u ∘→ (_ ,_) ∘→ [conv↓]∷ℕ→~↓ℕ t~)
    (inj₂ (inj₁ (PE.refl , _))) →
      no λ t≡zero →
      let [~] _ _ ~zero = [conv↓]∷ℕ→~↓ℕ t~ t≡zero in
      inv-~zero ~zero
    (inj₂ (inj₂ (_ , _ , PE.refl , _))) →
      no λ t≡suc →
      let [~] _ _ ~suc = [conv↓]∷ℕ→~↓ℕ t~ t≡suc in
      inv-~suc ~suc
  decConv↓Term zero≡zero@(zero-refl _) u≡ =
    case inv-[conv↓]∷-ℕ u≡ of λ where
      (inj₁ u~) →
        no λ zero≡t →
        let [~] _ _ ~zero = [conv↓]∷ℕ→~↓ℕ u~ (symConv↓Term′ zero≡t) in
        inv-~zero ~zero
      (inj₂ (inj₁ (PE.refl , _)))         → yes zero≡zero
      (inj₂ (inj₂ (_ , _ , PE.refl , _))) →
        no λ zero≡suc →
        case inv-[conv↓]∷-ℕ zero≡suc of λ where
          (inj₁ ([~] _ _ zero~suc))      → inv-zero~ zero~suc
          (inj₂ (inj₁ (_ , ())))
          (inj₂ (inj₂ (_ , _ , () , _)))
  decConv↓Term (suc-cong t≡) u≡ = case inv-[conv↓]∷-ℕ u≡ of λ where
    (inj₁ u~) →
      no λ suc≡t →
      let [~] _ _ ~suc = [conv↓]∷ℕ→~↓ℕ u~ (symConv↓Term′ suc≡t) in
      inv-~suc ~suc
    (inj₂ (inj₁ (PE.refl , _))) →
      no λ suc≡zero →
      case inv-[conv↓]∷-ℕ suc≡zero of λ where
        (inj₁ ([~] _ _ suc~zero))          → inv-~zero suc~zero
        (inj₂ (inj₁ (() , _)))
        (inj₂ (inj₂ (_ , _ , _ , () , _)))
    (inj₂ (inj₂ (_ , _ , PE.refl , _ , u≡))) →
      case decConv↑Term t≡ u≡ of λ where
        (yes t≡u) → yes (suc-cong t≡u)
        (no t≢u)  →
          no λ suc-t≡suc-u →
          case inv-[conv↓]∷-ℕ suc-t≡suc-u of λ where
            (inj₁ ([~] _ _ suc~suc)) →
              inv-suc~ suc~suc
            (inj₂ (inj₁ (() , _)))
            (inj₂ (inj₂ (_ , _ , PE.refl , PE.refl , t≡u))) →
              t≢u t≡u
  decConv↓Term (Id-ins ⊢t t~) u≡ = case inv-[conv↓]∷-Id u≡ of λ where
    (inj₁ (_ , _ , _ , u~)) →
      case dec~↓ t~ u~ of λ where
        (yes (_ , t~u)) →
          yes $
          Id-ins ⊢t $
          PE.subst (_⊢_~_↓_ _ _ _)
            (uncurry Id≡Whnf (~↓→∷→Whnf×≡ t~u (~↓→∷ t~))
               .proj₂ .proj₂ .proj₂)
            t~u
        (no ¬t~u) →
          no λ t≡u →
          case inv-[conv↓]∷-Id t≡u of λ where
            (inj₁ (_ , _ , _ , t~u)) → ¬t~u (_ , t~u)
            (inj₂ (_ , PE.refl , _)) →
              let [~] _ _ rfl~ = u~ in
              inv-rfl~ rfl~
    (inj₂ (PE.refl , _)) →
      no λ rfl≡u →
      ¬-Neutral-rfl $ ne⁻ $
      case inv-[conv↓]∷-Id rfl≡u of λ where
        (inj₁ (_ , _ , _ , t~rfl)) → ne~↓ t~rfl .proj₂ .proj₂
        (inj₂ (PE.refl , _))       → ne~↓ t~ .proj₂ .proj₁
  decConv↓Term rfl≡rfl@(rfl-refl _) u≡ =
    case inv-[conv↓]∷-Id u≡ of λ where
      (inj₁ (_ , _ , _ , u~)) →
        no λ rfl≡u →
        ¬-Neutral-rfl $ ne⁻ $
        case inv-[conv↓]∷-Id rfl≡u of λ where
          (inj₁ (_ , _ , _ , rfl~u)) → ne~↓ rfl~u .proj₂ .proj₁
          (inj₂ (_ , PE.refl , _))   → ne~↓ u~ .proj₂ .proj₁
      (inj₂ (PE.refl , _)) → yes rfl≡rfl

  -- Decidability of algorithmic equality of terms of equal types.
  decConv↑TermConv : ∀ {t u A B t′ u′}
                → Γ ⊢ A ≡ B
                → Γ ⊢ t [conv↑] t′ ∷ A
                → Γ ⊢ u [conv↑] u′ ∷ B
                → Dec (Γ ⊢ t [conv↑] u ∷ A)
  decConv↑TermConv A≡B t u =
    decConv↑Term t (convConv↑Term (sym A≡B) u)

  -- Decidability of algorithmic equality of levels.

  decConv↓Level
    : ∀ {t u t′ u′}
    → Γ ⊢ t [conv↓] t′ ∷Level → Γ ⊢ u [conv↓] u′ ∷Level
    → Dec (Γ ⊢ t [conv↓] u ∷Level)
  decConv↓Level ([↓]ˡ tᵛ _ t≡ _ t≡t′) ([↓]ˡ uᵛ _ u≡ _ u≡u′) =
    case tᵛ ≡ᵛ? uᵛ of λ where
      (yes t≡u) → yes ([↓]ˡ tᵛ uᵛ t≡ u≡ t≡u)
      (no t≢u) → no
        λ ([↓]ˡ tᵛ′ uᵛ′ t≡′ u≡′ t≡u) → t≢u
          (trans-≡≡ᵛ-≡ᵛ (deterministic-↓ᵛ t≡ t≡′)
            (trans-≡ᵛ-≡≡ᵛ t≡u (deterministic-↓ᵛ u≡′ u≡)))

  _≡ⁿ?_ : {t u : Term n} → Γ ⊢ t ~ t ↓ Level → Γ ⊢ u ~ u ↓ Level → Dec (≡ⁿ Γ t u false)
  _≡ⁿ?_ t u =
    let _ , ⊢t , _ = wf-⊢ (soundness~↓ t)
    in Dec-map ((λ (_ , x~y) → ne≡ (PE.subst (_ ⊢ _ ~ _ ↓_) (uncurry Level≡A (~↓→∷→Whnf×≡ x~y ⊢t)) x~y)) , λ { (ne≡ x) → _ , x }) (dec~↓ t u)

  _≡ⁿ¿_ : {t u : Term n} → Γ ⊢ t ~ t ↓ Level → Γ ⊢ u ~ u ↓ Level → Dec (≡ⁿ Γ t u true)
  _≡ⁿ¿_ t u =
    let _ , ⊢u , _ = wf-⊢ (soundness~↓ u)
    in Dec-map ((λ (_ , x~y) → ne≡' (PE.subst (_ ⊢ _ ~ _ ↓_) (uncurry Level≡A (~↓→∷→Whnf×≡ x~y ⊢u)) x~y)) , λ { (ne≡' x) → _ , x }) (dec~↓ u t)

  _≤ᵃ?_ : (t u : LevelAtom Γ) → Dec (≤ᵃ false t u)
  zeroᵘ ≤ᵃ? u = yes zeroᵘ≤
  ne x ≤ᵃ? zeroᵘ = no λ ()
  ne x ≤ᵃ? ne y = Dec-map (ne≤ , λ { (ne≤ x) → x }) (x ≡ⁿ? y)

  _≤ᵃ¿_ : (t u : LevelAtom Γ) → Dec (≤ᵃ true t u)
  zeroᵘ ≤ᵃ¿ u = yes zeroᵘ≤
  ne x ≤ᵃ¿ zeroᵘ = no λ ()
  ne x ≤ᵃ¿ ne y = Dec-map (ne≤ , λ { (ne≤ x) → x }) (x ≡ⁿ¿ y)

  _≤⁺?_ : (t u : Level⁺ Γ) → Dec (≤⁺ false t u)
  (n , t) ≤⁺? (m , u) = n ≤? m ×-dec t ≤ᵃ? u

  _≤⁺¿_ : (t u : Level⁺ Γ) → Dec (≤⁺ true t u)
  (n , t) ≤⁺¿ (m , u) = n ≤? m ×-dec t ≤ᵃ¿ u

  _≤⁺ᵛ?_ : (t : Level⁺ Γ) (u : Levelᵛ Γ) → Dec (≤⁺ᵛ false t u)
  t ≤⁺ᵛ? L.[] = no λ ()
  t ≤⁺ᵛ? (x L.∷ u) = Dec-map (Any.fromSum , Any.toSum) (t ≤⁺? x ⊎-dec t ≤⁺ᵛ? u)

  _≤⁺ᵛ¿_ : (t : Level⁺ Γ) (u : Levelᵛ Γ) → Dec (≤⁺ᵛ true t u)
  t ≤⁺ᵛ¿ L.[] = no λ ()
  t ≤⁺ᵛ¿ (x L.∷ u) = Dec-map (Any.fromSum , Any.toSum) (t ≤⁺¿ x ⊎-dec t ≤⁺ᵛ¿ u)

  _≤ᵛ?_ : (t u : Levelᵛ Γ) → Dec (≤ᵛ false t u)
  L.[] ≤ᵛ? u = yes All.[]
  (x L.∷ t) ≤ᵛ? u = Dec-map (uncurry All._∷_ , All.uncons) (x ≤⁺ᵛ? u ×-dec t ≤ᵛ? u)

  _≤ᵛ¿_ : (t u : Levelᵛ Γ) → Dec (≤ᵛ true t u)
  L.[] ≤ᵛ¿ u = yes All.[]
  (x L.∷ t) ≤ᵛ¿ u = Dec-map (uncurry All._∷_ , All.uncons) (x ≤⁺ᵛ¿ u ×-dec t ≤ᵛ¿ u)

  _≡ᵛ?_ : (t u : Levelᵛ Γ) → Dec (t ≡ᵛ u)
  t ≡ᵛ? u = t ≤ᵛ? u ×-dec u ≤ᵛ¿ t
