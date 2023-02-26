open import Tools.Bool
open import Tools.PropositionalEquality as PE
  using (_≈_; ≈-refl; ≈-sym; ≈-trans)
open import Tools.Sum using (_⊎_; inj₂)

open import Definition.Modality

module Definition.Modality.FullReduction
  {a} {M : Set a} (𝕄 : Modality M)
  (open Modality 𝕄)
  (p≤𝟘 : (p : M) → p ≤ 𝟘)
  -- The following assumption is only used for quantities p that
  -- correspond to the first quantity of a Σ-type with η-equality, and
  -- only in cases where the mode is 𝟙ᵐ. It might suffice to restrict
  -- such Σ-types so that when the first quantity is p and the mode is
  -- 𝟙ᵐ, then q ≤ p · q holds for all quantities q.
  (·-increasing : {p q : M} → q ≤ p · q)
  -- The following assumption is only used when the first quantity of
  -- a Σ-type with η-equality is 𝟘 and the mode is 𝟙ᵐ. It might
  -- suffice to restrict such Σ-types so that when the first quantity
  -- is 𝟘 and the mode is 𝟙ᵐ, then (𝟙 ≈ 𝟘) ⊎ T 𝟘ᵐ-allowed holds.
  (𝟙≈𝟘⊎𝟘ᵐ : (𝟙 ≈ 𝟘) ⊎ T 𝟘ᵐ-allowed)
  where

open import Tools.Empty
open import Tools.Fin
open import Tools.Nat using (Nat)
open import Tools.Product
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation

open import Definition.Untyped M hiding (_∷_; wk)
import Definition.Untyped M as U
open import Definition.Untyped.Properties M
open import Definition.Typed M
open import Definition.Typed.Properties M
open import Definition.Typed.Usage 𝕄
open import Definition.Typed.Weakening M
open import Definition.Typed.Consequences.InverseUniv M
open import Definition.Typed.Consequences.NeTypeEq M
open import Definition.Typed.Consequences.Substitution M
open import Definition.Typed.Consequences.Syntactic M

open import Definition.Conversion M
open import Definition.Conversion.Consequences.Completeness M
open import Definition.Conversion.FullReduction M
  hiding (fullRedNe; fullRedNe~↓; fullRed; fullRedConv↓; fullRedTerm; fullRedTermConv↓)
import Definition.Conversion.FullReduction M as FR
open import Definition.Conversion.Whnf M

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Context.Properties 𝕄
open import Definition.Modality.Usage 𝕄
open import Definition.Modality.Usage.Inversion 𝕄
open import Definition.Modality.Usage.Properties 𝕄
open import Definition.Modality.Usage.Weakening 𝕄
open import Definition.Mode 𝕄

private
  variable
    n : Nat
    Γ : Con Term n
    t t′ A A′ : Term n
    p : M
    γ : Conₘ n
    m : Mode

mutual
  fullRedNe :
    Γ ⊢ t ~ t′ ↑ A → γ ▸[ m ] t →
    ∃ λ u → NfNeutral u × Γ ⊢ t ≡ u ∷ A × γ ▸[ m ] u
  fullRedNe (var-refl x _) γ▸t = var _ , var _ , refl x , γ▸t
  fullRedNe {m = m} (app-cong t u p≈p₁ p≈p₂) γ▸t =
    let invUsageApp δ▸t η▸u γ≤γ′ = inv-usage-app γ▸t
        t′ , nfT′ , t≡t′ , δ▸t′ = fullRedNe~↓ t δ▸t
        u′ , nfU′ , u≡u′ , η▸u′ = fullRedTermConv↑ u η▸u
        p₁≈p₂ = ≈-trans (≈-sym p≈p₁) p≈p₂
    in  t′ ∘ u′ , ∘ₙ nfT′ nfU′ , app-cong t≡t′ u≡u′ p≈p₁ p≈p₂
      , sub (δ▸t′ ∘ₘ ▸-cong (ᵐ·-cong m p₁≈p₂) η▸u′)
          (≤ᶜ-trans γ≤γ′ (≤ᶜ-reflexive (+ᶜ-congˡ (·ᶜ-congʳ p₁≈p₂))))
  fullRedNe {m = m} (fst-cong {p = p} p~p) γ▸ =
    let invUsageFst m′ m≡m′ᵐ·p δ▸ γ≤δ 𝟘-cond = inv-usage-fst γ▸
        p′ , neP′ , p≡p′ , δ▸′               = fullRedNe~↓ p~p δ▸
        ⊢ΣFG , _ , _                         = syntacticEqTerm p≡p′
        ⊢F , ⊢G                              = syntacticΣ ⊢ΣFG
    in  fst _ p′
      , fstₙ neP′
      , fst-cong ⊢F ⊢G p≡p′
      , sub (fstₘ m′ (▸-cong m≡m′ᵐ·p δ▸′) (PE.sym m≡m′ᵐ·p) 𝟘-cond) γ≤δ
  fullRedNe (snd-cong p~p) γ▸ =
    let invUsageSnd δ▸ γ≤δ     = inv-usage-snd γ▸
        p′ , neP′ , p≡p′ , δ▸′ = fullRedNe~↓ p~p δ▸
        ⊢ΣFG , _ , _           = syntacticEqTerm p≡p′
        ⊢F , ⊢G                = syntacticΣ ⊢ΣFG
    in  snd _ p′
      , sndₙ neP′
      , snd-cong ⊢F ⊢G p≡p′
      , sub (sndₘ δ▸′) γ≤δ
  fullRedNe (natrec-cong {p = p} {r = r} C z s n p≈p′ r≈r′) γ▸t =
    let invUsageNatrec δ▸z η▸s θ▸n γ≤γ′ = inv-usage-natrec γ▸t
        C′ , nfC′ , C≡C′ = FR.fullRed C
        z′ , nfZ′ , z≡z′ , δ▸z′ = fullRedTermConv↑ z δ▸z
        s′ , nfS′ , s≡s′ , η▸s′ = fullRedTermConv↑ s η▸s
        n′ , nfN′ , n≡n′ , θ▸n′ = fullRedNe~↓ n θ▸n
    in  natrec p r C′ z′ s′ n′ , natrecₙ nfC′ nfZ′ nfS′ nfN′
      , natrec-cong (proj₁ (syntacticEq C≡C′)) C≡C′ z≡z′ s≡s′ n≡n′ ≈-refl ≈-refl
      , sub (natrecₘ δ▸z′ η▸s′ θ▸n′) γ≤γ′
  fullRedNe (prodrec-cong! C g u) γ▸t =
    let invUsageProdrec δ▸g η▸u P γ≤γ′ = inv-usage-prodrec γ▸t
        C′ , nfC′ , C≡C′ = FR.fullRed C
        g′ , nfg′ , g≡g′ , δ▸g′ = fullRedNe~↓ g δ▸g
        u′ , nfu′ , u≡u′ , η▸u′ = fullRedTermConv↑ u η▸u
        ⊢Σ , _ = syntacticEqTerm g≡g′
        ⊢F , ⊢G = syntacticΣ ⊢Σ
    in  prodrec _ _ C′ g′ u′ , prodrecₙ nfC′ nfg′ nfu′
      , prodrec-cong ⊢F ⊢G C≡C′ g≡g′ u≡u′ PE.refl
      , sub (prodrecₘ δ▸g′ η▸u′ P) γ≤γ′
  fullRedNe {m = m} (Emptyrec-cong C n p≈p′) γ▸t =
    let invUsageEmptyrec δ▸n γ≤δ = inv-usage-Emptyrec γ▸t
        C′ , nfC′ , C≡C′ = FR.fullRed C
        n′ , nfN′ , n≡n′ , δ▸n′ = fullRedNe~↓ n δ▸n
    in  Emptyrec _ C′ n′ , Emptyrecₙ nfC′ nfN′
      , Emptyrec-cong C≡C′ n≡n′ p≈p′
      , sub (Emptyrecₘ (▸-cong (ᵐ·-cong m p≈p′) δ▸n′))
          (≤ᶜ-trans γ≤δ (≤ᶜ-reflexive (·ᶜ-congʳ p≈p′)))

  fullRedNe~↓ :
    Γ ⊢ t ~ t′ ↓ A → γ ▸[ m ] t →
    ∃ λ u → NfNeutral u × Γ ⊢ t ≡ u ∷ A × γ ▸[ m ] u
  fullRedNe~↓ ([~] A D whnfB k~l) γ▸t =
    let u , nf , t≡u , γ▸u = fullRedNe k~l γ▸t
    in  u , nf , conv t≡u (subset* D) , γ▸u

  fullRedConv↑ :
    Γ ⊢ A [conv↑] A′ → γ ▸[ m ] A →
    ∃ λ B → Nf B × Γ ⊢ A ≡ B × γ ▸[ m ] B
  fullRedConv↑ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′) γ▸A =
    let γ▸A′ = usagePres* γ▸A D
        B″ , nf , B′≡B″ , γ▸B″ = fullRedConv↓ A′<>B′ γ▸A′
    in  B″ , nf , trans (subset* D) B′≡B″ , γ▸B″

  fullRedConv↓ :
    Γ ⊢ A [conv↓] A′ → γ ▸[ m ] A →
    ∃ λ B → Nf B × Γ ⊢ A ≡ B × γ ▸[ m ] B
  fullRedConv↓ (U-refl ⊢Γ) γ▸A = U , Uₙ , refl (Uⱼ ⊢Γ) , γ▸A
  fullRedConv↓ (ℕ-refl ⊢Γ) γ▸A = ℕ , ℕₙ , refl (ℕⱼ ⊢Γ) , γ▸A
  fullRedConv↓ (Empty-refl ⊢Γ) γ▸A = Empty , Emptyₙ , refl (Emptyⱼ ⊢Γ) , γ▸A
  fullRedConv↓ (Unit-refl ⊢Γ) γ▸A = Unit , Unitₙ , refl (Unitⱼ ⊢Γ) , γ▸A
  fullRedConv↓ (ne A) γ▸A =
    let B , nf , A≡B , γ▸B = fullRedNe~↓ A γ▸A
    in  B , ne nf , univ A≡B , γ▸B
  fullRedConv↓ {m = m} (Π-cong ⊢F F G p≈p′ q≈q′) γ▸A =
    let invUsageΠΣ δ▸F η▸G γ≤γ′ = inv-usage-Π γ▸A
        F′ , nfF′ , F≡F′ , δ▸F′ = fullRedConv↑ F δ▸F
        G′ , nfG′ , G≡G′ , η▸G′ = fullRedConv↑ G η▸G
        η′▸G′ = sub η▸G′ (≤ᶜ-reflexive (≈ᶜ-refl ∙ ≈-sym (·-congˡ q≈q′)))
    in  Π _ , _ ▷ F′ ▹ G′ , Πₙ nfF′ nfG′ , Π-cong ⊢F F≡F′ G≡G′ p≈p′ q≈q′
      , sub (Πₘ (▸-cong (ᵐ·-cong m p≈p′) δ▸F′) η′▸G′) γ≤γ′
  fullRedConv↓ {m = m} (Σ-cong ⊢F F G q≈q′) γ▸A =
    let invUsageΠΣ δ▸F η▸G γ≤γ′ = inv-usage-Σ γ▸A
        F′ , nfF′ , F≡F′ , δ▸F′ = fullRedConv↑ F δ▸F
        G′ , nfG′ , G≡G′ , η▸G′ = fullRedConv↑ G η▸G
        η′▸G′ = sub η▸G′ (≤ᶜ-reflexive (≈ᶜ-refl ∙ ≈-sym (·-congˡ q≈q′)))
    in  Σ _ , _ ▷ F′ ▹ G′ , Σₙ nfF′ nfG′ , Σ-cong ⊢F F≡F′ G≡G′ q≈q′
      , sub (Σₘ δ▸F′ η′▸G′) γ≤γ′

  fullRedTermConv↑ :
    Γ ⊢ t [conv↑] t′ ∷ A → γ ▸[ m ] t →
    ∃ λ u → Nf u × Γ ⊢ t ≡ u ∷ A × γ ▸[ m ] u
  fullRedTermConv↑ ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) γ▸t =
    let γ▸t′ = usagePres*Term γ▸t d
        u″ , nf , u′≡u″ , γ▸u″ = fullRedTermConv↓ t<>u γ▸t′
    in  u″ , nf , conv (trans (subset*Term d) u′≡u″) (sym (subset* D)) , γ▸u″

  fullRedTermConv↓ :
    Γ ⊢ t [conv↓] t′ ∷ A → γ ▸[ m ] t →
    ∃ λ u → Nf u × Γ ⊢ t ≡ u ∷ A × γ ▸[ m ] u
  fullRedTermConv↓ (ℕ-ins t) γ▸t =
    let u , nf , t≡u , γ▸u = fullRedNe~↓ t γ▸t
    in  u , ne nf , t≡u , γ▸u
  fullRedTermConv↓ (Empty-ins t) γ▸t =
    let u , nf , t≡u , γ▸u = fullRedNe~↓ t γ▸t
    in  u , ne nf , t≡u , γ▸u
  fullRedTermConv↓ (Unit-ins t) γ▸t =
    let u , nf , t≡u , γ▸u = fullRedNe~↓ t γ▸t
    in  u , ne nf , t≡u , γ▸u
  fullRedTermConv↓ (Σᵣ-ins t u t~u) γ▸t =
    let v , nf , t≡v , γ▸v = fullRedNe~↓ t~u γ▸t
        _ , t′ , _ = syntacticEqTerm t≡v
        _ , neT , _ = ne~↓ t~u
    in  v , ne nf , conv t≡v (neTypeEq neT t′ t) , γ▸v
  fullRedTermConv↓ (ne-ins ⊢t _ _ t) γ▸t =
    let u , nfU , t≡u , γ▸u = fullRedNe~↓ t γ▸t
        _ , ⊢t∷M , _ = syntacticEqTerm t≡u
        _ , neT , _ = ne~↓ t
    in  u , ne nfU , conv t≡u (neTypeEq neT ⊢t∷M ⊢t) , γ▸u
  fullRedTermConv↓ (univ ⊢t _ t) γ▸t =
    let u , nf , t≡u , γ▸u = fullRedConv↓ t γ▸t
    in  u , nf , inverseUnivEq ⊢t t≡u , γ▸u
  fullRedTermConv↓ (zero-refl ⊢Γ) γ▸t = zero , zeroₙ , refl (zeroⱼ ⊢Γ) , γ▸t
  fullRedTermConv↓ (suc-cong t) γ▸t =
    let invUsageSuc δ▸t γ≤δ = inv-usage-suc γ▸t
        u , nf , t≡u , δ▸u = fullRedTermConv↑ t δ▸t
    in  suc u , sucₙ nf , suc-cong t≡u , sub (sucₘ δ▸u) γ≤δ
  fullRedTermConv↓ (prod-cong! ⊢F ⊢G t↑t u↑u) γ▸t =
    let invUsageProdᵣ δ▸t η▸u γ″=δ+η γ≤γ″ = inv-usage-prodᵣ γ▸t
        t′ , nfT , t≡t′ , δ▸t′ = fullRedTermConv↑ t↑t δ▸t
        u′ , nfU , u≡u′ , η▸u′ = fullRedTermConv↑ u↑u η▸u
    in  prod! t′ u′ , prodₙ nfT nfU , prod-cong ⊢F ⊢G t≡t′ u≡u′
      , sub (prodᵣₘ δ▸t′ η▸u′ γ″=δ+η) γ≤γ″
  fullRedTermConv↓ {γ = γ} {m = m} (η-eq {p = p} ⊢t _ _ _ t∘0) γ▸t =
    let δ▸t∘0 = wkUsage (step id) γ▸t ∘ₘ var
        u , nf , t∘0≡u , δ▸u = fullRedTermConv↑ (t∘0 ≈-refl ≈-refl) δ▸t∘0
        ⊢G , _ , ⊢u = syntacticEqTerm t∘0≡u
        ⊢F , _ = syntacticΠ (syntacticTerm ⊢t)
        ΓF⊢ = wf ⊢F ∙ ⊢F
        wk⊢F = wk (step id) ΓF⊢ ⊢F
        wk⊢G = wk (lift (step id)) (ΓF⊢ ∙ wk⊢F) ⊢G
        ΓFF'⊢ = ΓF⊢ ∙ wk⊢F
        wk⊢u = wkTerm (lift (step id)) ΓFF'⊢ ⊢u
        wk⊢t = wkTerm (step id) ΓF⊢ ⊢t
        λu∘0 = lam p (U.wk (lift (step id)) u) ∘⟨ p ⟩ var x0
    in  lam _ u , lamₙ nf
      , η-eq ⊢F ⊢t (lamⱼ ⊢F ⊢u) (λ {p₁} {p₂} p≈p₁ p≈p₂ →
             let λu∘0 = lam p (U.wk (lift (step id)) u) ∘⟨ p₂ ⟩ var x0
             in  trans (PE.subst (λ x → _ ⊢ _ ≡ _ ∷ x) (wkSingleSubstId _)
                                 (app-cong (refl wk⊢t) (refl (var ΓF⊢ here)) p≈p₁ ≈-refl))
                       (trans t∘0≡u (PE.subst₂ (λ x y → _ ⊢ x ≡ λu∘0 ∷ y)
                                    (wkSingleSubstId u) (wkSingleSubstId _)
                                    (sym (β-red wk⊢F wk⊢G wk⊢u (var ΓF⊢ here) p≈p₂)))))
      , lamₘ (sub δ▸u (begin
          γ ∙ ⌜ m ⌝ · p                      ≈⟨ ≈ᶜ-refl ∙ ⌜⌝-·-comm m ⟩
          γ ∙ p · ⌜ m ⌝                      ≈˘⟨ +ᶜ-identityʳ _ ∙ ·⌜ᵐ·⌝ m ⟩
          γ +ᶜ 𝟘ᶜ ∙ p · ⌜ m ᵐ· p ⌝           ≈˘⟨ +ᶜ-congˡ (·ᶜ-zeroʳ _) ∙ +-identityˡ _ ⟩
          γ +ᶜ p ·ᶜ 𝟘ᶜ ∙ 𝟘 + p · ⌜ m ᵐ· p ⌝  ∎))
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset
  fullRedTermConv↓
    {t = t} {γ = γ} {m = m}
    (Σ-η {p = p} ⊢t _ tProd _ fstConv sndConv) γ▸t =
    let δ , δ▸t₁ , γ≤pδ = lemma m γ▸t
        γ▸t₂            = sndₘ γ▸t
        fst′ , nfFst′ , fst≡fst′ , δ▸u₁ = fullRedTermConv↑ fstConv δ▸t₁
        snd′ , nfSnd′ , snd≡snd′ , γ▸u₂ = fullRedTermConv↑ sndConv γ▸t₂
        _ , _ , ⊢fst′ = syntacticEqTerm fst≡fst′
        _ , _ , ⊢snd′₁ = syntacticEqTerm snd≡snd′
        ⊢ΣFG = syntacticTerm ⊢t
        ⊢F , ⊢G = syntacticΣ ⊢ΣFG

        Gfst≡Gfst′ = substTypeEq (refl ⊢G) fst≡fst′
        ⊢snd′ = conv ⊢snd′₁ Gfst≡Gfst′
        ⊢prod = prodⱼ ⊢F ⊢G ⊢fst′ ⊢snd′

        fstprod≡fst′ = Σ-β₁ ⊢F ⊢G ⊢fst′ ⊢snd′ ⊢prod PE.refl
        fst≡fstprod = trans fst≡fst′ (sym fstprod≡fst′)
        Gfst≡Gfstprod = substTypeEq (refl ⊢G) fst≡fstprod
        sndprod≡snd′ = conv (Σ-β₂ ⊢F ⊢G ⊢fst′ ⊢snd′ ⊢prod PE.refl)
                         (sym Gfst≡Gfstprod)
        snd≡sndprod = trans snd≡snd′ (sym sndprod≡snd′)
    in  prod! fst′ snd′ , prodₙ nfFst′ nfSnd′
      , Σ-η ⊢F ⊢G ⊢t ⊢prod fst≡fstprod snd≡sndprod
      , sub (prodₚₘ δ▸u₁ γ▸u₂)
          (begin
             γ            ≤⟨ ∧ᶜ-greatest-lower-bound γ≤pδ ≤ᶜ-refl ⟩
             p ·ᶜ δ ∧ᶜ γ  ∎)
    where
    ·ᶜ-increasing : (γ : Conₘ n) → γ ≤ᶜ p ·ᶜ γ
    ·ᶜ-increasing ε       = ε
    ·ᶜ-increasing (γ ∙ p) = ·ᶜ-increasing _ ∙ ·-increasing

    lemma :
      ∀ m →
      γ ▸[ m ] t →
      ∃ λ δ → δ ▸[ m ᵐ· p ] fst p t × γ ≤ᶜ p ·ᶜ δ
    lemma 𝟘ᵐ[ ok ] γ▸t =
        𝟘ᶜ
      , fstₘ 𝟘ᵐ[ ok ] (▸-𝟘 γ▸t) PE.refl (λ _ → inj₂ ok)
      , (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
           γ        ≤⟨ ▸-𝟘ᵐ γ▸t ⟩
           𝟘ᶜ       ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
           p ·ᶜ 𝟘ᶜ  ∎)
    lemma 𝟙ᵐ γ▸t with is-𝟘? p
    … | yes PE.refl =
        ⌜ ⌞ 𝟘 ⌟ ⌝ ·ᶜ γ
      , fstₘ 𝟙ᵐ
          (▸-cong
             (let open Tools.Reasoning.PropositionalEquality in
                ⌞ p ⌟ ·ᵐ 𝟙ᵐ  ≡⟨ ·ᵐ-comm _ 𝟙ᵐ ⟩
                𝟙ᵐ ·ᵐ ⌞ p ⌟  ≡⟨⟩
                ⌞ p ⌟        ∎)
             (▸-· γ▸t))
          ⌞𝟘⌟≡𝟘ᵐ?
          (λ _ → 𝟙≈𝟘⊎𝟘ᵐ)
      , (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
           γ                     ≤⟨ ·ᶜ-increasing _ ⟩
           𝟘 ·ᶜ γ                ≈˘⟨ ·ᶜ-congʳ (·-zeroˡ _) ⟩
           (𝟘 · ⌜ ⌞ 𝟘 ⌟ ⌝) ·ᶜ γ  ≈⟨ ·ᶜ-assoc _ _ _ ⟩
           𝟘 ·ᶜ ⌜ ⌞ 𝟘 ⌟ ⌝ ·ᶜ γ   ∎)
    … | no p≉𝟘 =
        γ
      , fstₘ 𝟙ᵐ
          (▸-cong (PE.sym (≉𝟘→⌞⌟≡𝟙ᵐ p≉𝟘)) γ▸t)
          (≉𝟘→⌞⌟≡𝟙ᵐ p≉𝟘)
          (λ p≈𝟘 → ⊥-elim (p≉𝟘 p≈𝟘))
      , (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
           γ       ≤⟨ ·ᶜ-increasing _ ⟩
           p ·ᶜ γ  ∎)

    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

  fullRedTermConv↓ (η-unit ⊢t _ tUnit _) γ▸t =
    star , starₙ , η-unit ⊢t (starⱼ (wfTerm ⊢t)) , sub starₘ γ≤𝟘ᶜ
    where
    γ≤𝟘ᶜ : γ ≤ᶜ 𝟘ᶜ
    γ≤𝟘ᶜ {γ = ε} = ε
    γ≤𝟘ᶜ {γ = γ ∙ p} = γ≤𝟘ᶜ ∙ p≤𝟘 p

fullRed :
  Γ ⊢ A → γ ▸[ m ] A →
  ∃ λ B → Nf B × Γ ⊢ A ≡ B × γ ▸[ m ] B
fullRed ⊢A = fullRedConv↑ (completeEq (refl ⊢A))

fullRedTerm :
  Γ ⊢ t ∷ A → γ ▸[ m ] t →
  ∃ λ u → Nf u × Γ ⊢ t ≡ u ∷ A × γ ▸[ m ] u
fullRedTerm ⊢t = fullRedTermConv↑ (completeEqTerm (refl ⊢t))
