open import Tools.Relation
open import Definition.Modality

module Definition.Modality.FullReduction {a ℓ}
       {M′ : Setoid a ℓ} (𝕄 : Modality M′)
       (p≤𝟘 : (p : Setoid.Carrier M′) → Modality._≤_ 𝕄 p (Modality.𝟘 𝕄))
       where

open Modality 𝕄
open Setoid M′ using (_≈_) renaming (Carrier to M)

open import Tools.Fin
open import Tools.Nat using (Nat)
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder

open import Definition.Untyped M hiding (_∷_; wk)
import Definition.Untyped M as U
open import Definition.Untyped.Properties M
open import Definition.Typed M′
open import Definition.Typed.Properties M′
open import Definition.Typed.Usage 𝕄
open import Definition.Typed.Weakening M′
open import Definition.Typed.Consequences.InverseUniv M′
open import Definition.Typed.Consequences.NeTypeEq M′
open import Definition.Typed.Consequences.Substitution M′
open import Definition.Typed.Consequences.Syntactic M′

open import Definition.Conversion M′
open import Definition.Conversion.Consequences.Completeness M′
open import Definition.Conversion.FullReduction M′
  hiding (fullRedNe; fullRedNe~↓; fullRed; fullRedConv↓; fullRedTerm; fullRedTermConv↓)
import Definition.Conversion.FullReduction M′ as FR
open import Definition.Conversion.Whnf M′

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
  fullRedNe (fst-cong p~p) γ▸t =
    let invUsageProj δ▸p γ≤δ = inv-usage-fst γ▸t
        p′ , neP′ , p≡p′ , δ▸p′ = fullRedNe~↓ p~p δ▸p
        ⊢ΣFG , _ , _ = syntacticEqTerm p≡p′
        ⊢F , ⊢G = syntacticΣ ⊢ΣFG
    in  fst p′ , fstₙ neP′ , fst-cong ⊢F ⊢G p≡p′
      , sub (fstₘ δ▸p′) γ≤δ
  fullRedNe (snd-cong p~p) γ▸t =
    let invUsageProj δ▸p γ≤δ = inv-usage-snd γ▸t
        p′ , neP′ , p≡p′ , δ▸p′ = fullRedNe~↓ p~p δ▸p
        ⊢ΣFG , _ , _ = syntacticEqTerm p≡p′
        ⊢F , ⊢G = syntacticΣ ⊢ΣFG
    in  snd p′ , sndₙ neP′ , snd-cong ⊢F ⊢G p≡p′
      , sub (sndₘ δ▸p′) γ≤δ
  fullRedNe (natrec-cong {p = p} {r = r} C z s n p≈p′ r≈r′) γ▸t =
    let invUsageNatrec δ▸z η▸s θ▸n γ≤γ′ = inv-usage-natrec γ▸t
        C′ , nfC′ , C≡C′ = FR.fullRed C
        z′ , nfZ′ , z≡z′ , δ▸z′ = fullRedTermConv↑ z δ▸z
        s′ , nfS′ , s≡s′ , η▸s′ = fullRedTermConv↑ s η▸s
        n′ , nfN′ , n≡n′ , θ▸n′ = fullRedNe~↓ n θ▸n
    in  natrec p r C′ z′ s′ n′ , natrecₙ nfC′ nfZ′ nfS′ nfN′
      , natrec-cong (proj₁ (syntacticEq C≡C′)) C≡C′ z≡z′ s≡s′ n≡n′ ≈-refl ≈-refl
      , sub (natrecₘ δ▸z′ η▸s′ θ▸n′) γ≤γ′
  fullRedNe (prodrec-cong {p = p} C g u p≈p′) γ▸t =
    let invUsageProdrec δ▸g η▸u P γ≤γ′ = inv-usage-prodrec γ▸t
        C′ , nfC′ , C≡C′ = FR.fullRed C
        g′ , nfg′ , g≡g′ , δ▸g′ = fullRedNe~↓ g δ▸g
        u′ , nfu′ , u≡u′ , η▸u′ = fullRedTermConv↑ u η▸u
        ⊢Σ , _ = syntacticEqTerm g≡g′
        ⊢F , ⊢G = syntacticΣ ⊢Σ
    in  prodrec p C′ g′ u′ , prodrecₙ nfC′ nfg′ nfu′
      , prodrec-cong ⊢F ⊢G C≡C′ g≡g′ u≡u′ ≈-refl
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
    let invUsageΠ δ▸F η▸G γ≤γ′ = inv-usage-Π γ▸A
        F′ , nfF′ , F≡F′ , δ▸F′ = fullRedConv↑ F δ▸F
        G′ , nfG′ , G≡G′ , η▸G′ = fullRedConv↑ G η▸G
        η′▸G′ = sub η▸G′ (≤ᶜ-reflexive (≈ᶜ-refl ∙ ≈-sym (·-congˡ q≈q′)))
    in  Π _ , _ ▷ F′ ▹ G′ , Πₙ nfF′ nfG′ , Π-cong ⊢F F≡F′ G≡G′ p≈p′ q≈q′
      , sub (Πₘ (▸-cong (ᵐ·-cong m p≈p′) δ▸F′) η′▸G′) γ≤γ′
  fullRedConv↓ (Σ-cong ⊢F F G q≈q′) γ▸A =
    let invUsageΣ δ▸F η▸G γ≤γ′ = inv-usage-Σ γ▸A
        F′ , nfF′ , F≡F′ , δ▸F′ = fullRedConv↑ F δ▸F
        G′ , nfG′ , G≡G′ , η▸G′ = fullRedConv↑ G η▸G
        η′▸G′ = sub η▸G′ (≤ᶜ-reflexive (≈ᶜ-refl ∙ ≈-sym (·-congˡ q≈q′)))
    in  Σ _ ▷ F′ ▹ G′ , Σₙ nfF′ nfG′ , Σ-cong ⊢F F≡F′ G≡G′ q≈q′
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
  fullRedTermConv↓ (prod-cong ⊢F ⊢G t↑t u↑u) γ▸t =
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
  fullRedTermConv↓ (Σ-η ⊢t _ tProd _ fstConv sndConv) γ▸t =
    let γ▸t₁ = fstₘ γ▸t
        γ▸t₂ = sndₘ γ▸t
        fst′ , nfFst′ , fst≡fst′ , γ▸u₁ = fullRedTermConv↑ fstConv γ▸t₁
        snd′ , nfSnd′ , snd≡snd′ , γ▸u₂ = fullRedTermConv↑ sndConv γ▸t₂
        _ , _ , ⊢fst′ = syntacticEqTerm fst≡fst′
        _ , _ , ⊢snd′₁ = syntacticEqTerm snd≡snd′
        ⊢ΣFG = syntacticTerm ⊢t
        ⊢F , ⊢G = syntacticΣ ⊢ΣFG

        Gfst≡Gfst′ = substTypeEq (refl ⊢G) fst≡fst′
        ⊢snd′ = conv ⊢snd′₁ Gfst≡Gfst′
        ⊢prod = prodⱼ ⊢F ⊢G ⊢fst′ ⊢snd′

        fstprod≡fst′ = Σ-β₁ ⊢F ⊢G ⊢fst′ ⊢snd′ ⊢prod
        fst≡fstprod = trans fst≡fst′ (sym fstprod≡fst′)
        Gfst≡Gfstprod = substTypeEq (refl ⊢G) fst≡fstprod
        sndprod≡snd′ = conv (Σ-β₂ ⊢F ⊢G ⊢fst′ ⊢snd′ ⊢prod) (sym Gfst≡Gfstprod)
        snd≡sndprod = trans snd≡snd′ (sym sndprod≡snd′)
    in  prod! fst′ snd′ , prodₙ nfFst′ nfSnd′
      , Σ-η ⊢F ⊢G ⊢t ⊢prod fst≡fstprod snd≡sndprod
      , prodₚₘ γ▸u₁ γ▸u₂
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
