------------------------------------------------------------------------
-- Typing and reduction are closed under weakenings
------------------------------------------------------------------------

open import Definition.Typed.Restrictions

module Definition.Typed.Weakening
  {a} {M : Set a}
  (R : Type-restrictions M)
  where

open import Definition.Untyped M as U hiding (wk ; _∷_)
open import Definition.Untyped.Properties M
open import Definition.Typed R hiding (_,_)

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
import Tools.PropositionalEquality as PE

private
  variable
    ℓ n m  : Nat
    A B t u : Term n
    Γ  : Con Term n
    Δ  : Con Term m
    Δ′ : Con Term ℓ
    ρ  : Wk m n
    ρ′ : Wk n ℓ

-- Weakening type

data _∷_⊆_ : Wk m n → Con Term m → Con Term n → Set a where
  id   :             id     ∷ Γ            ⊆ Γ
  step : ρ ∷ Δ ⊆ Γ → step ρ ∷ Δ ∙ A        ⊆ Γ
  lift : ρ ∷ Δ ⊆ Γ → lift ρ ∷ Δ ∙ U.wk ρ A ⊆ Γ ∙ A


-- Weakening composition

_•ₜ_ : ρ ∷ Γ ⊆ Δ → ρ′ ∷ Δ ⊆ Δ′ → ρ • ρ′ ∷ Γ ⊆ Δ′
id     •ₜ η′ = η′
step η •ₜ η′ = step (η •ₜ η′)
lift η •ₜ id = lift η
lift η •ₜ step η′ = step (η •ₜ η′)
_•ₜ_ {ρ = lift ρ} {ρ′ = lift ρ′} {Δ′ = Δ′ ∙ A} (lift η) (lift η′) =
  PE.subst (λ x → lift (ρ • ρ′) ∷ x ⊆ Δ′ ∙ A)
           (PE.cong₂ _∙_ PE.refl (PE.sym (wk-comp ρ ρ′ A)))
           (lift (η •ₜ η′))


-- Weakening of judgements

wkIndex : ∀ {n} → ρ ∷ Δ ⊆ Γ →
        let ρA = U.wk ρ A
            ρn = wkVar ρ n
        in  ⊢ Δ → n ∷ A ∈ Γ → ρn ∷ ρA ∈ Δ
wkIndex id ⊢Δ i = PE.subst (λ x → _ ∷ x ∈ _) (PE.sym (wk-id _)) i
wkIndex (step ρ) (⊢Δ ∙ A) i = PE.subst (λ x → _ ∷ x ∈ _)
                                       (wk1-wk _ _)
                                       (there (wkIndex ρ ⊢Δ i))
wkIndex (lift ρ) (⊢Δ ∙ A) (there i) = PE.subst (λ x → _ ∷ x ∈ _)
                                               (wk1-wk≡lift-wk1 _ _)
                                               (there (wkIndex ρ ⊢Δ i))
wkIndex (lift ρ) ⊢Δ here =
  let G = _
      n = _
  in  PE.subst (λ x → n ∷ x ∈ G)
               (wk1-wk≡lift-wk1 _ _)
               here

mutual
  wk : ρ ∷ Δ ⊆ Γ →
     let ρA = U.wk ρ A
     in  ⊢ Δ → Γ ⊢ A → Δ ⊢ ρA
  wk ρ ⊢Δ (ℕⱼ ⊢Γ) = ℕⱼ ⊢Δ
  wk ρ ⊢Δ (Emptyⱼ ⊢Γ) = Emptyⱼ ⊢Δ
  wk ρ ⊢Δ (Unitⱼ ⊢Γ ok) = Unitⱼ ⊢Δ ok
  wk ρ ⊢Δ (Uⱼ ⊢Γ) = Uⱼ ⊢Δ
  wk ρ ⊢Δ (ΠΣⱼ F G ok) = ΠΣⱼ ρF (wk (lift ρ) (⊢Δ ∙ ρF) G) ok
    where
    ρF = wk ρ ⊢Δ F
  wk ρ ⊢Δ (univ A) = univ (wkTerm ρ ⊢Δ A)

  wkTerm : {Δ : Con Term m} {ρ : Wk m n} → ρ ∷ Δ ⊆ Γ →
         let ρA = U.wk ρ A
             ρt = U.wk ρ t
         in ⊢ Δ → Γ ⊢ t ∷ A → Δ ⊢ ρt ∷ ρA
  wkTerm ρ ⊢Δ (ℕⱼ ⊢Γ) = ℕⱼ ⊢Δ
  wkTerm ρ ⊢Δ (Emptyⱼ ⊢Γ) = Emptyⱼ ⊢Δ
  wkTerm ρ ⊢Δ (Unitⱼ ⊢Γ ok) = Unitⱼ ⊢Δ ok
  wkTerm ρ ⊢Δ (ΠΣⱼ F G ok) =
    ΠΣⱼ ρF (wkTerm (lift ρ) (⊢Δ ∙ univ ρF) G) ok
    where
    ρF = wkTerm ρ ⊢Δ F
  wkTerm ρ ⊢Δ (var ⊢Γ x) = var ⊢Δ (wkIndex ρ ⊢Δ x)
  wkTerm ρ ⊢Δ (lamⱼ F t ok) =
    lamⱼ ρF (wkTerm (lift ρ) (⊢Δ ∙ ρF) t) ok
    where
    ρF = wk ρ ⊢Δ F
  wkTerm ρ ⊢Δ (_∘ⱼ_ {G = G} g a) = PE.subst (λ x → _ ⊢ _ ∷ x)
                                           (PE.sym (wk-β G))
                                           (wkTerm ρ ⊢Δ g ∘ⱼ wkTerm ρ ⊢Δ a)
  wkTerm ρ ⊢Δ (prodⱼ {G = G} ⊢F ⊢G t u ok) =
    let ρF = wk ρ ⊢Δ ⊢F
        ρG = wk (lift ρ) (⊢Δ ∙ ρF) ⊢G
        ρt = wkTerm ρ ⊢Δ t
        ρu = wkTerm ρ ⊢Δ u
        ρu = PE.subst (λ x → _ ⊢ _ ∷ x) (wk-β G) ρu
    in  prodⱼ ρF ρG ρt ρu ok
  wkTerm ρ ⊢Δ (fstⱼ {G = G} ⊢F ⊢G t) =
    let ρF = wk ρ ⊢Δ ⊢F
        ρG = wk (lift ρ) (⊢Δ ∙ ρF) ⊢G
        ρt = wkTerm ρ ⊢Δ t
    in  fstⱼ ρF ρG ρt
  wkTerm ρ ⊢Δ (sndⱼ {G = G} ⊢F ⊢G t) =
    let ρF = wk ρ ⊢Δ ⊢F
        ρG = wk (lift ρ) (⊢Δ ∙ ρF) ⊢G
        ρt = wkTerm ρ ⊢Δ t
    in  PE.subst (λ x → _ ⊢ snd _ _ ∷ x) (PE.sym (wk-β G)) (sndⱼ ρF ρG ρt)
  wkTerm ρ ⊢Δ (zeroⱼ ⊢Γ) = zeroⱼ ⊢Δ
  wkTerm ρ ⊢Δ (sucⱼ n) = sucⱼ (wkTerm ρ ⊢Δ n)
  wkTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (natrecⱼ {A = G} {s = s} ⊢G ⊢z ⊢s ⊢n) =
    PE.subst (λ x → _ ⊢ natrec _ _ _ _ _ _ _ ∷ x) (PE.sym (wk-β G))
             (natrecⱼ (wk (lift [ρ]) (⊢Δ ∙ ℕⱼ ⊢Δ) ⊢G)
                      (PE.subst (λ x → _ ⊢ _ ∷ x) (wk-β G) (wkTerm [ρ] ⊢Δ ⊢z))
                      (PE.subst (λ x → ((Δ ∙ ℕ) ∙ (U.wk (lift ρ) G)) ⊢ U.wk (lift (lift ρ)) s ∷ x)
                                (wk-β-natrec ρ G)
                                (wkTerm (lift (lift [ρ])) (((⊢Δ ∙ (ℕⱼ ⊢Δ))
                                        ∙ (wk (lift [ρ]) (⊢Δ ∙ (ℕⱼ ⊢Δ)) ⊢G)))
                                        ⊢s))
                      (wkTerm [ρ] ⊢Δ ⊢n))
  wkTerm
    {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (prodrecⱼ {A = A} ⊢F ⊢G ⊢A ⊢t ⊢u ok) =
    let ⊢ρF = wk [ρ] ⊢Δ ⊢F
        ⊢ρG = wk (lift [ρ]) (⊢Δ ∙ ⊢ρF) ⊢G
        ⊢ρA = wk (lift [ρ]) (⊢Δ ∙ ΠΣⱼ ⊢ρF ⊢ρG ok) ⊢A
        ⊢ρt = wkTerm [ρ] ⊢Δ ⊢t
        ⊢ρu = wkTerm (lift (lift [ρ])) (⊢Δ ∙ ⊢ρF ∙ ⊢ρG) ⊢u
    in  PE.subst (λ x → _ ⊢ prodrec _ _ _ _ _ _ ∷ x) (PE.sym (wk-β A))
                 (prodrecⱼ ⊢ρF ⊢ρG ⊢ρA ⊢ρt
                           (PE.subst (λ x → _ ⊢ _ ∷ x)
                                     (wk-β-prodrec ρ A) ⊢ρu)
                           ok)
  wkTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (Emptyrecⱼ {A = A} {t = e} ⊢A ⊢e) =
    (Emptyrecⱼ (wk [ρ] ⊢Δ ⊢A) (wkTerm [ρ] ⊢Δ ⊢e))
  wkTerm ρ ⊢Δ (starⱼ ⊢Γ ok) = starⱼ ⊢Δ ok
  wkTerm ρ ⊢Δ (conv t A≡B) = conv (wkTerm ρ ⊢Δ t) (wkEq ρ ⊢Δ A≡B)

  wkEq : ρ ∷ Δ ⊆ Γ →
       let ρA = U.wk ρ A
           ρB = U.wk ρ B
       in ⊢ Δ → Γ ⊢ A ≡ B → Δ ⊢ ρA ≡ ρB
  wkEq ρ ⊢Δ (univ A≡B) = univ (wkEqTerm ρ ⊢Δ A≡B)
  wkEq ρ ⊢Δ (refl A) = refl (wk ρ ⊢Δ A)
  wkEq ρ ⊢Δ (sym A≡B) = sym (wkEq ρ ⊢Δ A≡B)
  wkEq ρ ⊢Δ (trans A≡B B≡C) = trans (wkEq ρ ⊢Δ A≡B) (wkEq ρ ⊢Δ B≡C)
  wkEq ρ ⊢Δ (ΠΣ-cong F F≡H G≡E ok) =
    ΠΣ-cong ρF (wkEq ρ ⊢Δ F≡H) (wkEq (lift ρ) (⊢Δ ∙ ρF) G≡E) ok
    where
    ρF = wk ρ ⊢Δ F

  wkEqTerm : {Δ : Con Term m} {ρ : Wk m n} → ρ ∷ Δ ⊆ Γ →
           let ρA = U.wk ρ A
               ρt = U.wk ρ t
               ρu = U.wk ρ u
           in ⊢ Δ → Γ ⊢ t ≡ u ∷ A → Δ ⊢ ρt ≡ ρu ∷ ρA
  wkEqTerm ρ ⊢Δ (refl t) = refl (wkTerm ρ ⊢Δ t)
  wkEqTerm ρ ⊢Δ (sym t≡u) = sym (wkEqTerm ρ ⊢Δ t≡u)
  wkEqTerm ρ ⊢Δ (trans t≡u u≡r) = trans (wkEqTerm ρ ⊢Δ t≡u) (wkEqTerm ρ ⊢Δ u≡r)
  wkEqTerm ρ ⊢Δ (conv t≡u A≡B) = conv (wkEqTerm ρ ⊢Δ t≡u) (wkEq ρ ⊢Δ A≡B)
  wkEqTerm ρ ⊢Δ (ΠΣ-cong F F≡H G≡E ok) =
    let ρF = wk ρ ⊢Δ F
    in  ΠΣ-cong ρF (wkEqTerm ρ ⊢Δ F≡H)
          (wkEqTerm (lift ρ) (⊢Δ ∙ ρF) G≡E) ok
  wkEqTerm ρ ⊢Δ (app-cong {G = G} f≡g a≡b) =
    PE.subst (λ x → _ ⊢ _ ≡ _ ∷ x)
             (PE.sym (wk-β G))
             (app-cong (wkEqTerm ρ ⊢Δ f≡g) (wkEqTerm ρ ⊢Δ a≡b))
  wkEqTerm ρ ⊢Δ (β-red {G = G} {t = t} {a = a} F ⊢G ⊢t ⊢a x ok) =
    let ρF = wk ρ ⊢Δ F
        ⊢ρG = wk (lift ρ) (⊢Δ ∙ ρF) ⊢G
    in  PE.subst (λ x → _ ⊢ _ ≡ _ ∷ x)
                 (PE.sym (wk-β G))
                 (PE.subst (λ x → _ ⊢ U.wk _ (lam _ t ∘ a) ≡ x ∷ _)
                           (PE.sym (wk-β t))
                           (β-red ρF ⊢ρG (wkTerm (lift ρ) (⊢Δ ∙ ρF) ⊢t)
                                     (wkTerm ρ ⊢Δ ⊢a) x ok))
  wkEqTerm ρ ⊢Δ (η-eq F f g f0≡g0) =
    let ρF = wk ρ ⊢Δ F
    in  η-eq ρF (wkTerm ρ ⊢Δ f)
                (wkTerm ρ ⊢Δ g)
                (PE.subst₂ (λ t u → _ ⊢ t ∘ _ ≡ u ∘ _ ∷ _)
                           (PE.sym (wk1-wk≡lift-wk1 _ _))
                           (PE.sym (wk1-wk≡lift-wk1 _ _))
                           (wkEqTerm (lift ρ) (⊢Δ ∙ ρF) f0≡g0))
  wkEqTerm ρ ⊢Δ (fst-cong ⊢F ⊢G t≡t') =
    let ρF = wk ρ ⊢Δ ⊢F
        ρG = wk (lift ρ) (⊢Δ ∙ ρF) ⊢G
    in  fst-cong ρF ρG (wkEqTerm ρ ⊢Δ t≡t')
  wkEqTerm ρ ⊢Δ (snd-cong {G = G} ⊢F ⊢G t≡t') =
    let ρF = wk ρ ⊢Δ ⊢F
        ρG = wk (lift ρ) (⊢Δ ∙ ρF) ⊢G
        ρt≡t' = wkEqTerm ρ ⊢Δ t≡t'
    in  PE.subst (λ x → _ ⊢ snd _ _ ≡ snd _ _ ∷ x) (PE.sym (wk-β G))
      (snd-cong ρF ρG ρt≡t')
  wkEqTerm
    {Δ = Δ} {ρ = ρ}
    [ρ] ⊢Δ (prod-cong {G = G} {t} {t′} {u} {u′} ⊢F ⊢G t≡t′ u≡u′ ok) =
    let ρF = wk [ρ] ⊢Δ ⊢F
        ρG = wk (lift [ρ]) (⊢Δ ∙ ρF) ⊢G
        ρt≡t′ = wkEqTerm [ρ] ⊢Δ t≡t′
        ρu≡u′ = wkEqTerm [ρ] ⊢Δ u≡u′
    in  prod-cong ρF ρG ρt≡t′ (PE.subst (λ x → Δ ⊢ _ ≡ _ ∷ x) (wk-β G) ρu≡u′)
          ok
  wkEqTerm ρ ⊢Δ (Σ-η {G = G} ⊢F ⊢G ⊢p ⊢r fst≡ snd≡) =
    let ρF = wk ρ ⊢Δ ⊢F
        ρG = wk (lift ρ) (⊢Δ ∙ ρF) ⊢G
        ρp = wkTerm ρ ⊢Δ ⊢p
        ρr = wkTerm ρ ⊢Δ ⊢r
        ρfst≡ = wkEqTerm ρ ⊢Δ fst≡
        ρsnd≡ = wkEqTerm ρ ⊢Δ snd≡
        ρsnd≡ = PE.subst (λ x → _ ⊢ _ ≡ _ ∷ x)
                         (wk-β G)
                         ρsnd≡
    in  Σ-η ρF ρG ρp ρr ρfst≡ ρsnd≡
  wkEqTerm {ρ = ρ} [ρ] ⊢Δ (Σ-β₁ {G = G} ⊢F ⊢G t u p≡p′ ok) =
    let ρF = wk [ρ] ⊢Δ ⊢F
        ρG = wk (lift [ρ]) (⊢Δ ∙ ρF) ⊢G
        ρt = wkTerm [ρ] ⊢Δ t
        ρu = wkTerm [ρ] ⊢Δ u
        ρu = PE.subst (λ x → _ ⊢ _ ∷ x) (wk-β G) ρu
    in  Σ-β₁ ρF ρG ρt ρu p≡p′ ok
  wkEqTerm {ρ = ρ} [ρ] ⊢Δ (Σ-β₂ {G = G} ⊢F ⊢G t u p≡p′ ok) =
    let ρF = wk [ρ] ⊢Δ ⊢F
        ρG = wk (lift [ρ]) (⊢Δ ∙ ρF) ⊢G
        ρt = wkTerm [ρ] ⊢Δ t
        ρu = wkTerm [ρ] ⊢Δ u
        ρu = PE.subst (λ x → _ ⊢ _ ∷ x) (wk-β G) ρu
    in  PE.subst (λ x → _ ⊢ _ ≡ _ ∷ x) (PE.sym (wk-β G))
      (Σ-β₂ ρF ρG ρt ρu p≡p′ ok)
  wkEqTerm ρ ⊢Δ (suc-cong m≡n) = suc-cong (wkEqTerm ρ ⊢Δ m≡n)
  wkEqTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (natrec-cong {A = F} {s = s} {s′ = s′}
                                     ⊢F F≡F′ z≡z′ s≡s′ n≡n′) =
              PE.subst (λ x → Δ ⊢ natrec _ _ _ _ _ _ _ ≡ _ ∷ x) (PE.sym (wk-β F))
                       (natrec-cong (wk (lift [ρ]) (⊢Δ ∙ (ℕⱼ ⊢Δ)) ⊢F)
                          (wkEq (lift [ρ]) (⊢Δ ∙ ℕⱼ ⊢Δ) F≡F′)
                          (PE.subst (λ x → Δ ⊢ _ ≡ _ ∷ x) (wk-β F)
                                    (wkEqTerm [ρ] ⊢Δ z≡z′))
                          (PE.subst (λ x → ((Δ ∙ ℕ) ∙
                                    (U.wk (lift ρ) F)) ⊢ U.wk (lift (lift ρ)) s
                                                       ≡ U.wk (lift (lift ρ)) s′ ∷ x)
                                    (wk-β-natrec _ F)
                                    (wkEqTerm (lift (lift [ρ]))
                                              ((⊢Δ ∙ (ℕⱼ ⊢Δ)) ∙
                                              (wk (lift [ρ]) (⊢Δ ∙ ℕⱼ ⊢Δ) ⊢F)) s≡s′))
                          (wkEqTerm [ρ] ⊢Δ n≡n′))
  wkEqTerm
    {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ
    (natrec-zero {A = F} {z = z} {s = s} ⊢F ⊢z ⊢s) =
    PE.subst (λ x → Δ ⊢ natrec _ _ _ (U.wk (lift _) F) _ _ _ ≡ _ ∷ x)
             (PE.sym (wk-β F))
             (natrec-zero (wk (lift [ρ]) (⊢Δ ∙ ℕⱼ ⊢Δ) ⊢F)
                          (PE.subst (λ x → Δ ⊢ U.wk ρ z ∷ x)
                                    (wk-β F)
                                    (wkTerm [ρ] ⊢Δ ⊢z))
                          (PE.subst (λ x → ((Δ ∙ ℕ) ∙ (U.wk (lift ρ) F)) ⊢ U.wk (lift (lift ρ)) s ∷ x)
                                    (wk-β-natrec _ F)
                                    (wkTerm (lift (lift [ρ])) ((⊢Δ ∙ (ℕⱼ ⊢Δ))
                                      ∙ (wk (lift [ρ]) (⊢Δ ∙ (ℕⱼ ⊢Δ)) ⊢F)) ⊢s)))
  wkEqTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ
    (natrec-suc {A = F} {z = z} {s = s} {p = p} {q = q} {r = r} {n = n}
       ⊢F ⊢z ⊢s ⊢n) =
    let ρn = wkTerm [ρ] ⊢Δ ⊢n
        ρF = wk (lift [ρ]) (⊢Δ ∙ (ℕⱼ ⊢Δ)) ⊢F
        ρz = PE.subst (λ x → _ ⊢ _ ∷ x) (wk-β F) (wkTerm [ρ] ⊢Δ ⊢z)
    in  PE.subst (λ x → _ ⊢ natrec _ _ _ (U.wk (lift ρ) F) _ _ _
                          ≡ U.wk ρ (s [ n , natrec p q r F z s n ]) ∷ x)
             (PE.sym (wk-β F))
             (PE.subst (λ x → Δ ⊢ natrec _ _ _ _ _ _ _ ≡ x ∷ _)
                       (PE.sym (wk-β-doubleSubst ρ s (natrec p q r F z s n) n))
                       (natrec-suc ρF ρz
                                   (PE.subst (λ x → ((Δ ∙ ℕ) ∙ (U.wk (lift ρ) F)) ⊢ _ ∷ x)
                                             (wk-β-natrec _ F)
                                             (wkTerm (lift (lift [ρ]))
                                                     ((⊢Δ ∙ (ℕⱼ ⊢Δ)) ∙ ρF)
                                                     ⊢s))
                                   ρn))
  wkEqTerm
    {Δ = Δ} {ρ = ρ}
    [ρ] ⊢Δ (prodrec-cong {A = A} ⊢F ⊢G A≡A′ t≡t′ u≡u′ ok) =
    let ρF = wk [ρ] ⊢Δ ⊢F
        ρG = wk (lift [ρ]) (⊢Δ ∙ ρF) ⊢G
        ρA≡A′ = wkEq (lift [ρ]) (⊢Δ ∙ ΠΣⱼ ρF ρG ok) A≡A′
        ρt≡t′ = wkEqTerm [ρ] ⊢Δ t≡t′
        ρu≡u′ = wkEqTerm (lift (lift [ρ])) (⊢Δ ∙ ρF ∙ ρG) u≡u′
    in  PE.subst (λ x → Δ ⊢ prodrec _ _ _ _ _ _ ≡ _ ∷ x) (PE.sym (wk-β A))
                 (prodrec-cong ρF ρG ρA≡A′ ρt≡t′
                               (PE.subst (λ x → _ ⊢ _ ≡ _ ∷ x)
                                         (wk-β-prodrec ρ A) ρu≡u′)
                               ok)
  wkEqTerm
    {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ
    (prodrec-β {G = G} {A = A} {u = u} ⊢F ⊢G ⊢A ⊢t ⊢t′ ⊢u p≡p′ ok) =
    let ρF = wk [ρ] ⊢Δ ⊢F
        ρG = wk (lift [ρ]) (⊢Δ ∙ ρF) ⊢G
        ρA = wk (lift [ρ]) (⊢Δ ∙ ΠΣⱼ ρF ρG ok) ⊢A
        ρt = wkTerm [ρ] ⊢Δ ⊢t
        ρt′ = wkTerm [ρ] ⊢Δ ⊢t′
        ρu = wkTerm (lift (lift [ρ])) (⊢Δ ∙ ρF ∙ ρG) ⊢u
    in  PE.subst₂ (λ x y → _ ⊢ prodrec _ _ _ _ _ _ ≡ x ∷ y)
                  (PE.trans (subst-wk u)
                    (PE.trans (substVar-to-subst (λ{x0 → PE.refl; (x0 +1) → PE.refl; (x +1 +1) → PE.refl}) u)
                              (PE.sym (wk-subst u))))
                  (PE.sym (wk-β A))
                 (prodrec-β ρF ρG ρA ρt
                    (PE.subst (λ x → _ ⊢ _ ∷ x) (wk-β G) ρt′)
                    (PE.subst (λ x → _ ⊢ _ ∷ x) (wk-β-prodrec ρ A) ρu)
                    p≡p′ ok)
  wkEqTerm
    {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ
    (Emptyrec-cong {A = A} {B = A'} {t = e} {u = e'} A≡A' e≡e') =
    (Emptyrec-cong (wkEq [ρ] ⊢Δ A≡A')
                   (wkEqTerm [ρ] ⊢Δ e≡e'))
  wkEqTerm ρ ⊢Δ (η-unit e e') = η-unit (wkTerm ρ ⊢Δ e) (wkTerm ρ ⊢Δ e')

mutual
  wkRed : ρ ∷ Δ ⊆ Γ →
           let ρA = U.wk ρ A
               ρB = U.wk ρ B
           in ⊢ Δ → Γ ⊢ A ⇒ B → Δ ⊢ ρA ⇒ ρB
  wkRed ρ ⊢Δ (univ A⇒B) = univ (wkRedTerm ρ ⊢Δ A⇒B)

  wkRedTerm : {Δ : Con Term m} {ρ : Wk m n} → ρ ∷ Δ ⊆ Γ →
           let ρA = U.wk ρ A
               ρt = U.wk ρ t
               ρu = U.wk ρ u
           in ⊢ Δ → Γ ⊢ t ⇒ u ∷ A → Δ ⊢ ρt ⇒ ρu ∷ ρA
  wkRedTerm ρ ⊢Δ (conv t⇒u A≡B) = conv (wkRedTerm ρ ⊢Δ t⇒u) (wkEq ρ ⊢Δ A≡B)
  wkRedTerm ρ ⊢Δ (app-subst {G = B} t⇒u a) =
    PE.subst (λ x → _ ⊢ _ ⇒ _ ∷ x) (PE.sym (wk-β B))
             (app-subst (wkRedTerm ρ ⊢Δ t⇒u) (wkTerm ρ ⊢Δ a))
  wkRedTerm
    ρ ⊢Δ (β-red {F = A} {G = B} {t = t} {a = a} ⊢A ⊢B ⊢t ⊢a p≡q ok) =
    let ⊢ρA = wk ρ ⊢Δ ⊢A
        ⊢ρB = wk (lift ρ) (⊢Δ ∙ ⊢ρA) ⊢B
    in  PE.subst (λ x → _ ⊢ _ ⇒ _ ∷ x) (PE.sym (wk-β B))
                 (PE.subst (λ x → _ ⊢ U.wk _ (lam _ t ∘ a) ⇒ x ∷ _)
                           (PE.sym (wk-β t))
                           (β-red ⊢ρA ⊢ρB (wkTerm (lift ρ) (⊢Δ ∙ ⊢ρA) ⊢t)
                                      (wkTerm ρ ⊢Δ ⊢a) p≡q ok))
  wkRedTerm ρ ⊢Δ (fst-subst ⊢F ⊢G t⇒) =
    let ρF = wk ρ ⊢Δ ⊢F
        ρG = wk (lift ρ) (⊢Δ ∙ ρF) ⊢G
        ρt⇒ = wkRedTerm ρ ⊢Δ t⇒
    in  fst-subst ρF ρG ρt⇒
  wkRedTerm ρ ⊢Δ (snd-subst {G = G} ⊢F ⊢G t⇒) =
    let ρF = wk ρ ⊢Δ ⊢F
        ρG = wk (lift ρ) (⊢Δ ∙ ρF) ⊢G
        ρt⇒ = wkRedTerm ρ ⊢Δ t⇒
    in  PE.subst (λ x → _ ⊢ snd _ _ ⇒ snd _ _ ∷ x) (PE.sym (wk-β G))
      (snd-subst ρF ρG ρt⇒)
  wkRedTerm {ρ = ρ} [ρ] ⊢Δ (Σ-β₁ {G = G} ⊢F ⊢G t u p≡p′ ok) =
    let ρF = wk [ρ] ⊢Δ ⊢F
        ρG = wk (lift [ρ]) (⊢Δ ∙ ρF) ⊢G
        ρt = wkTerm [ρ] ⊢Δ t
        ρu = wkTerm [ρ] ⊢Δ u
        ρu = PE.subst (λ x → _ ⊢ _ ∷ x) (wk-β G) ρu
    in  Σ-β₁ ρF ρG ρt ρu p≡p′ ok
  wkRedTerm {ρ = ρ} [ρ] ⊢Δ (Σ-β₂ {G = G} ⊢F ⊢G t u p≡p′ ok) =
    let ρF = wk [ρ] ⊢Δ ⊢F
        ρG = wk (lift [ρ]) (⊢Δ ∙ ρF) ⊢G
        ρt = wkTerm [ρ] ⊢Δ t
        ρu = wkTerm [ρ] ⊢Δ u
        ρu = PE.subst (λ x → _ ⊢ _ ∷ x) (wk-β G) ρu
    in  PE.subst (λ x → _ ⊢ _ ⇒ _ ∷ x) (PE.sym (wk-β G))
      (Σ-β₂ ρF ρG ρt ρu p≡p′ ok)
  wkRedTerm
    {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ
    (prodrec-subst {A = A} ⊢F ⊢G ⊢A ⊢u t⇒t′ ok) =
    let ρF = wk [ρ] ⊢Δ ⊢F
        ρG = wk (lift [ρ]) (⊢Δ ∙ ρF) ⊢G
        ρA = wk (lift [ρ]) (⊢Δ ∙ ΠΣⱼ ρF ρG ok) ⊢A
        ρt⇒t′ = wkRedTerm [ρ] ⊢Δ t⇒t′
        ρu = wkTerm (lift (lift [ρ])) (⊢Δ ∙ ρF ∙ ρG) ⊢u
    in  PE.subst (λ x → Δ ⊢ prodrec _ _ _ _ _ _ ⇒ _ ∷ x) (PE.sym (wk-β A))
                 (prodrec-subst ρF ρG ρA
                               (PE.subst (λ x → _ ⊢ _ ∷ x)
                                         (wk-β-prodrec ρ A) ρu)
                               ρt⇒t′ ok)
  wkRedTerm
    {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ
    (prodrec-β {G = G} {A = A} {u = u} ⊢F ⊢G ⊢A ⊢t ⊢t′ ⊢u p≡p′ ok) =
    let ρF = wk [ρ] ⊢Δ ⊢F
        ρG = wk (lift [ρ]) (⊢Δ ∙ ρF) ⊢G
        ρA = wk (lift [ρ]) (⊢Δ ∙ ΠΣⱼ ρF ρG ok) ⊢A
        ρt = wkTerm [ρ] ⊢Δ ⊢t
        ρt′ = wkTerm [ρ] ⊢Δ ⊢t′
        ρu = wkTerm (lift (lift [ρ])) (⊢Δ ∙ ρF ∙ ρG) ⊢u
    in  PE.subst₂ (λ x y → _ ⊢ prodrec _ _ _ _ _ _ ⇒ x ∷ y)
          (PE.trans (subst-wk u)
            (PE.trans (substVar-to-subst
                         (λ where
                            x0        → PE.refl
                            (x0 +1)   → PE.refl
                            (x +1 +1) → PE.refl)
                         u)
            (PE.sym (wk-subst u))))
          (PE.sym (wk-β A))
          (prodrec-β ρF ρG ρA ρt
             (PE.subst (λ x → _ ⊢ _ ∷ x) (wk-β G) ρt′)
             (PE.subst (λ x → _ ⊢ _ ∷ x) (wk-β-prodrec ρ A) ρu)
             p≡p′ ok)
  wkRedTerm
    {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ
    (natrec-subst {A = F} {s = s} ⊢F ⊢z ⊢s n⇒n′) =
    PE.subst (λ x → _ ⊢ natrec _ _ _ _ _ _ _ ⇒ _ ∷ x) (PE.sym (wk-β F))
             (natrec-subst (wk (lift [ρ]) (⊢Δ ∙ ℕⱼ ⊢Δ) ⊢F)
                           (PE.subst (λ x → _ ⊢ _ ∷ x) (wk-β F)
                                     (wkTerm [ρ] ⊢Δ ⊢z))
                                     (PE.subst (λ x → ((Δ ∙ ℕ) ∙ (U.wk (lift ρ) F))
                                                    ⊢ U.wk (lift (lift ρ)) s ∷ x)
                                               (wk-β-natrec _ F)
                                               (wkTerm (lift (lift [ρ])) ((⊢Δ ∙ (ℕⱼ ⊢Δ)) ∙
                                                       (wk (lift [ρ]) (⊢Δ ∙ (ℕⱼ ⊢Δ)) ⊢F)) ⊢s))
                           (wkRedTerm [ρ] ⊢Δ n⇒n′))
  wkRedTerm
    {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (natrec-zero {A = F} {s = s} ⊢F ⊢z ⊢s) =
    PE.subst (λ x → _ ⊢ natrec _ _ _ (U.wk (lift ρ) F) _ _ _ ⇒ _ ∷ x)
             (PE.sym (wk-β F))
             (natrec-zero (wk (lift [ρ]) (⊢Δ ∙ ℕⱼ ⊢Δ) ⊢F)
                          (PE.subst (λ x → _ ⊢ _ ∷ x)
                                    (wk-β F)
                                    (wkTerm [ρ] ⊢Δ ⊢z))
                          (PE.subst (λ x → ((Δ ∙ ℕ) ∙ (U.wk (lift ρ) F))
                                         ⊢ U.wk (lift (lift ρ)) s ∷ x)
                                    (wk-β-natrec ρ F)
                                    (wkTerm (lift (lift [ρ])) ((⊢Δ ∙ (ℕⱼ ⊢Δ)) ∙
                                      (wk (lift [ρ]) (⊢Δ ∙ ℕⱼ ⊢Δ) ⊢F)) ⊢s))
             )
  wkRedTerm
    {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ
    (natrec-suc {A = F} {z = z} {s = s} {p = p} {q = q} {r = r} {n = n}
       ⊢F ⊢z ⊢s ⊢n) =
    let ρn = wkTerm [ρ] ⊢Δ ⊢n
        ρF = wk (lift [ρ]) (⊢Δ ∙ (ℕⱼ ⊢Δ)) ⊢F
        ρz = PE.subst (λ x → _ ⊢ _ ∷ x) (wk-β F) (wkTerm [ρ] ⊢Δ ⊢z)
        ρs = U.wk ρ (s [ n , natrec p q r F z s n ])
    in  PE.subst (λ x → _ ⊢ natrec _ _ _ (U.wk (lift ρ) F) _ _ _ ⇒ ρs ∷ x)
             (PE.sym (wk-β F))
             (PE.subst (λ x → _ ⊢ natrec _ _ _ _ _ _ _ ⇒ x ∷ _)
                       (PE.sym (wk-β-doubleSubst ρ s (natrec p q r F z s n) n))
                       (natrec-suc ρF ρz
                                   (PE.subst (λ x → ((Δ ∙ ℕ) ∙ (U.wk (lift ρ) F)) ⊢ _ ∷ x)
                                             (wk-β-natrec _ F)
                                             (wkTerm (lift (lift [ρ]))
                                                     ((⊢Δ ∙ (ℕⱼ ⊢Δ)) ∙ ρF)
                                                     ⊢s))
                                   ρn))
  wkRedTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (Emptyrec-subst {A = A} ⊢A n⇒n′) =
    (Emptyrec-subst (wk [ρ] ⊢Δ ⊢A)
                    (wkRedTerm [ρ] ⊢Δ n⇒n′))

wkRed* : ρ ∷ Δ ⊆ Γ →
           let ρA = U.wk ρ A
               ρB = U.wk ρ B
           in ⊢ Δ → Γ ⊢ A ⇒* B → Δ ⊢ ρA ⇒* ρB
wkRed* ρ ⊢Δ (id A) = id (wk ρ ⊢Δ A)
wkRed* ρ ⊢Δ (A⇒A′ ⇨ A′⇒*B) = wkRed ρ ⊢Δ A⇒A′ ⇨ wkRed* ρ ⊢Δ A′⇒*B

wkRed*Term : ρ ∷ Δ ⊆ Γ →
           let ρA = U.wk ρ A
               ρt = U.wk ρ t
               ρu = U.wk ρ u
           in ⊢ Δ → Γ ⊢ t ⇒* u ∷ A → Δ ⊢ ρt ⇒* ρu ∷ ρA
wkRed*Term ρ ⊢Δ (id t) = id (wkTerm ρ ⊢Δ t)
wkRed*Term ρ ⊢Δ (t⇒t′ ⇨ t′⇒*u) = wkRedTerm ρ ⊢Δ t⇒t′ ⇨ wkRed*Term ρ ⊢Δ t′⇒*u

wkRed:*: : ρ ∷ Δ ⊆ Γ →
         let ρA = U.wk ρ A
             ρB = U.wk ρ B
         in ⊢ Δ → Γ ⊢ A :⇒*: B → Δ ⊢ ρA :⇒*: ρB
wkRed:*: ρ ⊢Δ [ ⊢A , ⊢B , D ] = [ wk ρ ⊢Δ ⊢A , wk ρ ⊢Δ ⊢B , wkRed* ρ ⊢Δ D ]

wkRed:*:Term : ρ ∷ Δ ⊆ Γ →
             let ρA = U.wk ρ A
                 ρt = U.wk ρ t
                 ρu = U.wk ρ u
             in ⊢ Δ → Γ ⊢ t :⇒*: u ∷ A → Δ ⊢ ρt :⇒*: ρu ∷ ρA
wkRed:*:Term ρ ⊢Δ [ ⊢t , ⊢u , d ] =
  [ wkTerm ρ ⊢Δ ⊢t , wkTerm ρ ⊢Δ ⊢u , wkRed*Term ρ ⊢Δ d ]
