module Definition.Typed.Usage where

open import Definition.Modality
open import Definition.Modality.Context
open import Definition.Modality.Context.Properties
open import Definition.Modality.Substitution.Properties
open import Definition.Modality.Usage
open import Definition.Modality.Usage.Inversion
open import Definition.Typed
open import Definition.Untyped hiding (_∷_)

open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality as PE


private
  variable
    n : Nat
    M : Set

-- Reduction preserves resource usage

usagePresTerm : {𝕄 : Modality M} {γ : Conₘ 𝕄 n} {Γ : Con (Term M) n} {t u A : Term M n}
              → γ ▸ t → Γ ⊢ t ⇒ u ∷ A → γ ▸ u
usagePresTerm γ▸t (conv t⇒u x) = usagePresTerm γ▸t t⇒u
usagePresTerm γ▸t (app-subst t⇒u x) with inv-usage-app γ▸t
... | invUsageApp δ▸t η▸a γ≤δ+pη = sub ((usagePresTerm δ▸t t⇒u) ∘ₘ η▸a) γ≤δ+pη
usagePresTerm γ▸λta (β-red x x₁ x₂ refl) with inv-usage-app γ▸λta
... | invUsageApp δ▸λt η▸a γ≤δ′+pη with inv-usage-lam δ▸λt
... | invUsageLam δ▸t δ′≤δ = sub (sgSubstₘ-lemma δ▸t η▸a) (≤ᶜ-transitive γ≤δ′+pη (+ᶜ-monotone δ′≤δ))
usagePresTerm γ▸t (fst-subst x x₁ t⇒u) with inv-usage-fst γ▸t
... | invUsageProj 𝟘▸t γ≤𝟘 = sub (fstₘ (usagePresTerm 𝟘▸t t⇒u)) γ≤𝟘
usagePresTerm γ▸t (snd-subst x x₁ t⇒u) with inv-usage-snd γ▸t
... | invUsageProj 𝟘▸t γ≤𝟘 = sub (sndₘ (usagePresTerm 𝟘▸t t⇒u)) γ≤𝟘
usagePresTerm γ▸t′ (Σ-β₁ x x₁ x₂ x₃) with inv-usage-fst γ▸t′
... | invUsageProj 𝟘▸tu γ≤𝟘 with inv-usage-prod 𝟘▸tu
... | invUsageProd δ▸t η▸u refl 𝟘≤γ″ = sub δ▸t (≤ᶜ-transitive γ≤𝟘 {!𝟘≤γ″!})
usagePresTerm γ▸u′ (Σ-β₂ x x₁ x₂ x₃) with inv-usage-snd γ▸u′
... | invUsageProj 𝟘▸tu γ≤𝟘 with inv-usage-prod 𝟘▸tu
... | invUsageProd δ▸t η▸u refl 𝟘≤γ″ =  {!!}
usagePresTerm γ▸ptu (prodrec-subst x x₁ x₂ x₃ t⇒t′) with inv-usage-prodrec γ▸ptu
... | invUsageProdrec δ▸t η▸u γ≤pδ+η = sub (prodrecₘ (usagePresTerm δ▸t t⇒t′) η▸u) γ≤pδ+η
usagePresTerm γ▸ptu (prodrec-β {p} x x₁ x₂ x₃ x₄ x₅) with inv-usage-prodrec γ▸ptu
... | invUsageProdrec {δ} {η} δ▸tt′ η▸u γ≤pδ+η with inv-usage-prod δ▸tt′
... | invUsageProd {δ = δ′} {η = η′} δ′▸t η′▸t′ refl δ≤δ′+η′ = sub
  (doubleSubstₘ-lemma η▸u η′▸t′ δ′▸t)
  (≤ᶜ-transitive γ≤pδ+η (subst₂ _≤ᶜ_ refl eq (+ᶜ-monotone (·ᶜ-monotone δ≤δ′+η′))))
    where
    eq = begin
       p ·ᶜ (δ′ +ᶜ η′) +ᶜ η    ≡⟨ +ᶜ-comm (p ·ᶜ (δ′ +ᶜ η′)) η ⟩
       η +ᶜ p ·ᶜ (δ′ +ᶜ η′)    ≡⟨ cong₂ _+ᶜ_ refl (·ᶜ-distribˡ-+ᶜ p δ′ η′) ⟩
       η +ᶜ p ·ᶜ δ′ +ᶜ p ·ᶜ η′ ≡⟨ cong₂ _+ᶜ_ refl (+ᶜ-comm (p ·ᶜ δ′) (p ·ᶜ η′)) ⟩
       η +ᶜ p ·ᶜ η′ +ᶜ p ·ᶜ δ′ ∎
usagePresTerm γ▸natrec (natrec-subst x x₁ x₂ t⇒u) with inv-usage-natrec γ▸natrec
... | invUsageNatrec δ▸z δ▸s η▸n γ≤γ′ = sub (natrecₘ δ▸z δ▸s (usagePresTerm η▸n t⇒u)) γ≤γ′
usagePresTerm γ▸natrec (natrec-zero x x₁ x₂) with inv-usage-natrec γ▸natrec
... | invUsageNatrec δ▸z δ▸s η▸n γ≤γ′ = sub δ▸z (≤ᶜ-transitive γ≤γ′ {!!})
usagePresTerm {𝕄 = 𝕄} γ▸natrec (natrec-suc {p = p} {r = r} x x₁ x₂ x₃) with inv-usage-natrec γ▸natrec
... | invUsageNatrec {δ = δ} {η} δ▸z δ▸s η▸sn γ≤γ′ with inv-usage-suc η▸sn
... | invUsageSuc {δ = η′} η′▸n η≤η′ = sub
  (doubleSubstₘ-lemma δ▸s (natrecₘ δ▸z δ▸s η′▸n) η′▸n)
  (≤ᶜ-transitive γ≤γ′ (subst₂ _≤ᶜ_ refl eq (·ᶜ-monotone
    (+ᶜ-monotone₂ ≤ᶜ-reflexive (·ᶜ-monotone η≤η′)))))
  where
  r* = Modality._* 𝕄 r
  eq = begin
     r* ·ᶜ (δ +ᶜ p ·ᶜ η′)
       ≡⟨ cong₂ _·ᶜ_ (Modality.*-StarSemiring 𝕄 r) refl ⟩
     _ ≡⟨ ·ᶜ-distribʳ-+ᶜ (Modality.𝟙 𝕄) (Modality._·_ 𝕄 r r*) (δ +ᶜ p ·ᶜ η′) ⟩
     _ ≡⟨ cong₂ _+ᶜ_ (·ᶜ-identityˡ (δ +ᶜ p ·ᶜ η′)) (·ᶜ-assoc r r* (δ +ᶜ p ·ᶜ η′)) ⟩
     _ ≡⟨ +ᶜ-assoc δ (p ·ᶜ η′) _ ⟩
     _ ≡⟨ cong₂ _+ᶜ_ refl (+ᶜ-comm (p ·ᶜ η′) _) ⟩
     _ ∎
usagePresTerm γ▸et (Emptyrec-subst x t⇒u) with inv-usage-Emptyrec γ▸et
... | invUsageEmptyrec δ▸t γ≤δ = sub (Emptyrecₘ (usagePresTerm δ▸t t⇒u)) γ≤δ

usagePres : {𝕄 : Modality M} {γ : Conₘ 𝕄 n} {Γ : Con (Term M) n} {A B : Term M n}
          → γ ▸ A → Γ ⊢ A ⇒ B → γ ▸ B
usagePres γ▸A (univ A⇒B) = usagePresTerm γ▸A A⇒B


-- usagePresTerm x (conv y x₁) = {!usagePresTerm x!}
-- usagePresTerm x (app-subst y x₁) = {!!}
-- usagePresTerm γ▸λpt∘a (β-red Γ⊢A Γ∙A⊢t∷B Γ⊢a∷A refl) with inv-usage-app γ▸λpt∘a
-- ... | invUsageApp δ▸λpt η▸a γ≤δ+pη with inv-usage-lam δ▸λpt
-- ... | invUsageLam δ≤δ′ δ′∙p▸t = {!substₘ-lemma !}
-- usagePresTerm x (fst-subst x₁ x₂ y) = {!!}
-- usagePresTerm x (snd-subst x₁ x₂ y) = {!!}
-- usagePresTerm x (Σ-β₁ x₁ x₂ x₃ x₄) = {!!}
-- usagePresTerm x (Σ-β₂ x₁ x₂ x₃ x₄) = {!!}
-- usagePresTerm x (prodrec-subst x₁ x₂ x₃ x₄ y) = {!!}
-- usagePresTerm x (prodrec-β x₁ x₂ x₃ x₄ x₅ x₆) = {!!}
-- usagePresTerm x (natrec-subst x₁ x₂ x₃ y) = {!!}
-- usagePresTerm x (natrec-zero x₁ x₂ x₃) = {!!}
-- usagePresTerm x (natrec-suc x₁ x₂ x₃ x₄) = {!!}
-- usagePresTerm x (Emptyrec-subst x₁ y) = {!!}

{-
{-# TERMINATING #-}
usagePresTerm : {𝕄 : Modality M} {γ : Conₘ 𝕄 n} {Γ : Con (Term M) n} {t u A : Term M n}
              → γ ▸ t → Γ ⊢ t ⇒ u ∷ A → γ ▸ u
usagePresTerm γ▸t (conv t⇒u x) = usagePresTerm γ▸t t⇒u
usagePresTerm (γ▸t ∘ₘ δ▸u) (app-subst t⇒u x) = usagePresTerm γ▸t t⇒u ∘ₘ δ▸u

usagePresTerm (_∘ₘ_ {γ} {δ = δ} {u} {p} (lamₘ γ▸t) δ▸u) (β-red x x₁ x₂ PE.refl) =
  PE.subst₂ _▸_ eq PE.refl Ψγ▸σt
  where
  Ψγ▸σt = substₘ-lemma (sgSubstₘ δ) (sgSubst u) (wf-sgSubstₘ δ▸u) γ▸t
  eq = PE.begin
       p ·ᶜ δ +ᶜ idSubstₘ *> γ PE.≡⟨ PE.cong₂ _+ᶜ_ PE.refl (idSubstₘ-LeftIdentity γ) ⟩
       p ·ᶜ δ +ᶜ γ             PE.≡⟨ +ᶜ-comm (p ·ᶜ δ) γ ⟩
       γ +ᶜ p ·ᶜ δ             PE.∎

usagePresTerm (sub γ▸t γ≤γ′ ∘ₘ δ▸u) (β-red x x₁ x₂ PE.refl) =
  sub (usagePresTerm (γ▸t ∘ₘ δ▸u) (β-red x x₁ x₂ PE.refl)) (+ᶜ-monotone γ≤γ′)

usagePresTerm (fstₘ γ▸t) (fst-subst x x₁ t⇒u) = fstₘ (usagePresTerm γ▸t t⇒u)
usagePresTerm (fstₘ (prodₘ {γ} {δ = δ} γ▸t γ▸t₁ x₄)) (Σ-β₁ x x₁ x₂ x₃) rewrite proj₁ (+ᶜ-noInverse γ δ (PE.sym x₄)) = γ▸t
usagePresTerm {u = u} (fstₘ (sub γ▸t x₄)) (Σ-β₁ x x₁ x₂ x₃) = {!usagePresTerm γ▸t !}
  where
  qw = (Σ-β₁ x x₁ x₂ x₃)
  qwe = usagePresTerm {!fstₘ γ▸t!} qw

usagePresTerm (sndₘ γ▸t) (snd-subst x x₁ t⇒u) = sndₘ (usagePresTerm γ▸t t⇒u)
usagePresTerm (sndₘ (prodₘ {γ} {δ = δ} γ▸t γ▸t₁ x₄)) (Σ-β₂ x x₁ x₂ x₃) rewrite proj₂ (+ᶜ-noInverse γ δ (PE.sym x₄)) = γ▸t₁
usagePresTerm (sndₘ (sub γ▸t x₄)) (Σ-β₂ x x₁ x₂ x₃) = {!!}

usagePresTerm (prodrecₘ γ▸t δ▸u) (prodrec-subst x x₁ x₂ x₃ t⇒u) = prodrecₘ (usagePresTerm γ▸t t⇒u) δ▸u
usagePresTerm (prodrecₘ {δ = δ} {p} (prodₘ {γ} {t} {γ₁} {u = t₁} γ▸t γ▸t₁ eq) δ▸u) (prodrec-β x x₁ x₂ x₃ x₄ x₅) = PE.subst₂ _▸_ eq′ PE.refl {!!} --Ψγ▸σt
  where
  Ψγ▸σt = substₘ-lemma
          (consSubstₘ (sgSubstₘ γ₁) γ)
          (consSubst (consSubst idSubst t₁) t)
          (wf-consSubstₘ (wf-sgSubstₘ γ▸t₁) γ▸t)
          δ▸u
  eq′ = PE.begin
        p ·ᶜ γ +ᶜ p ·ᶜ γ₁ +ᶜ idSubstₘ *> δ
          PE.≡⟨ PE.sym (+ᶜ-assoc (p ·ᶜ γ) (p ·ᶜ γ₁) (idSubstₘ *> δ)) ⟩
        (p ·ᶜ γ +ᶜ p ·ᶜ γ₁) +ᶜ idSubstₘ *> δ
          PE.≡⟨ PE.cong₂ _+ᶜ_ (PE.sym (·ᶜ-distribˡ-+ᶜ p γ γ₁)) (idSubstₘ-LeftIdentity δ) ⟩
         p ·ᶜ (γ +ᶜ γ₁) +ᶜ δ
           PE.≡⟨ PE.cong₂ _+ᶜ_ (PE.cong₂ _·ᶜ_ PE.refl (PE.sym eq)) PE.refl ⟩
         _ PE.∎

usagePresTerm (prodrecₘ {γ} {δ = δ} {p} (sub γ▸t x₆) δ▸u) (prodrec-β {t = t} {t′} x x₁ x₂ x₃ x₄ x₅) = {!sub γ▸t x₆!}
  where
    Ψγ▸σt = substₘ-lemma
      (consSubstₘ (sgSubstₘ {!!}) {!!})
      (consSubst (consSubst idSubst t′) t)
      {!!}
       δ▸u

usagePresTerm (natrecₘ γ▸z γ▸s δ▸z) (natrec-subst x x₁ x₂ t⇒u) = natrecₘ γ▸z γ▸s (usagePresTerm δ▸z t⇒u)
usagePresTerm {𝕄 = 𝕄} (natrecₘ {γ} {q} {p} {δ} γ▸z γ▸s δ▸n) (natrec-zero x x₁ x₂) = sub γ▸z le
  where
  δ≤𝟘 : {η : Conₘ 𝕄 n} → η ▸ zero → η ≤ᶜ 𝟘ᶜ
  δ≤𝟘 zeroₘ = ≤ᶜ-reflexive
  δ≤𝟘 (sub x x₁) = ≤ᶜ-transitive x₁ (δ≤𝟘 x)
  le = ≤ᶜ-transitive
          (PE.subst₂ _≤ᶜ_
            PE.refl
            (·ᶜ-identityˡ _)
            (·ᶜ-monotone₂ ≤ᶜ-reflexive {!!})
          )
          (PE.subst₂ _≤ᶜ_
            PE.refl
            (+ᶜ-identityʳ _)
            (+ᶜ-monotone₂ ≤ᶜ-reflexive (PE.subst₂ _≤ᶜ_
              PE.refl
              (·ᶜ-zeroʳ p)
              (·ᶜ-monotone (δ≤𝟘 δ▸n))
            ))
          )

usagePresTerm {𝕄 = 𝕄} (natrecₘ {γ} {q = q} {p} {δ} {G = G} {z} {s} γ▸z γ▸s δ▸sucn) (natrec-suc {n = n} x x₁ x₂ x₃) = PE.subst₂ _▸_ eq PE.refl {!Ψγ▸σt!} --Ψγ▸σt
  where
  η▸n : {𝕄 : Modality M} {m : Nat} {η : Conₘ 𝕄 m} {t : Term M m} → η ▸ suc t → η ▸ t
  η▸n (sucₘ x) = x
  η▸n (sub x x₁) = sub (η▸n x) x₁
  Ψγ▸σt = substₘ-lemma
    (consSubstₘ (consSubstₘ idSubstₘ ((Modality._* 𝕄 q) ·ᶜ (γ +ᶜ p ·ᶜ δ))) δ)
    (consSubst (consSubst idSubst (natrec p q G z s n)) n)
    (wf-consSubstₘ (wf-sgSubstₘ (natrecₘ γ▸z γ▸s (η▸n δ▸sucn))) (η▸n δ▸sucn))
    γ▸s
  eq = PE.begin
       ((idSubstₘ ∙ ((Modality._* 𝕄 q) ·ᶜ (γ +ᶜ p ·ᶜ δ))) ∙ δ) *> (γ ∙ q ∙ p)
         PE.≡⟨ PE.refl ⟩
       p ·ᶜ δ +ᶜ (idSubstₘ ∙ ((Modality._* 𝕄 q) ·ᶜ (γ +ᶜ p ·ᶜ δ))) *> (γ ∙ q)
         PE.≡⟨ PE.refl ⟩
       p ·ᶜ δ +ᶜ q ·ᶜ (Modality._* 𝕄 q) ·ᶜ (γ +ᶜ p ·ᶜ δ) +ᶜ idSubstₘ *> γ
         PE.≡⟨ PE.cong₂ _+ᶜ_ PE.refl (PE.cong₂ _+ᶜ_ PE.refl (idSubstₘ-LeftIdentity γ)) ⟩
       p ·ᶜ δ +ᶜ q ·ᶜ (Modality._* 𝕄 q) ·ᶜ (γ +ᶜ p ·ᶜ δ) +ᶜ γ
         PE.≡⟨ PE.cong₂ _+ᶜ_ PE.refl (+ᶜ-comm (q ·ᶜ (Modality._* 𝕄 q) ·ᶜ (γ +ᶜ p ·ᶜ δ)) γ) ⟩
       p ·ᶜ δ +ᶜ γ +ᶜ q ·ᶜ (Modality._* 𝕄 q) ·ᶜ (γ +ᶜ p ·ᶜ δ)
         PE.≡⟨ PE.sym (+ᶜ-assoc (p ·ᶜ δ) γ _) ⟩
       (p ·ᶜ δ +ᶜ γ) +ᶜ q ·ᶜ (Modality._* 𝕄 q) ·ᶜ (γ +ᶜ p ·ᶜ δ)
         PE.≡⟨ PE.cong₂ _+ᶜ_ (+ᶜ-comm (p ·ᶜ δ) γ) PE.refl ⟩
       (γ +ᶜ p ·ᶜ δ) +ᶜ q ·ᶜ (Modality._* 𝕄 q) ·ᶜ (γ +ᶜ p ·ᶜ δ)
         PE.≡⟨ PE.cong₂ _+ᶜ_ (PE.sym (·ᶜ-identityˡ _)) (PE.sym (·ᶜ-assoc q (Modality._* 𝕄 q) (γ +ᶜ p ·ᶜ δ))) ⟩
       (Modality.𝟙 𝕄) ·ᶜ (γ +ᶜ p ·ᶜ δ) +ᶜ (Modality._·_ 𝕄 q (Modality._* 𝕄 q)) ·ᶜ (γ +ᶜ p ·ᶜ δ)
         PE.≡⟨ PE.sym (·ᶜ-distribʳ-+ᶜ (Modality.𝟙 𝕄) (Modality._·_ 𝕄 q (Modality._* 𝕄 q)) (γ +ᶜ p ·ᶜ δ)) ⟩
       (Modality._+_ 𝕄 (Modality.𝟙 𝕄) (Modality._·_ 𝕄 q (Modality._* 𝕄 q))) ·ᶜ (γ +ᶜ p ·ᶜ δ)
         PE.≡⟨ PE.cong₂ _·ᶜ_ (PE.sym (Modality.*-StarSemiring 𝕄 q)) PE.refl ⟩
       (Modality._* 𝕄 q) ·ᶜ (γ +ᶜ p ·ᶜ δ) PE.∎

usagePresTerm (Emptyrecₘ γ▸t) (Emptyrec-subst x t⇒u) = Emptyrecₘ (usagePresTerm γ▸t t⇒u)
usagePresTerm (sub γ▸t x) t⇒u = sub (usagePresTerm γ▸t t⇒u) x





-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
