------------------------------------------------------------------------
-- Validity for natural numbers
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Erasure.LogicalRelation.Assumptions
open import Graded.Modality

module Graded.Erasure.LogicalRelation.Fundamental.Nat
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Modality 𝕄)
  {R : Type-restrictions 𝕄}
  (as : Assumptions R)
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄
  where

open Assumptions as
open Has-well-behaved-zero 𝟘-well-behaved

open import Graded.Erasure.Extraction 𝕄
open import Graded.Erasure.LogicalRelation as
open import Graded.Erasure.LogicalRelation.Hidden as
open import Graded.Erasure.LogicalRelation.Value as
import Graded.Erasure.Target as T
import Graded.Erasure.Target.Properties as TP
open import Graded.Erasure.Target.Reasoning

open import Definition.Typed R
open import Definition.Typed.Consequences.Inversion R
import Definition.Typed.Consequences.RedSteps R as RS
open import Definition.Typed.Consequences.Reduction R
open import Definition.Typed.Consequences.Substitution R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Properties R
import Definition.Typed.Reasoning.Reduction R as RR

open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Fundamental R
open import Definition.LogicalRelation.Fundamental.Reducibility R
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Substitution.Introductions.Universe R
open import Definition.LogicalRelation.Substitution.Introductions.Nat R

open import Graded.Context 𝕄
open import Graded.Mode 𝕄

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PropositionalEquality

private
  variable
    n : Nat
    γ δ η χ : Conₘ n
    Γ : Con Term n
    A t u v : Term n
    t′ u′ v′ : T.Term n
    p q r : M
    m : Mode
    l l′ l″ l‴ : TypeLevel

opaque

  -- Validity of ℕ.

  ℕʳ :
    ⊢ Γ →
    γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ ℕ ∷[ m ] U
  ℕʳ ⊢Γ =
    ▸⊩ʳ∷⇔ .proj₂
      ( ⊩ᵛU (valid ⊢Γ)
      , λ _ →
          ®∷→®∷◂ (®∷U⇔ .proj₂ ((_ , 0<1) , Uᵣ (λ { PE.refl → T.refl })))
      )

opaque

  -- Validity of zero.

  zeroʳ :
    ⊢ Γ →
    γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ zero ∷[ m ] ℕ
  zeroʳ ⊢Γ =
    ▸⊩ʳ∷⇔ .proj₂
      ( ℕᵛ (valid ⊢Γ)
      , λ _ →
          ®∷→®∷◂ $ ®∷ℕ⇔ .proj₂ $
          zeroᵣ (id (zeroⱼ ⊢Δ)) T.refl
      )

opaque

  -- Validity of suc.

  sucʳ :
    Γ ⊢ t ∷ ℕ →
    γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] ℕ →
    γ ▸ Γ ⊩ʳ⟨ l ⟩ suc t ∷[ m ] ℕ
  sucʳ {t} {l} {m} ⊢t ⊩ʳt =
    case ▸⊩ʳ∷⇔ .proj₁ ⊩ʳt of λ
      (⊩ℕ , t®t) →
    case PE.singleton m of λ {
      (𝟘ᵐ , PE.refl) → ▸⊩ʳ∷[𝟘ᵐ] ⊩ℕ;
      (𝟙ᵐ , PE.refl) →
    ▸⊩ʳ∷⇔ .proj₂
      ( ⊩ℕ
      , λ {σ = σ} {σ′ = σ′} σ®σ′ →
          case escape-®∷[]◂ σ®σ′ of λ
            ⊩σ →
          case escape-⊩ˢ∷ ⊩σ of λ
            (⊢Δ , ⊢σ) →
          case
            (let open RR in
             suc (t [ σ ])  ∎⟨ sucⱼ (substitutionTerm ⊢t ⊢σ ⊢Δ) ⟩⇒)
          of λ
            suc-t[σ]⇒*suc-t[σ] →

          case                                           $⟨ t®t σ®σ′ ⟩
            t [ σ ] ®⟨ l ⟩ erase str t T.[ σ′ ] ∷ ℕ ◂ 𝟙  →⟨ ®∷→®∷◂ω non-trivial ⟩
            t [ σ ] ®⟨ l ⟩ erase str t T.[ σ′ ] ∷ ℕ      ⇔⟨ ®∷ℕ⇔ ⟩→
            t [ σ ] ® erase str t T.[ σ′ ] ∷ℕ            □
          of λ
            t[σ]®t[σ′] →

          ®∷→®∷◂ $ ®∷ℕ⇔ .proj₂ $
          case PE.singleton str of λ where
            (T.non-strict , PE.refl) →
              sucᵣ suc-t[σ]⇒*suc-t[σ] T.refl _ t[σ]®t[σ′]
            (T.strict , PE.refl) →
              case reduces-to-numeral PE.refl t[σ]®t[σ′] of λ
                (v′ , v′-num , erase-t[σ′]⇒*v′) →
              sucᵣ suc-t[σ]⇒*suc-t[σ]
                (T.lam (T.suc (T.var x0)) T.∘⟨ T.strict ⟩
                 erase T.strict t T.[ σ′ ]                    ⇒*⟨ TP.app-subst*-arg T.lam erase-t[σ′]⇒*v′ ⟩

                 T.lam (T.suc (T.var x0)) T.∘⟨ T.strict ⟩ v′  ⇒⟨ T.β-red (TP.Numeral→Value v′-num) ⟩

                 T.suc v′                                     ∎⇒)
                v′-num
                (                                              $⟨ t[σ]®t[σ′] ⟩
                 t [ σ ] ® erase T.strict t T.[ σ′ ] ∷ℕ        ⇔˘⟨ ®∷ℕ⇔ ⟩→
                 t [ σ ] ®⟨ l ⟩ erase T.strict t T.[ σ′ ] ∷ ℕ  →⟨ ®∷-⇒* erase-t[σ′]⇒*v′ ⟩
                 t [ σ ] ®⟨ l ⟩ v′ ∷ ℕ                         ⇔⟨ ®∷ℕ⇔ ⟩→
                 t [ σ ] ® v′ ∷ℕ                               □)
      ) }

private opaque

  -- If t ® t′ ∷ℕ holds, then t is well-typed.

  ®∷ℕ→⊢∷ℕ : t ® t′ ∷ℕ → Δ ⊢ t ∷ ℕ
  ®∷ℕ→⊢∷ℕ (zeroᵣ t⇒* _)    = syntacticRedTerm t⇒* .proj₂ .proj₁
  ®∷ℕ→⊢∷ℕ (sucᵣ t⇒* _ _ _) = syntacticRedTerm t⇒* .proj₂ .proj₁

opaque

  -- A lemma used to implement natrecʳ.

  natrecʳ′ :
    (∀ {v₁ v₂} →
     Δ ⊢ v₁ ⇒* v₂ ∷ ℕ →
     Δ ⊩⟨ l ⟩ A [ v₂ ]₀ ≡ A [ v₁ ]₀) →
    Δ ∙ ℕ ⊢ A →
    Δ ⊢ t ∷ A [ zero ]₀ →
    Δ ∙ ℕ ∙ A ⊢ u ∷ A [ suc (var x1) ]↑² →
    t ®⟨ l ⟩ t′ ∷ A [ zero ]₀ →
    (∀ {v v′ w w′} →
     v ® v′ ∷ℕ →
     Δ ⊢ w ∷ A [ v ]₀ →
     w ®⟨ l ⟩ w′ ∷ A [ v ]₀ →
     u [ v , w ]₁₀ ®⟨ l ⟩ u′ T.[ v′ , w′ ]₁₀ ∷ A [ suc v ]₀) →
    v ® v′ ∷ℕ →
    natrec p q r A t u v ®⟨ l ⟩ T.natrec t′ u′ v′ ∷ A [ v ]₀
  natrecʳ′
    {l} {A} {t} {u} {t′} {u′} {v} {v′} {p} {q} {r}
    A≡A ⊢A ⊢t ⊢u t®t′ u®u′ = λ where
      (zeroᵣ v⇒zero v′⇒zero) →                                           $⟨ t®t′ ⟩

        t ®⟨ l ⟩ t′ ∷ A [ zero ]₀                                        →⟨ ®∷-⇐* (redMany (natrec-zero ⊢A ⊢t ⊢u))
                                                                              (T.trans T.natrec-zero T.refl) ⟩
        natrec p q r A t u zero ®⟨ l ⟩ T.natrec t′ u′ T.zero ∷
          A [ zero ]₀                                                    →⟨ conv-®∷ $ A≡A v⇒zero ⟩

        natrec p q r A t u zero ®⟨ l ⟩ T.natrec t′ u′ T.zero ∷ A [ v ]₀  →⟨ ®∷-⇐* (RS.natrec-subst* ⊢A ⊢t ⊢u v⇒zero)
                                                                              (TP.natrec-subst* v′⇒zero) ⟩
        natrec p q r A t u v ®⟨ l ⟩ T.natrec t′ u′ v′ ∷ A [ v ]₀         □

      (sucᵣ {t′ = w} {v′ = w′} v⇒suc-w v′⇒suc-w′ _ w®w′) →             $⟨ natrecʳ′ A≡A ⊢A ⊢t ⊢u t®t′ u®u′ w®w′ ⟩

        natrec p q r A t u w ®⟨ l ⟩ T.natrec t′ u′ w′ ∷ A [ w ]₀       →⟨ u®u′ w®w′ $
                                                                          natrecⱼ ⊢A ⊢t ⊢u (®∷ℕ→⊢∷ℕ w®w′) ⟩
        u [ w , natrec p q r A t u w ]₁₀ ®⟨ l ⟩
          u′ T.[ w′ , T.natrec t′ u′ w′ ]₁₀ ∷ A [ suc w ]₀             →⟨ ®∷-⇐*
                                                                            (redMany $ natrec-suc ⊢A ⊢t ⊢u $
                                                                             inversion-suc (syntacticRedTerm v⇒suc-w .proj₂ .proj₂) .proj₁)
                                                                            (T.trans T.natrec-suc T.refl) ⟩
        natrec p q r A t u (suc w) ®⟨ l ⟩ T.natrec t′ u′ (T.suc w′) ∷
          A [ suc w ]₀                                                 →⟨ conv-®∷ $ A≡A v⇒suc-w ⟩
        natrec p q r A t u (suc w) ®⟨ l ⟩ T.natrec t′ u′ (T.suc w′) ∷
          A [ v ]₀                                                     →⟨ ®∷-⇐* (RS.natrec-subst* ⊢A ⊢t ⊢u v⇒suc-w)
                                                                            (TP.natrec-subst* v′⇒suc-w′) ⟩
        natrec p q r A t u v ®⟨ l ⟩ T.natrec t′ u′ v′ ∷ A [ v ]₀       □

opaque

  -- Validity of natrec.

  natrecʳ :
    Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ A →
    Γ ⊢ t ∷ A [ zero ]₀ →
    Γ ∙ ℕ ∙ A ⊢ u ∷ A [ suc (var x1) ]↑² →
    Γ ⊢ v ∷ ℕ →
    γ ▸ Γ ⊩ʳ⟨ l′ ⟩ t ∷[ m ] A [ zero ]₀ →
    δ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸ Γ ∙ ℕ ∙ A ⊩ʳ⟨ l″ ⟩ u ∷[ m ]
      A [ suc (var x1) ]↑² →
    η ▸ Γ ⊩ʳ⟨ l‴ ⟩ v ∷[ m ] ℕ →
    (∀ x → χ ⟨ x ⟩ PE.≡ 𝟘 →
     γ ⟨ x ⟩ PE.≡ 𝟘 × η ⟨ x ⟩ PE.≡ 𝟘 × δ ⟨ x ⟩ PE.≡ 𝟘) →
    χ ▸ Γ ⊩ʳ⟨ l ⟩ natrec p q r A t u v ∷[ m ] A [ v ]₀
  natrecʳ
    {Γ} {l} {A} {t} {u} {v} {γ} {l′} {m} {δ} {p} {r} {l″} {η} {l‴} {χ}
    {q} ⊩A ⊢t ⊢u ⊢v ⊩ʳt ⊩ʳu ⊩ʳv ≡𝟘→≡𝟘 =
    case ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]₀ ⊩A (fundamental-⊩ᵛ∷ ⊢v) of λ
      ⊩A[v] →
    case PE.singleton m of λ {
      (𝟘ᵐ , PE.refl) → ▸⊩ʳ∷[𝟘ᵐ] ⊩A[v];
      (𝟙ᵐ , PE.refl) →
    ▸⊩ʳ∷⇔ .proj₂
      ( ⊩A[v]
      , λ {σ = σ} {σ′ = σ′} σ®σ′ →
          case escape-®∷[]◂ σ®σ′ of λ
            ⊩σ →

          case                                                            $⟨ σ®σ′ ⟩
            σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ χ                                          →⟨ subsumption-®∷[]◂ (λ x → proj₁ ∘→ ≡𝟘→≡𝟘 x) ⟩
            σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ γ                                          →⟨ ▸⊩ʳ∷⇔ .proj₁ ⊩ʳt .proj₂ ⟩
            t [ σ ] ®⟨ l′ ⟩ erase str t T.[ σ′ ] ∷ A [ zero ]₀ [ σ ] ◂ 𝟙  →⟨ ®∷→®∷◂ω non-trivial ⟩
            t [ σ ] ®⟨ l′ ⟩ erase str t T.[ σ′ ] ∷ A [ zero ]₀ [ σ ]      ≡⟨ PE.cong (_®⟨_⟩_∷_ _ _ _) $ singleSubstLift A _ ⟩→
            t [ σ ] ®⟨ l′ ⟩ erase str t T.[ σ′ ] ∷ A [ σ ⇑ ] [ zero ]₀    →⟨ level-®∷ $ ⊩ᵛ→⊩ˢ∷→⊩∷→⊩[⇑][]₀ ⊩A ⊩σ (⊩zero {l = l} ⊢Δ) ⟩
            t [ σ ] ®⟨ l ⟩ erase str t T.[ σ′ ] ∷ A [ σ ⇑ ] [ zero ]₀     □
          of λ
            t[σ]®t[σ′] →

          case
            (λ {v = v} {v′ = v′} {w = w} {w′ = w′}
               (v®v′ : v ® v′ ∷ℕ)
               (⊢w : Δ ⊢ w ∷ A [ σ ⇑ ] [ v ]₀)
               (w®w′ : w ®⟨ l ⟩ w′ ∷ A [ σ ⇑ ] [ v ]₀) →
               case reducible-⊩∷ (®∷ℕ→⊢∷ℕ v®v′) of λ
                 ⊩v →                                                    $⟨ σ®σ′ ⟩

               σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ χ                                      →⟨ subsumption-®∷[]◂ (λ x → proj₂ ∘→ proj₂ ∘→ ≡𝟘→≡𝟘 x) ⟩

               σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ δ                                      →⟨ (λ σ®σ′ →
                                                                               ®∷[]∙◂∙⇔′ .proj₂
                                                                                 ( (_ , ⊩A)
                                                                                 , ( _
                                                                                   , PE.subst (_⊩⟨_⟩_∷_ _ _ _) (singleSubstComp _ _ A)
                                                                                       (reducible-⊩∷ ⊢w)
                                                                                   )
                                                                                 , ( _
                                                                                   , ®∷→®∷◂
                                                                                       (PE.subst (_®⟨_⟩_∷_ _ _ _) (singleSubstComp _ _ A)
                                                                                          w®w′)
                                                                                   )
                                                                                 , ®∷[]∙◂∙⇔′ .proj₂
                                                                                     ( (_ , wf-∙-⊩ᵛ ⊩A .proj₂) , (_ , ⊩v)
                                                                                     , (_ , ®∷→®∷◂ (®∷ℕ⇔ {l = l} .proj₂ v®v′)) , σ®σ′
                                                                                     )
                                                                                 )) ⟩
               consSubst (consSubst σ v) w ®
                 T.consSubst (T.consSubst σ′ v′) w′ ∷[ 𝟙ᵐ ] Γ ∙ ℕ ∙ A ◂
                 δ ∙ 𝟙 · p ∙ 𝟙 · r                                       →⟨ ▸⊩ʳ∷⇔ .proj₁ ⊩ʳu .proj₂ ⟩

               u [ consSubst (consSubst σ v) w ] ®⟨ l″ ⟩
                 erase str u T.[ T.consSubst (T.consSubst σ′ v′) w′ ] ∷
                 A [ suc (var x1) ]↑² [ consSubst (consSubst σ v) w ] ◂
                 𝟙                                                       ≡⟨ PE.cong₅ _®⟨_⟩_∷_◂_ (PE.sym $ doubleSubstComp u _ _ _) PE.refl
                                                                              (PE.sym $ TP.doubleSubstComp (erase _ u) _ _ _)
                                                                              (
                 A [ suc (var x1) ]↑² [ consSubst (consSubst σ v) w ]          ≡˘⟨ substComp↑² A _ ⟩
                 A [ consSubst σ (suc v) ]                                     ≡˘⟨ singleSubstComp _ _ A ⟩
                 A [ σ ⇑ ] [ suc v ]₀                                          ∎)
                                                                              PE.refl ⟩→
               u [ σ ⇑ ⇑ ] [ v , w ]₁₀ ®⟨ l″ ⟩
                 erase str u T.[ σ′ T.⇑ T.⇑ ] T.[ v′ , w′ ]₁₀ ∷
                 A [ σ ⇑ ] [ suc v ]₀ ◂ 𝟙                                →⟨ level-®∷ (⊩ᵛ→⊩ˢ∷→⊩∷→⊩[⇑][]₀ ⊩A ⊩σ (⊩suc ⊩v)) ∘→
                                                                            ®∷→®∷◂ω non-trivial ⟩
               u [ σ ⇑ ⇑ ] [ v , w ]₁₀ ®⟨ l ⟩
                 erase str u T.[ σ′ T.⇑ T.⇑ ] T.[ v′ , w′ ]₁₀ ∷
                 A [ σ ⇑ ] [ suc v ]₀                                    □)
          of λ
            u[σ⇑⇑]®u[σ′⇑⇑] →                                            $⟨ σ®σ′ ⟩

          σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ χ                                          →⟨ subsumption-®∷[]◂ (λ x → proj₁ ∘→ proj₂ ∘→ ≡𝟘→≡𝟘 x) ⟩

          σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ η                                          →⟨ ▸⊩ʳ∷⇔ .proj₁ ⊩ʳv .proj₂ ⟩

          v [ σ ] ®⟨ l‴ ⟩ erase str v T.[ σ′ ] ∷ ℕ ◂ 𝟙                  →⟨ ®∷ℕ⇔ .proj₁ ∘→ ®∷→®∷◂ω non-trivial ⟩

          v [ σ ] ® erase str v T.[ σ′ ] ∷ℕ                             →⟨ natrecʳ′
                                                                             (⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩A) (refl-⊩ˢ≡∷ ⊩σ) ∘→
                                                                              sym-⊩≡∷ ∘→ reducible-⊩≡∷ ∘→ subset*Term)
                                                                             (escape $ ⊩ᵛ→⊩ˢ∷→⊩[⇑] ⊩A ⊩σ)
                                                                             (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) $
                                                                              escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ (fundamental-⊩ᵛ∷ ⊢t) ⊩σ)
                                                                             (PE.subst (_⊢_∷_ _ _) (natrecSucCase _ A) $
                                                                              escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[⇑⇑]∷ (fundamental-⊩ᵛ∷ ⊢u) ⊩σ)
                                                                             t[σ]®t[σ′] u[σ⇑⇑]®u[σ′⇑⇑] ⟩
          (natrec p q r (A [ σ ⇑ ]) (t [ σ ]) (u [ σ ⇑ ⇑ ]) (v [ σ ])
             ®⟨ l ⟩
             T.natrec (erase str t T.[ σ′ ])
               (erase str u T.[ σ′ T.⇑ T.⇑ ]) (erase str v T.[ σ′ ]) ∷
             A [ σ ⇑ ] [ v [ σ ] ]₀)                                    →⟨ ®∷→®∷◂ ∘→
                                                                           PE.subst (_®⟨_⟩_∷_ _ _ _) (PE.sym $ singleSubstLift A _) ⟩
          natrec p q r (A [ σ ⇑ ]) (t [ σ ]) (u [ σ ⇑ ⇑ ]) (v [ σ ])
            ®⟨ l ⟩
            T.natrec (erase str t T.[ σ′ ])
              (erase str u T.[ σ′ T.⇑ T.⇑ ]) (erase str v T.[ σ′ ]) ∷
            A [ v ]₀ [ σ ] ◂ 𝟙                                          □
      ) }
    where
    open Tools.Reasoning.PropositionalEquality
