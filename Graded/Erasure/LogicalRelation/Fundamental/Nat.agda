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
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
import Definition.Typed.Reasoning.Reduction R as RR
open import Definition.Typed.Substitution R
open import Definition.Typed.Syntactic R

open import Definition.Untyped M
open import Definition.Untyped.Properties M

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
    l : Universe-level

opaque

  -- Validity of ℕ.

  ℕʳ : γ ▸ Γ ⊩ʳ ℕ ∷[ m ∣ n ] U zeroᵘ
  ℕʳ =
    ▸⊩ʳ∷⇔ .proj₂ λ _ _ →
    ®∷→®∷◂ (®∷U⇔ .proj₂ (⊢zeroᵘ ⊢Δ , U/Levelᵣ (λ { PE.refl → T.refl })))

opaque

  -- Validity of zero.

  zeroʳ : γ ▸ Γ ⊩ʳ zero ∷[ m ∣ n ] ℕ
  zeroʳ =
    ▸⊩ʳ∷⇔ .proj₂ λ _ _ →
    ®∷→®∷◂ $ ®∷ℕ⇔ .proj₂ $
    zeroᵣ (⇒*→⇛ (id (zeroⱼ ⊢Δ))) T.refl

opaque

  -- Validity of suc.

  sucʳ :
    ts » Γ ⊢ t ∷ ℕ →
    γ ▸ Γ ⊩ʳ t ∷[ m ∣ n ] ℕ →
    γ ▸ Γ ⊩ʳ suc t ∷[ m ∣ n ] ℕ
  sucʳ     {m = 𝟘ᵐ} _  _   = ▸⊩ʳ∷[𝟘ᵐ]
  sucʳ {t} {m = 𝟙ᵐ} ⊢t ⊩ʳt =
    ▸⊩ʳ∷⇔ .proj₂ λ {σ = σ} {σ′ = σ′} ⊢σ σ®σ′ →
    case
      (let open RR in
       suc (t [ σ ])  ∎⟨ sucⱼ (subst-⊢∷ ⊢t ⊢σ) ⟩⇒)
    of λ
      suc-t[σ]⇒*suc-t[σ] →

    case                                      $⟨ ▸⊩ʳ∷⇔ .proj₁ ⊩ʳt ⊢σ σ®σ′ ⟩
      t [ σ ] ® erase str t T.[ σ′ ] ∷ ℕ ◂ 𝟙  →⟨ ®∷→®∷◂ω non-trivial ⟩
      t [ σ ] ® erase str t T.[ σ′ ] ∷ ℕ      →⟨ ®∷ℕ⇔ .proj₁ ⟩
      t [ σ ] ® erase str t T.[ σ′ ] ∷ℕ       □
    of λ
      t[σ]®t[σ′] →

    ®∷→®∷◂ $ ®∷ℕ⇔ .proj₂ $
    case PE.singleton str of λ where
      (T.non-strict , PE.refl) →
        sucᵣ (⇒*→⇛ suc-t[σ]⇒*suc-t[σ]) T.refl _ t[σ]®t[σ′]
      (T.strict , PE.refl) →
        case reduces-to-numeral PE.refl t[σ]®t[σ′] of λ
          (v′ , v′-num , erase-t[σ′]⇒*v′) →
        sucᵣ (⇒*→⇛ suc-t[σ]⇒*suc-t[σ])
          (T.lam (T.suc (T.var x0)) T.∘⟨ T.strict ⟩
           erase T.strict t T.[ σ′ ]                    ⇒*⟨ TP.app-subst*-arg T.lam erase-t[σ′]⇒*v′ ⟩

           T.lam (T.suc (T.var x0)) T.∘⟨ T.strict ⟩ v′  ⇒⟨ T.β-red (TP.Numeral→Value v′-num) ⟩

           T.suc v′                                     ∎⇒)
          v′-num
          (                                         $⟨ t[σ]®t[σ′] ⟩
           t [ σ ] ® erase T.strict t T.[ σ′ ] ∷ℕ   ⇔˘⟨ ®∷ℕ⇔ ⟩→
           t [ σ ] ® erase T.strict t T.[ σ′ ] ∷ ℕ  →⟨ ®∷-⇒* erase-t[σ′]⇒*v′ ⟩
           t [ σ ] ® v′ ∷ ℕ                         ⇔⟨ ®∷ℕ⇔ ⟩→
           t [ σ ] ® v′ ∷ℕ                          □)

private opaque

  -- If t ® t′ ∷ℕ holds, then t is well-typed.

  ®∷ℕ→⊢∷ℕ : t ® t′ ∷ℕ → ts » Δ ⊢ t ∷ ℕ
  ®∷ℕ→⊢∷ℕ (zeroᵣ t⇒* _)    = wf-⇛ t⇒* .proj₁
  ®∷ℕ→⊢∷ℕ (sucᵣ t⇒* _ _ _) = wf-⇛ t⇒* .proj₁

opaque

  -- A lemma used to implement natrecʳ.

  natrecʳ′ :
    (∀ {v₁ v₂} →
     v₁ ⇛ v₂ ∷ ℕ →
     ts » Δ ⊢ A [ v₂ ]₀ ≡ A [ v₁ ]₀) →
    ts » Δ ∙ ℕ ⊢ A →
    ts » Δ ⊢ t ∷ A [ zero ]₀ →
    ts » Δ ∙ ℕ ∙ A ⊢ u ∷ A [ suc (var x1) ]↑² →
    t ® t′ ∷ A [ zero ]₀ →
    (∀ {v v′ w w′} →
     v ® v′ ∷ℕ →
     ts » Δ ⊢ w ∷ A [ v ]₀ →
     w ® w′ ∷ A [ v ]₀ →
     u [ v , w ]₁₀ ® u′ T.[ v′ , w′ ]₁₀ ∷ A [ suc v ]₀) →
    v ® v′ ∷ℕ →
    natrec p q r A t u v ® T.natrec t′ u′ v′ ∷ A [ v ]₀
  natrecʳ′
    {A} {t} {u} {t′} {u′} {v} {v′} {p} {q} {r}
    A≡A ⊢A ⊢t ⊢u t®t′ u®u′ = λ where
      (zeroᵣ v⇛zero v′⇒zero) →                                         $⟨ t®t′ ⟩
        t ® t′ ∷ A [ zero ]₀                                           →⟨ ®∷-⇐* (⇒*→⇛ (redMany (natrec-zero ⊢t ⊢u)))
                                                                            (T.trans T.natrec-zero T.refl) ⟩
        natrec p q r A t u zero ® T.natrec t′ u′ T.zero ∷ A [ zero ]₀  →⟨ conv-®∷ $ A≡A v⇛zero ⟩
        natrec p q r A t u zero ® T.natrec t′ u′ T.zero ∷ A [ v ]₀     →⟨ ®∷-⇐* (natrec-⇛ ⊢t ⊢u v⇛zero)
                                                                            (TP.natrec-subst* v′⇒zero) ⟩
        natrec p q r A t u v ® T.natrec t′ u′ v′ ∷ A [ v ]₀            □

      (sucᵣ {t′ = w} {v′ = w′} v⇛suc-w v′⇒suc-w′ _ w®w′) →        $⟨ natrecʳ′ A≡A ⊢A ⊢t ⊢u t®t′ u®u′ w®w′ ⟩

        natrec p q r A t u w ® T.natrec t′ u′ w′ ∷ A [ w ]₀       →⟨ u®u′ w®w′ $
                                                                     natrecⱼ ⊢t ⊢u (®∷ℕ→⊢∷ℕ w®w′) ⟩
        u [ w , natrec p q r A t u w ]₁₀ ®
          u′ T.[ w′ , T.natrec t′ u′ w′ ]₁₀ ∷ A [ suc w ]₀        →⟨ ®∷-⇐*
                                                                       (⇒*→⇛ $ redMany $ natrec-suc ⊢t ⊢u $
                                                                        inversion-suc (wf-⇛ v⇛suc-w .proj₂) .proj₁)
                                                                       (T.trans T.natrec-suc T.refl) ⟩
        natrec p q r A t u (suc w) ® T.natrec t′ u′ (T.suc w′) ∷
          A [ suc w ]₀                                            →⟨ conv-®∷ $ A≡A v⇛suc-w ⟩
        natrec p q r A t u (suc w) ® T.natrec t′ u′ (T.suc w′) ∷
          A [ v ]₀                                                →⟨ ®∷-⇐* (natrec-⇛ ⊢t ⊢u v⇛suc-w)
                                                                       (TP.natrec-subst* v′⇒suc-w′) ⟩
        natrec p q r A t u v ® T.natrec t′ u′ v′ ∷ A [ v ]₀       □

opaque

  -- Validity of natrec.

  natrecʳ :
    ts » Γ ⊢ t ∷ A [ zero ]₀ →
    ts » Γ ∙ ℕ ∙ A ⊢ u ∷ A [ suc (var x1) ]↑² →
    ts » Γ ⊢ v ∷ ℕ →
    γ ▸ Γ ⊩ʳ t ∷[ m ∣ n ] A [ zero ]₀ →
    δ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸ Γ ∙ ℕ ∙ A ⊩ʳ u ∷[ m ∣ n ]
      A [ suc (var x1) ]↑² →
    η ▸ Γ ⊩ʳ v ∷[ m ∣ n ] ℕ →
    (∀ x → χ ⟨ x ⟩ PE.≡ 𝟘 →
     γ ⟨ x ⟩ PE.≡ 𝟘 × η ⟨ x ⟩ PE.≡ 𝟘 × δ ⟨ x ⟩ PE.≡ 𝟘) →
    χ ▸ Γ ⊩ʳ natrec p q r A t u v ∷[ m ∣ n ] A [ v ]₀
  natrecʳ {m = 𝟘ᵐ} _ _ _ _ _ _ _ =
    ▸⊩ʳ∷[𝟘ᵐ]
  natrecʳ
    {Γ} {t} {A} {u} {v} {γ} {m = 𝟙ᵐ} {n} {δ} {p} {r} {η} {χ} {q}
    ⊢t ⊢u ⊢v ⊩ʳt ⊩ʳu ⊩ʳv ≡𝟘→≡𝟘 =
    ▸⊩ʳ∷⇔ .proj₂ λ {σ = σ} {σ′ = σ′} ⊢σ σ®σ′ →
    case wfTerm ⊢u of λ {
      (∙ ⊢A) →
    case                                                      $⟨ σ®σ′ ⟩
      σ ® σ′ ∷[ 𝟙ᵐ ∣ n ] Γ ◂ χ                                →⟨ subsumption-®∷[∣]◂ (λ x → proj₁ ∘→ ≡𝟘→≡𝟘 x) ⟩
      σ ® σ′ ∷[ 𝟙ᵐ ∣ n ] Γ ◂ γ                                →⟨ ▸⊩ʳ∷⇔ .proj₁ ⊩ʳt ⊢σ ⟩
      t [ σ ] ® erase str t T.[ σ′ ] ∷ A [ zero ]₀ [ σ ] ◂ 𝟙  →⟨ ®∷→®∷◂ω non-trivial ⟩
      t [ σ ] ® erase str t T.[ σ′ ] ∷ A [ zero ]₀ [ σ ]      ≡⟨ PE.cong (_®_∷_ _ _) (singleSubstLift A _) ⟩→
      t [ σ ] ® erase str t T.[ σ′ ] ∷ A [ σ ⇑ ] [ zero ]₀    □
    of λ
      t[σ]®t[σ′] →

    case
      (λ {v = v} {v′ = v′} {w = w} {w′ = w′}
         (v®v′ : v ® v′ ∷ℕ)
         (⊢w : ts » Δ ⊢ w ∷ A [ σ ⇑ ] [ v ]₀)
         (w®w′ : w ® w′ ∷ A [ σ ⇑ ] [ v ]₀) →
                                                                       $⟨ σ®σ′ ⟩

         σ ® σ′ ∷[ 𝟙ᵐ ∣ n ] Γ ◂ χ                                      →⟨ subsumption-®∷[∣]◂ (λ x → proj₂ ∘→ proj₂ ∘→ ≡𝟘→≡𝟘 x) ⟩

         σ ® σ′ ∷[ 𝟙ᵐ ∣ n ] Γ ◂ δ                                      →⟨ (λ σ®σ′ →
                                                                             ®∷[∣]∙◂∙⇔ .proj₂
                                                                               ( ®∷→®∷◂ (PE.subst (_®_∷_ _ _) (singleSubstComp _ _ A) w®w′)
                                                                               , ®∷[∣]∙◂∙⇔ .proj₂ (®∷→®∷◂ (®∷ℕ⇔ .proj₂ v®v′) , σ®σ′)
                                                                               )) ⟩
         consSubst (consSubst σ v) w ®
           T.consSubst (T.consSubst σ′ v′) w′ ∷[ 𝟙ᵐ ∣ n ] Γ ∙ ℕ ∙ A ◂
           δ ∙ 𝟙 · p ∙ 𝟙 · r                                           →⟨ ▸⊩ʳ∷⇔ .proj₁ ⊩ʳu $
                                                                          →⊢ˢʷ∷∙ (→⊢ˢʷ∷∙ ⊢σ (®∷ℕ→⊢∷ℕ v®v′))
                                                                          (PE.subst (_⊢_∷_ _ _) (singleSubstComp _ _ A) ⊢w) ⟩
         u [ consSubst (consSubst σ v) w ] ®
           erase str u T.[ T.consSubst (T.consSubst σ′ v′) w′ ] ∷
           A [ suc (var x1) ]↑² [ consSubst (consSubst σ v) w ] ◂ 𝟙    ≡⟨ PE.cong₄ _®_∷_◂_ (PE.sym $ doubleSubstComp u _ _ _)
                                                                            (PE.sym $ TP.doubleSubstComp (erase _ u) _ _ _)
                                                                            (
           A [ suc (var x1) ]↑² [ consSubst (consSubst σ v) w ]              ≡˘⟨ substComp↑² A _ ⟩
           A [ consSubst σ (suc v) ]                                         ≡˘⟨ singleSubstComp _ _ A ⟩
           A [ σ ⇑ ] [ suc v ]₀                                              ∎)
                                                                            PE.refl ⟩→
         u [ σ ⇑ ⇑ ] [ v , w ]₁₀ ®
           erase str u T.[ σ′ T.⇑ T.⇑ ] T.[ v′ , w′ ]₁₀ ∷
           A [ σ ⇑ ] [ suc v ]₀ ◂ 𝟙                                    →⟨ ®∷→®∷◂ω non-trivial ⟩

         u [ σ ⇑ ⇑ ] [ v , w ]₁₀ ®
           erase str u T.[ σ′ T.⇑ T.⇑ ] T.[ v′ , w′ ]₁₀ ∷
           A [ σ ⇑ ] [ suc v ]₀                                        □)
    of λ
      u[σ⇑⇑]®u[σ′⇑⇑] →                                             $⟨ σ®σ′ ⟩

    σ ® σ′ ∷[ 𝟙ᵐ ∣ n ] Γ ◂ χ                                       →⟨ subsumption-®∷[∣]◂ (λ x → proj₁ ∘→ proj₂ ∘→ ≡𝟘→≡𝟘 x) ⟩

    σ ® σ′ ∷[ 𝟙ᵐ ∣ n ] Γ ◂ η                                       →⟨ ▸⊩ʳ∷⇔ .proj₁ ⊩ʳv ⊢σ ⟩

    v [ σ ] ® erase str v T.[ σ′ ] ∷ ℕ ◂ 𝟙                         →⟨ ®∷ℕ⇔ .proj₁ ∘→ ®∷→®∷◂ω non-trivial ⟩

    v [ σ ] ® erase str v T.[ σ′ ] ∷ℕ                              →⟨ natrecʳ′
                                                                       (substTypeEq (refl (subst-⊢-⇑ ⊢A ⊢σ)) ∘→ sym′ ∘→ ⇛→⊢≡)
                                                                       (subst-⊢-⇑ ⊢A ⊢σ)
                                                                       (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) (subst-⊢∷ ⊢t ⊢σ))
                                                                       (PE.subst (_⊢_∷_ _ _) (natrecSucCase _ A) (subst-⊢∷-⇑ ⊢u ⊢σ))
                                                                       t[σ]®t[σ′] u[σ⇑⇑]®u[σ′⇑⇑] ⟩
    (natrec p q r (A [ σ ⇑ ]) (t [ σ ]) (u [ σ ⇑ ⇑ ]) (v [ σ ]) ®
       T.natrec (erase str t T.[ σ′ ])
         (erase str u T.[ σ′ T.⇑ T.⇑ ]) (erase str v T.[ σ′ ]) ∷
       A [ σ ⇑ ] [ v [ σ ] ]₀)                                     →⟨ ®∷→®∷◂ ∘→
                                                                      PE.subst (_®_∷_ _ _) (PE.sym $ singleSubstLift A _) ⟩
    natrec p q r (A [ σ ⇑ ]) (t [ σ ]) (u [ σ ⇑ ⇑ ]) (v [ σ ]) ®
      T.natrec (erase str t T.[ σ′ ])
        (erase str u T.[ σ′ T.⇑ T.⇑ ]) (erase str v T.[ σ′ ]) ∷
      A [ v ]₀ [ σ ] ◂ 𝟙                                           □ }
    where
    open Tools.Reasoning.PropositionalEquality
