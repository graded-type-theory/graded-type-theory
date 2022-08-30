open import Tools.PropositionalEquality as PE using (_≈_)
open import Tools.Relation

module Definition.Typed.Decidable
  {a} {M : Set a} (_≟_ : Decidable (_≈_ {A = M})) where

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed M
open import Definition.Conversion.Decidable _≟_
open import Definition.Conversion.Soundness M
open import Definition.Conversion.Consequences.Completeness M

open import Tools.Level
open import Tools.Nat
open import Tools.Nullary
open import Tools.Product
open import Tools.Unit

private
  variable
    n : Nat
    Γ : Con Term n
    A t : Term n

-- Re-export decidability of type and term equality
open import Definition.Typed.Decidable.Equality M″ public

NfCon : (Γ : Con Term n) → Set a
NfCon ε = Lift a ⊤
NfCon (Γ ∙ A) = Nf A × NfCon Γ

mutual

  decWfCon : NfCon Γ → Dec (⊢ Γ)
  decWfCon {Γ = ε} (lift tt) = yes ε
  decWfCon {Γ = Γ ∙ A} (NfA , NfΓ) with dec NfΓ NfA | decWfCon NfΓ
  ... | yes ⊢A | yes ⊢Γ = yes (⊢Γ ∙ ⊢A)
  ... | yes ⊢A | no ⊬Γ = no (λ { (x ∙ x₁) → ⊬Γ x})
  ... | no ⊬A | _ = no λ { (x ∙ x₁) → ⊬A x₁}

  dec : NfCon Γ → Nf A → Dec (Γ ⊢ A)
  dec Γ A with decWfCon Γ
  ... | yes ⊢Γ = map (soundness⇇Type ⊢Γ) (completeness⇇Type A) (dec⇇Type ⊢Γ A)
  ... | no ⊬Γ = no (λ x → ⊬Γ (wf x))


decNfTerm : NfCon Γ → Nf t → Nf A → Dec (Γ ⊢ t ∷ A)
decNfTerm Γ t A with dec Γ A
... | yes ⊢A = map (soundness⇇ (wf ⊢A) ⊢A) (completeness⇇ t) (dec⇇ (wf ⊢A) t ⊢A)
... | no ⊬A = no λ {x → ⊬A (syntacticTerm x)}

decNeTerm : NfCon Γ → NfNeutral t → Dec (∃ λ A → Γ ⊢ t ∷ A)
decNeTerm Γ t with decWfCon Γ
... | yes ⊢Γ = map (λ { (A , t⇉A) → A , proj₂ (soundness⇉ ⊢Γ t⇉A)})
                   (λ { (A , ⊢t) → _ , proj₁ (proj₂ (completeness⇉ t ⊢t))})
                   (dec⇉ ⊢Γ t)
... | no ⊬Γ = no (λ { (_ , ⊢t) → ⊬Γ (wfTerm ⊢t)})


mutual

  decNf : (t : Term n) → Dec (Nf t)
  decNf (var x) = yes (ne (var x))
  decNf (gen Ukind []) = yes Uₙ
  decNf (gen (Pikind p q) (F ∺ G ∺ [])) with decNf F | decNf G
  ... | yes F′ | yes G′ = yes (Πₙ F′ G′)
  ... | yes F′ | no ¬G′ = no λ { (Πₙ x x₁) → ¬G′ x₁}
  ... | no ¬F′ | _      = no λ { (Πₙ x x₁) → ¬F′ x}
  decNf (gen (Lamkind p) (t ∺ [])) with decNf t
  ... | yes t′ = yes (lamₙ t′)
  ... | no ¬t′ = no λ { (lamₙ x) → ¬t′ x}
  decNf (gen (Sigmakind q x) (F ∺ G ∺ [])) with decNf F | decNf G
  ... | yes F′ | yes G′ = yes (Σₙ F′ G′)
  ... | yes F′ | no ¬G′ = no λ { (Σₙ x x₁) → ¬G′ x₁}
  ... | no ¬F′ | _      = no λ { (Σₙ x x₁) → ¬F′ x}
  decNf (gen Prodkind (t ∺ u ∺ [])) with decNf t | decNf u
  ... | yes t′ | yes u′ = yes (prodₙ t′ u′)
  ... | yes t′ | no ¬u′ = no λ { (prodₙ x x₁) → ¬u′ x₁}
  ... | no t′ | _       = no λ { (prodₙ x x₁) → t′ x}
  decNf (gen Natkind []) = yes ℕₙ
  decNf (gen Zerokind []) = yes zeroₙ
  decNf (gen Suckind (t ∺ [])) with decNf t
  ... | yes t′ = yes (sucₙ t′)
  ... | no ¬t′ = no λ { (sucₙ x) → ¬t′ x}
  decNf (gen Unitkind []) = yes Unitₙ
  decNf (gen Starkind []) = yes starₙ
  decNf (gen Emptykind []) = yes Emptyₙ
  decNf T@(gen (Appkind p) (t ∺ u ∺ [])) with decNfNeutral T
  ... | yes x = yes (ne x)
  ... | no ¬x = no (λ { (ne x) → ¬x x})
  decNf T@(gen Fstkind (t ∺ [])) with decNfNeutral T
  ... | yes x = yes (ne x)
  ... | no ¬x = no (λ { (ne x) → ¬x x})
  decNf T@(gen Sndkind (t ∺ [])) with decNfNeutral T
  ... | yes x = yes (ne x)
  ... | no ¬x = no (λ { (ne x) → ¬x x})
  decNf T@(gen (Prodreckind p) (A ∺ t ∺ u ∺ [])) with decNfNeutral T
  ... | yes x = yes (ne x)
  ... | no ¬x = no (λ { (ne x) → ¬x x})
  decNf T@(gen (Natreckind p q) (A ∺ z ∺ s ∺ n ∺ [])) with decNfNeutral T
  ... | yes x = yes (ne x)
  ... | no ¬x = no (λ { (ne x) → ¬x x})
  decNf T@(gen (Emptyreckind p) (A ∺ t ∺ [])) with decNfNeutral T
  ... | yes x = yes (ne x)
  ... | no ¬x = no (λ { (ne x) → ¬x x})

  decNfNeutral : (t : Term n) → Dec (NfNeutral t)
  decNfNeutral (var x) = yes (var x)
  decNfNeutral (gen Ukind []) = no λ {()}
  decNfNeutral (gen (Pikind p q) (F ∺ G ∺ [])) = no λ {()}
  decNfNeutral (gen (Lamkind p) (t ∺ [])) = no λ {()}
  decNfNeutral (gen (Appkind p) (t ∺ u ∺ [])) with decNfNeutral t | decNf u
  ... | yes t′ | yes u′ = yes (∘ₙ t′ u′)
  ... | yes t′ | no ¬u′ = no (λ { (∘ₙ x x₁) → ¬u′ x₁})
  ... | no ¬t′ | _ = no (λ { (∘ₙ x x₁) → ¬t′ x})
  decNfNeutral (gen (Sigmakind q x) (F ∺ G ∺ [])) = no λ {()}
  decNfNeutral (gen Prodkind (t ∺ u ∺ [])) = no λ {()}
  decNfNeutral (gen Fstkind (t ∺ [])) with decNfNeutral t
  ... | yes t′ = yes (fstₙ t′)
  ... | no ¬t′ = no (λ { (fstₙ x) → ¬t′ x})
  decNfNeutral (gen Sndkind (t ∺ [])) with decNfNeutral t
  ... | yes t′ = yes (sndₙ t′)
  ... | no ¬t′ = no (λ { (sndₙ x) → ¬t′ x})
  decNfNeutral (gen (Prodreckind p) (A ∺ t ∺ u ∺ []))
    with decNf A | decNfNeutral t | decNf u
  ... | yes A′ | yes t′ | yes u′ = yes (prodrecₙ A′ t′ u′)
  ... | yes A′ | yes t′ | no ¬u′  = no λ { (prodrecₙ x x₁ x₂) → ¬u′ x₂}
  ... | yes A′ | no ¬t′ | _       = no λ { (prodrecₙ x x₁ x₂) → ¬t′ x₁}
  ... | no ¬A′ | _ | _            = no λ { (prodrecₙ x x₁ x₂) → ¬A′ x}
  decNfNeutral (gen Natkind []) = no λ {()}
  decNfNeutral (gen Zerokind []) = no λ {()}
  decNfNeutral (gen Suckind (t ∺ [])) = no λ {()}
  decNfNeutral (gen (Natreckind p q) (A ∺ z ∺ s ∺ n ∺ []))
    with decNf A | decNf z | decNf s | decNfNeutral n
  ... | yes A′ | yes z′ | yes s′ | yes n′ = yes (natrecₙ A′ z′ s′ n′)
  ... | yes A′ | yes z′ | yes s′ | no ¬n′ = no λ { (natrecₙ x x₁ x₂ x₃) → ¬n′ x₃}
  ... | yes A′ | yes z′ | no ¬s′ | _      = no λ { (natrecₙ x x₁ x₂ x₃) → ¬s′ x₂}
  ... | yes A′ | no ¬z′ | _ | _           = no λ { (natrecₙ x x₁ x₂ x₃) → ¬z′ x₁}
  ... | no ¬A′ | _ | _ | _                = no λ { (natrecₙ x x₁ x₂ x₃) → ¬A′ x}
  decNfNeutral (gen Unitkind []) = no λ {()}
  decNfNeutral (gen Starkind []) = no λ {()}
  decNfNeutral (gen Emptykind []) = no λ {()}
  decNfNeutral (gen (Emptyreckind p) (A ∺ t ∺ []))
    with decNf A | decNfNeutral t
  ... | yes A′ | yes t′ = yes (Emptyrecₙ A′ t′)
  ... | yes A′ | no ¬t′ = no λ { (Emptyrecₙ x x₁) → ¬t′ x₁}
  ... | no ¬A′ | _      = no λ { (Emptyrecₙ x x₁) → ¬A′ x}
