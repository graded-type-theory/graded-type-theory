------------------------------------------------------------------------
-- Properties of the typing and reduction relations
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Typed.Properties.Well-formed R public

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed R

import Graded.Derived.Erased.Typed.Primitive R as Erased

open import Tools.Empty using (⊥; ⊥-elim)
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    A A′ B B′ C U′ : Term n
    a b t u u′ v : Term n
    p p′ q : M


-- Reduction is a subset of conversion

subsetTerm : Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ≡ u ∷ A
subsetTerm (natrec-subst F z s n⇒n′) =
  natrec-cong F (refl F) (refl z) (refl s) (subsetTerm n⇒n′)
subsetTerm (natrec-zero F z s) = natrec-zero F z s
subsetTerm (natrec-suc F z s n) = natrec-suc F z s n
subsetTerm (emptyrec-subst A n⇒n′) =
  emptyrec-cong (refl A) (subsetTerm n⇒n′)
subsetTerm (app-subst t⇒u a) =
  app-cong (subsetTerm t⇒u) (refl a)
subsetTerm (β-red A B t a p≡p′ ok) = β-red A B t a p≡p′ ok
subsetTerm (conv t⇒u A≡B) = conv (subsetTerm t⇒u) A≡B
subsetTerm (fst-subst F G x) = fst-cong F G (subsetTerm x)
subsetTerm (snd-subst F G x) = snd-cong F G (subsetTerm x)
subsetTerm (prodrec-subst F G A u t⇒t′ ok) =
  prodrec-cong F G (refl A) (subsetTerm t⇒t′) (refl u) ok
subsetTerm (prodrec-β F G A t t′ u eq ok) =
  prodrec-β F G A t t′ u eq ok
subsetTerm (Σ-β₁ F G x x₁ x₂ ok) = Σ-β₁ F G x x₁ x₂ ok
subsetTerm (Σ-β₂ F G x x₁ x₂ ok) = Σ-β₂ F G x x₁ x₂ ok
subsetTerm (J-subst ⊢A ⊢t ⊢B ⊢u ⊢t′ v⇒v′) =
  J-cong ⊢A (refl ⊢A) ⊢t (refl ⊢t) (refl ⊢B) (refl ⊢u) (refl ⊢t′)
    (subsetTerm v⇒v′)
subsetTerm (K-subst ⊢A ⊢t ⊢B ⊢u v⇒v′ ok) =
  K-cong (refl ⊢A) ⊢t (refl ⊢t) (refl ⊢B) (refl ⊢u)
    (subsetTerm v⇒v′) ok
subsetTerm ([]-cong-subst ⊢A ⊢t ⊢u v⇒v′ ok) =
  []-cong-cong (refl ⊢A) (refl ⊢t) (refl ⊢u) (subsetTerm v⇒v′) ok
subsetTerm (J-β ⊢A ⊢t _ t≡t′ ⊢B _ ⊢u) =
  trans (sym (J-cong ⊢A (refl ⊢A) ⊢t (refl ⊢t) (refl ⊢B) (refl ⊢u)
                t≡t′ (refl (rflⱼ ⊢t))))
    (J-β ⊢A ⊢t ⊢B ⊢u PE.refl)
subsetTerm (K-β ⊢t ⊢B ⊢u ok) = K-β ⊢t ⊢B ⊢u ok
subsetTerm ([]-cong-β ⊢A ⊢t _ t≡t′ ok) =
  trans
    ([]-cong-cong (refl ⊢A) (refl ⊢t)
       (sym t≡t′)
       (conv (refl (rflⱼ ⊢t)) (Id-cong (refl ⊢A) (refl ⊢t) t≡t′))
       ok)
    (conv ([]-cong-β ⊢t PE.refl ok)
       (Id-cong (refl (Erasedⱼ ⊢A)) (refl ([]ⱼ ⊢A ⊢t))
          ([]-cong′ ⊢A t≡t′)))
  where
  open Erased ([]-cong→Erased ok)
subsetTerm (unitrec-subst A u t⇒t′ ok) =
  unitrec-cong (refl A) (subsetTerm t⇒t′) (refl u) ok
subsetTerm (unitrec-β A u ok) = unitrec-β A u ok

subset : Γ ⊢ A ⇒ B → Γ ⊢ A ≡ B
subset (univ A⇒B) = univ (subsetTerm A⇒B)

subset*Term : Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t ≡ u ∷ A
subset*Term (id t) = refl t
subset*Term (t⇒t′ ⇨ t⇒*u) = trans (subsetTerm t⇒t′) (subset*Term t⇒*u)

subset* : Γ ⊢ A ⇒* B → Γ ⊢ A ≡ B
subset* (id A) = refl A
subset* (A⇒A′ ⇨ A′⇒*B) = trans (subset A⇒A′) (subset* A′⇒*B)


-- Can extract left-part of a reduction

redFirstTerm :{Γ : Con Term n} → Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ∷ A
redFirstTerm (conv t⇒u A≡B) = conv (redFirstTerm t⇒u) A≡B
redFirstTerm (app-subst t⇒u a) = (redFirstTerm t⇒u) ∘ⱼ a
redFirstTerm (β-red A B t a PE.refl ok) =
  conv (lamⱼ A t ok) (ΠΣ-cong A (refl A) (refl B) ok) ∘ⱼ a
redFirstTerm (natrec-subst F z s n⇒n′) = natrecⱼ F z s (redFirstTerm n⇒n′)
redFirstTerm (natrec-zero F z s) = natrecⱼ F z s (zeroⱼ (wfTerm z))
redFirstTerm (natrec-suc F z s n) = natrecⱼ F z s (sucⱼ n)
redFirstTerm (emptyrec-subst A n⇒n′) = emptyrecⱼ A (redFirstTerm n⇒n′)
redFirstTerm (fst-subst F G x) = fstⱼ F G (redFirstTerm x)
redFirstTerm (snd-subst F G x) = sndⱼ F G (redFirstTerm x)
redFirstTerm (prodrec-subst F G A u t⇒t′ ok) =
  prodrecⱼ F G A (redFirstTerm t⇒t′) u ok
redFirstTerm (prodrec-β F G A t t′ u PE.refl ok) =
  prodrecⱼ F G A
    (conv (prodⱼ F G t t′ ok) (ΠΣ-cong F (refl F) (refl G) ok))
    u ok
redFirstTerm (Σ-β₁ F G x x₁ PE.refl ok) =
  fstⱼ F G
    (conv (prodⱼ F G x x₁ ok) (ΠΣ-cong F (refl F) (refl G) ok))
redFirstTerm (Σ-β₂ F G x x₁ PE.refl ok) =
  sndⱼ F G
    (conv (prodⱼ F G x x₁ ok) (ΠΣ-cong F (refl F) (refl G) ok))
redFirstTerm (J-subst ⊢A ⊢t ⊢B ⊢u ⊢t′ v⇒v′) =
  Jⱼ ⊢A ⊢t ⊢B ⊢u ⊢t′ (redFirstTerm v⇒v′)
redFirstTerm (K-subst _ ⊢t ⊢B ⊢u v⇒v′ ok) =
  Kⱼ ⊢t ⊢B ⊢u (redFirstTerm v⇒v′) ok
redFirstTerm ([]-cong-subst _ ⊢t ⊢u v⇒v′ ok) =
  []-congⱼ ⊢t ⊢u (redFirstTerm v⇒v′) ok
redFirstTerm (J-β ⊢A ⊢t ⊢t′ t≡t′ ⊢B B≡B ⊢u) =
  conv (Jⱼ ⊢A ⊢t ⊢B ⊢u ⊢t′
          (conv (rflⱼ ⊢t) (Id-cong (refl ⊢A) (refl ⊢t) t≡t′)))
    (sym B≡B)
redFirstTerm (K-β ⊢t ⊢B ⊢u ok) =
  Kⱼ ⊢t ⊢B ⊢u (rflⱼ ⊢t) ok
redFirstTerm ([]-cong-β ⊢A ⊢t ⊢t′ t≡t′ ok) =
  []-congⱼ ⊢t ⊢t′ (conv (rflⱼ ⊢t) (Id-cong (refl ⊢A) (refl ⊢t) t≡t′)) ok
redFirstTerm (unitrec-subst A u t⇒t′ ok) =
  unitrecⱼ A (redFirstTerm t⇒t′) u ok
redFirstTerm (unitrec-β A u ok) =
  unitrecⱼ A (starⱼ (wfTerm u) ok) u ok

redFirst :{Γ : Con Term n} → Γ ⊢ A ⇒ B → Γ ⊢ A
redFirst (univ A⇒B) = univ (redFirstTerm A⇒B)

redFirst*Term : {Γ : Con Term n} → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t ∷ A
redFirst*Term (id t) = t
redFirst*Term (t⇒t′ ⇨ t′⇒*u) = redFirstTerm t⇒t′

redFirst* : {Γ : Con Term n} → Γ ⊢ A ⇒* B → Γ ⊢ A
redFirst* (id A) = A
redFirst* (A⇒A′ ⇨ A′⇒*B) = redFirst A⇒A′

-- No neutral terms are well-formed in an empty context

noNe : ε ⊢ t ∷ A → Neutral t → ⊥
noNe (conv ⊢t x) n = noNe ⊢t n
noNe (var x₁ ()) (var x)
noNe (⊢t ∘ⱼ ⊢t₁) (∘ₙ neT) = noNe ⊢t neT
noNe (fstⱼ _ _ ⊢t) (fstₙ neT) = noNe ⊢t neT
noNe (sndⱼ _ _ ⊢t) (sndₙ neT) = noNe ⊢t neT
noNe (natrecⱼ x ⊢t ⊢t₁ ⊢t₂) (natrecₙ neT) = noNe ⊢t₂ neT
noNe (prodrecⱼ _ _ _ ⊢t _ _) (prodrecₙ neT) = noNe ⊢t neT
noNe (emptyrecⱼ A ⊢e) (emptyrecₙ neT) = noNe ⊢e neT
noNe (unitrecⱼ _ ⊢t _ _) (unitrecₙ neT) = noNe ⊢t neT
noNe (Jⱼ _ _ _ _ _ ⊢w) (Jₙ n) = noNe ⊢w n
noNe (Kⱼ _ _ _ ⊢v _) (Kₙ n) = noNe ⊢v n
noNe ([]-congⱼ _ _ ⊢v _) ([]-congₙ n) = noNe ⊢v n

-- Neutrals do not weak head reduce

neRedTerm : (d : Γ ⊢ t ⇒ u ∷ A) (n : Neutral t) → ⊥
neRedTerm (conv d x) n = neRedTerm d n
neRedTerm (app-subst d x) (∘ₙ n) = neRedTerm d n
neRedTerm (β-red _ _ _ _ _ _) (∘ₙ ())
neRedTerm (natrec-subst x x₁ x₂ d) (natrecₙ n₁) = neRedTerm d n₁
neRedTerm (natrec-zero x x₁ x₂) (natrecₙ ())
neRedTerm (natrec-suc x x₁ x₂ x₃) (natrecₙ ())
neRedTerm (emptyrec-subst x d) (emptyrecₙ n₁) = neRedTerm d n₁
neRedTerm (fst-subst _ _ d) (fstₙ n) = neRedTerm d n
neRedTerm (snd-subst _ _ d) (sndₙ n) = neRedTerm d n
neRedTerm (prodrec-subst _ _ _ _ d _) (prodrecₙ n) = neRedTerm d n
neRedTerm (prodrec-β _ _ _ _ _ _ _ _) (prodrecₙ ())
neRedTerm (Σ-β₁ _ _ _ _ _ _) (fstₙ ())
neRedTerm (Σ-β₂ _ _ _ _ _ _) (sndₙ ())
neRedTerm (J-subst _ _ _ _ _ w⇒w′) (Jₙ n) = neRedTerm w⇒w′ n
neRedTerm (K-subst _ _ _ _ v⇒v′ _) (Kₙ n) = neRedTerm v⇒v′ n
neRedTerm ([]-cong-subst _ _ _ v⇒v′ _) ([]-congₙ n) = neRedTerm v⇒v′ n
neRedTerm (J-β _ _ _ _ _ _ _) (Jₙ ())
neRedTerm (K-β _ _ _ _) (Kₙ ())
neRedTerm ([]-cong-β _ _ _ _ _) ([]-congₙ ())
neRedTerm (unitrec-subst _ _ d _) (unitrecₙ n) = neRedTerm d n
neRedTerm (unitrec-β _ _ _) (unitrecₙ ())


neRed : (d : Γ ⊢ A ⇒ B) (N : Neutral A) → ⊥
neRed (univ x) N = neRedTerm x N

-- Whnfs do not weak head reduce

whnfRedTerm : (d : Γ ⊢ t ⇒ u ∷ A) (w : Whnf t) → ⊥
whnfRedTerm (conv d x) w = whnfRedTerm d w
whnfRedTerm (app-subst d x) (ne (∘ₙ x₁)) = neRedTerm d x₁
whnfRedTerm (β-red _ _ _ _ _ _) (ne (∘ₙ ()))
whnfRedTerm (natrec-subst x x₁ x₂ d) (ne (natrecₙ x₃)) = neRedTerm d x₃
whnfRedTerm (natrec-zero x x₁ x₂) (ne (natrecₙ ()))
whnfRedTerm (natrec-suc x x₁ x₂ x₃) (ne (natrecₙ ()))
whnfRedTerm (emptyrec-subst x d) (ne (emptyrecₙ x₂)) = neRedTerm d x₂
whnfRedTerm (fst-subst _ _ d) (ne (fstₙ n)) = neRedTerm d n
whnfRedTerm (snd-subst _ _ d) (ne (sndₙ n)) = neRedTerm d n
whnfRedTerm (prodrec-subst _ _ _ _ d _) (ne (prodrecₙ n)) =
  neRedTerm d n
whnfRedTerm (prodrec-β _ _ _ _ _ _ _ _) (ne (prodrecₙ ()))
whnfRedTerm (Σ-β₁ _ _ _ _ _ _) (ne (fstₙ ()))
whnfRedTerm (Σ-β₂ _ _ _ _ _ _) (ne (sndₙ ()))
whnfRedTerm (J-subst _ _ _ _ _ w⇒w′) (ne (Jₙ n)) = neRedTerm w⇒w′ n
whnfRedTerm (K-subst _ _ _ _ v⇒v′ _) (ne (Kₙ n)) = neRedTerm v⇒v′ n
whnfRedTerm ([]-cong-subst _ _ _ v⇒v′ _) (ne ([]-congₙ n)) =
  neRedTerm v⇒v′ n
whnfRedTerm (J-β _ _ _ _ _ _ _) (ne (Jₙ ()))
whnfRedTerm (K-β _ _ _ _) (ne (Kₙ ()))
whnfRedTerm ([]-cong-β _ _ _ _ _) (ne ([]-congₙ ()))
whnfRedTerm (unitrec-subst _ _ d _) (ne (unitrecₙ n)) = neRedTerm d n
whnfRedTerm (unitrec-β x x₁ x₂) (ne (unitrecₙ ()))

whnfRed : (d : Γ ⊢ A ⇒ B) (w : Whnf A) → ⊥
whnfRed (univ x) w = whnfRedTerm x w

whnfRed*Term : (d : Γ ⊢ t ⇒* u ∷ A) (w : Whnf t) → t PE.≡ u
whnfRed*Term (id x) _ = PE.refl
whnfRed*Term (conv x x₁ ⇨ d) w = ⊥-elim (whnfRedTerm x w)
whnfRed*Term (x ⇨ d) (ne x₁) = ⊥-elim (neRedTerm x x₁)

whnfRed* : (d : Γ ⊢ A ⇒* B) (w : Whnf A) → A PE.≡ B
whnfRed* (id x) w = PE.refl
whnfRed* (x ⇨ d) w = ⊥-elim (whnfRed x w)

-- Whr is deterministic

whrDetTerm : (d : Γ ⊢ t ⇒ u ∷ A) (d′ : Γ ⊢ t ⇒ u′ ∷ A′) → u PE.≡ u′
whrDetTerm (conv d x) d′ = whrDetTerm d d′
whrDetTerm d (conv d′ x₁) = whrDetTerm d d′
whrDetTerm (app-subst d x) (app-subst d′ x₁) rewrite whrDetTerm d d′ = PE.refl
whrDetTerm (β-red _ _ _ _ _ _) (β-red _ _ _ _ _ _) = PE.refl
whrDetTerm (fst-subst _ _ x) (fst-subst _ _ y) rewrite whrDetTerm x y = PE.refl
whrDetTerm (snd-subst _ _ x) (snd-subst _ _ y) rewrite whrDetTerm x y = PE.refl
whrDetTerm (Σ-β₁ _ _ _ _ _ _) (Σ-β₁ _ _ _ _ _ _) = PE.refl
whrDetTerm (Σ-β₂ _ _ _ _ _ _) (Σ-β₂ _ _ _ _ _ _) = PE.refl
whrDetTerm (natrec-subst x x₁ x₂ d) (natrec-subst x₃ x₄ x₅ d′) rewrite whrDetTerm d d′ = PE.refl
whrDetTerm (natrec-zero x x₁ x₂) (natrec-zero x₃ x₄ x₅) = PE.refl
whrDetTerm (natrec-suc x x₁ x₂ x₃) (natrec-suc x₄ x₅ x₆ x₇) = PE.refl
whrDetTerm (prodrec-subst _ _ _ _ d _) (prodrec-subst _ _ _ _ d′ _)
  rewrite whrDetTerm d d′ = PE.refl
whrDetTerm (prodrec-β _ _ _ _ _ _ _ _) (prodrec-β _ _ _ _ _ _ _ _) =
  PE.refl
whrDetTerm (emptyrec-subst x d) (emptyrec-subst x₂ d′) rewrite whrDetTerm d d′ = PE.refl
whrDetTerm (J-subst _ _ _ _ _ w⇒w₁) (J-subst _ _ _ _ _ w⇒w₂)
  rewrite whrDetTerm w⇒w₁ w⇒w₂ = PE.refl
whrDetTerm (K-subst _ _ _ _ v⇒v₁ _) (K-subst _ _ _ _ v⇒v₂ _)
  rewrite whrDetTerm v⇒v₁ v⇒v₂ = PE.refl
whrDetTerm ([]-cong-subst _ _ _ v⇒v₁ _) ([]-cong-subst _ _ _ v⇒v₂ _)
  rewrite whrDetTerm v⇒v₁ v⇒v₂ = PE.refl
whrDetTerm (J-β _ _ _ _ _ _ _) (J-β _ _ _ _ _ _ _) =
  PE.refl
whrDetTerm (K-β _ _ _ _) (K-β _ _ _ _) =
  PE.refl
whrDetTerm ([]-cong-β _ _ _ _ _) ([]-cong-β _ _ _ _ _) =
  PE.refl
whrDetTerm (unitrec-subst x x₁ d x₂) (unitrec-subst x₃ x₄ d′ x₅)
  rewrite whrDetTerm d d′ = PE.refl
whrDetTerm (unitrec-β x x₁ x₂) (unitrec-β x₃ x₄ x₅) = PE.refl

whrDetTerm (app-subst d _) (β-red _ _ _ _ _ _) =
  ⊥-elim (whnfRedTerm d lamₙ)
whrDetTerm (β-red _ _ _ _ _ _) (app-subst d _) =
  ⊥-elim (whnfRedTerm d lamₙ)
whrDetTerm (natrec-subst x x₁ x₂ d) (natrec-zero x₃ x₄ x₅) = ⊥-elim (whnfRedTerm d zeroₙ)
whrDetTerm (natrec-subst x x₁ x₂ d) (natrec-suc x₃ x₄ x₅ x₆) = ⊥-elim (whnfRedTerm d sucₙ)
whrDetTerm (natrec-zero x x₁ x₂) (natrec-subst x₃ x₄ x₅ d′) = ⊥-elim (whnfRedTerm d′ zeroₙ)
whrDetTerm (natrec-suc x x₁ x₂ x₃) (natrec-subst x₄ x₅ x₆ d′) = ⊥-elim (whnfRedTerm d′ sucₙ)
whrDetTerm (fst-subst _ _ x) (Σ-β₁ _ _ _ _ _ _) =
  ⊥-elim (whnfRedTerm x prodₙ)
whrDetTerm (snd-subst _ _ x) (Σ-β₂ _ _ _ _ _ _) =
  ⊥-elim (whnfRedTerm x prodₙ)
whrDetTerm (Σ-β₁ _ _ _ _ _ _) (fst-subst _ _ y) =
  ⊥-elim (whnfRedTerm y prodₙ)
whrDetTerm (Σ-β₂ _ _ _ _ _ _) (snd-subst _ _ y) =
  ⊥-elim (whnfRedTerm y prodₙ)
whrDetTerm
  (prodrec-subst _ _ _ _ t⇒ _) (prodrec-β _ _ _ _ _ _ _ _) =
  ⊥-elim (whnfRedTerm t⇒ prodₙ)
whrDetTerm
  (prodrec-β _ _ _ _ _ _ _ _) (prodrec-subst _ _ _ _ t⇒ _) =
  ⊥-elim (whnfRedTerm t⇒ prodₙ)
whrDetTerm (J-subst _ _ _ _ _ rfl⇒) (J-β _ _ _ _ _ _ _) =
  ⊥-elim (whnfRedTerm rfl⇒ rflₙ)
whrDetTerm (J-β _ _ _ _ _ _ _) (J-subst _ _ _ _ _ rfl⇒) =
  ⊥-elim (whnfRedTerm rfl⇒ rflₙ)
whrDetTerm (K-subst _ _ _ _ rfl⇒ _) (K-β _ _ _ _) =
  ⊥-elim (whnfRedTerm rfl⇒ rflₙ)
whrDetTerm (K-β _ _ _ _) (K-subst _ _ _ _ rfl⇒ _) =
  ⊥-elim (whnfRedTerm rfl⇒ rflₙ)
whrDetTerm ([]-cong-subst _ _ _ rfl⇒ _) ([]-cong-β _ _ _ _ _) =
  ⊥-elim (whnfRedTerm rfl⇒ rflₙ)
whrDetTerm ([]-cong-β _ _ _ _ _) ([]-cong-subst _ _ _ rfl⇒ _) =
  ⊥-elim (whnfRedTerm rfl⇒ rflₙ)
whrDetTerm (unitrec-subst _ _ d _) (unitrec-β _ _ _) =
  ⊥-elim (whnfRedTerm d starₙ)
whrDetTerm (unitrec-β _ _ _) (unitrec-subst _ _ d _) =
  ⊥-elim (whnfRedTerm d starₙ)

whrDet : (d : Γ ⊢ A ⇒ B) (d′ : Γ ⊢ A ⇒ B′) → B PE.≡ B′
whrDet (univ x) (univ x₁) = whrDetTerm x x₁

whrDet↘Term : (d : Γ ⊢ t ↘ u ∷ A) (d′ : Γ ⊢ t ⇒* u′ ∷ A) → Γ ⊢ u′ ⇒* u ∷ A
whrDet↘Term (proj₁ , proj₂) (id x) = proj₁
whrDet↘Term (id x , proj₂) (x₁ ⇨ d′) = ⊥-elim (whnfRedTerm x₁ proj₂)
whrDet↘Term (x ⇨ proj₁ , proj₂) (x₁ ⇨ d′) =
  whrDet↘Term (PE.subst (λ x₂ → _ ⊢ x₂ ↘ _ ∷ _) (whrDetTerm x x₁) (proj₁ , proj₂)) d′

whrDet*Term : (d : Γ ⊢ t ↘ u ∷ A) (d′ : Γ ⊢ t ↘ u′ ∷ A′) → u PE.≡ u′
whrDet*Term (id x , proj₂) (id x₁ , proj₄) = PE.refl
whrDet*Term (id x , proj₂) (x₁ ⇨ proj₃ , proj₄) = ⊥-elim (whnfRedTerm x₁ proj₂)
whrDet*Term (x ⇨ proj₁ , proj₂) (id x₁ , proj₄) = ⊥-elim (whnfRedTerm x proj₄)
whrDet*Term (x ⇨ proj₁ , proj₂) (x₁ ⇨ proj₃ , proj₄) =
  whrDet*Term (proj₁ , proj₂) (PE.subst (λ x₂ → _ ⊢ x₂ ↘ _ ∷ _)
                                    (whrDetTerm x₁ x) (proj₃ , proj₄))

whrDet* : (d : Γ ⊢ A ↘ B) (d′ : Γ ⊢ A ↘ B′) → B PE.≡ B′
whrDet* (id x , proj₂) (id x₁ , proj₄) = PE.refl
whrDet* (id x , proj₂) (x₁ ⇨ proj₃ , proj₄) = ⊥-elim (whnfRed x₁ proj₂)
whrDet* (x ⇨ proj₁ , proj₂) (id x₁ , proj₄) = ⊥-elim (whnfRed x proj₄)
whrDet* (A⇒A′ ⇨ A′⇒*B , whnfB) (A⇒A″ ⇨ A″⇒*B′ , whnfB′) =
  whrDet* (A′⇒*B , whnfB) (PE.subst (λ x → _ ⊢ x ↘ _)
                                     (whrDet A⇒A″ A⇒A′)
                                     (A″⇒*B′ , whnfB′))

-- Reduction does not include η-expansion for the unit type with
-- η-equality (for WHNFs): if a WHNF t reduces to star (at type Unit),
-- then t is equal to star.

no-η-expansion-Unit : Whnf t → Γ ⊢ t ⇒* starˢ ∷ Unitˢ → t PE.≡ starˢ
no-η-expansion-Unit = flip whnfRed*Term

-- Reduction does not include η-expansion for Σ-types with η-equality
-- (for WHNFs): if a WHNF t reduces to prodₚ p u v (at type
-- Σₚ p′ , q ▷ A ▹ B), then t is equal to prodₚ p u v.

no-η-expansion-Σₚ :
  Whnf t →
  Γ ⊢ t ⇒* prodₚ p u v ∷ Σₚ p′ , q ▷ A ▹ B →
  t PE.≡ prodₚ p u v
no-η-expansion-Σₚ = flip whnfRed*Term

-- Identity of syntactic reduction

idRed:*: : Γ ⊢ A → Γ ⊢ A :⇒*: A
idRed:*: A = [ A , A , id A ]

idRedTerm:*: : Γ ⊢ t ∷ A → Γ ⊢ t :⇒*: t ∷ A
idRedTerm:*: t = [ t , t , id t ]

-- U cannot be a term

UnotInA : Γ ⊢ U ∷ A → ⊥
UnotInA (conv U∷U x) = UnotInA U∷U

UnotInA[t] : t [ a ]₀ PE.≡ U
         → Γ ⊢ a ∷ A
         → Γ ∙ A ⊢ t ∷ B
         → ⊥
UnotInA[t] () x₁ (ℕⱼ x₂)
UnotInA[t] () x₁ (Emptyⱼ x₂)
UnotInA[t] () _  (ΠΣⱼ _ _ _)
UnotInA[t] x₁ x₂ (var x₃ here) rewrite x₁ = UnotInA x₂
UnotInA[t] () x₂ (var x₃ (there x₄))
UnotInA[t] () _  (lamⱼ _ _ _)
UnotInA[t] () x₁ (x₂ ∘ⱼ x₃)
UnotInA[t] () x₁ (zeroⱼ x₂)
UnotInA[t] () x₁ (sucⱼ x₂)
UnotInA[t] () x₁ (natrecⱼ x₂ x₃ x₄ x₅)
UnotInA[t] () x₁ (emptyrecⱼ x₂ x₃)
UnotInA[t] x x₁ (conv x₂ x₃) = UnotInA[t] x x₁ x₂

UnotInA[t,u] : t [ consSubst (consSubst idSubst u) u′ ] PE.≡ U
              → Γ ⊢ u ∷ A
              → Γ ⊢ u′ ∷ B [ a ]₀
              → Γ ∙ A ∙ B ⊢ t ∷ C
              → ⊥
UnotInA[t,u] PE.refl u u′ (var x here) = UnotInA u′
UnotInA[t,u] PE.refl u u′ (var x (there here)) = UnotInA u
UnotInA[t,u] eq u u′ (conv t x) = UnotInA[t,u] eq u u′ t

redU*Term′ : U′ PE.≡ U → Γ ⊢ A ⇒ U′ ∷ B → ⊥
redU*Term′ U′≡U (conv A⇒U x) = redU*Term′ U′≡U A⇒U
redU*Term′ () (app-subst A⇒U x)
redU*Term′ U′≡U (β-red _ _ ⊢t ⊢u _ _) = UnotInA[t] U′≡U ⊢u ⊢t
redU*Term′ () (natrec-subst x x₁ x₂ A⇒U)
redU*Term′ PE.refl (natrec-zero x x₁ x₂) = UnotInA x₁
redU*Term′ U′≡U (natrec-suc x x₁ x₂ x₃) =
  UnotInA[t,u] U′≡U x₃ (natrecⱼ x x₁ x₂ x₃) x₂
redU*Term′ U′≡U (prodrec-β _ _ _ ⊢t ⊢u ⊢v _ _) =
  UnotInA[t,u] U′≡U ⊢t ⊢u ⊢v
redU*Term′ () (emptyrec-subst x A⇒U)
redU*Term′ PE.refl (Σ-β₁ _ _ x _ _ _) = UnotInA x
redU*Term′ PE.refl (Σ-β₂ _ _ _ x _ _) = UnotInA x
redU*Term′ PE.refl (J-β _ _ _ _ _ _ ⊢u) = UnotInA ⊢u
redU*Term′ PE.refl (K-β _ _ ⊢u _) = UnotInA ⊢u
redU*Term′ PE.refl (unitrec-β _ x _) = UnotInA x

redU*Term : Γ ⊢ A ⇒* U ∷ B → ⊥
redU*Term (id x) = UnotInA x
redU*Term (x ⇨ A⇒*U) = redU*Term A⇒*U

-- Nothing reduces to U

redU : Γ ⊢ A ⇒ U → ⊥
redU (univ x) = redU*Term′ PE.refl x

redU* : Γ ⊢ A ⇒* U → A PE.≡ U
redU* (id x) = PE.refl
redU* (x ⇨ A⇒*U) rewrite redU* A⇒*U = ⊥-elim (redU x)

det∈ : ∀ {x} → x ∷ A ∈ Γ → x ∷ B ∈ Γ → A PE.≡ B
det∈ here here = PE.refl
det∈ (there x) (there y) = PE.cong wk1 (det∈ x y)
