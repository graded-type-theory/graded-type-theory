{-# OPTIONS --safe --without-K #-}

module Definition.Typed.Properties where

open import Definition.Untyped hiding (_∷_)
open import Definition.Typed
open import Definition.Modality
open import Definition.Modality.Context
open import Definition.Modality.Context.Properties
open import Definition.Modality.Substitution
open import Definition.Modality.Substitution.Properties
open import Definition.Modality.Usage

open import Tools.Fin
open import Tools.Empty using (⊥; ⊥-elim)
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    M : Set
    𝕄 : Modality M
    Γ : Con (Term M) n
    A A′ B B′ C U′ : Term M n
    a b t u u′ : Term M n
    γ δ : Conₘ 𝕄 n

-- Escape context extraction

wfTerm : Γ ⊢ t ∷ A → ⊢ Γ
wfTerm (ℕⱼ ⊢Γ) = ⊢Γ
wfTerm (Emptyⱼ ⊢Γ) = ⊢Γ
wfTerm (Unitⱼ ⊢Γ) = ⊢Γ
wfTerm (Πⱼ F ▹ G) = wfTerm F
wfTerm (var ⊢Γ x₁) = ⊢Γ
wfTerm (lamⱼ F t) with wfTerm t
wfTerm (lamⱼ F t) | ⊢Γ ∙ F′ = ⊢Γ
wfTerm (g ∘ⱼ a) = wfTerm a
wfTerm (zeroⱼ ⊢Γ) = ⊢Γ
wfTerm (sucⱼ n) = wfTerm n
wfTerm (natrecⱼ F z s n) = wfTerm z
wfTerm (Emptyrecⱼ A e) = wfTerm e
wfTerm (starⱼ ⊢Γ) = ⊢Γ
wfTerm (conv t A≡B) = wfTerm t
wfTerm (Σⱼ a ▹ a₁) = wfTerm a
wfTerm (prodⱼ F G a a₁) = wfTerm a
wfTerm (fstⱼ _ _ a) = wfTerm a
wfTerm (sndⱼ _ _ a) = wfTerm a
wfTerm (prodrecⱼ _ _ t _ _) = wfTerm t

wf : Γ ⊢ A → ⊢ Γ
wf (ℕⱼ ⊢Γ) = ⊢Γ
wf (Emptyⱼ ⊢Γ) = ⊢Γ
wf (Unitⱼ ⊢Γ) = ⊢Γ
wf (Uⱼ ⊢Γ) = ⊢Γ
wf (Πⱼ F ▹ G) = wf F
wf (Σⱼ F ▹ G) = wf F
wf (univ A) = wfTerm A

wfEqTerm : Γ ⊢ t ≡ u ∷ A → ⊢ Γ
wfEqTerm (refl t) = wfTerm t
wfEqTerm (sym t≡u) = wfEqTerm t≡u
wfEqTerm (trans t≡u u≡r) = wfEqTerm t≡u
wfEqTerm (conv t≡u A≡B) = wfEqTerm t≡u
wfEqTerm (Π-cong F F≡H G≡E) = wfEqTerm F≡H
wfEqTerm (app-cong f≡g a≡b) = wfEqTerm f≡g
wfEqTerm (β-red F t a p≡q) = wfTerm a
wfEqTerm (η-eq F f g f0≡g0) = wfTerm f
wfEqTerm (suc-cong n) = wfEqTerm n
wfEqTerm (natrec-cong _ F≡F′ z≡z′ s≡s′ n≡n′) = wfEqTerm z≡z′
wfEqTerm (natrec-zero F z s) = wfTerm z
wfEqTerm (natrec-suc n F z s) = wfTerm n
wfEqTerm (Emptyrec-cong A≡A' e≡e') = wfEqTerm e≡e'
wfEqTerm (η-unit e e') = wfTerm e
wfEqTerm (Σ-cong F _ _) = wf F
wfEqTerm (fst-cong _ _ a) = wfEqTerm a
wfEqTerm (snd-cong _ _ a) = wfEqTerm a
wfEqTerm (Σ-η _ _ x _ _ _) = wfTerm x
wfEqTerm (Σ-β₁ F G x x₁) = wfTerm x
wfEqTerm (Σ-β₂ F G x x₁) = wfTerm x
wfEqTerm (prodrec-cong a _ _ _ _) = wf a
wfEqTerm (prodrec-β a _ _ _ _ _) = wf a

wfEq : Γ ⊢ A ≡ B → ⊢ Γ
wfEq (univ A≡B) = wfEqTerm A≡B
wfEq (refl A) = wf A
wfEq (sym A≡B) = wfEq A≡B
wfEq (trans A≡B B≡C) = wfEq A≡B
wfEq (Π-cong F F≡H G≡E) = wf F
wfEq (Σ-cong F x₁ x₂) = wf F


-- Reduction is a subset of conversion

subsetTerm : Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ≡ u ∷ A
subsetTerm (natrec-subst F z s n⇒n′) =
  natrec-cong F (refl F) (refl z) (refl s) (subsetTerm n⇒n′)
subsetTerm (natrec-zero F z s) = natrec-zero F z s
subsetTerm (natrec-suc n F z s) = natrec-suc n F z s
subsetTerm (Emptyrec-subst A n⇒n′) =
  Emptyrec-cong (refl A) (subsetTerm n⇒n′)
subsetTerm (app-subst t⇒u a) = app-cong (subsetTerm t⇒u) (refl a)
subsetTerm (β-red A t a p≡q) = β-red A t a p≡q
subsetTerm (conv t⇒u A≡B) = conv (subsetTerm t⇒u) A≡B
subsetTerm (fst-subst F G x) = fst-cong F G (subsetTerm x)
subsetTerm (snd-subst F G x) = snd-cong F G (subsetTerm x)
subsetTerm (Σ-β₁ F G x x₁) = Σ-β₁ F G x x₁
subsetTerm (Σ-β₂ F G x x₁) = Σ-β₂ F G x x₁
subsetTerm (prodrec-subst F G u A x) = prodrec-cong F G (subsetTerm x) A (refl u)
subsetTerm (prodrec-β F G t t' A u) = prodrec-β F G t t' A u

subset : Γ ⊢ A ⇒ B → Γ ⊢ A ≡ B
subset (univ A⇒B) = univ (subsetTerm A⇒B)

subset*Term : Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t ≡ u ∷ A
subset*Term (id t) = refl t
subset*Term (t⇒t′ ⇨ t⇒*u) = trans (subsetTerm t⇒t′) (subset*Term t⇒*u)

subset* : Γ ⊢ A ⇒* B → Γ ⊢ A ≡ B
subset* (id A) = refl A
subset* (A⇒A′ ⇨ A′⇒*B) = trans (subset A⇒A′) (subset* A′⇒*B)


-- Can extract left-part of a reduction

redFirstTerm : {p : M} {Γ : Con (Term M) n} → Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ∷ A
redFirstTerm {p = p} (conv t⇒u A≡B) = conv (redFirstTerm {p = p} t⇒u) A≡B
redFirstTerm {p = p} (app-subst t⇒u a) = (redFirstTerm {p = p} t⇒u) ∘ⱼ a
redFirstTerm {p = q} (β-red {p} A t a PE.refl) = _∘ⱼ_ {p = p} {q = q} (lamⱼ {p = p} A t) a
redFirstTerm {p = p} (natrec-subst F z s n⇒n′) = natrecⱼ F z s (redFirstTerm {p = p} n⇒n′)
redFirstTerm {p = p} (natrec-zero F z s) = natrecⱼ F z s (zeroⱼ (wfTerm z))
redFirstTerm {p = p} (natrec-suc n F z s) = natrecⱼ F z s (sucⱼ n)
redFirstTerm {p = p} (Emptyrec-subst A n⇒n′) = Emptyrecⱼ A (redFirstTerm {p = p} n⇒n′)
redFirstTerm {p = p} (fst-subst F G x) = fstⱼ F G (redFirstTerm {p = p} x)
redFirstTerm {p = p} (snd-subst F G x) = sndⱼ F G (redFirstTerm {p = p} x)
redFirstTerm {p = p} (Σ-β₁ F G x x₁) = fstⱼ {p = p} F G (prodⱼ F G x x₁)
redFirstTerm {p = p} (Σ-β₂ F G x x₁) = sndⱼ {p = p} F G (prodⱼ F G x x₁)
redFirstTerm {p = p} (prodrec-subst F G x A x₁) = prodrecⱼ F G (redFirstTerm {p = p} x₁) A x
redFirstTerm {p = p} (prodrec-β F G t t' A u) =  prodrecⱼ F G (prodⱼ F G t t') A u

redFirst : {p : M} {Γ : Con (Term M) n} → Γ ⊢ A ⇒ B → Γ ⊢ A
redFirst {p = p} (univ A⇒B) = univ (redFirstTerm {p = p} A⇒B)

redFirst*Term : {p : M} {Γ : Con (Term M) n} → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ t ∷ A
redFirst*Term (id t) = t
redFirst*Term {p = p} (t⇒t′ ⇨ t′⇒*u) = redFirstTerm {p = p} t⇒t′

redFirst* : {p : M} {Γ : Con (Term M) n} → Γ ⊢ A ⇒* B → Γ ⊢ A
redFirst* (id A) = A
redFirst* {p = p} (A⇒A′ ⇨ A′⇒*B) = redFirst {p = p} A⇒A′


-- No neutral terms are well-formed in an empty context

noNe : ε ⊢ t ∷ A → Neutral t → ⊥
noNe (conv ⊢t x) n = noNe ⊢t n
noNe (var x₁ ()) (var x)
noNe (⊢t ∘ⱼ ⊢t₁) (∘ₙ neT) = noNe ⊢t neT
noNe (fstⱼ _ _ ⊢t) (fstₙ neT) = noNe ⊢t neT
noNe (sndⱼ _ _ ⊢t) (sndₙ neT) = noNe ⊢t neT
noNe (natrecⱼ x ⊢t ⊢t₁ ⊢t₂) (natrecₙ neT) = noNe ⊢t₂ neT
noNe (Emptyrecⱼ A ⊢e) (Emptyrecₙ neT) = noNe ⊢e neT
noNe (prodrecⱼ _ _ ⊢t ⊢A ⊢u) (prodrecₙ neT) = noNe ⊢t neT

-- Neutrals do not weak head reduce

neRedTerm : (d : Γ ⊢ t ⇒ u ∷ A) (n : Neutral t) → ⊥
neRedTerm (conv d x) n = neRedTerm d n
neRedTerm (app-subst d x) (∘ₙ n) = neRedTerm d n
neRedTerm (β-red x x₁ x₂ _) (∘ₙ ())
neRedTerm (natrec-subst x x₁ x₂ d) (natrecₙ n₁) = neRedTerm d n₁
neRedTerm (natrec-zero x x₁ x₂) (natrecₙ ())
neRedTerm (natrec-suc x x₁ x₂ x₃) (natrecₙ ())
neRedTerm (Emptyrec-subst x d) (Emptyrecₙ n₁) = neRedTerm d n₁
neRedTerm (fst-subst _ _ d) (fstₙ n) = neRedTerm d n
neRedTerm (snd-subst _ _ d) (sndₙ n) = neRedTerm d n
neRedTerm (Σ-β₁ F G x x₁) (fstₙ ())
neRedTerm (Σ-β₂ F G x x₁) (sndₙ ())
neRedTerm (prodrec-subst x x₁ x₂ x₃ d) (prodrecₙ n) = neRedTerm d n
neRedTerm (prodrec-β x x₁ x₂ x₃ x₄ x₅) (prodrecₙ ())

neRed : (d : Γ ⊢ A ⇒ B) (N : Neutral A) → ⊥
neRed (univ x) N = neRedTerm x N

-- Whnfs do not weak head reduce

whnfRedTerm : (d : Γ ⊢ t ⇒ u ∷ A) (w : Whnf t) → ⊥
whnfRedTerm (conv d x) w = whnfRedTerm d w
whnfRedTerm (app-subst d x) (ne (∘ₙ x₁)) = neRedTerm d x₁
whnfRedTerm (β-red x x₁ x₂ _) (ne (∘ₙ ()))
whnfRedTerm (natrec-subst x x₁ x₂ d) (ne (natrecₙ x₃)) = neRedTerm d x₃
whnfRedTerm (natrec-zero x x₁ x₂) (ne (natrecₙ ()))
whnfRedTerm (natrec-suc x x₁ x₂ x₃) (ne (natrecₙ ()))
whnfRedTerm (Emptyrec-subst x d) (ne (Emptyrecₙ x₂)) = neRedTerm d x₂
whnfRedTerm (fst-subst _ _ d) (ne (fstₙ n)) = neRedTerm d n
whnfRedTerm (snd-subst _ _ d) (ne (sndₙ n)) = neRedTerm d n
whnfRedTerm (Σ-β₁ F G x x₁) (ne (fstₙ ()))
whnfRedTerm (Σ-β₂ F G x x₁) (ne (sndₙ ()))
whnfRedTerm (prodrec-subst x x₁ x₂ x₃ d) (ne (prodrecₙ n)) = neRedTerm d n
whnfRedTerm (prodrec-β x x₁ x₂ x₃ x₄ x₅) (ne (prodrecₙ ()))

whnfRed : (d : Γ ⊢ A ⇒ B) (w : Whnf A) → ⊥
whnfRed (univ x) w = whnfRedTerm x w

whnfRed*Term : (d : Γ ⊢ t ⇒* u ∷ A) (w : Whnf t) → t PE.≡ u
whnfRed*Term (id x) Uₙ = PE.refl
whnfRed*Term (id x) Πₙ = PE.refl
whnfRed*Term (id x) Σₙ = PE.refl
whnfRed*Term (id x) ℕₙ = PE.refl
whnfRed*Term (id x) Emptyₙ = PE.refl
whnfRed*Term (id x) Unitₙ = PE.refl
whnfRed*Term (id x) lamₙ = PE.refl
whnfRed*Term (id x) prodₙ = PE.refl
whnfRed*Term (id x) zeroₙ = PE.refl
whnfRed*Term (id x) sucₙ = PE.refl
whnfRed*Term (id x) starₙ = PE.refl
whnfRed*Term (id x) (ne x₁) = PE.refl
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
whrDetTerm (β-red x x₁ x₂ p≡q) (β-red x₃ x₄ x₅ p≡q₁) = PE.refl
whrDetTerm (fst-subst _ _ x) (fst-subst _ _ y) rewrite whrDetTerm x y = PE.refl
whrDetTerm (snd-subst _ _ x) (snd-subst _ _ y) rewrite whrDetTerm x y = PE.refl
whrDetTerm (Σ-β₁ F G x x₁) (Σ-β₁ F₁ G₁ x₂ x₃) = PE.refl
whrDetTerm (Σ-β₂ F G x x₁) (Σ-β₂ F₁ G₁ x₂ x₃) = PE.refl
whrDetTerm (natrec-subst x x₁ x₂ d) (natrec-subst x₃ x₄ x₅ d′) rewrite whrDetTerm d d′ = PE.refl
whrDetTerm (natrec-zero x x₁ x₂) (natrec-zero x₃ x₄ x₅) = PE.refl
whrDetTerm (natrec-suc x x₁ x₂ x₃) (natrec-suc x₄ x₅ x₆ x₇) = PE.refl
whrDetTerm (Emptyrec-subst x d) (Emptyrec-subst x₂ d′) rewrite whrDetTerm d d′ = PE.refl
whrDetTerm (prodrec-subst _ _ _ _ d) (prodrec-subst _ _ _ _ d′) rewrite whrDetTerm d d′ = PE.refl
whrDetTerm (prodrec-β _ _ _ _ _ _) (prodrec-β _ _ _ _ _ _) = PE.refl

whrDetTerm (app-subst d x) (β-red x₁ x₂ x₃ p≡q) = ⊥-elim (whnfRedTerm d lamₙ)
whrDetTerm (β-red x x₁ x₂ p≡q) (app-subst d x₃) = ⊥-elim (whnfRedTerm d lamₙ)
whrDetTerm (natrec-subst x x₁ x₂ d) (natrec-zero x₃ x₄ x₅) = ⊥-elim (whnfRedTerm d zeroₙ)
whrDetTerm (natrec-subst x x₁ x₂ d) (natrec-suc x₃ x₄ x₅ x₆) = ⊥-elim (whnfRedTerm d sucₙ)
whrDetTerm (natrec-zero x x₁ x₂) (natrec-subst x₃ x₄ x₅ d′) = ⊥-elim (whnfRedTerm d′ zeroₙ)
whrDetTerm (natrec-suc x x₁ x₂ x₃) (natrec-subst x₄ x₅ x₆ d′) = ⊥-elim (whnfRedTerm d′ sucₙ)
whrDetTerm (fst-subst _ _ x) (Σ-β₁ F G x₁ x₂) = ⊥-elim (whnfRedTerm x prodₙ)
whrDetTerm (snd-subst _ _ x) (Σ-β₂ F G x₁ x₂) = ⊥-elim (whnfRedTerm x prodₙ)
whrDetTerm (Σ-β₁ F G x x₁) (fst-subst _ _ y) = ⊥-elim (whnfRedTerm y prodₙ)
whrDetTerm (Σ-β₂ F G x x₁) (snd-subst _ _ y) = ⊥-elim (whnfRedTerm y prodₙ)
whrDetTerm (prodrec-subst _ _ _ _ d) (prodrec-β _ _ _ _ _ _) = ⊥-elim (whnfRedTerm d prodₙ)
whrDetTerm (prodrec-β _ _ _ _ _ _) (prodrec-subst _ _ _ _ d′) = ⊥-elim (whnfRedTerm d′ prodₙ)

whrDet : (d : Γ ⊢ A ⇒ B) (d′ : Γ ⊢ A ⇒ B′) → B PE.≡ B′
whrDet (univ x) (univ x₁) = whrDetTerm x x₁

whrDet↘Term : (d : Γ ⊢ t ↘ u ∷ A) (d′ : Γ ⊢ t ⇒* u′ ∷ A) → Γ ⊢ u′ ⇒* u ∷ A
whrDet↘Term (proj₁ , proj₂) (id x) = proj₁
whrDet↘Term (id x , proj₂) (x₁ ⇨ d′) = ⊥-elim (whnfRedTerm x₁ proj₂)
whrDet↘Term (x ⇨ proj₁ , proj₂) (x₁ ⇨ d′) =
  whrDet↘Term (PE.subst (λ x₂ → _ ⊢ x₂ ↘ _ ∷ _) (whrDetTerm x x₁) (proj₁ , proj₂)) d′

whrDet*Term : (d : Γ ⊢ t ↘ u ∷ A) (d′ : Γ ⊢ t ↘ u′ ∷ A) → u PE.≡ u′
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

-- Identity of syntactic reduction

idRed:*: : Γ ⊢ A → Γ ⊢ A :⇒*: A
idRed:*: A = [ A , A , id A ]

idRedTerm:*: : Γ ⊢ t ∷ A → Γ ⊢ t :⇒*: t ∷ A
idRedTerm:*: t = [ t , t , id t ]

-- U cannot be a term

UnotInA : Γ ⊢ U ∷ A → ⊥
UnotInA (conv U∷U x) = UnotInA U∷U

UnotInA[t] : t [ a ] PE.≡ U
         → Γ ⊢ a ∷ A
         → Γ ∙ A ⊢ t ∷ B
         → ⊥
UnotInA[t] () x₁ (ℕⱼ x₂)
UnotInA[t] () x₁ (Emptyⱼ x₂)
UnotInA[t] () x₁ (Πⱼ x₂ ▹ x₃)
UnotInA[t] x₁ x₂ (var x₃ here) rewrite x₁ = UnotInA x₂
UnotInA[t] () x₂ (var x₃ (there x₄))
UnotInA[t] () x₁ (lamⱼ x₂ x₃)
UnotInA[t] () x₁ (x₂ ∘ⱼ x₃)
UnotInA[t] () x₁ (zeroⱼ x₂)
UnotInA[t] () x₁ (sucⱼ x₂)
UnotInA[t] () x₁ (natrecⱼ x₂ x₃ x₄ x₅)
UnotInA[t] () x₁ (Emptyrecⱼ x₂ x₃)
UnotInA[t] x x₁ (conv x₂ x₃) = UnotInA[t] x x₁ x₂

UnotInA[t][u] : t [ u′ ][ u ] PE.≡ U
              → Γ ⊢ u ∷ A
              → Γ ⊢ u′ ∷ B [ a ]
              → Γ ∙ A ∙ B ⊢ t ∷ C
              → ⊥
UnotInA[t][u] PE.refl u u′ (var x here) = UnotInA u′
UnotInA[t][u] PE.refl u u′ (var x (there here)) = UnotInA u --u′
UnotInA[t][u] eq u u′ (conv t x) = UnotInA[t][u] eq u u′ t


redU*Term′ : U′ PE.≡ U → Γ ⊢ A ⇒ U′ ∷ B → ⊥
redU*Term′ U′≡U (conv A⇒U x) = redU*Term′ U′≡U A⇒U
redU*Term′ () (app-subst A⇒U x)
redU*Term′ U′≡U (β-red x x₁ x₂ p≡q) = UnotInA[t] U′≡U x₂ x₁
redU*Term′ () (natrec-subst x x₁ x₂ A⇒U)
redU*Term′ PE.refl (natrec-zero x x₁ x₂) = UnotInA x₁
redU*Term′ U′≡U (natrec-suc x x₁ x₂ x₃) = UnotInA[t][u] U′≡U x (natrecⱼ x₁ x₂ x₃ x) x₃
redU*Term′ () (Emptyrec-subst x A⇒U)
redU*Term′ PE.refl (Σ-β₁ F G x x₁) = UnotInA x
redU*Term′ PE.refl (Σ-β₂ F G x x₁) = UnotInA x₁
redU*Term′ U′≡U (prodrec-β {p = p} x x₁ x₂ x₃ x₄ x₅) = UnotInA[t][u] U′≡U x₂ x₃ x₅

redU*Term : Γ ⊢ A ⇒* U ∷ B → ⊥
redU*Term (id x) = UnotInA x
redU*Term (x ⇨ A⇒*U) = redU*Term A⇒*U

-- Nothing reduces to U

redU : Γ ⊢ A ⇒ U → ⊥
redU (univ x) = redU*Term′ PE.refl x

redU* : Γ ⊢ A ⇒* U → A PE.≡ U
redU* (id x) = PE.refl
redU* (x ⇨ A⇒*U) rewrite redU* A⇒*U = ⊥-elim (redU x)

-- Reduction preserves resource usage


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


usagePres : {𝕄 : Modality M} {γ : Conₘ 𝕄 n} {Γ : Con (Term M) n} {A B : Term M n}
          → γ ▸ A → Γ ⊢ A ⇒ B → γ ▸ B
usagePres γ▸A (univ x) = usagePresTerm γ▸A x
