------------------------------------------------------------------------
-- The algorithmic equality is closed under weakening of the definition
-- context
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Conversion.Weakening.Definition
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  where

open import Definition.Untyped M

open import Definition.Typed R
open import Definition.Typed.Weakening.Definition R

open import Definition.Conversion R

private
  variable
    ∇ ∇′ : DCon (Term 0) _
    Γ : Con Term _
    t u A B : Term _
    ξ : DExt (Term 0) _ _

opaque mutual

  defn-wk~↑ :
    ξ » ∇′ ⊇ ∇ →
    ∇ » Γ ⊢ t ~ u ↑ A →
    ∇′ » Γ ⊢ t ~ u ↑ A
  defn-wk~↑ ξ⊇ (var-refl ⊢t eq) = var-refl (defn-wkTerm ξ⊇ ⊢t) eq
  defn-wk~↑ ξ⊇ (defn-refl ⊢α α↦⊘ eq) =
    defn-refl (defn-wkTerm ξ⊇ ⊢α) (there*-↦⊘∈ ξ⊇ α↦⊘) eq
  defn-wk~↑ ξ⊇ (app-cong t~ u<>) =
    app-cong (defn-wk~↓ ξ⊇ t~) (defn-wkConv↑Term ξ⊇ u<>)
  defn-wk~↑ ξ⊇ (fst-cong t~) = fst-cong (defn-wk~↓ ξ⊇ t~)
  defn-wk~↑ ξ⊇ (snd-cong t~) = snd-cong (defn-wk~↓ ξ⊇ t~)
  defn-wk~↑ ξ⊇ (natrec-cong A<> t<> u<> v~) =
    natrec-cong (defn-wkConv↑ ξ⊇ A<>)
                (defn-wkConv↑Term ξ⊇ t<>)
                (defn-wkConv↑Term ξ⊇ u<>)
                (defn-wk~↓ ξ⊇ v~)
  defn-wk~↑ ξ⊇ (prodrec-cong C<> g~ u<> ) =
    prodrec-cong (defn-wkConv↑ ξ⊇ C<>)
                 (defn-wk~↓ ξ⊇ g~)
                 (defn-wkConv↑Term ξ⊇ u<>)
  defn-wk~↑ ξ⊇ (emptyrec-cong A<> t~) =
    emptyrec-cong (defn-wkConv↑ ξ⊇ A<>) (defn-wk~↓ ξ⊇ t~)
  defn-wk~↑ ξ⊇ (unitrec-cong A<> t~ u<> no-η) =
    unitrec-cong (defn-wkConv↑ ξ⊇ A<>)
                 (defn-wk~↓ ξ⊇ t~)
                 (defn-wkConv↑Term ξ⊇ u<>)
                 no-η
  defn-wk~↑ ξ⊇ (J-cong A<> t<> B<> u<> v<> w~ ≡Id) =
    J-cong (defn-wkConv↑ ξ⊇ A<>)
           (defn-wkConv↑Term ξ⊇ t<>)
           (defn-wkConv↑ ξ⊇ B<>)
           (defn-wkConv↑Term ξ⊇ u<>)
           (defn-wkConv↑Term ξ⊇ v<>)
           (defn-wk~↓ ξ⊇ w~)
           (defn-wkEq ξ⊇ ≡Id)
  defn-wk~↑ ξ⊇ (K-cong A<> t<> B<> u<> v~ ≡Id ok) =
    K-cong (defn-wkConv↑ ξ⊇ A<>)
           (defn-wkConv↑Term ξ⊇ t<>)
           (defn-wkConv↑ ξ⊇ B<>)
           (defn-wkConv↑Term ξ⊇ u<>)
           (defn-wk~↓ ξ⊇ v~)
           (defn-wkEq ξ⊇ ≡Id)
           ok
  defn-wk~↑ ξ⊇ ([]-cong-cong A<> t<> u<> v~ ≡Id ok) =
    []-cong-cong (defn-wkConv↑ ξ⊇ A<>)
                 (defn-wkConv↑Term ξ⊇ t<>)
                 (defn-wkConv↑Term ξ⊇ u<>)
                 (defn-wk~↓ ξ⊇ v~)
                 (defn-wkEq ξ⊇ ≡Id)
                 ok

  defn-wk~↓ :
    ξ » ∇′ ⊇ ∇ →
    ∇ » Γ ⊢ t ~ u ↓ A →
    ∇′ » Γ ⊢ t ~ u ↓ A
  defn-wk~↓ ξ⊇ ([~] A D k~l) =
    [~] A (defn-wkRed↘ ξ⊇ D) (defn-wk~↑ ξ⊇ k~l)

  defn-wkConv↓ :
    ξ » ∇′ ⊇ ∇ →
    ∇ » Γ ⊢ A [conv↓] B →
    ∇′ » Γ ⊢ A [conv↓] B
  defn-wkConv↓ ξ⊇ (U-refl ⊢Γ) = U-refl (defn-wk′ ξ⊇ ⊢Γ)
  defn-wkConv↓ ξ⊇ (ℕ-refl ⊢Γ) = ℕ-refl (defn-wk′ ξ⊇ ⊢Γ)
  defn-wkConv↓ ξ⊇ (Empty-refl ⊢Γ) = Empty-refl (defn-wk′ ξ⊇ ⊢Γ)
  defn-wkConv↓ ξ⊇ (Unit-refl ⊢Γ ok) = Unit-refl (defn-wk′ ξ⊇ ⊢Γ) ok
  defn-wkConv↓ ξ⊇ (ne A~) = ne (defn-wk~↓ ξ⊇ A~)
  defn-wkConv↓ ξ⊇ (ΠΣ-cong F<> G<> ok) =
    ΠΣ-cong (defn-wkConv↑ ξ⊇ F<>) (defn-wkConv↑ ξ⊇ G<>) ok
  defn-wkConv↓ ξ⊇ (Id-cong A<> t<> u<>) =
    Id-cong (defn-wkConv↑ ξ⊇ A<>)
            (defn-wkConv↑Term ξ⊇ t<>)
            (defn-wkConv↑Term ξ⊇ u<>)

  defn-wkConv↓Term :
    ξ » ∇′ ⊇ ∇ →
    ∇ » Γ ⊢ t [conv↓] u ∷ A →
    ∇′ » Γ ⊢ t [conv↓] u ∷ A
  defn-wkConv↓Term ξ⊇ (ℕ-ins t~) = ℕ-ins (defn-wk~↓ ξ⊇ t~)
  defn-wkConv↓Term ξ⊇ (Empty-ins t~) = Empty-ins (defn-wk~↓ ξ⊇ t~)
  defn-wkConv↓Term ξ⊇ (Unitʷ-ins no-η t~) = Unitʷ-ins no-η (defn-wk~↓ ξ⊇ t~)
  defn-wkConv↓Term ξ⊇ (Σʷ-ins ⊢t ⊢u t~u) =
    Σʷ-ins (defn-wkTerm ξ⊇ ⊢t) (defn-wkTerm ξ⊇ ⊢u) (defn-wk~↓ ξ⊇ t~u)
  defn-wkConv↓Term ξ⊇ (ne-ins ⊢t ⊢u neA t~u) =
    ne-ins (defn-wkTerm ξ⊇ ⊢t)
           (defn-wkTerm ξ⊇ ⊢u)
           (defn-wkNeutral ξ⊇ neA)
           (defn-wk~↓ ξ⊇ t~u)
  defn-wkConv↓Term ξ⊇ (univ ⊢t ⊢u t<>u) =
    univ (defn-wkTerm ξ⊇ ⊢t) (defn-wkTerm ξ⊇ ⊢u) (defn-wkConv↓ ξ⊇ t<>u)
  defn-wkConv↓Term ξ⊇ (zero-refl ⊢Γ) = zero-refl (defn-wk′ ξ⊇ ⊢Γ)
  defn-wkConv↓Term ξ⊇ (starʷ-refl ⊢Γ ok no-η) = starʷ-refl (defn-wk′ ξ⊇ ⊢Γ) ok no-η
  defn-wkConv↓Term ξ⊇ (suc-cong n<>) = suc-cong (defn-wkConv↑Term ξ⊇ n<>)
  defn-wkConv↓Term ξ⊇ (prod-cong ⊢G t<> u<> ok) =
    prod-cong (defn-wk ξ⊇ ⊢G)
              (defn-wkConv↑Term ξ⊇ t<>)
              (defn-wkConv↑Term ξ⊇ u<>)
              ok
  defn-wkConv↓Term ξ⊇ (η-eq ⊢t ⊢u ft fu 0<>) =
    η-eq (defn-wkTerm ξ⊇ ⊢t)
         (defn-wkTerm ξ⊇ ⊢u)
         (defn-wkFunction ξ⊇ ft)
         (defn-wkFunction ξ⊇ fu)
         (defn-wkConv↑Term ξ⊇ 0<>)
  defn-wkConv↓Term ξ⊇ (Σ-η ⊢t ⊢u pt pu fst<> snd<>) =
    Σ-η (defn-wkTerm ξ⊇ ⊢t)
        (defn-wkTerm ξ⊇ ⊢u)
        (defn-wkProduct ξ⊇ pt)
        (defn-wkProduct ξ⊇ pu)
        (defn-wkConv↑Term ξ⊇ fst<>)
        (defn-wkConv↑Term ξ⊇ snd<>)
  defn-wkConv↓Term ξ⊇ (η-unit ⊢t ⊢u wt wu η) =
    η-unit (defn-wkTerm ξ⊇ ⊢t)
           (defn-wkTerm ξ⊇ ⊢u)
           (defn-wkWhnf ξ⊇ wt)
           (defn-wkWhnf ξ⊇ wu)
           η
  defn-wkConv↓Term ξ⊇ (Id-ins ⊢t t~) =
    Id-ins (defn-wkTerm ξ⊇ ⊢t) (defn-wk~↓ ξ⊇ t~)
  defn-wkConv↓Term ξ⊇ (rfl-refl t≡) = rfl-refl (defn-wkEqTerm ξ⊇ t≡)

  defn-wkConv↑ :
    ξ » ∇′ ⊇ ∇ →
    ∇ » Γ ⊢ A [conv↑] B →
    ∇′ » Γ ⊢ A [conv↑] B
  defn-wkConv↑ ξ⊇ ([↑] A′ B′ D D′ A′<>B′) =
    [↑] A′ B′ (defn-wkRed↘ ξ⊇ D)
              (defn-wkRed↘ ξ⊇ D′)
              (defn-wkConv↓ ξ⊇ A′<>B′)

  defn-wkConv↑Term :
    ξ » ∇′ ⊇ ∇ →
    ∇ » Γ ⊢ t [conv↑] u ∷ A →
    ∇′ » Γ ⊢ t [conv↑] u ∷ A
  defn-wkConv↑Term ξ⊇ ([↑]ₜ B t′ u′ D d d′ t<>u) =
    [↑]ₜ B t′ u′ (defn-wkRed↘ ξ⊇ D)
                 (defn-wkRed↘Term ξ⊇ d)
                 (defn-wkRed↘Term ξ⊇ d′)
                 (defn-wkConv↓Term ξ⊇ t<>u)
