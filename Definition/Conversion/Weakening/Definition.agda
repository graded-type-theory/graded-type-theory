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

open import Tools.Bool
open import Tools.List hiding (_∷_)
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    d : Bool
    ∇ ∇′ : DCon (Term 0) _
    Γ : Con Term _
    A B t t₁ t₂ u : Term _
    l₁ l₂ : Lvl _
    v v′ v″ v₁ v₂ : Levelᵛ _
    v₁⁺ v₂⁺ : Level⁺ _
    ∇′⊇∇ : » _ ⊇ _

opaque mutual

  defn-wk~↑ :
    » ∇′ ⊇ ∇ →
    ∇ » Γ ⊢ t ~ u ↑ A →
    ∇′ » Γ ⊢ t ~ u ↑ A
  defn-wk~↑ ξ⊇ (var-refl ⊢t eq) = var-refl (defn-wk ξ⊇ ⊢t) eq
  defn-wk~↑ ξ⊇ (defn-refl ⊢α α↦⊘ eq) =
    defn-refl (defn-wk ξ⊇ ⊢α) (there*-↦⊘∈ ξ⊇ α↦⊘) eq
  defn-wk~↑ ∇′⊇∇ (lower-cong t≡u) =
    lower-cong (defn-wk~↓ ∇′⊇∇ t≡u)
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
           (defn-wk ξ⊇ ≡Id)
  defn-wk~↑ ξ⊇ (K-cong A<> t<> B<> u<> v~ ≡Id ok) =
    K-cong (defn-wkConv↑ ξ⊇ A<>)
           (defn-wkConv↑Term ξ⊇ t<>)
           (defn-wkConv↑ ξ⊇ B<>)
           (defn-wkConv↑Term ξ⊇ u<>)
           (defn-wk~↓ ξ⊇ v~)
           (defn-wk ξ⊇ ≡Id)
           ok
  defn-wk~↑ ξ⊇ ([]-cong-cong l↑ A<> t<> u<> v~ ≡Id ok) =
    []-cong-cong (defn-wkConv↑Level ξ⊇ l↑)
                 (defn-wkConv↑ ξ⊇ A<>)
                 (defn-wkConv↑Term ξ⊇ t<>)
                 (defn-wkConv↑Term ξ⊇ u<>)
                 (defn-wk~↓ ξ⊇ v~)
                 (defn-wk ξ⊇ ≡Id)
                 ok

  defn-wk~↓ :
    » ∇′ ⊇ ∇ →
    ∇ » Γ ⊢ t ~ u ↓ A →
    ∇′ » Γ ⊢ t ~ u ↓ A
  defn-wk~↓ ξ⊇ ([~] A D k~l) =
    [~] A (defn-wkRed↘ ξ⊇ D) (defn-wk~↑ ξ⊇ k~l)

  defn-wkConv↓ :
    » ∇′ ⊇ ∇ →
    ∇ » Γ ⊢ A [conv↓] B →
    ∇′ » Γ ⊢ A [conv↓] B
  defn-wkConv↓ ∇′⊇∇ (Level-refl ok ⊢Γ) =
    Level-refl ok (defn-wk ∇′⊇∇ ⊢Γ)
  defn-wkConv↓ ∇′⊇∇ (U-cong l₁≡l₂) =
    U-cong (defn-wkConv↑Level ∇′⊇∇ l₁≡l₂)
  defn-wkConv↓ ∇′⊇∇ (Lift-cong l₁≡l₂ A≡B) =
    Lift-cong (defn-wkConv↑Level ∇′⊇∇ l₁≡l₂) (defn-wkConv↑ ∇′⊇∇ A≡B)
  defn-wkConv↓ ξ⊇ (ℕ-refl ⊢Γ) = ℕ-refl (defn-wk ξ⊇ ⊢Γ)
  defn-wkConv↓ ξ⊇ (Empty-refl ⊢Γ) = Empty-refl (defn-wk ξ⊇ ⊢Γ)
  defn-wkConv↓ ξ⊇ (Unit-refl ⊢Γ ok) = Unit-refl (defn-wk ξ⊇ ⊢Γ) ok
  defn-wkConv↓ ξ⊇ (ne A~) = ne (defn-wk~↓ ξ⊇ A~)
  defn-wkConv↓ ξ⊇ (ΠΣ-cong F<> G<> ok) =
    ΠΣ-cong (defn-wkConv↑ ξ⊇ F<>) (defn-wkConv↑ ξ⊇ G<>) ok
  defn-wkConv↓ ξ⊇ (Id-cong A<> t<> u<>) =
    Id-cong (defn-wkConv↑ ξ⊇ A<>)
            (defn-wkConv↑Term ξ⊇ t<>)
            (defn-wkConv↑Term ξ⊇ u<>)

  defn-wkConv↓Term :
    » ∇′ ⊇ ∇ →
    ∇ » Γ ⊢ t [conv↓] u ∷ A →
    ∇′ » Γ ⊢ t [conv↓] u ∷ A
  defn-wkConv↓Term ∇′⊇∇ (Level-ins l₁≡l₂) =
    Level-ins (defn-wkConv↓Level ∇′⊇∇ l₁≡l₂)
  defn-wkConv↓Term ξ⊇ (ℕ-ins t~) = ℕ-ins (defn-wk~↓ ξ⊇ t~)
  defn-wkConv↓Term ξ⊇ (Empty-ins t~) = Empty-ins (defn-wk~↓ ξ⊇ t~)
  defn-wkConv↓Term ξ⊇ (Unitʷ-ins no-η t~) = Unitʷ-ins no-η (defn-wk~↓ ξ⊇ t~)
  defn-wkConv↓Term ξ⊇ (Σʷ-ins ⊢t ⊢u t~u) =
    Σʷ-ins (defn-wk ξ⊇ ⊢t) (defn-wk ξ⊇ ⊢u) (defn-wk~↓ ξ⊇ t~u)
  defn-wkConv↓Term ξ⊇ (ne-ins ⊢t ⊢u neA t~u) =
    ne-ins (defn-wk ξ⊇ ⊢t)
           (defn-wk ξ⊇ ⊢u)
           (defn-wkNeutral ξ⊇ neA)
           (defn-wk~↓ ξ⊇ t~u)
  defn-wkConv↓Term ξ⊇ (univ ⊢t ⊢u t<>u) =
    univ (defn-wk ξ⊇ ⊢t) (defn-wk ξ⊇ ⊢u) (defn-wkConv↓ ξ⊇ t<>u)
  defn-wkConv↓Term
    ∇′⊇∇ (Lift-η ⊢t₁ ⊢t₂ t₁-whnf t₂-whnf lower-t₁≡lower-t₂) =
    Lift-η (defn-wk ∇′⊇∇ ⊢t₁) (defn-wk ∇′⊇∇ ⊢t₂)
      (defn-wkWhnf ∇′⊇∇ t₁-whnf) (defn-wkWhnf ∇′⊇∇ t₂-whnf)
      (defn-wkConv↑Term ∇′⊇∇ lower-t₁≡lower-t₂)
  defn-wkConv↓Term ξ⊇ (zero-refl ⊢Γ) = zero-refl (defn-wk ξ⊇ ⊢Γ)
  defn-wkConv↓Term ξ⊇ (starʷ-refl ⊢Γ ok no-η) = starʷ-refl (defn-wk ξ⊇ ⊢Γ) ok no-η
  defn-wkConv↓Term ξ⊇ (suc-cong n<>) = suc-cong (defn-wkConv↑Term ξ⊇ n<>)
  defn-wkConv↓Term ξ⊇ (prod-cong ⊢G t<> u<> ok) =
    prod-cong (defn-wk ξ⊇ ⊢G)
              (defn-wkConv↑Term ξ⊇ t<>)
              (defn-wkConv↑Term ξ⊇ u<>)
              ok
  defn-wkConv↓Term ξ⊇ (η-eq ⊢t ⊢u ft fu 0<>) =
    η-eq (defn-wk ξ⊇ ⊢t)
         (defn-wk ξ⊇ ⊢u)
         (defn-wkFunction ξ⊇ ft)
         (defn-wkFunction ξ⊇ fu)
         (defn-wkConv↑Term ξ⊇ 0<>)
  defn-wkConv↓Term ξ⊇ (Σ-η ⊢t ⊢u pt pu fst<> snd<>) =
    Σ-η (defn-wk ξ⊇ ⊢t)
        (defn-wk ξ⊇ ⊢u)
        (defn-wkProduct ξ⊇ pt)
        (defn-wkProduct ξ⊇ pu)
        (defn-wkConv↑Term ξ⊇ fst<>)
        (defn-wkConv↑Term ξ⊇ snd<>)
  defn-wkConv↓Term ξ⊇ (η-unit ⊢t ⊢u wt wu η) =
    η-unit (defn-wk ξ⊇ ⊢t)
           (defn-wk ξ⊇ ⊢u)
           (defn-wkWhnf ξ⊇ wt)
           (defn-wkWhnf ξ⊇ wu)
           η
  defn-wkConv↓Term ξ⊇ (Id-ins ⊢t t~) =
    Id-ins (defn-wk ξ⊇ ⊢t) (defn-wk~↓ ξ⊇ t~)
  defn-wkConv↓Term ξ⊇ (rfl-refl t≡) = rfl-refl (defn-wk ξ⊇ t≡)

  defn-wkConv↑ :
    » ∇′ ⊇ ∇ →
    ∇ » Γ ⊢ A [conv↑] B →
    ∇′ » Γ ⊢ A [conv↑] B
  defn-wkConv↑ ξ⊇ ([↑] A′ B′ D D′ A′<>B′) =
    [↑] A′ B′ (defn-wkRed↘ ξ⊇ D)
              (defn-wkRed↘ ξ⊇ D′)
              (defn-wkConv↓ ξ⊇ A′<>B′)

  defn-wkConv↑Term :
    » ∇′ ⊇ ∇ →
    ∇ » Γ ⊢ t [conv↑] u ∷ A →
    ∇′ » Γ ⊢ t [conv↑] u ∷ A
  defn-wkConv↑Term ξ⊇ ([↑]ₜ B t′ u′ D d d′ t<>u) =
    [↑]ₜ B t′ u′ (defn-wkRed↘ ξ⊇ D)
                 (defn-wkRed↘Term ξ⊇ d)
                 (defn-wkRed↘Term ξ⊇ d′)
                 (defn-wkConv↓Term ξ⊇ t<>u)

  defn-wkConv↑Level :
    » ∇′ ⊇ ∇ →
    ∇ » Γ ⊢ l₁ [conv↑] l₂ ∷Level →
    ∇′ » Γ ⊢ l₁ [conv↑] l₂ ∷Level
  defn-wkConv↑Level ∇′⊇∇ (term ok l₁≡l₂) =
    term ok (defn-wkConv↑Term ∇′⊇∇ l₁≡l₂)
  defn-wkConv↑Level ∇′⊇∇ (literal! ok ⊢Γ) =
    literal! ok (defn-wk ∇′⊇∇ ⊢Γ)

  defn-wkConv↓Level :
    » ∇′ ⊇ ∇ →
    ∇ » Γ ⊢ t₁ [conv↓] t₂ ∷Level →
    ∇′ » Γ ⊢ t₁ [conv↓] t₂ ∷Level
  defn-wkConv↓Level ∇′⊇∇ ([↓]ˡ l₁ᵛ l₂ᵛ l₁↓l₁ᵛ l₂↓l₂ᵛ l₁ᵛ≡l₂ᵛ) =
    [↓]ˡ (defn-wkLevelᵛ ∇′⊇∇ l₁ᵛ) (defn-wkLevelᵛ ∇′⊇∇ l₂ᵛ)
      (defn-wk-↓ᵛ l₁↓l₁ᵛ) (defn-wk-↓ᵛ l₂↓l₂ᵛ) (defn-wk-≡ᵛ l₁ᵛ≡l₂ᵛ)

  defn-wkLevelᵛ : » ∇′ ⊇ ∇ → Levelᵛ (∇ » Γ) → Levelᵛ (∇′ » Γ)
  defn-wkLevelᵛ ∇′⊇∇ L.[]       = L.[]
  defn-wkLevelᵛ ∇′⊇∇ (x L.∷ xs) =
    defn-wkLevel⁺ ∇′⊇∇ x L.∷ defn-wkLevelᵛ ∇′⊇∇ xs

  defn-wkLevel⁺ : » ∇′ ⊇ ∇ → Level⁺ (∇ » Γ) → Level⁺ (∇′ » Γ)
  defn-wkLevel⁺ ∇′⊇∇ (n , l) = n , defn-wkLevelAtom ∇′⊇∇ l

  defn-wkLevelAtom : » ∇′ ⊇ ∇ → LevelAtom (∇ » Γ) → LevelAtom (∇′ » Γ)
  defn-wkLevelAtom ∇′⊇∇ zeroᵘ    = zeroᵘ
  defn-wkLevelAtom ∇′⊇∇ (ne t~t) = ne (defn-wk~↓ ∇′⊇∇ t~t)

  defn-wk-↓ᵛ : ∇ » Γ ⊢ t ↓ᵛ v → ∇′ » Γ ⊢ t ↓ᵛ defn-wkLevelᵛ ∇′⊇∇ v
  defn-wk-↓ᵛ {∇′⊇∇} (zeroᵘₙ ok ⊢Γ) =
    zeroᵘₙ ok (defn-wk ∇′⊇∇ ⊢Γ)
  defn-wk-↓ᵛ (sucᵘₙ eq t≡u) =
    sucᵘₙ (defn-wk-sucᵛ eq) (defn-wk-↑ᵛ t≡u)
  defn-wk-↓ᵛ (neₙ t~v) =
    neₙ (defn-wk-~ᵛ t~v)

  defn-wk-sucᵛ :
    v PE.≡ sucᵛ v′ →
    defn-wkLevelᵛ ∇′⊇∇ v PE.≡ sucᵛ (defn-wkLevelᵛ ∇′⊇∇ v′)
  defn-wk-sucᵛ PE.refl = PE.cong (_ L.∷_) (defn-wk-map-suc⁺ PE.refl)

  defn-wk-map-suc⁺ :
    v PE.≡ map-suc⁺ v′ →
    defn-wkLevelᵛ ∇′⊇∇ v PE.≡ map-suc⁺ (defn-wkLevelᵛ ∇′⊇∇ v′)
  defn-wk-map-suc⁺ {v′ = L.[]}    PE.refl = PE.refl
  defn-wk-map-suc⁺ {v′ = _ L.∷ _} PE.refl =
    PE.cong (_ L.∷_) (defn-wk-map-suc⁺ PE.refl)

  defn-wk-↑ᵛ : ∇ » Γ ⊢ t ↑ᵛ v → ∇′ » Γ ⊢ t ↑ᵛ defn-wkLevelᵛ ∇′⊇∇ v
  defn-wk-↑ᵛ {∇′⊇∇} ([↑]ᵛ d t↓v) =
    [↑]ᵛ (defn-wkRed↘Term ∇′⊇∇ d) (defn-wk-↓ᵛ t↓v)

  defn-wk-≡ᵛ : v₁ ≡ᵛ v₂ → defn-wkLevelᵛ ∇′⊇∇ v₁ ≡ᵛ defn-wkLevelᵛ ∇′⊇∇ v₂
  defn-wk-≡ᵛ (t≤u , u≤t) = defn-wk-≤ᵛ t≤u , defn-wk-≤ᵛ u≤t

  defn-wk-≤ᵛ :
    ≤ᵛ d v₁ v₂ → ≤ᵛ d (defn-wkLevelᵛ ∇′⊇∇ v₁) (defn-wkLevelᵛ ∇′⊇∇ v₂)
  defn-wk-≤ᵛ All.[]          = All.[]
  defn-wk-≤ᵛ (p All.∷ v₁≤v₂) = defn-wk-≤⁺ᵛ p All.∷ defn-wk-≤ᵛ v₁≤v₂

  defn-wk-≤⁺ᵛ :
    ≤⁺ᵛ d v₁⁺ v₂ →
    ≤⁺ᵛ d (defn-wkLevel⁺ ∇′⊇∇ v₁⁺) (defn-wkLevelᵛ ∇′⊇∇ v₂)
  defn-wk-≤⁺ᵛ (Any.here p)      = Any.here (defn-wk-≤⁺ p)
  defn-wk-≤⁺ᵛ (Any.there v₁≤v₂) = Any.there (defn-wk-≤⁺ᵛ v₁≤v₂)

  defn-wk-≤⁺ :
    ≤⁺ d v₁⁺ v₂⁺ →
    ≤⁺ d (defn-wkLevel⁺ ∇′⊇∇ v₁⁺) (defn-wkLevel⁺ ∇′⊇∇ v₂⁺)
  defn-wk-≤⁺        (n , zeroᵘ≤)      = n , zeroᵘ≤
  defn-wk-≤⁺ {∇′⊇∇} (n , ne≤ v₁⁺≡v₂⁺) =
    n , ne≤ (defn-wk-≡ⁿ ∇′⊇∇ v₁⁺≡v₂⁺)

  defn-wk-≡ⁿ : » ∇′ ⊇ ∇ → ≡ⁿ (∇ » Γ) t u d → ≡ⁿ (∇′ » Γ) t u d
  defn-wk-≡ⁿ ∇′⊇∇ (ne≡ t~u)  = ne≡ (defn-wk~↓ ∇′⊇∇ t~u)
  defn-wk-≡ⁿ ∇′⊇∇ (ne≡' u~t) = ne≡' (defn-wk~↓ ∇′⊇∇ u~t)

  defn-wk-~ᵛ : ∇ » Γ ⊢ t ~ᵛ v → ∇′ » Γ ⊢ t ~ᵛ defn-wkLevelᵛ ∇′⊇∇ v
  defn-wk-~ᵛ (supᵘˡₙ {v′} eq t~ u↑) =
    supᵘˡₙ (defn-wk-supᵛ v′ eq) (defn-wk-~ᵛ t~) (defn-wk-↑ᵛ u↑)
  defn-wk-~ᵛ (supᵘʳₙ {v′} eq t↑ u~) =
    supᵘʳₙ (defn-wk-supᵛ-sucᵛ v′ eq) (defn-wk-↑ᵛ t↑) (defn-wk-~ᵛ u~)
  defn-wk-~ᵛ (neₙ t~ eq) =
    neₙ (defn-wk~↓ _ t~) (defn-wkLevelᵛ-cong eq)

  defn-wk-supᵛ :
    (v′ : Levelᵛ (∇ » Γ)) →
    v PE.≡ supᵛ v′ v″ →
    defn-wkLevelᵛ ∇′⊇∇ v PE.≡
    supᵛ (defn-wkLevelᵛ ∇′⊇∇ v′) (defn-wkLevelᵛ ∇′⊇∇ v″)
  defn-wk-supᵛ               L.[]       PE.refl = PE.refl
  defn-wk-supᵛ {v = L.[]}    (_ L.∷ _)  ()
  defn-wk-supᵛ {v = _ L.∷ _} (_ L.∷ v′) eq      =
    let eq₁ , eq₂ = L.∷-injective eq in
    PE.cong₂ L._∷_ (defn-wkLevel⁺-cong eq₁) (defn-wk-supᵛ v′ eq₂)

  defn-wkLevel⁺-cong :
    v₁⁺ PE.≡ v₂⁺ → defn-wkLevel⁺ ∇′⊇∇ v₁⁺ PE.≡ defn-wkLevel⁺ ∇′⊇∇ v₂⁺
  defn-wkLevel⁺-cong PE.refl = PE.refl

  defn-wk-supᵛ-sucᵛ :
    (v′ : Levelᵛ (∇ » Γ)) →
    v PE.≡ supᵛ (sucᵛ v′) v″ →
    defn-wkLevelᵛ ∇′⊇∇ v PE.≡
    supᵛ (sucᵛ (defn-wkLevelᵛ ∇′⊇∇ v′)) (defn-wkLevelᵛ ∇′⊇∇ v″)
  defn-wk-supᵛ-sucᵛ {v = L.[]} _ ()
  defn-wk-supᵛ-sucᵛ {v = x L.∷ v} v′ eq =
    let eq₁ , eq₂ = L.∷-injective eq in
    PE.cong₂ L._∷_ (defn-wkLevel⁺-cong eq₁)
      (defn-wk-supᵛ-map-suc⁺ v′ eq₂)

  defn-wk-supᵛ-map-suc⁺ :
    (v′ : Levelᵛ (∇ » Γ)) →
    v PE.≡ supᵛ (map-suc⁺ v′) v″ →
    defn-wkLevelᵛ ∇′⊇∇ v PE.≡
    supᵛ (map-suc⁺ (defn-wkLevelᵛ ∇′⊇∇ v′)) (defn-wkLevelᵛ ∇′⊇∇ v″)
  defn-wk-supᵛ-map-suc⁺               L.[]       PE.refl = PE.refl
  defn-wk-supᵛ-map-suc⁺ {v = L.[]}    (_ L.∷ _)  ()
  defn-wk-supᵛ-map-suc⁺ {v = _ L.∷ _} (_ L.∷ v′) eq      =
    let eq₁ , eq₂ = L.∷-injective eq in
    PE.cong₂ L._∷_ (defn-wkLevel⁺-cong-suc⁺ eq₁)
      (defn-wk-supᵛ-map-suc⁺ v′ eq₂)

  defn-wkLevel⁺-cong-suc⁺ :
    v₁⁺ PE.≡ suc⁺ v₂⁺ →
    defn-wkLevel⁺ ∇′⊇∇ v₁⁺ PE.≡ suc⁺ (defn-wkLevel⁺ ∇′⊇∇ v₂⁺)
  defn-wkLevel⁺-cong-suc⁺ PE.refl = PE.refl

  defn-wkLevelᵛ-cong :
    v₁ PE.≡ v₂ → defn-wkLevelᵛ ∇′⊇∇ v₁ PE.≡ defn-wkLevelᵛ ∇′⊇∇ v₂
  defn-wkLevelᵛ-cong PE.refl = PE.refl
