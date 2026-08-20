------------------------------------------------------------------------
-- Has-[]-cong
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
import Graded.Modality
import Graded.Mode.Instances.Zero-one
open import Graded.Mode.Instances.Zero-one.Variant
open import Graded.Usage.Restrictions

module Graded.Has-box-cong
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  {variant : Mode-variant 𝕄}
  (open Graded.Mode.Instances.Zero-one variant)
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions 𝕄 Zero-one-isMode)
  where

open Modality 𝕄
open Type-restrictions TR

open import Definition.Typed TR
open import Definition.Typed.Inversion TR
open import Definition.Typed.Properties TR
open import Definition.Typed.Weakening TR using (_»_∷ʷ_⊇_)
open import Definition.Typed.Well-formed TR
open import Definition.Untyped M
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Properties M

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Usage UR

open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  n                          : Nat
  Δ                          : Con Term _
  A t u                      : Term _
  l                          : Lvl _
  p₁ p₂ p₃ p₄ q₁ q₂ q₃ q₄ q₅ : M
  m                          : Mode
  s                          : Strength

------------------------------------------------------------------------
-- Has-[]-cong

-- The property of supporting a []-cong combinator for a certain mode,
-- a certain erased variable context, a certain level, a certain type,
-- a certain value, and certain grades.

Has-[]-cong-for-value :
  Strength → Mode → Con Term n → Lvl n → (_ _ : Term n) (_ _ _ : M) →
  Set a
Has-[]-cong-for-value {n} s m Γ l A t p₁ q₁ q₂ =
  let open Erased s in
  ∃ λ ([]-cong : Term n) →
  𝟘ᶜ ▸[ m ] []-cong ×
  ε » Γ ⊢ []-cong ∷
    Π p₁ , q₁ ▷ A ▹
    Π 𝟘  , q₂ ▷ Id (wk1 A) (wk1 t) (var x0) ▹
    Id (Erased (wk[ 2 ]′ l) (wk[ 2 ]′ A)) [ wk[ 2 ]′ t ] ([ var x1 ])

-- The property of supporting a []-cong combinator for a certain mode,
-- a certain erased variable context, a certain level, a certain type,
-- and certain grades.

Has-[]-cong-for-type :
  Strength → Mode → Con Term n → Lvl n → Term n → (_ _ _ _ _ : M) →
  Set a
Has-[]-cong-for-type {n} s m Γ l A p₁ q₁ p₂ q₂ q₃ =
  let open Erased s in
  ∃ λ ([]-cong : Term n) →
  𝟘ᶜ ▸[ m ] []-cong ×
  ε » Γ ⊢ []-cong ∷
    Π p₁ , q₁ ▷ A ▹
    Π p₂ , q₂ ▷ wk1 A ▹
    Π 𝟘  , q₃ ▷ Id (wk[ 2 ]′ A) (var x1) (var x0) ▹
    Id (Erased (wk[ 3 ]′ l) (wk[ 3 ]′ A)) [ var x2 ] ([ var x1 ])

-- The property of supporting a []-cong combinator (with certain
-- grades) for a certain mode, a certain erased variable context, and
-- a certain level.
--
-- Note that, unlike the []-cong primitive, the type argument must be
-- a type in U l.

Has-[]-cong-for-level :
  Strength → Mode → Con Term n → Lvl n → (_ _ _ _ _ _ _ : M) → Set a
Has-[]-cong-for-level {n} s m Γ l p₁ q₁ p₂ q₂ p₃ q₃ q₄ =
  let open Erased s in
  ∃ λ ([]-cong : Term n) →
  𝟘ᶜ ▸[ m ] []-cong ×
  ε » Γ ⊢ []-cong ∷
    Π p₁ , q₁ ▷ U l ▹
    Π p₂ , q₂ ▷ var x0 ▹
    Π p₃ , q₃ ▷ var x1 ▹
    Π 𝟘  , q₄ ▷ Id (var x2) (var x1) (var x0) ▹
    Id (Erased (wk[ 4 ]′ l) (var x3)) ([ var x2 ]) ([ var x1 ])

-- The property of supporting a []-cong combinator (with certain
-- grades) for a certain mode and a certain erased variable context.
--
-- Note that, unlike the []-cong primitive, the type argument must be
-- a type in U l for some l.

Has-[]-cong :
  Strength → Mode → Con Term n → (_ _ _ _ _ _ _ _ _ : M) → Set a
Has-[]-cong {n} s m Γ p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ q₅ =
  let open Erased s in
  ∃ λ ([]-cong : Term n) →
  𝟘ᶜ ▸[ m ] []-cong ×
  ε » Γ ⊢ []-cong ∷
    Π p₁ , q₁ ▷ Level ▹
    Π p₂ , q₂ ▷ U (level (var x0)) ▹
    Π p₃ , q₃ ▷ var x0 ▹
    Π p₄ , q₄ ▷ var x1 ▹
    Π 𝟘  , q₅ ▷ Id (var x2) (var x1) (var x0) ▹
    Id (Erased (level (var x4)) (var x3)) ([ var x2 ]) ([ var x1 ])

-- The property of supporting a []-cong combinator that "computes"
-- correctly (stated in terms of definitional equality).

Has-computing-[]-cong-for-level :
  Strength → Mode → Con Term n → Lvl n → (_ _ _ _ _ _ _ : M) → Set a
Has-computing-[]-cong-for-level {n} s m Γ l p₁ q₁ p₂ q₂ p₃ q₃ p₄ =
  let open Erased s in
  ∃ λ (([]-cong′ , _) :
       Has-[]-cong-for-level s m Γ l p₁ q₁ p₂ q₂ p₃ q₃ p₄) →
  ∀ m n′ (Δ : Cons m n′) (A t : Term n′) (ρ : Wk n′ n) →
  Δ .defs » ρ ∷ʷ Δ .vars ⊇ Γ →
  Δ ⊢ A ∷ U (wk ρ l) →
  Δ ⊢ t ∷ A →
  Δ ⊢ wk ρ []-cong′ ∘⟨ p₁ ⟩ A ∘⟨ p₂ ⟩ t ∘⟨ p₃ ⟩ t ∘⟨ 𝟘 ⟩ rfl ≡
    rfl ∷ Id (Erased (wk ρ l) A) [ t ] ([ t ])

-- The property of supporting a []-cong combinator that "computes"
-- correctly (stated in terms of definitional equality).

Has-computing-[]-cong :
  Strength → Mode → Con Term n → (_ _ _ _ _ _ _ _ _ : M) → Set a
Has-computing-[]-cong {n} s m Γ p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ q₅ =
  let open Erased s in
  ∃ λ (([]-cong′ , _) : Has-[]-cong s m Γ p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ q₅) →
  ∀ m n′ (Δ : Cons m n′) (l A t : Term n′) (ρ : Wk n′ n) →
  Δ .defs » ρ ∷ʷ Δ .vars ⊇ Γ →
  Δ ⊢ A ∷ U (level l) →
  Δ ⊢ t ∷ A →
  Δ ⊢ wk ρ []-cong′ ∘⟨ p₁ ⟩ l ∘⟨ p₂ ⟩ A ∘⟨ p₃ ⟩ t ∘⟨ p₄ ⟩ t ∘⟨ 𝟘 ⟩ rfl ≡
    rfl ∷ Id (Erased (level l) A) [ t ] ([ t ])

------------------------------------------------------------------------
-- Some simple lemmas

opaque

  -- If Has-[]-cong holds, then Level is allowed.

  Has-[]-cong→Level-allowed :
    Has-[]-cong s m Δ p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ q₅ → Level-allowed
  Has-[]-cong→Level-allowed (_ , _ , ⊢[]-cong) =
    let ⊢Level , _ = inversion-ΠΣ (wf-⊢ ⊢[]-cong) in
    inversion-Level-⊢ ⊢Level

opaque

  -- If Has-[]-cong-for-level holds for l, then l is well-formed.

  Has-[]-cong-for-level→⊢∷L :
    Has-[]-cong-for-level s m Δ l p₁ q₁ p₂ q₂ p₃ q₃ q₄ →
    ε » Δ ⊢ l ∷Level
  Has-[]-cong-for-level→⊢∷L (_ , _ , ⊢[]-cong) =
    let ⊢U , _ = inversion-ΠΣ (wf-⊢ ⊢[]-cong) in
    inversion-U-Level ⊢U

opaque

  -- If Has-[]-cong-for-level holds for s, then Erased s is allowed.

  Has-[]-cong-for-level→Erased-allowed :
    Has-[]-cong-for-level s m Δ l p₁ q₁ p₂ q₂ p₃ q₃ q₄ →
    Erased-allowed s
  Has-[]-cong-for-level→Erased-allowed (_ , _ , ⊢[]-cong) =
    inversion-Erased
      (inversion-Id
         (inversion-ΠΣ
            (inversion-ΠΣ
               (inversion-ΠΣ
                  (inversion-ΠΣ (wf-⊢ ⊢[]-cong) .proj₂ .proj₁)
                  .proj₂ .proj₁)
               .proj₂ .proj₁)
            .proj₂ .proj₁)
         .proj₁)
      .proj₁

opaque

  -- Has-[]-cong implies Has-[]-cong-for-level, given certain
  -- assumptions.

  Has-[]-cong→Has-[]-cong-for-level :
    ε » Δ ⊢ level t ∷Level →
    𝟘ᶜ ▸[ m ᵐ· p₁ ] t →
    Has-[]-cong s m Δ p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ q₅ →
    Has-[]-cong-for-level s m Δ (level t) p₂ q₂ p₃ q₃ p₄ q₄ q₅
  Has-[]-cong→Has-[]-cong-for-level
    {t} {p₁} {s} {p₂} {q₂} {p₃} {q₃} {p₄} {q₄} {q₅}
    ⊢t ▸t has-[]-cong@([]-cong′ , ▸[]-cong′ , ⊢[]-cong′) =
    let ok = Has-[]-cong→Level-allowed has-[]-cong in
    []-cong′ ∘⟨ p₁ ⟩ t ,
    (sub
       (▸[]-cong′ ∘ₘ ▸t) $ begin
       𝟘ᶜ              ≈˘⟨ +ᶜ-identityʳ _ ⟩
       𝟘ᶜ +ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-congˡ (·ᶜ-zeroʳ _) ⟩
       𝟘ᶜ +ᶜ p₁ ·ᶜ 𝟘ᶜ  ∎) ,
    (PE.subst (_⊢_∷_ _ _)
       (PE.cong (Π p₂ , q₂ ▷_▹_ _) $
        PE.cong (Π p₃ , q₃ ▷_▹_ _) $
        PE.cong (Π p₄ , q₄ ▷_▹_ _) $
        PE.cong (Π 𝟘  , q₅ ▷_▹_ _) $
        PE.trans (PE.sym Id-Erased-[]) $
        PE.cong₃ Id
          (PE.cong (flip Erased _) wk[]≡wk[]′) PE.refl PE.refl) $
     ⊢[]-cong′ ∘ⱼ ⊢∷Level→⊢∷Level ok ⊢t)
    where
    open ≤ᶜ-reasoning
    open Erased s

opaque

  -- Has-[]-cong-for-level implies Has-[]-cong-for-type, given
  -- certain assumptions.

  Has-[]-cong-for-level→Has-[]-cong-for-type :
    ε » Δ ⊢ A ∷ U l →
    𝟘ᶜ ▸[ m ᵐ· p₁ ] A →
    Has-[]-cong-for-level s m Δ l p₁ q₁ p₂ q₂ p₃ q₃ q₄ →
    Has-[]-cong-for-type s m Δ l A p₂ q₂ p₃ q₃ q₄
  Has-[]-cong-for-level→Has-[]-cong-for-type
    {A} {l} {p₁} {s} {p₂} {q₂} {p₃} {q₃} {q₄}
    ⊢A ▸A has-[]-cong@([]-cong′ , ▸[]-cong′ , ⊢[]-cong′) =
    []-cong′ ∘⟨ p₁ ⟩ A ,
    (sub
       (▸[]-cong′ ∘ₘ ▸A) $ begin
       𝟘ᶜ              ≈˘⟨ +ᶜ-identityʳ _ ⟩
       𝟘ᶜ +ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-congˡ (·ᶜ-zeroʳ _) ⟩
       𝟘ᶜ +ᶜ p₁ ·ᶜ 𝟘ᶜ  ∎) ,
    (PE.subst (_⊢_∷_ _ _)
       (PE.cong  (Π p₂ , q₂ ▷_▹_ _) $
        PE.cong  (Π p₃ , q₃ ▷_▹_ _) $
        PE.cong₂ (Π 𝟘  , q₄ ▷_▹_)
          (PE.cong₃ Id wk[]≡wk[]′ PE.refl PE.refl) $
        PE.trans (PE.sym Id-Erased-[]) $
        PE.cong₃ Id
          (PE.cong₂ Erased
             (PE.trans (subst-wk l) $
              PE.sym (wk≡subst _ _))
             wk[]≡wk[]′)
          PE.refl PE.refl) $
     ⊢[]-cong′ ∘ⱼ ⊢A)
    where
    open ≤ᶜ-reasoning
    open Erased s

opaque

  -- Has-[]-cong implies Has-[]-cong-for-type, given certain
  -- assumptions.

  Has-[]-cong→Has-[]-cong-for-type :
    𝟘ᶜ ▸[ m ᵐ· p₁ ] t →
    𝟘ᶜ ▸[ m ᵐ· p₂ ] A →
    ε » Δ ⊢ A ∷ U (level t) →
    Has-[]-cong s m Δ p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ q₅ →
    Has-[]-cong-for-type s m Δ (level t) A p₃ q₃ p₄ q₄ q₅
  Has-[]-cong→Has-[]-cong-for-type ▸t ▸A ⊢A =
    Has-[]-cong-for-level→Has-[]-cong-for-type ⊢A ▸A ∘→
    Has-[]-cong→Has-[]-cong-for-level (inversion-U-Level (wf-⊢ ⊢A)) ▸t

opaque

  -- Has-[]-cong-for-type implies Has-[]-cong-for-value, given certain
  -- assumptions.

  Has-[]-cong-for-type→Has-[]-cong-for-value :
    ε » Δ ⊢ t ∷ A →
    𝟘ᶜ ▸[ m ᵐ· p₁ ] t →
    Has-[]-cong-for-type s m Δ l A p₁ q₁ p₂ q₂ q₃ →
    Has-[]-cong-for-value s m Δ l A t p₂ q₂ q₃
  Has-[]-cong-for-type→Has-[]-cong-for-value
    {t} {p₁} {s} {p₂} {q₂} {q₃}
    ⊢t ▸t has-[]-cong@([]-cong′ , ▸[]-cong′ , ⊢[]-cong′) =
    []-cong′ ∘⟨ p₁ ⟩ t ,
    (sub
       (▸[]-cong′ ∘ₘ ▸t) $ begin
       𝟘ᶜ              ≈˘⟨ +ᶜ-identityʳ _ ⟩
       𝟘ᶜ +ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-congˡ (·ᶜ-zeroʳ _) ⟩
       𝟘ᶜ +ᶜ p₁ ·ᶜ 𝟘ᶜ  ∎) ,
    (PE.subst (_⊢_∷_ _ _)
       (PE.cong₂ (Π p₂ , q₂ ▷_▹_) (wk1-sgSubst _ _) $
        PE.cong₂ (Π 𝟘  , q₃ ▷_▹_)
          (PE.cong₃ Id wk[+1]′-[₀⇑]≡ PE.refl PE.refl) $
        PE.trans (PE.sym Id-Erased-[]) $
        PE.cong₃ Id (PE.cong₂ Erased wk[+1]′-[₀⇑]≡ wk[+1]′-[₀⇑]≡)
          (PE.cong [_] wk[]≡wk[]′) PE.refl) $
     ⊢[]-cong′ ∘ⱼ ⊢t)
    where
    open ≤ᶜ-reasoning
    open Erased s

opaque

  -- Has-[]-cong-for-level implies Has-[]-cong-for-value, given
  -- certain assumptions.

  Has-[]-cong-for-level→Has-[]-cong-for-value :
    𝟘ᶜ ▸[ m ᵐ· p₁ ] A →
    𝟘ᶜ ▸[ m ᵐ· p₂ ] t →
    ε » Δ ⊢ A ∷ U l →
    ε » Δ ⊢ t ∷ A →
    Has-[]-cong-for-level s m Δ l p₁ q₁ p₂ q₂ p₃ q₃ q₄ →
    Has-[]-cong-for-value s m Δ l A t p₃ q₃ q₄
  Has-[]-cong-for-level→Has-[]-cong-for-value ▸A ▸t ⊢A ⊢t =
    Has-[]-cong-for-type→Has-[]-cong-for-value ⊢t ▸t ∘→
    Has-[]-cong-for-level→Has-[]-cong-for-type ⊢A ▸A

opaque

  -- Has-[]-cong implies Has-[]-cong-for-value, given certain
  -- assumptions.

  Has-[]-cong→Has-[]-cong-for-value :
    𝟘ᶜ ▸[ m ᵐ· p₁ ] t →
    𝟘ᶜ ▸[ m ᵐ· p₂ ] A →
    𝟘ᶜ ▸[ m ᵐ· p₃ ] u →
    ε » Δ ⊢ A ∷ U (level t) →
    ε » Δ ⊢ u ∷ A →
    Has-[]-cong s m Δ p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ q₅ →
    Has-[]-cong-for-value s m Δ (level t) A u p₄ q₄ q₅
  Has-[]-cong→Has-[]-cong-for-value ▸t ▸A ▸u ⊢A ⊢u =
    Has-[]-cong-for-type→Has-[]-cong-for-value ⊢u ▸u ∘→
    Has-[]-cong→Has-[]-cong-for-type ▸t ▸A ⊢A
