------------------------------------------------------------------------
-- Substitution operations used by Definition.Typed.Decidable.Internal
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality
open import Graded.Mode

module Definition.Typed.Decidable.Internal.Substitution
  {a a′} {M : Set a} {Mode : Set a′}
  {𝕄 : Modality M}
  (𝐌 : IsMode Mode 𝕄)
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Decidable.Internal.Monad 𝐌 R
import Definition.Typed.Decidable.Internal.Substitution.Primitive
open import Definition.Typed.Decidable.Internal.Term 𝐌 R
open import Definition.Typed.Decidable.Internal.Weakening 𝐌 R
open import Definition.Typed.Inversion R
open import Definition.Typed.Well-formed R

open import Definition.Untyped M as U
  using (Infinite; Level-literal; Term-kind; Wk)
open import Definition.Untyped.Allowed-literal R
open import Definition.Untyped.Properties M hiding (is-var?)
import Definition.Untyped.Sup R as S

open Term-kind
open Wk

open import Tools.Bool
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.List using (List)
import Tools.Maybe as M
open import Tools.Nat
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum

open Definition.Typed.Decidable.Internal.Substitution.Primitive 𝐌 R public

private variable
  b b₁ b₂                         : Bool
  α m n n′ n₁ n₂                  : Nat
  x                               : Fin _
  st                              : List _
  c                               : Constants
  γ γ′                            : Contexts _
  Γ                               : U.Cons _ _
  A′                              : U.Term _
  p q r                           : Termᵍ _
  s                               : Termˢ _
  bm                              : Termᵇᵐ _ _
  A A₁ A₂ l l₁ l₂ t t₁ t₂ t₃ t₄ u : Term[ _ , _ ] _
  k                               : Term-kind
  ρ                               : Wk _ _
  σ σ₁ σ₂                         : Subst _ _ _

------------------------------------------------------------------------
-- Applying substitutions to terms

-- Substitution (lazy): This operation applies the substitution by
-- pushing it just below the term's top-level constructor (unless the
-- term is a variable).

infix 25 _[_]

_[_] : Term[ c , k ] n₁ → Subst c n₂ n₁ → Term[ c , k ] n₂
meta-var x σ′         [ σ ] = meta-var x (σ ₛ•ₛ σ′)
weaken ρ t            [ σ ] = subst t (σ ₛ• ρ)
subst t σ′            [ σ ] = subst t (σ ₛ•ₛ σ′)
var x                 [ σ ] = x [ σ ]ᵛ
defn α                [ σ ] = defn α
Level                 [ _ ] = Level
zeroᵘ                 [ _ ] = zeroᵘ
1ᵘ+ t                 [ σ ] = 1ᵘ+ (subst t σ)
l₁ supᵘₗ l₂           [ σ ] = subst l₁ σ supᵘₗ subst l₂ σ
ωᵘ+ m                 [ _ ] = ωᵘ+ m
level t               [ σ ] = level (subst t σ)
U l                   [ σ ] = U (subst l σ)
Lift l A              [ σ ] = Lift (subst l σ) (subst A σ)
lift l t              [ σ ] = lift (flip subst σ M.<$> l) (subst t σ)
lower t               [ σ ] = lower (subst t σ)
Empty                 [ σ ] = Empty
emptyrec p A t        [ σ ] = emptyrec p (subst A σ) (subst t σ)
Unit s                [ σ ] = Unit s
star s                [ σ ] = star s
unitrec p q A t u     [ σ ] = unitrec p q (subst A (σ ⇑)) (subst t σ)
                                (subst u σ)
ΠΣ⟨ b ⟩ p , q ▷ A ▹ B [ σ ] = ΠΣ⟨ b ⟩ p , q ▷ subst A σ ▹ subst B (σ ⇑)
lam p qA t            [ σ ] = lam p (Σ.map idᶠ (flip subst σ) M.<$> qA)
                                (subst t (σ ⇑))
t ∘⟨ p ⟩ u            [ σ ] = subst t σ ∘⟨ p ⟩ subst u σ
prod s p qB t u       [ σ ] = prod s p
                                (Σ.map idᶠ (flip subst (σ ⇑)) M.<$> qB)
                                (subst t σ) (subst u σ)
fst p t               [ σ ] = fst p (subst t σ)
snd p t               [ σ ] = snd p (subst t σ)
prodrec r p q A t u   [ σ ] = prodrec r p q (subst A (σ ⇑)) (subst t σ)
                                (subst u (σ ⇑[ 2 ]))
ℕ                     [ σ ] = ℕ
zero                  [ σ ] = zero
suc t                 [ σ ] = suc (subst t σ)
natrec p q r A t u v  [ σ ] = natrec p q r (subst A (σ ⇑)) (subst t σ)
                                (subst u (σ ⇑[ 2 ])) (subst v σ)
Id A t u              [ σ ] = Id (subst A σ) (subst t σ) (subst u σ)
rfl t                 [ σ ] = rfl (flip subst σ M.<$> t)
J p q A t B u v w     [ σ ] = J p q (subst A σ) (subst t σ)
                                (subst B (σ ⇑[ 2 ])) (subst u σ)
                                (subst v σ) (subst w σ)
K p A t B u v         [ σ ] = K p (subst A σ) (subst t σ)
                                (subst B (σ ⇑)) (subst u σ) (subst v σ)
[]-cong s l A t u v   [ σ ] = []-cong s (subst l σ) (subst A σ)
                                (subst t σ) (subst u σ) (subst v σ)

------------------------------------------------------------------------
-- A lemma about level literals

opaque

  -- If ⌜ subst t σ ⌝ γ is a level literal, then ⌜ t [ σ ] ⌝ γ is a
  -- level literal.

  Level-literal-⌜[]⌝ :
    (t : Term[ c , k ] n) →
    Level-literal (⌜ subst t σ ⌝ γ) → Level-literal (⌜ t [ σ ] ⌝ γ)
  Level-literal-⌜[]⌝ {σ} {γ} (meta-var x σ′) =
    Level-literal (⌜ meta-var x σ′ ⌝ γ U.[ ⌜ σ ⌝ˢ γ ])       ≡⟨ PE.cong (Level-literal ∘→ U._[ _ ]) (⌜meta-var⌝ σ′) ⟩→
    Level-literal (⌜ x ⌝ᵐ γ U.[ ⌜ σ′ ⌝ˢ γ ] U.[ ⌜ σ ⌝ˢ γ ])  ≡⟨ PE.cong Level-literal (substCompEq (⌜ _ ⌝ᵐ γ)) ⟩→
    Level-literal (⌜ x ⌝ᵐ γ U.[ ⌜ σ ⌝ˢ γ U.ₛ•ₛ ⌜ σ′ ⌝ˢ γ ])  ≡⟨ PE.cong Level-literal (PE.sym (substVar-to-subst (⌜ₛ•ₛ⌝ˢ σ) (⌜ _ ⌝ᵐ γ))) ⟩→
    Level-literal (⌜ x ⌝ᵐ γ U.[ ⌜ σ ₛ•ₛ σ′ ⌝ˢ γ ])           ≡⟨ PE.cong Level-literal (PE.sym (⌜meta-var⌝ (σ ₛ•ₛ σ′))) ⟩→
    Level-literal (⌜ meta-var x (σ ₛ•ₛ σ′) ⌝ γ)              □
  Level-literal-⌜[]⌝ {σ} {γ} (weaken ρ t) =
    Level-literal (U.wk ρ (⌜ t ⌝ γ) U.[ ⌜ σ ⌝ˢ γ ])  ≡⟨ PE.cong Level-literal (subst-wk (⌜ t ⌝ _)) ⟩→
    Level-literal (⌜ t ⌝ γ U.[ ⌜ σ ⌝ˢ γ U.ₛ• ρ ])    ≡⟨ PE.cong Level-literal (PE.sym (substVar-to-subst (⌜ₛ•⌝ˢ σ) (⌜ t ⌝ _))) ⟩→
    Level-literal (⌜ t ⌝ γ U.[ ⌜ σ ₛ• ρ ⌝ˢ γ ])      □
  Level-literal-⌜[]⌝ {σ} {γ} (subst t σ′) =
    Level-literal (⌜ t ⌝ γ U.[ ⌜ σ′ ⌝ˢ γ ] U.[ ⌜ σ ⌝ˢ γ ])  ≡⟨ PE.cong Level-literal (substCompEq (⌜ t ⌝ _)) ⟩→
    Level-literal (⌜ t ⌝ γ U.[ ⌜ σ ⌝ˢ γ U.ₛ•ₛ ⌜ σ′ ⌝ˢ γ ])  ≡⟨ PE.cong Level-literal (PE.sym (substVar-to-subst (⌜ₛ•ₛ⌝ˢ σ) (⌜ t ⌝ _))) ⟩→
    Level-literal (⌜ t ⌝ γ U.[ ⌜ σ ₛ•ₛ σ′ ⌝ˢ γ ])           □
  Level-literal-⌜[]⌝ {σ} {γ} (var x) =
    Level-literal (⌜ σ ⌝ˢ γ x)      ≡⟨ PE.cong Level-literal (PE.sym (⌜[]ᵛ⌝ σ _)) ⟩→
    Level-literal (⌜ x [ σ ]ᵛ ⌝ γ)  □
  Level-literal-⌜[]⌝ zeroᵘ =
    idᶠ
  Level-literal-⌜[]⌝ {σ} {γ} (1ᵘ+ l) =
    Level-literal (U.1ᵘ+ (⌜ l ⌝ γ) U.[ ⌜ σ ⌝ˢ γ ])  ≡⟨ PE.cong Level-literal (1ᵘ+-[] (⌜ l ⌝ _)) ⟩→
    Level-literal (U.1ᵘ+ (⌜ l ⌝ γ U.[ ⌜ σ ⌝ˢ γ ]))  □
  Level-literal-⌜[]⌝ {σ} {γ} (l₁ supᵘₗ l₂) =
    Level-literal (⌜ l₁ ⌝ γ S.supᵘₗ ⌜ l₂ ⌝ γ U.[ ⌜ σ ⌝ˢ γ ])         →⟨ S.Level-literal-supᵘₗ-[]₂ ⟩

    Level-literal
      ((⌜ l₁ ⌝ γ U.[ ⌜ σ ⌝ˢ γ ]) S.supᵘₗ (⌜ l₂ ⌝ γ U.[ ⌜ σ ⌝ˢ γ ]))  □
  Level-literal-⌜[]⌝ (ωᵘ+ _) =
    idᶠ
  Level-literal-⌜[]⌝ (level _) =
    idᶠ
  Level-literal-⌜[]⌝ (defn _)                ()
  Level-literal-⌜[]⌝ Level                   ()
  Level-literal-⌜[]⌝ (U _)                   ()
  Level-literal-⌜[]⌝ (Lift _ _)              ()
  Level-literal-⌜[]⌝ (lift _ _)              ()
  Level-literal-⌜[]⌝ (lower _)               ()
  Level-literal-⌜[]⌝ Empty                   ()
  Level-literal-⌜[]⌝ (emptyrec _ _ _)        ()
  Level-literal-⌜[]⌝ (Unit _)                ()
  Level-literal-⌜[]⌝ (star _)                ()
  Level-literal-⌜[]⌝ (unitrec _ _ _ _ _)     ()
  Level-literal-⌜[]⌝ (ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _) ()
  Level-literal-⌜[]⌝ (lam _ _ _)             ()
  Level-literal-⌜[]⌝ (_ ∘⟨ _ ⟩ _)            ()
  Level-literal-⌜[]⌝ (prod _ _ _ _ _)        ()
  Level-literal-⌜[]⌝ (fst _ _)               ()
  Level-literal-⌜[]⌝ (snd _ _)               ()
  Level-literal-⌜[]⌝ (prodrec _ _ _ _ _ _)   ()
  Level-literal-⌜[]⌝ ℕ                       ()
  Level-literal-⌜[]⌝ zero                    ()
  Level-literal-⌜[]⌝ (suc _)                 ()
  Level-literal-⌜[]⌝ (natrec _ _ _ _ _ _ _)  ()
  Level-literal-⌜[]⌝ (Id _ _ _)              ()
  Level-literal-⌜[]⌝ (rfl _)                 ()
  Level-literal-⌜[]⌝ (J _ _ _ _ _ _ _ _)     ()
  Level-literal-⌜[]⌝ (K _ _ _ _ _ _)         ()
  Level-literal-⌜[]⌝ ([]-cong _ _ _ _ _ _)   ()

------------------------------------------------------------------------
-- Not-infinite, Literal-iff, Not-level-literal and Literal-free

-- Not-infinite l implies that the translation of l is definitely
-- not ωᵘ+ something.

data Not-infinite-level {c n} : Lvl c n → Set a where
  weaken   : Not-infinite-level l → Not-infinite-level (weaken ρ l)
  subst    : Not-infinite-level l → Not-infinite-level (subst l σ)
  1ᵘ+      : Not-infinite-level l → Not-infinite-level (1ᵘ+ l)
  sup      : Not-infinite-level l₁ → Not-infinite-level l₂ →
             Not-infinite-level (l₁ supᵘₗ l₂)
  level    : Not-infinite-level (level t)

-- Not-infinite l implies that the translation of l is definitely
-- not ωᵘ+ something.

data Not-infinite {c n} : Term[ c , k ] n → Set a where
  term  : Not-infinite {k = tm} t
  level : Not-infinite-level l → Not-infinite l

mutual

  -- Literal-iff t σ implies that, for any γ, ⌜ t ⌝ γ is a level
  -- literal if and only if ⌜ subst t σ ⌝ γ is a level literal.

  data Literal-iff : Term[ c , k ] n₁ → Subst c n₂ n₁ → Set a where
    literal-free : Literal-free σ → Literal-iff t σ
    meta-var     : ∀ {x} → Literal-free (σ₂ ₛ•ₛ σ₁) →
                   Literal-iff {k = k} (meta-var x σ₁) σ₂
    weaken       : Literal-iff t (σ ₛ• ρ) → Literal-iff (weaken ρ t) σ
    subst        : Literal-iff t (σ₂ ₛ•ₛ σ₁) →
                   Literal-iff (subst t σ₁) σ₂
    var          : Not-level-literal (x [ σ ]ᵛ) → Literal-iff (var x) σ
    defn         : Literal-iff (defn α) σ
    Level        : Literal-iff Level σ
    zeroᵘ        : Literal-iff zeroᵘ σ
    1ᵘ+          : Literal-iff l σ → Literal-iff (1ᵘ+ l) σ
    sup          : Literal-iff (l₁ supᵘₗ l₂) σ
    ωᵘ+          : Literal-iff (ωᵘ+ m) σ
    level        : Literal-iff t σ → Literal-iff (level t) σ
    U            : Literal-iff (U l) σ
    Lift         : Literal-iff (Lift l A) σ
    lift         : ∀ {l} → Literal-iff (lift l t) σ
    lower        : Literal-iff (lower t) σ
    Empty        : Literal-iff Empty σ
    emptyrec     : Literal-iff (emptyrec p A t) σ
    Unit         : Literal-iff (Unit s) σ
    star         : Literal-iff (star s) σ
    unitrec      : Literal-iff (unitrec p q A t₁ t₂) σ
    ΠΣ           : Literal-iff (ΠΣ⟨ bm ⟩ p , q ▷ A₁ ▹ A₂) σ
    lam          : ∀ {qA} → Literal-iff (lam p qA t) σ
    app          : Literal-iff (t₁ ∘⟨ p ⟩ t₂) σ
    prod         : ∀ {qB} → Literal-iff (prod s p qB t₁ t₂) σ
    fst          : Literal-iff (fst p t) σ
    snd          : Literal-iff (snd p t) σ
    prodrec      : Literal-iff (prodrec r p q A t₁ t₂) σ
    ℕ            : Literal-iff ℕ σ
    zero         : Literal-iff zero σ
    suc          : Literal-iff (suc t) σ
    natrec       : Literal-iff (natrec p q r A t₁ t₂ t₃) σ
    Id           : Literal-iff (Id A t₁ t₂) σ
    rfl          : ∀ {t} → Literal-iff (rfl t) σ
    J            : Literal-iff (J p q A₁ t₁ A₂ t₂ t₃ t₄) σ
    K            : Literal-iff (K p A₁ t₁ A₂ t₂ t₃) σ
    []-cong      : Literal-iff ([]-cong s l A t₁ t₂ t₃) σ

  -- Not-level-literal t implies that the translation of t is
  -- definitely not a level literal.

  data Not-level-literal {c n} : Term[ c , k ] n → Set a where
    weaken   : Not-level-literal t →
               Not-level-literal (weaken ρ t)
    subst    : Literal-iff t σ → Not-level-literal t →
               Not-level-literal (subst t σ)
    var      : Not-level-literal (var x)
    defn     : Not-level-literal (defn α)
    Level    : Not-level-literal Level
    1ᵘ+      : Not-level-literal l → Not-level-literal (1ᵘ+ l)
    supᵘₗˡ   : Not-level-literal l₁ → Not-infinite l₂ →
               Not-level-literal (l₁ supᵘₗ l₂)
    supᵘₗʳ   : Not-infinite l₁ → Not-level-literal l₂ →
               Not-level-literal (l₁ supᵘₗ l₂)
    level    : Not-level-literal t → Not-level-literal (level t)
    U        : Not-level-literal (U l)
    Lift     : Not-level-literal (Lift l A)
    lift     : ∀ {l} → Not-level-literal (lift l t)
    lower    : Not-level-literal (lower t)
    Empty    : Not-level-literal Empty
    emptyrec : Not-level-literal (emptyrec p A t)
    Unit     : Not-level-literal (Unit s)
    star     : Not-level-literal (star s)
    unitrec  : Not-level-literal (unitrec p q A t₁ t₂)
    ΠΣ       : Not-level-literal (ΠΣ⟨ bm ⟩ p , q ▷ A₁ ▹ A₂)
    lam      : ∀ {qA} → Not-level-literal (lam p qA t)
    app      : Not-level-literal (t₁ ∘⟨ p ⟩ t₂)
    prod     : ∀ {qB} → Not-level-literal (prod s p qB t₁ t₂)
    fst      : Not-level-literal (fst p t)
    snd      : Not-level-literal (snd p t)
    prodrec  : Not-level-literal (prodrec r p q A t₁ t₂)
    ℕ        : Not-level-literal ℕ
    zero     : Not-level-literal zero
    suc      : Not-level-literal (suc t)
    natrec   : Not-level-literal (natrec p q r A t₁ t₂ t₃)
    Id       : Not-level-literal (Id A t₁ t₂)
    rfl      : ∀ {t} → Not-level-literal (rfl t)
    J        : Not-level-literal (J p q A₁ t₁ A₂ t₂ t₃ t₄)
    K        : Not-level-literal (K p A₁ t₁ A₂ t₂ t₃)
    []-cong  : Not-level-literal ([]-cong s l A t₁ t₂ t₃)

  -- Literal-free σ implies that, for any term t in σ, the translation
  -- of t is definitely not a level literal.

  infix 35 _⇑

  data Literal-free {c} : Subst c n₂ n₁ → Set a where
    id   : Literal-free (id {n = n})
    wk1  : Literal-free σ → Literal-free (wk1 σ)
    _⇑   : Literal-free σ → Literal-free (σ ⇑)
    cons : Literal-free σ → Not-level-literal t →
           Literal-free (cons σ t)

opaque

  -- If Not-infinite-level l holds, then ⌜ l ⌝ γ is not infinite.

  Not-infinite-level→¬Infinite :
    Not-infinite-level l → ¬ Infinite (⌜ l ⌝ γ)
  Not-infinite-level→¬Infinite {γ} = λ where
    (weaken {l} {ρ} nω) →
      Infinite (U.wk ρ (⌜ l ⌝ γ))  ⇔⟨ Infinite-wk-⇔ ⟩→
      Infinite (⌜ l ⌝ γ)           →⟨ Not-infinite-level→¬Infinite nω ⟩
      ⊥                            □
    (subst {l} {σ} nω) →
      Infinite (⌜ l ⌝ γ U.[ ⌜ σ ⌝ˢ γ ])  ⇔⟨ Infinite-[]-⇔ ⟩→
      Infinite (⌜ l ⌝ γ)                 →⟨ Not-infinite-level→¬Infinite nω ⟩
      ⊥                                  □
    (1ᵘ+ {l} nω) →
      Infinite (U.1ᵘ+ (⌜ l ⌝ γ))  ⇔⟨ Infinite-1ᵘ+-⇔ ⟩→
      Infinite (⌜ l ⌝ γ)          →⟨ Not-infinite-level→¬Infinite nω ⟩
      ⊥                           □
    (sup {l₁} {l₂} nω₁ nω₂) →
      Infinite (⌜ l₁ ⌝ γ S.supᵘₗ ⌜ l₂ ⌝ γ)       ⇔⟨ S.Infinite-supᵘₗ-⇔ ⟩→
      Infinite (⌜ l₁ ⌝ γ) ⊎ Infinite (⌜ l₂ ⌝ γ)  →⟨ (λ where
                                                       (inj₁ inf) → Not-infinite-level→¬Infinite nω₁ inf
                                                       (inj₂ inf) → Not-infinite-level→¬Infinite nω₂ inf) ⟩
      ⊥                                          □
    (level {t}) →
      Infinite (U.level (⌜ t ⌝ γ))  →⟨ (λ ()) ⟩
      ⊥                             □

opaque

  -- If Not-infinite l holds, then ⌜ l ⌝ γ is not infinite.

  Not-infinite→¬Infinite : Not-infinite l → ¬ Infinite (⌜ l ⌝ γ)
  Not-infinite→¬Infinite term       = λ ()
  Not-infinite→¬Infinite (level nω) = Not-infinite-level→¬Infinite nω

opaque mutual

  -- If Literal-iff t σ holds, then ⌜ t ⌝ γ is a level literal if and
  -- only if ⌜ subst t σ ⌝ γ is a level literal.

  Literal-iff→⇔Level-literal-⌜subst⌝ :
    Literal-iff t σ →
    Level-literal (⌜ t ⌝ γ) ⇔ Level-literal (⌜ subst t σ ⌝ γ)
  Literal-iff→⇔Level-literal-⌜subst⌝ {γ} iff =
    Level-literal-[] , lemma iff
    where
    lemma :
      Literal-iff t σ → Level-literal (⌜ subst t σ ⌝ γ) →
      Level-literal (⌜ t ⌝ γ)
    lemma (literal-free {σ} {t} cf) =
      Level-literal (⌜ t ⌝ γ U.[ ⌜ σ ⌝ˢ γ ])  ⇔˘⟨ Literal-free→⇔Level-literal-[⌜⌝ˢ] cf ⟩→
      Level-literal (⌜ t ⌝ γ)                 □
    lemma (meta-var {σ₂} {σ₁} {x} cf) =
      Level-literal (⌜ meta-var x σ₁ ⌝ γ U.[ ⌜ σ₂ ⌝ˢ γ ])       ≡⟨ PE.cong (Level-literal ∘→ U._[ _ ]) (⌜meta-var⌝ σ₁) ⟩→
      Level-literal (⌜ x ⌝ᵐ γ U.[ ⌜ σ₁ ⌝ˢ γ ] U.[ ⌜ σ₂ ⌝ˢ γ ])  ≡⟨ PE.cong Level-literal (substCompEq (⌜ _ ⌝ᵐ γ)) ⟩→
      Level-literal (⌜ x ⌝ᵐ γ U.[ ⌜ σ₂ ⌝ˢ γ U.ₛ•ₛ ⌜ σ₁ ⌝ˢ γ ])  ≡⟨ PE.cong Level-literal (PE.sym (substVar-to-subst (⌜ₛ•ₛ⌝ˢ σ₂) (⌜ _ ⌝ᵐ γ))) ⟩→
      Level-literal (⌜ x ⌝ᵐ γ U.[ ⌜ σ₂ ₛ•ₛ σ₁ ⌝ˢ γ ])           ⇔˘⟨ Literal-free→⇔Level-literal-[⌜⌝ˢ] cf ⟩→
      Level-literal (⌜ x ⌝ᵐ γ)                                  →⟨ Level-literal-[] ⟩
      Level-literal (⌜ x ⌝ᵐ γ U.[ ⌜ σ₁ ⌝ˢ γ ])                  ≡⟨ PE.cong Level-literal (PE.sym (⌜meta-var⌝ σ₁)) ⟩→
      Level-literal (⌜ meta-var x σ₁ ⌝ γ)                       □
    lemma (weaken {t} {σ} {ρ} iff) =
      Level-literal (U.wk ρ (⌜ t ⌝ γ) U.[ ⌜ σ ⌝ˢ γ ])  ≡⟨ PE.cong Level-literal (subst-wk (⌜ t ⌝ _)) ⟩→
      Level-literal (⌜ t ⌝ γ U.[ ⌜ σ ⌝ˢ γ U.ₛ• ρ ])    ≡⟨ PE.cong Level-literal (PE.sym (substVar-to-subst (⌜ₛ•⌝ˢ σ) (⌜ t ⌝ _))) ⟩→
      Level-literal (⌜ t ⌝ γ U.[ ⌜ σ ₛ• ρ ⌝ˢ γ ])      →⟨ lemma iff ⟩
      Level-literal (⌜ t ⌝ γ)                          →⟨ wk-Level-literal .proj₁ ⟩
      Level-literal (U.wk ρ (⌜ t ⌝ γ))                 □
    lemma (subst {t} {σ₂} {σ₁} iff) =
      Level-literal (⌜ t ⌝ γ U.[ ⌜ σ₁ ⌝ˢ γ ] U.[ ⌜ σ₂ ⌝ˢ γ ])  ≡⟨ PE.cong Level-literal (substCompEq (⌜ t ⌝ _)) ⟩→
      Level-literal (⌜ t ⌝ γ U.[ ⌜ σ₂ ⌝ˢ γ U.ₛ•ₛ ⌜ σ₁ ⌝ˢ γ ])  ≡⟨ PE.cong Level-literal (PE.sym (substVar-to-subst (⌜ₛ•ₛ⌝ˢ σ₂) (⌜ t ⌝ _))) ⟩→
      Level-literal (⌜ t ⌝ γ U.[ ⌜ σ₂ ₛ•ₛ σ₁ ⌝ˢ γ ])           →⟨ lemma iff ⟩
      Level-literal (⌜ t ⌝ γ)                                  →⟨ Level-literal-[] ⟩
      Level-literal (⌜ t ⌝ γ U.[ ⌜ σ₁ ⌝ˢ γ ])                  □
    lemma (var {x} {σ} nll) =
      Level-literal (⌜ σ ⌝ˢ γ x)      ≡⟨ PE.cong Level-literal (PE.sym (⌜[]ᵛ⌝ σ _)) ⟩→
      Level-literal (⌜ x [ σ ]ᵛ ⌝ γ)  →⟨ Not-level-literal→¬Level-literal nll ⟩
      ⊥                               →⟨ ⊥-elim ⟩
      Level-literal (⌜ var x ⌝ γ)     □
    lemma defn  ()
    lemma Level ()
    lemma zeroᵘ =
      Level-literal U.zeroᵘ  →⟨ (λ _ → U.zeroᵘ) ⟩
      Level-literal U.zeroᵘ  □
    lemma (1ᵘ+ {l} {σ} iff) =
      Level-literal (U.1ᵘ+ (⌜ l ⌝ γ) U.[ ⌜ σ ⌝ˢ γ ])  ≡⟨ PE.cong Level-literal (1ᵘ+-[] (⌜ l ⌝ _)) ⟩→
      Level-literal (U.1ᵘ+ (⌜ l ⌝ γ U.[ ⌜ σ ⌝ˢ γ ]))  ⇔⟨ Level-literal-1ᵘ+-⇔ ⟩→
      Level-literal (⌜ l ⌝ γ U.[ ⌜ σ ⌝ˢ γ ])          →⟨ lemma iff ⟩
      Level-literal (⌜ l ⌝ γ)                         ⇔˘⟨ Level-literal-1ᵘ+-⇔ ⟩→
      Level-literal (U.1ᵘ+ (⌜ l ⌝ γ))                 □
    lemma (sup {l₁} {l₂} {σ}) =
      Level-literal (⌜ subst (l₁ supᵘₗ l₂) σ ⌝ γ)  →⟨ S.Level-literal-supᵘₗ-[]₁ ⟩
      Level-literal (⌜ l₁ supᵘₗ l₂ ⌝ γ)            □
    lemma (ωᵘ+ {m}) =
      Level-literal (U.ωᵘ+ m)  →⟨ (λ _ → U.ωᵘ+) ⟩
      Level-literal (U.ωᵘ+ m)  □
    lemma (level {t} {σ} iff) =
      Level-literal (U.level (⌜ t ⌝ γ U.[ ⌜ σ ⌝ˢ γ ]))  ⇔⟨ Level-literal-level-⇔ ⟩→
      Level-literal (⌜ t ⌝ γ U.[ ⌜ σ ⌝ˢ γ ])            →⟨ lemma iff ⟩
      Level-literal (⌜ t ⌝ γ)                           ⇔˘⟨ Level-literal-level-⇔ ⟩→
      Level-literal (U.level (⌜ t ⌝ γ))                 □
    lemma U        ()
    lemma Lift     ()
    lemma lift     ()
    lemma lower    ()
    lemma Empty    ()
    lemma emptyrec ()
    lemma Unit     ()
    lemma star     ()
    lemma unitrec  ()
    lemma ΠΣ       ()
    lemma lam      ()
    lemma app      ()
    lemma prod     ()
    lemma fst      ()
    lemma snd      ()
    lemma prodrec  ()
    lemma ℕ        ()
    lemma zero     ()
    lemma suc      ()
    lemma natrec   ()
    lemma Id       ()
    lemma rfl      ()
    lemma J        ()
    lemma K        ()
    lemma []-cong  ()

  -- If Not-level-literal t holds, then ⌜ t ⌝ γ is not a level
  -- literal.

  Not-level-literal→¬Level-literal :
    Not-level-literal t → ¬ Level-literal (⌜ t ⌝ γ)
  Not-level-literal→¬Level-literal {γ} = λ where
    (weaken {t} {ρ} nl) →
      Level-literal (U.wk ρ (⌜ t ⌝ γ))  ⇔˘⟨ wk-Level-literal ⟩→
      Level-literal (⌜ t ⌝ γ)           →⟨ Not-level-literal→¬Level-literal nl ⟩
      ⊥                                 □
    (subst {t} {σ} iff nl) →
      Level-literal (⌜ subst t σ ⌝ γ)  ⇔˘⟨ Literal-iff→⇔Level-literal-⌜subst⌝ iff ⟩→
      Level-literal (⌜ t ⌝ γ)          →⟨ Not-level-literal→¬Level-literal nl ⟩
      ⊥                                □
    (1ᵘ+ {l} nl) →
      Level-literal (U.1ᵘ+ (⌜ l ⌝ γ))  ⇔⟨ Level-literal-1ᵘ+-⇔ ⟩→
      Level-literal (⌜ l ⌝ γ)          →⟨ Not-level-literal→¬Level-literal nl ⟩
      ⊥                                □
    (supᵘₗˡ {l₁} {l₂} nl nω) →
      Level-literal (⌜ l₁ ⌝ γ S.supᵘₗ ⌜ l₂ ⌝ γ)     ⇔⟨ S.Level-literal-supᵘₗ-⇔′ ⟩→

      Infinite (⌜ l₁ ⌝ γ) ⊎ Infinite (⌜ l₂ ⌝ γ) ⊎
      ¬ Level-allowed × Level-literal (⌜ l₁ ⌝ γ) ×
      Level-literal (⌜ l₂ ⌝ γ)                      →⟨ (λ where
                                                          (inj₁ inf₁) →
                                                            Infinite→Level-literal inf₁
                                                          (inj₂ (inj₁ inf₂)) →
                                                            ⊥-elim (Not-infinite→¬Infinite nω inf₂)
                                                          (inj₂ (inj₂ (_ , lit , _))) →
                                                            lit) ⟩

      Level-literal (⌜ l₁ ⌝ γ)                      →⟨ Not-level-literal→¬Level-literal nl ⟩

      ⊥                                             □
    (supᵘₗʳ {l₁} {l₂} nω nl) →
      Level-literal (⌜ l₁ ⌝ γ S.supᵘₗ ⌜ l₂ ⌝ γ)     ⇔⟨ S.Level-literal-supᵘₗ-⇔′ ⟩→

      Infinite (⌜ l₁ ⌝ γ) ⊎ Infinite (⌜ l₂ ⌝ γ) ⊎
      ¬ Level-allowed × Level-literal (⌜ l₁ ⌝ γ) ×
      Level-literal (⌜ l₂ ⌝ γ)                      →⟨ (λ where
                                                          (inj₁ inf₁) →
                                                            ⊥-elim (Not-infinite→¬Infinite nω inf₁)
                                                          (inj₂ (inj₁ inf₂)) →
                                                            Infinite→Level-literal inf₂
                                                          (inj₂ (inj₂ (_ , _ , lit))) →
                                                            lit) ⟩

      Level-literal (⌜ l₂ ⌝ γ)                      →⟨ Not-level-literal→¬Level-literal nl ⟩

      ⊥                                             □
    (level {t} nl) →
      Level-literal (U.level (⌜ t ⌝ γ))  ⇔⟨ Level-literal-level-⇔ ⟩→
      Level-literal (⌜ t ⌝ γ)            →⟨ Not-level-literal→¬Level-literal nl ⟩
      ⊥                                  □

    var      ()
    defn     ()
    Level    ()
    U        ()
    Lift     ()
    lift     ()
    lower    ()
    Empty    ()
    emptyrec ()
    Unit     ()
    star     ()
    unitrec  ()
    ΠΣ       ()
    lam      ()
    app      ()
    prod     ()
    fst      ()
    snd      ()
    prodrec  ()
    ℕ        ()
    zero     ()
    suc      ()
    natrec   ()
    Id       ()
    rfl      ()
    J        ()
    K        ()
    []-cong  ()

  -- If σ is literal-free, then ⌜ σ ⌝ˢ γ x is not a level literal.

  Literal-free→¬Level-literal :
    Literal-free σ → ¬ Level-literal (⌜ σ ⌝ˢ γ x)
  Literal-free→¬Level-literal id ()
  Literal-free→¬Level-literal {γ} {x} (wk1 {σ} lf) =
    Level-literal (U.wk1 (⌜ σ ⌝ˢ γ x))  ⇔˘⟨ wk-Level-literal ⟩→
    Level-literal (⌜ σ ⌝ˢ γ x)          →⟨ Literal-free→¬Level-literal lf ⟩
    ⊥                                   □
  Literal-free→¬Level-literal {x = x0} (_ ⇑) ()
  Literal-free→¬Level-literal {γ} {x = x +1} (_⇑ {σ} lf) =
    Level-literal (U.wk1 (⌜ σ ⌝ˢ γ x))  ⇔˘⟨ wk-Level-literal ⟩→
    Level-literal (⌜ σ ⌝ˢ γ x)          →⟨ Literal-free→¬Level-literal lf ⟩
    ⊥                                   □
  Literal-free→¬Level-literal {γ} {x = x0} (cons {t} _ nll) =
    Level-literal (⌜ t ⌝ γ)  →⟨ Not-level-literal→¬Level-literal nll ⟩
    ⊥                        □
  Literal-free→¬Level-literal {γ} {x = x +1} (cons {σ} lf _) =
    Level-literal (⌜ σ ⌝ˢ γ x)  →⟨ Literal-free→¬Level-literal lf ⟩
    ⊥                           □

  -- If Literal-free σ holds, then t is a level literal if and only if
  -- t U.[ ⌜ σ ⌝ˢ γ ] is.

  Literal-free→⇔Level-literal-[⌜⌝ˢ] :
    {t : U.Term[ k ] n} →
    Literal-free σ →
    Level-literal t ⇔ Level-literal (t U.[ ⌜ σ ⌝ˢ γ ])
  Literal-free→⇔Level-literal-[⌜⌝ˢ] {n} {σ} {γ} lf =
    Level-literal-[] , lemma _ lf
    where
    lemma :
      (t : U.Term[ k ] n) → Literal-free σ →
      Level-literal (t U.[ ⌜ σ ⌝ˢ γ ]) → Level-literal t
    lemma (U.var x) lf =
      Level-literal (⌜ σ ⌝ˢ γ x)  →⟨ Literal-free→¬Level-literal lf ⟩
      ⊥                           →⟨ ⊥-elim ⟩
      Level-literal (U.var x)     □
    lemma U.zeroᵘ _ =
      Level-literal U.zeroᵘ  →⟨ (λ _ → U.zeroᵘ) ⟩
      Level-literal U.zeroᵘ  □
    lemma (U.sucᵘ l) lf =
      Level-literal (U.sucᵘ (l U.[ ⌜ σ ⌝ˢ γ ]))  →⟨ (λ { (U.sucᵘ l-lit) → l-lit }) ⟩
      Level-literal (l U.[ ⌜ σ ⌝ˢ γ ])           ⇔˘⟨ Literal-free→⇔Level-literal-[⌜⌝ˢ] lf ⟩→
      Level-literal l                            →⟨ U.sucᵘ ⟩
      Level-literal (U.sucᵘ l)                   □
    lemma (U.ωᵘ+ m) _ =
      Level-literal (U.ωᵘ+ m)  →⟨ (λ _ → U.ωᵘ+) ⟩
      Level-literal (U.ωᵘ+ m)  □
    lemma (U.level t) lf =
      Level-literal (U.level (t U.[ ⌜ σ ⌝ˢ γ ]))  ⇔⟨ Level-literal-level-⇔ ⟩→
      Level-literal (t U.[ ⌜ σ ⌝ˢ γ ])            ⇔˘⟨ Literal-free→⇔Level-literal-[⌜⌝ˢ] lf ⟩→
      Level-literal t                             ⇔˘⟨ Level-literal-level-⇔ ⟩→
      Level-literal (U.level t)                   □

    lemma (U.defn _)                _ ()
    lemma U.Level                   _ ()
    lemma (_ U.supᵘ _)              _ ()
    lemma (U.U _)                   _ ()
    lemma (U.Lift _ _)              _ ()
    lemma (U.lift _)                _ ()
    lemma (U.lower _)               _ ()
    lemma U.Empty                   _ ()
    lemma (U.emptyrec _ _ _)        _ ()
    lemma (U.Unit _)                _ ()
    lemma (U.star _)                _ ()
    lemma (U.unitrec _ _ _ _ _)     _ ()
    lemma (U.ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _) _ ()
    lemma (U.lam _ _)               _ ()
    lemma (_ U.∘⟨ _ ⟩ _)            _ ()
    lemma (U.prod _ _ _ _)          _ ()
    lemma (U.fst _ _)               _ ()
    lemma (U.snd _ _)               _ ()
    lemma (U.prodrec _ _ _ _ _ _)   _ ()
    lemma U.ℕ                       _ ()
    lemma U.zero                    _ ()
    lemma (U.suc _)                 _ ()
    lemma (U.natrec _ _ _ _ _ _ _)  _ ()
    lemma (U.Id _ _ _)              _ ()
    lemma U.rfl                     _ ()
    lemma (U.J _ _ _ _ _ _ _ _)     _ ()
    lemma (U.K _ _ _ _ _ _)         _ ()
    lemma (U.[]-cong _ _ _ _ _ _)   _ ()

opaque

  -- The substitution toSubst ρ is literal-free.

  Literal-free-toSubst :
    (ρ : Wk n₂ n₁) → Literal-free {c = c} (toSubst ρ)
  Literal-free-toSubst id       = id
  Literal-free-toSubst (step ρ) = wk1 (Literal-free-toSubst ρ)
  Literal-free-toSubst (lift ρ) = Literal-free-toSubst ρ ⇑

-- Checks if Not-infinite l holds.

not-infinite? : (l : Term[ c , k ] n) → Check c Bool
not-infinite? {k = tm} _ =
  return true
not-infinite? (weaken _ l) =
  not-infinite? l
not-infinite? (subst l _) =
  not-infinite? l
not-infinite? (1ᵘ+ l) =
  not-infinite? l
not-infinite? (l₁ supᵘₗ l₂) =
  and (not-infinite? l₁) (not-infinite? l₂)
not-infinite? (level _) =
  return true
not-infinite? _ =
  return false

opaque

  -- The function not-infinite? is sound.

  not-infinite?-sound :
    {l : Term[ c , k ] n} →
    OK (not-infinite? l) true γ st →
    Not-infinite l
  not-infinite?-sound {k = tm} ok! =
    term
  not-infinite?-sound {k = lvl} eq =
    level (not-infinite?-sound′ eq)
    where
    not-infinite?-sound′ :
      OK (not-infinite? l) true γ st →
      Not-infinite-level l
    not-infinite?-sound′ {l = meta-var _ _} not-ok
    not-infinite?-sound′ {l = weaken _ _}   eq     =
      weaken (not-infinite?-sound′ eq)
    not-infinite?-sound′ {l = subst _ _} eq =
      subst (not-infinite?-sound′ eq)
    not-infinite?-sound′ {l = 1ᵘ+ _} eq =
      1ᵘ+ (not-infinite?-sound′ eq)
    not-infinite?-sound′ {l = _ supᵘₗ _} eq =
      let eq₁ , eq₂ = inv-and eq in
      sup (not-infinite?-sound′ eq₁) (not-infinite?-sound′ eq₂)
    not-infinite?-sound′ {l = ωᵘ+ _}   not-ok
    not-infinite?-sound′ {l = level _} ok!    =
      level

mutual

  -- Checks if Literal-iff t σ holds.
  --
  -- If the last argument is true, then it is assumed that
  -- Literal-free σ does not hold.
  --
  -- Note the use of backtracking.
  --
  -- The implementation uses fuel. That is perhaps not necessary to
  -- ensure termination, but use of a termination measure could affect
  -- how the code computes at compile-time.

  literal-iff? :
    Fuel → (t : Term[ c , k ] n₁) (σ : Subst c n₂ n₁) → Bool →
    Check c Bool
  literal-iff? n (meta-var _ σ₁) σ₂ true =
    literal-free? n (σ₂ ₛ•ₛ σ₁)
  literal-iff? n (meta-var _ σ₁) σ₂ false =
    or (literal-free? n σ₂) (literal-free? n (σ₂ ₛ•ₛ σ₁))
  literal-iff? n (weaken ρ t) σ _ =
    literal-iff? n t (σ ₛ• ρ) false
  literal-iff? n (subst t σ₁) σ₂ true =
    literal-iff? n t (σ₂ ₛ•ₛ σ₁) false
  literal-iff? n (subst t σ₁) σ₂ false =
    or (literal-iff? n t (σ₂ ₛ•ₛ σ₁) false) (literal-free? n σ₂)
  literal-iff? n (var x) σ _ =
    not-level-literal? n (x [ σ ]ᵛ)
  literal-iff? n (1ᵘ+ l) σ already-checked =
    literal-iff? n l σ already-checked
  literal-iff? n (level t) σ already-checked =
    literal-iff? n t σ already-checked
  literal-iff? _ _ _ _ =
    return true

  -- Checks if Not-level-literal t holds.

  not-level-literal? : Fuel → (t : Term[ c , k ] n) → Check c Bool
  not-level-literal? _ (meta-var _ _) =
    return false
  not-level-literal? n (weaken _ t) =
    not-level-literal? n t
  not-level-literal? 0 (subst _ _) =
    no-fuel
  not-level-literal? (1+ n) (subst t σ) =
    and (literal-iff? n t σ false) (not-level-literal? n t)
  not-level-literal? _ zeroᵘ =
    return false
  not-level-literal? n (1ᵘ+ l) =
    not-level-literal? n l
  not-level-literal? n (l₁ supᵘₗ l₂) =
    or (and (not-infinite? l₂) (not-level-literal? n l₁))
      (and (not-infinite? l₁) (not-level-literal? n l₂))
  not-level-literal? _ (ωᵘ+ _) =
    return false
  not-level-literal? n (level t) =
    not-level-literal? n t
  not-level-literal? _ _ =
    return true

  -- Checks if Literal-free σ holds.

  literal-free? :
    Fuel → (σ : Subst c n₂ n₁) → Check c Bool
  literal-free? _ id         = return true
  literal-free? n (wk1 σ)    = literal-free? n σ
  literal-free? n (σ ⇑)      = literal-free? n σ
  literal-free? n (cons σ t) =
    and (not-level-literal? n t) (literal-free? n σ)

opaque mutual

  -- The function literal-iff? is sound.

  literal-iff?-sound :
    OK (literal-iff? n t σ b) true γ st →
    Literal-iff t σ
  literal-iff?-sound {t = meta-var _ _} {b = true} eq =
    meta-var (literal-free?-sound eq)
  literal-iff?-sound {t = meta-var _ _} {b = false} eq with inv-or eq
  … | inj₁ eq = literal-free (literal-free?-sound eq)
  … | inj₂ eq = meta-var (literal-free?-sound eq)
  literal-iff?-sound {t = weaken _ _} eq =
    weaken (literal-iff?-sound eq)
  literal-iff?-sound {t = subst _ _} {b = true} eq =
    subst (literal-iff?-sound eq)
  literal-iff?-sound {t = subst _ _} {b = false} eq with inv-or eq
  … | inj₁ eq = subst (literal-iff?-sound eq)
  … | inj₂ eq = literal-free (literal-free?-sound eq)
  literal-iff?-sound {t = var _} eq =
    var (not-level-literal?-sound eq)
  literal-iff?-sound {t = 1ᵘ+ _} eq =
    1ᵘ+ (literal-iff?-sound eq)
  literal-iff?-sound {t = level _} eq =
    level (literal-iff?-sound eq)
  literal-iff?-sound {t = defn _}                _ = defn
  literal-iff?-sound {t = Level}                 _ = Level
  literal-iff?-sound {t = zeroᵘ}                 _ = zeroᵘ
  literal-iff?-sound {t = _ supᵘₗ _}             _ = sup
  literal-iff?-sound {t = ωᵘ+ _}                 _ = ωᵘ+
  literal-iff?-sound {t = Lift _ _}              _ = Lift
  literal-iff?-sound {t = lift _ _}              _ = lift
  literal-iff?-sound {t = lower _}               _ = lower
  literal-iff?-sound {t = U _}                   _ = U
  literal-iff?-sound {t = Empty}                 _ = Empty
  literal-iff?-sound {t = emptyrec _ _ _}        _ = emptyrec
  literal-iff?-sound {t = Unit _}                _ = Unit
  literal-iff?-sound {t = star _}                _ = star
  literal-iff?-sound {t = unitrec _ _ _ _ _}     _ = unitrec
  literal-iff?-sound {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} _ = ΠΣ
  literal-iff?-sound {t = lam _ _ _}             _ = lam
  literal-iff?-sound {t = _ ∘⟨ _ ⟩ _}            _ = app
  literal-iff?-sound {t = prod _ _ _ _ _}        _ = prod
  literal-iff?-sound {t = fst _ _}               _ = fst
  literal-iff?-sound {t = snd _ _}               _ = snd
  literal-iff?-sound {t = prodrec _ _ _ _ _ _}   _ = prodrec
  literal-iff?-sound {t = ℕ}                     _ = ℕ
  literal-iff?-sound {t = zero}                  _ = zero
  literal-iff?-sound {t = suc _}                 _ = suc
  literal-iff?-sound {t = natrec _ _ _ _ _ _ _}  _ = natrec
  literal-iff?-sound {t = Id _ _ _}              _ = Id
  literal-iff?-sound {t = rfl _}                 _ = rfl
  literal-iff?-sound {t = J _ _ _ _ _ _ _ _}     _ = J
  literal-iff?-sound {t = K _ _ _ _ _ _}         _ = K
  literal-iff?-sound {t = []-cong _ _ _ _ _ _}   _ = []-cong

  -- The function not-level-literal? is sound.

  not-level-literal?-sound :
    OK (not-level-literal? n t) true γ st →
    Not-level-literal t
  not-level-literal?-sound {t = meta-var _ _} not-ok
  not-level-literal?-sound {t = weaken _ _}   eq     =
    weaken (not-level-literal?-sound eq)
  not-level-literal?-sound {n = 0}    {t = subst _ _} not-ok
  not-level-literal?-sound {n = 1+ _} {t = subst _ _} eq     =
    let eq₁ , eq₂ = inv-and eq in
    subst (literal-iff?-sound eq₁) (not-level-literal?-sound eq₂)
  not-level-literal?-sound {t = zeroᵘ}  not-ok
  not-level-literal?-sound {t = 1ᵘ+ _} eq     =
    1ᵘ+ (not-level-literal?-sound eq)
  not-level-literal?-sound {t = _ supᵘₗ _} eq with inv-or eq
  … | inj₁ eq =
    let eq₁ , eq₂ = inv-and eq in
    supᵘₗˡ (not-level-literal?-sound eq₂) (not-infinite?-sound eq₁)
  … | inj₂ eq =
    let eq₁ , eq₂ = inv-and eq in
    supᵘₗʳ (not-infinite?-sound eq₁) (not-level-literal?-sound eq₂)
  not-level-literal?-sound {t = ωᵘ+ _}   not-ok
  not-level-literal?-sound {t = level _} eq     =
    level (not-level-literal?-sound eq)
  not-level-literal?-sound {t = var _}                 _ = var
  not-level-literal?-sound {t = defn _}                _ = defn
  not-level-literal?-sound {t = Level}                 _ = Level
  not-level-literal?-sound {t = Lift _ _}              _ = Lift
  not-level-literal?-sound {t = lift _ _}              _ = lift
  not-level-literal?-sound {t = lower _}               _ = lower
  not-level-literal?-sound {t = U _}                   _ = U
  not-level-literal?-sound {t = Empty}                 _ = Empty
  not-level-literal?-sound {t = emptyrec _ _ _}        _ = emptyrec
  not-level-literal?-sound {t = Unit _}                _ = Unit
  not-level-literal?-sound {t = star _}                _ = star
  not-level-literal?-sound {t = unitrec _ _ _ _ _}     _ = unitrec
  not-level-literal?-sound {t = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} _ = ΠΣ
  not-level-literal?-sound {t = lam _ _ _}             _ = lam
  not-level-literal?-sound {t = _ ∘⟨ _ ⟩ _}            _ = app
  not-level-literal?-sound {t = prod _ _ _ _ _}        _ = prod
  not-level-literal?-sound {t = fst _ _}               _ = fst
  not-level-literal?-sound {t = snd _ _}               _ = snd
  not-level-literal?-sound {t = prodrec _ _ _ _ _ _}   _ = prodrec
  not-level-literal?-sound {t = ℕ}                     _ = ℕ
  not-level-literal?-sound {t = zero}                  _ = zero
  not-level-literal?-sound {t = suc _}                 _ = suc
  not-level-literal?-sound {t = natrec _ _ _ _ _ _ _}  _ = natrec
  not-level-literal?-sound {t = Id _ _ _}              _ = Id
  not-level-literal?-sound {t = rfl _}                 _ = rfl
  not-level-literal?-sound {t = J _ _ _ _ _ _ _ _}     _ = J
  not-level-literal?-sound {t = K _ _ _ _ _ _}         _ = K
  not-level-literal?-sound {t = []-cong _ _ _ _ _ _}   _ = []-cong

  -- The function literal-free? is sound.

  literal-free?-sound :
    OK (literal-free? n σ) true γ st →
    Literal-free σ
  literal-free?-sound {σ = id}       ok! = id
  literal-free?-sound {σ = wk1 _}    eq  = wk1 (literal-free?-sound eq)
  literal-free?-sound {σ = _ ⇑}      eq  = literal-free?-sound eq ⇑
  literal-free?-sound {σ = cons _ _} eq  =
    let eq₁ , eq₂ = inv-and eq in
    cons (literal-free?-sound eq₂) (not-level-literal?-sound eq₁)

------------------------------------------------------------------------
-- Not-supᵘₗ

-- The level is not an application of _supᵘₗ_.

Not-supᵘₗ : Term[ c , k ] n → Set a
Not-supᵘₗ l = ¬ (∃₂ λ l₁ l₂ → l PE.≡ l₁ supᵘₗ l₂)

opaque

  -- If l [ σ ] is not an application of _supᵘₗ_, then the same
  -- applies to l.

  Not-supᵘₗ-[]→ : Not-supᵘₗ (l [ σ ]) → Not-supᵘₗ l
  Not-supᵘₗ-[]→ {l = _ supᵘₗ _} hyp _ =
    hyp (_ , _ , PE.refl)
  Not-supᵘₗ-[]→ {l = meta-var _ _}          _ (_ , _ , ())
  Not-supᵘₗ-[]→ {l = weaken _ _}            _ (_ , _ , ())
  Not-supᵘₗ-[]→ {l = subst _ _}             _ (_ , _ , ())
  Not-supᵘₗ-[]→ {l = var _}                 _ (_ , _ , ())
  Not-supᵘₗ-[]→ {l = defn _}                _ (_ , _ , ())
  Not-supᵘₗ-[]→ {l = Level}                 _ (_ , _ , ())
  Not-supᵘₗ-[]→ {l = zeroᵘ}                 _ (_ , _ , ())
  Not-supᵘₗ-[]→ {l = 1ᵘ+ _}                 _ (_ , _ , ())
  Not-supᵘₗ-[]→ {l = ωᵘ+ _}                 _ (_ , _ , ())
  Not-supᵘₗ-[]→ {l = level _}               _ (_ , _ , ())
  Not-supᵘₗ-[]→ {l = U _}                   _ (_ , _ , ())
  Not-supᵘₗ-[]→ {l = Lift _ _}              _ (_ , _ , ())
  Not-supᵘₗ-[]→ {l = lift _ _}              _ (_ , _ , ())
  Not-supᵘₗ-[]→ {l = lower _}               _ (_ , _ , ())
  Not-supᵘₗ-[]→ {l = Empty}                 _ (_ , _ , ())
  Not-supᵘₗ-[]→ {l = emptyrec _ _ _}        _ (_ , _ , ())
  Not-supᵘₗ-[]→ {l = Unit _}                _ (_ , _ , ())
  Not-supᵘₗ-[]→ {l = star _}                _ (_ , _ , ())
  Not-supᵘₗ-[]→ {l = unitrec _ _ _ _ _}     _ (_ , _ , ())
  Not-supᵘₗ-[]→ {l = ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _} _ (_ , _ , ())
  Not-supᵘₗ-[]→ {l = lam _ _ _}             _ (_ , _ , ())
  Not-supᵘₗ-[]→ {l = _ ∘⟨ _ ⟩ _}            _ (_ , _ , ())
  Not-supᵘₗ-[]→ {l = prod _ _ _ _ _}        _ (_ , _ , ())
  Not-supᵘₗ-[]→ {l = fst _ _}               _ (_ , _ , ())
  Not-supᵘₗ-[]→ {l = snd _ _}               _ (_ , _ , ())
  Not-supᵘₗ-[]→ {l = prodrec _ _ _ _ _ _}   _ (_ , _ , ())
  Not-supᵘₗ-[]→ {l = ℕ}                     _ (_ , _ , ())
  Not-supᵘₗ-[]→ {l = zero}                  _ (_ , _ , ())
  Not-supᵘₗ-[]→ {l = suc _}                 _ (_ , _ , ())
  Not-supᵘₗ-[]→ {l = natrec _ _ _ _ _ _ _}  _ (_ , _ , ())
  Not-supᵘₗ-[]→ {l = Id _ _ _}              _ (_ , _ , ())
  Not-supᵘₗ-[]→ {l = rfl _}                 _ (_ , _ , ())
  Not-supᵘₗ-[]→ {l = J _ _ _ _ _ _ _ _}     _ (_ , _ , ())
  Not-supᵘₗ-[]→ {l = K _ _ _ _ _ _}         _ (_ , _ , ())
  Not-supᵘₗ-[]→ {l = []-cong _ _ _ _ _ _}   _ (_ , _ , ())

-- One can decide if a level is an application of _supᵘₗ_.

supᵘₗ? : (l : Term[ c , k ] n) → Dec (∃₂ λ l₁ l₂ → l PE.≡ l₁ supᵘₗ l₂)
supᵘₗ? (meta-var _ _)          = no (λ ())
supᵘₗ? (weaken _ _)            = no (λ ())
supᵘₗ? (subst _ _)             = no (λ ())
supᵘₗ? (var _)                 = no (λ ())
supᵘₗ? (defn _)                = no (λ ())
supᵘₗ? Level                   = no (λ ())
supᵘₗ? zeroᵘ                   = no (λ ())
supᵘₗ? (1ᵘ+ _)                 = no (λ ())
supᵘₗ? (_ supᵘₗ _)             = yes (_ , _ , PE.refl)
supᵘₗ? (ωᵘ+ _)                 = no (λ ())
supᵘₗ? (level _)               = no (λ ())
supᵘₗ? (U _)                   = no (λ ())
supᵘₗ? (Lift _ _)              = no (λ ())
supᵘₗ? (lift _ _)              = no (λ ())
supᵘₗ? (lower _)               = no (λ ())
supᵘₗ? Empty                   = no (λ ())
supᵘₗ? (emptyrec _ _ _)        = no (λ ())
supᵘₗ? (Unit _)                = no (λ ())
supᵘₗ? (star _)                = no (λ ())
supᵘₗ? (unitrec _ _ _ _ _)     = no (λ ())
supᵘₗ? (ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _) = no (λ ())
supᵘₗ? (lam _ _ _)             = no (λ ())
supᵘₗ? (_ ∘⟨ _ ⟩ _)            = no (λ ())
supᵘₗ? (prod _ _ _ _ _)        = no (λ ())
supᵘₗ? (fst _ _)               = no (λ ())
supᵘₗ? (snd _ _)               = no (λ ())
supᵘₗ? (prodrec _ _ _ _ _ _)   = no (λ ())
supᵘₗ? ℕ                       = no (λ ())
supᵘₗ? zero                    = no (λ ())
supᵘₗ? (suc _)                 = no (λ ())
supᵘₗ? (natrec _ _ _ _ _ _ _)  = no (λ ())
supᵘₗ? (Id _ _ _)              = no (λ ())
supᵘₗ? (rfl _)                 = no (λ ())
supᵘₗ? (J _ _ _ _ _ _ _ _)     = no (λ ())
supᵘₗ? (K _ _ _ _ _ _)         = no (λ ())
supᵘₗ? ([]-cong _ _ _ _ _ _)   = no (λ ())

------------------------------------------------------------------------
-- Is-weaken-subst

-- The term is an application of weaken or subst.

data Is-weaken-subst {c : Constants} {k n} :
       Term[ c , k ] n → Set a where
  weaken : ∀ (ρ : Wk n n′) t → Is-weaken-subst (weaken ρ t)
  subst  : ∀ t (σ : Subst c n n′) → Is-weaken-subst (subst t σ)

opaque

  -- If a level is an application of weaken or subst, then it is not
  -- an application of _supᵘₗ_.

  Is-weaken-subst→Not-supᵘₗ : Is-weaken-subst l → Not-supᵘₗ l
  Is-weaken-subst→Not-supᵘₗ (weaken _ _) (_ , _ , ())
  Is-weaken-subst→Not-supᵘₗ (subst _ _)  (_ , _ , ())

-- Is the term an application of weaken or subst?

is-weaken-subst? : (t : Term[ c , k ] n) → Dec (Is-weaken-subst t)
is-weaken-subst? (weaken _ _)            = yes (weaken _ _)
is-weaken-subst? (subst _ _)             = yes (subst _ _)
is-weaken-subst? (meta-var _ _)          = no (λ ())
is-weaken-subst? (var _)                 = no (λ ())
is-weaken-subst? (defn _)                = no (λ ())
is-weaken-subst? Level                   = no (λ ())
is-weaken-subst? zeroᵘ                   = no (λ ())
is-weaken-subst? (1ᵘ+ _)                 = no (λ ())
is-weaken-subst? (_ supᵘₗ _)             = no (λ ())
is-weaken-subst? (ωᵘ+ _)                 = no (λ ())
is-weaken-subst? (level _)               = no (λ ())
is-weaken-subst? (U _)                   = no (λ ())
is-weaken-subst? (Lift _ _)              = no (λ ())
is-weaken-subst? (lift _ _)              = no (λ ())
is-weaken-subst? (lower _)               = no (λ ())
is-weaken-subst? Empty                   = no (λ ())
is-weaken-subst? (emptyrec _ _ _)        = no (λ ())
is-weaken-subst? (Unit _)                = no (λ ())
is-weaken-subst? (star _)                = no (λ ())
is-weaken-subst? (unitrec _ _ _ _ _)     = no (λ ())
is-weaken-subst? (ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _) = no (λ ())
is-weaken-subst? (lam _ _ _)             = no (λ ())
is-weaken-subst? (_ ∘⟨ _ ⟩ _)            = no (λ ())
is-weaken-subst? (prod _ _ _ _ _)        = no (λ ())
is-weaken-subst? (fst _ _)               = no (λ ())
is-weaken-subst? (snd _ _)               = no (λ ())
is-weaken-subst? (prodrec _ _ _ _ _ _)   = no (λ ())
is-weaken-subst? ℕ                       = no (λ ())
is-weaken-subst? zero                    = no (λ ())
is-weaken-subst? (suc _)                 = no (λ ())
is-weaken-subst? (natrec _ _ _ _ _ _ _)  = no (λ ())
is-weaken-subst? (Id _ _ _)              = no (λ ())
is-weaken-subst? (rfl _)                 = no (λ ())
is-weaken-subst? (J _ _ _ _ _ _ _ _)     = no (λ ())
is-weaken-subst? (K _ _ _ _ _ _)         = no (λ ())
is-weaken-subst? ([]-cong _ _ _ _ _ _)   = no (λ ())

------------------------------------------------------------------------
-- ⌜[]⌝

-- A type used to state ⌜[]⌝.

data ⌜[]⌝-assumption
       (σ : Subst c n₂ n₁) (γ : Contexts c) :
       Term[ c , k ] n₁ → Set a where
  literal-free : Literal-free σ → ⌜[]⌝-assumption σ γ t

  literal-iff :
    Literal-iff l₁ σ → Literal-iff l₂ σ →
    ⌜[]⌝-assumption σ γ (l₁ supᵘₗ l₂)

  not-supᵘₗ : Not-supᵘₗ l → ⌜[]⌝-assumption σ γ l

  level-allowed : Level-allowed → ⌜[]⌝-assumption σ γ t

  type₁ : Γ ⊢ ⌜ t [ σ ] ⌝ γ               → ⌜[]⌝-assumption σ γ t
  type₂ : Γ ⊢ ⌜ t ⌝ γ U.[ ⌜ σ ⌝ˢ γ ]      → ⌜[]⌝-assumption σ γ t
  term₁ : Γ ⊢ ⌜ t [ σ ] ⌝ γ          ∷ A′ → ⌜[]⌝-assumption σ γ t
  term₂ : Γ ⊢ ⌜ t ⌝ γ U.[ ⌜ σ ⌝ˢ γ ] ∷ A′ → ⌜[]⌝-assumption σ γ t

  level :
    {l : Term[ c , k ] n₁} →
    Γ ⊢ ⌜ Term[]→Lvl l ⌝ γ U.[ ⌜ σ ⌝ˢ γ ] ∷Level → ⌜[]⌝-assumption σ γ l

opaque
  unfolding U.size-of-Level U.↓ᵘ_

  -- If Level is not allowed, then translation does not necessarily
  -- commute with _[_]/U._[_].

  ¬⌜[]⌝ :
    ¬ Level-allowed →
    let l = level (var {n = 1+ n} x0) supᵘₗ level (var x0)
        σ = sgSubst zeroᵘ
    in
    ¬ ⌜ l [ σ ] ⌝ γ PE.≡ ⌜ l ⌝ γ U.[ ⌜ σ ⌝ˢ γ ]
  ¬⌜[]⌝ {γ} not-okᴸ hyp =
    case
      U.zeroᵘₗ                                                        ≡˘⟨ PE.cong U.level (supᵘₗ′≡↓ᵘ⊔ U.zeroᵘ U.zeroᵘ) ⟩

      U.level (U.zeroᵘ U.supᵘₗ′ U.zeroᵘ)                              ≡˘⟨ S.supᵘₗ≡supᵘₗ′ not-okᴸ ⟩

      U.zeroᵘₗ S.supᵘₗ U.zeroᵘₗ                                       ≡⟨⟩

      ⌜ level (var x0) supᵘₗ level (var x0) [ sgSubst zeroᵘ ] ⌝ γ     ≡⟨ hyp ⟩

      ⌜ level (var x0) supᵘₗ level (var x0) ⌝ γ
        U.[ ⌜ sgSubst zeroᵘ ⌝ˢ γ ]                                    ≡⟨⟩

      (U.level (U.var x0) S.supᵘₗ U.level (U.var x0)) U.[ U.zeroᵘ ]₀  ≡⟨ PE.cong U._[ _ ]₀ (S.supᵘₗ≡supᵘₗ′ not-okᴸ) ⟩

      U.level (U.var x0 U.supᵘₗ′ U.var x0) U.[ U.zeroᵘ ]₀             ≡⟨ PE.cong (U._[ U.zeroᵘ ]₀ ∘→ U.level) (supᵘₗ′≡supᵘ (λ { (() , _) })) ⟩

      U.level (U.var x0 U.supᵘ U.var x0) U.[ U.zeroᵘ ]₀               ≡⟨⟩

      U.level (U.zeroᵘ U.supᵘ U.zeroᵘ)                                ∎
    of λ ()

opaque

  -- The function ⌜_⌝ commutes with substitution, given a certain
  -- assumption.

  ⌜[]⌝ :
    (t : Term[ c , k ] n) →
    ⌜[]⌝-assumption σ γ t →
    ⌜ t [ σ ] ⌝ γ PE.≡ ⌜ t ⌝ γ U.[ ⌜ σ ⌝ˢ γ ]
  ⌜[]⌝ {σ} {γ} (meta-var x σ′) _ =
    ⌜ meta-var x (σ ₛ•ₛ σ′) ⌝ γ              ≡⟨ ⌜meta-var⌝ (σ ₛ•ₛ _) ⟩
    ⌜ x ⌝ᵐ γ U.[ ⌜ σ ₛ•ₛ σ′ ⌝ˢ γ ]           ≡⟨ substVar-to-subst (⌜ₛ•ₛ⌝ˢ σ) (⌜ x ⌝ᵐ γ) ⟩
    ⌜ x ⌝ᵐ γ U.[ ⌜ σ ⌝ˢ γ U.ₛ•ₛ ⌜ σ′ ⌝ˢ γ ]  ≡˘⟨ substCompEq (⌜ x ⌝ᵐ γ) ⟩
    ⌜ x ⌝ᵐ γ U.[ ⌜ σ′ ⌝ˢ γ ] U.[ ⌜ σ ⌝ˢ γ ]  ≡˘⟨ PE.cong U._[ _ ] (⌜meta-var⌝ σ′) ⟩
    ⌜ meta-var x σ′ ⌝ γ U.[ ⌜ σ ⌝ˢ γ ]       ∎
  ⌜[]⌝ {σ} {γ} (weaken ρ t) _ =
    ⌜ t ⌝ γ U.[ ⌜ σ ₛ• ρ ⌝ˢ γ ]      ≡⟨ substVar-to-subst (⌜ₛ•⌝ˢ σ) (⌜ t ⌝ _) ⟩
    ⌜ t ⌝ γ U.[ ⌜ σ ⌝ˢ γ U.ₛ• ρ ]    ≡˘⟨ subst-wk (⌜ t ⌝ _) ⟩
    U.wk ρ (⌜ t ⌝ γ) U.[ ⌜ σ ⌝ˢ γ ]  ∎
  ⌜[]⌝ {σ} {γ} (subst t σ′) _ =
    ⌜ t ⌝ γ U.[ ⌜ σ ₛ•ₛ σ′ ⌝ˢ γ ]           ≡⟨ substVar-to-subst (⌜ₛ•ₛ⌝ˢ σ) (⌜ t ⌝ _) ⟩
    ⌜ t ⌝ γ U.[ ⌜ σ ⌝ˢ γ U.ₛ•ₛ ⌜ σ′ ⌝ˢ γ ]  ≡˘⟨ substCompEq (⌜ t ⌝ _) ⟩
    ⌜ t ⌝ γ U.[ ⌜ σ′ ⌝ˢ γ ] U.[ ⌜ σ ⌝ˢ γ ]  ∎
  ⌜[]⌝ {σ} (var _) _ =
    ⌜[]ᵛ⌝ σ _
  ⌜[]⌝ (defn _) _ =
    PE.refl
  ⌜[]⌝ Level _ =
    PE.refl
  ⌜[]⌝ zeroᵘ _ =
    PE.refl
  ⌜[]⌝ {σ} {γ} (1ᵘ+ l) _ =
    U.1ᵘ+ (⌜ l ⌝ γ U.[ ⌜ σ ⌝ˢ γ ])  ≡˘⟨ 1ᵘ+-[] (⌜ l ⌝ _) ⟩
    U.1ᵘ+ (⌜ l ⌝ γ) U.[ ⌜ σ ⌝ˢ γ ]  ∎
  ⌜[]⌝ {σ} {γ} (l₁ supᵘₗ l₂) hyp =
    case hyp of λ where
      (literal-free lf) →
        PE.sym $ S.supᵘₗ-[]′ λ _ →
        Level-literal (⌜ subst l₁ σ ⌝ γ) ×
        Level-literal (⌜ subst l₂ σ ⌝ γ)                     ⇔˘⟨ Literal-free→⇔Level-literal-[⌜⌝ˢ] lf
                                                                   ×-cong-⇔
                                                                 Literal-free→⇔Level-literal-[⌜⌝ˢ] lf ⟩→

        Level-literal (⌜ l₁ ⌝ γ) × Level-literal (⌜ l₂ ⌝ γ)  □
      (literal-iff iff₁ iff₂) →
        PE.sym $ S.supᵘₗ-[]′ λ _ →
        Level-literal (⌜ subst l₁ σ ⌝ γ) ×
        Level-literal (⌜ subst l₂ σ ⌝ γ)                     ⇔˘⟨ Literal-iff→⇔Level-literal-⌜subst⌝ iff₁
                                                                   ×-cong-⇔
                                                                 Literal-iff→⇔Level-literal-⌜subst⌝ iff₂ ⟩→

        Level-literal (⌜ l₁ ⌝ γ) × Level-literal (⌜ l₂ ⌝ γ)  □
      (not-supᵘₗ not-sup) →
        ⊥-elim (not-sup (_ , _ , PE.refl))
      (level-allowed okᴸ) →
        lemma₁ okᴸ
      (type₁ ⊢⊔) →
        let _ , _ , _ , ≡Level = inversion-supᵘₗ-⊢ ⊢⊔ in
        lemma₂ ≡Level
      (type₂ ⊢⊔) →
        case S.supᵘₗ≡ (⌜ l₁ ⌝ γ) (⌜ l₂ ⌝ γ) of λ where
          (inj₁ (n , eq)) →
            let _ , ≡Level =
                  inversion-↓ᵘ-⊢ {n = n} $
                  PE.subst (_⊢_ _)
                    (PE.trans (PE.cong U._[ _ ] eq) ↓ᵘ-[]) ⊢⊔
            in
            lemma₂ ≡Level
          (inj₂ eq) →
            let _ , _ , _ , ≡Level =
                  inversion-supᵘ-⊢ $
                  PE.subst (_⊢_ _) (PE.cong U._[ _ ] eq) ⊢⊔
            in
            lemma₂ ≡Level
      (term₁ ⊢⊔) →
        let _ , _ , ≡Level = inversion-supᵘₗ-⊢∷ ⊢⊔ in
        lemma₂ ≡Level
      (term₂ ⊢⊔) →
        case S.supᵘₗ≡ (⌜ l₁ ⌝ γ) (⌜ l₂ ⌝ γ) of λ where
          (inj₁ (n , eq)) →
            let ≡Level =
                  inversion-↓ᵘ {n = n} $
                  PE.subst (flip (_⊢_∷_ _) _)
                    (PE.trans (PE.cong U._[ _ ] eq) ↓ᵘ-[]) ⊢⊔
            in
            lemma₂ ≡Level
          (inj₂ eq) →
            let _ , _ , ≡Level =
                  inversion-supᵘ $
                  PE.subst (flip (_⊢_∷_ _) _) (PE.cong U._[ _ ] eq) ⊢⊔
            in
            lemma₂ ≡Level
      (level {k = tm} ⊢sup[]) →
        lemma₃ ⊢sup[]
      (level {k = lvl} ⊢sup[]) →
        lemma₄ ⊢sup[]
    where
    lemma₁ :
      {l₁ l₂ : U.Term[ k ] _} →
      Level-allowed →
      (l₁ U.[ ⌜ σ ⌝ˢ γ ]) S.supᵘₗ (l₂ U.[ ⌜ σ ⌝ˢ γ ]) PE.≡
      l₁ S.supᵘₗ l₂ U.[ ⌜ σ ⌝ˢ γ ]
    lemma₁ okᴸ = PE.sym (S.supᵘₗ-[]′ (⊥-elim ∘→ (_$ okᴸ)))

    lemma₂ :
      Γ ⊢ A′ ≡ U.Level →
      (⌜ l₁ ⌝ γ U.[ ⌜ σ ⌝ˢ γ ]) S.supᵘₗ (⌜ l₂ ⌝ γ U.[ ⌜ σ ⌝ˢ γ ]) PE.≡
      ⌜ l₁ ⌝ γ S.supᵘₗ ⌜ l₂ ⌝ γ U.[ ⌜ σ ⌝ˢ γ ]
    lemma₂ ≡Level = lemma₁ (inversion-Level-⊢ (wf-⊢≡ ≡Level .proj₂))

    lemma₃ :
      {t₁ t₂ : U.Term _} →
      Γ ⊢ U.level (t₁ S.supᵘₗ t₂ U.[ ⌜ σ ⌝ˢ γ ]) ∷Level →
      (t₁ U.[ ⌜ σ ⌝ˢ γ ]) S.supᵘₗ (t₂ U.[ ⌜ σ ⌝ˢ γ ]) PE.≡
      t₁ S.supᵘₗ t₂ U.[ ⌜ σ ⌝ˢ γ ]
    lemma₃ (term okᴸ _) =
      lemma₁ okᴸ
    lemma₃ {t₁} {t₂} (literal ⊔-ok _) =
      PE.sym $ S.supᵘₗ-[]′ λ _ _ →
                                                              $⟨ Allowed-literal→Level-literal ⊔-ok ⟩
      Level-literal (U.level (t₁ S.supᵘₗ t₂ U.[ ⌜ σ ⌝ˢ γ ]))  ⇔⟨ Level-literal-level-⇔ ⟩→
      Level-literal (t₁ S.supᵘₗ t₂ U.[ ⌜ σ ⌝ˢ γ ])            →⟨ S.Level-literal-supᵘₗ-[]₁ ⟩
      Level-literal (t₁ S.supᵘₗ t₂)                           →⟨ proj₂ ∘→ S.Level-literal-supᵘₗ-→-tm ⟩
      Level-literal t₁ × Level-literal t₂                     □

    opaque
      unfolding S._supᵘₗ_

      lemma₄ :
        {l₁ l₂ : U.Lvl _} →
        Γ ⊢ l₁ S.supᵘₗ l₂ U.[ ⌜ σ ⌝ˢ γ ] ∷Level →
        (l₁ U.[ ⌜ σ ⌝ˢ γ ]) S.supᵘₗ (l₂ U.[ ⌜ σ ⌝ˢ γ ]) PE.≡
        l₁ S.supᵘₗ l₂ U.[ ⌜ σ ⌝ˢ γ ]
      lemma₄ {l₁ = U.ωᵘ+ _} {l₂ = U.ωᵘ+ _} _ =
        PE.refl
      lemma₄ {l₁ = U.ωᵘ+ _} {l₂ = U.level _} _ =
        PE.refl
      lemma₄ {l₁ = U.level _} {l₂ = U.ωᵘ+ _} _ =
        PE.refl
      lemma₄ {l₁ = U.level _} {l₂ = U.level _} ⊢sup[] =
        PE.cong U.level (lemma₃ ⊢sup[])
  ⌜[]⌝ (ωᵘ+ _) _ =
    PE.refl
  ⌜[]⌝ (level _) _ =
    PE.refl
  ⌜[]⌝ (U _) _ =
    PE.refl
  ⌜[]⌝ (Lift _ _) _ =
    PE.refl
  ⌜[]⌝ (lift _ _) _ =
    PE.refl
  ⌜[]⌝ (lower _) _ =
    PE.refl
  ⌜[]⌝ Empty _ =
    PE.refl
  ⌜[]⌝ (emptyrec _ _ _) _ =
    PE.refl
  ⌜[]⌝ (Unit _) _ =
    PE.refl
  ⌜[]⌝ (star _) _ =
    PE.refl
  ⌜[]⌝ (unitrec _ _ _ _ _) _ =
    PE.refl
  ⌜[]⌝ (ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _) _ =
    PE.refl
  ⌜[]⌝ (lam _ _ _) _ =
    PE.refl
  ⌜[]⌝ (_ ∘⟨ _ ⟩ _) _ =
    PE.refl
  ⌜[]⌝ (prod _ _ _ _ _) _ =
    PE.refl
  ⌜[]⌝ (fst _ _) _ =
    PE.refl
  ⌜[]⌝ (snd _ _) _ =
    PE.refl
  ⌜[]⌝ (prodrec _ _ _ _ _ _) _ =
    PE.refl
  ⌜[]⌝ ℕ _ =
    PE.refl
  ⌜[]⌝ zero _ =
    PE.refl
  ⌜[]⌝ (suc _) _ =
    PE.refl
  ⌜[]⌝ (natrec _ _ _ _ _ _ _) _ =
    PE.refl
  ⌜[]⌝ (Id _ _ _) _ =
    PE.refl
  ⌜[]⌝ (rfl _) _ =
    PE.refl
  ⌜[]⌝ (J _ _ _ _ _ _ _ _) _ =
    PE.refl
  ⌜[]⌝ (K _ _ _ _ _ _) _ =
    PE.refl
  ⌜[]⌝ ([]-cong _ _ _ _ _ _) _ =
    PE.refl

-- A partial check of if ⌜[]⌝-assumption σ γ t holds for all γ.

⌜[]⌝-assumption? :
  Fuel → (t : Term[ c , k ] n₁) (σ : Subst c n₂ n₁) → Check c Bool
⌜[]⌝-assumption? n t σ with supᵘₗ? t
… | no _              = return true
… | yes (l₁ , l₂ , _) =
  or (literal-free? n σ)
    (and (literal-iff? n l₁ σ true) (literal-iff? n l₂ σ true))

opaque

  -- The function ⌜[]⌝-assumption? is sound.

  ⌜[]⌝-assumption?-sound :
    {t : Term[ c , k ] n₁} →
    OK (⌜[]⌝-assumption? n t σ) true γ st →
    ⌜[]⌝-assumption σ γ′ t
  ⌜[]⌝-assumption?-sound {t} eq with supᵘₗ? t
  … | no not                = not-supᵘₗ not
  … | yes (_ , _ , PE.refl) with inv-or eq
  … | inj₁ eq = literal-free (literal-free?-sound eq)
  … | inj₂ eq =
      let eq₁ , eq₂ = inv-and eq in
      literal-iff (literal-iff?-sound eq₁) (literal-iff?-sound eq₂)

------------------------------------------------------------------------
-- Removing weaken and subst

-- Removes top-level weaken and subst constructors.

remove-weaken-subst′ :
  Term[ c , k ] n → ∃ λ n′ → Subst c n n′ × Term[ c , k ] n′
remove-weaken-subst′ t with is-weaken-subst? t
remove-weaken-subst′ t | no _             = _ , id , t
remove-weaken-subst′ _ | yes (weaken ρ t) with remove-weaken-subst′ t
… | _ , σ , u = _ , ρ •ₛ σ , u
remove-weaken-subst′ _ | yes (subst t σ) with remove-weaken-subst′ t
… | _ , σ′ , u = _ , σ ₛ•ₛ σ′ , u

opaque

  -- The function remove-weaken-subst′ is correctly implemented.

  remove-weaken-subst′-correct :
    (t : Term[ c , k ] n) →
    let n , σ , u = remove-weaken-subst′ t in
    ¬ Is-weaken-subst u ×
    ⌜ t ⌝ γ PE.≡ ⌜ subst u σ ⌝ γ
  remove-weaken-subst′-correct {γ} t with is-weaken-subst? t
  … | no not =
      not ,
      (⌜ t ⌝ γ                  ≡˘⟨ subst-id _ ⟩
       ⌜ t ⌝ γ U.[ U.idSubst ]  ∎)
  … | yes (weaken ρ t) =
    let _ , σ , u = remove-weaken-subst′ t
        not , eq  = remove-weaken-subst′-correct t
    in
    not ,
    (U.wk ρ (⌜ t ⌝ γ)                 ≡⟨ PE.cong (U.wk _) eq ⟩
     U.wk ρ (⌜ u ⌝ γ U.[ ⌜ σ ⌝ˢ γ ])  ≡⟨ wk-subst (⌜ u ⌝ _) ⟩
     ⌜ u ⌝ γ U.[ ρ U.•ₛ ⌜ σ ⌝ˢ γ ]    ≡˘⟨ substVar-to-subst ⌜•ₛ⌝ˢ (⌜ u ⌝ _) ⟩
     ⌜ u ⌝ γ U.[ ⌜ ρ •ₛ σ ⌝ˢ γ ]      ∎)
  … | yes (subst t σ) =
    let _ , σ′ , u = remove-weaken-subst′ t
        not , eq   = remove-weaken-subst′-correct t
    in
    not ,
    (⌜ t ⌝ γ U.[ ⌜ σ ⌝ˢ γ ]                  ≡⟨ PE.cong U._[ _ ] eq ⟩
     ⌜ u ⌝ γ U.[ ⌜ σ′ ⌝ˢ γ ] U.[ ⌜ σ ⌝ˢ γ ]  ≡⟨ substCompEq (⌜ u ⌝ _) ⟩
     ⌜ u ⌝ γ U.[ ⌜ σ ⌝ˢ γ U.ₛ•ₛ ⌜ σ′ ⌝ˢ γ ]  ≡˘⟨ substVar-to-subst (⌜ₛ•ₛ⌝ˢ σ) (⌜ u ⌝ _) ⟩
     ⌜ u ⌝ γ U.[ ⌜ σ ₛ•ₛ σ′ ⌝ˢ γ ]           ∎)

-- A type used to state remove-weaken-subst.

data Remove-weaken-subst-assumption
       (b : Bool) (γ : Contexts c) :
       (_ _ : Term[ c , k ] n) → Set a where
  literal-free-or-iff :
    b PE.≡ true → Remove-weaken-subst-assumption b γ t u

  not-supᵘₗ : Not-supᵘₗ u → Remove-weaken-subst-assumption b γ t u

  level-allowed : Level-allowed → Remove-weaken-subst-assumption b γ t u

  type₁ : Γ ⊢ ⌜ t ⌝ γ      → Remove-weaken-subst-assumption b γ t u
  type₂ : Γ ⊢ ⌜ u ⌝ γ      → Remove-weaken-subst-assumption b γ t u
  term₁ : Γ ⊢ ⌜ t ⌝ γ ∷ A′ → Remove-weaken-subst-assumption b γ t u
  term₂ : Γ ⊢ ⌜ u ⌝ γ ∷ A′ → Remove-weaken-subst-assumption b γ t u

  level :
    Γ ⊢ ⌜ Term[]→Lvl l₁ ⌝ γ ∷Level →
    Remove-weaken-subst-assumption b γ l₁ l₂

opaque

  -- A cast lemma for Remove-weaken-subst-assumption.

  cast-Remove-weaken-subst-assumption :
    ⌜ t₁ ⌝ γ PE.≡ ⌜ t₂ ⌝ γ →
    Remove-weaken-subst-assumption b γ t₁ u →
    Remove-weaken-subst-assumption b γ t₂ u
  cast-Remove-weaken-subst-assumption eq = λ where
    (literal-free-or-iff hyp) →
      literal-free-or-iff hyp
    (level-allowed okᴸ) →
      level-allowed okᴸ
    (not-supᵘₗ ns) →
      not-supᵘₗ ns
    (type₁ ⊢t) →
      type₁ (PE.subst (_⊢_ _) eq ⊢t)
    (type₂ ⊢u) →
      type₂ ⊢u
    (term₁ ⊢t) →
      term₁ (PE.subst (flip (_⊢_∷_ _) _) eq ⊢t)
    (term₂ ⊢u) →
      term₂ ⊢u
    (level ⊢t) →
      level (PE.subst (_⊢_∷Level _) (Term[]→Lvl-cong eq) ⊢t)

-- Removes top-level weaken and subst constructors.
--
-- The boolean argument indicates whether ⌜[]⌝-assumption? should be
-- run.
--
-- Note that the result might have top-level weaken or subst
-- constructors (for instance if the term is
-- subst (var x0) (cons id (subst ℕ id))).

remove-weaken-subst :
  Fuel → Term[ c , k ] n → Bool → Check c (Term[ c , k ] n × Bool)
remove-weaken-subst n t run-check with remove-weaken-subst′ t
… | _ , σ , u = do
  b ← and (return run-check) (⌜[]⌝-assumption? n u σ)
  return (u [ σ ] , b)

opaque

  -- The function remove-weaken-subst is sound.

  remove-weaken-subst-sound :
    OK (remove-weaken-subst n t b₁) (u , b₂) γ st →
    Remove-weaken-subst-assumption b₂ γ′ t u →
    ⌜ t ⌝ γ′ PE.≡ ⌜ u ⌝ γ′
  remove-weaken-subst-sound {t} {γ′} eq hyp
    with remove-weaken-subst′ t
       | remove-weaken-subst′-correct {γ = γ′} t
  … | _ , σ , u | _ , correct
    with inv->>= eq
  … | inv b eq ok! =
    ⌜ t ⌝ γ′                  ≡⟨ correct ⟩
    ⌜ subst u σ ⌝ γ′          ≡⟨⟩
    ⌜ u ⌝ γ′ U.[ ⌜ σ ⌝ˢ γ′ ]  ≡˘⟨ ⌜[]⌝ _ ass ⟩
    ⌜ u [ σ ] ⌝ γ′            ∎
    where
    ass : ⌜[]⌝-assumption σ γ′ u
    ass = case hyp of λ where
      (literal-free-or-iff PE.refl) →
        let _ , eq = inv-and eq in
        ⌜[]⌝-assumption?-sound eq
      (not-supᵘₗ ns) →
        not-supᵘₗ (Not-supᵘₗ-[]→ ns)
      (level-allowed okᴸ) →
        level-allowed okᴸ
      (type₁ ⊢t) →
        type₂ (PE.subst (_⊢_ _) correct ⊢t)
      (type₂ ⊢u[σ]) →
        type₁ ⊢u[σ]
      (term₁ ⊢t) →
        term₂ (PE.subst (flip (_⊢_∷_ _) _) correct ⊢t)
      (term₂ ⊢u[σ]) →
        term₁ ⊢u[σ]
      (level ⊢t) →
        level $
        PE.subst (_⊢_∷Level _)
          (⌜ Term[]→Lvl t ⌝ γ′            ≡⟨ Term[]→Lvl-cong correct ⟩
           ⌜ Term[]→Lvl (subst u σ) ⌝ γ′  ≡˘⟨ ⌜subst-Term[]→Lvl⌝ u ⟩
           ⌜ subst (Term[]→Lvl u) σ ⌝ γ′  ∎)
          ⊢t

-- The result of remove-weaken-subst can have top-level weaken or
-- subst constructors.

_ :
  remove-weaken-subst {c = c} {n = n} 0
    (subst (var x0) (cons id (subst ℕ id))) true .run (γ # st) PE.≡
  inj₂ (subst ℕ id , true)
_ = PE.refl
