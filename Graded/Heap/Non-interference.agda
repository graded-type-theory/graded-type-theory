------------------------------------------------------------------------
-- A non-interference property using the heap semantics.
------------------------------------------------------------------------

-- We use a bounded distributive lattice of security levels as the
-- modality. The top element represents high security (secret)
-- information while the bottom element represents low security (public)
-- information.

open import Graded.Modality
open import Graded.Mode.Instances.Zero-one.Variant
import Graded.Mode.Instances.Zero-one
open import Graded.Usage.Restrictions
open import Graded.Heap.Assumptions
import Graded.Modality.Instances.Bounded-distributive-lattice
open import Definition.Typed.Restrictions
open import Tools.Bool using (T)
import Tools.PropositionalEquality as PE
open import Tools.Algebra
open import Tools.Relation

module Graded.Heap.Non-interference
  {a} {M : Set a}
  (L : Bounded-distributive-lattice M)
  (open Bounded-distributive-lattice L using (⊤; ⊥; ⊥≤))
  (is-⊤? : ∀ p → Dec (p PE.≡ ⊤))
  (open Graded.Modality.Instances.Bounded-distributive-lattice M L is-⊤?)
  (mode-variant : Mode-variant modality)
  (open Graded.Mode.Instances.Zero-one mode-variant)
  (UR : Usage-restrictions modality Zero-one-isMode)
  (TR : Type-restrictions modality)
  (As : Assumptions UR TR)
  (open Usage-restrictions UR)
  ⦃ no-nr : Nr-not-available-GLB ⦄
  where

private
  𝕄 : Modality M
  𝕄 = modality

open Assumptions As
open Modality 𝕄
open Type-restrictions TR

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum
import Tools.Reasoning.PartialOrder as RPo

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Neutral.Atomic M type-variant
open import Definition.Untyped.Inversion M
open import Definition.Untyped.Properties M
open import Definition.Untyped.Whnf M type-variant
open import Definition.Typed TR
open import Definition.Typed.Consequences.Canonicity TR
open import Definition.Typed.EqRelInstance TR
open import Definition.Typed.Inversion TR
open import Definition.Typed.Names-below TR
open import Definition.Typed.Properties TR
open import Definition.LogicalRelation TR
open import Definition.LogicalRelation.Fundamental.Reducibility TR
open import Definition.LogicalRelation.Substitution.Introductions.Nat TR
open import Definition.LogicalRelation.Unary TR

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Context.Weakening 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Restrictions.Zero-one 𝕄 mode-variant
open import Graded.Usage UR
open import Graded.Usage.Erased-matches
open import Graded.Usage.Restrictions.Natrec 𝕄
open import Graded.Usage.Inversion UR
open import Graded.Usage.Properties UR

open import Graded.Heap.Untyped type-variant UR factoring-nr
open import Graded.Heap.Untyped.Properties type-variant UR factoring-nr
open import Graded.Heap.Usage type-variant UR factoring-nr
open import Graded.Heap.Usage.Inversion type-variant UR factoring-nr
open import Graded.Heap.Usage.Properties type-variant UR factoring-nr
open import Graded.Heap.Usage.Reduction
  type-variant UR factoring-nr Unitʷ-η→ ¬Nr-not-available
open import Graded.Heap.Termination UR TR As
open import Graded.Heap.Typed UR TR factoring-nr
open import Graded.Heap.Typed.Inversion UR TR factoring-nr
open import Graded.Heap.Typed.Reduction UR TR factoring-nr
open import Graded.Heap.Typed.Properties UR TR factoring-nr
open import Graded.Heap.Typed.Substitution UR TR factoring-nr
open import Graded.Heap.Reduction type-variant UR factoring-nr
open import Graded.Heap.Reduction.Properties type-variant UR factoring-nr
open import Graded.Heap.Soundness UR TR As

private variable
  n t t′ t″ A : Term _
  s : State _ _ _
  γ δ η : Conₘ _
  Γ Δ : Con Term _
  H H′ H″ : Heap _ _
  ρ ρ′ ρ″ : Wk _ _
  S S′ : Stack _
  c : Cont _
  m : Mode
  x : Fin _
  p p₀ q r : M
  y : Ptr _

private instance
  or-empty-ε : ∀ {A : Set a} → A or-empty ε {A = Term}
  or-empty-ε = ε

record No-secret-matches (p : M) : Set a where
  no-eta-equality
  field
    no-secret-prodrec :
      ∀ {m p q r} → m ≤ p₀ → Prodrec-allowed ⌞ m ⌟ r p q → r ≤ p₀
    no-secret-unitrec :
      ∀ {m p q} → m ≤ p₀ → ¬ Unitʷ-η → Unitrec-allowed ⌞ m ⌟ p q → p ≤ p₀
    no-secret-J :
      ∀ {m} → m ≤ p₀ → erased-matches-for-J ⌞ m ⌟ PE.≡ none
    no-secret-K :
      ∀ {m} → m ≤ p₀ → erased-matches-for-K ⌞ m ⌟ PE.≡ none
    no-secret-[]-cong :
      ∀ {s m} → m ≤ p₀ → []-cong-allowed-mode s ⌞ m ⌟ → 𝟘 ≤ p₀

  ∣J∣≡𝟙 :
    ∀ {m p q} → m ≤ p₀ → ∣J erased-matches-for-J ⌞ m ⌟ , p , q ∣≡ 𝟙
  ∣J∣≡𝟙 m≤p₀ =
    ∣J∣≡ω (PE.subst (_≤ᵉᵐ some) (PE.sym (no-secret-J m≤p₀)) (none-≤ᵉᵐ {em = some}))
      λ em≡some → case PE.trans (PE.sym (no-secret-J m≤p₀)) em≡some of λ ()

  ∣K∣≡𝟙 :
    ∀ {m p} → m ≤ p₀ → ∣K erased-matches-for-K ⌞ m ⌟ , p ∣≡ 𝟙
  ∣K∣≡𝟙 m≤p₀ =
    ∣K∣≡ω (PE.subst (_≤ᵉᵐ some) (PE.sym (no-secret-K m≤p₀)) (none-≤ᵉᵐ {em = some}))
      (λ em≡some → case PE.trans (PE.sym (no-secret-K m≤p₀)) em≡some of λ ())

opaque

  no-secret-matchesᶜ :
    No-secret-matches p →
    (∀ {n q} {t : Term n} {ρ} → c PE.≢ emptyrecₑ q t ρ) →
    r ≤ p →
    γ ▸ᶜ[ ⌞ r ⌟ ] c →
    ∣ c ∣ᶜ[ ⌞ r ⌟ ]≡ q → q ≤ p
  no-secret-matchesᶜ _ _ _ _ ∘ₑ =
    ⊥≤ _
  no-secret-matchesᶜ _ _ _ _ fstₑ =
    ⊥≤ _
  no-secret-matchesᶜ _ _ _ _ sndₑ =
    ⊥≤ _
  no-secret-matchesᶜ ok _ r≤p ▸c prodrecₑ =
    No-secret-matches.no-secret-prodrec ok r≤p
      (▸-inv-prodrecₑ ▸c .proj₂ .proj₂ .proj₁)
  no-secret-matchesᶜ ok _ r≤p ▸c (natrecₑ (has-nrₑ ⦃ has-nr ⦄)) =
    ⊥-elim (¬[Nr∧No-nr-glb] has-nr no-nr)
  no-secret-matchesᶜ ok _ r≤p ▸c (natrecₑ (no-nrₑ q-GLB)) =
    ≤-trans (≤-reflexive (≤-antisym (q-GLB .proj₁ 0) (⊥≤ _))) (⊥≤ _)
  no-secret-matchesᶜ ok _ r≤p ▸c unitrecₑ =
    let _ , _ , Unit-ok , no-η , _ = ▸-inv-unitrecₑ ▸c
    in  No-secret-matches.no-secret-unitrec
          ok r≤p no-η Unit-ok
  no-secret-matchesᶜ _ er∉ _ _ emptyrecₑ =
    ⊥-elim (er∉ PE.refl)
  no-secret-matchesᶜ {p} {q} ok _ r≤p _ (Jₑ x) =
    let open ≤-reasoning in begin
      q ≈⟨ ∣J∣ᶜ-functional x (No-secret-matches.∣J∣≡𝟙 ok r≤p) ⟩
      𝟙 ≤⟨ ⊥≤ _ ⟩
      p ∎
  no-secret-matchesᶜ {p} {q} ok _ r≤p _ (Kₑ x) =
      let open ≤-reasoning in begin
      q ≈⟨ ∣K∣ᶜ-functional x (No-secret-matches.∣K∣≡𝟙 ok r≤p) ⟩
      𝟙 ≤⟨ ⊥≤ _ ⟩
      p ∎
  no-secret-matchesᶜ ok _ r≤p ▸c []-congₑ =
    No-secret-matches.no-secret-[]-cong ok r≤p (▸-inv-[]-congₑ ▸c .proj₁)
  no-secret-matchesᶜ ok _ _ ▸c lowerₑ =
    ⊥≤ _
  no-secret-matchesᶜ _ _ _ ▸c sucₑ =
    ⊥-elim (▸-inv-sucₑ ▸c)

opaque

  no-secret-matches :
    No-secret-matches p →
    (∀ {p} → ¬ emptyrec p ∈ S) →
    γ ▸ˢ S →
    ∣ S ∣≡ q → q ≤ p
  no-secret-matches _ _ ε ε = ⊥≤ _
  no-secret-matches {p} {q} ok er∉ (▸ˢ∙ {p = p′} ∣S∣≡p′ ▸c ▸S) ∣cS∣≡q =
    let q₁ , q₂ , ∣c∣≡q₁ , ∣S∣≡q₂ , q≡ = ∣∣∙-inv ∣cS∣≡q
        q₂≤p = no-secret-matches ok (λ er∈ → er∉ (there er∈)) ▸S ∣S∣≡q₂
        q₂≡p′ = ∣∣-functional ∣S∣≡q₂ ∣S∣≡p′
        open RPo ≤-poset
        p′≤p = begin
          p′ ≡˘⟨ q₂≡p′ ⟩
          q₂ ≤⟨ q₂≤p ⟩
          p ∎
        q₁≤p = no-secret-matchesᶜ ok (λ { PE.refl → er∉ here}) p′≤p ▸c
                (PE.subst (λ m → ∣ _ ∣ᶜ[ ⌞ m ⌟ ]≡ _) q₂≡p′ ∣c∣≡q₁)
    in  begin
      q       ≡⟨ q≡ ⟩
      q₂ · q₁ ≤⟨ ·-monotone q₂≤p q₁≤p ⟩
      p · p   ≡⟨ ·-idem _ ⟩
      p       ∎

opaque

  no-secret-matches′ :
    No-secret-matches p →
    ▸ ⟨ H , t , ρ , S ⟩ →
    ε ⊢ₛ ⟨ H , t , ρ , S ⟩ ∷ A →
    ∣ S ∣≡ q → q ≤ p
  no-secret-matches′ ok ▸s ⊢s ∣S∣≡q =
    no-secret-matches ok
      (⊢emptyrec∉S (λ _ → ¬Empty) ⊢s)
      (▸ₛ-inv ▸s .proj₂ .proj₂ .proj₂ .proj₂ .proj₂ .proj₂ .proj₂ .proj₁)
      ∣S∣≡q

opaque

  ~⟨⟩-↦[] :
    H ~⟨ p ⟩ H′ → H ⊢ y ↦[ q ] t , ρ ⨾ H″ →
    q ≤ p →
    ∃ λ H‴ → H′ ⊢ y ↦[ q ] t , ρ ⨾ H‴ × H″ ~⟨ p ⟩ H‴
  ~⟨⟩-↦[] ε ()
  ~⟨⟩-↦[] (H~H′ ∙ t≡u) (here p-q≡r) q≤p =
    _ , PE.subst (λ x → _ ⊢ y0 ↦[ _ ] x , _ ⨾ _)
          (PE.sym (t≡u (≤-trans (Addition≡Meet.p-q≡r→p≤q∧r≡p +≡∧ p-q≡r .proj₁) q≤p)))
          (here p-q≡r)
      , H~H′ ∙ λ _ → PE.refl
  ~⟨⟩-↦[] (H~H′ ∙ t≡u) (there d) q≤p =
    let _ , d , H″~H‴ = ~⟨⟩-↦[] H~H′ d q≤p
    in  _ , there d , H″~H‴ ∙ t≡u

opaque

  ~⟨⟩-⇒ₑ :
    H ~⟨ p ⟩ H′ →
    ⟨ H , t , ρ , S ⟩ ⇒ₑ ⟨ H″ , t′ , ρ′ , S′ ⟩ →
    ∃ λ H‴  → ⟨ H′ , t , ρ , S ⟩ ⇒ₑ ⟨ H‴ , t′ , ρ′ , S′ ⟩ × H″ ~⟨ p ⟩ H‴
  ~⟨⟩-⇒ₑ H~H′ appₕ =
    _ , appₕ , H~H′
  ~⟨⟩-⇒ₑ H~H′ fstₕ =
    _ , fstₕ , H~H′
  ~⟨⟩-⇒ₑ H~H′ sndₕ =
    _ , sndₕ , H~H′
  ~⟨⟩-⇒ₑ H~H′ prodrecₕ =
    _ , prodrecₕ , H~H′
  ~⟨⟩-⇒ₑ H~H′ natrecₕ =
    _ , natrecₕ , H~H′
  ~⟨⟩-⇒ₑ H~H′ (unitrecₕ x) =
    _ , unitrecₕ x , H~H′
  ~⟨⟩-⇒ₑ H~H′ emptyrecₕ =
    _ , emptyrecₕ , H~H′
  ~⟨⟩-⇒ₑ H~H′ Jₕ =
    _ , Jₕ , H~H′
  ~⟨⟩-⇒ₑ H~H′ Kₕ =
    _ , Kₕ , H~H′
  ~⟨⟩-⇒ₑ H~H′ []-congₕ =
    _ , []-congₕ , H~H′
  ~⟨⟩-⇒ₑ H~H′ lowerₕ =
    _ , lowerₕ , H~H′

opaque

  ~⟨⟩-⇾ₑ :
    No-secret-matches p →
    ▸ ⟨ H , t , ρ , S ⟩ →
    ε ⊢ₛ ⟨ H , t , ρ , S ⟩ ∷ A →
    H ~⟨ p ⟩ H′ →
    ⟨ H , t , ρ , S ⟩ ⇾ₑ ⟨ H″ , t′ , ρ′ , S′ ⟩ →
    ∃ λ H‴ → ⟨ H′ , t , ρ , S ⟩ ⇾ₑ ⟨ H‴ , t′ , ρ′ , S′ ⟩ × H″ ~⟨ p ⟩ H‴
  ~⟨⟩-⇾ₑ ok ▸s ⊢s H~H′ (var ∣S∣≡q d) =
    let _ , d′ , H″~H‴ = ~⟨⟩-↦[] H~H′ d (no-secret-matches′ ok ▸s ⊢s ∣S∣≡q)
    in  _ , var ∣S∣≡q d′ , H″~H‴
  ~⟨⟩-⇾ₑ ok ▸s ⊢s H~H′ (⇒ₑ d) =
    let H‴ , d′ , H″~H‴ = ~⟨⟩-⇒ₑ H~H′ d
    in  H‴ , ⇒ₑ d′ , H″~H‴

opaque

  ~⟨⟩-⇒ᵥ :
    H ~⟨ p ⟩ H′ →
    ⟨ H , t , ρ , S ⟩ ⇒ᵥ ⟨ H″ , t′ , ρ′ , S′ ⟩ →
    ∃ λ H‴ → ⟨ H′ , t , ρ , S ⟩ ⇒ᵥ ⟨ H‴ , t′ , ρ′ , S′ ⟩ × H″ ~⟨ p ⟩ H‴
  ~⟨⟩-⇒ᵥ H~H′ (lamₕ x) =
    _ , lamₕ x , H~H′ ∙ (λ _ → PE.refl)
  ~⟨⟩-⇒ᵥ H~H′ prodˢₕ₁ =
    _ , prodˢₕ₁ , H~H′
  ~⟨⟩-⇒ᵥ H~H′ prodˢₕ₂ =
    _ , prodˢₕ₂ , H~H′
  ~⟨⟩-⇒ᵥ H~H′ (prodʷₕ x) =
    _ , prodʷₕ x , H~H′ ∙ (λ _ → PE.refl) ∙ λ _ → PE.refl
  ~⟨⟩-⇒ᵥ H~H′ zeroₕ =
    _ , zeroₕ , H~H′
  ~⟨⟩-⇒ᵥ H~H′ (sucₕ x x₁) =
    _ , sucₕ x x₁ , H~H′ ∙ (λ _ → PE.refl) ∙ λ _ → PE.refl
  ~⟨⟩-⇒ᵥ H~H′ starʷₕ =
    _ , starʷₕ , H~H′
  ~⟨⟩-⇒ᵥ H~H′ (unitrec-ηₕ x) =
    _ , unitrec-ηₕ x , H~H′
  ~⟨⟩-⇒ᵥ H~H′ rflₕⱼ =
    _ , rflₕⱼ , H~H′
  ~⟨⟩-⇒ᵥ H~H′ rflₕₖ =
    _ , rflₕₖ , H~H′
  ~⟨⟩-⇒ᵥ H~H′ rflₕₑ =
    _ , rflₕₑ , H~H′
  ~⟨⟩-⇒ᵥ H~H′ liftₕ =
    _ , liftₕ , H~H′

opaque

  ~⟨⟩-⇒ₙ :
    H ~⟨ p ⟩ H′ →
    ⟨ H , t , ρ , S ⟩ ⇒ₙ ⟨ H″ , t′ , ρ′ , S′ ⟩ →
    ∃ λ H‴ → ⟨ H′ , t , ρ , S ⟩ ⇒ₙ ⟨ H‴ , t′ , ρ′ , S′ ⟩ × H″ ~⟨ p ⟩ H‴
  ~⟨⟩-⇒ₙ H~H′ (sucₕ x) =
    _ , sucₕ x , H~H′
  ~⟨⟩-⇒ₙ H~H′ (numₕ x) =
    _ , numₕ x , H~H′

opaque

  ~⟨⟩-⇾ :
    No-secret-matches p →
    ▸ ⟨ H , t , ρ , S ⟩ →
    ε ⊢ₛ ⟨ H , t , ρ , S ⟩ ∷ A →
    H ~⟨ p ⟩ H′ →
    ⟨ H , t , ρ , S ⟩ ⇾ ⟨ H″ , t′ , ρ′ , S′ ⟩ →
    ∃ λ H‴ → ⟨ H′ , t , ρ , S ⟩ ⇾ ⟨ H‴ , t′ , ρ′ , S′ ⟩ × H″ ~⟨ p ⟩ H‴
  ~⟨⟩-⇾ ok ▸s ⊢s H~H′ (⇾ₑ d) =
    let _ , d′ , H″~H‴ = ~⟨⟩-⇾ₑ ok ▸s ⊢s H~H′ d
    in  _ , ⇾ₑ d′ , H″~H‴
  ~⟨⟩-⇾ _ _ _ H~H′ (⇒ᵥ d) =
    let _ , d′ , H″~H‴ = ~⟨⟩-⇒ᵥ H~H′ d
    in  _ , ⇒ᵥ d′ , H″~H‴

opaque

  ~⟨⟩-↠ :
    No-secret-matches p →
    ▸ ⟨ H , t , ρ , S ⟩ →
    ε ⊢ₛ ⟨ H , t , ρ , S ⟩ ∷ A →
    H ~⟨ p ⟩ H′ →
    ⟨ H , t , ρ , S ⟩ ↠ ⟨ H″ , t′ , ρ′ , S′ ⟩ →
    ∃ λ H‴ → ⟨ H′ , t , ρ , S ⟩ ↠ ⟨ H‴ , t′ , ρ′ , S′ ⟩ × H″ ~⟨ p ⟩ H‴
  ~⟨⟩-↠ ok ▸s ⊢s H~H′ (⇾ₑ d) =
    let _ , d′ , H″~H‴ = ~⟨⟩-⇾ₑ ok ▸s ⊢s H~H′ d
    in  _ , ⇾ₑ d′ , H″~H‴
  ~⟨⟩-↠ _ _ _ H~H′ (⇒ᵥ d) =
    let _ , d′ , H″~H‴ = ~⟨⟩-⇒ᵥ H~H′ d
    in  _ , ⇒ᵥ d′ , H″~H‴
  ~⟨⟩-↠ _ _ _ H~H′ (⇒ₙ d) =
    let _ , d′ , H″~H‴ = ~⟨⟩-⇒ₙ H~H′ d
    in  _ , ⇒ₙ d′ , H″~H‴

opaque

  ~⟨⟩-⇾* :
    No-secret-matches p →
    ▸ ⟨ H , t , ρ , S ⟩ →
    ε ⊢ₛ ⟨ H , t , ρ , S ⟩ ∷ A →
    H ~⟨ p ⟩ H′ →
    ⟨ H , t , ρ , S ⟩ ⇾* ⟨ H″ , t′ , ρ′ , S′ ⟩ →
    ∃ λ H‴ → ⟨ H′ , t , ρ , S ⟩ ⇾* ⟨ H‴ , t′ , ρ′ , S′ ⟩ × H″ ~⟨ p ⟩ H‴
  ~⟨⟩-⇾* ok ▸s ⊢s H~H′ id =
    _ , id , H~H′
  ~⟨⟩-⇾* ok ▸s ⊢s H~H′ (_⇨_ {s₂ = record{}} x d) =
    let _  , x′ , H₀~H₁ = ~⟨⟩-⇾ ok ▸s ⊢s H~H′ x
        _ , d′ , H₂~H₃ = ~⟨⟩-⇾* ok (▸-⇾ ▸s x) (⊢ₛ-⇾ ⊢s x) H₀~H₁ d
    in  _ , (x′ ⇨ d′) , H₂~H₃

private opaque

  suc-red-lemma :
    ¬ Numeral n →
    Numeral t″ →
    t′ PE.≡ suc n →
    ⟨ H , t , ρ , S ⟩ ⇾* ⟨ H′ , t′ , ρ′ , ε ⟩ →
    ⟨ H′ , n , ρ′ , ε ⟩ ↠* ⟨ H″ , t″ , ρ″ , ε ⟩ →
    ⟨ H , t , ρ , S ⟩ ↠* ⟨ H″ , suc t″ , ρ″ , ε ⟩
  suc-red-lemma ¬num num PE.refl d₁ d₂ =
    ↠*-concat (⇾*→↠* d₁)
      (⇒ₙ sucₕ ¬num ⇨
      ↠*-concat (++sucₛ-↠* d₂) (⇒ₙ (numₕ num) ⇨ id))

private opaque

  non-interference′ :
    No-secret-matches p →
    ▸ ⟨ H , t , ρ , S ⟩ →
    ε ⊢ₛ ⟨ H , t , ρ , S ⟩ ∷ ℕ →
    H ~⟨ p ⟩ H′ →
    ε » ε ⊩ℕ n ∷ℕ → n PE.≡ ⦅ ⟨ H , t , ρ , S ⟩ ⦆ →
    ∃₆ λ m n H″ H‴ (ρ′ : Wk m n) t′ →
      ⟨ H , t , ρ , S ⟩ ↠* ⟨ H″ , t′ , ρ′ , ε ⟩ ×
      ⟨ H′ , t , ρ , S ⟩ ↠* ⟨ H‴ , t′ , ρ′ , ε ⟩ ×
      Numeral t′ ×
      H″ ~⟨ p ⟩ H‴
  non-interference′ ok ▸s ⊢s H~H′ (ℕₜ u ⇒*u ≅u (sucᵣ x)) PE.refl =
    let _ , _ , H , t , ρ , (d′ , _) , ≡u , v = whBisim-closed ⊢s ▸s (⇒*u , sucₙ)
    in  case subst-suc {t = wk ρ t} ≡u of λ where
      (inj₁ (x , ≡x)) →
        case PE.subst Value (wk-var ≡x .proj₂ .proj₁) v of λ ()
      (inj₂ (n′ , ≡suc , ≡n)) →
        let n″ , t≡ , ≡n′ = wk-suc ≡suc
            s≡ = ⇾*→≡ ⊢s d′
            H′ , d′₁ , H~H₁ = ~⟨⟩-⇾* ok ▸s ⊢s H~H′ d′
        in case isNumeral? n″ of λ where
          (yes num) →
            _ , _ , _ , _ , _ , _ , ⇾*→↠* d′ , ⇾*→↠* d′₁
              , PE.subst Numeral (PE.sym t≡) (sucₙ num)
              , H~H₁
          (no ¬num) →
            -- Using case_of_ instead of let here improves type checking
            -- time significantly.
            case ⊢ₛ-inv (⊢ₛ-⇾* ⊢s d′) of λ
              (_ , _ , ⊢H , ⊢t , ⊢S) →
            case ▸ₛ-inv (▸-⇾* ▸s d′) of λ
              (m , _ , γ , _ , ∣ε∣≡ , ▸H , ▸t , ▸ε , γ≤) →
            case inversion-suc (⊢∷-cong ⊢t (PE.cong (λ x → wk ρ x [ H ]ₕ) t≡)) of λ
              (⊢n″ , _) →
            case inv-usage-suc (PE.subst (_▸[_]_ γ ⌞ m ⌟) t≡ ▸t) of λ
              (invUsageSuc ▸n″ δ≤) →
            case non-interference′ {H = H} {t = n″} {ρ = ρ} {S = ε}
                    ok (▸ₛ ∣ε∣≡ ▸H ▸n″ ▸ε (≤ᶜ-trans γ≤ (+ᶜ-monotoneˡ (·ᶜ-monotoneʳ (wk-≤ᶜ ρ δ≤)))))
                    (⊢ₛ ⊢H ⊢n″ ε) H~H₁
                    x (PE.sym (PE.trans (PE.cong (_[ H ]ₕ) ≡n′) ≡n)) of λ
              (_ , _ , H″ , H‴ , ρ′ , t′ , d₀ , d₀′ , n , H~H₂) →
            _ , _ , _ , _ , _ , _
              , suc-red-lemma ¬num n t≡ d′ d₀
              , suc-red-lemma ¬num n t≡ d′₁ d₀′
              , sucₙ n , H~H₂
  non-interference′ ok ▸s ⊢s H~H′ (ℕₜ u ⇒*u ≅u zeroᵣ) PE.refl =
    let _ , _ , H , t , ρ , (d′ , _) , ≡u , v = whBisim-closed ⊢s ▸s (⇒*u , zeroₙ)
    in  case subst-zero {t = wk ρ t} ≡u of λ where
      (inj₁ (x , ≡x)) →
        let _ , t≡ , _ = wk-var ≡x
        in  case PE.subst Value t≡ v of λ ()
      (inj₂ ≡zero) →
        let _ , d″ , H″~H‴ = ~⟨⟩-⇾* ok ▸s ⊢s H~H′ d′
        in  _ , _ , _ , _ , _ , _
              , ⇾*→↠* d′ , ⇾*→↠* d″
              , PE.subst Numeral (PE.sym (wk-zero ≡zero)) zeroₙ
              , H″~H‴

  non-interference′ ok ▸s ⊢s H~H′ (ℕₜ u ⇒*u ≅u (ne (neNfₜ neK _))) PE.refl =
    let neK = ne→ _ (ne⁻ neK)
        _ , _ , H , t , ρ , d′ , ≡u , v = whBisim-closed ⊢s ▸s (⇒*u , ne neK)
    in  ⊥-elim (Value→¬Neutral (substValue (toSubstₕ H) (wkValue ρ v))
                 (PE.subst (Neutral⁺ ε) (PE.sym ≡u) neK))

opaque

  non-interference :
    No-secret-matches p →
    γ ▸[ 𝟙ᵐ ] t →
    ε » Δ ⊢ t ∷ ℕ →
    γ ▸ʰ H →
    ε ⊢ʰ H ∷ Δ →
    H ~⟨ p ⟩ H′ →
    ∃₆ λ m n H″ H‴ (ρ′ : Wk m n) t′ →
      ⟨ H  , t , id , ε ⟩ ↠* ⟨ H″ , t′ , ρ′ , ε ⟩ ×
      ⟨ H′ , t , id , ε ⟩ ↠* ⟨ H‴ , t′ , ρ′ , ε ⟩ ×
      Numeral t′ × H″ ~⟨ p ⟩ H‴
  non-interference {γ} ok ▸t ⊢t ▸H ⊢H H~H′ =
    let open ≤ᶜ-reasoning
        ▸s = ▸ₛ ε ▸H (▸-cong (PE.sym ⌞𝟙⌟) ▸t) ε $ begin
          γ            ≈˘⟨ ·ᶜ-identityˡ _ ⟩
          𝟙 ·ᶜ γ       ≈˘⟨ +ᶜ-identityʳ _ ⟩
          𝟙 ·ᶜ γ +ᶜ 𝟘ᶜ ∎
        ⊢t′ = substHeapTerm ⊢H (⊢∷-cong ⊢t (PE.sym (wk-id _)))
        ⊢s = ⊢ₛ ⊢H ⊢t′ ε
        _ , _ , _ , _ , _ , _ , d₁ , d₂ , num , H″~H‴ =
          non-interference′ ok ▸s ⊢s H~H′
            (⊩∷ℕ⇔ .proj₁ (reducible-⊩∷ (⊢⦅⦆ ⊢s) .proj₂) )
            PE.refl
    in  _ , _ , _ , _ , _ , _
          , d₁ , d₂ , num , H″~H‴
