{-# OPTIONS --without-K  #-}

open import Definition.Modality.Erasure

open import Definition.Typed.EqualityRelation

module Erasure.LogicalRelation.Properties {{eqrel : EqRelSet Erasure}} where
open EqRelSet {{...}}

open import Definition.LogicalRelation Erasure
import Definition.LogicalRelation.Fundamental Erasure as F
open import Definition.LogicalRelation.Fundamental.Reducibility  Erasure
open import Definition.LogicalRelation.Properties.Escape Erasure
open import Definition.LogicalRelation.Substitution Erasure
import Definition.LogicalRelation.Substitution.Irrelevance Erasure as I
open import Definition.LogicalRelation.Substitution.Properties Erasure

open import Definition.Typed Erasure
open import Definition.Typed.Consequences.Canonicity Erasure
open import Definition.Typed.Consequences.Substitution Erasure
open import Definition.Typed.Consequences.Syntactic Erasure
open import Definition.Typed.Consequences.RedSteps Erasure as RS′
open import Definition.Typed.Properties Erasure
open import Definition.Typed.RedSteps Erasure as RS
open import Definition.Typed.Weakening Erasure

open import Definition.Untyped Erasure as U hiding (_∷_)
open import Definition.Untyped.Properties Erasure using (noClosedNe ; wk-id ; wk-lift-id)

open import Erasure.Extraction
open import Erasure.Extraction.Properties
open import Erasure.LogicalRelation
open import Erasure.Target as T hiding (_⇒*_)
open import Erasure.Target.Properties.Reduction as TP

open import Tools.Empty
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Sum hiding (id ; sym)

private
  variable
    n : Nat
    t t′ A : U.Term 0
    v v′ : T.Term 0

-- Related terms are well-formed

wfTermEscapeℕ : t ® v ∷ℕ → ε ⊢ t ∷ ℕ
wfTermEscapeℕ (zeroᵣ x x₁) = redFirst*Term x
wfTermEscapeℕ (sucᵣ x x₁ t®v) = redFirst*Term x

wfTermEscapeU : t ® v ∷U → ε ⊢ t ∷ U
wfTermEscapeU (Uᵣ x x₁) = x

wfTermEscapeUnit : t ® v ∷Unit → ε ⊢ t ∷ Unit
wfTermEscapeUnit (starᵣ x x₁) = x

wfTermEscapeEmpty : t ® v ∷Empty → ε ⊢ t ∷ Empty
wfTermEscapeEmpty ()



-- Relation is preserved by reduction backwards

®-back-closureˡ : ∀ {l} ([A] : ε ⊩⟨ l ⟩ A) → t′ ®⟨ l ⟩ v ∷ A / [A] → ε ⊢ t ⇒* t′ ∷ A → t ®⟨ l ⟩ v ∷ A / [A]
®-back-closureˡ (Uᵣ x) (Uᵣ x₁ x₂) t⇒t′ = Uᵣ (redFirst*Term t⇒t′) x₂
®-back-closureˡ (ℕᵣ [ ⊢A , ⊢B , D ]) (zeroᵣ t′⇒zero v⇒zero) t⇒t′ = zeroᵣ
  ((conv* t⇒t′ (subset* D)) ⇨∷* t′⇒zero)
  v⇒zero
®-back-closureˡ [ℕ]@(ℕᵣ ([ ⊢A , ⊢B , D ])) (sucᵣ t⇒suct′ v⇒sucv′ t′®v′) t⇒t′ = sucᵣ
  ((conv* t⇒t′ (subset* D)) ⇨∷* t⇒suct′)
  v⇒sucv′
  t′®v′
®-back-closureˡ (Emptyᵣ [ ⊢A , ⊢B , D ]) () t⇒t′
®-back-closureˡ (Unitᵣ [ ⊢A , ⊢B , D ]) (starᵣ ⊢t′:Unit v⇒star) t⇒t′ = starᵣ
  (redFirst*Term (conv* t⇒t′ (subset* D)))
  v⇒star
®-back-closureˡ (ne′ K D neK K≡K) t′®v t⇒t′ with noClosedNe neK
... | ()
®-back-closureˡ {A} (Bᵣ′ (BΠ 𝟘 q) F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext) t®v t⇒t′ [a] = ®-back-closureˡ
  ([G] id ε [a])
  (t®v [a])
  (RS.app-subst* (conv* t⇒t′
                              (PE.subst (ε ⊢ A ≡_)
                                        ((PE.cong₂ (⟦ BΠ 𝟘 q ⟧_▹_))
                                                   (PE.sym (wk-id F))
                                                   (PE.sym (wk-lift-id G)))
                                        (subset* D)))
                       (escapeTerm ([F] id ε) [a]))
®-back-closureˡ {A} (Bᵣ′ (BΠ ω q) F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext) t®v t⇒t′ [a] a®w = ®-back-closureˡ
  ([G] id ε [a])
  (t®v [a] a®w)
  (RS.app-subst* (conv* t⇒t′
                              (PE.subst (ε ⊢ A ≡_)
                                        (PE.cong₂ (⟦ BΠ ω q ⟧_▹_)
                                                  (PE.sym (wk-id F))
                                            (PE.sym (wk-lift-id G)))
                                  (subset* D)))
                 (escapeTerm ([F] id ε) [a]))
®-back-closureˡ (Bᵣ′ (BΣ q) F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext) t®v t⇒t′ [t₁] = {!!}
-- ®-back-closureˡ ([F] id ε) {!proj₁ (t®v ?)!} (id {!!}) , {!!}
  where
  t₁⇒t′₁ = RS′.fst-subst* (conv* t⇒t′ (subset* D))
  [t′₁] = proj₂ (reducibleTerm (proj₂ (proj₂ (syntacticRedTerm t₁⇒t′₁))))
  a = t®v {![t′₁]!}
  IH = ®-back-closureˡ ([F] id ε) (proj₁ a) {!!}
  -- let ®Σ = t®v [t₁] [t₂]
  --     t′⇒p = proj₁ ®Σ
  --     v⇒w = proj₁ (proj₂ ®Σ)
  --     t₁®v₁ = proj₁ (proj₂ (proj₂ ®Σ))
  --     t₂®v₂ = proj₂ (proj₂ (proj₂ ®Σ))
  -- in  ((conv* t⇒t′ (subset* D)) ⇨∷* t′⇒p) , v⇒w , t₁®v₁ , t₂®v₂
®-back-closureˡ (emb 0<1 [A]) t′®v t⇒t′ = ®-back-closureˡ [A] t′®v t⇒t′


®-back-closureʳ : ∀ {l} ([A] : ε ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v′ ∷ A / [A] → v T.⇒* v′ → t ®⟨ l ⟩ v ∷ A / [A]
®-back-closureʳ (Uᵣ x) (Uᵣ ⊢t:U v′⇒undefined) v⇒v′ = Uᵣ ⊢t:U (red*concat v⇒v′ v′⇒undefined)
®-back-closureʳ (ℕᵣ x) (zeroᵣ t⇒zero v′⇒zero) v⇒v′ = zeroᵣ t⇒zero (red*concat v⇒v′ v′⇒zero)
®-back-closureʳ (ℕᵣ x) (sucᵣ t⇒suct′ v′⇒sucw t′®w) v⇒v′ = sucᵣ t⇒suct′ (red*concat v⇒v′ v′⇒sucw) t′®w
®-back-closureʳ (Emptyᵣ x) () v⇒v′
®-back-closureʳ (Unitᵣ x) (starᵣ t⇒star v′⇒star) v⇒v′ = starᵣ t⇒star (red*concat v⇒v′ v′⇒star)
®-back-closureʳ (ne′ K D neK K≡K) t®v′ v⇒v′ with noClosedNe neK
... | ()
®-back-closureʳ (Bᵣ′ (BΠ 𝟘 q) F G D ⊢F ⊢G A≡A [F] [G] G-ext) t®v v⇒v′ [a] = ®-back-closureʳ ([G] id ε [a]) (t®v [a]) (TP.app-subst* v⇒v′)
®-back-closureʳ (Bᵣ′ (BΠ ω q) F G D ⊢F ⊢G A≡A [F] [G] G-ext) t®v v⇒v′ [a] a®w = ®-back-closureʳ ([G] id ε [a]) (t®v [a] a®w) (TP.app-subst* v⇒v′)
®-back-closureʳ (Bᵣ′ (BΣ q) F G D ⊢F ⊢G A≡A [F] [G] G-ext) t®v v⇒v′ [t₁] =
  let ®Σ = t®v [t₁]
  in (®-back-closureʳ ([F] id ε) (proj₁ ®Σ) (TP.fst-subst* v⇒v′))
    , ®-back-closureʳ ([G] id ε [t₁]) (proj₂ ®Σ) (TP.snd-subst* v⇒v′)
®-back-closureʳ (emb 0<1 [A]) t®v′ v⇒v′ = ®-back-closureʳ [A] t®v′ v⇒v′


®-back-closure : ∀ {l} ([A] : ε ⊩⟨ l ⟩ A) → t′ ®⟨ l ⟩ v′ ∷ A / [A] → ε ⊢ t ⇒* t′ ∷ A → v T.⇒* v′ → t ®⟨ l ⟩ v ∷ A / [A]
®-back-closure [A] t′®v′ t⇒t′ v⇒v′ = ®-back-closureˡ [A] (®-back-closureʳ [A] t′®v′ v⇒v′) t⇒t′


®-forward-closureˡ : ∀ {l} ([A] : ε ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v ∷ A / [A] → ε ⊢ t ⇒* t′ ∷ A → t′ ®⟨ l ⟩ v ∷ A / [A]
®-forward-closureˡ (Uᵣ′ l′ l< ⊢Γ) (Uᵣ ⊢t:U v⇒undefined) t⇒t′ = Uᵣ {!!} v⇒undefined
®-forward-closureˡ (ℕᵣ [ ⊢A , ⊢B , D ]) (zeroᵣ t⇒zero v⇒zero) t⇒t′ with whrDet↘Term (t⇒zero , zeroₙ) (conv* t⇒t′ (subset* D))
... | t′⇒zero = zeroᵣ t′⇒zero v⇒zero
®-forward-closureˡ [ℕ]@(ℕᵣ ([ ⊢A , ⊢B , D ])) (sucᵣ t⇒sucu v⇒sucw u®w) t⇒t′ with whrDet↘Term (t⇒sucu , sucₙ) (conv* t⇒t′ (subset* D))
... | t′⇒sucu = sucᵣ t′⇒sucu v⇒sucw u®w
®-forward-closureˡ (Emptyᵣ [ ⊢A , ⊢B , D ]) () t⇒t′
®-forward-closureˡ (Unitᵣ [ ⊢A , ⊢B , D ]) (starᵣ ⊢t:Unit v⇒star) t⇒t′ = starᵣ {!!} v⇒star
®-forward-closureˡ (ne′ K D neK K≡K) t®v t⇒t′ with noClosedNe neK
... | ()
®-forward-closureˡ {A = A} (Bᵣ′ (BΠ 𝟘 q) F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext) t®v t⇒t′ [a] = ®-forward-closureˡ
  ([G] id ε [a]) (t®v [a])
  (RS.app-subst* (conv* t⇒t′ (PE.subst (ε ⊢ A ≡_)
                                       (PE.cong₂ (⟦ BΠ 𝟘 q ⟧_▹_)
                                                 (PE.sym (wk-id F))
                                                 (PE.sym (wk-lift-id G)))
                                       (subset* D)))
                 (escapeTerm ([F] id ε) [a]))
®-forward-closureˡ {A = A} (Bᵣ′ (BΠ ω q) F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext) t®v t⇒t′ [a] a®w = ®-forward-closureˡ
  ([G] id ε [a]) (t®v [a] a®w)
  (RS.app-subst* (conv* t⇒t′ (PE.subst (ε ⊢ A ≡_)
                                       (PE.cong₂ (⟦ BΠ ω q ⟧_▹_)
                                                 (PE.sym (wk-id F))
                                                 (PE.sym (wk-lift-id G)))
                                       (subset* D)))
                 (escapeTerm ([F] id ε) [a]))
®-forward-closureˡ (Bᵣ′ (BΣ p) F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext) t®v t⇒t′ [t′₁] =
 let [t₁] = {!!}
     ®Σ = t®v [t₁]
 in (®-forward-closureˡ ([F] id ε) (proj₁ ®Σ) {!RS′.fst-subst* t⇒t′!}) , {!!}
-- [t₁] [t₂] with t®v [t₁] [t₂]
-- ... | t⇒p , v⇒w , t₁®v₁ , t₂®v₂ with whrDet↘Term (t⇒p , prodₙ) (conv* t⇒t′ (subset* D))
-- ... | t′⇒p = t′⇒p , v⇒w , t₁®v₁ , t₂®v₂
®-forward-closureˡ (emb 0<1 [A]) t®v t⇒t′ = ®-forward-closureˡ [A] t®v t⇒t′


®-forward-closureʳ : ∀ {l} ([A] : ε ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v ∷ A / [A] → v T.⇒* v′ → t ®⟨ l ⟩ v′ ∷ A / [A]
®-forward-closureʳ (Uᵣ x) (Uᵣ ⊢t:U v⇒undefined) v⇒v′ with red*Det v⇒v′ v⇒undefined
... | inj₁ v′⇒undefined = Uᵣ ⊢t:U v′⇒undefined
... | inj₂ undefined⇒v′ rewrite undefined-noRed undefined⇒v′ = Uᵣ ⊢t:U refl
®-forward-closureʳ (ℕᵣ x) (zeroᵣ t⇒zero v⇒zero) v⇒v′ with red*Det v⇒v′ v⇒zero
... | inj₁ v′⇒zero = zeroᵣ t⇒zero v′⇒zero
... | inj₂ zero⇒v′ rewrite zero-noRed zero⇒v′ = zeroᵣ t⇒zero refl
®-forward-closureʳ (ℕᵣ x) (sucᵣ t⇒suct′ v⇒sucv′ t′®v′) v⇒v′ with red*Det v⇒v′ v⇒sucv′
... | inj₁ v′⇒sucw = sucᵣ t⇒suct′ v′⇒sucw t′®v′
... | inj₂ sucw⇒v′ rewrite suc-noRed sucw⇒v′ = sucᵣ t⇒suct′ refl t′®v′
®-forward-closureʳ (Emptyᵣ x) () v⇒v′
®-forward-closureʳ (Unitᵣ x) (starᵣ ⊢t:Unit v⇒star) v⇒v′ with red*Det v⇒v′ v⇒star
... | inj₁ v′⇒star = starᵣ ⊢t:Unit v′⇒star
... | inj₂ star⇒v′ rewrite star-noRed star⇒v′ = starᵣ ⊢t:Unit refl
®-forward-closureʳ (ne′ K D neK K≡K) t®v v⇒v′ with noClosedNe neK
... | ()
®-forward-closureʳ (Bᵣ′ (BΠ 𝟘 q) F G D ⊢F ⊢G A≡A [F] [G] G-ext) t®v v⇒v′ [a] = ®-forward-closureʳ ([G] id ε [a]) (t®v [a]) (TP.app-subst* v⇒v′)
®-forward-closureʳ (Bᵣ′ (BΠ ω q) F G D ⊢F ⊢G A≡A [F] [G] G-ext) t®v v⇒v′ [a] a®w = ®-forward-closureʳ ([G] id ε [a]) (t®v [a] a®w) (TP.app-subst* v⇒v′)
®-forward-closureʳ (Bᵣ′ (BΣ p) F G D ⊢F ⊢G A≡A [F] [G] G-ext) t®v v⇒v′ [t₁] with t®v [t₁]
... | a , b = {!®-forward-closureʳ ? a v⇒v′!} , {!!}
-- [t₁] [t₂] with t®v [t₁] [t₂]
-- ... | t⇒p , v⇒w , t₁®v₁ , t₂®v₂ with red*Det v⇒v′ v⇒w
-- ... | inj₁ v′⇒w = t⇒p , v′⇒w , t₁®v₁ , t₂®v₂
-- ... | inj₂ w⇒v′ rewrite prod-noRed w⇒v′ = t⇒p , refl , t₁®v₁ , t₂®v₂
®-forward-closureʳ (emb 0<1 [A]) t®v v⇒v′ = ®-forward-closureʳ [A] t®v v⇒v′



fundamental : ∀ {Γ : Con U.Term n} {t A : U.Term n} {σₜₛ : U.Subst 0 n} {l}
            → Γ ⊢ t ∷ A
            → ([Γ] : ⊩ᵛ Γ)
            → ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ])
            → ([ts] : ε ⊩ˢ σₜₛ ∷ Γ / [Γ] / ε)
            → (ts®vs : Γ ⊩ σₜₛ ®⟨ ¹ ⟩ eraseSubst σₜₛ / [Γ])
            → ∃ λ [A]′ → U.subst σₜₛ t ®⟨ ¹ ⟩ T.subst (eraseSubst σₜₛ) (erase t) ∷ U.subst σₜₛ A / [A]′
fundamental (Πⱼ Γ⊢F:U ▹ Γ⊢G:U) [Γ] [A] [ts] ts®vs =
  let [U] = Uᵣ (Uᵣ ⁰ 0<1 ε)
      Γ⊢F = univ Γ⊢F:U
      ⊢σF:U = substitutionTerm Γ⊢F:U (wellformedSubst [Γ] ε [ts]) ε
      ⊢σF = univ ⊢σF:U
      [Γ]′ , [F]′ = F.fundamental Γ⊢F
      [F] = I.irrelevance [Γ]′ [Γ] [F]′
      [⇑ts] = liftSubstS [Γ] ε [F] [ts]
      ⊢σG:U = substitutionTerm Γ⊢G:U (wellformedSubst ([Γ] ∙ [F]) (ε ∙ ⊢σF) [⇑ts]) (ε ∙ ⊢σF)
  in  [U] , Uᵣ (Πⱼ ⊢σF:U ▹ ⊢σG:U) refl
fundamental (Σⱼ Γ⊢F:U ▹ Γ⊢G:U) [Γ] [A] [ts] ts®vs =
  let [U] = Uᵣ (Uᵣ ⁰ 0<1 ε)
      Γ⊢F = univ Γ⊢F:U
      ⊢σF:U = substitutionTerm Γ⊢F:U (wellformedSubst [Γ] ε [ts]) ε
      ⊢σF = univ ⊢σF:U
      [Γ]′ , [F]′ = F.fundamental Γ⊢F
      [F] = I.irrelevance [Γ]′ [Γ] [F]′
      [⇑ts] = liftSubstS [Γ] ε [F] [ts]
      ⊢σG:U = substitutionTerm Γ⊢G:U (wellformedSubst ([Γ] ∙ [F]) (ε ∙ ⊢σF) [⇑ts]) (ε ∙ ⊢σF)
  in  [U] , Uᵣ (Σⱼ ⊢σF:U ▹ ⊢σG:U) refl
fundamental (ℕⱼ x) [Γ] [A] [ts] ts®vs = Uᵣ (Uᵣ ⁰ 0<1 ε) , Uᵣ (ℕⱼ ε) refl
fundamental (Emptyⱼ x) [Γ] [A] [ts] ts®vs = Uᵣ (Uᵣ ⁰ 0<1 ε) , Uᵣ (Emptyⱼ ε) refl
fundamental (Unitⱼ x) [Γ] [A] [ts] ts®vs = Uᵣ (Uᵣ ⁰ 0<1 ε) , Uᵣ (Unitⱼ ε) refl
fundamental (var ⊢Γ here) [Γ] [A] [ts] ts®vs = proj₁ ([A] ε [ts]) , {!!}
fundamental (var (⊢Γ ∙ ⊢B) (there x)) ([Γ] ∙ [B]) [A] ([ts] , [t]) ts®vs =
  let [A]′ , x®x′ = fundamental (var ⊢Γ x) [Γ] {![B]!} [ts] {!!}
  in  ? , ?
fundamental (lamⱼ x ⊢t:A) [Γ] [A] [ts] ts®vs =
  let [Π] = proj₁ ([A] ε [ts])
  in  [Π] , {!!}
fundamental (⊢t:Π ∘ⱼ ⊢u:F) [Γ] [A] [ts] ts®vs =
  let [Γ]₁ , [F]′ = F.fundamental (syntacticTerm ⊢t:Π)
      [F] = I.irrelevance [Γ]₁ [Γ] [F]′
      [Π] , t®v = fundamental ⊢t:Π [Γ] [F] [ts] ts®vs
  in  proj₁ ([A] ε [ts]) , {!t®v ?!}
fundamental (prodⱼ x x₁ ⊢t:A ⊢t:A₁) [Γ] [A] [ts] ts®vs = {!!} , {!!}
fundamental (fstⱼ x x₁ ⊢t:A) [Γ] [A] [ts] ts®vs = {!!} , {!!}
fundamental (sndⱼ x x₁ ⊢t:A) [Γ] [A] [ts] ts®vs = {!!}
fundamental (prodrecⱼ x x₁ ⊢t:A x₂ ⊢t:A₁) [Γ] [A] [ts] ts®vs = {!!}
fundamental (zeroⱼ x) [Γ] [A] [ts] ts®vs = (ℕᵣ ([ ℕⱼ ε , ℕⱼ ε , id (ℕⱼ ε) ])) , (zeroᵣ (id (zeroⱼ ε)) refl)
fundamental (sucⱼ ⊢t:A) [Γ] [A] [ts] ts®vs = {!!} , {!!}
fundamental (natrecⱼ x ⊢t:A ⊢t:A₁ ⊢t:A₂) [Γ] [A] [ts] ts®vs = {!!}
fundamental (Emptyrecⱼ x ⊢t:A) [Γ] [A] [ts] ts®vs =
  ⊥-elim (¬Empty (substitutionTerm ⊢t:A (wellformedSubst [Γ] ε [ts]) ε))
fundamental (starⱼ x) [Γ] [A] [ts] ts®vs =
  Unitᵣ ([ Unitⱼ ε , Unitⱼ ε , id (Unitⱼ ε) ]) , starᵣ (starⱼ ε) refl
fundamental (conv ⊢t:A x) [Γ] [B] [ts] ts®vs = {!!} , {!!}

