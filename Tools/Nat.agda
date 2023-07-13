------------------------------------------------------------------------
-- The natural numbers.
------------------------------------------------------------------------

module Tools.Nat where

-- We reexport Agda's built-in type of natural numbers.

open import Agda.Builtin.Nat using (Nat; _+_; _*_) public
open import Agda.Builtin.Nat using (zero; suc)
import Data.Fin as F
import Data.Fin.Properties as FP
open import Data.Nat.Base
open Data.Nat.Base using (_≤_; _⊔_; _⊓_) public
open import Data.Nat.DivMod
open Data.Nat.DivMod using (_/_; m/n*n≤m) public
open import Data.Nat.Properties
open Data.Nat.Properties
  using (_≟_;
         +-identityʳ; +-assoc; +-comm;
         *-identityʳ; *-assoc; *-comm; *-zeroʳ;
         ⊔-identityʳ; ⊔-assoc; ⊔-comm; ⊔-idem; m≥n⇒m⊔n≡m; m⊔n≡m⇒n≤m;
         ⊓-assoc; ⊓-comm;
         +-distribˡ-⊔; *-distribˡ-+; *-distribˡ-⊔; ⊓-distribʳ-⊔;
         ⊔-absorbs-⊓; ⊓-absorbs-⊔;
         m≤m+n; n≤1+n)
  public
open import Data.Nat.Show using (show) public

open import Tools.Function
open import Tools.PropositionalEquality

pattern 1+ n = suc n

private variable
  k m n o : Nat

private

  -- If 1+ m * n ≤ k + 1+ m * o for some k ≤ m, then
  -- 1+ m * n ≤ 1+ m * o.

  1+*≤+1+*→1+*≤1+* :
    k ≤ m →
    1+ m * n ≤ k + 1+ m * o →
    1+ m * n ≤ 1+ m * o
  1+*≤+1+*→1+*≤1+* {m = m} {n = 0} {o = o} _ _ =
                         $⟨ _≤_.z≤n ⟩
    0 ≤ 1+ m * o         ≡⟨ cong (_≤ 1+ m * o) (sym (*-zeroʳ m)) ⟩→
    1+ m * 0 ≤ 1+ m * o  □
  1+*≤+1+*→1+*≤1+* {k = k} {m = m} {n = 1+ n} {o = 0} k≤m =
    1+ m * 1+ n ≤ k + m * 0  ≡⟨ cong₂ _≤_ (*-comm (1+ m) (1+ n)) (cong (k +_) (*-zeroʳ m)) ⟩→
    1+ n * 1+ m ≤ k + 0      ≡⟨ cong (_ ≤_) (+-identityʳ _) ⟩→
    1+ n * 1+ m ≤ k          →⟨ idᶠ ⟩
    1+ m + n * 1+ m ≤ k      →⟨ m+n≤o⇒m≤o _ ⟩
    m < k                    →⟨ flip ≤-trans k≤m ⟩
    m < m                    →⟨ <-irrefl refl ⟩
    ⊥                        →⟨ ⊥-elim ⟩
    1+ m * 1+ n ≤ m * 0      □
  1+*≤+1+*→1+*≤1+* {k = k} {m = m} {n = 1+ n} {o = 1+ o} k≤m =
    1+ m * 1+ n ≤ k + 1+ m * 1+ o            ≡⟨ cong₂ _≤_ (*-suc (1+ m) _) (cong (k +_) (*-suc (1+ m) _)) ⟩→
    1+ m + 1+ m * n ≤ k + (1+ m + 1+ m * o)  ≡⟨ cong (1+ m + 1+ m * n ≤_) $
                                                trans (sym (+-assoc k (1+ m) _)) $
                                                trans (cong (_+ 1+ m * o) (+-comm k _)) $
                                                +-assoc (1+ m) _ _ ⟩→
    1+ m + 1+ m * n ≤ 1+ m + (k + 1+ m * o)  →⟨ +-cancelˡ-≤ (1+ m) ⟩
    1+ m * n ≤ k + 1+ m * o                  →⟨ 1+*≤+1+*→1+*≤1+* k≤m ⟩
    1+ m * n ≤ 1+ m * o                      →⟨ +-mono-≤ (≤-refl {x = 1+ m}) ⟩
    1+ m + 1+ m * n ≤ 1+ m + 1+ m * o        ≡⟨ sym $ cong₂ _≤_ (*-suc (1+ m) _) (*-suc (1+ m) _) ⟩→
    1+ m * 1+ n ≤ 1+ m * 1+ o                □

-- If 1+ m * n ≤ o, then n ≤ o / 1+ m.

*≤→≤/ : 1+ m * n ≤ o → n ≤ o / 1+ m
*≤→≤/ {m = m} {n = n} {o = o} = helper (o divMod 1+ m)
  where
  helper :
    (d : DivMod o (1+ m)) →
    1+ m * n ≤ o → n ≤ d .DivMod.quotient
  helper (record { quotient = q; remainder = r; property = refl }) =
    1+ m * n ≤ F.toℕ r + q * 1+ m  ≡⟨ cong (λ o → 1+ m * n ≤ F.toℕ r + o) (*-comm q _) ⟩→
    1+ m * n ≤ F.toℕ r + 1+ m * q  →⟨ 1+*≤+1+*→1+*≤1+* (FP.toℕ≤pred[n] r) ⟩
    1+ m * n ≤ 1+ m * q            →⟨ *-cancelˡ-≤ m ⟩
    n ≤ q                          □
