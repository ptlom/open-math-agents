import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.List.Infix

/-!
# The digit-sum conjecture for OEIS A044279

Sequence by Clark Kimberling. Conjecture by Harvey P. Dale.
Source: https://oeis.org/A044279
Credit: @ptlom (with Codex)

Mathlib lists digits from least to most significant, so [1, 3] represents
the substring 31 in the usual base-nine notation. The digit sum is decimal.
If the final base-nine digit is at least two, subtracting one preserves
every earlier digit. Any occurrence of 31 must then also occur in k - 1.
The remaining final digits, zero and one, give the two residues modulo nine.
-/

namespace OMA.S_oeis_a044279

theorem main :
    ∀ k : ℕ, 0 < k →
      ([1, 3] : List ℕ).IsInfix (Nat.digits 9 k) →
      ¬ ([1, 3] : List ℕ).IsInfix (Nat.digits 9 (k - 1)) →
      (Nat.digits 10 k).sum % 9 = 0 ∨ (Nat.digits 10 k).sum % 9 = 1 := by
  intro k hk hnow hprev
  have hsum : k % 9 = (Nat.digits 10 k).sum % 9 :=
    Nat.modEq_digits_sum 9 10 (by decide) k
  rw [← hsum]
  by_contra h
  have hr : 2 ≤ k % 9 := by omega
  have hk' : k - 1 ≠ 0 := by omega
  have hdiv : (k - 1) / 9 = k / 9 := by omega
  rw [Nat.digits_eq_cons_digits_div (by decide : 1 < 9) (by omega : k ≠ 0)] at hnow
  apply hprev
  rw [Nat.digits_eq_cons_digits_div (by decide : 1 < 9) hk', hdiv]
  apply List.infix_cons
  rcases List.infix_cons_iff.mp hnow with hp | ht
  · have hne : 1 ≠ k % 9 := by omega
    simp [List.prefix_cons_iff, hne] at hp
  · exact ht

end OMA.S_oeis_a044279
