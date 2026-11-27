import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.ModEq

/-!
# Rows ending in 33 in OEIS A372313

Ali Sada proposed the conjecture in https://oeis.org/A372313.
The row update uses A372289, by Antti Karttunen and Ali Sada.
Source: https://oeis.org/A372289
Credit: @ptlom (with Codex)
-/

namespace OMA.S_oeis_a372313

/-- A372289. The exponent is the number of factors of two in the input. -/
def transform (x : ℕ) : ℕ :=
  let e := x.factorization 2
  x * 2 ^ e + (4 ^ e - 1) / 3

/-- A372313 with the original one-based row and column indices.
Column zero is a sentinel outside the sequence. -/
def entry (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 2 * n - 1
  | k + 2 => transform (entry n (k + 1) + (2 * n - 1))

private theorem transform_of_two_mod_four (x : ℕ) (hx : x % 4 = 2) :
    transform x = 2 * x + 1 := by
  have half : (x / 2).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by omega)
  have he : x.factorization 2 = 1 := calc
    x.factorization 2 = (2 * (x / 2)).factorization 2 :=
      congrArg (fun t : ℕ => t.factorization 2) (by omega)
    _ = 1 := by
      rw [Nat.factorization_mul (by decide) (by omega), Finsupp.add_apply, half]
      simp [Nat.prime_two.factorization]
  simp [transform, he, Nat.mul_comm]

/-- If the first entry ends in 33, every entry in that row ends in 33. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → entry n 1 % 100 = 33 →
      ∀ k : ℕ, 1 ≤ k → entry n k % 100 = 33 := by
  intro n _ hfirst k hk
  change (2 * n - 1) % 100 = 33 at hfirst
  cases k with
  | zero => omega
  | succ j =>
    induction j with
    | zero => exact hfirst
    | succ j ih =>
      simp only [entry]
      rw [transform_of_two_mod_four]
      · have prev := ih (by omega)
        omega
      · have prev := ih (by omega)
        omega

/-- For every modulus divisible by four, this criterion characterizes exactly
the rows with a constant residue. -/
theorem constant_residue_iff (n m : ℕ) (hn : 1 ≤ n) (hm : 4 ∣ m) :
    (∀ j : ℕ, entry n (j + 1) ≡ (2*n-1) [MOD m]) ↔ m ∣ 3*(2*n-1)+1 := by
  let s := 2*n-1
  change (∀ j : ℕ, entry n (j+1) ≡ s [MOD m]) ↔ m ∣ 3*s+1
  constructor
  · intro h
    have h2 := h 1
    change transform (s+s) ≡ s [MOD m] at h2
    rw [transform_of_two_mod_four (s+s) (by dsimp [s]; omega)] at h2
    rw [show 2*(s+s)+1 = s+(3*s+1) by omega] at h2
    exact Nat.add_modEq_left_iff.mp h2
  · intro hd
    have h4 : 4 ∣ 3*s+1 := dvd_trans hm hd
    have hs : s % 4 = 1 := by omega
    intro j
    induction j with
    | zero => exact Nat.ModEq.refl _
    | succ j ih =>
      change transform (entry n (j+1) + s) ≡ s [MOD m]
      have hprev : entry n (j+1) ≡ s [MOD 4] := ih.of_dvd hm
      change entry n (j+1) % 4 = s % 4 at hprev
      rw [transform_of_two_mod_four _ (by omega)]
      calc
        2*(entry n (j+1)+s)+1 ≡ 2*(s+s)+1 [MOD m] :=
          ((ih.add_right s).mul_left 2).add_right 1
        _ = s+(3*s+1) := by omega
        _ ≡ s [MOD m] := Nat.add_modEq_left_iff.mpr hd

/-- The only possible constant last two digits are 33. -/
theorem unique_two_digit_ending (n : ℕ) (hn : 1 ≤ n) :
    (∀ j : ℕ, entry n (j+1) % 100 = (2*n-1) % 100) ↔ (2*n-1) % 100 = 33 := by
  rw [show (∀ j : ℕ, entry n (j+1) % 100 = (2*n-1) % 100) ↔
    100 ∣ 3*(2*n-1)+1 from constant_residue_iff n 100 hn (by decide)]
  omega

/-- The number written with exactly d threes, with zero for the empty string. -/
def threes : ℕ → ℕ
  | 0 => 0
  | d+1 => 10 * threes d + 3

private theorem three_times_threes (d : ℕ) : 3 * threes d + 1 = 10^d := by
  induction d with
  | zero => rfl
  | succ d ih => rw [threes, pow_succ]; omega

/-- For suffixes of length at least two, the string of threes is the unique
constant decimal suffix. Every row starting with that suffix retains it. -/
theorem decimal_suffix_iff (n d : ℕ) (hn : 1 ≤ n) (hd : 2 ≤ d) :
    (∀ j : ℕ, entry n (j+1) ≡ (2*n-1) [MOD 10^d]) ↔
      (2*n-1) ≡ threes d [MOD 10^d] := by
  have h4 : 4 ∣ (10:ℕ)^d := dvd_trans (show 4 ∣ (10:ℕ)^2 by decide)
    (pow_dvd_pow 10 hd)
  rw [constant_residue_iff n (10^d) hn h4]
  have base : (3*threes d+1) ≡ 0 [MOD 10^d] := by
    rw [three_times_threes]; exact Nat.modulus_modEq_zero
  constructor
  · intro h
    have eqn := h.modEq_zero_nat.trans base.symm
    have hc : Nat.Coprime (10^d) 3 := (show Nat.Coprime 10 3 by decide).pow_left d
    exact Nat.ModEq.cancel_left_of_coprime hc (Nat.ModEq.add_right_cancel' 1 eqn)
  · intro h
    exact Nat.modEq_zero_iff_dvd.mp (((h.mul_left 3).add_right 1).trans base)

end OMA.S_oeis_a372313
