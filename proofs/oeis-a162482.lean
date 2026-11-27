import OMAStatements.S_oeis_a162482
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
Paul Barry defined OEIS A162482. R. J. Mathar conjectured this recurrence
in 2015. Jean-François Alcover supplied a Motzkin-number computation.
Source: https://oeis.org/A162482
Statement by @ivillar. Formal proof by @ptlom with OpenAI Codex (gpt-6.2-astra).
-/

open PowerSeries
private abbrev S := PowerSeries ℚ
private noncomputable abbrev x : S := X

/-- Multiplying the derivative by X weights the n-th coefficient by n. -/
private theorem weighted (generating : S) (n : ℕ) :
    coeff n (x * derivative ℚ generating) = (n : ℚ) * coeff n generating := by
  cases n with
  | zero => simp [x]
  | succ n => rw [coeff_succ_X_mul, coeff_derivative]; simp [mul_comm]

/-- A formal square root of D satisfies 2 D S' = D' S. -/
private theorem square_ode (r d : S) (hs : r^2 = d) :
    2 * d * derivative ℚ r - derivative ℚ d * r = 0 := by
  have hd := congrArg (derivative ℚ) hs
  simp only [derivative_pow] at hd
  linear_combination r*hd - 2 * derivative ℚ r * hs

theorem OMA.solution : type_of% @OMA.S_oeis_a162482.main := by
  intro T G hT _h0 hG n hn
  have hr : (1-x)^3 - x - 2*x^2*G = T*(1-x)^3 := by linear_combination -hG
  have hs : ((1-x)^3 - x - 2*x^2*G)^2 = ((1-x)^3-x)^2 - 4*x^2 := by
    rw [hr]
    linear_combination hT
  have ho := square_ode _ _ hs
  have d2 : derivative ℚ (2:S) = 0 := derivative_C (r := (2:ℚ))
  have d4 : derivative ℚ (4:S) = 0 := derivative_C (r := (4:ℚ))
  simp only [map_sub, derivative_one, Derivation.leibniz, derivative_pow,
    smul_eq_mul, d2, d4, derivative_X, x, mul_zero] at ho
  have h4 : (4:S) ≠ 0 := by
    intro z
    have := congrArg (constantCoeff (R := ℚ)) z
    simp only [map_ofNat, map_zero] at this
    norm_num at this
  let w := x * derivative ℚ G
  have eqn : w + C (2:ℚ)*G + (C (-8:ℚ)*w + C (-12:ℚ)*G)*x^1 +
      (C (18:ℚ)*w + C (18:ℚ)*G)*x^2 + (C (-26:ℚ)*w + C (-13:ℚ)*G)*x^3 +
      (C (17:ℚ)*w)*x^4 + (C (-6:ℚ)*w + C (3:ℚ)*G)*x^5 + (w - G)*x^6 =
      C (2:ℚ) + C (-6:ℚ)*x^2 + C (4:ℚ)*x^3 := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp _).resolve_left (mul_ne_zero h4 (X_ne_zero (R := ℚ)))
    dsimp only [w, x]
    simp only [map_neg, map_ofNat]
    linear_combination -ho
  have ec := congrArg (coeff (R := ℚ) n) eqn
  simp only [map_add, map_sub, x, coeff_mul_X_pow', if_pos (show 1 ≤ n by omega),
    if_pos (show 2 ≤ n by omega), if_pos (show 3 ≤ n by omega),
    if_pos (show 4 ≤ n by omega), if_pos (show 5 ≤ n by omega), if_pos hn,
    coeff_C_mul, coeff_C, if_neg (show n ≠ 0 by omega),
    if_neg (show n - 2 ≠ 0 by omega), if_neg (show n - 3 ≠ 0 by omega),
    add_zero] at ec
  simp only [w, weighted, Nat.cast_sub (show 1 ≤ n by omega),
    Nat.cast_sub (show 2 ≤ n by omega), Nat.cast_sub (show 3 ≤ n by omega),
    Nat.cast_sub (show 4 ≤ n by omega), Nat.cast_sub (show 5 ≤ n by omega),
    Nat.cast_sub hn, Nat.cast_ofNat, Nat.cast_one] at ec
  linear_combination ec
