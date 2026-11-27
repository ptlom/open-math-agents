import OMAStatements.S_oeis_a162481
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
Paul Barry defined OEIS A162481. R. J. Mathar conjectured this recurrence in 2011.
The proof uses Vaclav Kotesovec's radical formula. Ilya Gutkovskiy recorded
the quadratic equation for the same generating function; Amiram Eldar supplied
the Catalan sum implementation. Source: https://oeis.org/A162481
Statement by @ivillar. Formal proof by @ptlom with OpenAI Codex (gpt-6.2-astra).
-/

open PowerSeries
private abbrev S := PowerSeries ℚ
private noncomputable abbrev x : S := X

private theorem series_two_ne_zero : (2:S) ≠ 0 := by
  intro z
  have := congrArg (constantCoeff (R := ℚ)) z
  simp only [map_ofNat, map_zero] at this
  norm_num at this

/-- Clear the radical by differentiating its square and eliminating the square. -/
private theorem radical_ode (T : S)
    (hT : T^2 * (1-x)^3 = (1-x)^3 - 4*x) :
    (1-8*x+10*x^2-4*x^3+x^4) * derivative ℚ T + (2+4*x)*T = 0 := by
  have h := congrArg (derivative ℚ) hT
  have d4 : derivative ℚ (4:S) = 0 := derivative_C (r := (4:ℚ))
  simp only [map_sub, derivative_one, d4, Derivation.leibniz, derivative_pow,
    smul_eq_mul, derivative_X, x, mul_zero] at h
  have hz : (2:S) * ((1-8*x+10*x^2-4*x^3+x^4) * derivative ℚ T + (2+4*x)*T) = 0 := by
    linear_combination (1-x)*T*h + (3*T-2*(1-x)*derivative ℚ T)*hT
  exact (mul_eq_zero.mp hz).resolve_left series_two_ne_zero

/-- Multiplying the derivative by X weights the n-th coefficient by n. -/
private theorem weighted (generating : S) (n : ℕ) :
    coeff n (x * derivative ℚ generating) = (n : ℚ) * coeff n generating := by
  cases n with
  | zero => simp [x]
  | succ n => rw [coeff_succ_X_mul, coeff_derivative]; simp [mul_comm]

theorem OMA.solution : type_of% @OMA.S_oeis_a162481.main := by
  intro T G hT _h0 hG n hn
  have ht := radical_ode T hT
  have he : T = 1 - 2*x*G := by linear_combination hG
  rw [he] at ht
  have d2 : derivative ℚ (2:S) = 0 := derivative_C (r := (2:ℚ))
  simp only [map_sub, derivative_one, Derivation.leibniz, d2, x, derivative_X,
    smul_eq_mul, mul_zero] at ht
  let w := x * derivative ℚ G
  have eqn : w + G + (C (-8:ℚ)*w + C (-6:ℚ)*G)*x^1 +
      (C (10:ℚ)*w + C (14:ℚ)*G)*x^2 + (C (-4:ℚ)*w + C (-4:ℚ)*G)*x^3 +
      (w + G)*x^4 = 1 + C (2:ℚ)*x := by
    dsimp only [w]
    simp only [map_neg, map_ofNat]
    have hz : (2:S) * ((x * derivative ℚ G + G +
        (-8*(x*derivative ℚ G) + -6*G)*x^1 +
        (10*(x*derivative ℚ G) + 14*G)*x^2 +
        (-4*(x*derivative ℚ G) + -4*G)*x^3 +
        (x*derivative ℚ G+G)*x^4) - (1+2*x)) = 0 := by
      linear_combination -ht
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left series_two_ne_zero)
  have ec := congrArg (coeff (R := ℚ) n) eqn
  have h0 : n ≠ 0 := by omega
  have h1 : n ≠ 1 := by omega
  simp only [map_add, x, coeff_mul_X_pow', if_pos (show 1 ≤ n by omega),
    if_pos (show 2 ≤ n by omega), if_pos (show 3 ≤ n by omega),
    if_pos hn, coeff_C_mul, coeff_one, coeff_X, if_neg h0, if_neg h1,
    mul_zero, add_zero] at ec
  simp only [w, weighted, Nat.cast_sub (show 1 ≤ n by omega),
    Nat.cast_sub (show 2 ≤ n by omega), Nat.cast_sub (show 3 ≤ n by omega),
    Nat.cast_sub hn, Nat.cast_ofNat, Nat.cast_one] at ec
  linear_combination ec
