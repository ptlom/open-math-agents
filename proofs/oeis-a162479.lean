import OMAStatements.S_oeis_a162479
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
Paul Barry defined OEIS A162479. R. J. Mathar proposed the recurrence in 2011.
Robert Israel used a related differential equation for A162478.
Statement by @ivillar. Full proof by @ptlom with OpenAI Codex (gpt-6.2-astra).
Sources: https://oeis.org/A162479 and https://oeis.org/A162478
-/

open PowerSeries
private abbrev S := PowerSeries ℚ
private noncomputable abbrev x : S := X
private noncomputable def discriminant : S := (1-x)^4 - 4*x

private theorem differential_equation (generating : S)
    (square_identity : discriminant * generating^2 = (1-x)^2) :
    (1-9*x+14*x^2-10*x^3+5*x^4-x^5) * derivative ℚ generating +
    (-3+2*x-6*x^2+4*x^3-x^4) * generating = 0 := by
  have h := congrArg (derivative ℚ) square_identity
  have hg : generating ≠ 0 := by
    intro hz
    have hc := congrArg (constantCoeff (R := ℚ)) square_identity
    rw [hz] at hc
    norm_num [x] at hc
  have e := square_identity
  unfold discriminant at h e
  have d4 : derivative ℚ (4:S) = 0 := by
    exact derivative_C (r := (4:ℚ))
  simp only [map_sub, derivative_one, d4, Derivation.leibniz, derivative_pow,
    smul_eq_mul, derivative_X, x, mul_zero] at h
  apply (mul_eq_zero.mp (show generating * (2 * ((1-9*x+14*x^2-10*x^3+5*x^4-x^5) *
      derivative ℚ generating + (-3+2*x-6*x^2+4*x^3-x^4) * generating)) = 0 from by
    linear_combination (1-x) * h + 2 * e)).resolve_left hg |> fun hh => ?_
  exact (mul_eq_zero.mp hh).resolve_left (fun z => by
    have := congrArg (constantCoeff (R := ℚ)) z
    simp only [map_ofNat, map_zero] at this
    norm_num at this)

/-- Multiplying the derivative by X weights the n-th coefficient by n. -/
private theorem weighted (generating : S) (n : ℕ) :
    coeff n (x * derivative ℚ generating) = (n : ℚ) * coeff n generating := by
  cases n with
  | zero => simp [x]
  | succ n => rw [coeff_succ_X_mul, coeff_derivative]; simp [mul_comm]

theorem OMA.solution : type_of% @OMA.S_oeis_a162479.main := by
  intro T generating hT _hinitial hUnit n hn
  have square_identity : discriminant * generating^2 = (1-x)^2 := by
    change T^2 * (1-x)^4 = discriminant at hT
    calc
      _ = (generating * ((1-x)*T))^2 * (1-x)^2 := by rw [← hT]; ring
      _ = _ := by rw [hUnit]; ring
  let w := x * derivative ℚ generating
  let f := generating
  have eqn : w + (C (-9:ℚ)*w + C (-3:ℚ)*f)*x^1 +
      (C (14:ℚ)*w + C (2:ℚ)*f)*x^2 + (C (-10:ℚ)*w + C (-6:ℚ)*f)*x^3 +
      (C (5:ℚ)*w + C (4:ℚ)*f)*x^4 + (C (-1:ℚ)*w + C (-1:ℚ)*f)*x^5 = 0 := by
    dsimp only [w, f]
    simp only [map_neg, map_ofNat, map_one]
    linear_combination x * differential_equation generating square_identity
  have ec := congrArg (coeff (R := ℚ) n) eqn
  simp only [map_add, map_zero, x, coeff_mul_X_pow', if_pos (show 1 ≤ n by omega),
    if_pos (show 2 ≤ n by omega), if_pos (show 3 ≤ n by omega),
    if_pos (show 4 ≤ n by omega), if_pos hn, coeff_C_mul] at ec
  simp only [w, weighted, f, Nat.cast_sub (show 1 ≤ n by omega),
    Nat.cast_sub (show 2 ≤ n by omega), Nat.cast_sub (show 3 ≤ n by omega),
    Nat.cast_sub (show 4 ≤ n by omega), Nat.cast_sub hn, Nat.cast_ofNat, Nat.cast_one] at ec
  linear_combination ec
