import OMAStatements.S_oeis_a162479
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# A five-step recurrence for OEIS A162479

Paul Barry defined the sequence in 2009. R. J. Mathar proposed the
recurrence in 2011. Robert Israel used a related differential equation
for the adjacent sequence A162478 in 2017.
Sources: https://oeis.org/A162479 and https://oeis.org/A162478
Formal proof: @ptlom with OpenAI Codex (gpt-6.2-astra).
-/

open OMA.S_oeis_a162479 PowerSeries

private theorem binomial_identity :
    (1 + X : S) * binomialSeries ℚ (-1/2 : ℚ)^2 = 1 := by
  have add := binomialSeries_add (A := ℚ) (-1/2:ℚ) (-1/2:ℚ)
  have one := binomialSeries_nat (R := ℚ) (A := ℚ) 1
  rw [pow_one] at one
  change binomialSeries ℚ (1:ℚ) = 1 + X at one
  rw [pow_two, ← add, ← one, ← binomialSeries_add,
    show (1:ℚ)+(-1/2+ -1/2) = 0 by norm_num, binomialSeries_zero]

private theorem substitutable : HasSubst (discriminant - 1) := by
  apply HasSubst.of_constantCoeff_zero
  change constantCoeff (discriminant - 1) = 0
  simp only [discriminant, x, map_sub, map_mul, map_pow, map_one, constantCoeff_X, mul_zero]
  norm_num

private theorem substituted (H : S →ₐ[ℚ] S) (hx : H X = discriminant - 1) :
    discriminant * (H (binomialSeries ℚ (-1/2 : ℚ)))^2 = 1 := by
  have hb := congrArg (fun g : S => H g) binomial_identity
  change H ((1+X) * binomialSeries ℚ (-1/2 : ℚ)^2) = H 1 at hb
  rw [map_mul, map_pow, map_add, map_one, hx, add_sub_cancel] at hb
  exact hb

private theorem square_identity : discriminant * generating^2 = (1-x)^2 := by
  let H : S →ₐ[ℚ] S := substAlgHom (R := ℚ) substitutable
  have hx : H X = discriminant - 1 := substAlgHom_X substitutable
  have hb := substituted H hx
  let g : S := H (binomialSeries ℚ (-1/2 : ℚ))
  have he : generating = (1-x) * g := by
    unfold generating g H
    rw [coe_substAlgHom]
  rw [he]
  change discriminant * ((1-x) * g)^2 = (1-x)^2
  change discriminant * g^2 = 1 at hb
  calc
    _ = (1-x)^2 * (discriminant * g^2) := by ring
    _ = _ := by rw [hb, mul_one]

private theorem differential_equation :
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
private theorem weighted (n : ℕ) :
    coeff n (x * derivative ℚ generating) = (n : ℚ) * a n := by
  cases n with
  | zero => simp [x]
  | succ n => rw [coeff_succ_X_mul, coeff_derivative]; simp [a, mul_comm]

theorem OMA.solution : type_of% @OMA.S_oeis_a162479.main := by
  intro n hn
  let w := x * derivative ℚ generating
  let f := generating
  have eqn : w + (C (-9:ℚ)*w + C (-3:ℚ)*f)*x^1 +
      (C (14:ℚ)*w + C (2:ℚ)*f)*x^2 + (C (-10:ℚ)*w + C (-6:ℚ)*f)*x^3 +
      (C (5:ℚ)*w + C (4:ℚ)*f)*x^4 + (C (-1:ℚ)*w + C (-1:ℚ)*f)*x^5 = 0 := by
    dsimp only [w, f]
    simp only [map_neg, map_ofNat, map_one]
    linear_combination x * differential_equation
  have ec := congrArg (coeff (R := ℚ) n) eqn
  simp only [map_add, map_zero, x, coeff_mul_X_pow', if_pos (show 1 ≤ n by omega),
    if_pos (show 2 ≤ n by omega), if_pos (show 3 ≤ n by omega),
    if_pos (show 4 ≤ n by omega), if_pos hn, coeff_C_mul] at ec
  have ca (k : ℕ) : coeff k generating = a k := rfl
  simp only [w, weighted, f, ca, Nat.cast_sub (show 1 ≤ n by omega),
    Nat.cast_sub (show 2 ≤ n by omega), Nat.cast_sub (show 3 ≤ n by omega),
    Nat.cast_sub (show 4 ≤ n by omega), Nat.cast_sub hn, Nat.cast_ofNat, Nat.cast_one] at ec
  linear_combination ec
