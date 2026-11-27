import OMAStatements.S_oeis_a372313

/-!
# Proof of Ali Sada's OEIS A372313 conjecture

Source: https://oeis.org/A372313
The row update is A372289 by Antti Karttunen and Ali Sada.
Credit: @ptlom (with Codex)

When the seed and the current entry both end in 33, their sum ends in 66.
It has exactly one factor of two, so the next entry is twice the sum plus
one and again ends in 33. Induction proves this for every column.
-/

open OMA.S_oeis_a372313

theorem OMA.solution : type_of% @OMA.S_oeis_a372313.main := by
  have transform_of_two_mod_four (x : ℕ) (hx : x % 4 = 2) :
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
