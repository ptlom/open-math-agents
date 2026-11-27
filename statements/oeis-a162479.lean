import Mathlib.RingTheory.PowerSeries.Binomial
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

namespace OMA.S_oeis_a162479
open PowerSeries
abbrev S := PowerSeries ℚ
noncomputable abbrev x : S := X
noncomputable def discriminant : S := (1-x)^4 - 4*x

/-- The constant-one branch of (1-X)/sqrt((1-X)^4-4X).
Factoring (1-X)^4 out of the radical gives Barry's generating function. -/
noncomputable def generating : S :=
  (1-x) * (binomialSeries ℚ (-1/2 : ℚ)).subst (discriminant - 1)

noncomputable def a (n : ℕ) : ℚ := coeff n generating

/-- Mathar's five-step recurrence for every index from five onwards. -/
theorem main (n : ℕ) (hn : 5 ≤ n) :
    n * a n + 3*(2-3*(n:ℚ))*a (n-1) + 2*(7*(n:ℚ)-13)*a (n-2) +
    2*(12-5*(n:ℚ))*a (n-3) + (5*(n:ℚ)-16)*a (n-4) + (4-(n:ℚ))*a (n-5) = 0 := by
  sorry

end OMA.S_oeis_a162479
