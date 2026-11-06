import SampLib.Bernoulli.Laws.Subtraction
import SampLib.Bernoulli.Laws.BernoulliRace

/-! # Laws of division by a Bernoulli race

Racing the numerator coin against the gap coin `p - q` cancels their common accepted mass,
so the output bias is `q/p`.
-/

namespace SampLib.Division

noncomputable section

/-- The numerator's share of the two complementary accepted masses. -/
def bias (p q : unitInterval) (e f : ℤ) (he : 0 < e) (hef : e < f)
    (h : (e : ℝ) / f ≤ (p : ℝ) - q) : unitInterval :=
  BernoulliRace.bias q (Subtraction.bias p q e f he hef h)

theorem bias_coe (p q : unitInterval) (e f : ℤ) (he : 0 < e) (hef : e < f)
    (h : (e : ℝ) / f ≤ (p : ℝ) - q) : (bias p q e f he hef h : ℝ) = (q : ℝ) / p := by
  change (q : ℝ) / ((q : ℝ) + (Subtraction.bias p q e f he hef h : ℝ)) = _
  rw [Subtraction.bias_coe]
  congr 1
  ring

theorem exit_pos (p q : unitInterval) (e f : ℤ) (he : 0 < e) (hef : e < f)
    (h : (e : ℝ) / f ≤ (p : ℝ) - q) :
    0 < (q : ℝ) + (Subtraction.bias p q e f he hef h : ℝ) := by
  have hg : 0 < (p : ℝ) - q :=
    lt_of_lt_of_le (div_pos (by exact_mod_cast he) (by exact_mod_cast he.trans hef)) h
  rw [Subtraction.bias_coe]
  linarith [q.2.1]

end

end SampLib.Division
