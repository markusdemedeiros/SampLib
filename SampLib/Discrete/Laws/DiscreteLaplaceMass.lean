import SampLib.Common.Laws.AcceptedProposal
import SampLib.Bernoulli.Laws.ExpMinusRational
import SampLib.Uniform.Laws.UniformInt
import SampLib.Continuous.Laws.GeometricFailures
import SampLib.Discrete.Laws.SymmetricGeometric

/-! # Discrete-Laplace proposal and masses

A remainder, a geometric whole part, and a sign form the proposal. Each
accepted integer has the standard two-sided geometric mass.
-/

open MeasureTheory Measure
open ENNReal (ofReal)
open scoped ENNReal

namespace SampLib.DiscreteLaplace

noncomputable section

abbrev Sample := ℕ × (ℕ × Bool)

def wholeBias : unitInterval := ExpMinusRational.bias 1 1 (by decide) (by decide)

def proposal (t : ℕ) (_ht : 0 < t) : Measure Sample :=
  (UniformInt.law t).prod
    ((GeometricFailures.law wholeBias).prod (RealCoin.law VonNeumann.fairBias))

instance (t : ℕ) (ht : 0 < t) : IsProbabilityMeasure (proposal t ht) := by
  let : NeZero t := ⟨ht.ne'⟩
  dsimp [proposal]
  infer_instance

def magnitude (s t : ℕ) (z : Sample) : ℕ := (z.1 + z.2.1 * t) / s

def output (s t : ℕ) (z : Sample) : ℤ :=
  if z.2.2 then (magnitude s t z : ℤ) else -(magnitude s t z : ℤ)

def acceptance (s t : ℕ) (ht : 0 < t) (z : Sample) : unitInterval :=
  if z.2.2 = false ∧ magnitude s t z = 0 then 0 else
    ExpMinusRational.bias z.1 t (by positivity) (by exact_mod_cast ht)

/-- The intended law, independently normalized by the standard two-sided geometric law. -/
def law (s t : ℕ) (_hs : 0 < s) (ht : 0 < t) : Measure ℤ :=
  SymmetricGeometric.law
    (unitInterval.symm (ExpMinusRational.bias s t (by positivity) (by exact_mod_cast ht)))

instance (s t : ℕ) (hs : 0 < s) (ht : 0 < t) : IsProbabilityMeasure (law s t hs ht) := by
  dsimp [law]
  infer_instance

def expWeight (t n : ℕ) : ℝ≥0∞ := ofReal (Real.exp (-(n : ℝ) / t))

def coefficient (s t : ℕ) : ℝ≥0∞ :=
  ofReal ((1 - Real.exp (-(s : ℝ) / t)) / (1 + Real.exp (-(s : ℝ) / t)))

def block (s t : ℕ) : ℝ≥0∞ := ∑ a ∈ Finset.range s, expWeight t a

def base (t : ℕ) : ℝ≥0∞ := ofReal (1 - Real.exp (-1)) / (2 * t)

def normalizer (s t : ℕ) : ℝ≥0∞ := base t * block s t / coefficient s t

theorem decay_lt_one (s t : ℕ) (hs : 0 < s) (ht : 0 < t) :
    Real.exp (-(s : ℝ) / t) < 1 := by
  apply Real.exp_lt_one_iff.mpr
  apply div_neg_of_neg_of_pos
  · exact neg_neg_of_pos (by exact_mod_cast hs)
  · exact_mod_cast ht

private theorem stop_pos (s t : ℕ) (hs : 0 < s) (ht : 0 < t) :
    0 < ((unitInterval.symm (ExpMinusRational.bias s t (by positivity)
      (by exact_mod_cast ht)) : unitInterval) : ℝ) := by
  simpa [unitInterval.coe_symm_eq, ExpMinusRational.bias] using
    sub_pos.mpr (decay_lt_one s t hs ht)

private theorem whole_stop_pos : 0 < (GeometricFailures.stopBias wholeBias : ℝ) := by
  change 0 < 1 - (wholeBias : ℝ)
  apply sub_pos.mpr
  simp [wholeBias, ExpMinusRational.bias]

private theorem whole_stop_ne_zero : GeometricFailures.stopBias wholeBias ≠ 0 := by
  intro h
  have hp := whole_stop_pos
  simp [h] at hp

theorem whole_singleton (n : ℕ) :
    GeometricFailures.law wholeBias {n} = ofReal (1 - Real.exp (-1)) * expWeight 1 n := by
  rw [GeometricFailures.law, ProbabilityTheory.geometricMeasure_singleton whole_stop_ne_zero]
  have hstop : (GeometricFailures.stopBias wholeBias : ℝ) = 1 - Real.exp (-1) := by
    simp [GeometricFailures.stopBias, wholeBias, unitInterval.coe_symm_eq, ExpMinusRational.bias]
  have hcontinue : 1 - (GeometricFailures.stopBias wholeBias : ℝ) = Real.exp (-1) := by
    rw [hstop]
    ring
  rw [hcontinue, hstop, ENNReal.ofReal_mul (pow_nonneg (Real.exp_nonneg _) _)]
  simp only [← Real.exp_nat_mul, mul_neg_one, expWeight, Nat.cast_one, div_one]
  rw [mul_comm]

/-- The proposal at remainder zero, whole zero and positive sign is always accepted. -/
theorem mass_nonzero (s t : ℕ) (ht : 0 < t) :
    AcceptedProposal.mass (proposal t ht) (acceptance s t ht) ≠ 0 := by
  let : NeZero t := ⟨ht.ne'⟩
  have hwhole : GeometricFailures.law wholeBias {0} ≠ 0 := by
    rw [GeometricFailures.law, ProbabilityTheory.geometricMeasure_singleton whole_stop_ne_zero]
    simpa only [pow_zero, one_mul] using (ENNReal.ofReal_pos.mpr whole_stop_pos).ne'
  have huniform : UniformInt.law t {0} ≠ 0 := by
    simp [UniformInt.law, Measure.uniformOfFinset_apply_singleton, Finset.mem_range, ht]
  have hfair : RealCoin.law VonNeumann.fairBias {true} ≠ 0 := by
    norm_num [RealCoin.law, RealCoin.pmf, VonNeumann.fairBias]
  have hatom : proposal t ht {(0, (0, true))} ≠ 0 := by
    have hset : ({(0, (0, true))} : Set Sample) =
        ({0} : Set ℕ) ×ˢ (({0} : Set ℕ) ×ˢ {true}) := by ext z; simp
    rw [proposal, hset, Measure.prod_prod, Measure.prod_prod]
    exact mul_ne_zero huniform (mul_ne_zero hwhole hfair)
  intro hzero
  have hae := (lintegral_eq_zero_iff
    (measurable_of_countable (AcceptedProposal.weight (acceptance s t ht)))).mp hzero
  have hz := ae_iff_of_countable.mp hae (0, (0, true)) hatom
  simp [AcceptedProposal.weight, acceptance, ExpMinusRational.bias] at hz

/-- The positive tail has the normalized discrete-Laplace mass. -/
theorem nonneg_mass (s t : ℕ) (hs : 0 < s) (ht : 0 < t) (n : ℕ) :
    law s t hs ht {(n : ℤ)} = coefficient s t * expWeight t s ^ n := by
  rw [law, SymmetricGeometric.nonneg_mass _ (stop_pos s t hs ht)]
  simp only [unitInterval.coe_symm_eq, ExpMinusRational.bias, Int.cast_natCast]
  have hsub : 1 - (1 - Real.exp (-(s : ℝ) / t)) = Real.exp (-(s : ℝ) / t) := by ring
  have hden : 2 - (1 - Real.exp (-(s : ℝ) / t)) = 1 + Real.exp (-(s : ℝ) / t) := by ring
  rw [hsub, hden]
  rw [coefficient, expWeight, ← ENNReal.ofReal_pow (Real.exp_nonneg _),
    ← ENNReal.ofReal_mul' (pow_nonneg (Real.exp_nonneg _) _)]
  congr 1
  ring

/-- The reflected negative tail has the same coefficient and decay. -/
theorem neg_mass (s t : ℕ) (hs : 0 < s) (ht : 0 < t) (n : ℕ) :
    law s t hs ht {-1 - (n : ℤ)} = coefficient s t * expWeight t s ^ (n + 1) := by
  rw [law, SymmetricGeometric.neg_mass _ (stop_pos s t hs ht)]
  simp only [unitInterval.coe_symm_eq, ExpMinusRational.bias, Int.cast_natCast]
  have hsub : 1 - (1 - Real.exp (-(s : ℝ) / t)) = Real.exp (-(s : ℝ) / t) := by ring
  have hden : 2 - (1 - Real.exp (-(s : ℝ) / t)) = 1 + Real.exp (-(s : ℝ) / t) := by ring
  rw [hsub, hden]
  rw [coefficient, expWeight, ← ENNReal.ofReal_pow (Real.exp_nonneg _),
    ← ENNReal.ofReal_mul' (pow_nonneg (Real.exp_nonneg _) _)]
  congr 1
  ring

/-- The standard discrete-Laplace mass is proportional to exponential absolute distance. -/
theorem law_singleton (s t : ℕ) (hs : 0 < s) (ht : 0 < t) (z : ℤ) :
    law s t hs ht {z} = coefficient s t * expWeight t s ^ z.natAbs := by
  cases z with
  | ofNat n => simpa using nonneg_mass s t hs ht n
  | negSucc n =>
    rw [Int.natAbs_negSucc, show Int.negSucc n = -1 - (n : ℤ) by omega]
    exact neg_mass s t hs ht n

end

end SampLib.DiscreteLaplace
