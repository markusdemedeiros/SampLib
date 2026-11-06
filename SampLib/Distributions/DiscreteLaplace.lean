import SampLib.Distributions.AcceptedProposal
import SampLib.Samplers.ExpMinusRational
import SampLib.Samplers.UniformInt
import SampLib.Samplers.GeometricFailures
import SampLib.Samplers.SymmetricGeometric

/-! # The rational discrete-Laplace lattice construction

A remainder and a geometric whole part join into one exponentially weighted
integer. Grouping that integer into blocks gives the geometric decay of the
magnitude. Removing negative zero leaves the standard symmetric geometric law.
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

private theorem decay_lt_one (s t : ℕ) (hs : 0 < s) (ht : 0 < t) :
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

private theorem whole_singleton (n : ℕ) :
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

private def tails (q : ℝ≥0∞) (F : ℤ → ℝ≥0∞) : ℝ≥0∞ :=
  (∑' n : ℕ, q ^ n * F n) + ∑' n : ℕ, q ^ (n + 1) * F (-1 - (n : ℤ))

private theorem law_expectation (s t : ℕ) (hs : 0 < s) (ht : 0 < t)
    (F : ℤ → ℝ≥0∞) :
    ∫⁻ z, F z ∂law s t hs ht = coefficient s t * tails (expWeight t s) F := by
  rw [lintegral_countable', tsum_of_nat_of_neg_add_one ENNReal.summable ENNReal.summable]
  simp_rw [nonneg_mass s t hs ht,
    show ∀ n : ℕ, -((n : ℤ) + 1) = -1 - (n : ℤ) by intro n; omega,
    neg_mass s t hs ht]
  simp only [tails, mul_add, ← ENNReal.tsum_mul_left]
  congr 1 <;> apply tsum_congr <;> intro n <;> ring

private theorem expWeight_block (s t n a : ℕ) :
    expWeight t (n * s + a) = expWeight t s ^ n * expWeight t a := by
  have he : -((n * s + a : ℕ) : ℝ) / t = (n : ℝ) * (-(s : ℝ) / t) + (-(a : ℝ) / t) := by
    push_cast
    ring
  simp only [expWeight, he, Real.exp_add, Real.exp_nat_mul,
    ENNReal.ofReal_mul' (Real.exp_nonneg _), ENNReal.ofReal_pow (Real.exp_nonneg _)]

/-- Quotient and remainder reindex every nonnegative integer exactly once. -/
private theorem join_remainders (t : ℕ) [NeZero t] (H : ℕ → ℝ≥0∞) :
    (∑ r ∈ Finset.range t, ∑' w : ℕ, H (r + w * t)) = ∑' v : ℕ, H v := by
  rw [← Fin.sum_univ_eq_sum_range (fun r => ∑' w : ℕ, H (r + w * t)) t]
  calc
    _ = ∑' r : Fin t, ∑' w : ℕ, H (r.val + w * t) := (tsum_fintype _).symm
    _ = ∑' p : ℕ × Fin t, H (p.2.val + p.1 * t) := by
      rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
    _ = _ := by
      simpa only [Nat.divModEquiv_symm_apply, Nat.add_comm] using
        (Nat.divModEquiv t).symm.tsum_eq H

private def signedCredit (F : ℤ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  F n + if n = 0 then 0 else F (-(n : ℤ))

private theorem signedCredit_sum (q : ℝ≥0∞) (F : ℤ → ℝ≥0∞) :
    (∑' n : ℕ, q ^ n * signedCredit F n) = tails q F := by
  simp only [signedCredit, mul_add, ENNReal.tsum_add]
  congr 1
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [pow_zero, ite_true, mul_zero, zero_add, Nat.add_eq_zero_iff,
    one_ne_zero, and_false, ite_false]
  apply tsum_congr
  intro n
  congr 2
  omega

/-- Equal-width lattice blocks contribute a common factor and geometric decay. -/
private theorem group_blocks (s t : ℕ) [NeZero s] (F : ℤ → ℝ≥0∞) :
    (∑' v : ℕ, expWeight t v * signedCredit F (v / s)) =
      block s t * tails (expWeight t s) F := by
  rw [← (Nat.divModEquiv s).symm.tsum_eq
    (fun v => expWeight t v * signedCredit F (v / s)), ENNReal.tsum_prod']
  have hdiv (p : ℕ × Fin s) : ((Nat.divModEquiv s).symm p) / s = p.1 :=
    congrArg Prod.fst ((Nat.divModEquiv s).apply_symm_apply p)
  simp_rw [hdiv]
  simp only [Nat.divModEquiv_symm_apply, expWeight_block, tsum_fintype]
  have hb : (∑ a : Fin s, expWeight t a.val) = block s t := by
    rw [Fin.sum_univ_eq_sum_range]
    rfl
  have hinner (n : ℕ) :
      (∑ a : Fin s, expWeight t s ^ n * expWeight t a.val * signedCredit F n) =
        block s t * (expWeight t s ^ n * signedCredit F n) := by
    rw [← hb, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    ring
  simp_rw [hinner]
  rw [ENNReal.tsum_mul_left, signedCredit_sum]

private theorem expWeight_join (t : ℕ) (ht : 0 < t) (r w : ℕ) :
    expWeight t (r + w * t) = expWeight t r * expWeight 1 w := by
  have htR : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  have he : -((r + w * t : ℕ) : ℝ) / t = -(r : ℝ) / t + -(w : ℝ) := by
    push_cast
    field_simp
    ring
  simp only [expWeight, he, Real.exp_add, ENNReal.ofReal_mul (Real.exp_nonneg _),
    Nat.cast_one, div_one]

private theorem fair_expectation (s t : ℕ) (ht : 0 < t) (r w : ℕ) (F : ℤ → ℝ≥0∞) :
    ∫⁻ b, AcceptedProposal.weight (acceptance s t ht) (r, (w, b)) *
      F (output s t (r, (w, b))) ∂RealCoin.law VonNeumann.fairBias =
      (1 / 2 : ℝ≥0∞) * expWeight t r * signedCredit F ((r + w * t) / s) := by
  rw [RealCoin.lintegral_law]
  have hhalf : ofReal (1 / 2 : ℝ) = (2 : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  by_cases hm : (r + w * t) / s = 0 <;>
    norm_num [RealCoin.credit, RealCoin.pmf, VonNeumann.fairBias, AcceptedProposal.weight,
      acceptance, output, magnitude, signedCredit, hm, ExpMinusRational.bias, expWeight] <;>
    rw [hhalf] <;> ring

/-- Remainders and geometric whole parts form a single exponential lattice weight. -/
private theorem proposal_expectation (s t : ℕ) (ht : 0 < t) (F : ℤ → ℝ≥0∞) :
    ∫⁻ z, AcceptedProposal.weight (acceptance s t ht) z * F (output s t z)
      ∂proposal t ht =
      base t * ∑' v : ℕ, expWeight t v * signedCredit F (v / s) := by
  let : NeZero t := ⟨ht.ne'⟩
  rw [proposal, lintegral_prod _ (measurable_of_countable _).aemeasurable]
  simp_rw [lintegral_prod _ (measurable_of_countable _).aemeasurable,
    fair_expectation s t ht]
  rw [UniformInt.lintegral_law]
  simp_rw [lintegral_countable', whole_singleton]
  let c : ℝ≥0∞ := (1 / 2) * ofReal (1 - Real.exp (-1))
  have hpoint (r w : ℕ) :
      ((1 / 2 : ℝ≥0∞) * expWeight t r * signedCredit F ((r + w * t) / s)) *
        (ofReal (1 - Real.exp (-1)) * expWeight 1 w) =
      c * (expWeight t (r + w * t) * signedCredit F ((r + w * t) / s)) := by
    rw [expWeight_join t ht]
    dsimp [c]
    ring
  simp_rw [hpoint, ENNReal.tsum_mul_left, ← Finset.mul_sum]
  rw [join_remainders t (fun v => expWeight t v * signedCredit F (v / s))]
  have hinv : ((2 : ℝ≥0∞) * t)⁻¹ = (2 : ℝ≥0∞)⁻¹ * (t : ℝ≥0∞)⁻¹ :=
    ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))
  dsimp [c]
  simp only [base, ENNReal.div_eq_inv_mul, one_div, hinv]
  ring

theorem coefficient_pos (s t : ℕ) (hs : 0 < s) (ht : 0 < t) : 0 < coefficient s t := by
  apply ENNReal.ofReal_pos.mpr
  exact div_pos (sub_pos.mpr (decay_lt_one s t hs ht)) (by positivity)

/-- The lattice construction has a common positive scale factor relative to the intended law. -/
theorem weighted_expectation (s t : ℕ) (hs : 0 < s) (ht : 0 < t) (F : ℤ → ℝ≥0∞) :
    ∫⁻ z, AcceptedProposal.weight (acceptance s t ht) z * F (output s t z)
      ∂proposal t ht = normalizer s t * ∫⁻ z, F z ∂law s t hs ht := by
  let : NeZero s := ⟨hs.ne'⟩
  have hc : coefficient s t ≠ 0 := (coefficient_pos s t hs ht).ne'
  have hctop : coefficient s t ≠ ∞ := ENNReal.ofReal_ne_top
  have hcancel : normalizer s t * coefficient s t = base t * block s t := by
    rw [normalizer, ENNReal.div_eq_inv_mul]
    calc
      _ = (coefficient s t)⁻¹ * coefficient s t * (base t * block s t) := by ring
      _ = _ := by rw [ENNReal.inv_mul_cancel hc hctop, one_mul]
  rw [proposal_expectation, group_blocks, law_expectation]
  calc
    _ = (base t * block s t) * tails (expWeight t s) F := by ring
    _ = (normalizer s t * coefficient s t) * tails (expWeight t s) F := by rw [hcancel]
    _ = _ := by ring

/-- The explicit normalizing factor is the total acceptance probability. -/
theorem mass_eq (s t : ℕ) (hs : 0 < s) (ht : 0 < t) :
    AcceptedProposal.mass (proposal t ht) (acceptance s t ht) = normalizer s t := by
  simpa [AcceptedProposal.mass] using weighted_expectation s t hs ht (fun _ => 1)

/-- Normalizing the accepted proposal yields the standard discrete-Laplace expectation. -/
theorem expectation (s t : ℕ) (hs : 0 < s) (ht : 0 < t) (F : ℤ → ℝ≥0∞) :
    ∫⁻ z, F (output s t z)
      ∂AcceptedProposal.law (proposal t ht) (acceptance s t ht) (mass_nonzero s t ht) =
      ∫⁻ z, F z ∂law s t hs ht := by
  rw [AcceptedProposal.law, lintegral_smul_measure, smul_eq_mul,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_of_countable _)
      (measurable_of_countable _)]
  simp only [Pi.mul_apply]
  rw [weighted_expectation s t hs ht F, ← mass_eq s t hs ht, ← mul_assoc,
    ENNReal.inv_mul_cancel (mass_nonzero s t ht)
      (AcceptedProposal.mass_ne_top (proposal t ht) (acceptance s t ht)), one_mul]

/-- The accepted signed quotient has the independently normalized intended law. -/
theorem accepted_map_eq (s t : ℕ) (hs : 0 < s) (ht : 0 < t) :
    (AcceptedProposal.law (proposal t ht) (acceptance s t ht) (mass_nonzero s t ht)).map
      (output s t) = law s t hs ht := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (measurable_of_countable _)]
  exact expectation s t hs ht F

end

end SampLib.DiscreteLaplace
