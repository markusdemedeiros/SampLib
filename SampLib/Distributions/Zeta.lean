import SampLib.Distributions.ZetaWeights
import SampLib.Distributions.AcceptedProposal

/-! # The canonical zeta law and rejection credit

Every positive integer belongs to one dyadic block. Cancellation leaves its
negative power with a common geometric factor; normalization removes that factor.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace SampLib.Zeta

noncomputable section

open DyadicBlocks

def weight (a b n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (((n + 1 : ℕ) : ℝ) ^ (-exponent a b))

def normalizer (a b : ℕ) : ℝ≥0∞ := ∑' n, weight a b n

private theorem sum_weights (a b : ℕ) :
    (∑' t : Block, ENNReal.ofReal ((value t : ℝ) ^ (-exponent a b))) = normalizer a b := by
  unfold normalizer weight
  simp_rw [value_eq]
  exact equiv.tsum_eq (fun n : ℕ => ENNReal.ofReal (((n + 1 : ℕ) : ℝ) ^ (-exponent a b)))

theorem normalizer_pos (a b : ℕ) : 0 < normalizer a b := by
  have h : weight a b 0 ≤ normalizer a b := ENNReal.le_tsum 0
  have hzero : weight a b 0 = 1 := by simp [weight]
  rw [hzero] at h
  exact zero_lt_one.trans_le h

/-- The accepted mass is the common geometric factor times the zeta series. -/
theorem mass_eq (a b : ℕ) (hb : 0 < b) (hab : b < a) :
    AcceptedProposal.mass (proposal a b hb) (acceptance a b hb) =
      ENNReal.ofReal (bias a b hb : ℝ) * normalizer a b := by
  rw [AcceptedProposal.mass, lintegral_countable']
  simp_rw [AcceptedProposal.weight, accepted_atom a b hb hab]
  rw [ENNReal.tsum_mul_left, sum_weights]

theorem mass_ne_zero (a b : ℕ) (hb : 0 < b) (hab : b < a) :
    AcceptedProposal.mass (proposal a b hb) (acceptance a b hb) ≠ 0 := by
  rw [mass_eq a b hb hab]
  exact mul_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr (bias_pos a b hb hab)))
    (ne_of_gt (normalizer_pos a b))

/-- The dyadic proposal also proves convergence of the positive zeta series. -/
theorem normalizer_ne_top (a b : ℕ) (hb : 0 < b) (hab : b < a) :
    normalizer a b ≠ ∞ := by
  have h := AcceptedProposal.mass_ne_top (proposal a b hb) (acceptance a b hb)
  rw [mass_eq a b hb hab] at h
  have hp : ENNReal.ofReal (bias a b hb : ℝ) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (bias_pos a b hb hab))
  intro hn
  simp [hn, hp] at h

/-- The accepted positive value, with its dyadic representation forgotten. -/
def law (a b : ℕ) (hb : 0 < b) (hab : b < a) : Measure ℕ :=
  (AcceptedProposal.law (proposal a b hb) (acceptance a b hb) (mass_ne_zero a b hb hab)).map value

instance (a b : ℕ) (hb : 0 < b) (hab : b < a) : IsProbabilityMeasure (law a b hb hab) := by
  unfold law
  infer_instance

theorem law_zero (a b : ℕ) (hb : 0 < b) (hab : b < a) : law a b hb hab {0} = 0 := by
  rw [law, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have hpre : value ⁻¹' ({0} : Set ℕ) = ∅ := by
    ext t
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    exact ne_of_gt (value_pos t)
  rw [hpre]
  simp

/-- The normalized point masses are exactly `(n+1)^(-a/b)/ζ(a/b)`. -/
theorem law_singleton (a b : ℕ) (hb : 0 < b) (hab : b < a) (n : ℕ) :
    law a b hb hab {n + 1} = weight a b n / normalizer a b := by
  rw [law, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have hpre : value ⁻¹' ({n + 1} : Set ℕ) = {equiv.symm n} := by
    ext t
    simp [value_eq, Equiv.eq_symm_apply]
  rw [hpre, AcceptedProposal.law, Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ (measurableSet_singleton _), lintegral_singleton,
    AcceptedProposal.weight, accepted_atom a b hb hab, mass_eq a b hb hab]
  have hp0 : ENNReal.ofReal (bias a b hb : ℝ) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (bias_pos a b hb hab))
  have hpT : ENNReal.ofReal (bias a b hb : ℝ) ≠ ∞ := ENNReal.ofReal_ne_top
  simp only [value_eq, Equiv.apply_symm_apply]
  change (ENNReal.ofReal (bias a b hb : ℝ) * normalizer a b)⁻¹ *
    (ENNReal.ofReal (bias a b hb : ℝ) * weight a b n) = _
  rw [← ENNReal.div_eq_inv_mul]
  exact ENNReal.mul_div_mul_left _ _ hp0 hpT

/-- Natural-valued continuations are the corresponding joint block continuations. -/
theorem credit_eq (a b : ℕ) (hb : 0 < b) (hab : b < a) (F : ℕ → ℝ≥0∞) :
    (∫⁻ n, F n ∂law a b hb hab) =
      AcceptedProposal.credit (proposal a b hb) (acceptance a b hb) (mass_ne_zero a b hb hab)
        (fun t => F (value t)) := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  rfl

abbrev factor (a b : ℕ) (hb : 0 < b) : ℝ≥0 :=
  AcceptedProposal.factor (proposal a b hb) (acceptance a b hb)

theorem one_lt_factor (a b : ℕ) (hb : 0 < b) (hab : b < a) : 1 < factor a b hb :=
  AcceptedProposal.one_lt_factor _ _ (mass_ne_zero a b hb hab)

def coinCredit (a b : ℕ) (hb : 0 < b) (hab : b < a) (F : ℕ → ℝ≥0∞)
    (ε : ℝ≥0∞) (t : Block) (s : Bool) : ℝ≥0∞ :=
  if s then F (value t) else (∫⁻ n, F n ∂law a b hb hab) + factor a b hb * ε

def proposalCredit (a b : ℕ) (hb : 0 < b) (hab : b < a) (F : ℕ → ℝ≥0∞)
    (ε : ℝ≥0∞) (t : Block) : ℝ≥0∞ :=
  ∫⁻ s, coinCredit a b hb hab F ε t s ∂RealCoin.law (acceptance a b hb t)

theorem coin_expectation (a b : ℕ) (hb : 0 < b) (hab : b < a) (F : ℕ → ℝ≥0∞)
    (ε : ℝ≥0∞) (t : Block) :
    proposalCredit a b hb hab F ε t =
      AcceptedProposal.kernel (proposal a b hb) (acceptance a b hb) (mass_ne_zero a b hb hab)
        (fun t => F (value t)) ε t := by
  rw [proposalCredit, RealCoin.lintegral_law]
  simp only [RealCoin.credit, RealCoin.pmf, coinCredit, Bool.false_eq_true, ↓reduceIte,
    credit_eq, AcceptedProposal.kernel, AcceptedProposal.weight, AcceptedProposal.rejectedWeight]

def levelCredit (a b : ℕ) (hb : 0 < b) (hab : b < a) (F : ℕ → ℝ≥0∞)
    (ε : ℝ≥0∞) (l : ℕ) : ℝ≥0∞ :=
  ∫⁻ r, proposalCredit a b hb hab F ε ⟨l, r⟩ ∂UniformFin.law (2 ^ l)

/-- Dyadic cancellation conserves the target moment and pays for every retry. -/
theorem expectation (a b : ℕ) (hb : 0 < b) (hab : b < a) (F : ℕ → ℝ≥0∞)
    (ε : ℝ≥0∞) :
    ∫⁻ l, levelCredit a b hb hab F ε l ∂Geometric.law (bias a b hb) ≤
      (∫⁻ n, F n ∂law a b hb hab) + ε := by
  unfold levelCredit
  rw [← DyadicProposal.lintegral_law (bias a b hb) (proposalCredit a b hb hab F ε)]
  change (∫⁻ t, proposalCredit a b hb hab F ε t ∂proposal a b hb) ≤ _
  simp only [coin_expectation, credit_eq]
  exact AcceptedProposal.expectation_preservation _ _ (measurable_of_countable _)
    (mass_ne_zero a b hb hab) (fun t => F (value t)) (measurable_of_countable _) ε

end

end SampLib.Zeta
