import SampLib.Common.Laws.AcceptedProposal
import SampLib.Common.RationalPower
import SampLib.Discrete.UniformFin

/-! # Finite Zipf laws from uniform rejection

The reciprocal-power acceptance weights normalize to the familiar finite power
sum. The zero exponent gives the uniform law on the positive support.
-/

open MeasureTheory Finset
open scoped ENNReal NNReal

namespace SampLib.Zipf

noncomputable section

/-- Reciprocal of a positive integer, as a coin bias. -/
def reciprocal (k : ℕ) : unitInterval :=
  ⟨1 / ((k : ℝ) + 1), by
    constructor
    · positivity
    · apply (div_le_one (by positivity : (0 : ℝ) < k + 1)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) k]⟩

/-- Acceptance at rank `k` returns the integer `k+1`. -/
def acceptance (n a b : ℕ) (hb : 0 < b) (k : Fin n) : unitInterval :=
  RationalPower.bias (reciprocal k) a b hb

def weight (n a b : ℕ) (hb : 0 < b) (k : Fin n) : ℝ≥0∞ :=
  AcceptedProposal.weight (acceptance n a b hb) k

def normalizer (n a b : ℕ) (hb : 0 < b) : ℝ≥0∞ := ∑ k, weight n a b hb k

/-- The weights are precisely the negative rational powers. -/
theorem weight_eq (n a b : ℕ) (hb : 0 < b) (k : Fin n) :
    weight n a b hb k = ENNReal.ofReal (((k : ℕ) + 1 : ℝ) ^ (-((a : ℝ) / b))) := by
  simp only [weight, AcceptedProposal.weight, acceptance, RationalPower.bias, reciprocal]
  rw [one_div, ← Real.rpow_neg_eq_inv_rpow]

private theorem weight_pos (n a b : ℕ) (hb : 0 < b) (k : Fin n) :
    0 < weight n a b hb k := by
  rw [weight_eq]
  exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by positivity) _)

private theorem normalizer_pos (n a b : ℕ) [NeZero n] (hb : 0 < b) :
    0 < normalizer n a b hb := by
  let k : Fin n := ⟨0, NeZero.pos n⟩
  exact (weight_pos n a b hb k).trans_le
    (Finset.single_le_sum (fun _ _ => zero_le) (mem_univ k))

/-- Uniform proposal mass contributes one common factor to the acceptance rate. -/
theorem mass_eq (n a b : ℕ) [NeZero n] (hb : 0 < b) :
    AcceptedProposal.mass (UniformFin.law n) (acceptance n a b hb) =
      normalizer n a b hb / n := by
  rw [AcceptedProposal.mass, UniformFin.lintegral_law]
  rfl

theorem mass_ne_zero (n a b : ℕ) [NeZero n] (hb : 0 < b) :
    AcceptedProposal.mass (UniformFin.law n) (acceptance n a b hb) ≠ 0 := by
  rw [mass_eq, ENNReal.div_ne_zero]
  exact ⟨ne_of_gt (normalizer_pos n a b hb), by finiteness⟩

/-- Zipf on ranks `0,…,n-1`, encoded by their positive successors. -/
def law (n a b : ℕ) [NeZero n] (hb : 0 < b) : Measure (Fin n) :=
  AcceptedProposal.law (UniformFin.law n) (acceptance n a b hb) (mass_ne_zero n a b hb)

instance (n a b : ℕ) [NeZero n] (hb : 0 < b) : IsProbabilityMeasure (law n a b hb) := by
  unfold law
  infer_instance

/-- The canonical finite Zipf mass: `j^(-a/b)` divided by the finite power sum. -/
theorem law_singleton (n a b : ℕ) [NeZero n] (hb : 0 < b) (k : Fin n) :
    law n a b hb {k} = weight n a b hb k / normalizer n a b hb := by
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hnT : (n : ℝ≥0∞) ≠ ∞ := by finiteness
  rw [law, AcceptedProposal.law, Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ (measurableSet_singleton _), lintegral_singleton,
    UniformFin.law_singleton, mass_eq,
    ENNReal.inv_div (Or.inl hnT) (Or.inl hn0), mul_comm]
  change (weight n a b hb k / n) * (n / normalizer n a b hb) = _
  exact ENNReal.div_mul_div_cancel hn0 hnT

/-- Exponent zero gives the uniform law on the entire finite support. -/
theorem law_zero (n b : ℕ) [NeZero n] (hb : 0 < b) :
    law n 0 b hb = UniformFin.law n := by
  apply Measure.ext_of_singleton
  intro k
  rw [law_singleton, UniformFin.law_singleton]
  simp [normalizer, weight_eq]

/-- A singleton support is certain, at every permitted exponent. -/
theorem law_one (a b : ℕ) (hb : 0 < b) : law 1 a b hb = Measure.dirac (0 : Fin 1) := by
  apply Measure.ext_of_singleton
  intro k
  have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
  subst k
  rw [law_singleton]
  simp [normalizer, weight_eq]

abbrev factor (n a b : ℕ) [NeZero n] (hb : 0 < b) : ℝ≥0 :=
  AcceptedProposal.factor (UniformFin.law n) (acceptance n a b hb)

theorem one_lt_factor (n a b : ℕ) [NeZero n] (hb : 0 < b) : 1 < factor n a b hb :=
  AcceptedProposal.one_lt_factor _ _ (mass_ne_zero n a b hb)

/-- Success keeps the rank credit; failure funds another independent proposal. -/
def coinCredit (n a b : ℕ) [NeZero n] (hb : 0 < b) (F : Fin n → ℝ≥0∞)
    (ε : ℝ≥0∞) (k : Fin n) (s : Bool) : ℝ≥0∞ :=
  if s then F k else (∫⁻ k, F k ∂law n a b hb) + factor n a b hb * ε

def proposalCredit (n a b : ℕ) [NeZero n] (hb : 0 < b) (F : Fin n → ℝ≥0∞)
    (ε : ℝ≥0∞) (k : Fin n) : ℝ≥0∞ :=
  ∫⁻ s, coinCredit n a b hb F ε k s ∂RealCoin.law (acceptance n a b hb k)

theorem coin_expectation (n a b : ℕ) [NeZero n] (hb : 0 < b) (F : Fin n → ℝ≥0∞)
    (ε : ℝ≥0∞) (k : Fin n) :
    proposalCredit n a b hb F ε k =
      AcceptedProposal.kernel (UniformFin.law n) (acceptance n a b hb)
        (mass_ne_zero n a b hb) F ε k := by
  rw [proposalCredit, RealCoin.lintegral_law]
  rfl

/-- Reciprocal powers give Zipf credit; the complementary mass funds termination. -/
theorem expectation (n a b : ℕ) [NeZero n] (hb : 0 < b) (F : Fin n → ℝ≥0∞)
    (ε : ℝ≥0∞) :
    ∫⁻ k, proposalCredit n a b hb F ε k ∂UniformFin.law n ≤
      (∫⁻ k, F k ∂law n a b hb) + ε := by
  simp only [coin_expectation]
  exact AcceptedProposal.expectation_preservation _ _ (measurable_of_countable _)
    (mass_ne_zero n a b hb) F (measurable_of_countable _) ε

end

end SampLib.Zipf
