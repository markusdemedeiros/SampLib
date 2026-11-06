module

public import SampLib.Common.Laws.FractionalPower
public import SampLib.Common.Laws.AbsorbingChain
public import SampLib.Uniform.Laws.RealCoin

@[expose] public section

/-! # Credits for the reciprocal-hazard power factory

First-exit masses carry the two result credits. The residual survival mass is the
only extra budget needed for finite unfolding, including infinite-mean cases.
-/

open MeasureTheory
open ENNReal (ofReal)
open scoped ENNReal

namespace SampLib.FractionalPower

noncomputable section

/-- The probability returned by the power factory. -/
def powerBias (p r : unitInterval) : unitInterval :=
  ⟨(p : ℝ) ^ (r : ℝ), Real.rpow_nonneg p.2.1 _, Real.rpow_le_one p.2.1 p.2.2 r.2.1⟩

/-- Probability of continuing after both tests in a round. -/
def continueProb (p r : unitInterval) (n : ℕ) : ℝ≥0∞ :=
  ofReal (1 - (p : ℝ)) * ofReal (1 - (r : ℝ) / (n + 1))

/-- Expected continuation credit paid by this round's two exits. -/
def exitCredit (p r : unitInterval) (F : Bool → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ofReal (p : ℝ) * F true +
    ofReal (1 - (p : ℝ)) * ofReal ((r : ℝ) / (n + 1)) * F false

/-- Expected output credit of the remaining first-exit distribution. -/
def tailCredit (p r : unitInterval) (F : Bool → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ∑' depth, AbsorbingChain.survival (continueProb p r) n depth * exitCredit p r F (n + depth)

/-- One-round conditioning is the conservation identity used by symbolic execution. -/
theorem tailCredit_succ (p r : unitInterval) (F : Bool → ℝ≥0∞) (n : ℕ) :
    tailCredit p r F n = exitCredit p r F n + continueProb p r n * tailCredit p r F (n + 1) := by
  rw [tailCredit, tsum_eq_zero_add' ENNReal.summable]
  simp only [AbsorbingChain.survival_zero, one_mul, Nat.add_zero]
  rw [tailCredit, ← ENNReal.tsum_mul_left]
  congr 1
  apply tsum_congr
  intro depth
  rw [AbsorbingChain.survival_succ]
  rw [show n + (depth + 1) = n + 1 + depth by omega]
  ring

theorem survival_from_zero (p r : unitInterval) (n : ℕ) :
    AbsorbingChain.survival (continueProb p r) 0 n = ofReal (roundSurvival p r n) := by
  simp only [AbsorbingChain.survival_eq_prod]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, roundSurvival_succ]
    rw [ENNReal.ofReal_mul
      (mul_nonneg (roundSurvival_nonneg p.2.1 p.2.2 r.2.1 r.2.2 n)
        (sub_nonneg.mpr p.2.2)),
      ENNReal.ofReal_mul (roundSurvival_nonneg p.2.1 p.2.2 r.2.1 r.2.2 n)]
    simp only [Nat.zero_add, continueProb]
    ring

/-- The reciprocal hazard at a given round, as a Bernoulli probability. -/
def hazardBias (r : unitInterval) (n : ℕ) : unitInterval :=
  ⟨(r : ℝ) / (n + 1), hazard_mem r.2.1 r.2.2 n⟩

def hazardCredit (F : Bool → ℝ≥0∞) (c : ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then F false else c

def inputCredit (r : unitInterval) (n : ℕ) (F : Bool → ℝ≥0∞)
    (c : ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then F true else RealCoin.credit (hazardBias r n) (hazardCredit F c)

/-- The two successive coin tests spend the two exit credits and the next-round credit. -/
theorem round_expectation (p r : unitInterval) (n : ℕ) (F : Bool → ℝ≥0∞) (c : ℝ≥0∞) :
    ∫⁻ b, inputCredit r n F c b ∂RealCoin.law p =
      exitCredit p r F n + continueProb p r n * c := by
  rw [RealCoin.lintegral_law]
  simp only [RealCoin.credit, RealCoin.pmf, inputCredit, hazardCredit, hazardBias,
    exitCredit, continueProb, Bool.false_eq_true, ite_false, ite_true]
  ring

/-- The source start state has exactly the intended Bernoulli expectation. -/
theorem tailCredit_zero (p r : unitInterval) (hstop : 0 < (p : ℝ) ∨ 0 < (r : ℝ))
    (F : Bool → ℝ≥0∞) : tailCredit p r F 0 = RealCoin.credit (powerBias p r) F := by
  have hterm (n : ℕ) :
      AbsorbingChain.survival (continueProb p r) 0 n * exitCredit p r F n =
        ofReal (successMass p r n) * F true + ofReal (failureMass p r n) * F false := by
    rw [survival_from_zero, exitCredit, successMass, failureMass]
    rw [ENNReal.ofReal_mul (roundSurvival_nonneg p.2.1 p.2.2 r.2.1 r.2.2 n),
      ENNReal.ofReal_mul (mul_nonneg (roundSurvival_nonneg p.2.1 p.2.2 r.2.1 r.2.2 n)
        (sub_nonneg.mpr p.2.2)),
      ENNReal.ofReal_mul (roundSurvival_nonneg p.2.1 p.2.2 r.2.1 r.2.2 n)]
    ring
  simp only [tailCredit, Nat.zero_add, hterm, ENNReal.tsum_add, ENNReal.tsum_mul_right,
    successMass_tsum p.2.1 p.2.2 r.2.1 r.2.2 hstop,
    failureMass_tsum p.2.1 p.2.2 r.2.1 r.2.2 hstop, RealCoin.credit, RealCoin.pmf,
    powerBias, ite_true, Bool.false_eq_true, ite_false]

/-- The unresolved finite-horizon mass vanishes on the complete terminating domain. -/
theorem absorbs (p r : unitInterval) (hstop : 0 < (p : ℝ) ∨ 0 < (r : ℝ)) :
    Filter.Tendsto (AbsorbingChain.survival (continueProb p r) 0) Filter.atTop (nhds 0) := by
  change Filter.Tendsto (fun n => AbsorbingChain.survival (continueProb p r) 0 n)
    Filter.atTop (nhds 0)
  simp_rw [survival_from_zero]
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (roundSurvival_tendsto_zero p.2.1 p.2.2 r.2.1 r.2.2 hstop)

end

end SampLib.FractionalPower
