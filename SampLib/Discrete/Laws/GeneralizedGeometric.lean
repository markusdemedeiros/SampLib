import SampLib.Common.Laws.AbsorbingChain
import SampLib.Uniform.Laws.RealCoin

/-! # Generalized geometric law

The first stopping index of an indexed continuation coin is an absorbing-chain
stopping law. One coin flip partitions the expected credit into stop and continue.
-/

open scoped ENNReal

namespace SampLib.GeneralizedGeometric

noncomputable section

open MeasureTheory (Measure IsProbabilityMeasure lintegral_map)

/-- The probability of continuing at the given index. -/
def continuation (p : ℕ → unitInterval) (n : ℕ) : ℝ≥0∞ := RealCoin.pmf (p n) true

private theorem continuation_le_one (p : ℕ → unitInterval) (n : ℕ) :
    continuation p n ≤ 1 := by
  simpa [continuation, RealCoin.pmf] using ENNReal.ofReal_le_one.mpr (p n).2.2

/-- First stopping index, with the source's initial index one. -/
def law (p : ℕ → unitInterval)
    (_absorbs : Filter.Tendsto (AbsorbingChain.survival (continuation p) 0)
      Filter.atTop (nhds 0)) : Measure ℕ := (AbsorbingChain.stopLaw (continuation p) 0).map Nat.succ

instance (p : ℕ → unitInterval)
    (absorbs : Filter.Tendsto (AbsorbingChain.survival (continuation p) 0)
      Filter.atTop (nhds 0)) : IsProbabilityMeasure (law p absorbs) :=
  by
    let := AbsorbingChain.isProbabilityMeasure_stopLaw _ (continuation_le_one p) 0 absorbs
    dsimp [law]
    infer_instance

/-- Stop credit and recursive credit are the two coin outcomes. -/
def kernel (F : ℕ → ℝ≥0∞) (n : ℕ) (c : ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then c else F n

/-- The continuation and stopping probabilities partition one trial. -/
theorem expectation (p : ℕ → unitInterval) (F : ℕ → ℝ≥0∞) (n : ℕ) (c : ℝ≥0∞) :
    ∫⁻ b, kernel F n c b ∂RealCoin.law (p n) =
      (1 - continuation p n) * F n + continuation p n * c := by
  simp [RealCoin.lintegral_law, RealCoin.credit, kernel, continuation, RealCoin.pmf,
    ENNReal.ofReal_sub _ (p n).2.1, add_comm]

end

end SampLib.GeneralizedGeometric
