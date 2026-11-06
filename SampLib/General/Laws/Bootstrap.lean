import SampLib.Combinatorial.Laws.SampleWithReplacement

/-! # Bootstrap law -/

open MeasureTheory
open scoped ENNReal

namespace SampLib.Bootstrap

noncomputable section

/-- Each bootstrap data set has `n` independent empirical positions. -/
abbrev blockLaw (n : ℕ) [NeZero n] :=
  SampleWithReplacement.law (Choice.law n) n

/-- The bootstrap replicates are independent, each with the original sample size. -/
def law (n : ℕ) [NeZero n] (replicates : ℕ) :=
  SampleWithReplacement.law (blockLaw n) replicates

instance (n : ℕ) [NeZero n] (replicates : ℕ) :
    IsProbabilityMeasure (law n replicates) := by
  dsimp [law]
  infer_instance

end

end SampLib.Bootstrap
