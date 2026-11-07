module

public import SampLib.Common.Laws.AbsorbingChain
public import SampLib.Discrete.Laws.HazardProduct

@[expose] public section

/-! # Divergent cumulative hazards force absorption

The elementary product bound needs neither independent identical trials nor a
finite expected stopping time. It applies to reciprocal hazards in particular.
-/

open Filter Finset
open scoped ENNReal Topology

namespace SampLib.AbsorbingChain

noncomputable section

private theorem survival_ofReal (q : ℕ → ℝ) (hq : ∀ n, 0 ≤ q n)
    (start depth : ℕ) :
    survival (fun n => ENNReal.ofReal (q n)) start depth =
      ENNReal.ofReal (realSurvival q start depth) := by
  induction depth generalizing start with
  | zero => simp [realSurvival]
  | succ depth ih =>
    rw [survival_succ, realSurvival, ih, ENNReal.ofReal_mul (hq start)]

/-- Divergence of the hazard sum is a sufficient, heavy-tail-friendly termination test. -/
theorem survival_tendsto_zero_of_hazard_sum (q : ℕ → ℝ)
    (hq : ∀ n, q n ∈ Set.Icc 0 1) (start : ℕ)
    (hazards : Tendsto (fun depth => ∑ i ∈ range depth, (1 - q (start + i)))
      atTop atTop) :
    Tendsto (survival (fun n => ENNReal.ofReal (q n)) start) atTop (𝓝 0) := by
  have hreal := realSurvival_tendsto_zero_of_hazard_sum q hq start hazards
  have heq : survival (fun n => ENNReal.ofReal (q n)) start =
      fun depth => ENNReal.ofReal (realSurvival q start depth) :=
    funext (survival_ofReal q (fun n => (hq n).1) start)
  rw [heq]
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal

end

end SampLib.AbsorbingChain
