module

public import Metrology.TotalEris.Examples.Samplers.NegExp
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.Algebra.Order.Interval.Set.Group

@[expose] public section

/-! # Exponential expectations on successive unit intervals -/

open Set MeasureTheory
open scoped ENNReal

namespace SampLib.Distributions.Exponential

noncomputable section

/-- Partition the nonnegative half-line into unit intervals and translate each to `[0,1)`. -/
theorem lintegral_Ici_eq_tsum (g : ℝ → ℝ≥0∞) :
    ∫⁻ z in Ici (0 : ℝ), g z =
      ∑' n : ℕ, ∫⁻ x in Ico (0 : ℝ) 1, g ((n : ℝ) + x) := by
  have hcover : (⋃ n : ℕ, Ico (n : ℝ) (n + 1)) = Ici (0 : ℝ) := by
    ext z
    simp only [mem_iUnion, mem_Ico, mem_Ici]
    constructor
    · rintro ⟨n, hn, _⟩
      exact (Nat.cast_nonneg n).trans hn
    · intro hz
      exact ⟨⌊z⌋₊, Nat.floor_le hz, Nat.lt_floor_add_one z⟩
  have hdisj : Pairwise (fun i j : ℕ =>
      _root_.Disjoint (Ico (i : ℝ) (i + 1)) (Ico (j : ℝ) (j + 1))) := by
    intro i j hij
    exact_mod_cast (pairwise_disjoint_Ico_intCast ℝ) (Int.ofNat_inj.ne.mpr hij)
  rw [← hcover, lintegral_iUnion (fun _ => measurableSet_Ico) hdisj]
  refine tsum_congr fun n => ?_
  rw [← lintegral_indicator measurableSet_Ico, ← lintegral_indicator measurableSet_Ico,
    ← lintegral_add_left_eq_self (μ := volume)
      ((Ico (n : ℝ) (n + 1)).indicator g) (n : ℝ)]
  apply lintegral_congr
  intro x
  simp only [indicator_apply, mem_Ico, le_add_iff_nonneg_right, add_lt_add_iff_left]

/-- The unit-strip density agrees with the standard unit-rate exponential measure. -/
theorem lintegral_expMeasure (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ z, F z ∂ProbabilityTheory.expMeasure 1 =
      ProbLang.TotalEris.Examples.NegExpCreditV (fun k x => F ((k : ℝ) + x)) 0 := by
  have hm : Measurable (ProbabilityTheory.gammaPDF 1 1) := by
    change Measurable (fun x => ENNReal.ofReal (ProbabilityTheory.gammaPDFReal 1 1 x))
    exact ENNReal.measurable_ofReal.comp (ProbabilityTheory.measurable_gammaPDFReal 1 1)
  rw [ProbabilityTheory.expMeasure, ProbabilityTheory.gammaMeasure,
    lintegral_withDensity_eq_lintegral_mul _ hm hF]
  change (∫⁻ z, ProbabilityTheory.exponentialPDF 1 z * F z) = _
  have hpdf : (fun z => ProbabilityTheory.exponentialPDF 1 z * F z) =
      (Ici (0 : ℝ)).indicator (fun z => ENNReal.ofReal (Real.exp (-z)) * F z) := by
    funext z
    by_cases hz : 0 ≤ z
    · simp [ProbabilityTheory.exponentialPDF_of_nonneg hz, hz]
    · simp [ProbabilityTheory.exponentialPDF_of_neg (lt_of_not_ge hz), hz]
  rw [hpdf, lintegral_indicator measurableSet_Ici, lintegral_Ici_eq_tsum,
    ProbLang.TotalEris.Examples.NegExpCreditV_reindex]
  simp only [Nat.zero_add]
  refine tsum_congr fun n => ?_
  rw [restrict_Ico_eq_restrict_Icc]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro x hx
  dsimp only
  simp only [ProbLang.TotalEris.Examples.NegExppdf₀, ite_eq_left (show 0 ≤ x ∧ x ≤ 1 from hx)]
  rw [add_comm]

end

end SampLib.Distributions.Exponential
