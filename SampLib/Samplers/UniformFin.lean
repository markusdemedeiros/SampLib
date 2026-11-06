import SampLib.Samplers.UniformInt

/-! # Uniform integer sampling with a bounded mathematical output -/

open ProbLang Finset
open scoped ENNReal

namespace SampLib.UniformFin

noncomputable section

section distribution

open MeasureTheory Measure

/-- The bound is retained in the mathematical output type. -/
def law (n : ℕ) : Measure (Fin n) := uniformOfFinset univ

instance (n : ℕ) [NeZero n] : IsProbabilityMeasure (law n) :=
  isProbabilityMeasure_uniformOfFinset Finset.univ_nonempty

theorem lintegral_law (n : ℕ) (F : Fin n → ℝ≥0∞) :
    ∫⁻ k, F k ∂law n = (∑ k, F k) / n := by
  simp only [law, uniformOfFinset, lintegral_finsetSum_measure,
    lintegral_smul_measure, lintegral_dirac, smul_eq_mul, card_univ, Fintype.card_fin]
  rw [← mul_sum, ENNReal.div_eq_inv_mul]

theorem law_singleton (n : ℕ) (k : Fin n) : law n {k} = (n : ℝ≥0∞)⁻¹ := by
  simp [law, uniformOfFinset_apply_singleton]

private def extend {n : ℕ} (F : Fin n → ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  if h : k < n then F ⟨k, h⟩ else 0

private theorem sum_extend (n : ℕ) (F : Fin n → ℝ≥0∞) :
    ∑ k ∈ range n, extend F k = ∑ k, F k := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp [extend]

end distribution

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The source still returns an integer; its specification retains the bound. -/
theorem uniformFin_distSpec (E : CoPset) (n : ℕ) [NeZero n] :
    IsDistSpec (GF := GF) E pl(&Occil.uniformInt #int (n : ℤ)) (law n)
      (fun k => Val.int (k : ℤ)) where
  spec F _ := by
    iintro Hcredit
    iapply tglWp_wand
    isplitl [Hcredit]
    · iapply UniformInt.twp_uniformInt E n (NeZero.pos n) (extend F)
      rw [sum_extend, ← lintegral_law]
      iexact Hcredit
    iintro %v ⟨%k, %hv, %hk, Hcredit⟩
    iexists (⟨k, hk⟩ : Fin n)
    isplit
    · ipureintro
      exact hv
    · simp only [extend, dite_eq_left hk]
      iexact Hcredit

end specification

end

end SampLib.UniformFin
