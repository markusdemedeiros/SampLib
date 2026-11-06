import SampLib.Discrete.Laws.UniformFin
import SampLib.Uniform.UniformInt

/-! # Uniform integer sampling with a bounded mathematical output -/

open ProbLang Finset
open scoped ENNReal

namespace SampLib.UniformFin

noncomputable section

private def extend {n : ℕ} (F : Fin n → ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  if h : k < n then F ⟨k, h⟩ else 0

private theorem sum_extend (n : ℕ) (F : Fin n → ℝ≥0∞) :
    ∑ k ∈ range n, extend F k = ∑ k, F k := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp [extend]

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
