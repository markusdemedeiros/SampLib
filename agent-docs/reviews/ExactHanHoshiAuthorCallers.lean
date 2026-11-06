import SampLib.Samplers.HanHoshi

open ProbLang Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open scoped ENNReal

namespace HanHoshiAuthorChecks

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example (E : CoPset) (ws : List ℕ) [NeZero ws.sum] (F : ℤ → ℝ≥0∞) (R : IProp GF) :
    ↯ (∫⁻ i, F i ∂SampLib.CategoricalCDF.law ws) ∗ R ⊢
      tglWp E pl(&Occil.Weighted.hanHoshi
        &(SampLib.listVal (fun n : ℕ => Val.int n) ws).fst #())
        (fun v => iprop(∃ i : ℤ, ⌜v = Val.int i⌝ ∗ ↯ (F i) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  iapply ((SampLib.HanHoshi.hanHoshi_distSpec E ws).wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %i Hcredit
  iexists i
  iframe Hcredit HR
  ipureintro
  rfl

example : SampLib.HanHoshi.scan 3 0 1 [1, 2] 0 = none := rfl
example : SampLib.HanHoshi.scan 3 0 2 [1, 2] 0 = none := rfl
example : SampLib.HanHoshi.scan 3 1 2 [1, 2] 0 = some 1 := rfl
example : SampLib.HanHoshi.scan 3 0 4 [1, 2] 0 = some 0 := rfl
example : SampLib.HanHoshi.scan 2 0 1 [0, 2, 0] 0 = some 1 := rfl

local instance : NeZero ([0, 2, 0] : List ℕ).sum := ⟨by decide⟩

example (E : CoPset) :
    SampLib.IsDistSpec (GF := GF) E pl(&Occil.Weighted.hanHoshi
      &(SampLib.listVal (fun n : ℕ => Val.int n) [0, 2, 0]).fst #())
      (SampLib.CategoricalCDF.law [0, 2, 0]) Val.int := by
  exact SampLib.HanHoshi.hanHoshi_distSpec E [0, 2, 0]

#print axioms SampLib.HanHoshi.hanHoshi_distSpec
#print axioms SampLib.HanHoshi.twp_hanHoshi
#print axioms SampLib.RealCategoricalCDF.law_eq
#print axioms SampLib.HanHoshi.unresolved_boundary
#print axioms SampLib.HanHoshi.exists_horizon
#print axioms SampLib.FiniteBoundaryBands.expectation_preservation

end HanHoshiAuthorChecks
