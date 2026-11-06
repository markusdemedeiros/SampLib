import SampLib.Weighted.InclusionSystematic
import SampLib.Weighted.Support.AliasTable

open ProbLang
open scoped ENNReal

#print axioms SampLib.InclusionSystematic.inclusionSystematic_distSpec
#print axioms SampLib.InclusionSystematic.inclusionSystematic_zero_distSpec
#print axioms SampLib.SystematicPPS.inclusion_probability
#print axioms SampLib.SystematicPPS.sample_length

section callers

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open SampLib

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.Weighted.inclusionSystematic
      &(listVal (fun n : ℕ => Val.int n) []).fst #0)
      (MeasureTheory.Measure.dirac ([] : List ℤ)) (listVal Val.int) :=
  InclusionSystematic.inclusionSystematic_zero_distSpec E []

example (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.Weighted.inclusionSystematic
      &(listVal (fun n : ℕ => Val.int n) [0, 0]).fst #0)
      (MeasureTheory.Measure.dirac ([] : List ℤ)) (listVal Val.int) :=
  InclusionSystematic.inclusionSystematic_zero_distSpec E [0, 0]

variable [ProbLangDist.IsUniformInt rT]

example (E : CoPset) (ws : List ℕ) [NeZero ws.sum] (count : ℕ)
    (hcount : count ≤ ws.length) (hcap : ∀ w ∈ ws, count * w ≤ ws.sum)
    (P : IProp GF) (F : List ℤ → ℝ≥0∞) :
    ⊢ P -∗ ↯ (∫⁻ xs, F xs ∂SystematicPPS.law ws count) -∗
      tglWp E pl(&Occil.Weighted.inclusionSystematic
        &(listVal (fun n : ℕ => Val.int n) ws).fst #int (count : ℤ))
        (fun v => iprop(∃ xs : List ℤ, ⌜v = listVal Val.int xs⌝ ∗ P ∗ ↯ (F xs))) := by
  iintro HP Hcredit
  iapply ((InclusionSystematic.inclusionSystematic_distSpec E ws count hcount hcap).wp
    F (measurable_of_countable _) _) $$ Hcredit
  iintro %xs Hcredit
  iexists xs
  iframe HP Hcredit
  itrivial

end callers

example : SampLib.SystematicPPS.law [1, 2, 3] 2 {xs | (2 : ℤ) ∈ xs} = 1 := by
  have h := SampLib.SystematicPPS.inclusion_probability [1, 2, 3] 2 2
    (by decide) (by decide) (by intro w hw; norm_num at hw ⊢; omega)
  norm_num at h
  rw [ENNReal.div_self (by norm_num : (6 : ℝ≥0∞) ≠ 0) (by finiteness)] at h
  exact h

example (ticket : ℕ) (ht : ticket < 6) :
    (SampLib.SystematicPPS.select 2 6 ticket [1, 2, 3] 0 0).length = 2 := by
  have h := SampLib.SystematicPPS.sample_length [1, 2, 3] 2 ticket
    (by decide) (by simpa using ht) (by intro w hw; norm_num at hw ⊢; omega)
  norm_num at h
  exact h
