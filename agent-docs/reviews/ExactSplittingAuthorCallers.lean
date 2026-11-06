import SampLib.Weighted.InclusionSplitting

open ProbLang Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open scoped ENNReal

namespace SplittingAuthorChecks

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example (E : CoPset) (R : IProp GF) (F : List ℤ → ℝ≥0∞) :
    ↯ (F []) ∗ R ⊢
      tglWp E pl(&Occil.Weighted.inclusionSplitting
        &(SampLib.listVal (fun n : ℕ => Val.int n) []).fst #0)
        (fun v => iprop(⌜v = SampLib.listVal Val.int []⌝ ∗ ↯ (F []) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  have hbudget : (∫⁻ xs, F xs ∂MeasureTheory.Measure.dirac ([] : List ℤ)) = F [] :=
    MeasureTheory.lintegral_dirac _ _
  isimp only [← hbudget] at Hcredit
  iapply ((SampLib.InclusionSplitting.inclusionSplitting_zero_distSpec E []).wp_supported
    (fun ys => ys = []) (Set.to_countable _).measurableSet
    (by simp only [MeasureTheory.ae_dirac_eq, Filter.eventually_pure])
    F (measurable_of_countable _) _) $$ Hcredit
  iintro %ys %hy Hcredit
  subst ys
  iframe Hcredit HR
  ipureintro
  rfl

variable [ProbLangDist.IsUniformInt rT]

example (E : CoPset) (ws : List ℕ) (count : ℕ) (ht : 0 < ws.sum)
    (hc : count ≤ ws.length) (hcap : ∀ w ∈ ws, count * w ≤ ws.sum)
    (F : List ℤ → ℝ≥0∞) (R : IProp GF) :
    ↯ (∫⁻ xs, F xs ∂SampLib.SplittingPPS.inputLaw ws count ht hc hcap) ∗ R ⊢
      tglWp E pl(&Occil.Weighted.inclusionSplitting
        &(SampLib.listVal (fun n : ℕ => Val.int n) ws).fst #int (count : ℤ))
        (fun v => iprop(∃ xs : List ℤ, ⌜v = SampLib.listVal Val.int xs⌝ ∗ ↯ (F xs) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  iapply ((SampLib.InclusionSplitting.inclusionSplitting_distSpec E ws count ht hc hcap).wp F
    (measurable_of_countable _) _) $$ Hcredit
  iintro %xs Hcredit
  iexists xs
  iframe Hcredit HR
  ipureintro
  rfl

example : SampLib.SplittingPPS.inputLaw [1, 2, 2, 3] 2 (by norm_num) (by norm_num)
    (by norm_num) {xs | (3 : ℤ) ∈ xs} = (6 : ℝ≥0∞) / 8 := by
  exact SampLib.SplittingPPS.input_inclusion_probability [1, 2, 2, 3] 2 3
    (by decide) (by decide) (by decide) (by decide)

example : ∀ᵐ xs ∂SampLib.SplittingPPS.inputLaw [1, 1, 0] 2 (by norm_num) (by norm_num)
    (by norm_num), xs.length = 2 := SampLib.SplittingPPS.input_length _ _ _ _ _

example : ∀ᵐ xs ∂SampLib.SplittingPPS.inputLaw [2, 2] 2 (by norm_num) (by norm_num)
    (by norm_num), xs.Nodup := SampLib.SplittingPPS.input_nodup _ _ _ _ _

#print axioms SampLib.InclusionSplitting.inclusionSplitting_distSpec
#print axioms SampLib.InclusionSplitting.inclusionSplitting_zero_distSpec
#print axioms SampLib.SplittingPPS.input_inclusion_expectation
#print axioms SampLib.SplittingPPS.input_inclusion_probability
#print axioms SampLib.SplittingPPS.input_length
#print axioms SampLib.SplittingPPS.input_nodup

end SplittingAuthorChecks
