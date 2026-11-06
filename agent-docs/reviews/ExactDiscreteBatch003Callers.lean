import SampLib.Samplers.GeneralizedSibuya

open ProbLang
open scoped ENNReal

namespace ReviewExactDiscrete003

noncomputable section

open SampLib

private def sibuya : GeneralizedSibuya.Parameters :=
  ⟨1, 2, 0, 1, by decide, by decide, by decide, by decide⟩

private def aboveOne : GeneralizedSibuya.Parameters :=
  ⟨3, 2, 1, 1, by decide, by decide, by decide, by decide⟩

example : GeneralizedSibuya.law sibuya {2} = (1 : ℝ≥0∞) / 8 := by
  rw [GeneralizedSibuya.mass sibuya 1]
  norm_num [sibuya, GeneralizedSibuya.marked, GeneralizedSibuya.unmarked,
    GeneralizedSibuya.total, GeneralizedSibuya.reinforcement,
    InverseUrn.positiveMass, InverseUrn.coefficient, InverseUrn.rising,
    PolyaEggenberger.rising, Nat.choose, ENNReal.ofReal_div_of_pos]

example : GeneralizedSibuya.law aboveOne {1} = (3 : ℝ≥0∞) / 4 := by
  rw [GeneralizedSibuya.mass aboveOne 0]
  norm_num [aboveOne, GeneralizedSibuya.marked, GeneralizedSibuya.unmarked,
    GeneralizedSibuya.total, GeneralizedSibuya.reinforcement,
    InverseUrn.positiveMass, InverseUrn.coefficient, InverseUrn.rising,
    PolyaEggenberger.rising, Nat.choose, ENNReal.ofReal_div_of_pos]

example : GeneralizedSibuya.law sibuya {0} = 0 := by
  rw [GeneralizedSibuya.law, MeasureTheory.Measure.map_apply (measurable_of_countable _)
    (measurableSet_singleton _)]
  have hpre : Nat.succ ⁻¹' ({0} : Set ℕ) = ∅ := by ext n; simp
  simp only [hpre, MeasureTheory.measure_empty]

section callers

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem framed (E : CoPset) (D : GeneralizedSibuya.Parameters)
    (F : ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂GeneralizedSibuya.law D) ∗ R -∗
      tglWp E pl(&Occil.DiscreteExtra.generalizedSibuya #int (D.alphaNumerator : ℤ)
        #int (D.alphaDenominator : ℤ) #int (D.nuNumerator : ℤ) #int (D.nuDenominator : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int k⌝ ∗ ↯ (F k) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  iapply ((GeneralizedSibuya.generalizedSibuya_distSpec E D).wp
    F (measurable_of_countable _) _) $$ Hcredit
  iintro %k Hcredit
  iexists k
  iframe Hcredit HR
  itrivial

example (E : CoPset) (F : ℕ → ℝ≥0∞) (R : IProp GF) := framed E sibuya F R
example (E : CoPset) (F : ℕ → ℝ≥0∞) (R : IProp GF) := framed E aboveOne F R
example (E : CoPset) (R : IProp GF) := framed E sibuya (fun _ => ∞) R

end callers

#print axioms SampLib.GeneralizedSibuya.generalizedSibuya_distSpec
#print axioms SampLib.GeneralizedSibuya.mass

end
end ReviewExactDiscrete003
