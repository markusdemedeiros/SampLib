import SampLib.Samplers.InversePolya
import SampLib.Samplers.BetaNegativeBinomial
import SampLib.Samplers.WaringYule
import SampLib.Samplers.YuleSimon

open ProbLang
open scoped ENNReal

private def unitShapes : SampLib.BetaNegativeBinomial.Parameters :=
  ⟨1, 1, 1, 1, by decide, by decide, by decide, by decide⟩

example : SampLib.BetaNegativeBinomial.law unitShapes 1 {0} = (1 : ℝ≥0∞) / 2 := by
  rw [SampLib.BetaNegativeBinomial.mass unitShapes 0 0]
  norm_num [unitShapes, SampLib.BetaNegativeBinomial.marked,
    SampLib.BetaNegativeBinomial.unmarked, SampLib.BetaNegativeBinomial.reinforcement,
    SampLib.InverseUrn.positiveMass, SampLib.InverseUrn.coefficient,
    SampLib.InverseUrn.rising, SampLib.PolyaEggenberger.rising, ENNReal.ofReal_div_of_pos]

example : SampLib.BetaNegativeBinomial.law unitShapes 1 {1} = (1 : ℝ≥0∞) / 6 := by
  rw [SampLib.BetaNegativeBinomial.mass unitShapes 0 1]
  norm_num [unitShapes, SampLib.BetaNegativeBinomial.marked,
    SampLib.BetaNegativeBinomial.unmarked, SampLib.BetaNegativeBinomial.reinforcement,
    SampLib.InverseUrn.positiveMass, SampLib.InverseUrn.coefficient,
    SampLib.InverseUrn.rising, SampLib.PolyaEggenberger.rising, ENNReal.ofReal_div_of_pos]

example : SampLib.InverseUrn.law 2 2 3 0 (by decide) {1} = (24 : ℝ≥0∞) / 125 := by
  rw [SampLib.InverseUrn.mass_positive 1 2 3 0 1 (by decide)]
  norm_num [SampLib.InverseUrn.positiveMass, SampLib.InverseUrn.coefficient,
    SampLib.InverseUrn.rising, SampLib.PolyaEggenberger.rising, ENNReal.ofReal_div_of_pos]

example : SampLib.InverseUrn.law 4 2 0 3 (by decide) {1} = 0 := by
  rw [SampLib.InverseUrn.mass_positive 3 2 0 3 1 (by decide)]
  norm_num [SampLib.InverseUrn.positiveMass, SampLib.InverseUrn.coefficient,
    SampLib.InverseUrn.rising, SampLib.PolyaEggenberger.rising, ENNReal.ofReal_div_of_pos]

#print axioms SampLib.InverseUrn.mass_positive
#print axioms SampLib.InversePolya.twp_inversePolya
#print axioms SampLib.InversePolya.inversePolya_distSpec
#print axioms SampLib.BetaNegativeBinomial.betaNegativeBinomial_distSpec
#print axioms SampLib.WaringYule.waringYule_distSpec
#print axioms SampLib.YuleSimon.yuleSimon_distSpec

section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example (E : CoPset) (D : SampLib.BetaNegativeBinomial.Parameters) (r : ℕ)
    (F : ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂SampLib.BetaNegativeBinomial.law D r) -∗ R -∗
      tglWp E pl(&Occil.DiscreteExtra.betaNegativeBinomial #int (r : ℤ)
        #int (D.alphaNumerator : ℤ) #int (D.alphaDenominator : ℤ)
        #int (D.betaNumerator : ℤ) #int (D.betaDenominator : ℤ))
        (fun v => iprop(∃ (k : ℕ), ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k) ∗ R)) := by
  iintro Hcredit HR
  iapply ((SampLib.BetaNegativeBinomial.betaNegativeBinomial_distSpec E D r).wp
    F (measurable_of_countable _) _) $$ Hcredit
  iintro %k Hcredit
  iexists k
  iframe Hcredit HR
  itrivial

end
