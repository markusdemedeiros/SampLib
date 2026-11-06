import SampLib.Discrete.GeneralizedSibuya

open ProbLang
open scoped ENNReal

private def half : SampLib.GeneralizedSibuya.Parameters :=
  ⟨1, 2, 0, 1, by decide, by decide, by decide, by decide⟩

private def threeHalves : SampLib.GeneralizedSibuya.Parameters :=
  ⟨3, 2, 1, 1, by decide, by decide, by decide, by decide⟩

example : SampLib.GeneralizedSibuya.law half {2} = (1 : ℝ≥0∞) / 8 := by
  rw [SampLib.GeneralizedSibuya.mass half 1]
  norm_num [half, SampLib.GeneralizedSibuya.marked, SampLib.GeneralizedSibuya.total,
    SampLib.GeneralizedSibuya.unmarked, SampLib.GeneralizedSibuya.reinforcement,
    SampLib.InverseUrn.positiveMass, SampLib.InverseUrn.coefficient,
    SampLib.InverseUrn.rising, SampLib.PolyaEggenberger.rising, ENNReal.ofReal_div_of_pos]

example : SampLib.GeneralizedSibuya.law threeHalves {1} = (3 : ℝ≥0∞) / 4 := by
  rw [SampLib.GeneralizedSibuya.mass threeHalves 0]
  norm_num [threeHalves, SampLib.GeneralizedSibuya.marked, SampLib.GeneralizedSibuya.total,
    SampLib.GeneralizedSibuya.unmarked, SampLib.GeneralizedSibuya.reinforcement,
    SampLib.InverseUrn.positiveMass, SampLib.InverseUrn.coefficient,
    SampLib.InverseUrn.rising, SampLib.PolyaEggenberger.rising, ENNReal.ofReal_div_of_pos]

#print axioms SampLib.GeneralizedSibuya.mass
#print axioms SampLib.GeneralizedSibuya.generalizedSibuya_distSpec

section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example (E : CoPset) (D : SampLib.GeneralizedSibuya.Parameters) (F : ℕ → ℝ≥0∞)
    (R : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂SampLib.GeneralizedSibuya.law D) -∗ R -∗
      tglWp E pl(&Occil.DiscreteExtra.generalizedSibuya #int (D.alphaNumerator : ℤ)
        #int (D.alphaDenominator : ℤ) #int (D.nuNumerator : ℤ) #int (D.nuDenominator : ℤ))
        (fun v => iprop(∃ (k : ℕ), ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k) ∗ R)) := by
  iintro Hcredit HR
  iapply ((SampLib.GeneralizedSibuya.generalizedSibuya_distSpec E D).wp
    F (measurable_of_countable _) _) $$ Hcredit
  iintro %k Hcredit
  iexists k
  iframe Hcredit HR
  itrivial

end
