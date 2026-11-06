import SampLib.LatentUniformRepresentation

open ProbLang
open scoped ENNReal

namespace UniformRepresentationAuthor

open SampLib SampLib.LatentUniform
open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

noncomputable section

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- A shorter read through the same alias retains the earlier exact observation. -/
theorem read_eight_then_three (E : CoPset) (v : Val rT) (p : List Bool)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :
    iprop(owns v p ∗ ↯ (∫⁻ x, F x ∂model.posterior p) ∗ R) ⊢
      tglWp E (.app (.lam (.app v.fst (.lit (.int 3)))) (.app v.fst (.lit (.int 8))))
        (fun result => iprop(∃ (q : List Bool) (I J : LatentReal.RationalInterval),
          ⌜result = LatentReal.intervalVal J ∧ representation.Observed q 8 I ∧
            representation.Observed q 3 J⌝ ∗
          owns v q ∗ ↯ (∫⁻ x, F x ∂model.posterior q) ∗ R)) := by
  iintro ⟨Hstate, Hcredit, HR⟩
  twp_bind pl(&v.fst #8)
  iapply ((representedOracleSpec E).wp v p 8 F hF _) $$ Hstate Hcredit
  iintro %q %I %hI Hstate Hcredit
  twp_pure
  iapply ((representedOracleSpec E).wp v q 3 F hF _) $$ Hstate Hcredit
  iintro %t %J %hJ Hstate Hcredit
  iexists t, I, J
  iframe Hstate Hcredit HR
  ipureintro
  exact ⟨rfl, representation.observed_refines hJ.1 hI.2.2, hJ.2.2⟩

example : (dyadicInterval 3 0).lower = 0 := by norm_num [dyadicInterval]
example : (dyadicInterval 3 (1 / 2)).lower = 4 := by norm_num [dyadicInterval]
example : (dyadicInterval 3 1).lower = 8 := by norm_num [dyadicInterval]
example : (dyadicInterval 3 (-1 / 2)).lower = -4 := by norm_num [dyadicInterval]
example (x : ℝ) : (dyadicInterval 3 x).width = 1 / 8 := by
  rw [dyadicInterval_width]
  norm_num

example (E : CoPset) :
    LatentReal.IsLatentDistSpec (GF := GF) E pl(&Occil.PSRN.newUniform #())
      model [] owns := (newUniform_representedDistSpec E).forget

#print axioms SampLib.LatentUniform.interval_observed
#print axioms SampLib.LatentUniform.representedOracleSpec
#print axioms SampLib.LatentUniform.newUniform_representedDistSpec
#print axioms UniformRepresentationAuthor.read_eight_then_three

end
end UniformRepresentationAuthor
