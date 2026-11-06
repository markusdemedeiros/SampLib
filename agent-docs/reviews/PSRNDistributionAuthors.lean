import SampLib.Samplers.PSRNRayleigh

#print axioms SampLib.PSRNRayleigh.newRayleigh_representedDistSpec
#print axioms SampLib.PSRNRayleigh.newRayleigh_latentDistSpec
#print axioms SampLib.PSRNRayleigh.model_law

open ProbLang SampLib.LatentReal
open Iris Iris.BI Iris.ProofMode ProbLang.TotalEris ProbLang.TotalEris.ErisWpGS
open scoped ENNReal

example (t : ℝ) :
    ProbabilityTheory.cdf (SampLib.PSRNRayleigh.model.law SampLib.PSRNRayleigh.initial) t =
      if 0 ≤ t then 1 - Real.exp (-(t ^ 2 / 2)) else 0 := by
  rw [SampLib.PSRNRayleigh.model_law, SampLib.PSRNRayleigh.cdf_eq]

section

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example (E : CoPset) (n m : ℕ) (F : ℕ × ℝ → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :
    iprop(R ∗ ↯ (∫⁻ x, F x ∂SampLib.PSRNRayleigh.model.posterior
      SampLib.PSRNRayleigh.initial)) ⊢
      tglWp E pl(let draw := &Occil.PSRN.newRayleigh #();
        let first := draw #int (n : ℤ);
        let second := draw #int (m : ℤ);
        (first, second))
        (fun result : Val rT => iprop(∃ (v : Val rT) (s : _) (I J : RationalInterval),
          ⌜result = Val.pair (intervalVal I) (intervalVal J) ∧
            SampLib.PSRNRayleigh.model.refines SampLib.PSRNRayleigh.initial s ∧
            SampLib.PSRNRayleigh.model.Encloses s n I ∧
            SampLib.PSRNRayleigh.model.Encloses s m J ∧
            SampLib.PSRNRayleigh.model.dyadicRepresentation.Observed s n I ∧
            SampLib.PSRNRayleigh.model.dyadicRepresentation.Observed s m J⌝ ∗
          SampLib.PSRNRayleigh.owns v s ∗ R ∗
          ↯ (∫⁻ x, F x ∂SampLib.PSRNRayleigh.model.posterior s))) := by
  let h := SampLib.PSRNRayleigh.newRayleigh_representedDistSpec (rT := rT) (GF := GF) E
  iintro ⟨HR, Hcredit⟩
  twp_bind pl(&Occil.PSRN.newRayleigh #())
  iapply h.forget.wp F hF _ $$ Hcredit
  iintro %draw %t %ht Hstate Hcredit
  twp_pure
  twp_bind pl(&draw.fst #int (n : ℤ))
  iapply h.oracle.wp draw t n F hF _ $$ Hstate Hcredit
  iintro %u %I %hI Hstate Hcredit
  twp_pure
  twp_bind pl(&draw.fst #int (m : ℤ))
  iapply h.oracle.wp draw u m F hF _ $$ Hstate Hcredit
  iintro %w %J %hJ Hstate Hcredit
  twp_pure
  twp_value
  imodintro
  iexists draw, w, I, J
  iframe Hstate HR Hcredit
  ipureintro
  exact ⟨rfl, SampLib.PSRNRayleigh.model.refines_trans ht
    (SampLib.PSRNRayleigh.model.refines_trans hI.1 hJ.1),
    SampLib.PSRNRayleigh.model.encloses_refines hJ.1 hI.2.1, hJ.2.1,
    SampLib.PSRNRayleigh.model.dyadicRepresentation.observed_refines hJ.1 hI.2.2, hJ.2.2⟩

end
