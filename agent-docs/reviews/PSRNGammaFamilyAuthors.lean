import SampLib.Samplers.PSRNGammaFamilies

open ProbLang SampLib.LatentReal SampLib.PSRNGammaFamilies
open Iris Iris.BI Iris.ProofMode ProbLang.TotalEris ProbLang.TotalEris.ErisWpGS
open scoped ENNReal

section

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
/-- A reusable same-handle client: both reads retain one latent world and one cache. -/
theorem twoReads {Ω S : Type} [MeasurableSpace Ω] (E : CoPset) (e : Exp rT)
    (D : Model Ω S) (initial : S) (owns : Val rT → S → IProp GF)
    (h : IsLatentDistSpec E e D initial owns) (n m : ℕ)
    (F : Ω → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :
    iprop(R ∗ ↯ (∫⁻ x, F x ∂D.posterior initial)) ⊢
      tglWp E pl(let draw := &e;
        let first := draw #int (n : ℤ);
        let second := draw #int (m : ℤ);
        (first, second))
        (fun result : Val rT => iprop(∃ (v : Val rT) (s : S) (I J : RationalInterval),
          ⌜result = Val.pair (intervalVal I) (intervalVal J) ∧
            D.refines initial s ∧ D.Encloses s n I ∧ D.Encloses s m J⌝ ∗
          owns v s ∗ R ∗ ↯ (∫⁻ x, F x ∂D.posterior s))) := by
  iintro ⟨HR, Hcredit⟩
  twp_bind e
  iapply h.wp F hF _ $$ Hcredit
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
  exact ⟨rfl, D.refines_trans ht (D.refines_trans hI.1 hJ.1),
    D.encloses_refines hJ.1 hI.2, hJ.2⟩

#check @newGarima_latentDistSpec
example (E : CoPset) :=
  twoReads E _ _ _ _ (newGarima_latentDistSpec (rT := rT) (GF := GF) E 3 2 (by decide) (by decide))
    7 1 (fun _ => ∞) measurable_const (iprop(⌜True⌝) : IProp GF)

#check @newIGarima_latentDistSpec
example (E : CoPset) :=
  twoReads E _ _ _ _ (newIGarima_latentDistSpec (rT := rT) (GF := GF) E 1 3 (by decide) (by decide))
    7 1 (fun _ => ∞) measurable_const (iprop(⌜True⌝) : IProp GF)

#check @newXgamma_latentDistSpec
example (E : CoPset) :=
  twoReads E _ _ _ _ (newXgamma_latentDistSpec (rT := rT) (GF := GF) E 2 5 (by decide) (by decide))
    7 1 (fun _ => ∞) measurable_const (iprop(⌜True⌝) : IProp GF)

#check @newWeightedExponentialGamma_latentDistSpec
example (E : CoPset) :=
  twoReads E _ _ _ _ (newWeightedExponentialGamma_latentDistSpec (rT := rT) (GF := GF) E 4 3 (by decide) (by decide))
    7 1 (fun _ => ∞) measurable_const (iprop(⌜True⌝) : IProp GF)

#check @newMirra_latentDistSpec
example (E : CoPset) :=
  twoReads E _ _ _ _ (newMirra_latentDistSpec (rT := rT) (GF := GF) E 5 2 3 7 (by decide) (by decide) (by decide) (by decide))
    7 1 (fun _ => ∞) measurable_const (iprop(⌜True⌝) : IProp GF)

end

#print axioms SampLib.PSRNGammaFamilies.newGarima_latentDistSpec
#print axioms SampLib.PSRNGammaFamilies.newIGarima_latentDistSpec
#print axioms SampLib.PSRNGammaFamilies.newXgamma_latentDistSpec
#print axioms SampLib.PSRNGammaFamilies.newWeightedExponentialGamma_latentDistSpec
#print axioms SampLib.PSRNGammaFamilies.newMirra_latentDistSpec
#print axioms SampLib.PSRNGammaFamilies.garima_model_law
#print axioms SampLib.PSRNGammaFamilies.igarima_model_law
#print axioms SampLib.PSRNGammaFamilies.xgamma_model_law
#print axioms SampLib.PSRNGammaFamilies.weightedExponentialGamma_model_law
#print axioms SampLib.PSRNGammaFamilies.mirra_model_law
