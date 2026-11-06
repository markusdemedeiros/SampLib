import SampLib.Samplers.PSRNGammaFamilies
import SampLib.Samplers.PSRNLindleyFamilies

/-! Author-side callers for the named gamma-mixture and Lindley-family PSRN samplers.

Each client constructs the actual sampler, then reads the SAME returned oracle twice
(precisions in either order) with an arbitrary framed Iris resource and arbitrary
measurable joint latent-world credit, including `∞`. -/

open ProbLang SampLib.LatentReal
open Iris Iris.BI Iris.ProofMode ProbLang.TotalEris ProbLang.TotalEris.ErisWpGS
open scoped ENNReal

section

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
/-- Construct once, read the same handle twice, and keep the frame `R`. -/
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

section gamma

open SampLib.PSRNGammaFamilies

variable (E : CoPset) (R : IProp GF)

-- Smallest rate `1/1`, precision 0 then a refinement; arbitrary credit and frame.
example := fun (F : _ → ℝ≥0∞) (hF : Measurable F) =>
  twoReads E _ _ _ _ (newGarima_latentDistSpec (rT := rT) (GF := GF) E 1 1 one_pos one_pos)
    0 9 F hF R

-- Unreduced rate `4/2` and a shorter reread.
example := fun (F : _ → ℝ≥0∞) (hF : Measurable F) =>
  twoReads E _ _ _ _ (newIGarima_latentDistSpec (rT := rT) (GF := GF) E 4 2
    (by decide) (by decide)) 8 2 F hF R

-- Rate below one, infinite credit.
example :=
  twoReads E _ _ _ _ (newXgamma_latentDistSpec (rT := rT) (GF := GF) E 2 5
    (by decide) (by decide)) 3 3 (fun _ => ∞) measurable_const R

example := fun (F : _ → ℝ≥0∞) (hF : Measurable F) =>
  twoReads E _ _ _ _ (newWeightedExponentialGamma_latentDistSpec (rT := rT) (GF := GF) E 1 1
    one_pos one_pos) 0 5 F hF R

-- Mirra's second parameter at its smallest value `1/1` and at an unreduced fraction.
example := fun (F : _ → ℝ≥0∞) (hF : Measurable F) =>
  twoReads E _ _ _ _ (newMirra_latentDistSpec (rT := rT) (GF := GF) E 1 1 1 1
    one_pos one_pos one_pos one_pos) 4 1 F hF R

example := fun (F : _ → ℝ≥0∞) (hF : Measurable F) =>
  twoReads E _ _ _ _ (newMirra_latentDistSpec (rT := rT) (GF := GF) E 5 2 6 4
    (by decide) (by decide) (by decide) (by decide)) 4 1 F hF R

end gamma

section lindley

open SampLib.PSRNLindleyFamilies

variable (E : CoPset) (R : IProp GF)

-- Sushila at scale one and at a shrinking unreduced scale.
example := fun (F : _ → ℝ≥0∞) (hF : Measurable F) =>
  twoReads E _ _ _ _ (newSushila_latentDistSpec (rT := rT) (GF := GF) E 1 1 1 1
    one_pos one_pos one_pos one_pos) 0 6 F hF R

example := fun (F : _ → ℝ≥0∞) (hF : Measurable F) =>
  twoReads E _ _ _ _ (newSushila_latentDistSpec (rT := rT) (GF := GF) E 3 7 2 6
    (by decide) (by decide) (by decide) (by decide)) 6 0 F hF R

-- XLindley keeps the selector-indexed world (exponential or Lindley component).
example := fun (F : _ → ℝ≥0∞) (hF : Measurable F) =>
  twoReads E _ _ _ _ (newXLindley_latentDistSpec (rT := rT) (GF := GF) E 1 1
    one_pos one_pos) 2 7 F hF R

example :=
  twoReads E _ _ _ _ (newXLindley_latentDistSpec (rT := rT) (GF := GF) E 5 2
    (by decide) (by decide)) 7 7 (fun _ => ∞) measurable_const R

end lindley

end

-- Canonical laws.
example : (SampLib.PSRNGammaFamilies.garimaModel 1 1 one_pos one_pos).law .initial =
    MeasureTheory.volume.withDensity (fun x => ENNReal.ofReal
      (SampLib.PSRNGammaFamilyDensities.garimaPDF ((1 : ℤ) / (1 : ℤ) : ℝ) x)) :=
  SampLib.PSRNGammaFamilies.garima_model_law_density 1 1 one_pos one_pos

example : (SampLib.PSRNLindleyFamilies.xlindleyModel 2 5 (by decide) (by decide)).law .initial =
    MeasureTheory.volume.withDensity (fun x => ENNReal.ofReal
      (SampLib.PSRNLindleyFamilies.xlindleyPDFReal ((2 : ℤ) / (5 : ℤ) : ℝ) x)) :=
  SampLib.PSRNLindleyFamilies.xlindley_model_law 2 5 (by decide) (by decide)

#print axioms SampLib.PSRNGammaFamilies.newGarima_latentDistSpec
#print axioms SampLib.PSRNGammaFamilies.newIGarima_latentDistSpec
#print axioms SampLib.PSRNGammaFamilies.newXgamma_latentDistSpec
#print axioms SampLib.PSRNGammaFamilies.newWeightedExponentialGamma_latentDistSpec
#print axioms SampLib.PSRNGammaFamilies.newMirra_latentDistSpec
#print axioms SampLib.PSRNGammaFamilies.garima_model_law_density
#print axioms SampLib.PSRNGammaFamilies.igarima_model_law_density
#print axioms SampLib.PSRNGammaFamilies.xgamma_model_law_density
#print axioms SampLib.PSRNGammaFamilies.weightedExponentialGamma_model_law_density
#print axioms SampLib.PSRNGammaFamilies.mirra_model_law_density
#print axioms SampLib.PSRNLindleyFamilies.newSushila_latentDistSpec
#print axioms SampLib.PSRNLindleyFamilies.newXLindley_latentDistSpec
#print axioms SampLib.PSRNLindleyFamilies.sushila_model_law
#print axioms SampLib.PSRNLindleyFamilies.xlindley_model_law
