import SampLib.LatentUniformRepresentation

open ProbLang
open scoped ENNReal

namespace UniformRepresentationReview001

open SampLib SampLib.LatentUniform
open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

noncomputable section

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem aliases (E : CoPset) (v w : Val rT) (halias : w = v) (p : List Bool)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :
    iprop(owns v p ∗ ↯ (∫⁻ x, F x ∂model.posterior p) ∗ R) ⊢
      tglWp E
        (.app (.lam (.app (.lam (.app w.fst (.lit (.int 5))))
          (.app v.fst (.lit (.int 0))))) (.app w.fst (.lit (.int 11))))
        (fun result => iprop(∃ (q : List Bool) (I J K : LatentReal.RationalInterval),
          ⌜result = LatentReal.intervalVal K ∧ representation.Observed q 11 I ∧
            representation.Observed q 0 J ∧ representation.Observed q 5 K⌝ ∗
          owns v q ∗ ↯ (∫⁻ x, F x ∂model.posterior q) ∗ R)) := by
  subst w
  iintro ⟨Hstate, Hcredit, HR⟩
  twp_bind pl(&v.fst #11)
  iapply ((representedOracleSpec E).wp v p 11 F hF _) $$ Hstate Hcredit
  iintro %q %I %hI Hstate Hcredit
  twp_pure
  twp_bind pl(&v.fst #0)
  iapply ((representedOracleSpec E).wp v q 0 F hF _) $$ Hstate Hcredit
  iintro %t %J %hJ Hstate Hcredit
  twp_pure
  iapply ((representedOracleSpec E).wp v t 5 F hF _) $$ Hstate Hcredit
  iintro %u %K %hK Hstate Hcredit
  iexists u, I, J, K
  iframe Hstate Hcredit HR
  ipureintro
  exact ⟨rfl, representation.observed_refines hK.1
    (representation.observed_refines hJ.1 hI.2.2),
    representation.observed_refines hK.1 hJ.2.2, hK.2.2⟩

example : (dyadicInterval 0 (3 / 4)).lower = 0 := by norm_num [dyadicInterval]
example : (dyadicInterval 5 (1 / 32)).lower = 1 := by norm_num [dyadicInterval]
example : (dyadicInterval 5 (-1 / 64)).lower = -1 := by norm_num [dyadicInterval]
example (x : ℝ) : (dyadicInterval 0 x).width = 1 := by
  rw [dyadicInterval_width]
  norm_num

example (E : CoPset) (v w : Val rT) (h : w = v) (p : List Bool) (R : IProp GF) :
    iprop(owns v p ∗ ↯ (∫⁻ x, (if x < 1 / 2 then ∞ else ENNReal.ofReal x)
      ∂model.posterior p) ∗ R) ⊢
      tglWp E
        (.app (.lam (.app (.lam (.app w.fst (.lit (.int 5))))
          (.app v.fst (.lit (.int 0))))) (.app w.fst (.lit (.int 11))))
        (fun result => iprop(∃ (q : List Bool) (I J K : LatentReal.RationalInterval),
          ⌜result = LatentReal.intervalVal K ∧ representation.Observed q 11 I ∧
            representation.Observed q 0 J ∧ representation.Observed q 5 K⌝ ∗
          owns v q ∗ ↯ (∫⁻ x, (if x < 1 / 2 then ∞ else ENNReal.ofReal x)
            ∂model.posterior q) ∗ R)) :=
  aliases E v w h p _ (by
    exact Measurable.ite measurableSet_Iio measurable_const ENNReal.measurable_ofReal) R

#print axioms SampLib.LatentUniform.interval_observed
#print axioms SampLib.LatentUniform.representedOracleSpec
#print axioms SampLib.LatentUniform.newUniform_representedDistSpec
#print axioms SampLib.LatentUniform.dyadicInterval_approximates
#print axioms UniformRepresentationReview001.aliases

end
end UniformRepresentationReview001
