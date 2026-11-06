import SampLib.Samplers.PSRNReciprocalUniform

open ProbLang
open scoped ENNReal

namespace ReciprocalUniformAuthor

open SampLib SampLib.PSRNReciprocalUniform
open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

noncomputable section

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private def readTwice (v : Val rT) : Exp rT :=
  .app (.lam (.app v.fst (.lit (.int 7)))) (.app v.fst (.lit (.int 0)))

/-- Precision zero also terminates, retaining its exact adaptive interval through a later read. -/
theorem reread (E : CoPset) (v : Val rT) (p : List Bool)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :
    iprop(owns v p ∗ ↯ (∫⁻ u, F u ∂model.posterior p) ∗ R) ⊢
      tglWp E (readTwice v) (fun result =>
        iprop(∃ (q : List Bool) (I J : LatentReal.RationalInterval),
          ⌜result = LatentReal.intervalVal J ∧ representation.Observed q 0 I ∧
            representation.Observed q 7 J⌝ ∗
          owns v q ∗ ↯ (∫⁻ u, F u ∂model.posterior q) ∗ R)) := by
  iintro ⟨Hstate, Hcredit, HR⟩
  unfold readTwice
  twp_bind pl(&v.fst #0)
  iapply ((representedOracleSpec E).wp v p 0 F hF _) $$ Hstate Hcredit
  iintro %q %I %hI Hstate Hcredit
  twp_pure
  iapply ((representedOracleSpec E).wp v q 7 F hF _) $$ Hstate Hcredit
  iintro %t %J %hJ Hstate Hcredit
  iexists t, I, J
  iframe Hstate Hcredit HR
  ipureintro
  exact ⟨rfl, representation.observed_refines hJ.1 hI.2.2, hJ.2.2⟩

/-- The actual constructor returns the certified owned observer and unspent joint credit. -/
example (E : CoPset) (F : ℝ → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :
    iprop(↯ (∫⁻ u, F u ∂model.posterior []) ∗ R) ⊢
      tglWp E pl(&Occil.PSRN.newReciprocalUniform #()) (fun v =>
        iprop(∃ p : List Bool, owns v p ∗ ↯ (∫⁻ u, F u ∂model.posterior p) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  iapply ((newReciprocalUniform_representedDistSpec E).toIsLatentPayloadSpec.wp F hF _)
    $$ Hcredit
  iintro %v %p %hp Hstate Hcredit
  iexists p
  iframe Hstate Hcredit HR

example : model.law [] (Set.Iic 1) = 0 := by
  rw [initial_law_pushforward]
  change ReciprocalUniform.law (Set.Iic 1) = 0
  rw [ReciprocalUniform.law_Iic]
  norm_num

example : model.law [] (Set.Iic 0) = 0 := by
  rw [initial_law_pushforward]
  change ReciprocalUniform.law (Set.Iic 0) = 0
  rw [ReciprocalUniform.law_Iic]
  norm_num

example : model.law [] Set.univ = 1 := MeasureTheory.measure_univ

example (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ y, F y ∂model.law []) = ∫⁻ u in Set.Ico (0 : ℝ) 1, F (1 / u) := by
  rw [initial_law_pushforward]
  exact ReciprocalUniform.expectation F hF

example : (∫⁻ _y, (∞ : ℝ≥0∞) ∂model.law []) = ∞ := by
  simp only [MeasureTheory.lintegral_const, MeasureTheory.measure_univ, mul_one]

example : (∫⁻ y, (Set.Iic (1 : ℝ)).indicator (fun _ => (∞ : ℝ≥0∞)) y
    ∂model.law []) = 0 := by
  have hzero : model.law [] (Set.Iic 1) = 0 := by
    rw [initial_law_pushforward]
    change ReciprocalUniform.law (Set.Iic 1) = 0
    rw [ReciprocalUniform.law_Iic]
    norm_num
  rw [MeasureTheory.lintegral_indicator measurableSet_Iic, MeasureTheory.setLIntegral_const,
    hzero, mul_zero]

#print axioms SampLib.PSRNReciprocalUniform.Program.source_eq
#print axioms SampLib.PSRNReciprocalUniform.initial_law
#print axioms SampLib.PSRNReciprocalUniform.newReciprocalUniform_representedDistSpec
#print axioms SampLib.PSRNReciprocalUniform.newReciprocalUniform_latentDistSpec
#print axioms ReciprocalUniformAuthor.reread

end
end ReciprocalUniformAuthor
