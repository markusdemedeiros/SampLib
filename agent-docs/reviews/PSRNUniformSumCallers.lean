import SampLib.Samplers.PSRNUniformSum

open ProbLang SampLib.LatentReal SampLib.PSRNUniformSum
open scoped ENNReal

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example (n : ℕ) : (model n).law (initial n) = SampLib.UniformSum.law n := model_law n

/-- A real caller keeps an unrelated resource and reads one returned handle twice. -/
example (E : CoPset) (n a b : ℕ) (F : World n → ℝ≥0∞) (hF : Measurable F)
    (R : IProp GF) :
    ⊢ R ∗ ↯ (∫⁻ x, F x ∂(model n).posterior (initial n)) -∗
      tglWp E pl(let value := &Occil.PSRN.newUniformSum #int (n : ℤ);
        let first := value #int (a : ℤ); value #int (b : ℤ))
        (fun result : Val rT => iprop(∃ (value : Val rT) (t : State n) (I : RationalInterval),
          ⌜result = intervalVal I ∧ (model n).Encloses t b I⌝ ∗
          owns n value t ∗ R ∗ ↯ (∫⁻ x, F x ∂(model n).posterior t))) := by
  iintro ⟨HR, Hcredit⟩
  twp_bind pl(&Occil.PSRN.newUniformSum #int (n : ℤ))
  iapply (newUniformSum_latentDistSpec E n).wp F hF _ $$ Hcredit
  iintro %value %s %hs Hstate Hcredit
  twp_pure
  twp_bind pl(&value.fst #int (a : ℤ))
  iapply (oracleSpec E n).wp value s a F hF _ $$ Hstate Hcredit
  iintro %t %I %hI Hstate Hcredit
  twp_pure
  iapply (oracleSpec E n).wp value t b F hF _ $$ Hstate Hcredit
  iintro %u %J %hJ Hstate Hcredit
  iexists value, u, J
  iframe Hstate HR Hcredit
  ipureintro
  exact ⟨rfl, hJ.2⟩

#print axioms SampLib.PSRNUniformSum.model_law
#print axioms SampLib.PSRNUniformSum.oracleSpec
#print axioms SampLib.PSRNUniformSum.newUniformSum_latentDistSpec
