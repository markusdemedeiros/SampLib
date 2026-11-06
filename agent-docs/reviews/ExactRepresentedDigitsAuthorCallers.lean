import SampLib.LatentRepresentedDigits
import SampLib.LatentConstantDigits

open ProbLang
open scoped ENNReal

namespace RepresentedDigitsAuthor

open SampLib
open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open MeasureTheory (Measure IsProbabilityMeasure)

noncomputable section

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
/-- Exact observations remain valid after shorter reads through the same physical handle. -/
theorem reread (E : CoPset) (D : LatentReal.Model Ω S) (A : LatentReal.Representation D)
    (owns : Val rT → S → IProp GF) (h : LatentReal.IsRepresentedOracleSpec E D A owns)
    (v : Val rT) (s : S) (F : Ω → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :
    iprop(owns v s ∗ ↯ (∫⁻ x, F x ∂D.posterior s) ∗ R) ⊢
      tglWp E (.app (.lam (.app v.fst (.lit (.int 3)))) (.app v.fst (.lit (.int 8))))
        (fun result => iprop(∃ (t : S) (I J : LatentReal.RationalInterval),
          ⌜result = LatentReal.intervalVal J ∧ A.Observed t 8 I ∧ A.Observed t 3 J⌝ ∗
          owns v t ∗ ↯ (∫⁻ x, F x ∂D.posterior t) ∗ R)) := by
  iintro ⟨Hstate, Hcredit, HR⟩
  twp_bind pl(&v.fst #8)
  iapply (h.wp v s 8 F hF _) $$ Hstate Hcredit
  iintro %t %I %hI Hstate Hcredit
  twp_pure
  iapply (h.wp v t 3 F hF _) $$ Hstate Hcredit
  iintro %u %J %hJ Hstate Hcredit
  iexists u, I, J
  iframe Hstate Hcredit HR
  ipureintro
  exact ⟨rfl, A.observed_refines hJ.1 hI.2.2, hJ.2.2⟩

example (E : CoPset) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (digits : Ω → ℕ → Bool) (hd : ∀ n, Measurable (fun x => digits x n))
    (next : Val rT) (hnext : LatentDigits.IsNextDigitSpec (GF := GF) E μ digits hd next)
    (v : Val rT) (s : LatentDigits.State μ digits)
    (F : Ω → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :=
  reread E (LatentDigits.model μ digits hd) (LatentDigits.representation μ digits hd)
    (LatentDigits.owns μ digits next) (LatentDigits.representedOracleSpec E μ digits hd next hnext)
    v s F hF R

example (E : CoPset) (μ : Measure Ω) [IsProbabilityMeasure μ] (b : Bool) :
    LatentReal.IsRepresentedDistSpec (GF := GF) E
      pl(&Occil.PSRN.newByDigits &(LatentDigits.constantCallback b).fst #())
      (LatentDigits.model μ (fun _ _ => b) (fun _ => measurable_const))
      (LatentDigits.representation μ (fun _ _ => b) (fun _ => measurable_const))
      (LatentDigits.initial μ (fun _ _ => b))
      (LatentDigits.owns μ (fun _ _ => b) (LatentDigits.constantCallback b)) :=
  LatentDigits.newByDigits_representedDistSpec E μ (fun _ _ => b) (fun _ => measurable_const)
    (LatentDigits.constantCallback b) (LatentDigits.constant_digitSpec E μ b)

example : (LatentDigits.representedInterval (fun (_ : Unit) _ => true) 3 ()).lower = 7 := by
  norm_num [LatentDigits.representedInterval, LatentUniform.interval,
    LatentDigits.streamPrefix, List.ofFn_succ, UniformBag.rank]

example : (LatentDigits.representedInterval (fun (_ : Unit) _ => true) 3 ()).upperReal = 1 := by
  norm_num [LatentDigits.representedInterval, LatentUniform.interval,
    LatentReal.RationalInterval.upperReal, LatentDigits.streamPrefix,
    List.ofFn_succ, UniformBag.rank]

example : (LatentDigits.representedInterval (fun (_ : Unit) _ => false) 3 ()).lower = 0 := by
  norm_num [LatentDigits.representedInterval, LatentUniform.interval,
    LatentDigits.streamPrefix, List.ofFn_succ, UniformBag.rank]

#print axioms SampLib.LatentDigits.prefix_eq
#print axioms SampLib.LatentDigits.representation
#print axioms SampLib.LatentDigits.interval_observed
#print axioms SampLib.LatentDigits.representedOracleSpec
#print axioms SampLib.LatentDigits.newByDigits_representedDistSpec
#print axioms RepresentedDigitsAuthor.reread

end
end RepresentedDigitsAuthor
