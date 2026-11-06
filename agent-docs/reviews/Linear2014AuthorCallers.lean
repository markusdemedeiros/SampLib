import SampLib.Samplers.Linear2014

open ProbLang
open scoped ENNReal

namespace Linear2014AuthorCallers

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example [ProbLangDist.IsUniformInt rT] (E : CoPset) (p : unitInterval)
    (a b e f : ℤ) (h : LinearFactory.Admissible p a b e f) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ z, F z ∂RealCoin.law (LinearFactory.bias p a b e f h)) ∗ R -∗
      tglWp E pl(&Occil.FactoryExtra.linear2014 &coin.fst
        #int a #int b #int e #int f #())
        (fun v : Val rT => iprop(∃ z : Bool, ⌜v = Val.bool z⌝ ∗ ↯ (F z) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  iapply ((Linear2014.linear2014_distSpec E p a b e f h coin hcoin).wp F
    (measurable_of_countable _) _) $$ Hcredit
  iintro %z Hcredit
  iexists z
  iframe Hcredit HR
  itrivial

private def quarter : unitInterval := ⟨1 / 4, by constructor <;> norm_num⟩
private def eighth : unitInterval := ⟨1 / 8, by constructor <;> norm_num⟩

private theorem halfMargin : LinearFactory.Admissible quarter 2 1 1 2 := by
  norm_num [LinearFactory.Admissible, quarter, Gambler.ratio]

private theorem clampedMargin : LinearFactory.Admissible eighth 2 1 3 4 := by
  norm_num [LinearFactory.Admissible, eighth, Gambler.ratio]

example : (Linear2014.Parameters.initial quarter 2 1 1 2 halfMargin (by norm_num)).e = 1 := by
  norm_num [Linear2014.Parameters.initial]

example : (Linear2014.Parameters.initial eighth 2 1 3 4 clampedMargin (by norm_num)).e = 644 := by
  norm_num [Linear2014.Parameters.initial]

example : LinearFactory.Admissible (0 : unitInterval) 2 1 9 10 := by
  norm_num [LinearFactory.Admissible, Gambler.ratio]

example : LinearFactory.Admissible (1 : unitInterval) 0 1 (-10) (-20) := by
  norm_num [LinearFactory.Admissible]

example : LinearFactory.Admissible (1 : unitInterval) 1 1 (-10) (-20) := by
  norm_num [LinearFactory.Admissible]

example (p : unitInterval) : RealCoin.credit p (fun _ => ∞) = ∞ := by
  rw [← RealCoin.lintegral_law]
  simp [-Bool.univ_eq]

example : RealCoin.credit 0 (fun b => if b then ∞ else 0) = 0 := by
  simp [RealCoin.credit, RealCoin.pmf]

end

end Linear2014AuthorCallers

#print axioms SampLib.Linear2014Jump.geometric_pgf
#print axioms SampLib.Linear2014Jump.jump_expectation
#print axioms SampLib.Linear2014Jump.ordinary_bound
#print axioms SampLib.Linear2014.Parameters.expectation
#print axioms SampLib.Linear2014.Syntax.source_eq
#print axioms SampLib.Linear2014.twp_loop
#print axioms SampLib.Linear2014.linear2014_distSpec
