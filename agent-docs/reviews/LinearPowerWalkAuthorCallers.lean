import SampLib.Bernoulli.LinearPowerWalk

open ProbLang
open scoped ENNReal

namespace LinearPowerWalkAuthorCallers

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example [ProbLangDist.IsUniformInt rT] (E : CoPset) (p : unitInterval)
    (a b e f : ℤ) (h : LinearFactory.Admissible p a b e f) (n : ℕ) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ z, F z ∂IterateCoin.law (LinearFactory.bias p a b e f h) n) ∗ R -∗
      tglWp E pl(&Occil.FactoryExtra.linearPowerWalk &coin.fst
        #int a #int b #int (n : ℤ) #int e #int f #())
        (fun v : Val rT => iprop(∃ z : Bool, ⌜v = Val.bool z⌝ ∗ ↯ (F z) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  iapply ((LinearPowerWalk.linearPowerWalk_distSpec E p a b e f h n coin hcoin).wp F
    (measurable_of_countable _) _) $$ Hcredit
  iintro %z Hcredit
  iexists z
  iframe Hcredit HR
  itrivial

private def quarter : unitInterval := ⟨1 / 4, by constructor <;> norm_num⟩

example : LinearFactory.Admissible quarter 2 1 1 2 := by
  norm_num [LinearFactory.Admissible, quarter, Gambler.ratio]

example : LinearFactory.Admissible (0 : unitInterval) 2 1 1 2 := by
  norm_num [LinearFactory.Admissible, Gambler.ratio]

example : LinearFactory.Admissible (1 : unitInterval) 1 2 (-10) (-20) := by
  norm_num [LinearFactory.Admissible, Gambler.ratio]

example (p : unitInterval) (F : Bool → ℝ≥0∞) : IterateCoin.credit p 0 F = F true := by
  simp [IterateCoin.credit, IterateCoin.bias, RealCoin.credit, RealCoin.pmf]

example : IterateCoin.credit 0 8 (fun b => if b then ∞ else 0) = 0 := by
  norm_num [IterateCoin.credit, IterateCoin.bias, RealCoin.credit, RealCoin.pmf]

example (p : unitInterval) (n : ℕ) : IterateCoin.credit p n (fun _ => ∞) = ∞ := by
  change RealCoin.credit (IterateCoin.bias p n) (fun _ => ∞) = ∞
  rw [← RealCoin.lintegral_law]
  simp [-Bool.univ_eq]

end

end LinearPowerWalkAuthorCallers

#print axioms SampLib.CurriedStep.twp_apply
#print axioms SampLib.CurriedStep.twp_fix_apply
#print axioms SampLib.LinearPowerWalk.Syntax.source_eq
#print axioms SampLib.AdaptivePowerWalk.expectation
#print axioms SampLib.LinearPowerWalk.twp_loop
#print axioms SampLib.LinearPowerWalk.linearPowerWalk_distSpec
