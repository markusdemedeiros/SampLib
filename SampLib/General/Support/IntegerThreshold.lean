import SampLib.Uniform.UniformInt
import SampLib.Uniform.RationalCoin
import SampLib.General.Laws.IntegerThreshold

/-! # Integer threshold coin specification -/

open ProbLang
open scoped ENNReal

namespace SampLib.IntegerThreshold

noncomputable section

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The comparison samples even at deterministic endpoint thresholds. -/
theorem twp_threshold (E : CoPset) (a b : ℕ) (hb : 0 < b) (hab : a ≤ b)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (bias a b hb hab) F) -∗
      tglWp E pl(&Occil.uniformInt #int (b : ℤ) < #int (a : ℤ))
        (fun v : Val rT => iprop(∃ r : Bool, ⌜v = Val.bool r⌝ ∗ ↯ (F r))) := by
  iintro Hcredit
  twp_bind pl(&Occil.uniformInt #int (b : ℤ))
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply UniformInt.twp_uniformInt E b hb (RationalCoin.rankCredit a F)
    rw [expectation a b hb hab F]
    iexact Hcredit
  iintro %v ⟨%k, %hv, %hk, Hcredit⟩
  subst v
  twp_pures
  twp_value
  imodintro
  iexists decide ((k : ℤ) < (a : ℤ))
  isimp only [rankCredit_eq] at Hcredit
  iframe Hcredit
  ipureintro
  rfl

/-- Supporting typed Bernoulli specification for a bounded integer threshold. -/
theorem threshold_distSpec (E : CoPset) (a b : ℕ) (hb : 0 < b) (hab : a ≤ b) :
    IsDistSpec (GF := GF) E pl(&Occil.uniformInt #int (b : ℤ) < #int (a : ℤ))
      (RealCoin.law (bias a b hb hab)) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law] using
      wand_entails (twp_threshold E a b hb hab F)

end specification

end

end SampLib.IntegerThreshold
