import SampLib.Distributions.EulerConstants
import SampLib.Samplers.EulerBounds
import SampLib.Syntax.Exponential

/-! # Exact affine and fractional-linear coins in Euler's number -/

open ProbLang
open scoped SampLib.ExponentialTerms

namespace SampLib.EulerAffineConstants

noncomputable section

@[pl_fold] private def minusTwoCode {rT : Type} : Exp rT := pl%
  fun n,
    let interval := &Occil.Constants.eBounds n;
    let d := snd(snd(interval));
    ((fst(interval)) - #2 * d, (fst(snd(interval)) - #2 * d, d))

private def minusTwoBounds {rT : Type} : Val rT :=
  ⟨minusTwoCode, .lam (by is_lc), by is_lc⟩

@[pl_fold] private def threeMinusCode {rT : Type} : Exp rT := pl%
  fun n,
    let interval := &Occil.Constants.eBounds n;
    let d := snd(snd(interval));
    (#3 * d - fst(snd(interval)), (#3 * d - (fst(interval)), d))

private def threeMinusBounds {rT : Type} : Val rT :=
  ⟨threeMinusCode, .lam (by is_lc), by is_lc⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_minusTwoBounds (E : CoPset) (n : ℕ) :
    ⊢ tglWp E pl(&(minusTwoBounds : Val rT).fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = FromBounds.encodeInterval
        (EulerConstants.minusTwoInterval n)⌝)) := by
  twp_pure
  twp_bind pl(&Occil.Constants.eBounds #int (n : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply EulerEnclosure.twp_eBounds E n
  iintro %v %hv
  subst v
  twp_pures
  twp_value
  imodintro
  ipureintro
  rw [EulerConstants.minusTwo_encode]
  rfl

/-- The source's factorial bounds converge to the advertised probability. -/
theorem eMinusTwo_distSpec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.Constants.eMinusTwo #())
      (RealCoin.law EulerConstants.minusTwo) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    ieval (change _ ⊢ tglWp E pl(&Occil.Constants.fromBounds &minusTwoBounds.fst #()) _)
    iapply ((FromBounds.fromBounds_distSpec E EulerConstants.minusTwo
      EulerConstants.minusTwoInterval EulerConstants.minusTwo_tight
      minusTwoBounds (twp_minusTwoBounds E)).spec F hF) $$ Hcredit

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_threeMinusBounds (E : CoPset) (n : ℕ) :
    ⊢ tglWp E pl(&(threeMinusBounds : Val rT).fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = FromBounds.encodeInterval
        (EulerConstants.threeMinusInterval n)⌝)) := by
  twp_pure
  twp_bind pl(&Occil.Constants.eBounds #int (n : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply EulerEnclosure.twp_eBounds E n
  iintro %v %hv
  subst v
  twp_pures
  twp_value
  imodintro
  ipureintro
  rw [EulerConstants.threeMinus_encode]
  rfl

/-- The source's factorial bounds converge to the advertised probability. -/
theorem threeMinusE_distSpec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.Constants.threeMinusE #())
      (RealCoin.law EulerConstants.threeMinus) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    ieval (change _ ⊢ tglWp E pl(&Occil.Constants.fromBounds &threeMinusBounds.fst #()) _)
    iapply ((FromBounds.fromBounds_distSpec E EulerConstants.threeMinus
      EulerConstants.threeMinusInterval EulerConstants.threeMinus_tight
      threeMinusBounds (twp_threeMinusBounds E)).spec F hF) $$ Hcredit

end specification

end

end SampLib.EulerAffineConstants
