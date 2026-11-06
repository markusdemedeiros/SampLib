import SampLib.Distributions.EulerHyperbolic
import SampLib.Samplers.EulerBounds
import SampLib.Syntax.Exponential

/-! # The factorial-enclosure coin for `(e-1)/(e+1)` -/

open ProbLang
open scoped SampLib.ExponentialTerms

namespace SampLib.TanhHalf

noncomputable section

@[pl_fold] private def boundsCode {rT : Type} : Exp rT := pl%
  fun n,
    let interval := &Occil.Constants.eBounds n;
    let lo := fst(interval);
    let hi := fst(snd(interval));
    let d := snd(snd(interval));
    ((lo - d) * (hi + d), ((hi - d) * (lo + d), (lo + d) * (hi + d)))

private def bounds {rT : Type} : Val rT := ⟨boundsCode, .lam (by is_lc), by is_lc⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_bounds (E : CoPset) (n : ℕ) :
    ⊢ tglWp E pl(&(bounds : Val rT).fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = FromBounds.encodeInterval (EulerHyperbolic.interval n)⌝)) := by
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
  rw [EulerHyperbolic.encode]
  rfl

/-- The original source bounds use the monotonicity of `(x-1)/(x+1)`. -/
theorem tanhHalf_distSpec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.Constants.tanhHalf #())
      (RealCoin.law EulerHyperbolic.bias) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    ieval (change _ ⊢ tglWp E pl(&Occil.Constants.fromBounds &bounds.fst #()) _)
    iapply ((FromBounds.fromBounds_distSpec E EulerHyperbolic.bias
      EulerHyperbolic.interval EulerHyperbolic.tight bounds (twp_bounds E)).spec F hF) $$ Hcredit

end specification

end

end SampLib.TanhHalf
