import SampLib.Constants.Laws.EulerPi
import SampLib.Bernoulli.EulerBounds
import SampLib.Bernoulli.Support.PiBounds
import Samplers.Constants.Special

/-! # Exact sampling at Euler's number divided by pi -/

open ProbLang

namespace SampLib.EulerPi

noncomputable section

private instance eBounds_closed {rT : Type} :
    ClosedExp (Occil.Constants.eBounds : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.Constants.eBounds, Exp.fv]

private instance piBounds_closed {rT : Type} :
    ClosedExp (Occil.Constants.piBounds : Exp rT) where
  lc := PiBounds.piBounds_lc
  fv := PiBounds.piBounds_fv

private instance fromBounds_closed {rT : Type} :
    ClosedExp (Occil.Constants.fromBounds : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.Constants.fromBounds, Occil.newUniformBag, Exp.fv,
    UniformBag.uniformBagLess_fv]

private def enclosures (n : ℕ) : FromBounds.Interval bias :=
  (interval n).toProbability bias rfl

@[pl_fold] private def boundsCode {rT : Type} : Exp rT := pl%
  fun n,
    let e := &Occil.Constants.eBounds n;
    let p := &Occil.Constants.piBounds n;
    let eLow := fst(e);
    let eHigh := fst(snd(e));
    let eDenominator := snd(snd(e));
    let pLow := fst(p);
    let pHigh := fst(snd(p));
    let pDenominator := snd(snd(p));
    (eLow * pDenominator * pLow,
      (eHigh * pDenominator * pHigh, eDenominator * pLow * pHigh))

private def bounds {rT : Type} : Val rT :=
  ⟨boundsCode, by unfold boundsCode; exact .lam (by is_lc), by is_lc⟩

private instance bounds_closed {rT : Type} : ClosedExp (bounds (rT := rT)).fst where
  lc := bounds.lc
  fv := by simp [bounds, boundsCode, Exp.fv, Occil.Constants.eBounds, PiBounds.piBounds_fv]

private theorem source_eq {rT : Type} :
    (Occil.Constants.eOverPi : Exp rT) =
      pl(fun u, &Occil.Constants.fromBounds &bounds.fst #()) := by
  kernel_rfl

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
      (fun v : Val rT => iprop(⌜v = FromBounds.encodeInterval (enclosures n)⌝)) := by
  twp_pure
  twp_bind pl(&Occil.Constants.eBounds #int (n : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply EulerEnclosure.twp_eBounds E n
  iintro %v %hv
  subst v
  twp_pure
  twp_bind pl(&Occil.Constants.piBounds #int (n : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply PiBounds.twp_piBounds E n
  iintro %v %hv
  subst v
  twp_pures
  twp_value
  imodintro
  ipureintro
  apply Val.ext
  change _ = (RealEnclosure.encodeInterval (interval n) : Val rT).fst
  rw [RealEnclosure.encodeInterval, interval_triple, ← PiBounds.interval_triple]
  rfl

/-- The actual factorial and Machin oracles enclose the canonical ratio `exp 1 / pi`. -/
theorem eOverPi_distSpec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.Constants.eOverPi #())
      (RealCoin.law bias) Val.bool where
  spec F hF := by
    rw [source_eq]
    iintro Hcredit
    twp_pure
    iapply ((FromBounds.fromBounds_distSpec E bias enclosures
      (tight.toProbability bias rfl) bounds (twp_bounds E)).spec F hF) $$ Hcredit

end specification

end

end SampLib.EulerPi
