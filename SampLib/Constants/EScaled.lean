import SampLib.Bernoulli.EulerBounds
import SampLib.Bernoulli.Laws.RationalEnclosureScale
import SampLib.Bernoulli.Syntax.Exponential

/-! # Exact rational multiples of Euler's number -/

open ProbLang
open scoped SampLib.ExponentialTerms

namespace SampLib.EScaled

noncomputable section

def bias (u v : ℕ) (h : Real.exp 1 * u / v ≤ 1) : unitInterval :=
  ⟨Real.exp 1 * u / v, ⟨by positivity, h⟩⟩

private def enclosures (u v : ℕ) (hv : 0 < v)
    (h : Real.exp 1 * u / v ≤ 1) (n : ℕ) : FromBounds.Interval (bias u v h) :=
  ((EulerEnclosure.interval n).scale u v hv).toProbability (bias u v h) rfl

@[pl_fold] private def boundsCode {rT : Type} (u v : ℕ) : Exp rT := pl%
  fun n,
    let interval := &Occil.Constants.eBounds n;
    let low := fst(interval);
    let high := fst(snd(interval));
    let d := snd(snd(interval));
    (#int (u : ℤ) * low, (#int (u : ℤ) * high, #int (v : ℤ) * d))

private def bounds {rT : Type} (u v : ℕ) : Val rT :=
  ⟨boundsCode u v, by unfold boundsCode; exact .lam (by is_lc), by is_lc⟩

private theorem guard (v : ℕ) (hv : 0 < v) :
    (false || decide ((v : ℤ) ≤ 0)) = false := by
  simp only [Bool.false_or]
  exact decide_eq_false (by omega)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_bounds (E : CoPset) (u v : ℕ) (hv : 0 < v)
    (h : Real.exp 1 * u / v ≤ 1) (n : ℕ) :
    ⊢ tglWp E pl(&(bounds u v : Val rT).fst #int (n : ℤ))
      (fun w : Val rT => iprop(⌜w = FromBounds.encodeInterval (enclosures u v hv h n)⌝)) := by
  twp_pure
  twp_bind pl(&Occil.Constants.eBounds #int (n : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply EulerEnclosure.twp_eBounds E n
  iintro %w %hw
  subst w
  twp_pures
  twp_value
  imodintro
  ipureintro
  apply Val.ext
  simp [enclosures, FromBounds.encodeInterval, RealEnclosure.Interval.toProbability,
    RealEnclosure.Interval.scale, RealEnclosure.Interval.triple, Exp.ofVal]

/-- All nonnegative rational scales whose product with `exp 1` is a probability. -/
theorem eScaled_distSpec (E : CoPset) (u v : ℕ) (hv : 0 < v)
    (h : Real.exp 1 * u / v ≤ 1) :
    IsDistSpec (GF := GF) E pl(&Occil.Constants.eScaled #int (u : ℤ) #int (v : ℤ) #())
      (RealCoin.law (bias u v h)) Val.bool where
  spec F hF := by
    iintro Hcredit
    iterate 3 twp_pure
    twp_pures
    rw [guard v hv]
    twp_pure
    ieval (change _ ⊢ tglWp E pl(&Occil.Constants.fromBounds &(bounds u v).fst #()) _)
    iapply ((FromBounds.fromBounds_distSpec E (bias u v h) (enclosures u v hv h)
      ((EulerEnclosure.tight.scale u v hv).toProbability (bias u v h) rfl)
      (bounds u v) (twp_bounds E u v hv h)).spec F hF) $$ Hcredit

end specification

end

end SampLib.EScaled
