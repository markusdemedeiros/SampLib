import SampLib.Samplers.InverseEPlusRational

/-! # The integer-shifted reciprocal of Euler's number -/

open ProbLang
open scoped SampLib.ExponentialTerms

namespace SampLib.InverseEPlus

noncomputable section

abbrev bias (c : ℕ) (hc : 1 ≤ c) : unitInterval :=
  InverseEPlusRational.bias c 1 (by decide) hc

private def enclosures (c : ℕ) (hc : 1 ≤ c) (n : ℕ) : FromBounds.Interval (bias c hc) :=
  (EulerReciprocal.interval c 1 (by decide) hc n).toProbability _ rfl

@[pl_fold] private def boundsCode {rT : Type} (c : ℕ) : Exp rT := pl%
  fun n,
    let interval := &Occil.Constants.eBounds n;
    let d := snd(snd(interval));
    let lo := fst(interval) + (#int (c : ℤ) - #2) * d;
    let hi := fst(snd(interval)) + (#int (c : ℤ) - #2) * d;
    (d * lo, (d * hi, lo * hi))

private def bounds {rT : Type} (c : ℕ) : Val rT :=
  ⟨boundsCode c, .lam (by is_lc), by is_lc⟩

private theorem guard (c : ℕ) (hc : 1 ≤ c) :
    decide ((c : ℤ) < 1) = false := by simp; omega

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_bounds (E : CoPset) (c : ℕ) (hc : 1 ≤ c) (n : ℕ) :
    ⊢ tglWp E pl(&(bounds c : Val rT).fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = FromBounds.encodeInterval (enclosures c hc n)⌝)) := by
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
  change _ = RealEnclosure.encodeInterval (EulerReciprocal.interval c 1 (by decide) hc n)
  rw [RealEnclosure.encodeInterval, EulerReciprocal.triple_eq]
  simp only [EulerReciprocal.low, EulerReciprocal.high, Nat.cast_one, mul_one, one_mul]
  rfl

/-- All positive integer shifts, including the initial `1/(e-1)` case. -/
theorem inverseEPlus_distSpec (E : CoPset) (c : ℕ) (hc : 1 ≤ c) :
    IsDistSpec (GF := GF) E pl(&Occil.Constants.inverseEPlus #int (c : ℤ) #())
      (RealCoin.law (bias c hc)) Val.bool where
  spec F hF := by
    iintro Hcredit
    iterate 2 twp_pure
    twp_pures
    rw [guard c hc]
    twp_pure
    ieval (change _ ⊢ tglWp E pl(&Occil.Constants.fromBounds &(bounds c).fst #()) _)
    iapply ((FromBounds.fromBounds_distSpec E (bias c hc) (enclosures c hc)
      ((EulerReciprocal.tight c 1 (by decide) hc).toProbability _ rfl)
      (bounds c) (twp_bounds E c hc)).spec F hF) $$ Hcredit

end specification

end

end SampLib.InverseEPlus
