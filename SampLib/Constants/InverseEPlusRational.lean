import SampLib.Constants.Laws.EulerReciprocal
import SampLib.Bernoulli.EulerBounds
import SampLib.Bernoulli.Syntax.Exponential

/-! # The shifted reciprocal of Euler's number on the full rational source domain -/

open ProbLang
open scoped SampLib.ExponentialTerms

namespace SampLib.InverseEPlusRational

noncomputable section

def bias (a b : ℕ) (hb : 0 < b) (hab : b ≤ a) : unitInterval :=
  ⟨1 / EulerReciprocal.center a b, ⟨by
    have h := EulerReciprocal.center_ge_one a b hb hab
    positivity, by
    simpa only [div_one] using one_div_le_one_div_of_le zero_lt_one
      (EulerReciprocal.center_ge_one a b hb hab)⟩⟩

private def enclosures (a b : ℕ) (hb : 0 < b) (hab : b ≤ a) (n : ℕ) :
    FromBounds.Interval (bias a b hb hab) :=
  (EulerReciprocal.interval a b hb hab n).toProbability (bias a b hb hab) rfl

private theorem encode_enclosures {rT : Type} (a b : ℕ) (hb : 0 < b)
    (hab : b ≤ a) (n : ℕ) :
    FromBounds.encodeInterval (rT := rT) (enclosures a b hb hab n) =
      RealEnclosure.encodeTriple
        ((b : ℤ) * (EulerEnclosure.interval n).denominator * EulerReciprocal.low a b n,
          ((b : ℤ) * (EulerEnclosure.interval n).denominator * EulerReciprocal.high a b n,
            EulerReciprocal.low a b n * EulerReciprocal.high a b n)) := by
  change RealEnclosure.encodeInterval (EulerReciprocal.interval a b hb hab n) = _
  rw [RealEnclosure.encodeInterval, EulerReciprocal.triple_eq]

@[pl_fold] private def boundsCode {rT : Type} (a b : ℕ) : Exp rT := pl%
  fun n,
    let interval := &Occil.Constants.eBounds n;
    let d := snd(snd(interval));
    let lo := fst(interval) * #int (b : ℤ) + (#int (a : ℤ) - #2 * #int (b : ℤ)) * d;
    let hi := fst(snd(interval)) * #int (b : ℤ) + (#int (a : ℤ) - #2 * #int (b : ℤ)) * d;
    (#int (b : ℤ) * d * lo, (#int (b : ℤ) * d * hi, lo * hi))

private def bounds {rT : Type} (a b : ℕ) : Val rT :=
  ⟨boundsCode a b, by unfold boundsCode; exact .lam (by is_lc), by is_lc⟩

private theorem guard (a b : ℕ) (hb : 0 < b) (hab : b ≤ a) :
    (decide ((b : ℤ) ≤ 0) || decide ((a : ℤ) < b)) = false := by
  simp [hb.ne', show ¬(a : ℤ) < b by omega]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_bounds (E : CoPset) (a b : ℕ) (hb : 0 < b) (hab : b ≤ a) (n : ℕ) :
    ⊢ tglWp E pl(&(bounds a b : Val rT).fst #int (n : ℤ))
      (fun w : Val rT => iprop(⌜w = FromBounds.encodeInterval (enclosures a b hb hab n)⌝)) := by
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
  rw [encode_enclosures]
  apply Val.ext
  simp [RealEnclosure.encodeTriple, RealEnclosure.Interval.triple,
    EulerReciprocal.low, EulerReciprocal.high, Exp.ofVal]

/-- Exact `1 / (exp 1 + a/b - 2)` for all `a ≥ b > 0`, including `a=b`. -/
theorem inverseEPlusRational_distSpec (E : CoPset) (a b : ℕ) (hb : 0 < b) (hab : b ≤ a) :
    IsDistSpec (GF := GF) E
      pl(&Occil.Constants.inverseEPlusRational #int (a : ℤ) #int (b : ℤ) #())
      (RealCoin.law (bias a b hb hab)) Val.bool where
  spec F hF := by
    iintro Hcredit
    iterate 3 twp_pure
    twp_pures
    rw [guard a b hb hab]
    twp_pure
    ieval (change _ ⊢ tglWp E pl(&Occil.Constants.fromBounds &(bounds a b).fst #()) _)
    iapply ((FromBounds.fromBounds_distSpec E (bias a b hb hab) (enclosures a b hb hab)
      ((EulerReciprocal.tight a b hb hab).toProbability (bias a b hb hab) rfl)
      (bounds a b) (twp_bounds E a b hb hab)).spec F hF) $$ Hcredit

end specification

end

end SampLib.InverseEPlusRational
