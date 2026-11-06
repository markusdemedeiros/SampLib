import SampLib.Distributions.ReciprocalPiProbability
import SampLib.PiBounds
import SampLib.Syntax.ClosedExp

/-! # Exact scaled reciprocal probabilities in π -/

open ProbLang
open scoped ENNReal

namespace SampLib.ReciprocalPiScaled

noncomputable section

private instance piBounds_closed {rT : Type} :
    ClosedExp (Occil.Constants.piBounds : Exp rT) where
  lc := PiBounds.piBounds_lc
  fv := PiBounds.piBounds_fv

private instance fromBounds_closed {rT : Type} :
    ClosedExp (Occil.Constants.fromBounds : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.Constants.fromBounds, Occil.newUniformBag, Exp.fv,
    UniformBag.uniformBagLess_fv]

@[pl_fold] private def boundsCode {rT : Type} (numerator denominator : ℕ) : Exp rT := pl%
  fun n,
    let interval := &Occil.Constants.piBounds n;
    let lo := fst(interval);
    let hi := fst(snd(interval));
    let d := snd(snd(interval));
    (#int (numerator : ℤ) * d * lo,
      (#int (numerator : ℤ) * d * hi, #int (denominator : ℤ) * lo * hi))

private def bounds {rT : Type} (numerator denominator : ℕ) : Val rT :=
  ⟨boundsCode numerator denominator,
    by unfold boundsCode; exact .lam (by is_lc), by is_lc⟩

private theorem parameter_test (denominator : ℕ) (hd : 0 < denominator) :
    (false || decide ((denominator : ℤ) ≤ 0)) = false := by
  simp; omega

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_bounds (E : CoPset) (numerator denominator : ℕ) (hd : 0 < denominator)
    (hp : (numerator : ℝ) ≤ denominator * Real.pi) (n : ℕ) :
    ⊢ tglWp E pl(&(bounds numerator denominator : Val rT).fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = FromBounds.encodeInterval
        (ReciprocalPiProbability.interval numerator denominator hd hp n)⌝)) := by
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
  rw [ReciprocalPiProbability.encode]
  rfl

/-- The zero numerator and every positive denominator in the probability domain are admitted. -/
theorem twp_reciprocalPiScaled (E : CoPset) (numerator denominator : ℕ) (hd : 0 < denominator)
    (hp : (numerator : ℝ) ≤ denominator * Real.pi)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (ReciprocalPiProbability.bias numerator denominator hd hp) F) -∗
      tglWp E
        pl(&Occil.Constants.reciprocalPiScaled #int (numerator : ℤ) #int (denominator : ℤ) #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  have hsample := FromBounds.twp_fromBounds (rT := rT) (GF := GF) E _ _
    (ReciprocalPiProbability.tight numerator denominator hd hp) (bounds numerator denominator)
    (twp_bounds E numerator denominator hd hp) F
  simp [bounds, boundsCode, Exp.close, Exp.closeRec,
    ClosedExp.closeRec, Var.internal.injEq] at hsample
  iintro Hcredit
  iterate 6 twp_pure
  rw [parameter_test denominator hd]
  twp_pure
  iapply hsample
  iexact Hcredit

theorem reciprocalPiScaled_distSpec (E : CoPset) (numerator denominator : ℕ) (hd : 0 < denominator)
    (hp : (numerator : ℝ) ≤ denominator * Real.pi) :
    IsDistSpec (GF := GF) E
      pl(&Occil.Constants.reciprocalPiScaled #int (numerator : ℤ) #int (denominator : ℤ) #())
      (RealCoin.law (ReciprocalPiProbability.bias numerator denominator hd hp)) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law] using
      wand_entails (twp_reciprocalPiScaled E numerator denominator hd hp F)

end specification

end

end SampLib.ReciprocalPiScaled
