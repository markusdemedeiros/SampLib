import SampLib.Constants.FromBounds
import SampLib.Bernoulli.Support.PiEncodings
import SampLib.Bernoulli.Support.PiBounds
import SampLib.Core.Syntax.ClosedExp

/-! # Exact affine probabilities in π -/

open ProbLang
open scoped ENNReal

namespace SampLib.PiAffine

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

@[pl_fold] private def boundsCode {rT : Type} (offset : ℤ) (divisor : ℕ) : Exp rT := pl%
  fun n,
    let interval := &Occil.Constants.piBounds n;
    let d := snd(snd(interval));
    (fst(interval) - #int offset * d,
      (fst(snd(interval)) - #int offset * d, #int (divisor : ℤ) * d))

private def bounds {rT : Type} (offset : ℤ) (divisor : ℕ) : Val rT :=
  ⟨boundsCode offset divisor, by unfold boundsCode; exact .lam (by is_lc), by is_lc⟩

private theorem divisor_test (divisor : ℕ) (hd : 0 < divisor) :
    decide ((divisor : ℤ) ≤ 0) = false := by simp; omega

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_bounds (E : CoPset) (offset : ℤ) (divisor : ℕ) (hd : 0 < divisor)
    (hlo : 0 ≤ Real.pi - offset) (hhi : Real.pi - offset ≤ divisor) (n : ℕ) :
    ⊢ tglWp E pl(&(bounds offset divisor : Val rT).fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = FromBounds.encodeInterval
        (PiProbability.affineInterval offset divisor hd hlo hhi n)⌝)) := by
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
  rw [PiProbability.affine_encode]
  rfl

/-- Arbitrary signed offsets are admitted whenever the resulting ratio lies in `[0,1]`. -/
theorem twp_piAffine (E : CoPset) (offset : ℤ) (divisor : ℕ) (hd : 0 < divisor)
    (hlo : 0 ≤ Real.pi - offset) (hhi : Real.pi - offset ≤ divisor)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (PiProbability.affineBias offset divisor hd hlo hhi) F) -∗
      tglWp E pl(&Occil.Constants.piAffine #int offset #int (divisor : ℤ) #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  have hsample := FromBounds.twp_fromBounds (rT := rT) (GF := GF) E _ _
    (PiProbability.affine_tight offset divisor hd hlo hhi) (bounds offset divisor)
    (twp_bounds E offset divisor hd hlo hhi) F
  simp [bounds, boundsCode, Exp.close, Exp.closeRec,
    ClosedExp.closeRec, Var.internal.injEq] at hsample
  iintro Hcredit
  iterate 4 twp_pure
  rw [divisor_test divisor hd]
  twp_pure
  iapply hsample
  iexact Hcredit

theorem piAffine_distSpec (E : CoPset) (offset : ℤ) (divisor : ℕ) (hd : 0 < divisor)
    (hlo : 0 ≤ Real.pi - offset) (hhi : Real.pi - offset ≤ divisor) :
    IsDistSpec (GF := GF) E
      pl(&Occil.Constants.piAffine #int offset #int (divisor : ℤ) #())
      (RealCoin.law (PiProbability.affineBias offset divisor hd hlo hhi)) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law] using
      wand_entails (twp_piAffine E offset divisor hd hlo hhi F)

end specification

end

end SampLib.PiAffine
