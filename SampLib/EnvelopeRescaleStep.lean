import SampLib.Syntax.EnvelopeFactory

/-! # The envelope source's exact rational rescaling

The deterministic stage preserves an arbitrary continuation. All nine fraction
operations follow the existing source order; only the old mean width must be positive.
-/

open ProbLang

namespace SampLib.EnvelopeFactory

open FactoryFractions

noncomputable section

def rescaledLower (lo hi lower oldLower oldUpper : Fraction) : Fraction :=
  .ofRat (lo.value + (lower.value - oldLower.value) *
    ((hi.value - lo.value) / (oldUpper.value - oldLower.value)))

def rescaledUpper (lo hi upper oldLower oldUpper : Fraction) : Fraction :=
  .ofRat (hi.value - (oldUpper.value - upper.value) *
    ((hi.value - lo.value) / (oldUpper.value - oldLower.value)))

private instance multiply_closed {rT : Type} :
    ClosedExp (Occil.FactoryExtra.multiplyFraction : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.FactoryExtra.multiplyFraction, Exp.fv, ClosedExp.closeRec, ClosedExp.fv]

private instance divide_closed {rT : Type} :
    ClosedExp (Occil.FactoryExtra.divideFraction : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.FactoryExtra.divideFraction, Exp.fv, ClosedExp.closeRec, ClosedExp.fv]

private instance less_closed {rT : Type} : ClosedExp (Occil.uniformBagLess : Exp rT) where
  lc := UniformBag.uniformBagLess_lc
  fv := UniformBag.uniformBagLess_fv

attribute [local irreducible] FactoryFractions.encode

private def afterRescaleRat {rT : Type} (self : Val rT) (l : Loc) (degree heads : ℕ)
    (lower upper : ℚ) : Exp rT :=
  Program.afterRescaleCode (fun _ => self.fst) (fun _ => (Val.loc l).fst)
    (fun _ => pl(#int (degree : ℤ))) (fun _ => pl(#int (heads : ℤ)))
    (fun _ => (encode lower).fst) (fun _ => (encode upper).fst)

private theorem afterRescaleRat_eq {rT : Type} (self : Val rT) (l : Loc) (degree heads : ℕ)
    (lower upper : ℚ) :
    afterRescaleRat self l degree heads lower upper =
      Program.afterRescale self l degree heads (.ofRat lower) (.ofRat upper) := by
  simp only [afterRescaleRat, Program.afterRescale, Fraction.encode_ofRat]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec ProbLang.openRec_val_fst

private theorem twp_multiplyRat (E : CoPset) (a b : ℚ) :
    ⊢ tglWp E pl(&Occil.FactoryExtra.multiplyFraction &(encode a : Val rT).fst
      &(encode b : Val rT).fst) (fun v : Val rT => iprop(⌜v = encode (a * b)⌝)) := by
  simpa only [Fraction.encode_ofRat, Fraction.value_ofRat] using
    twp_multiplyFraction (rT := rT) (GF := GF) E (.ofRat a) (.ofRat b)

private theorem twp_divideRat (E : CoPset) (a b : ℚ) (hb : 0 < b) :
    ⊢ tglWp E pl(&Occil.FactoryExtra.divideFraction &(encode a : Val rT).fst
      &(encode b : Val rT).fst) (fun v : Val rT => iprop(⌜v = encode (a / b)⌝)) := by
  simpa only [Fraction.encode_ofRat, Fraction.value_ofRat] using
    twp_divideFraction (rT := rT) (GF := GF) E (.ofRat a) (.ofRat b) (Rat.num_pos.mpr hb)

private theorem twp_addRat (E : CoPset) (a : Fraction) (b : ℚ) :
    ⊢ tglWp E pl(&Occil.FactoryExtra.addFraction &a.encode.fst &(encode b : Val rT).fst)
      (fun v : Val rT => iprop(⌜v = encode (a.value + b)⌝)) := by
  simpa only [Fraction.encode_ofRat, Fraction.value_ofRat] using
    twp_addFraction (rT := rT) (GF := GF) E a (.ofRat b)

private theorem twp_subtractRat (E : CoPset) (a : Fraction) (b : ℚ) :
    ⊢ tglWp E pl(&Occil.FactoryExtra.subtractFraction &a.encode.fst &(encode b : Val rT).fst)
      (fun v : Val rT => iprop(⌜v = encode (a.value - b)⌝)) := by
  simpa only [Fraction.encode_ofRat, Fraction.value_ofRat] using
    twp_subtractFraction (rT := rT) (GF := GF) E a (.ofRat b)

/-- Execute the nine source operations, leaving the comparison continuation untouched. -/
theorem twp_rescale (E : CoPset) (self : Val rT) (l : Loc) (degree heads : ℕ)
    (lo hi lower upper oldLower oldUpper : Fraction)
    (hwidth : 0 < oldUpper.value - oldLower.value) (Φ : Val rT → IProp GF) :
    tglWp E (Program.afterRescale self l degree heads
      (rescaledLower lo hi lower oldLower oldUpper)
      (rescaledUpper lo hi upper oldLower oldUpper)) Φ ⊢
      tglWp E (Program.afterConditional self l degree heads
        lo hi lower upper oldLower oldUpper) Φ := by
  let remaining := hi.value - lo.value
  let width := oldUpper.value - oldLower.value
  let factor := remaining / width
  let lowerGap := lower.value - oldLower.value
  let upperGap := oldUpper.value - upper.value
  iintro H
  isimp only [rescaledLower, rescaledUpper, ← afterRescaleRat_eq] at H
  unfold Program.afterConditional Program.afterConditionalCode Program.afterRescaleCode
  twp_bind pl(&Occil.FactoryExtra.subtractFraction &hi.encode.fst &lo.encode.fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_subtractFraction E hi lo
  iintro %v %hv
  subst v
  twp_pure
  twp_bind pl(&Occil.FactoryExtra.subtractFraction &oldUpper.encode.fst &oldLower.encode.fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_subtractFraction E oldUpper oldLower
  iintro %v %hv
  subst v
  twp_pure
  twp_bind pl(&Occil.FactoryExtra.divideFraction &(encode remaining : Val rT).fst
    &(encode width : Val rT).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_divideRat E remaining width hwidth
  iintro %v %hv
  subst v
  twp_pure
  twp_bind pl(&Occil.FactoryExtra.subtractFraction &lower.encode.fst &oldLower.encode.fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_subtractFraction E lower oldLower
  iintro %v %hv
  subst v
  twp_pure
  twp_bind pl(&Occil.FactoryExtra.subtractFraction &oldUpper.encode.fst &upper.encode.fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_subtractFraction E oldUpper upper
  iintro %v %hv
  subst v
  twp_pure
  twp_bind pl(&Occil.FactoryExtra.multiplyFraction &(encode lowerGap : Val rT).fst
    &(encode factor : Val rT).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_multiplyRat E lowerGap factor
  iintro %v %hv
  subst v
  twp_bind pl(&Occil.FactoryExtra.addFraction &lo.encode.fst
    &(encode (lowerGap * factor) : Val rT).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_addRat E lo (lowerGap * factor)
  iintro %v %hv
  subst v
  twp_pure
  twp_bind pl(&Occil.FactoryExtra.multiplyFraction &(encode upperGap : Val rT).fst
    &(encode factor : Val rT).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_multiplyRat E upperGap factor
  iintro %v %hv
  subst v
  twp_bind pl(&Occil.FactoryExtra.subtractFraction &hi.encode.fst
    &(encode (upperGap * factor) : Val rT).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_subtractRat E hi (upperGap * factor)
  iintro %v %hv
  subst v
  twp_pure
  ieval (change _ ⊢ tglWp E (afterRescaleRat self l degree heads
    (lo.value + lowerGap * factor) (hi.value - upperGap * factor)) Φ)
  iexact H

end specification

end

end SampLib.EnvelopeFactory
