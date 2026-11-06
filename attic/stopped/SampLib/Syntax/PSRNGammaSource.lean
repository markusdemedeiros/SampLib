import SampLib.Syntax.PSRNGamma
import SampLib.Latent.LatentSpec

/-! # The guards and integer part of the rational-shape gamma constructor

After its positivity guard, the source computes the integer quotient and remainder,
constructs the integer part, and only then tests whether a fractional part remains.
-/

open ProbLang

namespace SampLib.PSRNGamma.Program

open scoped SampLib.PSRNGammaInteger.Program SampLib.PSRNGamma.Program

/-- The integer part: zero, or the integer-shape gamma constructor. -/
def integer {rT : Type} (w a b : ℤ) : Exp rT :=
  .cond (.binop .eq (.lit (.int w)) (.lit (.int 0)))
    (.app (.app Occil.PSRN.rational (.lit (.int 0))) (.lit (.int 1)))
    (.app (.app (.app Occil.PSRN.newGammaInteger (.lit (.int w))) (.lit (.int a)))
      (.lit (.int b)))

/-- The fractional branch before its complementary beta shape is evaluated. -/
def fraction {rT : Type} (r d a b : ℤ) : Exp rT :=
  .app (.lam
      (.app (.lam (.app (.app Occil.PSRN.add (.bvar 2))
        (.app (.app Occil.PSRN.multiply (.bvar 1)) (.bvar 0))))
        (.app (.app (.app Occil.PSRN.newExponential (.lit (.int a))) (.lit (.int b)))
          (.lit .unit))))
    (.app (.app (.app (.app (.app Occil.PSRN.newBeta (.lit (.int r))) (.lit (.int d)))
      (.binop .minus (.lit (.int d)) (.lit (.int r)))) (.lit (.int d))) (.lit .unit))

/-- The remainder test, with the integer part bound to `bvar 0`. -/
def remainderTest {rT : Type} (r d a b : ℤ) : Exp rT :=
  .cond (.binop .eq (.lit (.int r)) (.lit (.int 0))) (.bvar 0) (fraction r d a b)

private def le0 {rT : Type} (k : ℕ) : Exp rT := .binop .le (.bvar k) (.lit (.int 0))

private def code {rT : Type} : Exp rT :=
  .cond (.binop .or (.binop .or (.binop .or (le0 4) (le0 3)) (le0 2)) (le0 1)) .fail
    (.app (.lam (.app (.lam
      (.app (.lam
        (.cond (.binop .eq (.bvar 1) (.lit (.int 0))) (.bvar 0)
          (.app (.lam
              (.app (.lam (.app (.app Occil.PSRN.add (.bvar 2))
                (.app (.app Occil.PSRN.multiply (.bvar 1)) (.bvar 0))))
                (.app (.app (.app Occil.PSRN.newExponential (.bvar 6)) (.bvar 5))
                  (.lit .unit))))
            (.app (.app (.app (.app (.app Occil.PSRN.newBeta (.bvar 1)) (.bvar 6))
              (.binop .minus (.bvar 6) (.bvar 1))) (.bvar 6)) (.lit .unit)))))
        (.cond (.binop .eq (.bvar 1) (.lit (.int 0)))
          (.app (.app Occil.PSRN.rational (.lit (.int 0))) (.lit (.int 1)))
          (.app (.app (.app Occil.PSRN.newGammaInteger (.bvar 1)) (.bvar 4)) (.bvar 3)))))
      (.binop .mod (.bvar 5) (.bvar 4))))
      (.binop .div (.bvar 4) (.bvar 3)))

private theorem source_eq {rT : Type} :
    (Occil.PSRN.newGamma : Exp rT) = CurriedStep.lambdas 5 code := by
  kernel_rfl

private theorem int_beq {rT : Type} [BEq rT] (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = (a == b) := rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]
local bi (IProp GF)

/-- Positive parameters pass the guard; the quotient and remainder become literals. -/
theorem twp_open (E : CoPset) (sn sd rn rd : ℤ) (hsn : 0 < sn) (hsd : 0 < sd)
    (hrn : 0 < rn) (hrd : 0 < rd) (Φ : Val rT → IProp GF) :
    tglWp E (bind (integer (sn / sd) rn rd) (remainderTest (sn % sd) sd rn rd)) Φ ⊢
      tglWp E pl(&Occil.PSRN.newGamma #sn #sd #rn #rd #()) Φ := by
  have h := CurriedStep.twp_apply (GF := GF) E []
    [.int sn, .int sd, .int rn, .int rd, .unit] code (by kernel_rfl) Φ
  rw [source_eq]
  refine BI.BIBase.Entails.trans ?_ h
  simp only [CurriedStep.opened, code, Exp.openRec, le0, List.length_cons,
    List.length_nil, Ectx.fill, Nat.reduceAdd, Nat.zero_add, ↓reduceIte, Nat.reduceEqDiff,
    List.foldl_nil, ClosedExp.openRec, bind, integer, remainderTest, fraction]
  iintro H
  twp_pures
  rw [show (((decide (sn ≤ 0)).or (decide (sd ≤ 0))).or (decide (rn ≤ 0))).or
      (decide (rd ≤ 0)) = false by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_le]; omega]
  iterate 5 twp_pure
  isimp only [ClosedExp.openRec]
  iexact H

theorem twp_integer_zero (E : CoPset) (a b : ℤ) (Φ : Val rT → IProp GF) :
    tglWp E pl(&Occil.PSRN.rational #0 #1) Φ ⊢ tglWp E (integer 0 a b) Φ := by
  iintro H
  unfold integer
  twp_pure
  twp_pure
  iexact H

theorem twp_integer_pos (E : CoPset) (w a b : ℤ) (hw : w ≠ 0) (Φ : Val rT → IProp GF) :
    tglWp E pl(&Occil.PSRN.newGammaInteger #w #a #b) Φ ⊢ tglWp E (integer w a b) Φ := by
  iintro H
  unfold integer
  twp_pure
  rw [int_beq, beq_eq_false_iff_ne.mpr hw]
  twp_pure
  iexact H

/-- Without a fractional remainder, the integer part is returned unchanged. -/
theorem twp_remainder_zero (E : CoPset) (d a b : ℤ) (iv : Val rT) (Φ : Val rT → IProp GF) :
    Φ iv ⊢ tglWp E (bind (.ofVal iv) (remainderTest 0 d a b)) Φ := by
  iintro H
  unfold bind remainderTest
  twp_pure
  twp_pure
  twp_pure
  ieval (change _ ⊢ tglWp E (Exp.ofVal iv) _)
  iapply tglWp_value
  iexact H

/-- A nonzero remainder evaluates the complementary beta shape and enters the
fractional branch. -/
theorem twp_remainder_pos (E : CoPset) (r d a b : ℤ) (hr : r ≠ 0) (iv : Val rT)
    (Φ : Val rT → IProp GF) :
    tglWp E (bind (beta r d) (afterBeta a b iv)) Φ ⊢
      tglWp E (bind (.ofVal iv) (remainderTest r d a b)) Φ := by
  iintro H
  unfold bind remainderTest
  twp_pure
  twp_pure
  rw [int_beq, beq_eq_false_iff_ne.mpr hr]
  twp_pure
  isimp only [fraction, Exp.openRec, ClosedExp.openRec, ↓reduceIte]
  twp_pure
  isimp only [beta, afterBeta, exponential, bind] at H
  isimp only [Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte, Exp.ofVal]
  iexact H

end specification

end SampLib.PSRNGamma.Program
