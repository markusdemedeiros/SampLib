import Samplers.Bernoulli.Polynomials
import SampLib.Bernoulli.Support.PolynomialFactoryData
import SampLib.Core.ListEncoding
import SampLib.Core.Syntax.ClosedExp
import SampLib.Bernoulli.Support.FactoryChoose
import SampLib.Core.Syntax.ListAccess
import SampLib.Core.Syntax.ListValues

/-! Named source continuations for the polynomial factory's deterministic phases. -/

open ProbLang

namespace SampLib.PolynomialFactory.Syntax

open FactoryFractions

variable {rT : Type _} [ProbLangℝ rT]

@[simp] theorem fractionList_fv (xs : List Fraction) :
    (listVal (Fraction.encode (rT := rT)) xs).fst.fv = ∅ :=
  ListValues.listVal_fv _ xs (fun _ _ => rfl)

@[simp] theorem fractionList_closeRec (xs : List Fraction) (k : ℕ) (x : Var) :
    Exp.closeRec k x (listVal (Fraction.encode (rT := rT)) xs).fst =
      (listVal Fraction.encode xs).fst :=
  Exp.closeRec_fresh x _ k
    (by rw [ListValues.listVal_fv (Fraction.encode (rT := rT)) xs (fun _ _ => rfl)]; simp)

instance multiplyFraction_closed : ClosedExp (Occil.FactoryExtra.multiplyFraction : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.FactoryExtra.multiplyFraction, Exp.fv, ClosedExp.closeRec, ClosedExp.fv]


def terms (xs : List Fraction) (n k : ℕ) : Exp rT := pl%
  rec terms j value :=
    if (#int (degree xs : ℤ) < j) || (#int (k : ℤ) < j) then value else
      let a := &Occil.getAt &(listVal (Fraction.encode (rT := rT)) xs).fst j;
      let numerator := &Occil.FactoryExtra.choose #int (k : ℤ) j;
      let denominator := &Occil.FactoryExtra.choose #int (n : ℤ) j;
      let term := &Occil.FactoryExtra.multiplyFraction a (numerator, denominator);
      terms (j + #1) (&Occil.FactoryExtra.addFraction value term)

def coefficient (xs : List Fraction) (n : ℕ) : Exp rT := pl%
  fun k,
    let sum := (rec terms j value :=
      if (#int (degree xs : ℤ) < j) || (k < j) then value else
        let a := &Occil.getAt &(listVal (Fraction.encode (rT := rT)) xs).fst j;
        let numerator := &Occil.FactoryExtra.choose k j;
        let denominator := &Occil.FactoryExtra.choose #int (n : ℤ) j;
        let term := &Occil.FactoryExtra.multiplyFraction a (numerator, denominator);
        terms (j + #1) (&Occil.FactoryExtra.addFraction value term));
    sum #0 (#0, #1)

instance coefficient_closed (xs : List Fraction) (n : ℕ) :
    ClosedExp (coefficient (rT := rT) xs n) where
  lc := by is_lc
  fv := by simp [coefficient, Exp.fv, ClosedExp.closeRec, ClosedExp.fv,
    ListAccess.getAt_closeRec, ListAccess.getAt_fv, FactoryChoose.choose_closeRec,
    FactoryChoose.choose_fv]

def collect (xs : List Fraction) (n : ℕ) : Exp rT := pl%
  rec collect k :=
    if #int (n : ℤ) < k then inl(#())
    else inr(((&(coefficient xs n)) k, collect (k + #1)))

/-- The small collection loop, keeping its verified coefficient function opaque. -/
def collectBody (xs : List Fraction) (n : ℕ) : Exp rT :=
  .cond (.binop .lt (.lit (.int n)) (.bvar 0)) (.inl (.lit .unit))
    (.inr (.pair (.app (coefficient xs n) (.bvar 0))
      (.app (.bvar 1) (.binop .plus (.bvar 0) (.lit (.int 1))))))

def collectCode (xs : List Fraction) (n : ℕ) : Exp rT := .fix (.lam (collectBody xs n))

theorem collect_eq (xs : List Fraction) (n : ℕ) :
    (collect xs n : Exp rT) = collectCode xs n := by
  simp [collect, collectCode, collectBody, Exp.close, Exp.closeRec, ClosedExp.closeRec]

def check : Exp rT := pl%
  rec check xs := case! xs
    | inl(v) => #true
    | inr(pair) =>
      let value := fst(pair);
      if ((fst(value)) < #0) || ((snd(value)) < (fst(value))) then #false
      else check (snd(pair))

end SampLib.PolynomialFactory.Syntax
