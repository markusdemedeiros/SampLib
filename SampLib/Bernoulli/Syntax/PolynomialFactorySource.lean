import SampLib.Bernoulli.Syntax.PolynomialFactory
import SampLib.Core.CurriedStep

/-! Named continuations taken directly from the polynomial source. -/

open ProbLang

namespace SampLib.PolynomialFactory.Source

open FactoryFractions

variable {rT : Type} [ProbLangℝ rT]

def lambdaBody : Exp rT → Exp rT
  | .lam body => body
  | _ => .fail

/-- The source after binding its coin. -/
def sourceBody : Exp rT := lambdaBody Occil.FactoryExtra.polynomial

def coefficientsBody (coin : Val rT) : Exp rT :=
  lambdaBody (Exp.open' sourceBody coin.fst)

def unitBody (coin : Val rT) (xs : List Fraction) : Exp rT :=
  lambdaBody (Exp.open' (coefficientsBody coin) (listVal Fraction.encode xs).fst)

def initialBody (coin : Val rT) (xs : List Fraction) : Exp rT :=
  Exp.open' (unitBody coin xs) (Val.unit : Val rT).fst

def degreeBody (coin : Val rT) (xs : List Fraction) : Exp rT :=
  match initialBody coin xs with
  | .app (.lam body) _ => body
  | _ => .fail

/-- The original recursive degree search, with its actual captured input values. -/
def convert (coin : Val rT) (xs : List Fraction) : Exp rT :=
  match Exp.open' (degreeBody coin xs) (Val.int (degree xs : ℤ)).fst with
  | .cond _ _ (.app (.lam _) code) => code
  | _ => .fail

omit [ProbLangℝ rT] in
theorem source_eq : (Occil.FactoryExtra.polynomial : Exp rT) = .lam sourceBody := rfl

omit [ProbLangℝ rT] in
theorem opened_source (coin : Val rT) :
    Exp.open' sourceBody coin.fst = .lam (coefficientsBody coin) := rfl

theorem opened_coefficients (coin : Val rT) (xs : List Fraction) :
    Exp.open' (coefficientsBody coin) (listVal Fraction.encode xs).fst =
      .lam (unitBody coin xs) := rfl

private instance length_closed : ClosedExp (Occil.length : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.length, Exp.fv]

theorem initial_eq (coin : Val rT) (xs : List Fraction) :
    initialBody coin xs = .app (Exp.lam (degreeBody coin xs))
      pl(&Occil.length &(listVal Fraction.encode xs).fst - #1) := by
  simp [initialBody, unitBody, coefficientsBody, sourceBody, lambdaBody,
    degreeBody, Occil.FactoryExtra.polynomial, Exp.close, Exp.closeRec,
    Exp.open', Exp.openRec, openRec_val_fst, ClosedExp.closeRec, ClosedExp.openRec]

theorem opened_degree (coin : Val rT) (xs : List Fraction) :
    Exp.open' (degreeBody coin xs) (Val.int (degree xs : ℤ)).fst =
      .cond pl(#int (degree xs : ℤ) < #0) .fail
        (.app (.lam (.app (.bvar 0) (Val.int (degree xs : ℤ)).fst)) (convert coin xs)) := by
  simp [convert, degreeBody, initialBody, unitBody, coefficientsBody, sourceBody,
    lambdaBody, Occil.FactoryExtra.polynomial, Exp.close, Exp.closeRec,
    Exp.open', Exp.openRec, openRec_val_fst, ClosedExp.closeRec, ClosedExp.openRec]

omit [ProbLangℝ rT] in
theorem source_lc : (.lam sourceBody : Exp rT).IsLocallyClosed := by
  rw [← source_eq]
  is_lc

omit [ProbLangℝ rT] in
theorem coefficients_lc (coin : Val rT) :
    (Exp.lam (coefficientsBody coin)).IsLocallyClosed := by
  apply Exp.lcb_imp_lc
  have h := Exp.lcb_openRec (Exp.lc_imp_lcb coin.lc) (Exp.lc_imp_lcb source_lc)
  change Exp.lcb 0 (Exp.open' sourceBody coin.fst) = true at h
  rwa [opened_source] at h

theorem unit_lc (coin : Val rT) (xs : List Fraction) :
    (Exp.lam (unitBody coin xs)).IsLocallyClosed := by
  apply Exp.lcb_imp_lc
  have h := Exp.lcb_openRec (Exp.lc_imp_lcb (listVal Fraction.encode xs).lc)
    (Exp.lc_imp_lcb (coefficients_lc coin))
  change Exp.lcb 0 (Exp.open' (coefficientsBody coin) (listVal Fraction.encode xs).fst) = true at h
  rwa [opened_coefficients] at h

omit [ProbLangℝ rT] in
private theorem open_lc (body : Exp rT) (v : Val rT)
    (hc : (Exp.lam body).IsLocallyClosed) : (Exp.open' body v.fst).IsLocallyClosed := by
  apply Exp.lcb_imp_lc
  exact Exp.lcb_openRec (Exp.lc_imp_lcb v.lc) (Exp.lc_imp_lcb hc)

theorem degree_lc (coin : Val rT) (xs : List Fraction) :
    (Exp.lam (degreeBody coin xs)).IsLocallyClosed := by
  have h := open_lc (unitBody coin xs) Val.unit (unit_lc coin xs)
  change (initialBody coin xs).IsLocallyClosed at h
  rw [initial_eq] at h
  cases h with
  | app hf _ => exact hf

theorem convert_lc (coin : Val rT) (xs : List Fraction) :
    (convert coin xs).IsLocallyClosed := by
  have h := open_lc (degreeBody coin xs) (Val.int (degree xs : ℤ)) (degree_lc coin xs)
  rw [opened_degree] at h
  cases h with
  | cond _ _ he =>
    cases he with
    | app _ hf => exact hf

end SampLib.PolynomialFactory.Source
