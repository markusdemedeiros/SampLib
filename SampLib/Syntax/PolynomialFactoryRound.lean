import SampLib.Syntax.PolynomialFactorySource
import SampLib.Samplers.BernsteinFactory

/-! One search round, with verified closed routines retained as named constants. -/

open ProbLang

namespace SampLib.PolynomialFactory.Source

open FactoryFractions

variable {rT : Type}

section

variable [ProbLangℝ rT]

def convertBody (coin : Val rT) (xs : List Fraction) : Exp rT :=
  match convert coin xs with
  | .fix (.lam body) => body
  | _ => .fail

def validBody (coin : Val rT) (xs : List Fraction) (n : ℕ) : Exp rT :=
  .cond (.app (.bvar 0) (.bvar 1))
    (.app (.app (.app Occil.bernsteinFactory coin.fst) (.bvar 1)) (.lit .unit))
    (.app (convert coin xs) (.binop .plus (.lit (.int n)) (.lit (.int 1))))

def tableBody (coin : Val rT) (xs : List Fraction) (n : ℕ) : Exp rT :=
  .app (.lam (validBody coin xs n)) Syntax.check

def allBody (coin : Val rT) (xs : List Fraction) (n : ℕ) : Exp rT :=
  .app (.lam (tableBody coin xs n)) (.app (.bvar 0) (.lit (.int 0)))

def collectOpen (n : ℕ) : Exp rT :=
  .fix (.lam (.cond (.binop .lt (.lit (.int n)) (.bvar 0)) (.inl (.lit .unit))
    (.inr (.pair (.app (.bvar 2) (.bvar 0))
      (.app (.bvar 1) (.binop .plus (.bvar 0) (.lit (.int 1))))))))

def coefficientBody (coin : Val rT) (xs : List Fraction) (n : ℕ) : Exp rT :=
  .app (.lam (allBody coin xs n)) (collectOpen n)

theorem convert_eq (coin : Val rT) (xs : List Fraction) :
    convert coin xs = .fix (.lam (convertBody coin xs)) := rfl

private instance binomial_closed : ClosedExp (Occil.binomial : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.binomial, Exp.fv]

private instance rational_closed : ClosedExp (Occil.rationalCoin : Exp rT) where
  lc := RationalCoin.rationalCoin_lc
  fv := RationalCoin.rationalCoin_fv

private instance bernstein_closed : ClosedExp (Occil.bernsteinFactory : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.bernsteinFactory, Exp.fv, ClosedExp.closeRec, ClosedExp.fv,
    ListAccess.getAt_closeRec, ListAccess.getAt_fv, Occil.length]

private instance check_closed : ClosedExp (Syntax.check : Exp rT) where
  lc := by is_lc
  fv := by simp [Syntax.check, Exp.fv]

theorem opened_convert (coin : Val rT) (xs : List Fraction) (n : ℕ) :
    Exp.open' (Exp.openRec 1 (convert coin xs) (convertBody coin xs)) (Val.int (n : ℤ)).fst =
      .app (.lam (coefficientBody coin xs n)) (Syntax.coefficient xs n) := by
  simp [convertBody, convert, degreeBody, initialBody, unitBody, coefficientsBody,
    sourceBody, lambdaBody, Occil.FactoryExtra.polynomial, coefficientBody,
    allBody, tableBody, validBody, collectOpen, Syntax.coefficient, Syntax.check,
    Exp.close, Exp.closeRec, Exp.open', Exp.openRec, openRec_val_fst,
    Syntax.fractionList_closeRec, ClosedExp.closeRec, ClosedExp.openRec,
    ListAccess.getAt_closeRec, ListAccess.getAt_openRec,
    FactoryChoose.choose_closeRec, FactoryChoose.choose_openRec]

@[simp] theorem convert_openRec (coin : Val rT) (xs : List Fraction) (k : ℕ) (e : Exp rT) :
    Exp.openRec k e (convert coin xs) = convert coin xs :=
  (Exp.open_lc k e _ (convert_lc coin xs)).symm

theorem convert_body_lcb (coin : Val rT) (xs : List Fraction) :
    Exp.lcb 2 (convertBody coin xs) = true := by
  have h := Exp.lc_imp_lcb (convert_lc coin xs)
  rw [convert_eq] at h
  exact h

def convertValue (coin : Val rT) (xs : List Fraction) : Val rT :=
  ⟨convert coin xs, .fix (convert_lc coin xs), convert_lc coin xs⟩

def coefficientValue (xs : List Fraction) (n : ℕ) : Val rT :=
  have hc : (Syntax.coefficient (rT := rT) xs n).IsLocallyClosed :=
    (Syntax.coefficient_closed xs n).lc
  ⟨Syntax.coefficient xs n, .lam hc, hc⟩

theorem coefficient_lc (coin : Val rT) (xs : List Fraction) (n : ℕ) :
    (Exp.lam (coefficientBody coin xs n)).IsLocallyClosed := by
  have hs := Exp.lcb_openRec (Exp.lcb_ofVal 1 (convertValue coin xs)) (convert_body_lcb coin xs)
  have h := Exp.lcb_openRec (Exp.lcb_ofVal 0 (Val.int (n : ℤ))) hs
  change Exp.lcb 0
    (Exp.open' (Exp.openRec 1 (convert coin xs) (convertBody coin xs))
      (Val.int (n : ℤ)).fst) = true at h
  rw [opened_convert] at h
  have hc := Exp.lcb_imp_lc h
  cases hc with
  | app hf _ => exact hf

theorem opened_coefficient (coin : Val rT) (xs : List Fraction) (n : ℕ) :
    Exp.open' (coefficientBody coin xs n) (coefficientValue xs n).fst =
      .app (.lam (allBody coin xs n)) (Syntax.collectCode xs n) := by
  simp [coefficientBody, coefficientValue, allBody, tableBody, validBody, collectOpen,
    Syntax.collectCode, Syntax.collectBody, Exp.open', Exp.openRec,
    openRec_val_fst, ClosedExp.openRec]

theorem all_lc (coin : Val rT) (xs : List Fraction) (n : ℕ) :
    (Exp.lam (allBody coin xs n)).IsLocallyClosed := by
  have h := Exp.lcb_openRec (Exp.lc_imp_lcb (coefficientValue (rT := rT) xs n).lc)
    (Exp.lc_imp_lcb (coefficient_lc coin xs n))
  change Exp.lcb 0 (Exp.open' (coefficientBody coin xs n) (coefficientValue xs n).fst) = true at h
  rw [opened_coefficient] at h
  cases Exp.lcb_imp_lc h with
  | app hf _ => exact hf

def collectValue (xs : List Fraction) (n : ℕ) : Val rT :=
  have hc : (Syntax.collectCode (rT := rT) xs n).IsLocallyClosed := by
    unfold Syntax.collectCode Syntax.collectBody
    is_lc
  ⟨Syntax.collectCode xs n, .fix hc, hc⟩

theorem opened_all (coin : Val rT) (xs : List Fraction) (n : ℕ) :
    Exp.open' (allBody coin xs n) (collectValue xs n).fst =
      .app (.lam (tableBody coin xs n)) pl(&(Syntax.collectCode xs n) #0) := by
  simp [allBody, collectValue, tableBody, validBody, Exp.open', Exp.openRec,
    openRec_val_fst, ClosedExp.openRec]

theorem table_lc (coin : Val rT) (xs : List Fraction) (n : ℕ) :
    (Exp.lam (tableBody coin xs n)).IsLocallyClosed := by
  have h := Exp.lcb_openRec (Exp.lc_imp_lcb (collectValue (rT := rT) xs n).lc)
    (Exp.lc_imp_lcb (all_lc coin xs n))
  change Exp.lcb 0 (Exp.open' (allBody coin xs n) (collectValue xs n).fst) = true at h
  rw [opened_all] at h
  cases Exp.lcb_imp_lc h with
  | app hf _ => exact hf

def conditionBody (coin : Val rT) (xs : List Fraction) (n : ℕ) (qs : Val rT) : Exp rT :=
  .cond (.app (.bvar 0) qs.fst)
    pl(&Occil.bernsteinFactory &coin.fst &qs.fst #())
    pl(&(convert coin xs) (#int (n : ℤ) + #1))

def branchCode (coin : Val rT) (xs : List Fraction) (n : ℕ) (qs : Val rT) : Exp rT :=
  .cond pl(&Syntax.check &qs.fst)
    pl(&Occil.bernsteinFactory &coin.fst &qs.fst #())
    pl(&(convert coin xs) (#int (n : ℤ) + #1))

def checkValue : Val rT :=
  have hc : (Syntax.check : Exp rT).IsLocallyClosed := check_closed.lc
  ⟨Syntax.check, .fix hc, hc⟩

theorem opened_table (coin : Val rT) (xs : List Fraction) (n : ℕ) (qs : Val rT) :
    Exp.open' (tableBody coin xs n) qs.fst =
      .app (.lam (conditionBody coin xs n qs)) Syntax.check := by
  simp [tableBody, validBody, conditionBody, Exp.open', Exp.openRec,
    openRec_val_fst, ClosedExp.openRec]

theorem condition_lc (coin : Val rT) (xs : List Fraction) (n : ℕ) (qs : Val rT) :
    (Exp.lam (conditionBody coin xs n qs)).IsLocallyClosed := by
  have h := Exp.lcb_openRec (Exp.lc_imp_lcb qs.lc) (Exp.lc_imp_lcb (table_lc coin xs n))
  change Exp.lcb 0 (Exp.open' (tableBody coin xs n) qs.fst) = true at h
  rw [opened_table] at h
  cases Exp.lcb_imp_lc h with
  | app hf _ => exact hf

theorem opened_condition (coin : Val rT) (xs : List Fraction) (n : ℕ) (qs : Val rT) :
    Exp.open' (conditionBody coin xs n qs) (checkValue (rT := rT)).fst =
      branchCode coin xs n qs := by
  simp [conditionBody, checkValue, branchCode, Exp.open', Exp.openRec,
    openRec_val_fst, ClosedExp.openRec]

end

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]
local bi (IProp GF)

/-- Unfold one search round and install its two deterministic local functions. -/
theorem twp_round (E : CoPset) (coin : Val rT) (xs : List Fraction) (n : ℕ)
    (Φ : Val rT → IProp GF) :
    tglWp E (.app (.lam (tableBody coin xs n)) pl(&(Syntax.collectCode xs n) #0)) Φ ⊢
      tglWp E pl(&(convert coin xs) #int (n : ℤ)) Φ := by
  iintro H
  rw [convert_eq]
  ieval (
    change _ ⊢ tglWp E
      (Ectx.fill ([] : Ectx rT) (CurriedStep.application [Val.int (n : ℤ)]
        (.fix (CurriedStep.lambdas 1 (convertBody coin xs))))) Φ)
  iapply (CurriedStep.twp_fix_apply E [] (Val.int (n : ℤ)) []
    (convertBody coin xs) (convert_body_lcb coin xs) Φ)
  ieval (
    change _ ⊢ tglWp E
      (Exp.open' (Exp.openRec 1 (convert coin xs) (convertBody coin xs)) (Val.int (n : ℤ)).fst) Φ)
  rw [opened_convert]
  ieval (
    change _ ⊢ tglWp E (Ectx.fill ([] : Ectx rT)
      (.app (.lam (coefficientBody coin xs n)) (coefficientValue xs n).fst)) Φ)
  iapply (twp_beta E [] (coefficientBody coin xs n) (coefficientValue xs n)
    (coefficient_lc coin xs n) Φ)
  ieval (
    change _ ⊢ tglWp E
      (Exp.open' (coefficientBody coin xs n) (coefficientValue xs n).fst) Φ)
  rw [opened_coefficient]
  ieval (
    change _ ⊢ tglWp E (Ectx.fill ([] : Ectx rT)
      (.app (.lam (allBody coin xs n)) (collectValue xs n).fst)) Φ)
  iapply (twp_beta E [] (allBody coin xs n) (collectValue xs n) (all_lc coin xs n) Φ)
  ieval (change _ ⊢ tglWp E (Exp.open' (allBody coin xs n) (collectValue xs n).fst) Φ)
  rw [opened_all]
  iexact H

/-- Install the check function and expose the source's two search exits. -/
theorem twp_table (E : CoPset) (coin : Val rT) (xs : List Fraction) (n : ℕ)
    (qs : Val rT) (Φ : Val rT → IProp GF) :
    tglWp E (branchCode coin xs n qs) Φ ⊢
      tglWp E (.app (.lam (tableBody coin xs n)) qs.fst) Φ := by
  iintro H
  ieval (
    change _ ⊢ tglWp E (Ectx.fill ([] : Ectx rT)
      (.app (.lam (tableBody coin xs n)) qs.fst)) Φ)
  iapply (twp_beta E [] (tableBody coin xs n) qs (table_lc coin xs n) Φ)
  ieval (
    change _ ⊢ tglWp E (Exp.open' (tableBody coin xs n) qs.fst) Φ)
  rw [opened_table]
  ieval (
    change _ ⊢ tglWp E (Ectx.fill ([] : Ectx rT)
      (.app (.lam (conditionBody coin xs n qs)) (checkValue (rT := rT)).fst)) Φ)
  iapply (twp_beta E [] (conditionBody coin xs n qs) checkValue (condition_lc coin xs n qs) Φ)
  ieval (
    change _ ⊢ tglWp E (Exp.open' (conditionBody coin xs n qs) (checkValue (rT := rT)).fst) Φ)
  rw [opened_condition]
  iexact H

end specification

end SampLib.PolynomialFactory.Source
