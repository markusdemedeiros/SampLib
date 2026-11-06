import SampLib.Syntax.PolynomialFactory
import SampLib.CurriedStep

/-! Cached closure openings for the polynomial conversion loops. -/

open ProbLang

namespace SampLib.PolynomialFactory.Syntax

open FactoryFractions

section code

variable {rT : Type} [ProbLangℝ rT]

private instance getAt_closed : ClosedExp (Occil.getAt : Exp rT) where
  lc := ListAccess.getAt_lc
  fv := ListAccess.getAt_fv

private instance choose_closed : ClosedExp (Occil.FactoryExtra.choose : Exp rT) where
  lc := FactoryChoose.choose_lc
  fv := FactoryChoose.choose_fv

instance terms_closed (xs : List Fraction) (n k : ℕ) : ClosedExp (terms (rT := rT) xs n k) where
  lc := by is_lc
  fv := by simp [terms, Exp.fv, ClosedExp.closeRec, ClosedExp.fv]

instance check_closed : ClosedExp (check : Exp rT) where
  lc := by is_lc
  fv := by simp [check, Exp.fv]

def termsValue (xs : List Fraction) (n k : ℕ) : Val rT :=
  have hc : (terms (rT := rT) xs n k).IsLocallyClosed := (terms_closed xs n k).lc
  ⟨terms xs n k, .fix hc, hc⟩

@[simp] theorem termsValue_fst (xs : List Fraction) (n k : ℕ) :
    (termsValue (rT := rT) xs n k).fst = terms xs n k := rfl

def checkValue : Val rT :=
  have hc : (check : Exp rT).IsLocallyClosed := check_closed.lc
  ⟨check, .fix hc, hc⟩

omit [ProbLangℝ rT] in
@[simp] theorem checkValue_fst : (checkValue (rT := rT)).fst = check := rfl

instance termsValue_closed (xs : List Fraction) (n k : ℕ) :
    ClosedExp (termsValue (rT := rT) xs n k).fst where
  lc := (termsValue xs n k).lc
  fv := by rw [termsValue_fst]; exact (terms_closed xs n k).fv

instance checkValue_closed : ClosedExp (checkValue (rT := rT)).fst where
  lc := (checkValue (rT := rT)).lc
  fv := by rw [checkValue_fst]; exact check_closed.fv

private def termsCore (xs : List Fraction) (n k : ℕ) : Exp rT :=
  match terms xs n k with
  | .fix (.lam (.lam body)) => body
  | _ => .fail

private def checkCore : Exp rT :=
  match check with
  | .fix (.lam body) => body
  | _ => .fail

private theorem terms_eq (xs : List Fraction) (n k : ℕ) :
    (terms xs n k : Exp rT) = .fix (CurriedStep.lambdas 2 (termsCore xs n k)) := rfl

omit [ProbLangℝ rT] in
private theorem check_eq : (check : Exp rT) = .fix (.lam checkCore) := rfl

private theorem terms_lcb (xs : List Fraction) (n k : ℕ) :
    Exp.lcb 3 (termsCore (rT := rT) xs n k) = true := by
  have h := Exp.lc_imp_lcb (termsValue (rT := rT) xs n k).lc
  change Exp.lcb 0 (terms xs n k) = true at h
  rw [terms_eq] at h
  exact h

omit [ProbLangℝ rT] in
private theorem check_lcb : Exp.lcb 2 (checkCore : Exp rT) = true := by
  have h := Exp.lc_imp_lcb (checkValue (rT := rT)).lc
  change Exp.lcb 0 (check : Exp rT) = true at h
  rw [check_eq] at h
  exact h

private def nextBody (xs : List Fraction) (n k j : ℕ) (acc : ℚ) : Exp rT :=
  pl(&(termsValue xs n k).fst (#int (j : ℤ) + #1)
    (&Occil.FactoryExtra.addFraction &(encode acc).fst {Exp.bvar 0}))

private def denominatorCode (xs : List Fraction) (n k j : ℕ) (acc : ℚ)
    (a num : ℕ → Exp rT) : Exp rT :=
  .app (.lam (nextBody xs n k j acc))
    pl(&Occil.FactoryExtra.multiplyFraction {a 0} ({num 0}, {Exp.bvar 0}))

private def numeratorCode (xs : List Fraction) (n k j : ℕ) (acc : ℚ)
    (a : ℕ → Exp rT) : Exp rT :=
  .app (.lam (denominatorCode xs n k j acc (fun d => a (d + 1))
    (fun d => .bvar (d + 1)))) pl(&Occil.FactoryExtra.choose #int (n : ℤ) #int (j : ℤ))

private def lookupBody (xs : List Fraction) (n k j : ℕ) (acc : ℚ) : Exp rT :=
  .app (.lam (numeratorCode xs n k j acc (fun d => .bvar (d + 1))))
    pl(&Occil.FactoryExtra.choose #int (k : ℤ) #int (j : ℤ))

private def numeratorBody (xs : List Fraction) (n k j : ℕ) (acc : ℚ) (a : Fraction) : Exp rT :=
  numeratorCode xs n k j acc (fun _ => a.encode.fst)

private def denominatorBody (xs : List Fraction) (n k j : ℕ) (acc : ℚ)
    (a : Fraction) (num : ℕ) : Exp rT :=
  denominatorCode xs n k j acc (fun _ => a.encode.fst) (fun _ => .lit (.int num))

def termsCase (xs : List Fraction) (n k j : ℕ) (acc : ℚ) : Exp rT :=
  .cond pl((#int (degree xs : ℤ) < #int (j : ℤ)) || (#int (k : ℤ) < #int (j : ℤ)))
    (encode acc).fst (.app (.lam (lookupBody xs n k j acc))
      pl(&Occil.getAt &(listVal Fraction.encode xs).fst #int (j : ℤ)))

def checkCase (xs : List Fraction) : Exp rT := pl%
  case! &(listVal Fraction.encode xs).fst
    | inl(v) => #true
    | inr(pair) =>
      let value := fst(pair);
      if ((fst(value)) < #0) || ((snd(value)) < (fst(value))) then #false
      else &(checkValue (rT := rT)).fst (snd(pair))

private theorem opened_terms (xs : List Fraction) (n k j : ℕ) (acc : ℚ) :
    CurriedStep.opened [Val.int (j : ℤ), encode acc]
      (Exp.openRec 2 (terms xs n k) (termsCore xs n k)) =
        (termsCase xs n k j acc : Exp rT) := by
  simp [termsCore, terms, termsCase, lookupBody, numeratorCode, denominatorCode, nextBody,
    termsValue, CurriedStep.opened, encode,
    Exp.close, Exp.closeRec, Exp.openRec, ClosedExp.closeRec, ClosedExp.openRec,
    openRec_val_fst]

private theorem termsCase_lc (xs : List Fraction) (n k j : ℕ) (acc : ℚ) :
    (termsCase (rT := rT) xs n k j acc).IsLocallyClosed := by
  have hs := Exp.lcb_openRec (Exp.lcb_ofVal 2 (termsValue (rT := rT) xs n k))
    (terms_lcb xs n k)
  have hj := Exp.lcb_openRec (Exp.lcb_ofVal 1 (Val.int (j : ℤ))) hs
  have ha := Exp.lcb_openRec (Exp.lcb_ofVal 0 (encode (rT := rT) acc)) hj
  change Exp.lcb 0 (CurriedStep.opened [Val.int (j : ℤ), encode acc]
    (Exp.openRec 2 (terms xs n k) (termsCore xs n k))) = true at ha
  rw [opened_terms] at ha
  exact Exp.lcb_imp_lc ha

private theorem lookup_lc (xs : List Fraction) (n k j : ℕ) (acc : ℚ) :
    (Exp.lam (lookupBody (rT := rT) xs n k j acc)).IsLocallyClosed := by
  have h := termsCase_lc (rT := rT) xs n k j acc
  change (Exp.cond _ _ (.app (.lam (lookupBody xs n k j acc)) _)).IsLocallyClosed at h
  cases h with
  | cond _ _ he =>
    cases he with
    | app hf _ => exact hf

omit [ProbLangℝ rT] in
private theorem open_lc (body : Exp rT) (v : Val rT)
    (hc : (Exp.lam body).IsLocallyClosed) : (Exp.open' body v.fst).IsLocallyClosed :=
  Exp.lcb_imp_lc (Exp.lcb_openRec (Exp.lc_imp_lcb v.lc) (Exp.lc_imp_lcb hc))

private theorem opened_lookup (xs : List Fraction) (n k j : ℕ) (acc : ℚ) (a : Fraction) :
    Exp.open' (lookupBody (rT := rT) xs n k j acc) a.encode.fst =
      .app (.lam (numeratorBody xs n k j acc a))
        pl(&Occil.FactoryExtra.choose #int (k : ℤ) #int (j : ℤ)) := by
  simp [lookupBody, numeratorBody, numeratorCode, denominatorCode, nextBody,
    Exp.open', Exp.openRec, ClosedExp.openRec, openRec_val_fst]

private theorem numerator_lc (xs : List Fraction) (n k j : ℕ) (acc : ℚ) (a : Fraction) :
    (Exp.lam (numeratorBody (rT := rT) xs n k j acc a)).IsLocallyClosed := by
  have h := open_lc _ a.encode (lookup_lc (rT := rT) xs n k j acc)
  rw [opened_lookup] at h
  cases h with
  | app hf _ => exact hf

private theorem opened_numerator (xs : List Fraction) (n k j : ℕ) (acc : ℚ)
    (a : Fraction) (num : ℕ) :
    Exp.open' (numeratorBody (rT := rT) xs n k j acc a) (Val.int (num : ℤ)).fst =
      .app (.lam (denominatorBody xs n k j acc a num))
        pl(&Occil.FactoryExtra.choose #int (n : ℤ) #int (j : ℤ)) := by
  simp [numeratorBody, numeratorCode, denominatorBody, denominatorCode, nextBody,
    Exp.open', Exp.openRec, ClosedExp.openRec, openRec_val_fst]

private theorem denominator_lc (xs : List Fraction) (n k j : ℕ) (acc : ℚ)
    (a : Fraction) (num : ℕ) :
    (Exp.lam (denominatorBody (rT := rT) xs n k j acc a num)).IsLocallyClosed := by
  have h := open_lc _ (Val.int (num : ℤ)) (numerator_lc (rT := rT) xs n k j acc a)
  rw [opened_numerator] at h
  cases h with
  | app hf _ => exact hf

private theorem opened_denominator (xs : List Fraction) (n k j : ℕ) (acc : ℚ)
    (a : Fraction) (num den : ℕ) :
    Exp.open' (denominatorBody (rT := rT) xs n k j acc a num) (Val.int (den : ℤ)).fst =
      .app (.lam (nextBody xs n k j acc))
        pl(&Occil.FactoryExtra.multiplyFraction &a.encode.fst
          (#int (num : ℤ), #int (den : ℤ))) := by
  simp [denominatorBody, denominatorCode, nextBody, Exp.open', Exp.openRec,
    ClosedExp.openRec, openRec_val_fst]

private theorem next_lc (xs : List Fraction) (n k j : ℕ) (acc : ℚ) :
    (Exp.lam (nextBody (rT := rT) xs n k j acc)).IsLocallyClosed := by
  have h := open_lc _ (Val.int (0 : ℤ))
    (denominator_lc (rT := rT) xs n k j acc zeroFraction 0)
  have he := opened_denominator (rT := rT) xs n k j acc zeroFraction 0 0
  simp only [Nat.cast_zero] at he
  rw [he] at h
  cases h with
  | app hf _ => exact hf

private theorem opened_next (xs : List Fraction) (n k j : ℕ) (acc q : ℚ) :
    Exp.open' (nextBody (rT := rT) xs n k j acc) (encode q).fst =
      pl(&(terms xs n k) (#int (j : ℤ) + #1)
        (&Occil.FactoryExtra.addFraction &(encode acc).fst &(encode q).fst)) := by
  simp [nextBody, termsValue, Exp.open', Exp.openRec, ClosedExp.openRec, openRec_val_fst]

private theorem opened_check (xs : List Fraction) :
    CurriedStep.opened [listVal Fraction.encode xs]
      (Exp.openRec 1 check checkCore) = (checkCase xs : Exp rT) := by
  simp [checkCore, check, checkCase, checkValue, CurriedStep.opened,
    Exp.close, Exp.closeRec, Exp.openRec]

private def coefficientCore (xs : List Fraction) (n : ℕ) : Exp rT :=
  match coefficient xs n with
  | .lam body => body
  | _ => .fail

private theorem coefficient_eq (xs : List Fraction) (n : ℕ) :
    (coefficient xs n : Exp rT) = .lam (coefficientCore xs n) := rfl

private def initialCall : Exp rT :=
  .app (.app (.bvar 0) (.lit (.int 0))) (.pair (.lit (.int 0)) (.lit (.int 1)))

private theorem opened_coefficient (xs : List Fraction) (n k : ℕ) :
    Exp.open' (coefficientCore (rT := rT) xs n) (Val.int (k : ℤ)).fst =
      .app (.lam initialCall) (termsValue xs n k).fst := by
  simp [coefficientCore, coefficient, terms, termsValue, initialCall,
    Exp.close, Exp.closeRec, Exp.open', Exp.openRec, ClosedExp.closeRec,
    ClosedExp.openRec, openRec_val_fst]

private theorem opened_initialCall (xs : List Fraction) (n k : ℕ) :
    Exp.open' (initialCall : Exp rT) (termsValue xs n k).fst =
      pl(&(terms xs n k) #0 &(encode (0 : ℚ)).fst) := by
  simp [initialCall, termsValue, encode, Exp.open', Exp.openRec]

end code

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]
local bi (IProp GF)

private theorem twp_return (E : CoPset) (body : Exp rT) (v : Val rT)
    (hc : (Exp.lam body).IsLocallyClosed) (e : Exp rT)
    (h : Exp.open' body v.fst = e) (Φ : Val rT → IProp GF) :
    tglWp E e Φ ⊢ tglWp E (.app (.lam body) v.fst) Φ := by
  simpa only [Ectx.fill, List.foldl_nil, h] using twp_beta E [] body v hc Φ

theorem twp_lookup_return (E : CoPset) (xs : List Fraction) (n k j : ℕ) (acc : ℚ)
    (a : Fraction) (Φ : Val rT → IProp GF) :
    tglWp E (.app (.lam (numeratorBody xs n k j acc a))
      pl(&Occil.FactoryExtra.choose #int (k : ℤ) #int (j : ℤ))) Φ ⊢
      tglWp E (.app (.lam (lookupBody xs n k j acc)) a.encode.fst) Φ :=
  twp_return E _ a.encode (lookup_lc xs n k j acc) _ (opened_lookup xs n k j acc a) Φ

theorem twp_numerator_return (E : CoPset) (xs : List Fraction) (n k j : ℕ) (acc : ℚ)
    (a : Fraction) (num : ℕ) (Φ : Val rT → IProp GF) :
    tglWp E (.app (.lam (denominatorBody xs n k j acc a num))
      pl(&Occil.FactoryExtra.choose #int (n : ℤ) #int (j : ℤ))) Φ ⊢
      tglWp E (.app (.lam (numeratorBody xs n k j acc a)) (Val.int (num : ℤ)).fst) Φ :=
  twp_return E _ (Val.int (num : ℤ)) (numerator_lc xs n k j acc a) _
    (opened_numerator xs n k j acc a num) Φ

theorem twp_denominator_return (E : CoPset) (xs : List Fraction) (n k j : ℕ) (acc : ℚ)
    (a : Fraction) (num den : ℕ) (Φ : Val rT → IProp GF) :
    tglWp E (.app (.lam (nextBody xs n k j acc))
      pl(&Occil.FactoryExtra.multiplyFraction &a.encode.fst (#int (num : ℤ), #int (den : ℤ)))) Φ ⊢
      tglWp E (.app (.lam (denominatorBody xs n k j acc a num)) (Val.int (den : ℤ)).fst) Φ :=
  twp_return E _ (Val.int (den : ℤ)) (denominator_lc xs n k j acc a num) _
    (opened_denominator xs n k j acc a num den) Φ

theorem twp_product_return (E : CoPset) (xs : List Fraction) (n k j : ℕ) (acc q : ℚ)
    (Φ : Val rT → IProp GF) :
    tglWp E pl(&(terms xs n k) (#int (j : ℤ) + #1)
      (&Occil.FactoryExtra.addFraction &(encode acc).fst &(encode q).fst)) Φ ⊢
      tglWp E (.app (.lam (nextBody xs n k j acc)) (encode q).fst) Φ :=
  twp_return E _ (encode q) (next_lc xs n k j acc) _ (opened_next xs n k j acc q) Φ

/-- Open the recursive accumulator with its cached closure certificate. -/
theorem twp_terms_open (E : CoPset) (xs : List Fraction) (n k j : ℕ) (acc : ℚ)
    (Φ : Val rT → IProp GF) :
    tglWp E (termsCase xs n k j acc) Φ ⊢
      tglWp E pl(&(terms xs n k) #int (j : ℤ) &(encode acc).fst) Φ := by
  iintro H
  rw [terms_eq]
  ieval (
    change _ ⊢ tglWp E (Ectx.fill ([] : Ectx rT)
      (CurriedStep.application [Val.int (j : ℤ), encode acc]
        (.fix (CurriedStep.lambdas 2 (termsCore xs n k))))) Φ)
  iapply (CurriedStep.twp_fix_apply E [] (Val.int (j : ℤ)) [encode acc]
    (termsCore xs n k) (terms_lcb xs n k) Φ)
  ieval (
    change _ ⊢ tglWp E (CurriedStep.opened [Val.int (j : ℤ), encode acc]
      (Exp.openRec 2 (terms xs n k) (termsCore xs n k))) Φ)
  rw [opened_terms]
  iexact H

/-- Open the list check without unfolding its recursive closure in a CTE proof. -/
theorem twp_check_open (E : CoPset) (xs : List Fraction) (Φ : Val rT → IProp GF) :
    tglWp E (checkCase xs) Φ ⊢ tglWp E pl(&check &(listVal Fraction.encode xs).fst) Φ := by
  iintro H
  rw [check_eq]
  ieval (
    change _ ⊢ tglWp E (Ectx.fill ([] : Ectx rT)
      (CurriedStep.application [listVal Fraction.encode xs]
        (.fix (CurriedStep.lambdas 1 checkCore)))) Φ)
  iapply (CurriedStep.twp_fix_apply E [] (listVal Fraction.encode xs) [] checkCore check_lcb Φ)
  ieval (
    change _ ⊢ tglWp E (CurriedStep.opened [listVal Fraction.encode xs]
      (Exp.openRec 1 check checkCore)) Φ)
  rw [opened_check]
  iexact H

/-- Open a coefficient closure and install its unchanged accumulator loop. -/
theorem twp_coefficient_open (E : CoPset) (xs : List Fraction) (n k : ℕ)
    (Φ : Val rT → IProp GF) :
    tglWp E pl(&(terms xs n k) #0 &(encode (0 : ℚ)).fst) Φ ⊢
      tglWp E pl(&(coefficient xs n) #int (k : ℤ)) Φ := by
  iintro H
  rw [coefficient_eq]
  ieval (
    change _ ⊢ tglWp E (Ectx.fill ([] : Ectx rT)
      (.app (.lam (coefficientCore xs n)) (Val.int (k : ℤ)).fst)) Φ)
  have hc : (Exp.lam (coefficientCore (rT := rT) xs n)).IsLocallyClosed := by
    rw [← coefficient_eq]
    exact (coefficient_closed xs n).lc
  iapply (twp_beta E [] (coefficientCore xs n) (Val.int (k : ℤ)) hc Φ)
  ieval (
    change _ ⊢ tglWp E (Exp.open' (coefficientCore xs n) (Val.int (k : ℤ)).fst) Φ)
  rw [opened_coefficient]
  ieval (
    change _ ⊢ tglWp E (Ectx.fill ([] : Ectx rT)
      (.app (.lam initialCall) (termsValue xs n k).fst)) Φ)
  iapply (twp_beta E [] initialCall (termsValue xs n k) (by is_lc) Φ)
  ieval (
    change _ ⊢ tglWp E (Exp.open' initialCall (termsValue xs n k).fst) Φ)
  rw [opened_initialCall]
  iexact H

end specification

end SampLib.PolynomialFactory.Syntax
