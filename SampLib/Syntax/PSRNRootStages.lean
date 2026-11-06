import SampLib.Syntax.PSRNRootObserve

/-! # Certified source openings between root-observation stages

These entailments execute only the two deterministic powers and closure/let
steps. The sampler proof can then work entirely with the named search rules.
-/

open ProbLang

namespace SampLib.LatentReal.Root.Program

private instance less_closed {rT : Type} : ClosedExp (Occil.PSRN.less : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.PSRN.less, Exp.fv]

private instance rational_closed {rT : Type} : ClosedExp (Occil.PSRN.rational : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.PSRN.rational, Exp.fv]

private def afterPowerBody {rT : Type} (source : Val rT) (degree : ℕ) (denominator : ℤ) : Exp rT :=
  let bind (rhs body : Exp rT) := .app (.lam body) rhs
  let finish := .app (.app (.bvar 0) (.lit (.int 0))) (.bvar 1)
  let search := bind (searchCode (.bvar 6) (.lit (.int denominator))) finish
  let upper := bind (.app (.bvar 0) (.lit (.int denominator))) search
  let bracket := bind (bracketCode (.bvar 2)) upper
  bind (callbackCode source.fst degree (.bvar 2)) bracket

/-- The first exact power fixes the denominator; the second fixes its degree-th power. -/
def powerStage {rT : Type} (source : Val rT) (degree : ℕ) (denominator : ℤ) : Exp rT :=
  .app (.lam (afterPowerBody source degree denominator))
    (.app (.app Occil.PSRN.integerPower (.lit (.int denominator))) (.lit (.int (degree : ℤ))))

/-- The initial grid-denominator computation. -/
def denominatorStage {rT : Type} (source : Val rT) (degree n : ℕ) : Exp rT :=
  match observeCode source degree n with
  | .cond _ _ code => code
  | _ => .fail

private def afterUpperBody {rT : Type} (source : Val rT) (degree : ℕ) (denominator : ℤ) : Exp rT :=
  .app (.lam (.app (.app (.bvar 0) (.lit (.int 0))) (.bvar 1)))
    (bisect (belowVal source degree denominator) denominator)

/-- Once the grid is fixed, only the upper-bracket call and final bisection remain. -/
def bracketStage {rT : Type} (source : Val rT) (degree : ℕ) (denominator : ℤ) : Exp rT :=
  .app (.lam (afterUpperBody source degree denominator))
    (.app (bracket (belowVal source degree denominator)) (.lit (.int denominator)))

def bracketContinuation {rT : Type} (source : Val rT) (degree : ℕ) (denominator : ℤ)
    (result : Val rT) : Exp rT := .app (.lam (afterUpperBody source degree denominator)) result.fst

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Open one nonnegative precision request up to its first exact power. -/
theorem twp_begin (E : CoPset) (source : Val rT) (degree n : ℕ) (Φ : Val rT → IProp GF) :
    tglWp E (denominatorStage source degree n) Φ ⊢
      tglWp E pl(&(value source degree).fst #int (n : ℤ)) Φ := by
  iintro H
  iapply twp_open_observe E source degree n Φ
  isimp only [observeCode, callbackCode, bracketCode, searchCode]
  iterate 2 twp_pure
  ieval (change _ ⊢ tglWp E (denominatorStage source degree n) Φ)
  iexact H

/-- Execute `2^n` and substitute its exact integer result. -/
theorem twp_power_denominator (E : CoPset) (source : Val rT) (degree n : ℕ)
    (Φ : Val rT → IProp GF) :
    tglWp E (powerStage source degree ((2 : ℤ) ^ n)) Φ ⊢
      tglWp E (denominatorStage source degree n) Φ := by
  iintro H
  isimp only [denominatorStage, observeCode, callbackCode, bracketCode, searchCode]
  twp_bind pl(&Occil.PSRN.integerPower #2 #int (n : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply PSRNIntegerPower.twp_integerPower E 2 n
  iintro %denominator %hdenominator
  subst denominator
  twp_pure
  have hopen (k : ℕ) (e : Exp rT) : Exp.openRec k e source.fst = source.fst :=
    (Exp.open_lc k e source.fst source.lc).symm
  isimp only [ClosedExp.openRec, ClosedExp.closeRec, hopen]
  ieval (change _ ⊢ tglWp E (powerStage source degree ((2 : ℤ) ^ n)) Φ)
  iexact H

/-- Execute the denominator's degree-th power and capture the two search closures. -/
theorem twp_power_grid (E : CoPset) (source : Val rT) (degree : ℕ) (denominator : ℤ)
    (Φ : Val rT → IProp GF) :
    tglWp E (bracketStage source degree denominator) Φ ⊢
      tglWp E (powerStage source degree denominator) Φ := by
  iintro H
  isimp only [powerStage, afterPowerBody, callbackCode, bracketCode, searchCode]
  twp_bind pl(&Occil.PSRN.integerPower #denominator #int (degree : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply PSRNIntegerPower.twp_integerPower E denominator degree
  iintro %power %hpower
  subst power
  iterate 3 twp_pure
  have hopen (k : ℕ) (e : Exp rT) : Exp.openRec k e source.fst = source.fst :=
    (Exp.open_lc k e source.fst source.lc).symm
  isimp only [ClosedExp.openRec, ClosedExp.closeRec, hopen]
  ieval (change _ ⊢ tglWp E (bracketStage source degree denominator) Φ)
  iexact H

/-- Focus the sole remaining upper-bracket query in its source continuation. -/
theorem twp_bind_bracket (E : CoPset) (source : Val rT) (degree : ℕ) (denominator : ℤ)
    (Φ : Val rT → IProp GF) :
    tglWp E pl(&(bracket (belowVal source degree denominator)) #denominator)
      (fun v => tglWp E (bracketContinuation source degree denominator v) Φ) ⊢
      tglWp E (bracketStage source degree denominator) Φ := by
  iintro H
  isimp only [bracketStage, afterUpperBody]
  twp_bind pl(&(bracket (belowVal source degree denominator)) #denominator)
  ieval (
    change _ ⊢ tglWp E pl(&(bracket (belowVal source degree denominator)) #denominator)
      (fun v => tglWp E (bracketContinuation source degree denominator v) Φ))
  iexact H

/-- The returned upper endpoint opens the final bisection call. -/
theorem twp_open_bisect (E : CoPset) (source : Val rT) (degree : ℕ) (denominator hi : ℤ)
    (Φ : Val rT → IProp GF) :
    tglWp E pl(&(bisect (belowVal source degree denominator) denominator) #0 #hi) Φ ⊢
      tglWp E (bracketContinuation source degree denominator (Val.int hi)) Φ := by
  iintro H
  isimp only [bracketContinuation, afterUpperBody]
  iterate 2 twp_pure
  have hopen (k : ℕ) (e : Exp rT) :
      Exp.openRec k e (bisect (belowVal source degree denominator) denominator) =
        bisect (belowVal source degree denominator) denominator :=
    (Exp.open_lc k e _ (bisect_lc _ _)).symm
  isimp only [hopen]
  iexact H

end specification

end SampLib.LatentReal.Root.Program
