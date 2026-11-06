import SampLib.Discrete.Support.BinomialHalfBranchesSyntax
import SampLib.Uniform.RationalCoin

/-! # Two primitive openings of the half-binomial source

Keeping the intermediate syntax unreduced lets closed-constant lemmas avoid
repeatedly traversing the large recursive function.
-/

open ProbLang

namespace SampLib.BinomialHalfOpening

noncomputable section

variable {rT : Type}

def body : Exp rT := match (Occil.DiscreteExtra.binomialHalfRejection : Exp rT) with
  | .fix b => b
  | _ => .lit .unit

/-- The actual recursive body, with its recursive variable left bound. -/
theorem body_eq : (body : Exp rT) = (pl% fun n,
    if n < #0 then fail else if n < #4 then &Occil.DiscreteExtra.binomialHalfBits n else
    if n % #2 = #1 then
      {Exp.bvar 1} (n - #1) + &Occil.uniformInt #2
    else
      let width := &Occil.DiscreteExtra.integerSqrt n + #1;
      let loop := (rec draw u :=
        let block := &Occil.geometric &Occil.fairCoin #();
        let offset := block * width + &Occil.uniformInt width;
        let candidate := (if &Occil.fairCoin #() then n / #2 + offset
                          else n / #2 - offset - #1);
        if (candidate < #0) || (n < candidate) then draw #() else
          let numerator := &Occil.DiscreteExtra.choose n candidate * width;
          let denominator := &Occil.DiscreteExtra.integerPower #2 (n + #2 - block);
          if &Occil.rationalCoin numerator denominator then candidate else draw #());
      loop #()) := by
  simp [body, Occil.DiscreteExtra.binomialHalfRejection, Exp.close, Exp.closeRec]

def opened : Exp rT :=
  Exp.open' body Occil.DiscreteExtra.binomialHalfRejection

def argumentBody : Exp rT := match (opened : Exp rT) with
  | .lam b => b
  | _ => .lit .unit

/-- The source after its recursive function and size argument have been opened. -/
def stage (n : ℕ) : Exp rT := pl%
  if #int (n : ℤ) < #0 then fail else
  if #int (n : ℤ) < #4 then &Occil.DiscreteExtra.binomialHalfBits #int (n : ℤ) else
  if #int (n : ℤ) % #2 = #1 then
    &Occil.DiscreteExtra.binomialHalfRejection (#int (n : ℤ) - #1) + &Occil.uniformInt #2
  else
    let width := &Occil.DiscreteExtra.integerSqrt #int (n : ℤ) + #1;
    let loop := (rec draw u :=
      let block := &Occil.geometric &Occil.fairCoin #();
      let offset := block * width + &Occil.uniformInt width;
      let candidate := (if &Occil.fairCoin #() then #int (n : ℤ) / #2 + offset
                        else #int (n : ℤ) / #2 - offset - #1);
      if (candidate < #0) || (#int (n : ℤ) < candidate) then draw #() else
        let numerator := &Occil.DiscreteExtra.choose #int (n : ℤ) candidate * width;
        let denominator := &Occil.DiscreteExtra.integerPower #2 (#int (n : ℤ) + #2 - block);
        if &Occil.rationalCoin numerator denominator then candidate else draw #());
    loop #()

theorem source_lc : (Occil.DiscreteExtra.binomialHalfRejection : Exp rT).IsLocallyClosed := by
  is_lc

@[simp] theorem source_openRec (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.DiscreteExtra.binomialHalfRejection =
      Occil.DiscreteExtra.binomialHalfRejection :=
  (Exp.open_lc k e _ source_lc).symm

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_open_raw (E : CoPset) (n : ℕ) (Φ : Val rT → IProp GF) :
    tglWp E (Exp.open' argumentBody (Val.int (n : ℤ)).fst) Φ ⊢
      tglWp E pl(&Occil.DiscreteExtra.binomialHalfRejection #int (n : ℤ)) Φ := by
  apply BI.BIBase.Entails.trans (Q := tglWp E (.app opened (Val.int (n : ℤ)).fst) Φ)
  · let : PureExec ((Val.int (n : ℤ)).fst.isValue ∧ (opened : Exp rT).IsLocallyClosed) 1
        (.app opened (Val.int (n : ℤ)).fst)
        (Exp.open' argumentBody (Val.int (n : ℤ)).fst) :=
      pureExec_app_lam (body := argumentBody)
    exact twp_pure_step_fupd _ ⟨IsVal.toIsValue .lit, by is_lc⟩
  · let : PureExec ((Val.int (n : ℤ)).fst.isValue ∧
        (Occil.DiscreteExtra.binomialHalfRejection : Exp rT).IsLocallyClosed) 1
        pl(&Occil.DiscreteExtra.binomialHalfRejection #int (n : ℤ))
        (.app opened (Val.int (n : ℤ)).fst) := pureExec_app_fix (body := body)
    exact twp_pure_step_fupd _ ⟨IsVal.toIsValue .lit, source_lc⟩

/-- Open the unchanged source while keeping closed sampler constants folded. -/
theorem twp_open (E : CoPset) (n : ℕ) (Φ : Val rT → IProp GF) :
    tglWp E (stage n) Φ ⊢
      tglWp E pl(&Occil.DiscreteExtra.binomialHalfRejection #int (n : ℤ)) Φ := by
  convert twp_open_raw (rT := rT) (GF := GF) E n Φ using 1
  simp [stage, argumentBody, opened, body_eq, Exp.open', Exp.openRec, Exp.close, Exp.closeRec]

end

end SampLib.BinomialHalfOpening
