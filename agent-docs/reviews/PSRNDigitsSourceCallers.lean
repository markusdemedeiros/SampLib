import SampLib.LatentDigitSource
import SampLib.Syntax.PSRNDigitsFreeVariables

open ProbLang SampLib.LatentDigits.Syntax

/-- A callback may contain a name used by quotation's internal binder bookkeeping. -/
def digitCallback {rT : Type} : Val rT :=
  ⟨.lam (.lam (.fvar (.internal 0))), .lam (by is_lc), by is_lc⟩

example {rT : Type} : Var.internal 0 ∈ (readVal (digitCallback (rT := rT))).fst.fv := by
  rw [read_fv]
  simp [digitCallback, Exp.fv]

example {rT : Type} (root : Loc) :
    Var.internal 0 ∈ (oracleVal (digitCallback (rT := rT)) root).fst.fv := by
  rw [oracle_fv]
  simp [digitCallback, Exp.fv]

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]
local bi (IProp GF)

example (E : CoPset) (nextBit : Val rT) (root : Loc) (remaining numerator denominator : ℤ)
    (P : IProp GF) (Φ : Val rT → IProp GF) :
    ⊢ P ∗ (P -∗ tglWp E (openedReadCode nextBit root remaining numerator denominator) Φ) -∗
      tglWp E pl(&(readVal nextBit).fst #loc root #int remaining #int numerator #int denominator)
        Φ := by
  iintro ⟨HP, Hbody⟩
  iapply twp_read_apply E nextBit root remaining numerator denominator Φ
  iapply Hbody $$ HP

#print axioms SampLib.LatentDigits.Syntax.twp_read_apply
#print axioms SampLib.LatentDigits.Syntax.allocated_oracle
#print axioms SampLib.LatentDigits.Syntax.read_fv
#print axioms SampLib.LatentDigits.Syntax.oracle_fv
