import SampLib.Constants.FromApproximateDigits

open ProbLang SampLib FromApproximateDigits Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open scoped ENNReal

noncomputable section

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example (E : CoPset) (D : Model) (oracle : Val rT)
    (h : ∀ n : ℕ, ⊢ tglWp E pl(&oracle.fst #int ((n + 1 : ℕ) : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (D.approximation n)⌝)))
    (F : Bool → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (RealCoin.credit D.probability F) ∗ R -∗
      tglWp E pl(&Occil.Constants.fromApproximateDigits #int (D.base : ℤ) &oracle.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  isimp only [← RealCoin.lintegral_law] at Hcredit
  iapply ((fromApproximateDigits_distSpec E D oracle h).wp F
    (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HR
  itrivial

private def zeroAbove : Model where
  base := 2
  atLeastTwo := by decide
  probability := 0
  approximation := fun _ => 1
  accurate := by intro n; simp

-- The callback deliberately retains a named free variable in an unused branch.
private def oracle {rT : Type _} : Val rT :=
  ⟨pl(fun k, if #false then source k else #1), .lam (by is_lc), by is_lc⟩

example {rT : Type _} : (oracle (rT := rT)).fst.fv ≠ ∅ := by
  simp [oracle, Exp.fv, Exp.close, Exp.closeRec]

omit [ProbLangDist.IsUniformInt rT] in
private theorem oracle_spec (E : CoPset) (n : ℕ) :
    ⊢ tglWp E pl(&(oracle (rT := rT)).fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int 1⌝)) := by
  twp_pures
  twp_value
  imodintro
  ipureintro
  rfl

example (E : CoPset) : IsDistSpec (GF := GF) E
    pl(&Occil.Constants.fromApproximateDigits #2 &(oracle (rT := rT)).fst #())
    (RealCoin.law 0) Val.bool :=
  fromApproximateDigits_distSpec E zeroAbove oracle (fun n => oracle_spec E (n + 1))

example : RealCoin.credit zeroAbove.probability (fun b => if b then ∞ else 7) = 7 := by
  simp [zeroAbove, RealCoin.credit, RealCoin.pmf]

#print axioms twp_fromApproximateDigits
#print axioms fromApproximateDigits_distSpec
