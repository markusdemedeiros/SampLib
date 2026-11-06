import SampLib.Samplers.ContinuedLogarithm

open ProbLang
open scoped ENNReal

namespace ExactFactoriesReview015

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
theorem frame {E : CoPset} {e : Exp rT} {μ : MeasureTheory.Measure Bool}
    [MeasureTheory.IsProbabilityMeasure μ]
    (h : IsDistSpec (GF := GF) E e μ Val.bool) (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂μ) ∗ I -∗ tglWp E e
      (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply (h.wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HI
  itrivial

example (E : CoPset) (a : ℕ → ContinuedLogarithm.Coefficient) (start : ℕ)
    (coefficient : Val rT)
    (horacle : ∀ i, CriticalCoin.Reachable (ContinuedLogarithm.coefficients a) start i →
      ⊢ tglWp E pl(&coefficient.fst #int (i : ℤ))
        (fun v : Val rT => iprop(⌜v = ContinuedLogarithm.encodeCoefficient (a i)⌝)))
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (ContinuedLogarithm.continuedLogarithm_distSpec E a start coefficient horacle) F I

private def terminal (n : ℕ) : ℕ → ContinuedLogarithm.Coefficient := fun _ => ⟨n, true⟩

private def terminalCode {rT : Type} (n : ℕ) : Val rT :=
  ⟨pl(fun i, (#int (n : ℤ), #true)), .lam (by is_lc), by is_lc⟩

omit [ProbLangDist.IsUniformInt rT] in
private theorem terminal_spec (E : CoPset) (n i : ℕ) :
    ⊢ tglWp E pl(&(terminalCode (rT := rT) n).fst #int (i : ℤ))
      (fun v : Val rT => iprop(⌜v = ContinuedLogarithm.encodeCoefficient (terminal n i)⌝)) := by
  twp_pures
  twp_value
  imodintro
  ipureintro
  rfl

example (E : CoPset) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (ContinuedLogarithm.continuedLogarithm_distSpec E (terminal 3) 1 (terminalCode 3)
    (fun i _ => terminal_spec E 3 i)) F I

example (E : CoPset) (I : IProp GF) :=
  frame (ContinuedLogarithm.continuedLogarithm_distSpec E (terminal 0) 1 (terminalCode 0)
    (fun i _ => terminal_spec E 0 i)) (fun b => if b then 0 else ∞) I

private theorem terminal_zero : ContinuedLogarithm.bias (terminal 0) 1 = 1 := by
  rw [ContinuedLogarithm.bias, CriticalCoin.bias_last _ _ rfl]
  apply Subtype.ext
  simp [ContinuedLogarithm.coefficients, terminal, ContinuedLogarithm.Coefficient.critical,
    RationalCoin.bias]

example : (ContinuedLogarithm.bias (terminal 3) 1 : ℝ) = 1 / 8 := by
  rw [ContinuedLogarithm.bias, CriticalCoin.bias_last _ _ rfl]
  norm_num [ContinuedLogarithm.coefficients, terminal,
    ContinuedLogarithm.Coefficient.critical, RationalCoin.bias]

example : RealCoin.credit (ContinuedLogarithm.bias (terminal 0) 1)
    (fun b => if b then 0 else ∞) = 0 := by
  simp [terminal_zero, RealCoin.credit, RealCoin.pmf]

private def infinite : ℕ → ContinuedLogarithm.Coefficient := fun _ => ⟨0, false⟩

private def infiniteCode {rT : Type} : Val rT :=
  ⟨pl(fun i, (#0, #false)), .lam (by is_lc), by is_lc⟩

omit [ProbLangDist.IsUniformInt rT] in
private theorem infinite_spec (E : CoPset) (i : ℕ) :
    ⊢ tglWp E pl(&(infiniteCode (rT := rT)).fst #int (i : ℤ))
      (fun v : Val rT => iprop(⌜v = ContinuedLogarithm.encodeCoefficient (infinite i)⌝)) := by
  twp_pures
  twp_value
  imodintro
  ipureintro
  rfl

example (E : CoPset) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (ContinuedLogarithm.continuedLogarithm_distSpec E infinite 1 infiniteCode
    (fun i _ => infinite_spec E i)) F I

private def unbounded (i : ℕ) : ContinuedLogarithm.Coefficient := ⟨i, false⟩

private def unboundedCode {rT : Type} : Val rT :=
  ⟨pl(fun i, (i, #false)), .lam (by is_lc), by is_lc⟩

omit [ProbLangDist.IsUniformInt rT] in
private theorem unbounded_spec (E : CoPset) (i : ℕ) :
    ⊢ tglWp E pl(&(unboundedCode (rT := rT)).fst #int (i : ℤ))
      (fun v : Val rT => iprop(⌜v = ContinuedLogarithm.encodeCoefficient (unbounded i)⌝)) := by
  twp_pures
  twp_value
  imodintro
  ipureintro
  rfl

example (E : CoPset) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (ContinuedLogarithm.continuedLogarithm_distSpec E unbounded 1 unboundedCode
    (fun i _ => unbounded_spec E i)) F I

#print axioms ContinuedLogarithm.continuedLogarithm_distSpec
#print axioms CriticalCoin.distSpec_of_finite
#print axioms CriticalCoin.expectation
#print axioms CriticalCoin.credit_tendsto
#print axioms CriticalCoin.bias_recurrence

end

end ExactFactoriesReview015
