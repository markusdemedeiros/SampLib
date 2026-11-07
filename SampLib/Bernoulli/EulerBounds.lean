import SampLib.Bernoulli.Laws.EulerEnclosure
import SampLib.Constants.FromBounds
import SampLib.Bernoulli.Support.RealEnclosureEncoding
import Samplers.Constants.Exponential
import SampLib.Core.Syntax.ClosedExp
import Metrology.Iris.LocalBI

/-! # The concrete factorial-series gateway for Euler's number -/

open ProbLang

namespace SampLib.EulerEnclosure

@[pl_fold] private def accumulate {rT : Type _} (m : ℕ) : Exp rT := pl%
  rec addTerm k a d :=
    if k = #int (m : ℤ) then (k * a, (k * a + #1, k * d)) else
      let next := k + #1;
      addTerm next (a * next + #1) (d * next)

private instance accumulate_closed {rT : Type _} (m : ℕ) :
    ClosedExp (accumulate (rT := rT) m) where
  lc := by is_lc
  fv := by simp [accumulate, Exp.fv]

private theorem natural_test {rT : Type _} [BEq rT] (a b : ℕ) :
    ((BaseLit.int (a : ℤ) : BaseLit rT) == .int (b : ℤ)) = decide (a = b) := by
  change decide ((a : ℤ) = (b : ℤ)) = decide (a = b)
  exact decide_eq_decide.mpr (by omega)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

private theorem twp_accumulate (E : CoPset) (m k : ℕ) (hk : k ≤ m) :
    ⊢ tglWp E pl(&(accumulate m) #int (k : ℤ)
      #int (numerator k : ℤ) #int (k.factorial : ℤ))
      (fun v : Val rT => iprop(⌜v = RealEnclosure.encodeTriple
        ((m : ℤ) * numerator m, ((m : ℤ) * numerator m + 1, (m : ℤ) * m.factorial))⌝)) := by
  refine Nat.decreasingInduction ?_ ?_ hk
  · intro k hk IH
    iterate 5 twp_pure
    rw [natural_test k m, decide_eq_false (Nat.ne_of_lt hk)]
    iterate 6 twp_pure
    have h := IH
    simp only [numerator, Nat.factorial_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_one] at h
    simp only [mul_comm, Exp.ofVal] at h ⊢
    exact h
  · iterate 5 twp_pure
    rw [natural_test m m, decide_eq_true rfl]
    twp_pures
    twp_value
    imodintro
    ipureintro
    rfl

/-- The actual integer oracle returns the factorial enclosure at every requested index. -/
theorem twp_eBounds (E : CoPset) (n : ℕ) :
    ⊢ tglWp E pl(&Occil.Constants.eBounds #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = RealEnclosure.encodeInterval (interval n)⌝)) := by
  iterate 3 twp_pure
  rw [← Nat.cast_add_one]
  twp_pure
  have h := twp_accumulate (rT := rT) (GF := GF) E (n + 1) 0 (Nat.zero_le _)
  simp only [numerator, Nat.factorial_zero, Nat.cast_zero, Nat.cast_one] at h
  exact h

end specification

end SampLib.EulerEnclosure
