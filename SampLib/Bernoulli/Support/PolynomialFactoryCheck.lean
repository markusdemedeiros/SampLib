import SampLib.Bernoulli.Syntax.PolynomialFactoryLoops

/-! # Admissibility check of the polynomial factory

The source's exact admissibility check on a rational coefficient table.
-/

open ProbLang

namespace SampLib.PolynomialFactory

open FactoryFractions

def valid (xs : List Fraction) : Bool :=
  xs.all (fun a => decide (0 ≤ a.numerator ∧ a.numerator ≤ (a.denominator : ℤ)))

theorem valid_fraction (a : Fraction) :
    (0 ≤ a.numerator ∧ a.numerator ≤ (a.denominator : ℤ)) ↔ a.value ∈ Set.Icc 0 1 := by
  have hd : (0 : ℚ) < a.denominator := by exact_mod_cast a.positive
  simp only [Fraction.value, Rat.mkRat_eq_div, Set.mem_Icc]
  rw [le_div_iff₀ hd, div_le_iff₀ hd]
  simp only [zero_mul, one_mul]
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨by exact_mod_cast h0, by exact_mod_cast h1⟩
  · rintro ⟨h0, h1⟩
    exact ⟨by exact_mod_cast h0, by exact_mod_cast h1⟩

theorem valid_iff (xs : List Fraction) :
    valid xs = true ↔ ∀ a ∈ xs, a.value ∈ Set.Icc 0 1 := by
  simp [valid, List.all_eq_true, valid_fraction]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem twp_check (E : CoPset) (xs : List Fraction) :
    ⊢ tglWp E pl(&(Syntax.check (rT := rT)) &(listVal Fraction.encode xs).fst)
      (fun v : Val rT => iprop(⌜v = Val.bool (valid xs)⌝)) := by
  induction xs with
  | nil =>
    iapply (Syntax.twp_check_open E [] _)
    isimp only [Syntax.checkCase]
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    ipureintro
    rfl
  | cons a xs IH =>
    iapply (Syntax.twp_check_open E (a :: xs) _)
    isimp only [Syntax.checkCase]
    simp only [listVal, Fraction.encode]
    twp_pures
    by_cases ha : 0 ≤ a.numerator ∧ a.numerator ≤ (a.denominator : ℤ)
    · have htest : (decide (a.numerator < 0) ||
          decide ((a.denominator : ℤ) < a.numerator)) = false := by simp; omega
      rw [htest]
      iterate 2 twp_pure
      have hvalid : valid (a :: xs) = valid xs := by simp [valid, ha]
      rw [hvalid]
      isimp only [ClosedExp.openRec, ClosedExp.closeRec, Syntax.checkValue_fst, Exp.ofVal]
      iapply IH
    · have htest : (decide (a.numerator < 0) ||
          decide ((a.denominator : ℤ) < a.numerator)) = true := by simp; omega
      rw [htest]
      twp_pure
      twp_value
      imodintro
      ipureintro
      apply Val.ext
      simp [valid, ha]

end specification

end SampLib.PolynomialFactory
