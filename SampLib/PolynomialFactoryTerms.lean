import SampLib.PolynomialFactoryCheck

/-! Exact execution of one power-basis to Bernstein coefficient conversion. -/

open ProbLang

namespace SampLib.PolynomialFactory

open FactoryFractions

def term (xs : List Fraction) (n k j : ℕ) : ℚ :=
  (input xs j).value * ((Nat.choose k j : ℚ) / Nat.choose n j)

def sumFrom (xs : List Fraction) (n k j : ℕ) : ℕ → ℚ
  | 0 => 0
  | steps + 1 => term xs n k j + sumFrom xs n k (j + 1) steps

def cutoff (xs : List Fraction) (k : ℕ) : ℕ := min xs.length (k + 1)

theorem sumFrom_eq (xs : List Fraction) (n k j steps : ℕ) :
    sumFrom xs n k j steps = ∑ i ∈ Finset.range steps, term xs n k (j + i) := by
  induction steps generalizing j with
  | zero => simp [sumFrom]
  | succ steps IH =>
    rw [sumFrom, Finset.sum_range_succ']
    simp only [IH, Nat.add_assoc, Nat.add_comm 1, Nat.add_zero]
    exact add_comm _ _

theorem sumFrom_coefficient (xs : List Fraction) (n k : ℕ) :
    sumFrom xs n k 0 (cutoff xs k) = coefficient xs n k := by
  rw [sumFrom_eq]
  simp only [Nat.zero_add, coefficient]
  apply Finset.sum_subset
  · exact Finset.range_mono (Nat.min_le_left _ _)
  · intro j hj hnot
    have hjx := Finset.mem_range.mp hj
    have hjc : cutoff xs k ≤ j := by simpa using hnot
    have hjk : k < j := by simp only [cutoff] at hjc; omega
    simp [term, Nat.choose_eq_zero_of_lt hjk]

/-- The exact positive-denominator ratio passed to fraction multiplication. -/
def chooseFraction (n k j : ℕ) (hj : j ≤ n) : Fraction :=
  ⟨Nat.choose k j, Nat.choose n j, Nat.choose_pos hj⟩

private theorem chooseFraction_value (n k j : ℕ) (hj : j ≤ n) :
    (chooseFraction n k j hj).value = (Nat.choose k j : ℚ) / Nat.choose n j := by
  simp [chooseFraction, Fraction.value, Rat.mkRat_eq_div]

private theorem source_term_value (xs : List Fraction) (n k j : ℕ)
    (hj : j < xs.length) (hjn : j ≤ n) :
    (xs.get ⟨j, hj⟩).value * (chooseFraction n k j hjn).value = term xs n k j := by
  rw [chooseFraction_value]
  simp [term, input, List.getElem?_eq_getElem hj]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- One exact arithmetic update, preserving an arbitrary continuation. -/
private theorem twp_next_term (E : CoPset) (xs : List Fraction) (n k j : ℕ)
    (hj : j < xs.length) (hjk : j ≤ k) (hjn : j ≤ n) (acc : ℚ)
    (Φ : Val rT → IProp GF) :
    tglWp E pl(&(Syntax.terms xs n k) #int ((j + 1 : ℕ) : ℤ)
      &(encode (acc + term xs n k j)).fst) Φ ⊢
      tglWp E (Syntax.termsCase xs n k j acc) Φ := by
  have htest : (decide ((degree xs : ℤ) < j) || decide ((k : ℤ) < j)) = false := by
    have hd : j ≤ degree xs := by simp only [degree]; omega
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
    exact ⟨by exact_mod_cast (not_lt.mpr hd), by exact_mod_cast (not_lt.mpr hjk)⟩
  iintro H
  isimp only [Syntax.termsCase, ClosedExp.closeRec]
  twp_pures
  rw [htest]
  twp_pure
  twp_bind pl(&Occil.getAt &(listVal (Fraction.encode (rT := rT)) xs).fst #int (j : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply twp_getAt E Fraction.encode xs ⟨j, hj⟩
  iintro %v %hv
  subst v
  isimp only [Exp.ofVal]
  iapply (Syntax.twp_lookup_return E xs n k j acc (xs.get ⟨j, hj⟩) Φ)
  twp_bind pl(&Occil.FactoryExtra.choose #int (k : ℤ) #int (j : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply FactoryChoose.twp_choose E k j
  iintro %v %hv
  subst v
  isimp only [Exp.ofVal]
  iapply (Syntax.twp_numerator_return E xs n k j acc (xs.get ⟨j, hj⟩) (Nat.choose k j) Φ)
  twp_bind pl(&Occil.FactoryExtra.choose #int (n : ℤ) #int (j : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply FactoryChoose.twp_choose E n j
  iintro %v %hv
  subst v
  isimp only [Exp.ofVal]
  iapply (Syntax.twp_denominator_return E xs n k j acc (xs.get ⟨j, hj⟩)
    (Nat.choose k j) (Nat.choose n j) Φ)
  let ratio := chooseFraction n k j hjn
  twp_bind pl(&Occil.FactoryExtra.multiplyFraction
    &(xs.get ⟨j, hj⟩).encode.fst &ratio.encode.fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_multiplyFraction E (xs.get ⟨j, hj⟩) ratio
  iintro %v %hv
  subst v
  isimp only [Exp.ofVal]
  iapply (Syntax.twp_product_return E xs n k j acc
    ((xs.get ⟨j, hj⟩).value * ratio.value) Φ)
  twp_bind pl(&Occil.FactoryExtra.addFraction
    &(Fraction.ofRat acc).encode.fst
    &(Fraction.ofRat ((xs.get ⟨j, hj⟩).value * ratio.value)).encode.fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_addFraction
  iintro %v %hv
  subst v
  twp_pure
  have hvalue : (xs.get ⟨j, hj⟩).value * ratio.value = term xs n k j :=
    source_term_value xs n k j hj hjn
  isimp only [Fraction.value_ofRat, hvalue, Exp.ofVal,
    ClosedExp.openRec, ClosedExp.closeRec, Syntax.termsValue_fst]
  isimp only [Nat.cast_add_one] at H
  iexact H

theorem twp_terms (E : CoPset) (xs : List Fraction) (hxs : xs ≠ [])
    (n k j steps : ℕ) (hn : degree xs ≤ n) (hsteps : j + steps = cutoff xs k)
    (acc : ℚ) :
    ⊢ tglWp E pl(&(Syntax.terms xs n k) #int (j : ℤ) &(encode acc).fst)
      (fun v : Val rT => iprop(⌜v = encode (acc + sumFrom xs n k j steps)⌝)) := by
  induction steps generalizing j acc with
  | zero =>
    have hstop : degree xs < j ∨ k < j := by
      have hx := List.length_pos_iff.mpr hxs
      simp only [cutoff, degree] at *
      omega
    have htest : (decide ((degree xs : ℤ) < j) || decide ((k : ℤ) < j)) = true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      omega
    iapply (Syntax.twp_terms_open E xs n k j acc _)
    isimp only [Syntax.termsCase, ClosedExp.closeRec]
    twp_pures
    rw [htest]
    twp_pures
    twp_value
    imodintro
    ipureintro
    simp only [sumFrom, add_zero]
    rfl
  | succ steps IH =>
    have hj : j < xs.length := by
      have hc := Nat.min_le_left xs.length (k + 1)
      simp only [cutoff] at hsteps
      omega
    have hjk : j ≤ k := by
      have hc := Nat.min_le_right xs.length (k + 1)
      simp only [cutoff] at hsteps
      omega
    have hjn : j ≤ n := by simp only [degree] at hn; omega
    iapply (Syntax.twp_terms_open E xs n k j acc _)
    iapply (twp_next_term E xs n k j hj hjk hjn acc _)
    have hrec := IH (j + 1) (by omega) (acc + term xs n k j)
    simp only [add_assoc] at hrec
    isimp only [sumFrom, add_assoc]
    iapply hrec

/-- Convert one coefficient, with exact zero terms beyond the lookup range omitted. -/
theorem twp_coefficient (E : CoPset) (xs : List Fraction) (hxs : xs ≠ [])
    (n k : ℕ) (hn : degree xs ≤ n) :
    ⊢ tglWp E pl(&(Syntax.coefficient xs n) #int (k : ℤ))
      (fun v : Val rT => iprop(⌜v = encode (coefficient xs n k)⌝)) := by
  iapply (Syntax.twp_coefficient_open E xs n k _)
  have h := twp_terms (rT := rT) (GF := GF) E xs hxs n k 0 (cutoff xs k) hn (by simp) 0
  simp only [sumFrom_coefficient, zero_add] at h
  iapply h

end specification

end SampLib.PolynomialFactory
