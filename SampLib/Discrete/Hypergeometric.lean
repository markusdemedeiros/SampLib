import SampLib.Common.Laws.Urn
import SampLib.Combinatorial.SampleWithoutReplacement
import Metrology.Iris.LocalBI

/-! # Hypergeometric sampling

The law counts marked balls in a uniform ordered selection of distinct labelled
balls. Partitioning those selections by the first ball gives the urn recurrence.
-/

open Set ProbLang
open scoped ENNReal

namespace SampLib.Hypergeometric

noncomputable section

section mathematics

open MeasureTheory Measure
open SampleWithoutReplacement

/-- A labelled urn with the marked balls first. -/
def urn (ones zeros : ℕ) : List Bool :=
  List.replicate ones true ++ List.replicate zeros false

@[simp] theorem urn_length (ones zeros : ℕ) : (urn ones zeros).length = ones + zeros := by
  simp [urn]

/-- Number of marked balls in a uniform ordered selection without replacement. -/
def law (n ones zeros : ℕ) : Measure ℕ :=
  (SampleWithoutReplacement.law (urn ones zeros) n).map
    (fun t => (selected (urn ones zeros) n t).count true)

instance (n ones zeros : ℕ) [Fact (n ≤ ones + zeros)] :
    IsProbabilityMeasure (law n ones zeros) := by
  let : Fact (n ≤ (urn ones zeros).length) := ⟨by simpa using Fact.out⟩
  unfold law
  constructor
  rw [Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
  simp

@[simp] theorem expectation_zero (ones zeros : ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ k, F k ∂law 0 ones zeros = F 0 := by
  let : Fact (0 ≤ (urn ones zeros).length) := ⟨Nat.zero_le _⟩
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  simp [selected]

private theorem urn_erase_true (ones zeros i : ℕ) (hi : i < ones) :
    (urn ones zeros).eraseIdx i = urn (ones - 1) zeros := by
  unfold urn
  rw [List.eraseIdx_append_of_lt_length (l := List.replicate ones true) (by simpa using hi)]
  simp [List.eraseIdx_replicate, hi]

private theorem urn_erase_false (ones zeros i : ℕ) (hi : ones ≤ i) (hib : i < ones + zeros) :
    (urn ones zeros).eraseIdx i = urn ones (zeros - 1) := by
  have hz : i - ones < zeros := by omega
  unfold urn
  rw [List.eraseIdx_append_of_length_le (l := List.replicate ones true) (by simpa using hi)]
  simp [List.eraseIdx_replicate, hz]

/-- Partition the uniform labelled selections by the color of the first ball. -/
theorem expectation (n ones zeros : ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ k, F k ∂law (n + 1) ones zeros =
      ((ones : ℝ≥0∞) * (∫⁻ k, F (k + 1) ∂law n (ones - 1) zeros) +
        (zeros : ℝ≥0∞) * (∫⁻ k, F k ∂law n ones (zeros - 1))) / (ones + zeros) := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    SampleWithoutReplacement.expectation]
  have hstep (i : Fin (urn ones zeros).length) :
      (∫⁻ t, F ((selected (urn ones zeros) (n + 1) ⟨i, t⟩).count true)
        ∂SampleWithoutReplacement.law ((urn ones zeros).eraseIdx i) n) =
      if i.val < ones then ∫⁻ k, F (k + 1) ∂law n (ones - 1) zeros
      else ∫⁻ k, F k ∂law n ones (zeros - 1) := by
    simp only [selected]
    by_cases hi : i.val < ones
    · have hget : (urn ones zeros).get i = true := by
        rw [List.get_eq_getElem]
        simp [urn, hi]
      simp only [hi, ite_true, hget, List.count_cons_self]
      rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
      rw [urn_erase_true ones zeros i hi]
    · have hib : i.val < ones + zeros := by simpa using i.isLt
      have hget : (urn ones zeros).get i = false := by
        rw [List.get_eq_getElem]
        simp [urn, List.getElem_append, hi]
      simp only [hi, ite_false, hget, List.count_cons_of_ne Bool.false_ne_true]
      rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
      rw [urn_erase_false ones zeros i (by omega) hib]
  simp_rw [hstep]
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < ones then
    ∫⁻ k, F (k + 1) ∂law n (ones - 1) zeros else ∫⁻ k, F k ∂law n ones (zeros - 1))]
  simp only [urn_length]
  rw [Finset.sum_range_add]
  simp [Finset.sum_ite_of_true, Nat.not_lt.mpr (Nat.le_add_right ones _), nsmul_eq_mul]

/-- Impossible colors receive infinite credit, making their proof branches vacuous. -/
def continuation (n ones zeros : ℕ) (F : ℕ → ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then if ones = 0 then ∞ else ∫⁻ k, F (k + 1) ∂law n (ones - 1) zeros
  else if zeros = 0 then ∞ else ∫⁻ k, F k ∂law n ones (zeros - 1)

theorem expectation_coin (n ones zeros : ℕ) (h : 0 < ones + zeros) (F : ℕ → ℝ≥0∞) :
    ∫⁻ b, continuation n ones zeros F b ∂RealCoin.law (Urn.bias ones zeros) =
      ∫⁻ k, F k ∂law (n + 1) ones zeros := by
  rw [RealCoin.lintegral_law, RealCoin.credit, Urn.pmf_true ones zeros h,
    Urn.pmf_false ones zeros h, expectation]
  simp only [continuation, ite_true, Bool.false_eq_true, ite_false]
  by_cases ho : ones = 0 <;> by_cases hz : zeros = 0 <;>
    simp [ho, hz, ENNReal.div_eq_inv_mul, mul_add, mul_assoc]

end mathematics

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem valid_test (n ones zeros : ℕ) (h : n ≤ ones + zeros) :
    decide ((ones : ℤ) + zeros < n) = false := by
  exact decide_eq_false (by omega)

private theorem pred_cast (n : ℕ) (h : 0 < n) :
    (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) := by omega

/-- Finite urn sampling, including exhausted colors and the empty zero-draw urn. -/
theorem twp_hypergeometric (E : CoPset) (n ones zeros : ℕ) (h : n ≤ ones + zeros)
    (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ k, F k ∂law n ones zeros) -∗
      tglWp E pl(&Occil.hypergeometric #int (n : ℤ) #int (ones : ℤ) #int (zeros : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k))) := by
  induction n generalizing ones zeros F with
  | zero =>
    iintro Hcredit
    twp_pures
    twp_value
    imodintro
    iexists 0
    isimp only [expectation_zero] at Hcredit
    iframe Hcredit
    itrivial
  | succ n ih =>
    have ht : 0 < ones + zeros := by omega
    have hcoin : IsDistSpec (GF := GF) E
        pl(&Occil.rationalCoin #int (ones : ℤ) #int ((ones : ℤ) + zeros))
        (RealCoin.law (Urn.bias ones zeros)) Val.bool := by
      simpa only [Urn.bias, dite_eq_left ht, Nat.cast_add] using
        RationalCoin.rationalCoin_distSpec (GF := GF) E ones (ones + zeros)
          (by omega) (by omega) (by omega)
    iintro Hcredit
    twp_pures
    simp only [Bool.false_or, valid_test (n + 1) ones zeros h]
    iterate 4 twp_pure
    simp only [RationalCoin.rationalCoin_closeRec, RationalCoin.rationalCoin_openRec]
    twp_bind pl(&Occil.rationalCoin #int (ones : ℤ) #int ((ones : ℤ) + zeros))
    isimp only [← expectation_coin n ones zeros ht F] at Hcredit
    iapply (hcoin.wp (continuation n ones zeros F) (measurable_of_countable _) _) $$ Hcredit
    iintro %b Hcredit
    cases b
    · by_cases hz : zeros = 0
      · isimp only [continuation, Bool.false_eq_true, ite_false, hz, ite_true] at Hcredit
        iexfalso
        iapply (ErrorCredit.contradict (ε := ∞) le_top) $$ Hcredit
      · iterate 3 twp_pure
        rw [Nat.cast_add_one, add_sub_cancel_right, pred_cast zeros (by omega)]
        simp only [Exp.ofVal]
        twp_bind pl(&Occil.hypergeometric #int (n : ℤ) #int (ones : ℤ)
          #int ((zeros - 1 : ℕ) : ℤ))
        iapply tglWp_wand
        isplitl [Hcredit]
        · isimp only [continuation, Bool.false_eq_true, ite_false, hz] at Hcredit
          iapply (ih ones (zeros - 1) (by omega) F) $$ Hcredit
        iintro %v ⟨%k, %hv, Hcredit⟩
        iapply (tglWp_value (v := v))
        iexists k
        iframe Hcredit
        ipureintro
        exact hv
    · by_cases ho : ones = 0
      · isimp only [continuation, ite_true, ho, ite_false] at Hcredit
        iexfalso
        iapply (ErrorCredit.contradict (ε := ∞) le_top) $$ Hcredit
      · iterate 3 twp_pure
        rw [Nat.cast_add_one, add_sub_cancel_right, pred_cast ones (by omega)]
        simp only [Exp.ofVal]
        twp_bind pl(&Occil.hypergeometric #int (n : ℤ) #int ((ones - 1 : ℕ) : ℤ)
          #int (zeros : ℤ))
        iapply tglWp_wand
        isplitl [Hcredit]
        · isimp only [continuation, ite_true, ho, ite_false] at Hcredit
          iapply (ih (ones - 1) zeros (by omega) (fun k => F (k + 1))) $$ Hcredit
        iintro %v ⟨%k, %hv, Hcredit⟩
        subst v
        twp_pures
        twp_value
        imodintro
        iexists k + 1
        iframe Hcredit
        ipureintro
        apply Val.ext
        simp [add_comm]

/-- Typed hypergeometric law on the full feasible urn domain. -/
theorem hypergeometric_distSpec (E : CoPset) (n ones zeros : ℕ)
    [Fact (n ≤ ones + zeros)] :
    IsDistSpec (GF := GF) E
      pl(&Occil.hypergeometric #int (n : ℤ) #int (ones : ℤ) #int (zeros : ℤ))
      (law n ones zeros) (fun k : ℕ => Val.int (k : ℤ)) where
  spec F _ := wand_entails (twp_hypergeometric E n ones zeros Fact.out F)

end specification

end

end SampLib.Hypergeometric
