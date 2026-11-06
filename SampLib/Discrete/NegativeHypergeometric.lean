import SampLib.Discrete.Hypergeometric
import SampLib.Core.SupportedSpec
import Samplers.Discrete.Urns

/-! # Failures before marked draws without replacement

Read a uniformly permuted labelled urn until the requested marked ball appears.
The first-color partition supplies the finite-population expectation recurrence.
-/

open Set ProbLang
open scoped ENNReal

namespace SampLib.NegativeHypergeometric

noncomputable section

section mathematics

open MeasureTheory Measure SampleWithoutReplacement

/-- Count unmarked entries before the requested marked entry. -/
def failures : ℕ → List Bool → ℕ
  | 0, _ => 0
  | _, [] => 0
  | r + 1, true :: xs => failures r xs
  | r + 1, false :: xs => failures (r + 1) xs + 1

/-- Uniform random ordering of the input positions, decoded to their values. -/
def wordLaw (xs : List Bool) : Measure (List Bool) :=
  (SampleWithoutReplacement.law xs xs.length).map (selected xs xs.length)

instance (xs : List Bool) : IsProbabilityMeasure (wordLaw xs) := by
  let : Fact (xs.length ≤ xs.length) := ⟨le_rfl⟩
  constructor
  rw [wordLaw, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
  simp

/-- Negative-hypergeometric count from a uniform ordering of labelled balls. -/
def law (r ones zeros : ℕ) : Measure ℕ :=
  (wordLaw (Hypergeometric.urn ones zeros)).map (failures r)

instance (r ones zeros : ℕ) : IsProbabilityMeasure (law r ones zeros) where
  measure_univ := by
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

@[simp] theorem expectation_zero (ones zeros : ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ k, F k ∂law 0 ones zeros = F 0 := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  simp [failures]

/-- Every position is equally likely to be first in a uniform ordering. -/
theorem word_expectation (xs : List Bool) (h : xs ≠ []) (F : List Bool → ℝ≥0∞) :
    ∫⁻ ys, F ys ∂wordLaw xs =
      (∑ i : Fin xs.length, ∫⁻ ys, F (xs.get i :: ys) ∂wordLaw (xs.eraseIdx i)) /
        xs.length := by
  cases xs with
  | nil => exact (h rfl).elim
  | cons x xs =>
      rw [wordLaw, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
      change (∫⁻ t, F (selected (x :: xs) (xs.length + 1) t)
        ∂SampleWithoutReplacement.law (x :: xs) (xs.length + 1)) = _
      rw [SampleWithoutReplacement.expectation]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [wordLaw, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
      simp only [selected]
      rw [show ((x :: xs).eraseIdx i.val).length = xs.length from by
        simpa using List.length_eraseIdx_of_lt i.isLt]

private theorem erase_true (ones zeros i : ℕ) (hi : i < ones) :
    (Hypergeometric.urn ones zeros).eraseIdx i = Hypergeometric.urn (ones - 1) zeros := by
  unfold Hypergeometric.urn
  rw [List.eraseIdx_append_of_lt_length (l := List.replicate ones true) (by simpa using hi)]
  simp [List.eraseIdx_replicate, hi]

private theorem erase_false (ones zeros i : ℕ) (hi : ones ≤ i) (hib : i < ones + zeros) :
    (Hypergeometric.urn ones zeros).eraseIdx i = Hypergeometric.urn ones (zeros - 1) := by
  have hz : i - ones < zeros := by omega
  unfold Hypergeometric.urn
  rw [List.eraseIdx_append_of_length_le (l := List.replicate ones true) (by simpa using hi)]
  simp [List.eraseIdx_replicate, hz]

/-- Partition permutations according to the first marked or unmarked ball. -/
theorem expectation (r ones zeros : ℕ) (ho : 0 < ones) (F : ℕ → ℝ≥0∞) :
    ∫⁻ k, F k ∂law (r + 1) ones zeros =
      ((ones : ℝ≥0∞) * (∫⁻ k, F k ∂law r (ones - 1) zeros) +
        (zeros : ℝ≥0∞) * (∫⁻ k, F (k + 1) ∂law (r + 1) ones (zeros - 1))) /
          (ones + zeros) := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  rw [word_expectation _ (List.ne_nil_of_length_pos (by
    simpa using (show 0 < ones + zeros by omega)))]
  have hstep (i : Fin (Hypergeometric.urn ones zeros).length) :
      (∫⁻ ys, F (failures (r + 1) ((Hypergeometric.urn ones zeros).get i :: ys))
        ∂wordLaw ((Hypergeometric.urn ones zeros).eraseIdx i)) =
      if i.val < ones then ∫⁻ k, F k ∂law r (ones - 1) zeros
      else ∫⁻ k, F (k + 1) ∂law (r + 1) ones (zeros - 1) := by
    by_cases hi : i.val < ones
    · have hget : (Hypergeometric.urn ones zeros).get i = true := by
        rw [List.get_eq_getElem]
        simp [Hypergeometric.urn, hi]
      simp only [hi, ite_true, hget, failures]
      rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
      rw [erase_true ones zeros i hi]
    · have hib : i.val < ones + zeros := by simpa using i.isLt
      have hget : (Hypergeometric.urn ones zeros).get i = false := by
        rw [List.get_eq_getElem]
        simp [Hypergeometric.urn, List.getElem_append, hi]
      simp only [hi, ite_false, hget, failures]
      rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
      rw [erase_false ones zeros i (by omega) hib]
  simp_rw [hstep]
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < ones then
    ∫⁻ k, F k ∂law r (ones - 1) zeros else ∫⁻ k, F (k + 1) ∂law (r + 1) ones (zeros - 1))]
  simp only [Hypergeometric.urn_length]
  rw [Finset.sum_range_add]
  simp [Finset.sum_ite_of_true, Nat.not_lt.mpr (Nat.le_add_right ones _), nsmul_eq_mul]

/-- Credit after the first color in the permuted urn. -/
def continuation (r ones zeros : ℕ) (F : ℕ → ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then ∫⁻ k, F k ∂law r (ones - 1) zeros
  else ∫⁻ k, F (k + 1) ∂law (r + 1) ones (zeros - 1)

/-- The first marked/unmarked partition is the input coin's expectation. -/
theorem expectation_coin (r ones zeros : ℕ) (ho : 0 < ones) (F : ℕ → ℝ≥0∞) :
    ∫⁻ b, continuation r ones zeros F b ∂RealCoin.law (Urn.bias ones zeros) =
      ∫⁻ k, F k ∂law (r + 1) ones zeros := by
  have ht : 0 < ones + zeros := by omega
  rw [RealCoin.lintegral_law, RealCoin.credit, Urn.pmf_true ones zeros ht,
    Urn.pmf_false ones zeros ht, expectation r ones zeros ho]
  simp only [continuation, ite_true, Bool.false_eq_true, ite_false,
    ENNReal.div_eq_inv_mul]
  ring

private theorem possible_failure (ones zeros : ℕ) (ho : 0 < ones) :
    ∀ᵐ b ∂RealCoin.law (Urn.bias ones zeros), b = false → 0 < zeros := by
  by_cases hz : zeros = 0
  · subst zeros
    have hb : Urn.bias ones 0 = 1 := by
      apply Subtype.ext
      simp [Urn.bias, ho, RationalCoin.bias, ho.ne']
    simp [hb, RealCoin.law, RealCoin.pmf]
  · exact Filter.Eventually.of_forall fun _ _ => Nat.pos_of_ne_zero hz

end mathematics

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem valid_test (r ones : ℕ) (h : r ≤ ones) :
    decide ((ones : ℤ) < (r : ℤ)) = false := decide_eq_false (by omega)

private theorem pred_cast (n : ℕ) (h : 0 < n) :
    (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) := by omega

/-- Finite urn execution, with the sampled color supplying the recursive domain. -/
theorem twp_negativeHypergeometric (E : CoPset) (r ones zeros : ℕ) (h : r ≤ ones)
    (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ k, F k ∂law r ones zeros) -∗
      tglWp E pl(&Occil.DiscreteExtra.negativeHypergeometric #int (r : ℤ)
        #int (ones : ℤ) #int (zeros : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k))) := by
  induction zeros using Nat.strong_induction_on generalizing r ones F with
  | h zeros ihz =>
    induction r generalizing ones F with
    | zero =>
      iintro Hcredit
      twp_pures
      twp_value
      imodintro
      iexists 0
      isimp only [expectation_zero] at Hcredit
      iframe Hcredit
      itrivial
    | succ r ihr =>
      have ho : 0 < ones := by omega
      have ht : 0 < ones + zeros := by omega
      have hcoin : IsDistSpec (GF := GF) E
          pl(&Occil.rationalCoin #int (ones : ℤ) #int ((ones : ℤ) + zeros))
          (RealCoin.law (Urn.bias ones zeros)) Val.bool := by
        simpa only [Urn.bias, dite_eq_left ht, Nat.cast_add] using
          RationalCoin.rationalCoin_distSpec (GF := GF) E ones (ones + zeros)
            (by omega) (by omega) (by omega)
      iintro Hcredit
      twp_pures
      rw [valid_test (r + 1) ones h]
      iterate 4 twp_pure
      simp only [RationalCoin.rationalCoin_closeRec, RationalCoin.rationalCoin_openRec]
      twp_bind pl(&Occil.rationalCoin #int (ones : ℤ) #int ((ones : ℤ) + zeros))
      isimp only [← expectation_coin r ones zeros ho F] at Hcredit
      iapply (hcoin.wp_supported (fun b => b = false → 0 < zeros)
        ((Set.to_countable _).measurableSet) (possible_failure ones zeros ho)
        (continuation r ones zeros F) (measurable_of_countable _) _) $$ Hcredit
      iintro %b %hb Hcredit
      cases b
      · have hz : 0 < zeros := hb rfl
        iterate 2 twp_pure
        rw [pred_cast zeros hz]
        twp_bind pl(&Occil.DiscreteExtra.negativeHypergeometric #int ((r + 1 : ℕ) : ℤ)
          #int (ones : ℤ) #int ((zeros - 1 : ℕ) : ℤ))
        iapply tglWp_wand
        isplitl [Hcredit]
        · isimp only [continuation, Bool.false_eq_true, ite_false] at Hcredit
          iapply (ihz (zeros - 1) (by omega) (r + 1) ones h (fun k => F (k + 1))) $$ Hcredit
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
      · iterate 3 twp_pure
        rw [Nat.cast_add_one, add_sub_cancel_right, pred_cast ones ho]
        twp_bind pl(&Occil.DiscreteExtra.negativeHypergeometric #int (r : ℤ)
          #int ((ones - 1 : ℕ) : ℤ) #int (zeros : ℤ))
        iapply (tglWp_mono fun _ => tglWp_value)
        isimp only [continuation, ite_true] at Hcredit
        iapply (ihr (ones - 1) (by omega) F) $$ Hcredit

/-- Typed negative-hypergeometric law for every feasible requested success count. -/
theorem negativeHypergeometric_distSpec (E : CoPset) (r ones zeros : ℕ) (h : r ≤ ones) :
    IsDistSpec (GF := GF) E pl(&Occil.DiscreteExtra.negativeHypergeometric #int (r : ℤ)
      #int (ones : ℤ) #int (zeros : ℤ)) (law r ones zeros)
      (fun k : ℕ => Val.int (k : ℤ)) where
  spec F _ := wand_entails (twp_negativeHypergeometric E r ones zeros h F)

end specification

end

end SampLib.NegativeHypergeometric
