import SampLib.Core.ListEncoding
import SampLib.Uniform.UniformInt
import Samplers.Combinatorial.Basic
import Metrology.Iris.LocalBI

/-! # Uniform subsets in input order

Every selection of positions of the requested size has equal weight. Enumerating
sublists retains position multiplicities when input values coincide.
-/

open Set ProbLang
open scoped ENNReal

namespace SampLib.SampleInOrder

noncomputable section

variable {α : Type _}
-- Only finitely many lists occur; the output uses the discrete measurable structure.
local instance : MeasurableSpace (List α) := ⊤

section mathematics

open MeasureTheory Measure

/-- Average over the position selections, with multiplicity. -/
def credit (xs : List α) (k : ℕ) (F : List α → ℝ≥0∞) : ℝ≥0∞ :=
  ((xs.sublistsLen k).map F).sum / xs.length.choose k

/-- Uniform position subsets, returned in input order. -/
def law (xs : List α) (k : ℕ) (_hk : k ≤ xs.length) : Measure (List α) :=
  (xs.length.choose k : ℝ≥0∞)⁻¹ • ((xs.sublistsLen k).map dirac).sum

private theorem sum_dirac_univ (ys : List (List α)) :
    (ys.map (dirac : List α → Measure (List α))).sum univ = ys.length := by
  induction ys with
  | nil => simp
  | cons y ys IH => simp [IH, add_comm]

instance (xs : List α) (k : ℕ) (hk : k ≤ xs.length) :
    IsProbabilityMeasure (law xs k hk) where
  measure_univ := by
    simp only [law, Measure.smul_apply, smul_eq_mul, sum_dirac_univ,
      List.length_sublistsLen]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast (Nat.choose_pos hk).ne') (by simp)

private theorem lintegral_sum_dirac (ys : List (List α)) (F : List α → ℝ≥0∞) :
    ∫⁻ y, F y ∂(ys.map dirac).sum = (ys.map F).sum := by
  induction ys with
  | nil => simp
  | cons y ys IH => simp [IH, lintegral_add_measure]

theorem lintegral_law (xs : List α) (k : ℕ) (hk : k ≤ xs.length)
    (F : List α → ℝ≥0∞) : ∫⁻ y, F y ∂law xs k hk = credit xs k F := by
  simp [law, credit, lintegral_smul_measure, lintegral_sum_dirac, div_eq_mul_inv, mul_comm]

@[simp] theorem credit_zero (xs : List α) (F : List α → ℝ≥0∞) :
    credit xs 0 F = F [] := by simp [credit]

private theorem choose_include (n k : ℕ) (hk : k ≤ n) :
    (k + 1 : ℝ≥0∞) / (n + 1) / n.choose k =
      ((n + 1).choose (k + 1) : ℝ≥0∞)⁻¹ := by
  have hn : (n + 1 : NNReal) ≠ 0 := by positivity
  have hc : (n.choose k : NNReal) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  have hd : ((n + 1).choose (k + 1) : NNReal) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.succ_le_succ hk)).ne'
  have h : ((k + 1 : ℕ) : NNReal) / (n + 1) / n.choose k =
      ((n + 1).choose (k + 1) : NNReal)⁻¹ := by
    field_simp
    exact_mod_cast (by simpa [mul_comm] using (Nat.add_one_mul_choose_eq n k).symm :
      (k + 1) * (n + 1).choose (k + 1) = (n + 1) * n.choose k)
  simpa only [ENNReal.coe_div hc, ENNReal.coe_div hn, ENNReal.coe_inv hd,
    ENNReal.coe_natCast, ENNReal.coe_add, ENNReal.coe_one, Nat.cast_add, Nat.cast_one]
    using congrArg (fun x : NNReal => (x : ℝ≥0∞)) h

private theorem choose_exclude (n k : ℕ) (hk : k + 1 ≤ n) :
    ((n - k : ℕ) : ℝ≥0∞) / (n + 1) / n.choose (k + 1) =
      ((n + 1).choose (k + 1) : ℝ≥0∞)⁻¹ := by
  have hn : (n + 1 : NNReal) ≠ 0 := by positivity
  have hc : (n.choose (k + 1) : NNReal) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hk).ne'
  have hd : ((n + 1).choose (k + 1) : NNReal) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : k + 1 ≤ n + 1)).ne'
  have h : ((n - k : ℕ) : NNReal) / (n + 1) / n.choose (k + 1) =
      ((n + 1).choose (k + 1) : NNReal)⁻¹ := by
    field_simp
    have he := Nat.choose_mul_succ_eq n (k + 1)
    have hs : n + 1 - (k + 1) = n - k := by omega
    rw [hs] at he
    exact_mod_cast (by simpa [mul_comm] using he.symm :
      (n - k) * (n + 1).choose (k + 1) = (n + 1) * n.choose (k + 1))
  simpa only [ENNReal.coe_div hc, ENNReal.coe_div hn, ENNReal.coe_inv hd,
    ENNReal.coe_natCast, ENNReal.coe_add, ENNReal.coe_one, Nat.cast_add, Nat.cast_one]
    using congrArg (fun x : NNReal => (x : ℝ≥0∞)) h

/-- The first position is kept in exactly `k+1` of the `n+1` equally likely ranks. -/
def rankCredit (x : α) (xs : List α) (k : ℕ) (F : List α → ℝ≥0∞)
    (r : ℕ) : ℝ≥0∞ :=
  if r < k + 1 then credit xs k (fun ys => F (x :: ys)) else credit xs (k + 1) F

/-- Pascal's partition of position subsets matches the two continuation branches. -/
theorem expectation (x : α) (xs : List α) (k : ℕ) (hk : k ≤ xs.length)
    (F : List α → ℝ≥0∞) :
    (∑ r ∈ Finset.range (xs.length + 1), rankCredit x xs k F r) /
      (xs.length + 1) = credit (x :: xs) (k + 1) F := by
  have hsum : (∑ r ∈ Finset.range (xs.length + 1), rankCredit x xs k F r) =
      (k + 1 : ℝ≥0∞) * credit xs k (fun ys => F (x :: ys)) +
        ((xs.length - k : ℕ) : ℝ≥0∞) * credit xs (k + 1) F := by
    rw [show xs.length + 1 = (k + 1) + (xs.length - k) by omega,
      Finset.sum_range_add]
    congr 1
    · simp only [rankCredit]
      rw [Finset.sum_congr rfl (fun r hr => ite_eq_left (Finset.mem_range.mp hr))]
      simp [nsmul_eq_mul]
    · simp [rankCredit, Nat.not_lt.mpr (Nat.le_add_right (k + 1) _), nsmul_eq_mul]
  rw [hsum]
  by_cases hfull : k = xs.length
  · subst k
    have hn : (xs.length + 1 : ℝ≥0∞) ≠ 0 := by positivity
    simp only [credit, List.sublistsLen_length, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, Nat.choose_self, Nat.cast_one, div_one,
      Nat.sub_self, Nat.cast_zero, zero_mul, List.length_cons]
    rw [mul_comm, ENNReal.mul_div_cancel_right hn (by simp)]
    simp [List.sublistsLen_of_length_lt (Nat.lt_succ_self xs.length)]
  · have hskip : k + 1 ≤ xs.length := by omega
    calc
      _ = ((k + 1 : ℝ≥0∞) / (xs.length + 1) / xs.length.choose k) *
          ((xs.sublistsLen k).map (fun ys => F (x :: ys))).sum +
          (((xs.length - k : ℕ) : ℝ≥0∞) / (xs.length + 1) /
            xs.length.choose (k + 1)) * ((xs.sublistsLen (k + 1)).map F).sum := by
        simp only [credit, div_eq_mul_inv]
        ring
      _ = _ := by
        rw [choose_include xs.length k hk, choose_exclude xs.length k hskip]
        simp only [credit, List.sublistsLen_succ_cons, List.map_append, List.sum_append,
          List.map_map, Function.comp_def, List.length_cons, div_eq_mul_inv]
        ring

end mathematics

@[pl_fold] private def draw {rT : Type _} : Exp rT := pl%
  rec go ys remaining needed :=
    if needed = #0 then inl(#()) else
    case! ys | inl(u) => fail | inr(p) =>
      if &Occil.uniformInt remaining < needed then
        inr((fst(p), go (snd(p)) (remaining - #1) (needed - #1)))
      else go (snd(p)) (remaining - #1) needed

private theorem encode_cons {rT : Type _} [ProbLangℝ rT] (encode : α → Val rT)
    (x : α) (ys : List α) :
    pl(inr(({(encode x).fst}, {Exp.ofVal (listVal encode ys)}))) =
      Exp.ofVal (listVal encode (x :: ys)) := by
  simp [Exp.ofVal, listVal]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_draw (E : CoPset) (encode : α → Val rT) (xs : List α)
    (k : ℕ) (hk : k ≤ xs.length) (F : List α → ℝ≥0∞) :
    ⊢ ↯ (credit xs k F) -∗
      tglWp E pl(&draw &(listVal encode xs).fst #int (xs.length : ℤ) #int (k : ℤ))
        (fun v : Val rT => iprop(∃ ys : List α,
          ⌜v = listVal encode ys⌝ ∗ ↯ (F ys))) := by
  induction xs generalizing k F with
  | nil =>
    have : k = 0 := by simpa using hk
    subst k
    iintro Hcredit
    twp_pures
    twp_value
    imodintro
    iexists []
    isimp only [credit_zero] at Hcredit
    iframe Hcredit
    ipureintro
    rfl
  | cons x xs IH =>
    cases k with
    | zero =>
      iintro Hcredit
      twp_pures
      twp_value
      imodintro
      iexists []
      isimp only [credit_zero] at Hcredit
      iframe Hcredit
      ipureintro
      rfl
    | succ k =>
      have hk' : k ≤ xs.length := by simpa using hk
      iintro Hcredit
      simp only [listVal]
      iterate 8 twp_pure
      simp only [UniformInt.uniformInt_openRec, UniformInt.uniformInt_closeRec,
        List.length_cons]
      twp_bind pl(&Occil.uniformInt #int ((xs.length + 1 : ℕ) : ℤ))
      iapply tglWp_wand
      isplitl [Hcredit]
      · iapply (UniformInt.twp_uniformInt E (xs.length + 1) (by omega)
          (rankCredit x xs k F))
        isimp only [← expectation x xs k hk' F] at Hcredit
        isimp only [Nat.cast_add, Nat.cast_one]
        iexact Hcredit
      iintro %v ⟨%r, %hv, %hr, Hcredit⟩
      subst v
      twp_pure
      by_cases hrk : r < k + 1
      · have hlt : (r : ℤ) < ((k + 1 : ℕ) : ℤ) := by exact_mod_cast hrk
        simp only [hlt, decide_true]
        iterate 4 twp_pure
        rw [Nat.cast_add_one, add_sub_cancel_right, Nat.cast_add_one,
          add_sub_cancel_right]
        twp_bind pl(&draw &(listVal encode xs).fst #int (xs.length : ℤ) #int (k : ℤ))
        iapply tglWp_wand
        isplitl [Hcredit]
        · isimp only [rankCredit, ite_eq_left hrk] at Hcredit
          iapply (IH k hk' (fun ys => F (x :: ys))) $$ Hcredit
        iintro %v ⟨%ys, %hv, Hcredit⟩
        subst v
        twp_pure
        rw [encode_cons]
        iapply (tglWp_value (v := listVal encode (x :: ys)))
        iexists x :: ys
        iframe Hcredit
        itrivial
      · have hnot : ¬(r : ℤ) < ((k + 1 : ℕ) : ℤ) := by exact_mod_cast hrk
        have hk'' : k + 1 ≤ xs.length := by omega
        simp only [hnot, decide_false]
        iterate 3 twp_pure
        rw [Nat.cast_add_one, add_sub_cancel_right]
        isimp only [rankCredit, ite_eq_right hrk] at Hcredit
        change Iris.ProofMode.Entails' _
          (tglWp E pl(&draw &(listVal encode xs).fst #int (xs.length : ℤ)
            #int ((k + 1 : ℕ) : ℤ)) _)
        iapply (IH (k + 1) hk'' F) $$ Hcredit

private theorem valid_test (n k : ℕ) (hk : k ≤ n) :
    Bool.or false (decide ((n : ℤ) < k)) = false := by
  simp [show ¬(n : ℤ) < k by omega]

/-- CTE proof for every valid subset size, including zero draws from an empty list. -/
theorem twp_sampleInOrder (E : CoPset) (encode : α → Val rT) (xs : List α)
    (k : ℕ) (hk : k ≤ xs.length) (F : List α → ℝ≥0∞) :
    ⊢ ↯ (credit xs k F) -∗
      tglWp E pl(&Occil.sampleInOrder &(listVal encode xs).fst #int (k : ℤ))
        (fun v : Val rT => iprop(∃ ys : List α,
          ⌜v = listVal encode ys⌝ ∗ ↯ (F ys))) := by
  iintro Hcredit
  iterate 2 twp_pure
  twp_bind pl(&Occil.length &(listVal encode xs).fst)
  iapply tglWp_wand
  isplitl []
  · iapply (twp_length E encode xs)
  iintro %v %hv
  subst v
  iterate 4 twp_pure
  rw [valid_test xs.length k hk]
  iterate 2 twp_pure
  simp only [UniformInt.uniformInt_openRec, UniformInt.uniformInt_closeRec]
  change Iris.ProofMode.Entails' _
    (tglWp E pl(&draw &(listVal encode xs).fst #int (xs.length : ℤ) #int (k : ℤ)) _)
  iapply (twp_draw E encode xs k hk F) $$ Hcredit

/-- Uniform position subsets, encoded as the selected entries in input order. -/
theorem sampleInOrder_distSpec (E : CoPset) (encode : α → Val rT) (xs : List α)
    (k : ℕ) (hk : k ≤ xs.length) :
    IsDistSpec (GF := GF) E
      pl(&Occil.sampleInOrder &(listVal encode xs).fst #int (k : ℤ))
      (law xs k hk) (listVal encode) where
  spec F _ := by
    simpa only [lintegral_law] using wand_entails (twp_sampleInOrder E encode xs k hk F)

end specification

end
end SampLib.SampleInOrder
