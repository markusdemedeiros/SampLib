import SampLib.Distributions.PiecewiseConstant
import SampLib.ProofMode.BindFrom
import Samplers.General.Core

/-! # Sampling a piecewise constant integer-grid density -/

open ProbLang
open scoped ENNReal

namespace SampLib.PiecewiseConstant

noncomputable section

@[pl_fold] private def areas {rT : Type _} : Exp rT := pl%
  rec areas xs hs := case! hs
    | inl(v) => inl(#())
    | inr(hp) =>
      let left := &Occil.getAt xs #0;
      let right := &Occil.getAt xs #1;
      let h := fst(hp);
      if (right <= left) || (h < #0) then fail else
        inr(((right - left) * h, areas (&Occil.General.tail xs) (snd(hp))))

private theorem tail_lc {rT : Type _} :
    (Occil.General.tail : Exp rT).IsLocallyClosed := by is_lc

private theorem tail_fv {rT : Type _} : (Occil.General.tail : Exp rT).fv = ∅ := by
  simp [Occil.General.tail, Exp.fv]

@[simp] private theorem tail_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.General.tail = Occil.General.tail :=
  (Exp.open_lc k e _ tail_lc).symm

@[simp] private theorem tail_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.General.tail : Exp rT) = Occil.General.tail :=
  Exp.closeRec_fresh x _ k (by simp [tail_fv])

private theorem bin_valid (a b : ℤ) (hab : a < b) :
    decide (b ≤ a) = false := decide_eq_false (not_le.mpr hab)

private theorem area_cast (a b : ℤ) (h : ℕ) (hab : a < b) :
    (b - a) * (h : ℤ) = (((b - a).toNat * h : ℕ) : ℤ) := by
  rw [Nat.cast_mul, Int.toNat_of_nonneg (sub_nonneg.mpr hab.le)]

private theorem tail_length (a b : ℤ) (xs : List ℤ) (h : ℕ) (hs : List ℕ)
    (hlen : (a :: b :: xs).length = (h :: hs).length + 1) :
    (b :: xs).length = hs.length + 1 := by simpa using hlen

private theorem tail_increasing (a b : ℤ) (xs : List ℤ) (h : ℕ) (hs : List ℕ)
    (hinc : ∀ i, i < (h :: hs).length →
      (a :: b :: xs)[i]?.getD 0 < (a :: b :: xs)[i + 1]?.getD 0) :
    ∀ i, i < hs.length → (b :: xs)[i]?.getD 0 < (b :: xs)[i + 1]?.getD 0 := by
  intro i hi
  simpa using hinc (i + 1) (by simpa using hi)

private theorem encode_cons {rT : Type _} [ProbLangℝ rT] (a : ℕ) (xs : List ℕ) :
    pl(inr((#int (a : ℤ), {Exp.ofVal (listVal (fun n : ℕ => (Val.int n : Val rT)) xs)}))) =
      Exp.ofVal (listVal (fun n : ℕ => (Val.int n : Val rT)) (a :: xs)) := rfl

private theorem getD_eq_get (xs : List ℤ) (i : ℕ) (hi : i < xs.length) :
    xs[i]?.getD 0 = xs.get ⟨i, hi⟩ := by
  simp [List.getElem?_eq_getElem hi]

private theorem bin_bounds (points : List ℤ) (weights : List ℕ)
    (hlen : points.length = weights.length + 1) (i : ℕ) (hi : i < weights.length) :
    i < points.length ∧ i + 1 < points.length := by omega

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_getAtD (E : CoPset) (xs : List ℤ) (i : ℕ) (hi : i < xs.length) :
    ⊢ tglWp E pl(&Occil.getAt &(listVal (fun z : ℤ => Val.int z) xs).fst #int (i : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (xs[i]?.getD 0)⌝)) := by
  simpa only [getD_eq_get xs i hi] using twp_getAt E (fun z : ℤ => Val.int z) xs ⟨i, hi⟩

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_areas (E : CoPset) (points : List ℤ) (heights : List ℕ)
    (hlen : points.length = heights.length + 1)
    (hinc : ∀ i, i < heights.length → points[i]?.getD 0 < points[i + 1]?.getD 0) :
    ⊢ tglWp E pl(&areas &(listVal (fun z : ℤ => Val.int z) points).fst
        &(listVal (fun h : ℕ => Val.int (h : ℤ)) heights).fst)
      (fun v : Val rT => iprop(⌜v = listVal (fun h : ℕ => Val.int (h : ℤ))
        (weights points heights)⌝)) := by
  induction heights generalizing points with
  | nil =>
    cases points <;> simp only [listVal, weights]
    all_goals twp_pures; twp_value; imodintro; itrivial
  | cons h hs IH =>
    match points with
    | [] => simp at hlen
    | [_] => simp at hlen
    | a :: b :: xs =>
      have hab : a < b := by simpa using hinc 0 (by simp)
      simp only [listVal]
      iterate 5 twp_pure
      simp only [MarkovTerms.getAt_openRec, MarkovTerms.getAt_closeRec,
        tail_openRec, tail_closeRec]
      twp_bind pl(&Occil.getAt &(listVal (fun z : ℤ => Val.int z) (a :: b :: xs)).fst #0)
      iapply tglWp_wand
      isplitl []
      · iapply twp_getAt E _ _ ⟨0, by simp⟩
      iintro %v %hv
      subst v
      twp_pure
      twp_bind pl(&Occil.getAt &(listVal (fun z : ℤ => Val.int z) (a :: b :: xs)).fst #1)
      iapply tglWp_wand
      isplitl []
      · iapply twp_getAt E _ _ ⟨1, by simp⟩
      iintro %v %hv
      subst v
      twp_pures
      simp only [List.get_eq_getElem, List.getElem_cons_zero, List.getElem_cons_succ,
        tail_openRec]
      rw [bin_valid a b hab, Bool.or_false]
      iterate 6 twp_pure
      simp only [MarkovTerms.getAt_openRec, Exp.ofVal]
      have hnext := IH (b :: xs) (tail_length a b xs h hs hlen)
        (tail_increasing a b xs h hs hinc)
      simp [areas, Exp.close, Exp.closeRec] at hnext
      twp_bind_from hnext
      iapply tglWp_wand
      isplitl []
      · iapply hnext
      iintro %v %hv
      subst v
      twp_pures
      rw [area_cast a b h hab, encode_cons]
      iapply (tglWp_value (v := listVal (fun n : ℕ => Val.int (n : ℤ))
        ((b - a).toNat * h :: weights (b :: xs) hs)))
      ipureintro
      rfl

/-- Choose a bin by its exact grid mass, then choose a point uniformly within it. -/
theorem twp_piecewiseConstant (E : CoPset) (D : Model) (F : ℤ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ z, F z ∂law D) -∗
      tglWp E pl(&Occil.General.piecewiseConstant
        &(listVal (fun z : ℤ => Val.int z) D.points).fst
        &(listVal (fun h : ℕ => Val.int (h : ℤ)) D.heights).fst #())
        (fun v : Val rT => iprop(∃ z : ℤ, ⌜v = Val.int z⌝ ∗ ↯ (F z))) := by
  let points := D.points
  let heights := D.heights
  let weights := weights points heights
  have hlen : points.length = weights.length + 1 := D.partition_length
  have hwidth : ∀ i, i < weights.length →
      points[i]?.getD 0 < points[i + 1]?.getD 0 := D.bin_width
  have hlength : points.length = heights.length + 1 := D.length
  have harea := twp_areas (rT := rT) (GF := GF) E points heights D.length D.increasing
  simp [areas, Exp.close, Exp.closeRec] at harea
  iintro Hcredit
  iterate 3 twp_pure
  simp only [GeneralSyntax.length_openRec, GeneralSyntax.length_closeRec,
    MarkovTerms.weightedChoice_openRec, MarkovTerms.weightedChoice_closeRec,
    MarkovTerms.getAt_openRec, MarkovTerms.getAt_closeRec,
    GeneralSyntax.rndIntExcRange_openRec, GeneralSyntax.rndIntExcRange_closeRec,
    tail_openRec, tail_closeRec]
  twp_bind pl(&Occil.length &(listVal (fun w : ℕ => Val.int (w : ℤ)) heights).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_length E _ heights
  iintro %v %hv
  subst v
  twp_pure
  twp_bind pl(&Occil.length &(listVal (fun z : ℤ => Val.int z) points).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_length E _ points
  iintro %v %hv
  subst v
  simp only [hlength, Nat.cast_add_one]
  twp_pure
  rw [beq_self_eq_true]
  iterate 2 twp_pure
  simp only [MarkovTerms.weightedChoice_openRec, MarkovTerms.getAt_openRec,
    GeneralSyntax.rndIntExcRange_openRec]
  twp_bind_from harea
  iapply tglWp_wand
  isplitl []
  · iapply harea
  iintro %v %hv
  subst v
  twp_bind pl(&Occil.weightedChoice &(listVal (fun w : ℕ => Val.int (w : ℤ)) weights).fst)
  isimp only [← expectation D F] at Hcredit
  iapply ((WeightedChoice.weightedChoice_distSpec E weights).wp_supported
    (fun i => i < weights.length) (Set.to_countable _).measurableSet
    (WeightedChoice.ae_lt_length weights)
    (fun i => ∫⁻ z, F z ∂Histogram.binLaw points weights hwidth i)
    (measurable_of_countable _) _) $$ Hcredit
  iintro %i %hi Hcredit
  obtain ⟨hlo, hhi⟩ := bin_bounds points weights hlen i hi
  twp_pure
  twp_bind pl(&Occil.getAt &(listVal (fun z : ℤ => Val.int z) points).fst #int (i : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply twp_getAtD E points i hlo
  iintro %v %hv
  subst v
  twp_pure
  twp_pure
  rw [← Nat.cast_add_one]
  twp_bind pl(&Occil.getAt &(listVal (fun z : ℤ => Val.int z) points).fst
    #int ((i + 1 : ℕ) : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply twp_getAtD E points (i + 1) hhi
  iintro %v %hv
  subst v
  twp_pure
  isimp only [Histogram.binLaw, dite_eq_left hi] at Hcredit
  simp only [GeneralSyntax.rndIntExcRange_openRec]
  iapply RndIntExcRange.twp_rndIntExcRange E _ _ (hwidth i hi) F
  iexact Hcredit

/-- Exact normalized piecewise constant density on the integer grid. -/
theorem piecewiseConstant_distSpec (E : CoPset) (D : Model) :
    IsDistSpec (GF := GF) E pl(&Occil.General.piecewiseConstant
      &(listVal (fun z : ℤ => Val.int z) D.points).fst
      &(listVal (fun h : ℕ => Val.int (h : ℤ)) D.heights).fst #()) (law D) Val.int where
  spec F _ := wand_entails (twp_piecewiseConstant E D F)

end specification

end

end SampLib.PiecewiseConstant
