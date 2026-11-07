import SampLib.Discrete.WeightedChoice
import SampLib.General.Laws.PiecewiseLinear
import SampLib.General.Support.LinearBinSampling
import SampLib.Core.GeneralSyntax
import SampLib.Core.ProofMode.BindFrom
import Samplers.General.Core

/-! # Sampling a piecewise linear integer-grid density -/

open ProbLang
open scoped ENNReal

namespace SampLib.PiecewiseLinear

noncomputable section

private def encode {rT : Type _} [ProbLangℝ rT] (p : ℤ × ℕ) : Val rT :=
  Val.pair (Val.int p.1) (Val.int (p.2 : ℤ))

@[pl_fold] private def areas {rT : Type _} : Exp rT := pl%
  rec areas xs := case! xs
    | inl(v) => fail
    | inr(p) => case! snd(p)
      | inl(v) => inl(#())
      | inr(q) =>
        let a := fst(p);
        let b := fst(q);
        let width := fst(b) - fst(a);
        let ha := snd(a);
        let hb := snd(b);
        if (width <= #0) || (ha < #0) || (hb < #0) then fail else
          inr(((width + #1) * ha + (width - #1) * hb, areas (snd(p))))

private theorem profile_cast (a b : ℤ × ℕ) (hab : a.1 < b.1) :
    (b.1 - a.1 + 1) * (a.2 : ℤ) + (b.1 - a.1 - 1) * (b.2 : ℤ) =
      (binWeight a b : ℤ) := by
  have hw : 1 ≤ (b.1 - a.1).toNat := by omega
  simp only [binWeight, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hw,
    Int.toNat_of_nonneg (sub_nonneg.mpr hab.le), Nat.cast_one]

private theorem width_valid (a b : ℤ × ℕ) (hab : a.1 < b.1) :
    decide (b.1 - a.1 ≤ 0) = false := decide_eq_false (by omega)

private theorem tail_increasing (a : ℤ × ℕ) (xs : List (ℤ × ℕ))
    (hinc : ∀ i, i + 1 < (a :: xs).length →
      ((a :: xs)[i]?.getD (0, 0)).1 < ((a :: xs)[i + 1]?.getD (0, 0)).1) :
    ∀ i, i + 1 < xs.length →
      (xs[i]?.getD (0, 0)).1 < (xs[i + 1]?.getD (0, 0)).1 := by
  intro i hi
  simpa using hinc (i + 1) (by simpa using hi)

private theorem nonempty (D : Model) : D.vertices ≠ [] := by
  intro h
  have := D.positive
  simp [h, weights] at this

private theorem encode_cons {rT : Type _} [ProbLangℝ rT] (h : ℕ) (hs : List ℕ) :
    pl(inr((#int (h : ℤ), {Exp.ofVal (listVal (fun n : ℕ => (Val.int n : Val rT)) hs)}))) =
      Exp.ofVal (listVal (fun n : ℕ => (Val.int n : Val rT)) (h :: hs)) := rfl

private theorem getD_eq_get (xs : List (ℤ × ℕ)) (i : ℕ) (hi : i < xs.length) :
    xs[i]?.getD (0, 0) = xs.get ⟨i, hi⟩ := by simp [List.getElem?_eq_getElem hi]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_areas (E : CoPset) (xs : List (ℤ × ℕ)) (hne : xs ≠ [])
    (hinc : ∀ i, i + 1 < xs.length →
      (xs[i]?.getD (0, 0)).1 < (xs[i + 1]?.getD (0, 0)).1) :
    ⊢ tglWp E pl(&areas &(listVal (encode (rT := rT)) xs).fst)
      (fun v : Val rT => iprop(⌜v = listVal (fun n : ℕ => Val.int (n : ℤ)) (weights xs)⌝)) := by
  induction xs with
  | nil => contradiction
  | cons a xs IH =>
    cases xs with
    | nil =>
      simp only [listVal, encode]
      isimp [areas, Exp.close, Exp.closeRec]
      twp_pures
      twp_value
      imodintro
      ipureintro
      rfl
    | cons b xs =>
      have hab : a.1 < b.1 := by simpa using hinc 0 (by simp)
      simp only [listVal, encode]
      isimp [areas, Exp.close, Exp.closeRec]
      twp_pures
      rw [width_valid a b hab]
      simp only [Bool.false_or]
      iterate 2 twp_pure
      have hnext := IH (by simp) (tail_increasing a (b :: xs) hinc)
      simp [areas, Exp.close, Exp.closeRec] at hnext
      twp_bind_from hnext
      iapply tglWp_wand
      isplitl []
      · iapply hnext
      iintro %v %hv
      subst v
      twp_pures
      rw [profile_cast a b hab, encode_cons]
      iapply (tglWp_value (v := listVal (fun n : ℕ => Val.int (n : ℤ))
        (binWeight a b :: weights (b :: xs))))
      ipureintro
      rfl

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_lookup (E : CoPset) (xs : List (ℤ × ℕ)) (i : ℕ)
    (hi : i < xs.length) :
    ⊢ tglWp E pl(&Occil.getAt &(listVal (encode (rT := rT)) xs).fst #int (i : ℤ))
      (fun v : Val rT => iprop(⌜v = encode (xs[i]?.getD (0, 0))⌝)) := by
  simpa only [getD_eq_get xs i hi] using twp_getAt E encode xs ⟨i, hi⟩

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_envelope (E : CoPset) (a b : ℕ) :
    ⊢ tglWp E pl(if #bool (decide ((a : ℤ) < (b : ℤ))) then #int (b : ℤ) else #int (a : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (max a b : ℕ)⌝)) := by
  by_cases h : a < b
  · rw [decide_eq_true (show (a : ℤ) < b by exact_mod_cast h)]
    twp_pures
    twp_value
    imodintro
    ipureintro
    rw [max_eq_right h.le]
  · rw [decide_eq_false (show ¬(a : ℤ) < b by exact_mod_cast h)]
    twp_pures
    twp_value
    imodintro
    ipureintro
    rw [max_eq_left (Nat.le_of_not_gt h)]

/-- Weight bins by their exact half-open grid mass, then sample the chosen profile. -/
theorem twp_piecewiseLinear (E : CoPset) (D : Model) (F : ℤ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ x, F x ∂law D) -∗
      tglWp E pl(&Occil.General.piecewiseLinear &(listVal (encode (rT := rT)) D.vertices).fst
        #()) (fun v : Val rT => iprop(∃ x : ℤ, ⌜v = Val.int x⌝ ∗ ↯ (F x))) := by
  have harea := twp_areas (rT := rT) (GF := GF) E D.vertices (nonempty D) D.increasing
  simp [areas, Exp.close, Exp.closeRec] at harea
  iintro Hcredit
  isimp [Occil.General.piecewiseLinear, Exp.close, Exp.closeRec]
  iterate 3 twp_pure
  simp only [MarkovTerms.weightedChoice_openRec, MarkovTerms.getAt_openRec,
    UniformInt.uniformInt_openRec]
  twp_bind_from harea
  iapply tglWp_wand
  isplitl []
  · iapply harea
  iintro %v %hv
  subst v
  twp_bind pl(&Occil.weightedChoice
    &(listVal (fun n : ℕ => Val.int (n : ℤ)) (weights D.vertices)).fst)
  isimp only [← expectation D F] at Hcredit
  iapply ((WeightedChoice.weightedChoice_distSpec E (weights D.vertices)).wp_supported
    (fun i => i < (weights D.vertices).length ∧ 0 < (weights D.vertices)[i]?.getD 0)
    (Set.to_countable _).measurableSet
    ((WeightedChoice.ae_lt_length (weights D.vertices)).and
      (WeightedChoice.ae_getD_pos (weights D.vertices)))
    (fun i => ∫⁻ x, F x ∂binLaw D i) (measurable_of_countable _) _) $$ Hcredit
  iintro %i %hi Hcredit
  obtain ⟨hlo, hhi⟩ := bin_bounds D i hi.1
  have hdraw := LinearBin.twp_draw (rT := rT) (GF := GF) E (bin D i hi.1 hi.2) F
  simp [LinearBin.draw, bin, LinearBin.envelope, Exp.close, Exp.closeRec,
    Int.toNat_of_nonneg (sub_nonneg.mpr (D.increasing i hhi).le)] at hdraw
  twp_pure
  twp_bind pl(&Occil.getAt &(listVal (encode (rT := rT)) D.vertices).fst #int (i : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply twp_lookup E D.vertices i hlo
  iintro %v %hv
  subst v
  iterate 2 twp_pure
  rw [← Nat.cast_add_one]
  twp_bind pl(&Occil.getAt &(listVal (encode (rT := rT)) D.vertices).fst
    #int ((i + 1 : ℕ) : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply twp_lookup E D.vertices (i + 1) hhi
  iintro %v %hv
  subst v
  simp only [encode]
  twp_pures
  twp_bind pl(if #bool (decide (((D.vertices[i]?.getD (0, 0)).2 : ℤ) <
      ((D.vertices[i + 1]?.getD (0, 0)).2 : ℤ))) then
    #int ((D.vertices[i + 1]?.getD (0, 0)).2 : ℤ) else
    #int ((D.vertices[i]?.getD (0, 0)).2 : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply twp_envelope E _ _
  iintro %v %hv
  subst v
  iterate 2 twp_pure
  simp only [UniformInt.uniformInt_openRec, Nat.cast_max]
  isimp only [binLaw, dite_eq_left hi, bin] at Hcredit
  iapply hdraw $$ Hcredit

/-- Exact piecewise linear grid law, including zero-height vertices and empty-weight bins. -/
theorem piecewiseLinear_distSpec (E : CoPset) (D : Model) :
    IsDistSpec (GF := GF) E pl(&Occil.General.piecewiseLinear
      &(listVal (encode (rT := rT)) D.vertices).fst #()) (law D) Val.int where
  spec F _ := wand_entails (twp_piecewiseLinear E D F)

end specification

end

end SampLib.PiecewiseLinear
