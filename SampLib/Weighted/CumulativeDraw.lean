import SampLib.Weighted.Laws.CumulativeDraw
import SampLib.Core.GeneralSyntax
import Samplers.Weighted.Tables

/-! # Drawing from a precomputed cumulative table

A uniform ticket selects the first cumulative mass strictly above it. The
bisection bracket always contains that quantile, including across zero masses.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.CumulativeDraw

noncomputable section

open FiniteCDF

/-- The table stores its total mass together with the cumulative array. -/
def table {rT : Type _} [ProbLangℝ rT] (D : Model) (n : ℕ) : Val rT :=
  .pair (.int D.scale) (listVal (fun z : ℤ => Val.int z) (cumulative D n))

private theorem index_bounds (D : Model) (n : ℕ) (hl : D.lower = 0)
    (hu : D.upper = (n : ℤ) - 1) (x : ℤ) (hx : x ∈ Set.Icc D.lower D.upper) :
    0 ≤ x ∧ x.toNat < n := by
  simp only [Set.mem_Icc, hl, hu] at hx
  omega

private theorem midpoint_eq (a b : ℤ) : (a + b) / 2 = a + (b - a) / 2 := by omega

private theorem ticket_test (i : ℕ) (x : ℤ) :
    decide ((i : ℤ) < x) = decide ((i : ℤ) + 1 ≤ x) := by
  congr 1

@[simp] private theorem getAt_subst {rT : Type _} (x : Var) (e : Exp rT) :
    Exp.subst Occil.getAt x e = Occil.getAt :=
  Exp.subst_fresh x _ e (by simp [Occil.getAt, Exp.fv])

/-- The closed table-search term used by cumulative-table draws. -/
def search {rT : Type _} [ProbLangℝ rT] (D : Model) (n : ℕ)
    (ticket : ℕ) : Exp rT :=
  Exp.subst (pl% rec find lo hi :=
    if hi <= lo then lo else
      let mid := (lo + hi) / #2;
      if #int (ticket : ℤ) < &Occil.getAt table mid then
        find lo mid else find (mid + #1) hi)
    (.named "table") (listVal (fun z : ℤ => Val.int z) (cumulative D n)).fst

private theorem stop_test (D : Model) (i : Fin D.scale) (w : Bracket D i) :
    decide (w.upper ≤ w.lower) = decide (w.lower = w.upper) := by
  by_cases h : w.lower = w.upper
  · simp [h]
  · have hnot : ¬w.upper ≤ w.lower := not_le.mpr (w.strict_of_ne h)
    simp [h, hnot]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_lookup (E : CoPset) (D : Model) (n : ℕ) (hl : D.lower = 0)
    (hu : D.upper = (n : ℤ) - 1) (x : ℤ) (hx : x ∈ Set.Icc D.lower D.upper) :
    ⊢ tglWp E pl(&Occil.getAt
      &(listVal (fun z : ℤ => Val.int z) (cumulative D n)).fst #int x)
      (fun v : Val rT => iprop(⌜v = Val.int (D.cdf x)⌝)) := by
  obtain ⟨hx0, hxn⟩ := index_bounds D n hl hu x hx
  have h := twp_getAt (rT := rT) (GF := GF) E (fun z : ℤ => Val.int z)
    (cumulative D n) ⟨x.toNat, by simpa [cumulative] using hxn⟩
  simpa [cumulative, Int.toNat_of_nonneg hx0] using h

omit [ProbLangDist.IsUniformInt rT] in
/-- Every valid bracket converges to its fixed first-reaching quantile. -/
theorem twp_search (E : CoPset) (D : Model) (n : ℕ) (hl : D.lower = 0)
    (hu : D.upper = (n : ℤ) - 1) (i : Fin D.scale) (w : Bracket D i) :
    ⊢ tglWp E pl(&(search D n i.val) #int w.lower #int w.upper)
      (fun v : Val rT => iprop(⌜v = Val.int (quantile D i)⌝)) := by
  induction w using (measure (fun w : Bracket D i => w.width)).wf.induction with
  | h w IH =>
    by_cases heq : w.lower = w.upper
    · isimp [search, Exp.subst, Exp.close, Exp.closeRec]
      twp_pures
      rw [stop_test, decide_eq_true heq]
      twp_pures
      twp_value
      imodintro
      ipureintro
      rw [Bracket.done w heq]
    · have hlt := w.strict_of_ne heq
      isimp [search, Exp.subst, Exp.close, Exp.closeRec]
      twp_pures
      rw [stop_test, decide_eq_false heq]
      iterate 4 twp_pure
      rw [midpoint_eq]
      twp_bind pl(&Occil.getAt
        &(listVal (fun z : ℤ => Val.int z) (cumulative D n)).fst #int w.midpoint)
      iapply tglWp_wand
      isplitl []
      · iapply twp_lookup E D n hl hu w.midpoint (w.midpoint_mem hlt)
      iintro %v %hv
      subst v
      twp_pure
      rw [ticket_test]
      by_cases hc : (i.val : ℤ) + 1 ≤ D.cdf w.midpoint
      · rw [decide_eq_true hc]
        twp_pure
        have hnext := IH (w.left hlt hc) (w.left_width_lt hlt hc)
        simp [search, Exp.subst, Exp.close, Exp.closeRec, Bracket.left, Bracket.midpoint] at hnext
        simp only [MarkovTerms.getAt_openRec]
        iapply hnext
      · rw [decide_eq_false hc]
        iterate 2 twp_pure
        have hnext := IH (w.right hlt hc) (w.right_width_lt hlt hc)
        simp [search, Exp.subst, Exp.close, Exp.closeRec, Bracket.right, Bracket.midpoint] at hnext
        simp only [Exp.ofVal, MarkovTerms.getAt_openRec]
        iapply hnext

/-- Exact inversion of every bounded monotone cumulative array with positive final mass. -/
theorem cumulativeDraw_distSpec (E : CoPset) (D : Model) (n : ℕ) (hl : D.lower = 0)
    (hu : D.upper = (n : ℤ) - 1) :
    IsDistSpec (GF := GF) E pl(&Occil.Weighted.cumulativeDraw &(table D n).fst #())
      (law D) Val.int := by
  refine ⟨fun F _ => ?_⟩
  iintro Hcredit
  iterate 6 twp_pure
  simp only [UniformInt.uniformInt_openRec, UniformInt.uniformInt_closeRec,
    MarkovTerms.getAt_openRec, MarkovTerms.getAt_closeRec,
    GeneralSyntax.length_openRec, GeneralSyntax.length_closeRec]
  twp_bind pl(&Occil.uniformInt #int (D.scale : ℤ))
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply UniformInt.twp_uniformInt E D.scale D.positive
      (fun k => F (quantile D (position D k)))
    rw [FiniteCDF.expectation D F]
    iexact Hcredit
  iintro %v ⟨%k, %hv, %hk, Hcredit⟩
  subst v
  iterate 2 twp_pure
  simp only [MarkovTerms.getAt_openRec]
  twp_bind pl(&Occil.length &(listVal (fun z : ℤ => Val.int z) (cumulative D n)).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_length E _ (cumulative D n)
  iintro %v %hv
  subst v
  simp only [cumulative, List.length_ofFn]
  twp_pure
  have hsearch := twp_search (rT := rT) (GF := GF) E D n hl hu
    ⟨k, hk⟩ (Bracket.initial D ⟨k, hk⟩)
  simp [search, Exp.subst, Exp.close, Exp.closeRec, Bracket.initial, cumulative, hl, hu] at hsearch
  iapply tglWp_wand
  isplitl []
  · iapply hsearch
  iintro %v %hv
  iexists quantile D ⟨k, hk⟩
  isimp only [position_of_lt D k hk] at Hcredit
  iframe Hcredit
  ipureintro
  exact hv

end specification

end

end SampLib.CumulativeDraw
