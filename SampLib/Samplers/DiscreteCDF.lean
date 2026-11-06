import SampLib.Distributions.FiniteCDF
import SampLib.GeneralSyntax
import Samplers.General.Core

/-! # Bisection in a finite cumulative-weight table -/

open ProbLang
open scoped ENNReal

namespace SampLib.DiscreteCDF

noncomputable section

open FiniteCDF

/-- Store the CDF on its natural index grid, with no restriction on plateaus. -/
def cumulative (D : Model) (n : ℕ) : List ℤ :=
  List.ofFn (fun i : Fin n => D.cdf (i.val : ℤ))

private theorem index_bounds (D : Model) (n : ℕ) (hl : D.lower = 0)
    (hu : D.upper = (n : ℤ) - 1) (x : ℤ) (hx : x ∈ Set.Icc D.lower D.upper) :
    0 ≤ x ∧ x.toNat < n := by
  simp only [Set.mem_Icc, hl, hu] at hx
  omega

private theorem size_pos (D : Model) (n : ℕ) (hl : D.lower = 0)
    (hu : D.upper = (n : ℤ) - 1) : 0 < n := by
  have := D.nonempty
  omega

private theorem midpoint_eq (a b : ℤ) : (a + b) / 2 = a + (b - a) / 2 := by omega

private theorem ticket_test (i : ℕ) (x : ℤ) :
    decide ((i : ℤ) < x) = decide ((i : ℤ) + 1 ≤ x) := by
  congr 1

@[simp] private theorem getAt_subst {rT : Type _} (x : Var) (e : Exp rT) :
    Exp.subst Occil.getAt x e = Occil.getAt :=
  Exp.subst_fresh x _ e (by simp [Occil.getAt, Exp.fv])

/-- The closed table-search term used by discrete CDF inversion. -/
def search {rT : Type _} [ProbLangℝ rT] (D : Model) (n : ℕ)
    (ticket : ℕ) : Exp rT :=
  Exp.subst (pl% rec find lo hi :=
    if lo = hi then lo else
      let mid := (lo + hi) / #2;
      if #int (ticket : ℤ) < &Occil.getAt table mid then
        find lo mid else find (mid + #1) hi)
    (.named "table") (listVal (fun z : ℤ => Val.int z) (cumulative D n)).fst

private theorem equal_test {rT : Type _} [BEq rT] (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = decide (a = b) := by
  change (a == b) = decide (a = b)
  by_cases h : a = b <;> simp [h]

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
      rw [equal_test, decide_eq_true heq]
      twp_pures
      twp_value
      imodintro
      ipureintro
      rw [Bracket.done w heq]
    · have hlt := w.strict_of_ne heq
      isimp [search, Exp.subst, Exp.close, Exp.closeRec]
      twp_pures
      rw [equal_test, decide_eq_false heq]
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

/-- Invert a nonnegative nondecreasing cumulative table with positive final mass. -/
theorem twp_discreteCDF (E : CoPset) (D : Model) (n : ℕ) (hl : D.lower = 0)
    (hu : D.upper = (n : ℤ) - 1) (F : ℤ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ x, F x ∂law D) -∗
      tglWp E pl(&Occil.General.discreteCDF
        &(listVal (fun z : ℤ => Val.int z) (cumulative D n)).fst #())
        (fun v : Val rT => iprop(∃ x : ℤ, ⌜v = Val.int x⌝ ∗ ↯ (F x))) := by
  have hn := size_pos D n hl hu
  have htest : decide ((n : ℤ) ≤ 0) = false := decide_eq_false (by omega)
  iintro Hcredit
  iterate 2 twp_pure
  simp only [GeneralSyntax.length_openRec, GeneralSyntax.length_closeRec,
    MarkovTerms.getAt_openRec, MarkovTerms.getAt_closeRec,
    UniformInt.uniformInt_openRec, UniformInt.uniformInt_closeRec]
  twp_bind pl(&Occil.length &(listVal (fun z : ℤ => Val.int z) (cumulative D n)).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_length E _ (cumulative D n)
  iintro %v %hv
  subst v
  simp only [cumulative, List.length_ofFn]
  twp_pures
  rw [htest]
  iterate 2 twp_pure
  rw [← hu]
  twp_bind pl(&Occil.getAt
    &(listVal (fun z : ℤ => Val.int z) (cumulative D n)).fst #int D.upper)
  iapply tglWp_wand
  isplitl []
  · iapply twp_lookup E D n hl hu D.upper ⟨D.nonempty, le_rfl⟩
  iintro %v %hv
  subst v
  rw [D.upper_mass]
  twp_pure
  twp_bind pl(&Occil.uniformInt #int (D.scale : ℤ))
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply (UniformInt.twp_uniformInt E D.scale D.positive
      (fun k => F (quantile D (position D k))))
    rw [FiniteCDF.expectation D F]
    iexact Hcredit
  iintro %v ⟨%k, %hv, %hk, Hcredit⟩
  subst v
  iterate 3 twp_pure
  simp only [MarkovTerms.getAt_openRec]
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

/-- The supplied cumulative masses characterize the output CDF exactly. -/
theorem discreteCDF_distSpec (E : CoPset) (D : Model) (n : ℕ) (hl : D.lower = 0)
    (hu : D.upper = (n : ℤ) - 1) :
    IsDistSpec (GF := GF) E pl(&Occil.General.discreteCDF
      &(listVal (fun z : ℤ => Val.int z) (cumulative D n)).fst #()) (law D) Val.int where
  spec F _ := wand_entails (twp_discreteCDF E D n hl hu F)

end specification

end

end SampLib.DiscreteCDF
