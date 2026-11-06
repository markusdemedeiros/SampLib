import SampLib.General.Laws.LatinHypercubeSupport
import SampLib.General.Laws.RepeatedSupport
import SampLib.Core.SupportedSpec
import SampLib.General.Syntax.LatinHypercube
import SampLib.Core.Syntax.ListAccess
import SampLib.Core.Syntax.ListValues
import SampLib.Core.ListOperations
import SampLib.Core.SamplerStep
import SampLib.Core.ProofMode.BindFrom

/-! # Independent shuffled columns form a Latin hypercube

Each column has the rounded-bin shuffled-stratification law. The columns are
independent, and a deterministic transpose returns the point rows.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.LatinHypercube

noncomputable section

open Source

set_option maxHeartbeats 200000

/-- Read a row, with a total default outside the fixed-length column support. -/
def row (columns : List (List ℤ)) (i : ℕ) : List ℤ :=
  columns.map (fun xs => xs[i]?.getD 0)

/-- Consecutive rows of the sampled columns. -/
def rowsFrom (columns : List (List ℤ)) (i : ℕ) : ℕ → List (List ℤ)
  | 0 => []
  | n + 1 => row columns i :: rowsFrom columns (i + 1) n

section mathematics

open MeasureTheory

/-- Independent shuffled columns, transposed into point order. -/
def law (scale count : ℕ) (hc : 0 < count) (h : count ≤ scale) (dimension : ℕ) :
    Measure (List (List ℤ)) :=
  (SampleWithReplacement.law (LatinHypercube1D.law scale count hc h) dimension).map
    (fun columns => rowsFrom (List.ofFn columns) 0 count)

instance (scale count : ℕ) (hc : 0 < count) (h : count ≤ scale) (dimension : ℕ) :
    IsProbabilityMeasure (law scale count hc h dimension) := by unfold law; infer_instance

/-- The transpose is a deterministic pushforward of the independent column law. -/
theorem expectation (scale count : ℕ) (hc : 0 < count) (h : count ≤ scale)
    (dimension : ℕ) (F : List (List ℤ) → ℝ≥0∞) :
    ∫⁻ columns, F (rowsFrom (List.ofFn columns) 0 count)
        ∂SampleWithReplacement.law (LatinHypercube1D.law scale count hc h) dimension =
      ∫⁻ ys, F ys ∂law scale count hc h dimension := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]

/-- Every sampled column has one entry for each stratum. -/
theorem columns_valid (scale count : ℕ) (hc : 0 < count) (h : count ≤ scale)
    (dimension : ℕ) :
    ∀ᵐ columns ∂SampleWithReplacement.law (LatinHypercube1D.law scale count hc h) dimension,
      ∀ i, (columns i).length = count :=
  SampleWithReplacement.all_ae _ _ (LatinHypercube1D.length_ae scale count hc h) dimension

end mathematics

private def sampler {rT : Type _} [ProbLangℝ rT] (scale count : ℕ) : Val rT :=
  ⟨pl(fun u, &Occil.General.latinHypercube1D #int (scale : ℤ) #int (count : ℤ) #()),
    .lam (by is_lc), by is_lc⟩

private def readColumn {rT : Type _} (i : ℕ) : Val rT :=
  ⟨pl(fun column, &Occil.getAt column #int (i : ℤ)), .lam (by is_lc), by is_lc⟩

private def buildRows {rT : Type _} [ProbLangℝ rT]
    (count : ℕ) (columns : List (List ℤ)) : Exp rT :=
  .fix (.lam (.cond (.binop .eq (.bvar 0) (.lit (.int count))) (.inl (.lit .unit))
    (.inr (.pair
      (.app (.app Occil.General.map
        (.lam (.app (.app Occil.getAt (.bvar 0)) (.bvar 1))))
        (listVal (listVal Val.int) columns).fst)
      (.app (.bvar 1) (.binop .plus (.bvar 0) (.lit (.int 1))))))))

private def rowsValue {rT : Type _} [ProbLangℝ rT]
    (count : ℕ) (columns : List (List ℤ)) : Val rT :=
  ⟨buildRows count columns, .fix (by is_lc), by is_lc⟩

private theorem rowsValue_fst {rT : Type _} [ProbLangℝ rT]
    (count : ℕ) (columns : List (List ℤ)) :
    (rowsValue (rT := rT) count columns).fst = buildRows count columns := rfl

private theorem get_eq_default (xs : List ℤ) (i : ℕ) (hi : i < xs.length) :
    xs.get ⟨i, hi⟩ = xs[i]?.getD 0 := by
  simp [List.getElem?_eq_getElem hi, List.get_eq_getElem]

private theorem ofFn_valid {dimension count : ℕ} (columns : Fin dimension → List ℤ)
    (h : ∀ i, (columns i).length = count) :
    ∀ xs ∈ List.ofFn columns, xs.length = count := by
  intro xs hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact h i

private theorem int_beq {rT : Type _} [BEq rT] (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = (a == b) := rfl

private theorem dimension_test (d : ℕ) (hd : 0 < d) :
    decide ((d : ℤ) ≤ 0) = false := by simp [Nat.ne_of_gt hd]

private theorem encode_cons {rT : Type _} [ProbLangℝ rT] {α : Type _}
    (encode : α → Val rT) (x : α) (xs : List α) :
    pl(inr(({Exp.ofVal (encode x)}, {Exp.ofVal (listVal encode xs)}))) =
      Exp.ofVal (listVal encode (x :: xs)) := by simp [Exp.ofVal, listVal]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_readColumn (E : CoPset) (i : ℕ) (xs : List ℤ) (hi : i < xs.length) :
    ⊢ tglWp E pl(&(readColumn (rT := rT) i).fst &(listVal Val.int xs).fst)
      (fun v : Val rT => iprop(⌜v = Val.int (xs[i]?.getD 0)⌝)) := by
  have hread := twp_getAt (rT := rT) (GF := GF) E Val.int xs ⟨i, hi⟩
  rw [get_eq_default xs i hi] at hread
  twp_pure
  simp only [ListAccess.getAt_openRec, ListAccess.getAt_closeRec]
  iapply hread

private theorem twp_row (E : CoPset) (i : ℕ) (columns : List (List ℤ))
    (hi : ∀ xs ∈ columns, i < xs.length) :
    ⊢ tglWp E pl(&Occil.General.map &(readColumn (rT := rT) i).fst
        &(listVal (listVal Val.int) columns).fst)
      (fun v : Val rT => iprop(⌜v = listVal Val.int (row columns i)⌝)) := by
  induction columns with
  | nil =>
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    ipureintro
    exact Val.ext rfl
  | cons xs columns IH =>
    have hx := hi xs (by simp)
    have htail : ∀ ys ∈ columns, i < ys.length := fun ys hy => hi ys (by simp [hy])
    simp only [listVal]
    iterate 6 twp_pure
    twp_bind pl(&Occil.General.map &(readColumn (rT := rT) i).fst
      &(listVal (listVal Val.int) columns).fst)
    iapply tglWp_wand
    isplitl []
    · iapply IH htail
    iintro %v %hv
    subst v
    twp_pure
    twp_bind pl(&(readColumn (rT := rT) i).fst &(listVal Val.int xs).fst)
    iapply tglWp_wand
    isplitl []
    · iapply twp_readColumn E i xs hx
    iintro %v %hv
    subst v
    rw [encode_cons]
    iapply (tglWp_value (v := listVal Val.int ((xs[i]?.getD 0) :: row columns i)))
    ipureintro
    exact Val.ext rfl

private theorem twp_rows (E : CoPset) (count : ℕ) (columns : List (List ℤ))
    (hcols : ∀ xs ∈ columns, xs.length = count) (n i : ℕ) (hi : i + n = count) :
    ⊢ tglWp E pl(&(buildRows (rT := rT) count columns) #int (i : ℤ))
      (fun v : Val rT => iprop(⌜v = listVal (listVal Val.int) (rowsFrom columns i n)⌝)) := by
  induction n generalizing i with
  | zero =>
    have he : i = count := by omega
    subst i
    rw [← rowsValue_fst]
    twp_step
    simp [Exp.open', Exp.openRec]
    twp_pure
    twp_pure
    rw [int_beq, beq_self_eq_true]
    twp_pures
    twp_value
    imodintro
    ipureintro
    exact Val.ext rfl
  | succ n IH =>
    have hne : (i : ℤ) ≠ count := by omega
    have hi' : (i + 1) + n = count := by omega
    have hrow : ∀ xs ∈ columns, i < xs.length := by
      intro xs hx
      rw [hcols xs hx]
      omega
    rw [← rowsValue_fst]
    twp_step
    simp [Exp.open', Exp.openRec]
    twp_pure
    twp_pure
    rw [int_beq, beq_eq_false_iff_ne.mpr hne]
    twp_pure
    twp_pure
    simp only [ListAccess.map_openRec, ListAccess.getAt_openRec]
    rw [← Nat.cast_add_one]
    twp_bind pl(&(rowsValue (rT := rT) count columns).fst #int ((i + 1 : ℕ) : ℤ))
    rw [rowsValue_fst]
    iapply tglWp_wand
    isplitl []
    · iapply IH (i + 1) hi'
    iintro %v %hv
    subst v
    twp_bind pl(&Occil.General.map &(readColumn (rT := rT) i).fst
      &(listVal (listVal Val.int) columns).fst)
    iapply tglWp_wand
    isplitl []
    · iapply twp_row E i columns hrow
    iintro %v %hv
    subst v
    rw [encode_cons]
    iapply (tglWp_value (v := listVal (listVal Val.int)
      (row columns i :: rowsFrom columns (i + 1) n)))
    ipureintro
    exact Val.ext rfl

variable [ProbLangDist.IsUniformInt rT]

private theorem sampler_spec (E : CoPset) (scale count : ℕ) (hc : 0 < count)
    (h : count ≤ scale) :
    IsDistSpec (GF := GF) E pl(&(sampler (rT := rT) scale count).fst #())
      (LatinHypercube1D.law scale count hc h) (listVal Val.int) where
  spec F hF := by
    iintro Hcredit
    twp_pure
    simp only [LatinHypercube1D.latinHypercube1D_openRec,
      LatinHypercube1D.latinHypercube1D_closeRec]
    iapply (LatinHypercube1D.latinHypercube1D_distSpec E scale count hc h).spec F hF $$ Hcredit

/-- Independent stratifications in every coordinate, transposed into point rows. -/
theorem latinHypercube_distSpec (E : CoPset) (scale count dimension : ℕ)
    (hc : 0 < count) (h : count ≤ scale) (hd : 0 < dimension) :
    IsDistSpec (GF := GF) E
      pl(&Occil.General.latinHypercube #int (scale : ℤ) #int (count : ℤ)
        #int (dimension : ℤ) #())
      (law scale count hc h dimension) (listVal (listVal Val.int)) where
  spec F _ := by
    have hsample := SampleWithReplacement.repeatSample_distSpec (rT := rT) (GF := GF) E
      (LatinHypercube1D.law scale count hc h) (listVal Val.int) (sampler scale count)
      (sampler_spec E scale count hc h) dimension
    simp [sampler, Exp.close, Exp.closeRec] at hsample
    have hCount := countStage_fst (rT := rT) scale
    have hDimension := dimensionStage_fst (rT := rT) scale count
    have hUnit := unitStage_fst (rT := rT) scale count dimension
    simp [Exp.close, Exp.closeRec, Var.internal.injEq] at hCount hDimension hUnit
    have hrows (columns : Fin dimension → List ℤ)
        (hcolumns : ∀ i, (columns i).length = count) :=
      twp_rows (rT := rT) (GF := GF) E count (List.ofFn columns)
        (ofFn_valid columns hcolumns) count 0 (Nat.zero_add _)
    simp [buildRows] at hrows
    iintro Hcredit
    rw [← sourceValue_fst]
    twp_step pl(&(sourceValue (rT := rT)).fst #int (scale : ℤ))
    simp [Exp.open', Exp.openRec, Exp.close, Exp.closeRec, Exp.ofVal, Var.internal.injEq]
    rw [← hCount]
    twp_step
    simp [Exp.open', Exp.openRec, Exp.close, Exp.closeRec, Exp.ofVal, Var.internal.injEq]
    rw [← hDimension]
    twp_step
    simp [Exp.open', Exp.openRec, Exp.close, Exp.closeRec, Exp.ofVal, Var.internal.injEq]
    rw [← hUnit]
    twp_step
    simp [Exp.open', Exp.openRec, Exp.close, Exp.closeRec, Var.internal.injEq]
    twp_pure
    rw [dimension_test dimension hd]
    twp_pure
    twp_bind_from (hsample.spec
      (fun columns => F (rowsFrom (List.ofFn columns) 0 count)) (measurable_of_countable _))
    isimp only [← expectation scale count hc h dimension F] at Hcredit
    iapply (hsample.wp_supported (fun columns => ∀ i, (columns i).length = count)
      (Set.to_countable _).measurableSet (columns_valid scale count hc h dimension)
      (fun columns => F (rowsFrom (List.ofFn columns) 0 count)) (measurable_of_countable _) _)
      $$ Hcredit
    iintro %columns %hcolumns Hcredit
    twp_pure
    twp_pure
    simp only [ListAccess.map_openRec, ListAccess.getAt_openRec]
    iapply tglWp_wand
    isplitl []
    · iapply hrows columns hcolumns
    iintro %v %hv
    iexists rowsFrom (List.ofFn columns) 0 count
    iframe Hcredit
    ipureintro
    exact hv

end specification

end

end SampLib.LatinHypercube
