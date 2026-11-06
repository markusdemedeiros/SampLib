import SampLib.Common.Laws.ListProduct
import SampLib.Common.Laws.Sorting
import SampLib.Uniform.RealCoin

/-! # Independent-edge graphs in canonical edge order

The upper triangle is enumerated by increasing first coordinate, then increasing
second coordinate. Independent Bernoulli coordinates retain these edges; the
pushforward records the retained edges in that same order.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.RandomGraph

noncomputable section

abbrev Edge := ℕ × ℕ

def columns (i j : ℕ) : ℕ → List Edge
  | 0 => []
  | r + 1 => (i, j) :: columns i (j + 1) r

def edges (i : ℕ) : ℕ → List Edge
  | 0 => []
  | m + 1 => columns i (i + 1) m ++ edges (i + 1) m

/-- The canonical upper triangle on vertices `0, …, n-1`. -/
abbrev complete (n : ℕ) := edges 0 n

@[simp] theorem mem_columns (i j r a b : ℕ) :
    (a, b) ∈ columns i j r ↔ a = i ∧ j ≤ b ∧ b < j + r := by
  induction r generalizing j with
  | zero => simp [columns]
  | succ r IH =>
    simp only [columns, List.mem_cons, Prod.mk.injEq, IH]
    omega

@[simp] theorem mem_edges (i m a b : ℕ) :
    (a, b) ∈ edges i m ↔ i ≤ a ∧ a < b ∧ b < i + m := by
  induction m generalizing i with
  | zero => simp [edges]; omega
  | succ m IH =>
    simp only [edges, List.mem_append, mem_columns, IH]
    omega

theorem columns_nodup (i j r : ℕ) : (columns i j r).Nodup := by
  induction r generalizing j with
  | zero => simp [columns]
  | succ r IH => simp [columns, IH]

theorem edges_nodup (i m : ℕ) : (edges i m).Nodup := by
  induction m generalizing i with
  | zero => simp [edges]
  | succ m IH =>
    rw [edges, List.nodup_append]
    refine ⟨columns_nodup _ _ _, IH _, ?_⟩
    rintro ⟨a, b⟩ ha _ hb rfl
    have ha' := (mem_columns _ _ _ _ _).mp ha
    have hb' := (mem_edges _ _ _ _).mp hb
    omega

/-- The strict lexicographic order on edges. -/
def before (e f : Edge) : Prop := e.1 < f.1 ∨ e.1 = f.1 ∧ e.2 < f.2

theorem columns_ordered (i j r : ℕ) : (columns i j r).Pairwise before := by
  induction r generalizing j with
  | zero => simp [columns]
  | succ r IH =>
    rw [columns, List.pairwise_cons]
    refine ⟨?_, IH _⟩
    rintro ⟨a, b⟩ h
    have h' := (mem_columns _ _ _ _ _).mp h
    exact Or.inr ⟨h'.1.symm, by omega⟩

theorem edges_ordered (i m : ℕ) : (edges i m).Pairwise before := by
  induction m generalizing i with
  | zero => simp [edges]
  | succ m IH =>
    rw [edges, List.pairwise_append]
    refine ⟨columns_ordered _ _ _, IH _, ?_⟩
    rintro ⟨a, b⟩ ha ⟨c, d⟩ hc
    have ha' := (mem_columns _ _ _ _ _).mp ha
    have hc' := (mem_edges _ _ _ _).mp hc
    exact Or.inl (by omega)

def retain : List Edge → List Bool → List Edge
  | [], _ => []
  | _, [] => []
  | e :: es, b :: bs => if b then e :: retain es bs else retain es bs

/-- The product Bernoulli law, pushed forward to the retained ordered edge list. -/
def law (p : unitInterval) (es : List Edge) : Measure (List Edge) :=
  (ListProduct.law (fun _ => RealCoin.law p) 0 es.length).map (retain es)

instance (p : unitInterval) (es : List Edge) : IsProbabilityMeasure (law p es) where
  measure_univ := by
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

def credit (p : unitInterval) (e : Edge) (es : List Edge)
    (F : List Edge → ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  ∫⁻ ys, F (if b then e :: ys else ys) ∂law p es

@[simp] theorem expectation_nil (p : unitInterval) (F : List Edge → ℝ≥0∞) :
    ∫⁻ ys, F ys ∂law p [] = F [] := by
  simp [law, ListProduct.law, retain]

/-- Fubini separates the first independent edge indicator from the remaining ones. -/
theorem expectation (p : unitInterval) (e : Edge) (es : List Edge)
    (F : List Edge → ℝ≥0∞) :
    ∫⁻ b, credit p e es F b ∂RealCoin.law p = ∫⁻ ys, F ys ∂law p (e :: es) := by
  simp_rw [credit, law, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  rw [List.length_cons, ← ListProduct.expectation]
  simp only [ListProduct.constant_start, retain]
  exact lintegral_lintegral_swap (measurable_of_countable _).aemeasurable

@[simp] theorem law_zero (es : List Edge) : law 0 es = Measure.dirac [] := by
  induction es with
  | nil => simp [law, ListProduct.law, retain]
  | cons e es IH =>
    apply Measure.ext_of_lintegral
    intro F _
    rw [← expectation, RealCoin.lintegral_law]
    simp [credit, RealCoin.credit, RealCoin.pmf, IH]

@[simp] theorem law_one (es : List Edge) : law 1 es = Measure.dirac es := by
  induction es with
  | nil => simp [law, ListProduct.law, retain]
  | cons e es IH =>
    apply Measure.ext_of_lintegral
    intro F _
    rw [← expectation, RealCoin.lintegral_law]
    simp [credit, RealCoin.credit, RealCoin.pmf, IH]

end

end SampLib.RandomGraph
