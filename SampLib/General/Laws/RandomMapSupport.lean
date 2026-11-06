import SampLib.General.Laws.RandomMap
import SampLib.General.Laws.CouplingFromPast

/-! # Typed finite maps sampled from stochastic matrices

Square rows produce exactly one valid destination per state. The typed mapping
law has the normalized matrix row as each coordinate marginal.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.RandomMapSupport

noncomputable section

abbrev Row := MarkovChain.Row

def Valid (n : ℕ) (xs : List ℕ) : Prop :=
  xs.length = n ∧ ∀ j ∈ xs, j < n

/-- Square transition rows produce valid finite destination lists almost surely. -/
theorem valid_ae (rows : List Row) (n : ℕ)
    (hsquare : ∀ r ∈ rows, r.val.length = n) :
    ∀ᵐ xs ∂RandomMap.law rows, xs.length = rows.length ∧ ∀ j ∈ xs, j < n := by
  induction rows with
  | nil => simp [RandomMap.law]
  | cons r rs IH =>
    let : NeZero r.val.sum := ⟨r.property.ne'⟩
    have hr : r.val.length = n := hsquare r (by simp)
    have htail : ∀ s ∈ rs, s.val.length = n := fun s hs => hsquare s (by simp [hs])
    rw [RandomMap.law, ae_map_iff (measurable_of_countable _).aemeasurable
      (Set.to_countable _).measurableSet]
    apply (Measure.ae_prod_iff_ae_ae (Set.to_countable _).measurableSet).2
    filter_upwards [IH htail] with xs hxs
    filter_upwards [WeightedChoice.ae_lt_length r.val] with j hj
    refine ⟨by simp [hxs.1], ?_⟩
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · simpa only [hr] using hj
    · exact hxs.2 k hk

def lookup (xs : List ℕ) (i : ℕ) : ℕ := xs[i]?.getD 0

/-- One sampled-map coordinate has exactly its normalized transition-row law. -/
theorem lookup_expectation (rows : List Row) (i : ℕ) (hi : i < rows.length)
    (F : ℕ → ℝ≥0∞) :
    ∫⁻ xs, F (lookup xs i) ∂RandomMap.law rows = ∫⁻ j, F j ∂MarkovChain.kernel rows i := by
  induction rows generalizing i with
  | nil => simp at hi
  | cons r rs IH =>
    let : NeZero r.val.sum := ⟨r.property.ne'⟩
    rw [RandomMap.law,
      lintegral_map (measurable_of_countable _) (measurable_of_countable _),
      lintegral_prod _ (measurable_of_countable _).aemeasurable]
    cases i with
    | zero =>
      simp [lookup, MarkovChain.kernel, MarkovChain.row]
    | succ i =>
      simpa [lookup, MarkovChain.kernel, MarkovChain.row] using IH i (by simpa using hi)

theorem lookup_map (rows : List Row) (i : ℕ) (hi : i < rows.length) :
    (RandomMap.law rows).map (fun xs => lookup xs i) = MarkovChain.kernel rows i := by
  apply Measure.ext_of_lintegral
  intro F _
  rw [lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    lookup_expectation rows i hi F]

/-- The default is used only outside the proved finite-state support. -/
def toState (n : ℕ) [NeZero n] (j : ℕ) : Fin n :=
  if h : j < n then ⟨j, h⟩ else 0

@[simp] theorem toState_val (n : ℕ) [NeZero n] (j : ℕ) (hj : j < n) :
    (toState n j).val = j := by simp [toState, hj]

def decode (n : ℕ) [NeZero n] (xs : List ℕ) : CouplingFromPast.Map n :=
  fun i => toState n (lookup xs i.val)

theorem decode_list (n : ℕ) [NeZero n] (xs : List ℕ) (hxs : Valid n xs) :
    List.ofFn (fun i => (decode n xs i).val) = xs := by
  rcases hxs with ⟨hlen, hbound⟩
  subst n
  calc
    _ = List.ofFn xs.get := by
      congr 1
      funext i
      have hi : lookup xs i.val = xs.get i := by
        simp [lookup, List.get_eq_getElem]
      simp only [decode, hi]
      exact toState_val _ _ (hbound _ (List.get_mem ..))
    _ = xs := List.ofFn_get xs

/-- The actual independently sampled map, interpreted as a finite-state function. -/
def law (rows : List Row) [NeZero rows.length] : Measure (CouplingFromPast.Map rows.length) :=
  (RandomMap.law rows).map (decode rows.length)

instance (rows : List Row) [NeZero rows.length] : IsProbabilityMeasure (law rows) where
  measure_univ := by
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- The finite-state matrix kernel, with its null outside-support values discarded. -/
def kernel (rows : List Row) [NeZero rows.length] (i : Fin rows.length) :
    Measure (Fin rows.length) :=
  (MarkovChain.kernel rows i.val).map (toState rows.length)

instance (rows : List Row) [NeZero rows.length] (i : Fin rows.length) :
    IsProbabilityMeasure (kernel rows i) where
  measure_univ := by
    rw [kernel, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- Reusing one sampled mapping has precisely the original matrix marginals. -/
theorem transition_eq_kernel (rows : List Row) [NeZero rows.length] (i : Fin rows.length) :
    CouplingFromPast.transition (law rows) i = kernel rows i := by
  rw [CouplingFromPast.transition, law,
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  change (RandomMap.law rows).map (fun xs => toState rows.length (lookup xs i.val)) = _
  calc
    _ = ((RandomMap.law rows).map (fun xs => lookup xs i.val)).map
        (toState rows.length) :=
      (Measure.map_map (measurable_of_countable _) (measurable_of_countable _)).symm
    _ = kernel rows i := by rw [lookup_map rows i.val i.isLt]; rfl

theorem stationary (rows : List Row) [NeZero rows.length] (π : Measure (Fin rows.length))
    (hπ : π.bind (kernel rows) = π) : CouplingFromPast.Stationary (law rows) π := by
  unfold CouplingFromPast.Stationary
  have hk : CouplingFromPast.transition (law rows) = kernel rows :=
    funext (transition_eq_kernel rows)
  rw [hk]
  exact hπ

end

end SampLib.RandomMapSupport
