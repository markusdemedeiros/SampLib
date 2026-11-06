import SampLib.General.Laws.FiniteKernels

/-! # Finite-grid slice sampling

The flow between two states sums the reciprocal slice sizes below both weights.
This expression is symmetric, so the target proportional to the weights is invariant.
-/

open MeasureTheory Measure
open scoped ENNReal Classical

namespace SampLib.SliceLaw

noncomputable section

variable {α : Type*} [Fintype α]

/-- Grid positions strictly above a chosen integer height. -/
def level (w : α → ℕ) (h : ℕ) : Finset α := Finset.univ.filter (fun x => h < w x)

@[simp] theorem mem_level (w : α → ℕ) (h : ℕ) (x : α) : x ∈ level w h ↔ h < w x := by
  simp [level]

theorem level_nonempty (w : α → ℕ) (x : α) (h : ℕ) (hx : h < w x) :
    (level w h).Nonempty := ⟨x, (mem_level w h x).mpr hx⟩

/-- Every possible height has a nonempty slice precisely when the cap has a grid anchor. -/
theorem levels_nonempty_iff (w : α → ℕ) (cap : ℕ) (hcap : 0 < cap) :
    (∀ h < cap, (level w h).Nonempty) ↔ ∃ x, cap ≤ w x := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h (cap - 1) (by omega)
    exact ⟨x, by have := (mem_level w (cap - 1) x).mp hx; omega⟩
  · rintro ⟨x, hx⟩ h hh
    exact level_nonempty w x h (hh.trans_le hx)

variable [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Uniform integer height below the cap, then uniform position in that slice. -/
def heightMixture (w : α → ℕ) (cap : ℕ) : Measure α :=
  (cap : ℝ≥0∞)⁻¹ • ∑ h ∈ Finset.range cap, uniformOfFinset (level w h)

theorem isProbabilityMeasure_heightMixture (w : α → ℕ) (cap : ℕ) (hcap : 0 < cap)
    (hanchor : ∃ x, cap ≤ w x) : IsProbabilityMeasure (heightMixture w cap) where
  measure_univ := by
    have hlevels := (levels_nonempty_iff w cap hcap).mpr hanchor
    have hsum : (∑ h ∈ Finset.range cap, uniformOfFinset (level w h) Set.univ) = cap := by
      calc
        _ = ∑ h ∈ Finset.range cap, (1 : ℝ≥0∞) := by
          apply Finset.sum_congr rfl
          intro h hh
          let : IsProbabilityMeasure (uniformOfFinset (level w h)) :=
            isProbabilityMeasure_uniformOfFinset (hlevels h (Finset.mem_range.mp hh))
          exact measure_univ
        _ = cap := by simp
    simp only [heightMixture, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
    rw [hsum, ENNReal.inv_mul_cancel (by exact_mod_cast hcap.ne') (by finiteness)]

omit [MeasurableSingletonClass α] in
/-- The height average preserves arbitrary credits, including infinite ones. -/
theorem heightMixture_expectation (w : α → ℕ) (cap : ℕ) (F : α → ℝ≥0∞) :
    (∑ h ∈ Finset.range cap, ∫⁻ y, F y ∂uniformOfFinset (level w h)) / cap =
      ∫⁻ y, F y ∂heightMixture w cap := by
  simp only [heightMixture, lintegral_smul_measure, lintegral_finsetSum_measure,
    smul_eq_mul, ENNReal.div_eq_inv_mul]

theorem heightMixture_singleton (w : α → ℕ) (cap : ℕ) (y : α) :
    heightMixture w cap {y} =
      (∑ h ∈ Finset.range (min cap (w y)), ((level w h).card : ℝ≥0∞)⁻¹) / cap := by
  have he : (Finset.range cap).filter (fun h => h < w y) =
      Finset.range (min cap (w y)) := by
    ext h
    simp [lt_min_iff]
  simp only [heightMixture, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul,
    Measure.uniformOfFinset_apply_singleton, mem_level]
  rw [← Finset.sum_filter, he, ENNReal.div_eq_inv_mul]

theorem heightMixture_ae_positive (w : α → ℕ) (cap : ℕ) :
    ∀ᵐ y ∂heightMixture w cap, 0 < w y := by
  apply ae_iff_of_countable.mpr
  intro y hy
  by_contra h
  apply hy
  simp [heightMixture_singleton, Nat.eq_zero_of_not_pos h]

/-- A height cap with a grid anchor gives a normalized transition even from outside the grid. -/
def stepLaw (w : α → ℕ) (cap : ℕ) (_hcap : 0 < cap) (_hanchor : ∃ x, cap ≤ w x) : Measure α :=
  heightMixture w cap

instance (w : α → ℕ) (cap : ℕ) (hcap : 0 < cap) (hanchor : ∃ x, cap ≤ w x) :
    IsProbabilityMeasure (stepLaw w cap hcap hanchor) :=
  isProbabilityMeasure_heightMixture w cap hcap hanchor

omit [MeasurableSingletonClass α] in
theorem stepLaw_expectation (w : α → ℕ) (cap : ℕ) (hcap : 0 < cap)
    (hanchor : ∃ x, cap ≤ w x) (F : α → ℝ≥0∞) :
    (∑ h ∈ Finset.range cap, ∫⁻ y, F y ∂uniformOfFinset (level w h)) / cap =
      ∫⁻ y, F y ∂stepLaw w cap hcap hanchor := heightMixture_expectation w cap F

/-- A uniform grid proposal accepts exactly the fraction lying in the chosen slice. -/
theorem acceptance_mass (w : α → ℕ) (h : ℕ) :
    uniformOfFinset (Finset.univ : Finset α) {y | h < w y} =
      ((level w h).card : ℝ≥0∞) / Fintype.card α := by
  rw [Measure.uniformOfFinset_apply]
  simp only [level, Set.mem_ofPred_eq, Finset.card_univ]

theorem acceptance_nonzero (w : α → ℕ) (h : ℕ) (hne : (level w h).Nonempty) :
    uniformOfFinset (Finset.univ : Finset α) {y | h < w y} ≠ 0 := by
  simpa [acceptance_mass, ENNReal.div_eq_zero_iff] using hne.card_ne_zero

/-- Conditioning the enclosing uniform grid leaves the uniform law on its accepted slice. -/
theorem conditioned_uniform (w : α → ℕ) (h : ℕ) (hne : (level w h).Nonempty) :
    (uniformOfFinset (Finset.univ : Finset α) {y | h < w y})⁻¹ •
      (uniformOfFinset (Finset.univ : Finset α)).restrict {y | h < w y} =
        uniformOfFinset (level w h) := by
  have hcard : (Fintype.card α : ℝ≥0∞) ≠ 0 := by
    have : Nonempty α := ⟨hne.choose⟩
    exact_mod_cast Fintype.card_ne_zero
  apply Measure.ext_of_singleton
  intro y
  simp only [Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply (measurableSet_singleton y), Measure.uniformOfFinset_apply_singleton,
    mem_level]
  by_cases hy : h < w y
  · rw [Set.singleton_inter_of_mem (show y ∈ {z | h < w z} from hy),
      Measure.uniformOfFinset_apply_singleton,
      ite_eq_left (Finset.mem_univ y), acceptance_mass,
      ENNReal.inv_div (Or.inl (by finiteness)) (Or.inl hcard),
      ENNReal.div_eq_inv_mul, mul_assoc, Finset.card_univ,
      ENNReal.mul_inv_cancel hcard (by finiteness), mul_one, ite_eq_left hy]
  · rw [Set.singleton_inter_of_notMem (show y ∉ {z | h < w z} from hy),
      measure_empty, mul_zero, ite_eq_right hy]

/-- Zero-weight rows are extended by the identity; positive rows are actual slice transitions. -/
def kernel (w : α → ℕ) (x : α) : Measure α :=
  if 0 < w x then heightMixture w (w x) else dirac x

instance (w : α → ℕ) (x : α) : IsProbabilityMeasure (kernel w x) := by
  by_cases hx : 0 < w x
  · rw [kernel, ite_eq_left hx]
    exact isProbabilityMeasure_heightMixture w (w x) hx ⟨x, le_rfl⟩
  · rw [kernel, ite_eq_right hx]
    infer_instance

omit [MeasurableSingletonClass α] in
theorem kernel_expectation (w : α → ℕ) (x : α) (hx : 0 < w x) (F : α → ℝ≥0∞) :
    (∑ h ∈ Finset.range (w x), ∫⁻ y, F y ∂uniformOfFinset (level w h)) / w x =
      ∫⁻ y, F y ∂kernel w x := by
  rw [kernel, ite_eq_left hx]
  exact heightMixture_expectation w (w x) F

theorem ae_positive (w : α → ℕ) (x : α) (hx : 0 < w x) :
    ∀ᵐ y ∂kernel w x, 0 < w y := by
  rw [kernel, ite_eq_left hx]
  exact heightMixture_ae_positive w (w x)

/-- Each shared height contributes reciprocal slice size, independently of the direction. -/
theorem weighted_flux (w : α → ℕ) (x y : α) :
    (w x : ℝ≥0∞) * kernel w x {y} =
      ∑ h ∈ Finset.range (min (w x) (w y)), ((level w h).card : ℝ≥0∞)⁻¹ := by
  by_cases hx : 0 < w x
  · rw [kernel, ite_eq_left hx, heightMixture_singleton,
      ENNReal.mul_div_cancel (by exact_mod_cast hx.ne') (by finiteness)]
  · simp [kernel, Nat.eq_zero_of_not_pos hx]

theorem flux_symm (w : α → ℕ) (x y : α) :
    (w x : ℝ≥0∞) * kernel w x {y} = (w y : ℝ≥0∞) * kernel w y {x} := by
  rw [weighted_flux, weighted_flux, min_comm]

/-- Normalize the natural weights; only the all-zero target is excluded. -/
def target (w : α → ℕ) (_h : 0 < ∑ x, w x) : Measure α :=
  ((∑ x, w x : ℕ) : ℝ≥0∞)⁻¹ • ∑ x, (w x : ℝ≥0∞) • dirac x

instance (w : α → ℕ) (h : 0 < ∑ x, w x) : IsProbabilityMeasure (target w h) where
  measure_univ := by
    have hz : ((∑ x, w x : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast h.ne'
    simpa [target] using ENNReal.inv_mul_cancel hz (by finiteness)

theorem target_singleton (w : α → ℕ) (h : 0 < ∑ x, w x) (y : α) :
    target w h {y} = (w y : ℝ≥0∞) / (∑ x, w x : ℕ) := by
  simp [target, ENNReal.div_eq_inv_mul, smul_eq_mul, Pi.single_apply, eq_comm]

theorem detailed_balance (w : α → ℕ) (h : 0 < ∑ x, w x) (x y : α) :
    kernel w x {y} * target w h {x} = kernel w y {x} * target w h {y} := by
  rw [target_singleton, target_singleton]
  have hflux := congrArg (fun t : ℝ≥0∞ => t / (∑ z, w z : ℕ)) (flux_symm w x y)
  simpa [ENNReal.div_eq_inv_mul, mul_comm, mul_left_comm, mul_assoc] using hflux

theorem invariant (w : α → ℕ) (h : 0 < ∑ x, w x) :
    (target w h).bind (kernel w) = target w h :=
  FiniteKernels.invariant_of_detailed_balance _ _ (detailed_balance w h)

/-- The state after the requested finite number of slice transitions. -/
abbrev law (w : α → ℕ) := FiniteKernels.iterate (kernel w)

theorem iterate_invariant (w : α → ℕ) (h : 0 < ∑ x, w x) (n : ℕ) :
    (target w h).bind (law w n) = target w h :=
  FiniteKernels.invariant _ _ (invariant w h) n

theorem iterate_expectation_invariant (w : α → ℕ) (h : 0 < ∑ x, w x)
    (n : ℕ) (F : α → ℝ≥0∞) :
    ∫⁻ x, (∫⁻ y, F y ∂law w n x) ∂target w h = ∫⁻ y, F y ∂target w h := by
  rw [← Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aemeasurable, iterate_invariant]

/-- Positive states remain positive after any finite number of slice transitions. -/
theorem iterate_ae_positive (w : α → ℕ) (n : ℕ) (x : α) (hx : 0 < w x) :
    ∀ᵐ y ∂law w n x, 0 < w y := by
  induction n generalizing x with
  | zero => simpa [law, FiniteKernels.iterate]
  | succ n ih =>
    change ∀ᵐ y ∂(kernel w x).bind (law w n), 0 < w y
    rw [ae_iff, Measure.bind_apply (Set.to_countable _).measurableSet
      (measurable_of_countable _).aemeasurable]
    exact lintegral_eq_zero_of_ae_eq_zero
      ((ae_positive w x hx).mono fun y hy => ae_iff.mp (ih y hy))

end

end SampLib.SliceLaw
