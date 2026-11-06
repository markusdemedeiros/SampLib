import SampLib.General.Laws.CouplingFromPast

/-! # A bounded remaining-round potential for doubling CFTP

Before reaching the coalescent block length, doubling lowers a finite countdown.
Afterwards, every extension coalesces with uniformly positive probability. The
resulting one-round drift pays a fixed amplification of the remaining-round potential.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace SampLib.CouplingFromPast

noncomputable section

namespace Block

variable {n : ℕ} {ρ : Measure (Map n)} [IsProbabilityMeasure ρ]

def work (b : Block ρ) (h : ℕ) : ℝ≥0 := (b.length - h : ℕ) + b.chance⁻¹

def ceiling (b : Block ρ) : ℝ≥0 := b.length + b.chance⁻¹

def amplification (b : Block ρ) : ℝ≥0 := 1 + b.ceiling⁻¹

theorem one_le_work (b : Block ρ) (h : ℕ) : 1 ≤ b.work h := by
  have hq : 1 ≤ b.chance⁻¹ := (one_le_inv₀ b.positive).mpr b.chance_le_one
  exact hq.trans (le_add_of_nonneg_left (by positivity))

omit [IsProbabilityMeasure ρ] in
theorem work_le_ceiling (b : Block ρ) (h : ℕ) : b.work h ≤ b.ceiling := by
  change ((b.length - h : ℕ) : ℝ≥0) + b.chance⁻¹ ≤ (b.length : ℝ≥0) + b.chance⁻¹
  exact add_le_add (by exact_mod_cast Nat.sub_le b.length h) le_rfl

omit [IsProbabilityMeasure ρ] in
theorem ceiling_pos (b : Block ρ) : 0 < b.ceiling := by
  exact add_pos_of_nonneg_of_pos (by positivity) (inv_pos.mpr b.positive)

omit [IsProbabilityMeasure ρ] in
theorem one_lt_amplification (b : Block ρ) : 1 < b.amplification :=
  lt_add_of_pos_right _ (inv_pos.mpr b.ceiling_pos)

omit [IsProbabilityMeasure ρ] in
private theorem work_drop (b : Block ρ) (h : ℕ) (hh : 0 < h) (hL : h < b.length) :
    b.work (h * 2) + 1 ≤ b.work h := by
  have hd : b.length - h * 2 + 1 ≤ b.length - h := by omega
  have hd' : ((b.length - h * 2 : ℕ) : ℝ≥0) + 1 ≤ (b.length - h : ℕ) := by
    exact_mod_cast hd
  change ((b.length - h * 2 : ℕ) : ℝ≥0) + b.chance⁻¹ + 1 ≤
    ((b.length - h : ℕ) : ℝ≥0) + b.chance⁻¹
  calc
    _ = (((b.length - h * 2 : ℕ) : ℝ≥0) + 1) + b.chance⁻¹ := by ring
    _ ≤ _ := add_le_add hd' le_rfl

private theorem geometric_work (b : Block ρ) :
    (1 - (b.chance : ℝ≥0∞)) * (b.chance⁻¹ : ℝ≥0) + 1 = (b.chance⁻¹ : ℝ≥0) := by
  have hq := b.chance_le_one
  have hreal : (1 - b.chance) * b.chance⁻¹ + 1 = b.chance⁻¹ := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_sub hq, NNReal.coe_inv,
      NNReal.coe_one]
    have hn : (b.chance : ℝ) ≠ 0 := by exact_mod_cast b.positive.ne'
    field_simp
    ring
  exact_mod_cast hreal

/-- One expected extension round is lost, counting only still-uncoalesced histories. -/
theorem drift (b : Block ρ) (h : ℕ) (hh : 0 < h) (newer : List (Map n)) :
    (IIDList.law ρ h) {older | ¬Coalesces (older ++ newer)} * b.work (h * 2) + 1 ≤
      b.work h := by
  by_cases hL : h < b.length
  · have hp : (IIDList.law ρ h) {older | ¬Coalesces (older ++ newer)} ≤ 1 := prob_le_one
    have hd : (b.work (h * 2) : ℝ≥0∞) + 1 ≤ b.work h := by
      exact_mod_cast b.work_drop h hh hL
    have hm : (IIDList.law ρ h) {older | ¬Coalesces (older ++ newer)} *
        b.work (h * 2) ≤ (b.work (h * 2) : ℝ≥0∞) := by
      simpa only [one_mul] using mul_le_mul' hp (le_refl (b.work (h * 2) : ℝ≥0∞))
    exact (add_le_add hm (le_refl (1 : ℝ≥0∞))).trans hd
  · have hnext : b.length ≤ h * 2 := by omega
    simp only [work, Nat.sub_eq_zero_of_le (le_of_not_gt hL),
      Nat.sub_eq_zero_of_le hnext, Nat.cast_zero, zero_add]
    have hm := mul_le_mul' (b.failure_bound h (le_of_not_gt hL) newer)
      (le_refl ((b.chance⁻¹ : ℝ≥0) : ℝ≥0∞))
    exact (add_le_add hm (le_refl (1 : ℝ≥0∞))).trans (le_of_eq b.geometric_work)

/-- The bounded potential leaves room for one fixed amplification above one. -/
theorem amplified_drift (b : Block ρ) (h : ℕ) (hh : 0 < h)
    (newer : List (Map n)) (ε : ℝ≥0∞) :
    (IIDList.law ρ h) {older | ¬Coalesces (older ++ newer)} *
        (b.amplification * ε * b.work (h * 2)) ≤ ε * b.work h := by
  let A : ℝ≥0∞ := (IIDList.law ρ h) {older | ¬Coalesces (older ++ newer)} * b.work (h * 2)
  have hd : A + 1 ≤ b.work h := b.drift h hh newer
  have hb : A ≤ b.ceiling :=
    (le_add_of_nonneg_right (by positivity)).trans
      (hd.trans (by exact_mod_cast b.work_le_ceiling h))
  have hscale : (b.ceiling⁻¹ : ℝ≥0) * A ≤ (1 : ℝ≥0∞) := by
    have hc : (b.ceiling⁻¹ : ℝ≥0) * (b.ceiling : ℝ≥0∞) = 1 := by
      norm_cast
      exact inv_mul_cancel₀ b.ceiling_pos.ne'
    exact (mul_le_mul' le_rfl hb).trans (le_of_eq hc)
  have hampl : (b.amplification : ℝ≥0∞) * A ≤ b.work h := by
    calc
      _ = A + (b.ceiling⁻¹ : ℝ≥0) * A := by simp [amplification, add_mul]
      _ ≤ A + 1 := add_le_add (le_refl A) hscale
      _ ≤ _ := hd
  simpa only [A, mul_assoc, mul_left_comm, mul_comm] using mul_le_mul' (le_refl ε) hampl

omit [IsProbabilityMeasure ρ] in
/-- Scale any initial slack to fund the potential at every horizon. -/
theorem initial_work (b : Block ρ) (h : ℕ) (ε : ℝ≥0∞) :
    (ε * (b.ceiling⁻¹ : ℝ≥0)) * b.work h ≤ ε := by
  have hc : (b.ceiling⁻¹ : ℝ≥0) * (b.work h : ℝ≥0∞) ≤ 1 := by
    have hb : (b.work h : ℝ≥0∞) ≤ b.ceiling := by exact_mod_cast b.work_le_ceiling h
    have he : (b.ceiling⁻¹ : ℝ≥0) * (b.ceiling : ℝ≥0∞) = 1 := by
      norm_cast
      exact inv_mul_cancel₀ b.ceiling_pos.ne'
    exact (mul_le_mul' le_rfl hb).trans (le_of_eq he)
  simpa only [mul_assoc, mul_one] using (mul_le_mul' (le_refl ε) hc)

end Block

/-- Credit after drawing an older block; completed histories require no round slack. -/
def extensionCredit {n : ℕ} {ρ : Measure (Map n)} (b : Block ρ)
    (π : Measure (Fin n)) (h : ℕ) (newer : List (Map n)) (F : Fin n → ℝ≥0∞)
    (ε : ℝ≥0∞) (older : List (Map n)) : ℝ≥0∞ :=
  credit π (older ++ newer) F +
    if Coalesces (older ++ newer) then 0 else b.amplification * ε * b.work (h * 2)

/-- Stationarity pays the output credit, and coalescence pays the amplified retry. -/
theorem expectation {n : ℕ} (ρ : Measure (Map n)) [IsProbabilityMeasure ρ]
    (π : Measure (Fin n)) (hπ : Stationary ρ π) (b : Block ρ)
    (h : ℕ) (hh : 0 < h) (newer : List (Map n)) (F : Fin n → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ older, extensionCredit b π h newer F ε older ∂IIDList.law ρ h ≤
      credit π newer F + ε * b.work h := by
  classical
  unfold extensionCredit
  rw [lintegral_add_left (measurable_of_countable _),
    block_expectation ρ π hπ h newer F]
  have hwork : (fun older : List (Map n) =>
      if Coalesces (older ++ newer) then 0 else b.amplification * ε * b.work (h * 2)) =
      {older | ¬Coalesces (older ++ newer)}.indicator
        (fun _ => (b.amplification : ℝ≥0∞) * ε * b.work (h * 2)) := by
    funext older
    by_cases hc : Coalesces (older ++ newer)
    · rw [ite_eq_left hc, Set.indicator_of_notMem (not_not.mpr hc)]
    · rw [ite_eq_right hc, Set.indicator_of_mem hc]
  rw [hwork, lintegral_indicator (Set.to_countable _).measurableSet, setLIntegral_const]
  apply add_le_add le_rfl
  simpa only [mul_comm] using b.amplified_drift h hh newer ε

end

end SampLib.CouplingFromPast
