module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # Accepting a proposal with a value-dependent probability

The accepted law is the proposal weighted by its acceptance probability. A
bounded amplification factor handles both genuine retries and certain acceptance.
-/

open MeasureTheory Measure
open ENNReal (ofReal ofReal_add ofReal_one)
open scoped ENNReal NNReal

namespace SampLib.AcceptedProposal

noncomputable section

variable {α : Type _} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
  (g : α → unitInterval)

/-- The two complementary parts of a proposal's mass. -/
def weight (x : α) : ℝ≥0∞ := ofReal (g x : ℝ)
def rejectedWeight (x : α) : ℝ≥0∞ := ofReal (1 - (g x : ℝ))
def mass : ℝ≥0∞ := ∫⁻ x, weight g x ∂μ
def rejectedMass : ℝ≥0∞ := ∫⁻ x, rejectedWeight g x ∂μ

theorem measurable_weight (hg : Measurable g) : Measurable (weight g) :=
  ENNReal.measurable_ofReal.comp (measurable_subtype_coe.comp hg)

theorem measurable_rejectedWeight (hg : Measurable g) : Measurable (rejectedWeight g) :=
  ENNReal.measurable_ofReal.comp (measurable_const.sub (measurable_subtype_coe.comp hg))

theorem mass_le_one : mass μ g ≤ 1 := by
  calc
    _ ≤ ∫⁻ _ : α, (1 : ℝ≥0∞) ∂μ :=
      lintegral_mono fun x => ENNReal.ofReal_le_one.mpr (g x).2.2
    _ = 1 := by simp

theorem rejectedMass_le_one : rejectedMass μ g ≤ 1 := by
  calc
    _ ≤ ∫⁻ _ : α, (1 : ℝ≥0∞) ∂μ :=
      lintegral_mono fun x => ENNReal.ofReal_le_one.mpr (sub_le_self _ (g x).2.1)
    _ = 1 := by simp

theorem mass_ne_top : mass μ g ≠ ∞ := ne_of_lt ((mass_le_one μ g).trans_lt (by simp))

/-- Acceptance and rejection partition a probability measure. -/
theorem mass_add_rejectedMass (hg : Measurable g) : mass μ g + rejectedMass μ g = 1 := by
  rw [mass, rejectedMass, ← lintegral_add_left (measurable_weight g hg) (rejectedWeight g)]
  have hpoint (x : α) : weight g x + rejectedWeight g x = 1 := by
    rw [weight, rejectedWeight, ← ofReal_add (g x).2.1 (sub_nonneg.mpr (g x).2.2)]
    rw [show (g x : ℝ) + (1 - (g x : ℝ)) = 1 by ring, ofReal_one]
  simp_rw [hpoint]
  simp

/-- Proposal measure normalized after weighting by its acceptance probability. -/
def law (_h : mass μ g ≠ 0) : Measure α := (mass μ g)⁻¹ • μ.withDensity (weight g)

instance (h : mass μ g ≠ 0) : IsProbabilityMeasure (law μ g h) where
  measure_univ := by
    simp only [law, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel h (mass_ne_top μ g)

/-- Expected output credit under the accepted proposal law. -/
def credit (h : mass μ g ≠ 0) (F : α → ℝ≥0∞) : ℝ≥0∞ := ∫⁻ x, F x ∂law μ g h

/-- A finite amplification factor strictly above one for every positive acceptance mass. -/
def factor : ℝ≥0 := 1 + (mass μ g).toNNReal

theorem one_lt_factor (h : mass μ g ≠ 0) : 1 < factor μ g :=
  lt_add_of_pos_right _ (ENNReal.toNNReal_pos h (mass_ne_top μ g))

/-- The acceptance coin returns the output credit or the amplified retry budget. -/
def kernel (h : mass μ g ≠ 0) (F : α → ℝ≥0∞) (ε : ℝ≥0∞) (x : α) : ℝ≥0∞ :=
  weight g x * F x + rejectedWeight g x * (credit μ g h F + factor μ g * ε)

omit [IsProbabilityMeasure μ] in
theorem measurable_kernel (hg : Measurable g) (h : mass μ g ≠ 0)
    (F : α → ℝ≥0∞) (hF : Measurable F) (ε : ℝ≥0∞) :
    Measurable (kernel μ g h F ε) :=
  ((measurable_weight g hg).mul hF).add
    ((measurable_rejectedWeight g hg).mul measurable_const)

/-- Weighting conserves output credit; the complementary mass funds amplification. -/
theorem expectation_preservation (hg : Measurable g) (h : mass μ g ≠ 0)
    (F : α → ℝ≥0∞) (hF : Measurable F) (ε : ℝ≥0∞) :
    ∫⁻ x, kernel μ g h F ε x ∂μ ≤ credit μ g h F + ε := by
  have hcredit : ∫⁻ x, weight g x * F x ∂μ = mass μ g * credit μ g h F := by
    rw [credit, law, lintegral_smul_measure, smul_eq_mul,
      lintegral_withDensity_eq_lintegral_mul _ (measurable_weight g hg) hF,
      ← mul_assoc, ENNReal.mul_inv_cancel h (mass_ne_top μ g), one_mul]
    rfl
  have hamp : rejectedMass μ g * (factor μ g : ℝ≥0∞) ≤ 1 := by
    calc
      _ = rejectedMass μ g + rejectedMass μ g * mass μ g := by
        simp [factor, ENNReal.coe_toNNReal (mass_ne_top μ g), mul_add]
      _ ≤ rejectedMass μ g + mass μ g :=
        add_le_add le_rfl (mul_le_of_le_one_left
          (show 0 ≤ mass μ g from zero_le) (rejectedMass_le_one μ g))
      _ = 1 := by rw [add_comm, mass_add_rejectedMass μ g hg]
  calc
    _ = mass μ g * credit μ g h F +
        rejectedMass μ g * (credit μ g h F + factor μ g * ε) := by
      change (∫⁻ x, weight g x * F x +
        rejectedWeight g x * (credit μ g h F + factor μ g * ε) ∂μ) = _
      have hm : Measurable (fun x => weight g x * F x) := (measurable_weight g hg).mul hF
      rw [lintegral_add_left hm _,
        lintegral_mul_const _ (measurable_rejectedWeight g hg), hcredit]
      rfl
    _ = credit μ g h F + (rejectedMass μ g * (factor μ g : ℝ≥0∞)) * ε := by
      calc
        _ = (mass μ g + rejectedMass μ g) * credit μ g h F +
            (rejectedMass μ g * (factor μ g : ℝ≥0∞)) * ε := by ring
        _ = _ := by rw [mass_add_rejectedMass μ g hg, one_mul]
    _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_left (show 0 ≤ ε from zero_le) hamp)

end

end SampLib.AcceptedProposal
