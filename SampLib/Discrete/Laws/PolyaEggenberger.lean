import Metrology.ProbLang.Discrete
import SampLib.Common.Laws.Urn

/-! # Pólya–Eggenberger count law

The count law is induced by the exchangeable color sequence of a reinforced urn.
Each word's mass is a quotient of rising products, depending only on its counts.
-/

open scoped ENNReal

namespace SampLib.PolyaEggenberger

noncomputable section

open MeasureTheory Measure Urn

/-- Distribution of the successive colors in the standard reinforced-urn process. -/
def wordLaw : ℕ → ℕ → ℕ → ℕ → Measure (List Bool)
  | 0, _, _, _ => dirac []
  | n + 1, ones, zeros, reinforcement =>
      (RealCoin.pmf (bias ones zeros) true •
        (wordLaw n (ones + reinforcement) zeros reinforcement).map (List.cons true)) +
      (RealCoin.pmf (bias ones zeros) false •
        (wordLaw n ones (zeros + reinforcement) reinforcement).map (List.cons false))

instance (n ones zeros reinforcement : ℕ) :
    IsProbabilityMeasure (wordLaw n ones zeros reinforcement) := by
  induction n generalizing ones zeros with
  | zero => dsimp [wordLaw]; infer_instance
  | succ n ih =>
    let := ih (ones + reinforcement) zeros
    let := ih ones (zeros + reinforcement)
    constructor
    simpa [wordLaw, Measure.map_apply (measurable_of_countable (List.cons true)),
      Measure.map_apply (measurable_of_countable (List.cons false))]
      using RealCoin.pmf_sum (bias ones zeros)

/-- Number of marked draws in the reinforced-urn color sequence. -/
def law (n ones zeros reinforcement : ℕ) : Measure ℕ :=
  (wordLaw n ones zeros reinforcement).map (List.count true)

instance (n ones zeros reinforcement : ℕ) :
    IsProbabilityMeasure (law n ones zeros reinforcement) := by
  constructor
  rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
  simp

/-- Rising product with integer step, including step zero. -/
def rising (start step : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => start * rising (start + step) step n

/-- Each color word has the usual rising-product mass, hence is exchangeable. -/
theorem word_mass (xs : List Bool) (ones zeros reinforcement : ℕ)
    (h : xs = [] ∨ 0 < ones + zeros) :
    wordLaw xs.length ones zeros reinforcement {xs} =
      ((rising ones reinforcement (xs.count true) *
        rising zeros reinforcement (xs.count false) : ℕ) : ℝ≥0∞) /
        rising (ones + zeros) reinforcement xs.length := by
  induction xs generalizing ones zeros with
  | nil => simp [wordLaw, rising]
  | cons b xs ih =>
    have ht : 0 < ones + zeros := h.resolve_left (by simp)
    have htrue : 0 < (ones + reinforcement) + zeros := by omega
    have hfalse : 0 < ones + (zeros + reinforcement) := by omega
    cases b
    · have hp₀ : (List.cons false) ⁻¹' {false :: xs} = {xs} := by ext; simp
      have hp₁ : (List.cons true) ⁻¹' {false :: xs} = ∅ := by ext; simp
      simp only [List.length_cons, wordLaw, Measure.add_apply, Measure.smul_apply,
        smul_eq_mul, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
        hp₀, hp₁, measure_empty, mul_zero, zero_add]
      rw [ih ones (zeros + reinforcement) (Or.inr hfalse), pmf_false ones zeros ht]
      simp only [List.count_cons_self, List.count_cons_of_ne Bool.false_ne_true, rising,
        Nat.cast_mul]
      rw [show ones + (zeros + reinforcement) = (ones + zeros) + reinforcement by omega]
      rw [ENNReal.mul_div_mul_comm (Or.inr (ENNReal.natCast_ne_top _))
        (Or.inl (ENNReal.natCast_ne_top _))]
      simp only [Nat.cast_add, ENNReal.div_eq_inv_mul]
      ring
    · have hp₀ : (List.cons false) ⁻¹' {true :: xs} = ∅ := by ext; simp
      have hp₁ : (List.cons true) ⁻¹' {true :: xs} = {xs} := by ext; simp
      simp only [List.length_cons, wordLaw, Measure.add_apply, Measure.smul_apply,
        smul_eq_mul, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
        hp₀, hp₁, measure_empty, mul_zero, add_zero]
      rw [ih (ones + reinforcement) zeros (Or.inr htrue), pmf_true ones zeros ht]
      simp only [List.count_cons_self, List.count_cons_of_ne (by decide : true ≠ false), rising,
        Nat.cast_mul]
      rw [show (ones + reinforcement) + zeros = (ones + zeros) + reinforcement by omega]
      rw [ENNReal.mul_div_mul_comm (Or.inr (ENNReal.natCast_ne_top _))
        (Or.inl (ENNReal.natCast_ne_top _))]
      simp only [Nat.cast_add, ENNReal.div_eq_inv_mul]
      ring

/-- Conditional continuation credit after the first color. -/
def continuation (n ones zeros reinforcement : ℕ) (F : ℕ → ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then ∫⁻ k, F (k + 1) ∂law n (ones + reinforcement) zeros reinforcement
  else ∫⁻ k, F k ∂law n ones (zeros + reinforcement) reinforcement

/-- Counting a word turns the first-color partition into the urn expectation. -/
theorem expectation (n ones zeros reinforcement : ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ b, continuation n ones zeros reinforcement F b ∂RealCoin.law (bias ones zeros) =
      ∫⁻ k, F k ∂law (n + 1) ones zeros reinforcement := by
  simp [law, wordLaw, RealCoin.lintegral_law, RealCoin.credit, continuation,
    lintegral_map (measurable_of_countable _) (measurable_of_countable _), smul_eq_mul]

end

end SampLib.PolyaEggenberger
