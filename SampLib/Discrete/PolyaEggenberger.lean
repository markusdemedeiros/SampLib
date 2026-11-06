import SampLib.Common.Laws.Urn
import Samplers.Discrete
import Metrology.Iris.LocalBI

/-! # Pólya–Eggenberger sampling

The count law is induced by the exchangeable color sequence of a reinforced urn.
Each word's mass is a quotient of rising products, depending only on its counts.
-/

open Set ProbLang
open scoped ENNReal

namespace SampLib.PolyaEggenberger

noncomputable section

section mathematics

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

end mathematics

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Reinforced urn counts, allowing both absent colors and zero reinforcement. -/
theorem twp_polyaEggenberger (E : CoPset) (n ones zeros reinforcement : ℕ)
    (h : n = 0 ∨ 0 < ones + zeros) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ k, F k ∂law n ones zeros reinforcement) -∗
      tglWp E pl(&Occil.polyaEggenberger #int (n : ℤ) #int (ones : ℤ)
        #int (zeros : ℤ) #int (reinforcement : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k))) := by
  induction n generalizing ones zeros F with
  | zero =>
    iintro Hcredit
    twp_pures
    twp_value
    imodintro
    iexists 0
    isimp only [law, wordLaw, MeasureTheory.lintegral_map (measurable_of_countable _)
      (measurable_of_countable _), MeasureTheory.lintegral_dirac, List.count_nil] at Hcredit
    iframe Hcredit
    itrivial
  | succ n ih =>
    have ht : 0 < ones + zeros := h.resolve_left (Nat.succ_ne_zero n)
    have ht₁ : 0 < (ones + reinforcement) + zeros := by omega
    have ht₀ : 0 < ones + (zeros + reinforcement) := by omega
    have hcoin : IsDistSpec (GF := GF) E
        pl(&Occil.rationalCoin #int (ones : ℤ) #int ((ones : ℤ) + zeros))
        (RealCoin.law (Urn.bias ones zeros)) Val.bool := by
      simpa only [Urn.bias, dite_eq_left ht, Nat.cast_add] using
        RationalCoin.rationalCoin_distSpec (GF := GF) E ones (ones + zeros)
          (by omega) (by omega) (by omega)
    iintro Hcredit
    iterate 16 twp_pure
    simp only [RationalCoin.rationalCoin_closeRec, RationalCoin.rationalCoin_openRec]
    twp_bind pl(&Occil.rationalCoin #int (ones : ℤ) #int ((ones : ℤ) + zeros))
    isimp only [← expectation n ones zeros reinforcement F] at Hcredit
    iapply (hcoin.wp (continuation n ones zeros reinforcement F)
      (measurable_of_countable _) _) $$ Hcredit
    iintro %b Hcredit
    cases b
    · iterate 3 twp_pure
      rw [Nat.cast_add_one, add_sub_cancel_right, ← Nat.cast_add]
      simp only [Exp.ofVal]
      twp_bind pl(&Occil.polyaEggenberger #int (n : ℤ) #int (ones : ℤ)
        #int ((zeros + reinforcement : ℕ) : ℤ) #int (reinforcement : ℤ))
      iapply tglWp_wand
      isplitl [Hcredit]
      · isimp only [continuation, Bool.false_eq_true, ite_false] at Hcredit
        iapply (ih ones (zeros + reinforcement) (Or.inr ht₀) F) $$ Hcredit
      iintro %v ⟨%k, %hv, Hcredit⟩
      iapply (tglWp_value (v := v))
      iexists k
      iframe Hcredit
      ipureintro
      exact hv
    · iterate 3 twp_pure
      rw [Nat.cast_add_one, add_sub_cancel_right, ← Nat.cast_add]
      simp only [Exp.ofVal]
      twp_bind pl(&Occil.polyaEggenberger #int (n : ℤ) #int ((ones + reinforcement : ℕ) : ℤ)
        #int (zeros : ℤ) #int (reinforcement : ℤ))
      iapply tglWp_wand
      isplitl [Hcredit]
      · isimp only [continuation, ite_true] at Hcredit
        iapply (ih (ones + reinforcement) zeros (Or.inr ht₁) (fun k => F (k + 1))) $$ Hcredit
      iintro %v ⟨%k, %hv, Hcredit⟩
      subst v
      twp_pures
      twp_value
      imodintro
      iexists k + 1
      iframe Hcredit
      ipureintro
      apply Val.ext
      simp [add_comm]

/-- Typed Pólya–Eggenberger law on the entire terminating natural-input domain. -/
theorem polyaEggenberger_distSpec (E : CoPset) (n ones zeros reinforcement : ℕ)
    (h : n = 0 ∨ 0 < ones + zeros) :
    IsDistSpec (GF := GF) E
      pl(&Occil.polyaEggenberger #int (n : ℤ) #int (ones : ℤ)
        #int (zeros : ℤ) #int (reinforcement : ℤ))
      (law n ones zeros reinforcement) (fun k : ℕ => Val.int (k : ℤ)) where
  spec F _ := wand_entails (twp_polyaEggenberger E n ones zeros reinforcement h F)

end specification

end

end SampLib.PolyaEggenberger
