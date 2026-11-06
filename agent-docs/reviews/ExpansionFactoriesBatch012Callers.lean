import SampLib.Constants.FromApproximateDigits
import SampLib.Bernoulli.ExpMinusShifted
import SampLib.Bernoulli.TanhHalfShifted
import SampLib.Bernoulli.ExpMinusShiftPower
import SampLib.Constants.Laws.ApproximateDigits
import SampLib.Templates
import Metrology.Iris.LocalBI
open ProbLang
open scoped ENNReal
namespace ExpansionFactoriesReview
noncomputable section
open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib
variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)
theorem frame {E : CoPset} {e : Exp rT} {μ : MeasureTheory.Measure Bool}
    [MeasureTheory.IsProbabilityMeasure μ]
    (h : IsDistSpec (GF := GF) E e μ Val.bool) (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂μ) ∗ I -∗ tglWp E e
      (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply (h.wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HI
  itrivial

private def slowZero : FromApproximateDigits.Model where
  base := 2
  atLeastTwo := by norm_num
  probability := 0
  approximation := fun _ => 1
  accurate := by intro n; norm_num

-- Both first digits retry for a legal extreme certificate; no one-round half-bound holds.
example (v : Fin 2) : ¬(1 : ℤ)+1 ≤ v.val ∧ ¬(v.val : ℤ) ≤ 1-2 := by
  have := v.isLt
  omega
example : slowZero.credit 0 (fun b => if b then ∞ else 0) 0 0 = 1 := by
  rw [FromApproximateDigits.Model.credit, pow_zero, RadixPosterior.credit,
    RadixPosterior.law_one_zero]
  calc
    _ = ∫⁻ _ : ℝ, (1 : ℝ≥0∞) ∂DyadicPosterior.unitLaw := by
      apply MeasureTheory.lintegral_congr_ae
      have hu : ∀ᵐ u ∂DyadicPosterior.unitLaw, u ∈ Set.Ico (0 : ℝ) 1 := by
        simpa only [DyadicPosterior.law_nil] using DyadicPosterior.ae_mem_unit []
      filter_upwards [hu] with u hu
      have hm : u ∈ (slowZero.enclosure 0).uncertain := by
        norm_num [FromApproximateDigits.Model.enclosure, slowZero,
          FromBounds.Interval.uncertain, FromBounds.Interval.left,
          FromBounds.Interval.right] at ⊢
        exact hu
      change (if u < (0 : ℝ) then (∞ : ℝ≥0∞) else 0) +
        (slowZero.enclosure 0).uncertain.indicator (fun _ => 1) u = 1
      simp [not_lt.mpr hu.1, hm]
    _ = 1 := by simp

example : RadixPosterior.credit 10 (-2) (fun u => if u < (-1 : ℝ) then ∞ else 0) = 0 := by
  unfold RadixPosterior.credit
  calc
    _ = ∫⁻ _ : ℝ, (0 : ℝ≥0∞) ∂RadixPosterior.law 10 (-2) := by
      apply MeasureTheory.lintegral_congr_ae
      filter_upwards [RadixPosterior.ae_mem_cell 10 (by norm_num) (-2)] with u hu
      norm_num [RadixPosterior.cell] at hu
      have h : ¬u < (-1 : ℝ) := by linarith [hu.1]
      simp [h]
    _ = 0 := by simp

variable [ProbLangDist.IsUniformInt rT]
example (E : CoPset) (p : unitInterval) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b)
    (coin : Val rT) (hc : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (ExpMinusShifted.expMinusShifted_distSpec E p a b ha hb coin hc) F I
example (E : CoPset) (p : unitInterval) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b)
    (coin : Val rT) (hc : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (TanhHalfShifted.tanhHalfShifted_distSpec E p a b ha hb coin hc) F I
example (E : CoPset) (p : unitInterval) (m k : ℕ) (coin : Val rT)
    (hc : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (ExpMinusShiftPower.expMinusShiftPower_distSpec E p m k coin hc) F I
omit [ProbLangDist.IsUniformInt rT] in
example (E : CoPset) (n k : ℕ) (I : IProp GF) : I ⊢
    tglWp E pl(&Occil.FactoryExtra.choose #int (n : ℤ) #int (k : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (n.choose k : ℤ)⌝ ∗ I)) := by
  iintro HI
  iapply tglWp_wand
  isplitl []
  · iapply FactoryChoose.twp_choose E n k
  iintro %v %hv
  subst v
  iframe HI
  itrivial
example : (ExpMinusShifted.bias 0 0 1 (by norm_num) (by norm_num) : ℝ) = 1 := by
  rw [ExpMinusShifted.bias_coe]
  norm_num
example : (TanhHalfShifted.bias 0 0 1 (by norm_num) (by norm_num) : ℝ) = 0 := by
  rw [TanhHalfShifted.bias_coe]
  norm_num
example : (TanhHalfShifted.bias 1 1 1 (by norm_num) (by norm_num) : ℝ) = Real.tanh 1 := by
  rw [TanhHalfShifted.bias_coe]
  norm_num
example (p : unitInterval) (m : ℕ) :
    (ExpMinusShiftPower.bias p m 0 : ℝ) = Real.exp (-1) := by
  rw [ExpMinusShiftPower.bias_coe]
  simp
example : (ExpMinusShiftPower.bias 0 0 0 : ℝ) = Real.exp (-1) := by
  rw [ExpMinusShiftPower.bias_coe]
  norm_num
example : (ExpMinusShiftPower.bias 1 1 2 : ℝ) = Real.exp (-4) := by
  rw [ExpMinusShiftPower.bias_coe]
  norm_num
example : RealCoin.credit (ExpMinusShiftPower.bias 0 0 1)
    (fun b => if b then 0 else ∞) = 0 := by
  have hb : ExpMinusShiftPower.bias 0 0 1 = 1 := by
    apply Subtype.ext
    rw [ExpMinusShiftPower.bias_coe]
    norm_num
  rw [hb]
  simp [RealCoin.credit, RealCoin.pmf]
example : RealCoin.credit (TanhHalfShifted.bias 0 0 1 (by norm_num) (by norm_num))
    (fun b => if b then ∞ else 0) = 0 := by
  have hb : TanhHalfShifted.bias 0 0 1 (by norm_num) (by norm_num) = 0 := by
    apply Subtype.ext
    rw [TanhHalfShifted.bias_coe]
    norm_num
  rw [hb]
  simp [RealCoin.credit, RealCoin.pmf]
example (E : CoPset) (D : FromApproximateDigits.Model) (oracle : Val rT)
    (ho : ∀ n : ℕ, ⊢ tglWp E pl(&oracle.fst #int ((n+1 : ℕ) : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (D.approximation n)⌝)))
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (FromApproximateDigits.fromApproximateDigits_distSpec E D oracle ho) F I

-- `read` deliberately collides with the private recursive template's nominal binder.
private def radixOracle {rT : Type} : Val rT :=
  ⟨pl(fun position, if #false then read position else #1), .lam (by is_lc), by is_lc⟩
example {rT : Type} : (radixOracle (rT := rT)).fst.fv ≠ ∅ := by
  simp [radixOracle, Exp.fv, Exp.close, Exp.closeRec]
omit [ProbLangDist.IsUniformInt rT] in
private theorem radixOracle_spec (E : CoPset) (n : ℕ) :
    ⊢ tglWp E pl(&(radixOracle (rT := rT)).fst #int ((n+1 : ℕ) : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int 1⌝)) := by
  twp_pures
  twp_value
  imodintro
  ipureintro
  rfl
example (E : CoPset) (I : IProp GF) :=
  frame (FromApproximateDigits.fromApproximateDigits_distSpec E slowZero
    (radixOracle (rT := rT)) (fun n => radixOracle_spec E n))
    (fun b => if b then ∞ else 0) I

#print axioms SampLib.FromApproximateDigits.fromApproximateDigits_distSpec
#print axioms SampLib.FromApproximateDigits.twp_fromApproximateDigits
#print axioms SampLib.FromApproximateDigits.Model.exists_horizon

#print axioms SampLib.ExpMinusShifted.expMinusShifted_distSpec
#print axioms SampLib.ExpMinusShifted.expectation
#print axioms SampLib.TanhHalfShifted.tanhHalfShifted_distSpec
#print axioms SampLib.TanhHalfShifted.bias_coe
#print axioms SampLib.ExpMinusShiftPower.expMinusShiftPower_distSpec
#print axioms SampLib.ShiftPowerCore.twp_loop
#print axioms SampLib.ShiftPowerCore.expectation
#print axioms SampLib.FactoryChoose.twp_choose
#print axioms SampLib.BinomialShiftPower.value_zero
#print axioms SampLib.BinomialShiftPower.product

#print axioms SampLib.RadixPosterior.credit_split
#print axioms SampLib.RadixPosterior.law_eq_uniform
#print axioms SampLib.FromApproximateDigits.Model.expectation
#print axioms SampLib.FromApproximateDigits.Model.unresolved_credit
end
end ExpansionFactoriesReview
