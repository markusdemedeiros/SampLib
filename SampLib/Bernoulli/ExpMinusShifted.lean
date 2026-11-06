import SampLib.Bernoulli.Laws.ShiftedExponential
import SampLib.Bernoulli.ExpMinusRational
import SampLib.Bernoulli.ExpMinusMartingale
import Samplers.Bernoulli.Exponential

/-! # The shifted negative-exponential factory (derived)

The actual rational and martingale exponentials are called independently; their
product adds the rational shift to the unknown input probability.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.ExpMinusShifted

noncomputable section

abbrev bias := ShiftedExponential.bias

theorem bias_coe (p : unitInterval) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) :
    (bias p a b ha hb : ℝ) = Real.exp (-((a : ℝ) / b + (p : ℝ))) := rfl

private theorem product_bias (p : unitInterval) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) :
    ExpMinusRational.bias a b ha hb * FactorialSeriesFactory.bias .exp p = bias p a b ha hb := by
  apply Subtype.ext
  simp only [Set.Icc.coe_mul, FactorialSeriesFactory.bias_exp_coe]
  exact ShiftedExponential.factor p a b ha hb

/-- The independent exponential product preserves the shifted target credit. -/
theorem expectation (p : unitInterval) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b)
    (F : Bool → ℝ≥0∞) :
    (∫⁻ r, CoinProduct.firstCredit (FactorialSeriesFactory.bias .exp p) F r
      ∂RealCoin.law (ExpMinusRational.bias a b ha hb)) =
      ∫⁻ r, F r ∂RealCoin.law (bias p a b ha hb) := by
  rw [CoinProduct.expectation_preservation, CoinProduct.law, product_bias]

theorem expMinusShifted_lc {rT : Type} :
    (Occil.FactoryExtra.expMinusShifted : Exp rT).IsLocallyClosed := by is_lc

theorem expMinusShifted_fv {rT : Type} :
    (Occil.FactoryExtra.expMinusShifted : Exp rT).fv = ∅ := by
  simp [Occil.FactoryExtra.expMinusShifted, Exp.fv, ExpMinusRational.expMinusRational_fv,
    ExpMinusMartingale.expMinusMartingale_fv]

@[simp] theorem expMinusShifted_openRec {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.FactoryExtra.expMinusShifted = Occil.FactoryExtra.expMinusShifted :=
  (Exp.open_lc k e _ expMinusShifted_lc).symm

@[simp] theorem expMinusShifted_closeRec {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.FactoryExtra.expMinusShifted : Exp rT) =
      Occil.FactoryExtra.expMinusShifted :=
  Exp.closeRec_fresh x _ k (by simp [expMinusShifted_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Compose the two actual exponential samplers, with the complete rational-shift domain. -/
theorem twp_expMinusShifted (E : CoPset) (p : unitInterval) (a b : ℤ)
    (ha : 0 ≤ a) (hb : 0 < b) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ r, F r ∂RealCoin.law (bias p a b ha hb)) -∗
      tglWp E pl(&Occil.FactoryExtra.expMinusShifted &coin.fst #int a #int b #())
        (fun v : Val rT => iprop(∃ r : Bool, ⌜v = Val.bool r⌝ ∗ ↯ (F r))) := by
  iintro Hcredit
  iterate 4 twp_pure
  isimp only [ExpMinusRational.expMinusRational_openRec,
    ExpMinusRational.expMinusRational_closeRec, ExpMinusMartingale.expMinusMartingale_openRec,
    ExpMinusMartingale.expMinusMartingale_closeRec]
  twp_bind pl(&Occil.expMinusRational #int a #int b #())
  isimp only [← expectation p a b ha hb F] at Hcredit
  iapply ((ExpMinusRational.expMinusRational_distSpec E a b ha hb).wp
    (CoinProduct.firstCredit (FactorialSeriesFactory.bias .exp p) F)
    (measurable_of_finite _) _) $$ Hcredit
  iintro %r Hcredit
  cases r
  · twp_pures
    twp_value
    imodintro
    iexists false
    isimp only [CoinProduct.firstCredit, Bool.false_eq_true, ite_false] at Hcredit
    iframe Hcredit
    itrivial
  · twp_pure
    isimp only [CoinProduct.firstCredit, ite_true] at Hcredit
    iapply (ExpMinusMartingale.expMinusMartingale_distSpec E p coin hcoin).spec F
      (measurable_of_finite _) $$ Hcredit

/-- Exact exp(-(a/b+p)) for every nonnegative rational shift and every input bias. -/
theorem expMinusShifted_distSpec (E : CoPset) (p : unitInterval) (a b : ℤ)
    (ha : 0 ≤ a) (hb : 0 < b) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.expMinusShifted &coin.fst #int a #int b #())
      (RealCoin.law (bias p a b ha hb)) Val.bool where
  spec F _ := wand_entails (twp_expMinusShifted E p a b ha hb coin hcoin F)

end specification

end

end SampLib.ExpMinusShifted
