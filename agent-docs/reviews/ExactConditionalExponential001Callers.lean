import SampLib.PSRN.Support.LatentCoinExponential
import SampLib.LatentCoinConstants

open ProbLang
open scoped ENNReal

namespace ReviewConditionalExponential001

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib SampLib.LatentReal

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

private def endpoint (b : Bool) : unitInterval := if b then 1 else 0

private def constantCoin (b : Bool) : Val ℝ :=
  ⟨.lam (.lit (.bool b)), .lam (by is_lc), by is_lc⟩

omit [ProbLangDist.IsUniformReal ℝ] in
private theorem constant_spec (E : CoPset) (b : Bool) :
    IsDistSpec (GF := GF) E pl(&(constantCoin b).fst #())
      (RealCoin.law (endpoint b)) Val.bool where
  spec F _ := by
    iintro Hcredit
    have hz : ((0 : unitInterval) : ℝ) = 0 := rfl
    have ho : ((1 : unitInterval) : ℝ) = 1 := rfl
    cases b <;> isimp only [endpoint, Bool.false_eq_true, ite_false, ite_true,
      RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf, hz, ho,
      ENNReal.ofReal_zero, ENNReal.ofReal_one,
      sub_self, sub_zero, zero_mul, one_mul, add_zero, zero_add] at Hcredit
    all_goals
      unfold constantCoin
      twp_pures
      twp_value
      imodintro
      iexists _
      iframe Hcredit
      itrivial

/-- The actual factory retains full joint continuation dependence and arbitrary frame. -/
theorem framed (E : CoPset) (D : Model Ω S) (owns : Val ℝ → S → IProp GF)
    (φ : Ω → unitInterval) (coin : Val ℝ → Val ℝ)
    (hcoin : IsLatentCoinSpec E D owns φ coin) (source : Val ℝ) (s : S)
    (G : Bool → Ω → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) (R : IProp GF) :
    iprop(owns source s ∗ ↯ (LatentCoin.credit D s (CoinExponential.bias φ) G) ∗ R) ⊢
      tglWp E pl(&Occil.expMinusFactory &(coin source).fst #())
        (fun v : Val ℝ => iprop(LatentCoin.post D owns source s G v ∗ R)) := by
  iintro ⟨Hstate, Hcredit, HR⟩
  iapply tglWp_wand
  isplitl [Hstate Hcredit]
  · iapply CoinExponential.twp_expMinusFactory E D owns φ coin hcoin source s G hG
    iframe Hstate Hcredit
  iintro %v Hpost
  iframe Hpost HR

example (E : CoPset) (D : Model Ω S) (owns : Val ℝ → S → IProp GF)
    (source : Val ℝ) (s : S) (b : Bool) (G : Bool → Ω → ℝ≥0∞)
    (hG : ∀ a, Measurable (G a)) (R : IProp GF) :=
  framed E D owns (fun _ => endpoint b) (fun _ => constantCoin b)
    (LatentCoin.constantSpec E D owns (endpoint b) (constantCoin b) (constant_spec E b))
    source s G hG R

example (E : CoPset) (D : Model Ω S) (owns : Val ℝ → S → IProp GF)
    (source : Val ℝ) (s : S) (R : IProp GF) :=
  framed E D owns (fun _ => endpoint false) (fun _ => constantCoin false)
    (LatentCoin.constantSpec E D owns (endpoint false) (constantCoin false)
      (constant_spec E false)) source s (fun _ _ => ∞) (fun _ => measurable_const) R

/-- Infinite credit on an impossible output still contributes zero. -/
example (x : Ω) : LatentCoin.kernel (CoinExponential.bias (fun _ : Ω => 0))
    (fun b _ => if b then 0 else ∞) x = 0 := by
  simp [LatentCoin.kernel, CoinExponential.bias, ExpMinusFactory.bias,
    ExponentialFactory.decay, RealCoin.credit, RealCoin.pmf]

example (x : Ω) : (CoinExponential.bias (fun _ : Ω => 1) x : ℝ) = Real.exp (-1) := by
  simpa using CoinExponential.bias_coe (fun _ : Ω => 1) x

#print axioms SampLib.LatentReal.CoinExponential.exponential_programSpec
#print axioms SampLib.LatentReal.CoinExponential.exponential_coinSpec
#print axioms SampLib.LatentReal.CoinExponential.expectation
#print axioms framed
#print axioms constant_spec

end
end ReviewConditionalExponential001
