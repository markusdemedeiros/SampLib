import SampLib.Samplers.GeneralizedGeometric

open ProbLang
open scoped ENNReal

namespace ReviewExactDiscrete001

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The public rule spends expected credit and retains an unrelated caller resource. -/
theorem frame {α : Type _} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {E : CoPset} {e : Exp rT}
    {encode : α → Val rT} (h : IsDistSpec (GF := GF) E e μ encode)
    (F : α → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂μ) ∗ R -∗ tglWp E e
      (fun v : Val rT => iprop(∃ x : α, ⌜v = encode x⌝ ∗ ↯ (F x) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  iapply (h.wp F hF _) $$ Hcredit
  iintro %x Hcredit
  iexists x
  iframe Hcredit HR
  itrivial

example (E : CoPset) (p : ℕ → unitInterval) (coin : Val rT)
    (hcoin : ∀ n : ℕ, IsDistSpec (GF := GF) E
      pl(&coin.fst #int ((n + 1 : ℕ) : ℤ)) (RealCoin.law (p n)) Val.bool)
    (absorbs : Filter.Tendsto (AbsorbingChain.survival
      (GeneralizedGeometric.continuation p) 0) Filter.atTop (nhds 0))
    (F : ℕ → ℝ≥0∞) (R : IProp GF) :=
  frame (GeneralizedGeometric.generalizedGeometric_distSpec E p coin hcoin absorbs)
    F (measurable_of_countable _) R

private def stopBias : ℕ → unitInterval := fun _ => ⟨0, by constructor <;> norm_num⟩

private def stopCoin : Val rT :=
  ⟨.lam (.lit (.bool false)), .lam (by is_lc), by is_lc⟩

private theorem stopCoin_spec (E : CoPset) (n : ℕ) :
    IsDistSpec (GF := GF) E pl(&(stopCoin : Val rT).fst #int ((n + 1 : ℕ) : ℤ))
      (RealCoin.law (stopBias n)) Val.bool where
  spec F _ := by
    iintro Hcredit
    simp only [stopCoin]
    twp_pures
    twp_value
    imodintro
    iexists false
    isimp only [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf, stopBias,
      Bool.false_eq_true, ite_false, ite_true, ENNReal.ofReal_zero, zero_mul,
      sub_zero, ENNReal.ofReal_one, one_mul, zero_add] at Hcredit
    iframe Hcredit
    itrivial

private theorem stop_absorbs : Filter.Tendsto
    (AbsorbingChain.survival (GeneralizedGeometric.continuation stopBias) 0)
    Filter.atTop (nhds 0) := by
  have hq : GeneralizedGeometric.continuation stopBias = fun _ => 0 := by
    funext n
    simp [GeneralizedGeometric.continuation, RealCoin.pmf, stopBias]
  rw [hq]
  have hz : (fun _ : ℕ => (0 : ℝ≥0∞)) =ᶠ[Filter.atTop]
      AbsorbingChain.survival (fun _ => 0) 0 := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    cases n with
    | zero => omega
    | succ n => simp [AbsorbingChain.survival_succ]
  exact Filter.Tendsto.congr' hz tendsto_const_nhds

/-- A terminal callback is valid: the source starts at one and asks no callback at zero. -/
example (E : CoPset) (F : ℕ → ℝ≥0∞) (R : IProp GF) :=
  frame (GeneralizedGeometric.generalizedGeometric_distSpec E stopBias stopCoin
    (stopCoin_spec E) stop_absorbs) F (measurable_of_countable _) R

/-- The same public theorem admits infinite continuation credit. -/
example (E : CoPset) (R : IProp GF) :=
  frame (GeneralizedGeometric.generalizedGeometric_distSpec E stopBias stopCoin
    (stopCoin_spec E) stop_absorbs) (fun _ => ∞) measurable_const R

#print axioms SampLib.GeneralizedGeometric.generalizedGeometric_distSpec
#print axioms SampLib.AbsorbingChain.twp_of_survival
#print axioms SampLib.AbsorbingChain.stopLaw_expectation
#print axioms stopCoin_spec
#print axioms stop_absorbs

end

end ReviewExactDiscrete001
