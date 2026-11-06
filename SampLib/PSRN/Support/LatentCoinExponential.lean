import SampLib.PSRN.Support.LatentExponentialKernel
import SampLib.Core.Syntax.ClosedExp

/-! # A decreasing-uniform exponential factory over an owned latent world

Every input call carries its posterior and arbitrary joint continuation credit.
After the first uniform, a fixed threshold cap supplies termination amplification
uniformly over all latent input biases, including zero and one.
-/

open ProbLang
open LawfulProbLangℝ (unifUnit)
open scoped ENNReal NNReal

namespace SampLib.LatentReal.CoinExponential

noncomputable section

open LatentCoin

@[pl_fold] private def loop (coin : Val ℝ) : Exp ℝ :=
  .fix (.lam (.lam (.app (.lam
    (.cond (.binop .lt (.bvar 0) (.bvar 2))
      (.cond (.app coin.fst (.lit .unit))
        (.app (.app (.bvar 3) (.bvar 0)) (.unop .neg (.bvar 1))) (.bvar 1))
      (.bvar 1))) .urand)))

private theorem bool_not (b : Bool) : Bool.rec true false b = !b := by cases b <;> rfl

private theorem inputCredit_false {Ω : Type} (φ : Ω → unitInterval) (y : ℝ)
    (b : Bool) (G : Bool → Ω → ℝ≥0∞) (c : ℝ≥0∞) :
    inputCredit φ y b G c false = G b := rfl

private theorem inputCredit_true {Ω : Type} (φ : Ω → unitInterval) (y : ℝ)
    (b : Bool) (G : Bool → Ω → ℝ≥0∞) (c : ℝ≥0∞) :
    inputCredit φ y b G c true = fun z => tail φ y (!b) G z + c := rfl

private theorem initial_credit {Ω S : Type} [MeasurableSpace Ω] (D : Model Ω S) (s : S)
    (φ : Ω → unitInterval) (G : Bool → Ω → ℝ≥0∞) :
    credit D s (bias φ) G = ∫⁻ z, tail φ 1 true G z ∂D.posterior s := by
  rfl

private instance exponential_closed : ClosedExp (Occil.expMinusFactory : Exp ℝ) where
  lc := by is_lc
  fv := by simp [Occil.expMinusFactory, Exp.fv]

/-- Structural insertion preserves all free variables of the supplied callback. -/
def callback (coin : Val ℝ) : Val ℝ :=
  ⟨.lam (.app (.app Occil.expMinusFactory coin.fst) (.lit .unit)),
    .lam (by is_lc), by is_lc⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

private theorem twp_tail (E : CoPset) (D : Model Ω S) (owns : Val ℝ → S → IProp GF)
    (φ : Ω → unitInterval) (coin : Val ℝ → Val ℝ)
    (hcoin : IsLatentCoinSpec E D owns φ coin) (source : Val ℝ)
    (G : Bool → Ω → ℝ≥0∞) (hG : ∀ b, Measurable (G b))
    (B : unitInterval) (hB : 0 < (B : ℝ) ∧ (B : ℝ) < 1) :
    ⊢ ∀ (s : S) (x : ℝ) (b : Bool), ⌜0 ≤ x⌝ -∗ ⌜x ≤ (B : ℝ)⌝ -∗
      owns source s -∗ ↯ (∫⁻ z, tail φ x b G z ∂D.posterior s) -∗
      tglWp E pl(&(loop (coin source)) #real x #bool b) (post D owns source s G) := by
  iintro %s %x %b %hx0 %hxB Hstate Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert %s %x %b %hx0 %hxB Hstate Hcredit
  iapply ErrorCredit.Induction.simple hε (ExponentialFactory.one_lt_factor B hB) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ %s %x %b %hx0 %hxB Hstate Hcredit
  twp_pures
  twp_bind pl(urand)
  icombine Hcredit Hterm as Hcredit
  iapply (twp_urand_exp (ε₂ := uniformCredit D s φ x b G (ExponentialFactory.factor B * ε))
    (measurable_uniformCredit D s hcoin.measurable_bias x b hG _)
    (budget D s hcoin.measurable_bias B hB.1 x ⟨hx0, hxB⟩ b hG ε)) $$ Hcredit
  iintro %y ⟨%hy, Hcredit⟩
  have hy' := mem_unifUnitSupport_real.mp hy
  twp_pures
  rcases hyx : ProbLangℝ.realLt y x with _ | _
  · isimp only [uniformCredit_exit D s φ x y b G _ (of_decide_eq_false hyx)] at Hcredit
    twp_pures
    twp_value
    imodintro
    iapply post_return D owns source s s b G (D.refines_refl s)
    iframe Hstate Hcredit
  · isimp only [uniformCredit_below D s φ x y b G _ (of_decide_eq_true hyx)] at Hcredit
    twp_pure
    twp_bind pl(&(coin source).fst #())
    iapply hcoin.wp source s (inputCredit φ y b G (ExponentialFactory.factor B * ε))
      (measurable_inputCredit hcoin.measurable_bias y b hG _) _ $$ Hstate Hcredit
    iintro %a %t %hst Hstate Hcredit
    cases a
    · isimp only [inputCredit_false] at Hcredit
      twp_pures
      twp_value
      imodintro
      iapply post_return D owns source s t b G hst
      iframe Hstate Hcredit
    · isimp only [inputCredit_true,
        posterior_add_const D t _ (measurable_tail hcoin.measurable_bias y (!b) hG) _]
        at Hcredit
      ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
      twp_pure
      twp_pure
      simp only [bool_not]
      twp_bind pl(&(loop (coin source)) #real y #bool (!b))
      iapply tglWp_wand
      isplitl [IH Hstate Hcredit Hterm]
      · iapply IH $$ Hterm %t %y %(!b) %hy'.1.le
          %((of_decide_eq_true hyx).le.trans hxB) Hstate Hcredit
      iintro %v Hpost
      iapply (tglWp_value (v := v))
      iapply post_weaken D owns source s t G v hst $$ Hpost

private theorem twp_loop (E : CoPset) (D : Model Ω S) (owns : Val ℝ → S → IProp GF)
    (φ : Ω → unitInterval) (coin : Val ℝ → Val ℝ)
    (hcoin : IsLatentCoinSpec E D owns φ coin) (source : Val ℝ) (s : S)
    (G : Bool → Ω → ℝ≥0∞) (hG : ∀ b, Measurable (G b))
    (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (b : Bool) :
    iprop(owns source s ∗ ↯ (∫⁻ z, tail φ x b G z ∂D.posterior s)) ⊢
      tglWp E pl(&(loop (coin source)) #real x #bool b) (post D owns source s G) := by
  iintro ⟨Hstate, Hcredit⟩
  twp_pures
  twp_bind pl(urand)
  iapply (twp_urand_exp (ε₂ := uniformCredit D s φ x b G 0)
    (measurable_uniformCredit D s hcoin.measurable_bias x b hG 0) ?_) $$ Hcredit
  · rw [expectation D s hcoin.measurable_bias x hx b hG]
    simp only [mul_zero, add_zero, le_refl]
  iintro %y ⟨%hy, Hcredit⟩
  have hy' := mem_unifUnitSupport_real.mp hy
  twp_pures
  rcases hyx : ProbLangℝ.realLt y x with _ | _
  · isimp only [uniformCredit_exit D s φ x y b G 0 (of_decide_eq_false hyx)] at Hcredit
    twp_pures
    twp_value
    imodintro
    iapply post_return D owns source s s b G (D.refines_refl s)
    iframe Hstate Hcredit
  · isimp only [uniformCredit_below D s φ x y b G 0 (of_decide_eq_true hyx)] at Hcredit
    twp_pure
    twp_bind pl(&(coin source).fst #())
    iapply hcoin.wp source s (inputCredit φ y b G 0)
      (measurable_inputCredit hcoin.measurable_bias y b hG 0) _ $$ Hstate Hcredit
    iintro %a %t %hst Hstate Hcredit
    cases a
    · isimp only [inputCredit_false] at Hcredit
      twp_pures
      twp_value
      imodintro
      iapply post_return D owns source s t b G hst
      iframe Hstate Hcredit
    · isimp only [inputCredit_true, add_zero] at Hcredit
      twp_pure
      twp_pure
      simp only [bool_not]
      twp_bind pl(&(loop (coin source)) #real y #bool (!b))
      iapply tglWp_wand
      isplitl [Hstate Hcredit]
      · iapply (twp_tail E D owns φ coin hcoin source G hG ⟨y, hy'.1.le, hy'.2.le⟩ hy')
          $$ %t %y %(!b) %hy'.1.le %le_rfl Hstate Hcredit
      iintro %v Hpost
      iapply (tglWp_value (v := v))
      iapply post_weaken D owns source s t G v hst $$ Hpost

/-- Execute the unchanged exponential factory without forgetting its latent dependencies. -/
theorem twp_expMinusFactory (E : CoPset) (D : Model Ω S) (owns : Val ℝ → S → IProp GF)
    (φ : Ω → unitInterval) (coin : Val ℝ → Val ℝ)
    (hcoin : IsLatentCoinSpec E D owns φ coin) (source : Val ℝ) (s : S)
    (G : Bool → Ω → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) :
    iprop(owns source s ∗ ↯ (credit D s (bias φ) G)) ⊢
      tglWp E pl(&Occil.expMinusFactory &(coin source).fst #()) (post D owns source s G) := by
  iintro ⟨Hstate, Hcredit⟩
  isimp only [initial_credit] at Hcredit
  iterate 4 twp_pure
  simp only [realOfInt_real, Int.cast_one, Exp.ofVal]
  change iprop(owns source s ∗ ↯ (∫⁻ z, tail φ 1 true G z ∂D.posterior s)) ⊢
    tglWp E pl(&(loop (coin source)) #real 1 #true) (post D owns source s G)
  iapply twp_loop E D owns φ coin hcoin source s G hG 1 ⟨zero_le_one, le_rfl⟩ true

/-- The direct factory preserves the source's complete posterior and its ownership. -/
theorem exponential_programSpec (E : CoPset) (D : Model Ω S)
    (owns : Val ℝ → S → IProp GF) (φ : Ω → unitInterval) (coin : Val ℝ → Val ℝ)
    (hcoin : IsLatentCoinSpec E D owns φ coin) :
    IsLatentCoinProgramSpec E D owns (bias φ)
      (fun source => pl(&Occil.expMinusFactory &(coin source).fst #())) where
  measurable_bias := measurable_bias hcoin.measurable_bias
  spec source s G hG := twp_expMinusFactory E D owns φ coin hcoin source s G hG

/-- A unit callback for conditional exponential trials over the same latent world. -/
theorem exponential_coinSpec (E : CoPset) (D : Model Ω S)
    (owns : Val ℝ → S → IProp GF) (φ : Ω → unitInterval) (coin : Val ℝ → Val ℝ)
    (hcoin : IsLatentCoinSpec E D owns φ coin) :
    IsLatentCoinSpec E D owns (bias φ) (fun source => callback (coin source)) where
  measurable_bias := measurable_bias hcoin.measurable_bias
  spec source s G hG := by
    iintro ⟨Hstate, Hcredit⟩
    twp_pure
    isimp only [ClosedExp.openRec]
    iapply twp_expMinusFactory E D owns φ coin hcoin source s G hG
    iframe Hstate Hcredit

end specification

end

end SampLib.LatentReal.CoinExponential
