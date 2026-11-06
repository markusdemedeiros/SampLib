import SampLib.Common.Laws.ExponentialFactory
import SampLib.Common.Laws.BernoulliMixture
import SampLib.Bernoulli.CoinConditional
import Samplers.Bernoulli.Exponential

/-! # The sorted-uniform factory for `(1-p) exp(p)`

At a positive count and threshold `x`, success has probability `(1-p) exp(px)`.
The first uniform supplies a strict threshold cap for the remaining recursion.
-/

open ProbLang
open ENNReal (ofReal)
open LawfulProbLangℝ (unifUnit)
open scoped ENNReal NNReal

namespace SampLib.ExpTimesComplement

noncomputable section

open ExponentialFactory

abbrev bias (p : unitInterval) := growth p 1

abbrev credit (p : unitInterval) (x : ℝ) (F : Bool → ℝ≥0∞) : ℝ≥0∞ :=
  RealCoin.credit (growth p x) F

def kernel (p : unitInterval) (x : ℝ) (F : Bool → ℝ≥0∞)
    (c : ℝ≥0∞) (y : ℝ) : ℝ≥0∞ :=
  if x < y then F false else credit p y F + c

def coinCredit (p : unitInterval) (x : ℝ) (F : Bool → ℝ≥0∞)
    (c : ℝ≥0∞) (a : Bool) : ℝ≥0∞ :=
  if a then ∫⁻ y, kernel p x F c y ∂unifUnit else F true

section mathematics

open MeasureTheory

private theorem nested_credit (p : unitInterval) (x y : ℝ)
    (F : Bool → ℝ≥0∞) (c : ℝ≥0∞) :
    RealCoin.credit p (fun a => if a then kernel p x F c y else F true) =
      RealCoin.credit (growthStep p x y) F +
        (if x < y then 0 else ofReal (p : ℝ)) * c := by
  have hbase := CoinConditional.expectation_preservation (growthWindow p x y) 1 p F
  have hbias : CoinConditional.bias (growthWindow p x y) 1 p = growthStep p x y := by
    apply Subtype.ext
    simp only [CoinConditional.bias, Set.Icc.coe_convexComb, growthStep,
      unitInterval.coe_symm_eq, Set.Icc.coe_mul, Set.Icc.coe_one]
    ring
  simp only [CoinConditional.firstCredit, CoinConditional.law, RealCoin.lintegral_law,
    hbias] at hbase
  by_cases h : x < y
  · simpa [kernel, growthWindow, h, RealCoin.credit, RealCoin.pmf] using hbase
  · have hb : growthWindow p x y = growth p y := ite_eq_right h
    rw [hb] at hbase
    simp only [kernel, h, ite_false, credit]
    rw [← hbase]
    simp only [RealCoin.credit, RealCoin.pmf, Bool.false_eq_true, ite_true, ite_false,
      Set.Icc.coe_one, sub_self,
      ENNReal.ofReal_one, ENNReal.ofReal_zero, zero_mul, add_zero]
    ring

theorem measurable_kernel (p : unitInterval) (x : ℝ) (F : Bool → ℝ≥0∞)
    (c : ℝ≥0∞) : Measurable (kernel p x F c) := by
  exact Measurable.ite measurableSet_Ioi measurable_const
    ((BernoulliMixture.measurable_credit _ (measurable_growth p) F).add_const c)

/-- The coin and sorted-uniform step preserve the exponential success credit. -/
theorem expectation (p : unitInterval) (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1)
    (F : Bool → ℝ≥0∞) (c : ℝ≥0∞) :
    RealCoin.credit p (coinCredit p x F c) =
      credit p x F + ofReal ((p : ℝ) * x) * c := by
  have hswap : RealCoin.credit p (coinCredit p x F c) =
      ∫⁻ y, RealCoin.credit p (fun a => if a then kernel p x F c y else F true)
        ∂unifUnit := by
    simp only [RealCoin.credit, RealCoin.pmf, coinCredit,
      Bool.false_eq_true, ite_true, ite_false]
    rw [lintegral_add_left (show Measurable (fun y => ofReal (p : ℝ) * kernel p x F c y)
        from (measurable_kernel p x F c).const_mul _),
      lintegral_const_mul _ (measurable_kernel p x F c),
      lintegral_const, measure_univ, mul_one]
  rw [hswap]
  simp_rw [nested_credit]
  rw [lintegral_add_left
      (BernoulliMixture.measurable_credit _ (measurable_growthStep p x) F),
    BernoulliMixture.expectation unifUnit (growthStep p x) (measurable_growthStep p x)
      (growth p x) (growth_step_mass p x hx) F,
    lintegral_mul_const _ (Measurable.ite measurableSet_Ioi measurable_const measurable_const),
    growth_continuation_mass p x hx]

private theorem initial_credit (p : unitInterval) (F : Bool → ℝ≥0∞) :
    RealCoin.credit p (coinCredit p 1 F 0) = credit p 1 F := by
  simpa only [mul_zero, add_zero] using expectation p 1 ⟨zero_le_one, le_rfl⟩ F 0

private theorem budget (p B : unitInterval) (hB : 0 < (B : ℝ)) (x : ℝ)
    (hx : 0 ≤ x ∧ x ≤ (B : ℝ)) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) :
    RealCoin.credit p (coinCredit p x F (factor B * ε)) ≤ credit p x F + ε := by
  rw [expectation p x ⟨hx.1, hx.2.trans B.2.2⟩ F]
  exact add_le_add le_rfl (amplified_continuation p B hB x hx ε)

end mathematics

-- The callback is a locally closed leaf; the remaining indices are the four binders.
@[pl_fold] private def loop (coin : Val ℝ) : Exp ℝ :=
  .fix (.lam (.lam (.cond (.app coin.fst (.lit .unit))
    (.app (.lam (.cond (.binop .eq (.bvar 2) (.lit (.int 0)))
      (.app (.app (.bvar 3) (.lit (.int 1))) (.bvar 0))
      (.cond (.binop .lt (.bvar 1) (.bvar 0)) (.lit (.bool false))
        (.app (.app (.bvar 3) (.binop .plus (.bvar 2) (.lit (.int 1)))) (.bvar 0)))))
      .urand) (.lit (.bool true)))))

private theorem int_ne_zero (n : ℤ) (hn : 0 < n) :
    ((BaseLit.int n : BaseLit ℝ) == .int 0) = false := by
  change (n == 0) = false
  simp only [beq_eq_false_iff_ne]
  exact ne_of_gt hn

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
local bi (IProp GF)

private theorem twp_tail (E : CoPset) (p : unitInterval) (coin : Val ℝ)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (B : unitInterval) (hB : 0 < (B : ℝ) ∧ (B : ℝ) < 1) :
    ⊢ ∀ (n : ℤ) (x : ℝ), ⌜0 < n⌝ -∗ ⌜0 ≤ x⌝ -∗ ⌜x ≤ (B : ℝ)⌝ -∗
      ↯ (credit p x F) -∗ tglWp E pl(&(loop coin) #int n #real x)
        (fun v : Val ℝ => iprop(∃ a : Bool, ⌜v = Val.bool a⌝ ∗ ↯ (F a))) := by
  iintro %n %x %hn %hx0 %hxB Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert %n %x %hn %hx0 %hxB Hcredit
  iapply ErrorCredit.Induction.simple hε (one_lt_factor B hB) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ %n %x %hn %hx0 %hxB Hcredit
  twp_pures
  twp_bind pl(&coin.fst #())
  icombine Hcredit Hterm as Hcredit
  ihave Hcredit := ErrorCredit.weaken (budget p B hB.1 x ⟨hx0, hxB⟩ F ε) $$ Hcredit
  isimp only [← RealCoin.lintegral_law] at Hcredit
  iapply (hcoin.wp (coinCredit p x F (factor B * ε)) (measurable_of_countable _) _)
    $$ Hcredit
  iintro %a Hcredit
  cases a
  · isimp only [coinCredit, Bool.false_eq_true, ite_false] at Hcredit
    twp_pures
    twp_value
    imodintro
    iexists true
    iframe Hcredit
    itrivial
  · isimp only [coinCredit, ite_true] at Hcredit
    twp_pure
    twp_bind pl(urand)
    iapply (twp_urand_exp (ε₂ := kernel p x F (factor B * ε))
      (measurable_kernel p x F _) le_rfl) $$ Hcredit
    iintro %y ⟨%hy, Hcredit⟩
    have hy' := mem_unifUnitSupport_real.mp hy
    twp_pures
    simp only [int_ne_zero n hn]
    twp_pures
    rcases hxy : ProbLangℝ.realLt x y with _ | _
    · isimp only [kernel, of_decide_eq_false hxy, ite_false] at Hcredit
      ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
      twp_pure
      twp_pure
      twp_bind pl(&(loop coin) #int (n + 1) #real y)
      iapply (tglWp_mono fun _ => tglWp_value)
      iapply IH $$ Hterm %(n + 1) %y %(hn.trans (lt_add_one n)) %hy'.1.le
        %((le_of_not_gt (of_decide_eq_false hxy)).trans hxB) Hcredit
    · isimp only [kernel, of_decide_eq_true hxy, ite_true] at Hcredit
      twp_pures
      twp_value
      imodintro
      iexists false
      iframe Hcredit
      itrivial

private theorem twp_initial (E : CoPset) (p : unitInterval) (coin : Val ℝ)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (credit p 1 F) -∗ tglWp E pl(&(loop coin) #0 #real 0)
      (fun v : Val ℝ => iprop(∃ a : Bool, ⌜v = Val.bool a⌝ ∗ ↯ (F a))) := by
  iintro Hcredit
  twp_pures
  twp_bind pl(&coin.fst #())
  isimp only [← initial_credit p F, ← RealCoin.lintegral_law] at Hcredit
  iapply (hcoin.wp (coinCredit p 1 F 0) (measurable_of_countable _) _) $$ Hcredit
  iintro %a Hcredit
  cases a
  · isimp only [coinCredit, Bool.false_eq_true, ite_false] at Hcredit
    twp_pures
    twp_value
    imodintro
    iexists true
    iframe Hcredit
    itrivial
  · isimp only [coinCredit, ite_true] at Hcredit
    twp_pure
    twp_bind pl(urand)
    iapply (twp_urand_exp (ε₂ := kernel p 1 F 0) (measurable_kernel p 1 F 0) le_rfl)
      $$ Hcredit
    iintro %y ⟨%hy, Hcredit⟩
    have hy' := mem_unifUnitSupport_real.mp hy
    isimp only [kernel, not_lt.mpr hy'.2.le, ite_false, add_zero] at Hcredit
    iterate 3 twp_pure
    twp_bind pl(&(loop coin) #1 #real y)
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply (twp_tail E p coin hcoin F ⟨y, hy'.1.le, hy'.2.le⟩ hy')
      $$ %(1 : ℤ) %y %zero_lt_one %hy'.1.le %le_rfl Hcredit

/-- Exact sorted-uniform factory law, including both deterministic input coins. -/
theorem expTimesComplement_distSpec (E : CoPset) (p : unitInterval) (coin : Val ℝ)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.expTimesComplement &coin.fst #())
      (RealCoin.law (bias p)) Val.bool where
  spec F _ := by
    iintro Hcredit
    isimp only [RealCoin.lintegral_law] at Hcredit
    iterate 4 twp_pure
    simp only [realOfInt_real, Int.cast_zero]
    change ↯ (credit p 1 F) ⊢ tglWp E pl(&(loop coin) #0 #real 0)
      (fun v : Val ℝ => iprop(∃ a : Bool, ⌜v = Val.bool a⌝ ∗ ↯ (F a)))
    iapply (twp_initial E p coin hcoin F)

end specification

end

end SampLib.ExpTimesComplement
