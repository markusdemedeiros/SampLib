import SampLib.Common.Laws.ExponentialFactory
import SampLib.Common.Laws.BernoulliMixture
import SampLib.Bernoulli.CoinProduct

/-! # A decreasing-uniform factory for `exp (-p)`

At threshold `x`, the probability of reversing the current parity is
`∫₀ˣ p exp(-py) dy = 1-exp(-px)`. Once the first uniform is observed, all later
thresholds lie below a fixed cap strictly smaller than one.
-/

open ProbLang
open ENNReal (ofReal)
open LawfulProbLangℝ (unifUnit)
open scoped ENNReal NNReal

namespace SampLib.ExpMinusFactory

noncomputable section

open ExponentialFactory

abbrev bias (p : unitInterval) := decay p 1

def relative (b : Bool) (F : Bool → ℝ≥0∞) (a : Bool) : ℝ≥0∞ :=
  if a then F (!b) else F b

def credit (p : unitInterval) (x : ℝ) (b : Bool) (F : Bool → ℝ≥0∞) : ℝ≥0∞ :=
  RealCoin.credit (decay p x) (fun a => if a then F b else F (!b))

def coinCredit (p : unitInterval) (y : ℝ) (b : Bool) (F : Bool → ℝ≥0∞)
    (c : ℝ≥0∞) (a : Bool) : ℝ≥0∞ :=
  if a then credit p y (!b) F + c else F b

def kernel (p : unitInterval) (x : ℝ) (b : Bool) (F : Bool → ℝ≥0∞)
    (c : ℝ≥0∞) (y : ℝ) : ℝ≥0∞ :=
  if y < x then RealCoin.credit p (coinCredit p y b F c) else F b

section mathematics

open MeasureTheory

private theorem initial_credit (p : unitInterval) (F : Bool → ℝ≥0∞) :
    credit p 1 true F = RealCoin.credit (bias p) F := by
  unfold credit
  congr 1
  funext a
  cases a <;> rfl

private theorem reversed_credit (p : unitInterval) (x : ℝ) (b : Bool)
    (F : Bool → ℝ≥0∞) :
    RealCoin.credit (unitInterval.symm (decay p x)) (relative b F) = credit p x b F := by
  simp only [RealCoin.credit, RealCoin.pmf, relative, credit, unitInterval.coe_symm_eq,
    Bool.false_eq_true, ite_true, ite_false, sub_sub_cancel]
  ring

private theorem nested_credit (p : unitInterval) (y : ℝ) (b : Bool)
    (F : Bool → ℝ≥0∞) (c : ℝ≥0∞) :
    RealCoin.credit p (coinCredit p y b F c) =
      RealCoin.credit (p * decay p y) (relative b F) + ofReal (p : ℝ) * c := by
  have hbase : RealCoin.credit p (fun a => if a then credit p y (!b) F else F b) =
      RealCoin.credit (p * decay p y) (relative b F) := by
    have h := CoinProduct.expectation_preservation p (decay p y) (relative b F)
    simp only [CoinProduct.firstCredit, RealCoin.lintegral_law] at h
    have hflip : credit p y (!b) F = RealCoin.credit (decay p y) (relative b F) := by
      unfold credit
      congr 1
      funext a
      cases a <;> simp [relative]
    rw [hflip]
    simpa only [relative, Bool.false_eq_true, ite_false] using h
  rw [← hbase]
  simp only [RealCoin.credit, RealCoin.pmf, coinCredit,
    Bool.false_eq_true, ite_true, ite_false]
  ring

private theorem kernel_eq (p : unitInterval) (x : ℝ) (b : Bool)
    (F : Bool → ℝ≥0∞) (c : ℝ≥0∞) (y : ℝ) :
    kernel p x b F c y = RealCoin.credit (flipBias p x y) (relative b F) +
      (if y < x then ofReal (p : ℝ) else 0) * c := by
  by_cases h : y < x
  · simp only [kernel, flipBias, ite_eq_left h, nested_credit]
  · simp [kernel, flipBias, h, RealCoin.credit, RealCoin.pmf, relative]

theorem measurable_kernel (p : unitInterval) (x : ℝ) (b : Bool)
    (F : Bool → ℝ≥0∞) (c : ℝ≥0∞) : Measurable (kernel p x b F c) := by
  change Measurable (fun y => kernel p x b F c y)
  simp_rw [kernel_eq]
  exact (BernoulliMixture.measurable_credit _ (measurable_flipBias p x) _).add
    ((Measurable.ite measurableSet_Iio measurable_const measurable_const).mul_const c)

/-- Integrating the first-step flip mass preserves all parity credits. -/
theorem expectation (p : unitInterval) (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (b : Bool)
    (F : Bool → ℝ≥0∞) (c : ℝ≥0∞) :
    ∫⁻ y, kernel p x b F c y ∂unifUnit = credit p x b F + ofReal ((p : ℝ) * x) * c := by
  simp_rw [kernel_eq]
  rw [lintegral_add_left (BernoulliMixture.measurable_credit _ (measurable_flipBias p x) _),
    BernoulliMixture.expectation unifUnit (flipBias p x) (measurable_flipBias p x)
      (unitInterval.symm (decay p x))
      (by simpa only [unitInterval.coe_symm_eq] using flip_mass p x hx) (relative b F),
    lintegral_mul_const _ (Measurable.ite measurableSet_Iio measurable_const measurable_const),
    continuation_mass p x hx, reversed_credit]

private theorem budget (p B : unitInterval) (hB : 0 < (B : ℝ)) (x : ℝ)
    (hx : 0 ≤ x ∧ x ≤ (B : ℝ)) (b : Bool) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ y, kernel p x b F (factor B * ε) y ∂unifUnit ≤ credit p x b F + ε := by
  rw [expectation p x ⟨hx.1, hx.2.trans B.2.2⟩ b F]
  exact add_le_add le_rfl (amplified_continuation p B hB x hx ε)

end mathematics

-- Instantiate the callback without introducing named-variable closing wrappers.
@[pl_fold] private def loop (coin : Val ℝ) : Exp ℝ :=
  .fix (.lam (.lam (.app (.lam
    (.cond (.binop .lt (.bvar 0) (.bvar 2))
      (.cond (.app coin.fst (.lit .unit))
        (.app (.app (.bvar 3) (.bvar 0)) (.unop .neg (.bvar 1))) (.bvar 1))
      (.bvar 1))) .urand)))

private theorem bool_not (b : Bool) : Bool.rec true false b = !b := by cases b <;> rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
local bi (IProp GF)

private theorem twp_tail (E : CoPset) (p : unitInterval) (coin : Val ℝ)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (B : unitInterval) (hB : 0 < (B : ℝ) ∧ (B : ℝ) < 1) :
    ⊢ ∀ (x : ℝ) (b : Bool), ⌜0 ≤ x⌝ -∗ ⌜x ≤ (B : ℝ)⌝ -∗
      ↯ (credit p x b F) -∗ tglWp E pl(&(loop coin) #real x #bool b)
        (fun v : Val ℝ => iprop(∃ a : Bool, ⌜v = Val.bool a⌝ ∗ ↯ (F a))) := by
  iintro %x %b %hx0 %hxB Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert %x %b %hx0 %hxB Hcredit
  iapply ErrorCredit.Induction.simple hε (one_lt_factor B hB) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ %x %b %hx0 %hxB Hcredit
  twp_pures
  twp_bind pl(urand)
  icombine Hcredit Hterm as Hcredit
  iapply (twp_urand_exp (ε₂ := kernel p x b F (factor B * ε))
    (measurable_kernel p x b F _) (budget p B hB.1 x ⟨hx0, hxB⟩ b F ε)) $$ Hcredit
  iintro %y ⟨%hy, Hcredit⟩
  have hy' := mem_unifUnitSupport_real.mp hy
  twp_pures
  rcases hyx : ProbLangℝ.realLt y x with _ | _
  · isimp only [kernel, of_decide_eq_false hyx, ite_false] at Hcredit
    twp_pures
    twp_value
    imodintro
    iexists b
    iframe Hcredit
    itrivial
  · isimp only [kernel, of_decide_eq_true hyx, ite_true] at Hcredit
    twp_pure
    twp_bind pl(&coin.fst #())
    isimp only [← RealCoin.lintegral_law] at Hcredit
    iapply (hcoin.wp (coinCredit p y b F (factor B * ε)) (measurable_of_countable _) _)
      $$ Hcredit
    iintro %a Hcredit
    cases a
    · isimp only [coinCredit, Bool.false_eq_true, ite_false] at Hcredit
      twp_pures
      twp_value
      imodintro
      iexists b
      iframe Hcredit
      itrivial
    · isimp only [coinCredit, ite_true] at Hcredit
      ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
      twp_pure
      twp_pure
      simp only [bool_not]
      twp_bind pl(&(loop coin) #real y #bool (!b))
      iapply (tglWp_mono fun _ => tglWp_value)
      iapply IH $$ Hterm %y %(!b) %hy'.1.le
        %((of_decide_eq_true hyx).le.trans hxB) Hcredit

private theorem twp_loop (E : CoPset) (p : unitInterval) (coin : Val ℝ)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (b : Bool) :
    ⊢ ↯ (credit p x b F) -∗ tglWp E pl(&(loop coin) #real x #bool b)
      (fun v : Val ℝ => iprop(∃ a : Bool, ⌜v = Val.bool a⌝ ∗ ↯ (F a))) := by
  iintro Hcredit
  twp_pures
  twp_bind pl(urand)
  iapply (twp_urand_exp (ε₂ := kernel p x b F 0) (measurable_kernel p x b F 0) ?_)
    $$ Hcredit
  · rw [expectation p x hx b F, mul_zero, add_zero]
  iintro %y ⟨%hy, Hcredit⟩
  have hy' := mem_unifUnitSupport_real.mp hy
  twp_pures
  rcases hyx : ProbLangℝ.realLt y x with _ | _
  · isimp only [kernel, of_decide_eq_false hyx, ite_false] at Hcredit
    twp_pures
    twp_value
    imodintro
    iexists b
    iframe Hcredit
    itrivial
  · isimp only [kernel, of_decide_eq_true hyx, ite_true] at Hcredit
    twp_pure
    twp_bind pl(&coin.fst #())
    isimp only [← RealCoin.lintegral_law] at Hcredit
    iapply (hcoin.wp (coinCredit p y b F 0) (measurable_of_countable _) _) $$ Hcredit
    iintro %a Hcredit
    cases a
    · isimp only [coinCredit, Bool.false_eq_true, ite_false] at Hcredit
      twp_pures
      twp_value
      imodintro
      iexists b
      iframe Hcredit
      itrivial
    · isimp only [coinCredit, ite_true, add_zero] at Hcredit
      twp_pure
      twp_pure
      simp only [bool_not]
      twp_bind pl(&(loop coin) #real y #bool (!b))
      iapply (tglWp_mono fun _ => tglWp_value)
      iapply (twp_tail E p coin hcoin F ⟨y, hy'.1.le, hy'.2.le⟩ hy')
        $$ %y %(!b) %hy'.1.le %le_rfl Hcredit

/-- Exact exponential bias for every input bias, including zero and one. -/
theorem expMinusFactory_distSpec (E : CoPset) (p : unitInterval) (coin : Val ℝ)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.expMinusFactory &coin.fst #())
      (RealCoin.law (bias p)) Val.bool where
  spec F _ := by
    iintro Hcredit
    isimp only [RealCoin.lintegral_law, ← initial_credit p F] at Hcredit
    iterate 4 twp_pure
    simp only [realOfInt_real, Int.cast_one, Exp.ofVal]
    change ↯ (credit p 1 true F) ⊢ tglWp E pl(&(loop coin) #real 1 #true)
      (fun v : Val ℝ => iprop(∃ a : Bool, ⌜v = Val.bool a⌝ ∗ ↯ (F a)))
    iapply (twp_loop E p coin hcoin F 1 ⟨zero_le_one, le_rfl⟩ true)

end specification

end

end SampLib.ExpMinusFactory
