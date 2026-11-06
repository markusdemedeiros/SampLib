import SampLib.Bernoulli.Laws.ExpMinusFactory
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
