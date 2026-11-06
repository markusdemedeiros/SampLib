import SampLib.Bernoulli.Laws.LogisticFactory
import SampLib.Uniform.RationalCoin
import Samplers.Bernoulli.Combinators
import Metrology.Iris.LocalBI

/-!
# Logistic Bernoulli factory

A selector returns `false` with probability `r`; otherwise the input coin is
tried. Thus the success bias is `(1-r)*p / (r + (1-r)*p)`, equal to
`x*p/(y+x*p)` when the selector has bias `r=y/(x+y)`.
-/

open Set ProbLang
open scoped ENNReal NNReal

namespace SampLib.LogisticFactory

open RealCoin (lintegral_law)

noncomputable section

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

private theorem positive_guard (x y : ℤ) (hx : 0 < x) (hy : 0 < y) :
    (decide (x ≤ 0) || decide (y ≤ 0)) = false := by
  simp [not_le.mpr hx, not_le.mpr hy]

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- CTE specification with an abstract selector of bias `r`. -/
theorem twp_logisticFactory (E : CoPset) (p r : unitInterval) (hr : 0 < (r : ℝ))
    (hr1 : (r : ℝ) < 1) (x y : ℤ) (hx : 0 < x) (hy : 0 < y) (coin : Val rT)
    (hselect : IsDistSpec (GF := GF) E pl(&Occil.rationalCoin #int y #int (x + y))
      (RealCoin.law r) Val.bool)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (credit p r hr F) -∗ tglWp E pl(&Occil.logisticFactory &coin.fst #int x #int y #())
      (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε (one_lt_terminationFactor r hr hr1) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  twp_pures
  rw [positive_guard x y hx hy]
  twp_pure
  twp_pure
  simp only [RationalCoin.rationalCoin_openRec, RationalCoin.rationalCoin_closeRec]
  twp_bind pl(&Occil.rationalCoin #int y #int (x + y))
  icombine Hcredit Hterm as Hcredit
  ihave Hcredit := ErrorCredit.weaken (expectation_preservation p r hr hr1 F ε) $$ Hcredit
  iapply (hselect.wp (selectorCredit p r hr F ε) (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  cases b
  · twp_pure
    twp_bind pl(&coin.fst #())
    isimp only [selectorCredit, Bool.false_eq_true, ite_false] at Hcredit
    iapply (hcoin.wp (inputCredit p r hr F ε) (measurable_of_countable _) _) $$ Hcredit
    iintro %a Hcredit
    cases a
    · twp_pure
      isimp only [inputCredit, Bool.false_eq_true, ite_false] at Hcredit
      ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
      twp_bind pl(&Occil.logisticFactory &coin.fst #int x #int y #())
      iapply (tglWp_mono fun _ => tglWp_value)
      iapply IH $$ Hterm Hcredit
    · twp_pures
      twp_value
      imodintro
      iexists true
      isimp only [inputCredit, ite_true] at Hcredit
      iframe Hcredit
      itrivial
  · twp_pures
    twp_value
    imodintro
    iexists false
    isimp only [selectorCredit, ite_true] at Hcredit
    iframe Hcredit
    itrivial

/-- Typed logistic law for every positive integer coefficient `x/y`. -/
theorem logisticFactory_distSpec [ProbLangDist.IsUniformInt rT]
    (E : CoPset) (p : unitInterval) (x y : ℤ) (hx : 0 < x) (hy : 0 < y) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.logisticFactory &coin.fst #int x #int y #())
      (RealCoin.law (integerBias p x y hx hy)) Val.bool where
  spec F _ := by
    let r := RationalCoin.bias y (x + y) hy.le (by omega) (by omega)
    obtain ⟨hr, hr1, hbias⟩ := selector_parameters p x y hx hy r rfl
    have hselect := RationalCoin.rationalCoin_distSpec (rT := rT) (GF := GF)
      E y (x + y) hy.le (by omega) (by omega)
    simpa only [lintegral_law, credit, hbias] using
      wand_entails (twp_logisticFactory E p r hr hr1 x y hx hy coin hselect hcoin F)

end specification

end

end SampLib.LogisticFactory
