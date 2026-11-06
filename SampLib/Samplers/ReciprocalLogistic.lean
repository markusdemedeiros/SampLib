import SampLib.Samplers.LogisticFactory
import SampLib.Samplers.Complement
import Samplers.Bernoulli.Rational

/-! # Reciprocal logistic factory -/

open Set ProbLang
open scoped ENNReal

namespace SampLib.ReciprocalLogistic

noncomputable section

private theorem denominator_pos (p : unitInterval) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) :
    0 < (b : ℝ) + a * (p : ℝ) :=
  add_pos_of_pos_of_nonneg (by exact_mod_cast hb)
    (mul_nonneg (by exact_mod_cast ha) p.2.1)

/-- The reciprocal logistic bias `b / (b + a*p)`. -/
def bias (p : unitInterval) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) : unitInterval :=
  ⟨(b : ℝ) / ((b : ℝ) + a * (p : ℝ)),
    div_nonneg (by exact_mod_cast hb.le) (denominator_pos p a b ha hb).le,
    (div_le_one (denominator_pos p a b ha hb)).mpr
      (le_add_of_nonneg_right (mul_nonneg (by exact_mod_cast ha) p.2.1))⟩

private theorem complement_bias (p : unitInterval) (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    unitInterval.symm (LogisticFactory.integerBias p a b ha hb) = bias p a b ha.le hb := by
  apply Subtype.ext
  change 1 - ((a : ℝ) * (p : ℝ)) / ((b : ℝ) + a * (p : ℝ)) = _
  dsimp [bias]
  field_simp [(denominator_pos p a b ha.le hb).ne']
  ring

/-- Complementing the logistic output preserves the reciprocal expectation. -/
theorem expectation (p : unitInterval) (a b : ℤ) (ha : 0 < a) (hb : 0 < b)
    (F : Bool → ℝ≥0∞) :
    ∫⁻ c, F (!c) ∂RealCoin.law (LogisticFactory.integerBias p a b ha hb) =
      ∫⁻ c, F c ∂RealCoin.law (bias p a b ha.le hb) := by
  rw [Complement.expectation_preservation, Complement.law, complement_bias]

private theorem zero_credit (p : unitInterval) (b : ℤ) (hb : 0 < b)
    (F : Bool → ℝ≥0∞) :
    (∫⁻ c, F c ∂RealCoin.law (bias p 0 b (by omega) hb)) = F true := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  simp [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf, bias, hbR]

@[simp] private theorem logistic_open {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.logisticFactory = Occil.logisticFactory :=
  (Exp.open_lc k e _ (by is_lc)).symm

@[simp] private theorem logistic_close {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.logisticFactory : Exp rT) = Occil.logisticFactory :=
  Exp.closeRec_fresh x _ k (by
    simp [Occil.logisticFactory, Exp.fv, RationalCoin.rationalCoin_fv])

private theorem bool_not (b : Bool) : Bool.rec true false b = !b := by cases b <;> rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Reciprocal logistic sampling, including coefficient zero and both coin endpoints. -/
theorem twp_reciprocalLogistic (E : CoPset) (p : unitInterval) (a b : ℤ)
    (ha : 0 ≤ a) (hb : 0 < b) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ c, F c ∂RealCoin.law (bias p a b ha hb)) -∗
      tglWp E pl(&Occil.FactoryExtra.reciprocalLogistic &coin.fst #int a #int b #())
        (fun v : Val rT => iprop(∃ c : Bool, ⌜v = Val.bool c⌝ ∗ ↯ (F c))) := by
  iintro Hcredit
  twp_pures
  by_cases hz : a = 0
  · subst a
    twp_pures
    twp_value
    imodintro
    iexists true
    isimp only [zero_credit] at Hcredit
    iframe Hcredit
    itrivial
  · have ha' : 0 < a := by omega
    have heq : ((BaseLit.int a : BaseLit rT) == .int 0) = false := by
      change (a == 0) = false
      exact beq_eq_false_iff_ne.mpr hz
    rw [heq]
    twp_pure
    simp only [logistic_open, logistic_close]
    twp_bind pl(&Occil.logisticFactory &coin.fst #int a #int b #())
    isimp only [← expectation p a b ha' hb F] at Hcredit
    iapply ((LogisticFactory.logisticFactory_distSpec E p a b ha' hb coin hcoin).wp
      (fun c => F (!c)) (measurable_of_countable _) _) $$ Hcredit
    iintro %c Hcredit
    twp_pures
    twp_value
    imodintro
    iexists !c
    iframe Hcredit
    ipureintro
    simp only [Val.ext_iff, bool_not]

/-- Typed reciprocal logistic law for every nonnegative rational coefficient. -/
theorem reciprocalLogistic_distSpec (E : CoPset) (p : unitInterval) (a b : ℤ)
    (ha : 0 ≤ a) (hb : 0 < b) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.reciprocalLogistic &coin.fst #int a #int b #())
      (RealCoin.law (bias p a b ha hb)) Val.bool where
  spec F _ := wand_entails (twp_reciprocalLogistic E p a b ha hb coin hcoin F)

end specification

end

end SampLib.ReciprocalLogistic
