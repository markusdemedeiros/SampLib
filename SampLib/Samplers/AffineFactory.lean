import SampLib.LinearFactorySyntax
import SampLib.Samplers.CoinConditional
import Samplers.Bernoulli.Rational

/-! # Derived affine Bernoulli factory

A rational mixture inserts the constant offset; the verified linear factory supplies
its scale. Margins are required only when that final scale expands.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.AffineFactory

noncomputable section

private theorem selector_bounds (x y : ℤ) (hx : 0 ≤ x) (hy : 0 < y) :
    0 < x + y ∧ x ≤ x + y := by omega

private def selector (x y : ℤ) (hx : 0 ≤ x) (hy : 0 < y) : unitInterval :=
  RationalCoin.bias x (x + y) hx (selector_bounds x y hx hy).1 (selector_bounds x y hx hy).2

private def mixedBias (p : unitInterval) (x y : ℤ) (hx : 0 ≤ x) (hy : 0 < y) : unitInterval :=
  CoinConditional.bias 1 p (selector x y hx hy)

/-- Only an expanding final linear coefficient inspects the margin arguments. -/
def Admissible (p : unitInterval) (a b x y e f : ℤ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 ≤ x ∧ 0 < y ∧
    (y * a < (x + y) * b →
      0 < e ∧ e < f ∧ ((x : ℝ) / y + p) / ((a : ℝ) / b) ≤ 1 - (e : ℝ) / f)

/-- Mixing the offset first gives exactly the requested affine ratio. -/
private theorem mixed_ratio (p : unitInterval) (a b x y : ℤ) (ha : 0 < a) (hb : 0 < b)
    (hx : 0 ≤ x) (hy : 0 < y) :
    Gambler.ratio (mixedBias p x y hx hy) ((x + y) * b) (y * a) =
      ((x : ℝ) / y + p) / ((a : ℝ) / b) := by
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hyR : (y : ℝ) ≠ 0 := by exact_mod_cast hy.ne'
  have hxy : (x : ℝ) + y ≠ 0 := by
    have : (0 : ℝ) < (x : ℝ) + y := by exact_mod_cast (show 0 < x + y by omega)
    exact this.ne'
  simp only [Gambler.ratio, mixedBias, CoinConditional.bias, Set.Icc.coe_convexComb,
    selector, RationalCoin.bias, Set.Icc.coe_one, Int.cast_mul, Int.cast_add]
  field_simp
  ring

private theorem linear_admissible (p : unitInterval) (a b x y e f : ℤ)
    (h : Admissible p a b x y e f) :
    LinearFactory.Admissible (mixedBias p x y h.2.2.1 h.2.2.2.1)
      ((x + y) * b) (y * a) e f := by
  rcases h with ⟨ha, hb, hx, hy, hm⟩
  refine ⟨mul_nonneg (by omega) hb.le, mul_pos hy ha, fun he => ?_⟩
  obtain ⟨he0, hef, hbound⟩ := hm he
  exact ⟨he0, hef, by simpa only [mixed_ratio p a b x y ha hb hx hy] using hbound⟩

/-- The affine success probability `(x/y+p)/(a/b)`. -/
def bias (p : unitInterval) (a b x y e f : ℤ) (h : Admissible p a b x y e f) : unitInterval :=
  LinearFactory.bias (mixedBias p x y h.2.2.1 h.2.2.2.1) ((x + y) * b) (y * a) e f
    (linear_admissible p a b x y e f h)

@[simp] theorem bias_coe (p : unitInterval) (a b x y e f : ℤ)
    (h : Admissible p a b x y e f) :
    (bias p a b x y e f h : ℝ) = ((x : ℝ) / y + p) / ((a : ℝ) / b) :=
  mixed_ratio p a b x y h.1 h.2.1 h.2.2.1 h.2.2.2.1

private def mixedCredit (p : unitInterval) (F : Bool → ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then F true else RealCoin.credit p F

private theorem expectation (p : unitInterval) (x y : ℤ) (hx : 0 ≤ x) (hy : 0 < y)
    (F : Bool → ℝ≥0∞) :
    ∫⁻ b, mixedCredit p F b ∂RealCoin.law (selector x y hx hy) =
      ∫⁻ b, F b ∂RealCoin.law (mixedBias p x y hx hy) := by
  simpa [mixedCredit, mixedBias, CoinConditional.firstCredit, CoinConditional.law,
    RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf] using
    CoinConditional.expectation_preservation 1 p (selector x y hx hy) F

private def source {rT : Type} : Val rT :=
  ⟨Occil.FactoryExtra.affine, .lam (by is_lc), by is_lc⟩

private theorem source_fst {rT : Type} :
    (source (rT := rT)).fst = Occil.FactoryExtra.affine := rfl

private def mixed {rT : Type} (coin : Val rT) (x y : ℤ) : Val rT :=
  ⟨.lam pl(if &Occil.rationalCoin #int x (#int x + #int y) then #true else &coin.fst #()),
    .lam (by is_lc), by is_lc⟩

private theorem valid_test (a b x y : ℤ) (ha : 0 < a) (hb : 0 < b) (hx : 0 ≤ x)
    (hy : 0 < y) :
    (((decide (a ≤ 0) || decide (b ≤ 0)) || decide (x < 0)) || decide (y ≤ 0)) = false := by
  simp [not_le.mpr ha, not_le.mpr hb, not_lt.mpr hx, not_le.mpr hy]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem mixed_spec (E : CoPset) (p : unitInterval) (x y : ℤ) (hx : 0 ≤ x)
    (hy : 0 < y) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&(mixed coin x y).fst #())
      (RealCoin.law (mixedBias p x y hx hy)) Val.bool where
  spec F hF := by
    have hxy := selector_bounds x y hx hy
    have hs := RationalCoin.rationalCoin_distSpec (rT := rT) (GF := GF)
      E x (x + y) hx hxy.1 hxy.2
    iintro Hcredit
    twp_step
    simp [Exp.open', Exp.openRec, ProbLang.openRec_val_fst,
      RationalCoin.rationalCoin_openRec]
    twp_pure
    twp_bind pl(&Occil.rationalCoin #int x #int (x + y))
    isimp only [← expectation p x y hx hy F, selector] at Hcredit
    iapply (hs.wp (mixedCredit p F) (measurable_of_countable _) _) $$ Hcredit
    iintro %b Hcredit
    cases b
    · twp_pure
      isimp only [mixedCredit, Bool.false_eq_true, ite_false] at Hcredit
      have hc := hcoin.spec F hF
      simp only [RealCoin.lintegral_law] at hc
      iapply hc $$ Hcredit
    · twp_pure
      twp_value
      imodintro
      iexists true
      isimp only [mixedCredit, ite_true] at Hcredit
      iframe Hcredit
      itrivial

/-- Derived affine law over the complete conditional-margin domain. -/
theorem affine_distSpec (E : CoPset) (p : unitInterval) (a b x y e f : ℤ)
    (h : Admissible p a b x y e f) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.affine &coin.fst #int a #int b #int x #int y #int e #int f #())
      (RealCoin.law (bias p a b x y e f h)) Val.bool where
  spec F hF := by
    have hl := LinearFactory.linear_distSpec E _ ((x + y) * b) (y * a) e f
      (linear_admissible p a b x y e f h) (mixed coin x y)
      (mixed_spec E p x y h.2.2.1 h.2.2.2.1 coin hcoin)
    iintro Hcredit
    rw [← source_fst (rT := rT)]
    iterate 8 (twp_step; simp [Exp.open', Exp.openRec, Exp.close, Exp.closeRec, Exp.ofVal,
      Var.internal.injEq, ProbLang.openRec_val_fst,
      LinearFactorySyntax.linear_openRec, LinearFactorySyntax.linear_closeRec,
      RationalCoin.rationalCoin_openRec, RationalCoin.rationalCoin_closeRec])
    twp_pures
    rw [valid_test a b x y h.1 h.2.1 h.2.2.1 h.2.2.2.1]
    iterate 5 twp_pure
    simp only [LinearFactorySyntax.linear_openRec, Exp.ofVal]
    isimp only [bias] at Hcredit
    simp only [mixed] at hl
    iapply hl.spec F hF $$ Hcredit

end specification

end

end SampLib.AffineFactory
