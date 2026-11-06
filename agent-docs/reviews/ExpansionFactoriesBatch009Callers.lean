import SampLib.Samplers.LogOnePlusFactory
import SampLib.Samplers.ComplementLogOnePlus
import SampLib.Samplers.LinearFactory
import SampLib.Samplers.FromBounds
import SampLib.BagProduct
import SampLib.BagReciprocal
import SampLib.UniformBagBracket
import SampLib.Samplers.SampleGeometricBag
import SampLib.Distributions.BoundsKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Metrology.TotalEris.Examples.Samplers.RealDecrTrial
import SampLib.Templates
import Metrology.Iris.LocalBI

open ProbLang
open scoped ENNReal

namespace ExpansionFactoriesReview

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem frame {E : CoPset} {e : Exp rT} {μ : MeasureTheory.Measure Bool}
    [MeasureTheory.IsProbabilityMeasure μ]
    (h : IsDistSpec (GF := GF) E e μ Val.bool) (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂μ) ∗ I -∗ tglWp E e
      (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply (h.wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HI
  itrivial


variable [ProbLangDist.IsUniformInt rT]

example (E : CoPset) (l : Loc) (p : List Bool) (G : Bool → ℝ → ℝ≥0∞)
    (hG : ∀ b, Measurable (G b)) (I : IProp GF) :
    iprop((UniformBag.owns l p ∗ ↯ (LatentBernoulli.credit p LatentBernoulli.bias G)) ∗ I) ⊢
      tglWp E pl(&Occil.sampleGeometricBag #loc l #())
        (fun v : Val rT => iprop(UniformBag.coinPost l p G v ∗ I)) := by
  iintro ⟨Hbag, HI⟩
  iapply tglWp_wand
  isplitl [Hbag]
  · iapply SampleGeometricBag.twp_sampleGeometricBag E l p G hG $$ Hbag
  iintro %v Hpost
  iframe Hpost HI

-- The second continuation stays conditional on the same U after the first call.
example (E : CoPset) (l : Loc) (p : List Bool) (G : Bool → Bool → ℝ → ℝ≥0∞)
    (hG : ∀ b c, Measurable (G b c)) (I : IProp GF) :
    iprop((UniformBag.owns l p ∗ ↯ (LatentBernoulli.credit p LatentBernoulli.bias
      (fun b u => LatentBernoulli.kernel LatentBernoulli.bias (G b) u))) ∗ I) ⊢
      tglWp E pl(let first := &Occil.sampleGeometricBag #loc l #();
        let second := &Occil.sampleGeometricBag #loc l #(); (first, second))
        (fun v : Val rT => iprop(∃ (b c : Bool) (q : List Bool),
          ⌜v = Val.pair (Val.bool b) (Val.bool c) ∧ p <+: q⌝ ∗
          UniformBag.owns l q ∗ ↯ (DyadicPosterior.credit q (G b c)) ∗ I)) := by
  iintro ⟨⟨Hbag, Hcredit⟩, HI⟩
  twp_bind pl(&Occil.sampleGeometricBag #loc l #())
  iapply tglWp_wand
  isplitl [Hbag Hcredit]
  · iapply SampleGeometricBag.twp_sampleGeometricBag E l p
      (fun b u => LatentBernoulli.kernel LatentBernoulli.bias (G b) u)
      (fun b => LatentBernoulli.measurable_kernel LatentBernoulli.measurable_bias (hG b))
    iframe Hbag Hcredit
  iintro %v Hpost
  isimp only [UniformBag.coinPost] at Hpost
  ihave ⟨%b, %q, %hb, Hbag, Hcredit⟩ := Hpost
  rcases hb with ⟨rfl, hpq⟩
  twp_pure
  twp_bind pl(&Occil.sampleGeometricBag #loc l #())
  iapply tglWp_wand
  isplitl [Hbag Hcredit]
  · iapply SampleGeometricBag.twp_sampleGeometricBag E l q (G b) (hG b)
    isimp only [LatentBernoulli.credit]
    iframe Hbag Hcredit
  iintro %v Hpost
  isimp only [UniformBag.coinPost] at Hpost
  ihave ⟨%c, %r, %hc, Hbag, Hcredit⟩ := Hpost
  rcases hc with ⟨rfl, hqr⟩
  twp_pures
  twp_value
  imodintro
  iexists b, c, r
  iframe Hbag Hcredit HI
  ipureintro
  exact ⟨rfl, hpq.trans hqr⟩

private def bothTrue (b c : Bool) (_ : ℝ) : ℝ≥0∞ := if b && c then 1 else 0

private theorem unit_second_moment :
    (∫⁻ u, ENNReal.ofReal (u ^ 2) ∂DyadicPosterior.unitLaw) = (1 : ℝ≥0∞)/3 := by
  change (∫⁻ u in Set.Ico (0:ℝ) 1, ENNReal.ofReal (u ^ 2)) = _
  rw [MeasureTheory.restrict_Ico_eq_restrict_Icc,
    ProbLang.TotalEris.Examples.lintegral_ofReal_Icc (by norm_num) (by fun_prop)
      (fun u _ => sq_nonneg u), integral_pow]
  norm_num [ENNReal.ofReal_div_of_pos]

-- Two conditionally independent Bern(U) draws have joint success E[U²]=1/3.
private theorem joint_success :
    LatentBernoulli.credit [] LatentBernoulli.bias
      (fun b u => LatentBernoulli.kernel LatentBernoulli.bias (bothTrue b) u) =
        (1 : ℝ≥0∞)/3 := by
  unfold LatentBernoulli.credit LatentBernoulli.kernel bothTrue
    RealCoin.credit RealCoin.pmf
  simp only [Bool.and_true, Bool.and_false, ite_true, Bool.false_eq_true, ite_false,
    mul_one, mul_zero, add_zero]
  unfold DyadicPosterior.credit
  rw [DyadicPosterior.law_nil]
  calc
    _ = ∫⁻ u, ENNReal.ofReal (u ^ 2) ∂DyadicPosterior.unitLaw := by
      apply MeasureTheory.lintegral_congr_ae
      have hu : ∀ᵐ u ∂DyadicPosterior.unitLaw, u ∈ Set.Ico 0 1 := by
        simpa only [DyadicPosterior.law_nil] using DyadicPosterior.ae_mem_unit []
      filter_upwards [hu] with u hu
      rw [LatentBernoulli.bias_coe hu]
      simp only [pow_two, ENNReal.ofReal_mul hu.1]
    _ = _ := unit_second_moment

example :
    LatentBernoulli.credit [] LatentBernoulli.bias
      (fun b u => LatentBernoulli.kernel LatentBernoulli.bias (bothTrue b) u) ≠
        (1 : ℝ≥0∞)/4 := by
  rw [joint_success]
  norm_num

example (p : List Bool) :
    LatentBernoulli.credit p (fun _ => 0) (fun b _ => if b then ∞ else 0) = 0 := by
  simp [LatentBernoulli.credit, LatentBernoulli.kernel, RealCoin.credit, RealCoin.pmf,
    DyadicPosterior.credit]

example (p : unitInterval) (F : Bool → ℝ≥0∞) :
    DyadicPosterior.credit [] (FromBounds.outputCredit p F) = RealCoin.credit p F :=
  FromBounds.output_expectation p F
example {p : unitInterval} (a : FromBounds.Interval p) (q : List Bool)
    (F : Bool → ℝ≥0∞) (hlo : DyadicPosterior.resolves q a.left false)
    (hhi : DyadicPosterior.resolves q a.right true) :
    1 ≤ DyadicPosterior.credit q (FromBounds.horizonCredit a F) :=
  FromBounds.unresolved_credit a q F hlo hhi
example {p : unitInterval} (a : ℕ → FromBounds.Interval p) (ha : FromBounds.Tight a)
    (F : Bool → ℝ≥0∞) :
    ∃ N, DyadicPosterior.credit [] (FromBounds.horizonCredit (a N) F) ≤
      RealCoin.credit p F + ∞ :=
  FromBounds.exists_horizon a ha F ∞ (by simp)

example (E : CoPset) (l : Loc) (φ ψ : ℝ → unitInterval) (left right : Exp rT)
    (hl : UniformBag.IsCoinSpec (GF := GF) E l left φ)
    (hr : UniformBag.IsCoinSpec (GF := GF) E l right ψ)
    (p : List Bool) (G : Bool → ℝ → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) (I : IProp GF) :
    iprop((UniformBag.owns l p ∗ ↯ (LatentBernoulli.credit p (BagProduct.bias φ ψ) G)) ∗ I) ⊢
      tglWp E pl(if &left then &right else #false)
        (fun v : Val rT => iprop(UniformBag.coinPost l p G v ∗ I)) := by
  iintro ⟨Hbag, HI⟩
  iapply tglWp_wand
  isplitl [Hbag]
  · iapply BagProduct.twp_product E l φ ψ left right hl hr p G hG $$ Hbag
  iintro %v Hpost
  iframe Hpost HI

example (E : CoPset) (l : Loc) (φ : ℝ → unitInterval) (coin : Val rT)
    (hc : UniformBag.IsCoinSpec (GF := GF) E l pl(&coin.fst #()) φ)
    (p : List Bool) (G : Bool → ℝ → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) (I : IProp GF) :
    iprop((UniformBag.owns l p ∗ ↯ (LatentBernoulli.credit p (BagReciprocal.bias φ) G)) ∗ I) ⊢
      tglWp E pl(&Occil.oneDivOnePlus &coin.fst #())
        (fun v : Val rT => iprop(UniformBag.coinPost l p G v ∗ I)) := by
  iintro ⟨Hbag, HI⟩
  iapply tglWp_wand
  isplitl [Hbag]
  · iapply BagReciprocal.twp_oneDivOnePlus E l φ coin hc p G hG $$ Hbag
  iintro %v Hpost
  iframe Hpost HI

example (E : CoPset) (p : unitInterval) (a b e f : ℤ)
    (h : LinearFactory.Admissible p a b e f) (coin : Val rT)
    (hc : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (LinearFactory.linear_distSpec E p a b e f h coin hc) F I

private theorem zero_admissible (p : unitInterval) :
    LinearFactory.Admissible p 0 1 (-7) 0 := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  omega
private theorem one_admissible (p : unitInterval) :
    LinearFactory.Admissible p 1 1 (-7) 0 := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  omega
private def quarter : unitInterval := ⟨1/4, by norm_num, by norm_num⟩
private theorem expanding_admissible : LinearFactory.Admissible quarter 2 1 1 2 := by
  refine ⟨by decide, by decide, ?_⟩
  intro _
  norm_num [Gambler.ratio, quarter]

example : LinearFactory.scale 1 2 = 10 := by decide
example : (LinearFactory.bias quarter 2 1 1 2 expanding_admissible : ℝ) = 1/2 := by
  norm_num [LinearFactory.bias_coe, quarter]
example (p : unitInterval) : LinearFactory.bias p 1 1 (-7) 0 (one_admissible p) = p := by
  apply Subtype.ext
  rw [LinearFactory.bias_coe]
  simp
example (p : unitInterval) : LinearFactory.bias p 0 1 (-7) 0 (zero_admissible p) = 0 := by
  apply Subtype.ext
  rw [LinearFactory.bias_coe]
  simp
example (p : unitInterval) :
    RealCoin.credit (LinearFactory.bias p 0 1 (-7) 0 (zero_admissible p))
      (fun b => if b then ∞ else 0) = 0 := by
  have h : LinearFactory.bias p 0 1 (-7) 0 (zero_admissible p) = 0 := by
    apply Subtype.ext
    rw [LinearFactory.bias_coe]
    simp
  rw [h]
  simp [RealCoin.credit, RealCoin.pmf]

example (E : CoPset) (p : unitInterval) (a : ℕ → FromBounds.Interval p)
    (ha : FromBounds.Tight a) (bounds : Val rT)
    (hb : ∀ n : ℕ, ⊢ tglWp E pl(&bounds.fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = FromBounds.encodeInterval (a n)⌝)))
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (FromBounds.fromBounds_distSpec E p a ha bounds hb) F I

private def zeroInterval : FromBounds.Interval 0 := ⟨0,0,1,by decide,by norm_num,by norm_num⟩
private def oneInterval : FromBounds.Interval 1 := ⟨1,1,1,by decide,by norm_num,by norm_num⟩
private theorem zero_tight : FromBounds.Tight (fun _ => zeroInterval) := by
  intro ε hε
  refine ⟨0, ?_⟩
  simpa [FromBounds.Interval.width, FromBounds.Interval.left, FromBounds.Interval.right,
    zeroInterval] using hε.le
private theorem one_tight : FromBounds.Tight (fun _ => oneInterval) := by
  intro ε hε
  refine ⟨0, ?_⟩
  simpa [FromBounds.Interval.width, FromBounds.Interval.left, FromBounds.Interval.right,
    oneInterval] using hε.le

private def zeroOracle {rT : Type} : Val rT :=
  ⟨pl(fun n, (#0,(#0,#1))), .lam (by is_lc), by is_lc⟩
private def oneOracle {rT : Type} : Val rT :=
  ⟨pl(fun n, (#1,(#1,#1))), .lam (by is_lc), by is_lc⟩

omit [ProbLangDist.IsUniformInt rT] in
private theorem zero_oracle_spec (E : CoPset) (n : ℕ) :
    ⊢ tglWp E pl(&(zeroOracle (rT := rT)).fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = FromBounds.encodeInterval zeroInterval⌝)) := by
  twp_pures
  twp_value
  imodintro
  ipureintro
  rfl
omit [ProbLangDist.IsUniformInt rT] in
private theorem one_oracle_spec (E : CoPset) (n : ℕ) :
    ⊢ tglWp E pl(&(oneOracle (rT := rT)).fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = FromBounds.encodeInterval oneInterval⌝)) := by
  twp_pures
  twp_value
  imodintro
  ipureintro
  rfl

example (E : CoPset) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (FromBounds.fromBounds_distSpec E 0 (fun _ => zeroInterval) zero_tight
    (zeroOracle (rT := rT)) (zero_oracle_spec E)) F I
example (E : CoPset) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (FromBounds.fromBounds_distSpec E 1 (fun _ => oneInterval) one_tight
    (oneOracle (rT := rT)) (one_oracle_spec E)) F I

private def half : unitInterval := ⟨1/2,by norm_num,by norm_num⟩
private def exactHalf : FromBounds.Interval half := ⟨1,1,2,by decide,by norm_num [half],
  by norm_num [half]⟩
private def wideHalf : FromBounds.Interval half := ⟨-1,2,1,by decide,by norm_num [half],
  by norm_num [half]⟩
private def nonmonotone (n : ℕ) : FromBounds.Interval half :=
  if n = 2 then exactHalf else wideHalf
private theorem nonmonotone_tight : FromBounds.Tight nonmonotone := by
  intro ε hε
  refine ⟨2, ?_⟩
  simpa [nonmonotone, FromBounds.Interval.width, FromBounds.Interval.left,
    FromBounds.Interval.right, exactHalf] using hε.le
example : (nonmonotone 2).width < (nonmonotone 3).width := by
  norm_num [nonmonotone, FromBounds.Interval.width, FromBounds.Interval.left,
    FromBounds.Interval.right, exactHalf, wideHalf]
example (E : CoPset) (bounds : Val rT)
    (hb : ∀ n : ℕ, ⊢ tglWp E pl(&bounds.fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = FromBounds.encodeInterval (nonmonotone n)⌝)))
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (FromBounds.fromBounds_distSpec E half nonmonotone nonmonotone_tight bounds hb) F I

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hc : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (LogOnePlusFactory.logOnePlusFactory_distSpec E p coin hc) F I
example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hc : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (ComplementLogOnePlus.complementLogOnePlus_distSpec E p coin hc) F I

private def trueCallback {rT : Type} : Val rT :=
  ⟨.lam (.lit (.bool true)), .lam (by is_lc), by is_lc⟩
omit [ProbLangDist.IsUniformInt rT] in
private theorem true_callback_spec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&(trueCallback (rT := rT)).fst #())
      (RealCoin.law 1) Val.bool where
  spec F _ := by
    iintro Hcredit
    twp_pure
    twp_value
    imodintro
    iexists true
    isimp [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf] at Hcredit
    iframe Hcredit
    itrivial
example (E : CoPset) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (LogOnePlusFactory.logOnePlusFactory_distSpec E 1
    (trueCallback (rT := rT)) (true_callback_spec E)) F I

example : (LogOnePlusFactory.bias 1 : ℝ) = Real.log 2 := by
  norm_num [LogOnePlusFactory.bias]
example : (ComplementLogOnePlus.bias 1 : ℝ) = 1 - Real.log 2 := by
  rw [ComplementLogOnePlus.bias_coe]
  norm_num
example : RealCoin.credit (LogOnePlusFactory.bias 0)
    (fun b => if b then ∞ else 0) = 0 := by
  simp [LogOnePlusFactory.bias, RealCoin.credit, RealCoin.pmf]
example : RealCoin.credit (ComplementLogOnePlus.bias 0)
    (fun b => if b then 0 else ∞) = 0 := by
  simp [ComplementLogOnePlus.bias, LogOnePlusFactory.bias, RealCoin.credit, RealCoin.pmf]

#print axioms SampLib.LogOnePlusFactory.logOnePlusFactory_distSpec
#print axioms SampLib.LogOnePlusFactory.expectation
#print axioms SampLib.LogOnePlusFactory.integral
#print axioms SampLib.ComplementLogOnePlus.complementLogOnePlus_distSpec
#print axioms SampLib.ComplementLogOnePlus.twp_complementLogOnePlus


#print axioms SampLib.LinearFactory.linear_distSpec
#print axioms SampLib.LinearFactory.expectation
#print axioms SampLib.LinearFactory.inner_expectation
#print axioms SampLib.LinearFactory.Parameters.expected_calls_bound
#print axioms SampLib.IsDistSpec.wp_supported
#print axioms SampLib.FromBounds.fromBounds_distSpec
#print axioms SampLib.UniformBag.twp_bracket
#print axioms SampLib.BagProduct.twp_product
#print axioms SampLib.BagReciprocal.oneDivOnePlus_coinSpec
#print axioms SampLib.BagReciprocal.expectation


#print axioms SampLib.SampleGeometricBag.sampleGeometricBag_coinSpec
#print axioms SampLib.SampleGeometricBag.twp_sampleGeometricBag
#print axioms SampLib.UniformBag.IsCoinSpec.wp
#print axioms SampLib.LatentBernoulli.half_kernel
#print axioms SampLib.LatentBernoulli.expectation
#print axioms SampLib.FromBounds.output_expectation
#print axioms SampLib.FromBounds.initial_expectation
#print axioms SampLib.FromBounds.unresolved_credit
#print axioms SampLib.FromBounds.exists_horizon

end
end ExpansionFactoriesReview
