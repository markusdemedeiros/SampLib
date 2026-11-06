import SampLib.Constants.PiAffine
import SampLib.Constants.ReciprocalPiScaled
import SampLib.Constants.EScaled
import SampLib.Constants.EOverPi
import SampLib.Bernoulli.Laws.PiProbability
import SampLib.Bernoulli.Laws.ReciprocalPiProbability
import SampLib.Bernoulli.Laws.PiBoundsState
import SampLib.Bernoulli.Support.PiBounds
import SampLib.Bernoulli.EulerBounds
import SampLib.Templates
import Metrology.Iris.LocalBI
import SampLib.Constants.ExponentialRationalProduct
import SampLib.Constants.FromPositiveSeries
import SampLib.Constants.ThreeZetaThreeOverFour
import SampLib.Bernoulli.Laws.RationalEnclosureScale
import SampLib.Constants.InverseEPlusRational
import SampLib.Constants.Laws.ExponentialBoundsKernel

-- Prior cohort: replay after the coordinated support-only formatting change.
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
example : ((PiBounds.arctanRaw 2 1).1 : ℝ) / (PiBounds.arctanRaw 2 1).2.2 = 11/24 := by
  norm_num [PiBounds.arctanRaw, PiBounds.numerator, PiBounds.denominator,
    PiBounds.termDenominator, PiBounds.sign]
example : ((PiBounds.arctanRaw 2 2).2.1 : ℝ) / (PiBounds.arctanRaw 2 2).2.2 = 223/480 := by
  norm_num [PiBounds.arctanRaw, PiBounds.numerator, PiBounds.denominator,
    PiBounds.termDenominator, PiBounds.sign]
example : (3 : ℝ) < ((PiBounds.piRaw 0).1 : ℝ) / (PiBounds.piRaw 0).2.2 := by
  norm_num [PiBounds.piRaw, PiBounds.arctanRaw, PiBounds.numerator, PiBounds.denominator,
    PiBounds.termDenominator, PiBounds.sign]
example (E : CoPset) (n : ℕ) (I : IProp GF) : I ⊢
    tglWp E pl(&Occil.Constants.piBounds #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = RealEnclosure.encodeInterval (PiBounds.interval n)⌝ ∗ I)) := by
  have hp := PiBounds.twp_piBounds (rT := rT) (GF := GF) E n
  rw [← PiBounds.encode_interval] at hp
  iintro HI
  iapply tglWp_wand
  isplitl []
  · iapply hp
  iintro %v %hv
  subst v
  iframe HI
  itrivial
example (E : CoPset) (n : ℕ) (I : IProp GF) : I ⊢
    tglWp E pl(&Occil.Constants.eBounds #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = RealEnclosure.encodeInterval (EulerEnclosure.interval n)⌝ ∗ I))
    := by
  iintro HI
  iapply tglWp_wand
  isplitl []
  · iapply EulerEnclosure.twp_eBounds E n
  iintro %v %hv
  subst v
  iframe HI
  itrivial
example {rT : Type} : RealEnclosure.encodeInterval (rT := rT) (EulerEnclosure.interval 2) =
    Val.pair (Val.int 48) (Val.pair (Val.int 49) (Val.int 18)) := by
  rfl
private def signedZero : RealEnclosure.Interval (0 : ℝ) where
  lower := -1
  upper := 1
  denominator := 1
  positive := by norm_num
  below := by norm_num
  above := by norm_num
private def exactTwo : RealEnclosure.Interval (2 : ℝ) where
  lower := 2
  upper := 2
  denominator := 1
  positive := by norm_num
  below := by norm_num
  above := by norm_num
example : (signedZero.quotient exactTwo (by norm_num)
    (by norm_num [RealEnclosure.Interval.left, exactTwo])).triple = (-2, (2, 4)) := by
  rfl

private theorem fourEleven : Real.exp 1 * ((4 : ℕ) : ℝ) / ((11 : ℕ) : ℝ) ≤ 1 := by
  have h := EulerEnclosure.upper_bound 2 (by norm_num)
  norm_num [EulerEnclosure.numerator] at h
  linarith
example : 1 < ((EulerEnclosure.interval 0).scale 4 11 (by norm_num)).right := by
  norm_num [RealEnclosure.Interval.right, RealEnclosure.Interval.scale,
    EulerEnclosure.interval, EulerEnclosure.numerator]

variable [ProbLangDist.IsUniformInt rT]
example (E : CoPset) (u v : ℕ) (hv : 0 < v) (h : Real.exp 1 * u / v ≤ 1)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (EScaled.eScaled_distSpec E u v hv h) F I
example (E : CoPset) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (EScaled.eScaled_distSpec E 4 11 (by norm_num) fourEleven) F I
example (E : CoPset) (I : IProp GF) :=
  frame (EScaled.eScaled_distSpec E 0 7 (by norm_num) (by simp))
    (fun b => if b then ∞ else 0) I
example : RealCoin.credit (EScaled.bias 0 7 (by simp))
    (fun b => if b then ∞ else 0) = 0 := by
  have hb : EScaled.bias 0 7 (by simp) = 0 := Subtype.ext (by simp [EScaled.bias])
  rw [hb]
  simp [RealCoin.credit, RealCoin.pmf]
example (E : CoPset) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (EulerPi.eOverPi_distSpec E) F I
example (E : CoPset) (I : IProp GF) :=
  frame (EulerPi.eOverPi_distSpec E) (fun b => if b then ∞ else 0) I
example : RealCoin.credit EulerPi.bias (fun _ => ∞) = ∞ := by
  rw [← RealCoin.lintegral_law]
  simp only [MeasureTheory.lintegral_const, MeasureTheory.measure_univ, mul_one]

private theorem pi_lt_four : Real.pi < 4 := by
  have h := (PiBounds.interval 0).le_right
  rw [PiBounds.interval_right] at h
  have hu : ArctanSeries.piUpper 0 < 4 := by
    norm_num [ArctanSeries.piUpper, ArctanSeries.upper_one, ArctanSeries.lower_one]
  exact h.trans_lt hu
private theorem negative_offset_low : 0 ≤ Real.pi - ((-1 : ℤ) : ℝ) := by
  have h := Real.pi_pos
  norm_num
  linarith
private theorem negative_offset_high : Real.pi - ((-1 : ℤ) : ℝ) ≤ ((5 : ℕ) : ℝ) := by
  have h := pi_lt_four
  norm_num
  linarith
example (E : CoPset) (o : ℤ) (d : ℕ) (hd : 0 < d)
    (hlo : 0 ≤ Real.pi-o) (hhi : Real.pi-o ≤ d) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (PiAffine.piAffine_distSpec E o d hd hlo hhi) F I
example (E : CoPset) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (PiAffine.piAffine_distSpec E (-1) 5 (by norm_num)
    negative_offset_low negative_offset_high) F I
example (E : CoPset) (a b : ℕ) (hb : 0 < b) (h : (a : ℝ) ≤ b*Real.pi)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (ReciprocalPiScaled.reciprocalPiScaled_distSpec E a b hb h) F I
example (E : CoPset) (d : ℕ) (hd : 0 < d) (I : IProp GF) :=
  frame (ReciprocalPiScaled.reciprocalPiScaled_distSpec E 0 d hd
    (by simpa only [Nat.cast_zero] using mul_nonneg (Nat.cast_nonneg d) Real.pi_pos.le))
    (fun b => if b then ∞ else 0) I
example (d : ℕ) (hd : 0 < d) (h : ((0 : ℕ) : ℝ) ≤ d * Real.pi) :
    RealCoin.credit (ReciprocalPiProbability.bias 0 d hd h)
      (fun b => if b then ∞ else 0) = 0 := by
  have hb : ReciprocalPiProbability.bias 0 d hd h = 0 := by
    apply Subtype.ext
    simp [ReciprocalPiProbability.bias]
  rw [hb]
  simp [RealCoin.credit, RealCoin.pmf]
private theorem close_reciprocal_valid : ((333 : ℕ) : ℝ) ≤ ((106 : ℕ) : ℝ)*Real.pi := by
  have hl : ((333 : ℕ) : ℝ) ≤ ((106 : ℕ) : ℝ)*(PiBounds.interval 2).left := by
    rw [PiBounds.interval_left]
    norm_num [ArctanSeries.piLower, ArctanSeries.lower, ArctanSeries.upper,
      AlternatingEnclosure.lower, AlternatingEnclosure.upper, AlternatingEnclosure.partialSum,
      AlternatingEnclosure.sign, ArctanSeries.coefficient, Finset.sum_range_succ]
  exact hl.trans (mul_le_mul_of_nonneg_left (PiBounds.interval 2).left_le (by positivity))
example : (PiBounds.interval 0).left < (333 : ℝ)/106 := by
  rw [PiBounds.interval_left]
  norm_num [ArctanSeries.piLower, ArctanSeries.lower_one, ArctanSeries.upper_one]
example (E : CoPset) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (ReciprocalPiScaled.reciprocalPiScaled_distSpec E 333 106 (by norm_num)
    close_reciprocal_valid) F I

#print axioms SampLib.PiAffine.piAffine_distSpec
#print axioms SampLib.ReciprocalPiScaled.reciprocalPiScaled_distSpec
#print axioms SampLib.PiProbability.affine_tight
#print axioms SampLib.ReciprocalPiProbability.tight
#print axioms SampLib.RealEnclosure.left_tendsto
#print axioms SampLib.RealEnclosure.right_tendsto

#print axioms SampLib.EScaled.eScaled_distSpec
#print axioms SampLib.RealEnclosure.Tight.scale
#print axioms SampLib.EulerPi.eOverPi_distSpec
#print axioms SampLib.EulerPi.tight
#print axioms SampLib.RealEnclosure.quotient_width_tendsto
#print axioms SampLib.RealEnclosure.quotient_tight
#print axioms SampLib.RealEnclosure.Interval.quotient_left
#print axioms SampLib.RealEnclosure.Interval.quotient_right

#print axioms SampLib.ArctanSeries.hasSum
#print axioms SampLib.ArctanSeries.machin
#print axioms SampLib.PiBounds.numerator_real
#print axioms SampLib.PiBounds.interval_tight
#print axioms SampLib.EulerEnclosure.twp_eBounds
#print axioms SampLib.EulerEnclosure.lower_bound
#print axioms SampLib.EulerEnclosure.upper_bound
#print axioms SampLib.EulerEnclosure.tight
#print axioms SampLib.ClosedExp.closeRec
end
end ExpansionFactoriesReview

-- New final cohort: four distinct samplers.
open ProbLang
open scoped ENNReal
namespace ExpansionFactoriesFinalReview
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
example : (EulerReciprocal.interval 1 1 (by norm_num) (by norm_num) 0).triple =
    (1, (2, 2)) := by rfl
example : (EulerReciprocal.interval 2 1 (by norm_num) (by norm_num) 0).triple =
    (2, (3, 6)) := by rfl
example : (ExponentialEnclosure.interval 2 1 (by norm_num) 0).triple =
    (-8, (8, 24)) := by rfl
example : ((ExponentialEnclosure.interval 2 1 (by norm_num) 0).scale 4 1
    (by norm_num)).triple = (-32, (32, 24)) := by rfl
example : (ExponentialEnclosure.interval 2 1 (by norm_num) 0).left < 0 := by
  norm_num [RealEnclosure.Interval.left, ExponentialEnclosure.interval,
    ExponentialEnclosure.lower, ExponentialEnclosure.last, ExponentialEnclosure.middle,
    ExponentialEnclosure.numerator, ExponentialEnclosure.power, ExponentialEnclosure.denominator]

variable [ProbLangDist.IsUniformInt rT]
example (E : CoPset) (a b : ℕ) (hb : 0 < b) (hab : b ≤ a)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (InverseEPlusRational.inverseEPlusRational_distSpec E a b hb hab) F I
example (E : CoPset) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (InverseEPlusRational.inverseEPlusRational_distSpec E 1 1 (by norm_num) (by norm_num)) F I
example (E : CoPset) (I : IProp GF) :=
  frame (InverseEPlusRational.inverseEPlusRational_distSpec E 7 7 (by norm_num) (by norm_num))
    (fun b => if b then ∞ else 0) I
example : (InverseEPlusRational.bias 1 1 (by norm_num) (by norm_num) : ℝ) =
    1/(Real.exp 1-1) := by
  simp [InverseEPlusRational.bias, EulerReciprocal.center]
  ring
private def zeroCoefficient : FromPositiveSeries.Coefficient :=
  ⟨0, 1, by norm_num, 0, 1, by norm_num⟩
private def zeroSeries : FromPositiveSeries.Parameters where
  coefficient := fun _ => zeroCoefficient
  summable := by simp [zeroCoefficient, FromPositiveSeries.Coefficient.value]
  mass_le_one := by simp [zeroCoefficient, FromPositiveSeries.Coefficient.value]
  remainder n := by
    simp [zeroCoefficient, FromPositiveSeries.Coefficient.value,
      FromPositiveSeries.Coefficient.error]
  tight ε hε := ⟨0, by simpa [zeroCoefficient, FromPositiveSeries.Coefficient.error] using hε.le⟩
private def unitCoefficient (n : ℕ) : FromPositiveSeries.Coefficient :=
  ⟨if n=0 then 1 else 0, 1, by norm_num, 0, 1, by norm_num⟩
private def unitSeries : FromPositiveSeries.Parameters where
  coefficient := unitCoefficient
  summable := by
    apply summable_of_ne_finset_zero (s := {0})
    intro n hn
    have hne : n ≠ 0 := by simpa using hn
    simp [unitCoefficient, FromPositiveSeries.Coefficient.value, hne]
  mass_le_one := by simp [unitCoefficient, FromPositiveSeries.Coefficient.value]
  remainder n := by
    simp [unitCoefficient, FromPositiveSeries.Coefficient.value,
      FromPositiveSeries.Coefficient.error]
  tight ε hε := ⟨0, by simpa [unitCoefficient, FromPositiveSeries.Coefficient.error] using hε.le⟩

private def zeroOracle {rT : Type} : Val rT :=
  ⟨pl(fun position, if #false then term position else
    &(FromPositiveSeries.encodeCoefficient zeroCoefficient).fst), .lam (by is_lc), by is_lc⟩
example {rT : Type} : (zeroOracle (rT := rT)).fst.fv ≠ ∅ := by
  simp [zeroOracle, Exp.fv, Exp.close, Exp.closeRec, FromPositiveSeries.encodeCoefficient]
omit [ProbLangDist.IsUniformInt rT] in
private theorem zeroOracle_spec (E : CoPset) (n : ℕ) :
    ⊢ tglWp E pl(&(zeroOracle (rT := rT)).fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = FromPositiveSeries.encodeCoefficient
        (zeroSeries.coefficient n)⌝)) := by
  twp_pures
  twp_value
  imodintro
  ipureintro
  rfl
private def unitOracle {rT : Type} : Val rT :=
  ⟨pl(fun position, if position = #0 then
      &(FromPositiveSeries.encodeCoefficient (unitCoefficient 0)).fst else
      &(FromPositiveSeries.encodeCoefficient zeroCoefficient).fst), .lam (by is_lc), by is_lc⟩
omit [ProbLangDist.IsUniformInt rT] in
private theorem unitOracle_spec (E : CoPset) (n : ℕ) :
    ⊢ tglWp E pl(&(unitOracle (rT := rT)).fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = FromPositiveSeries.encodeCoefficient
        (unitSeries.coefficient n)⌝)) := by
  by_cases hn : n=0
  · subst n
    twp_pures
    twp_value
    imodintro
    ipureintro
    rfl
  · have he : ((BaseLit.int (n : ℤ) : BaseLit rT) == .int 0) = false := by
      change ((n : ℤ) == 0) = false
      apply beq_eq_false_iff_ne.mpr
      exact_mod_cast hn
    twp_pures
    rw [he]
    twp_pures
    twp_value
    imodintro
    ipureintro
    apply Val.ext
    simp [unitSeries, unitCoefficient, hn, zeroCoefficient,
      FromPositiveSeries.encodeCoefficient, Exp.closeRec, Exp.openRec]
example (E : CoPset) (a : FromPositiveSeries.Parameters) (term : Val rT)
    (ht : ∀ n : ℕ, ⊢ tglWp E pl(&term.fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = FromPositiveSeries.encodeCoefficient (a.coefficient n)⌝)))
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (FromPositiveSeries.fromPositiveSeries_distSpec E a term ht) F I
example (E : CoPset) (I : IProp GF) :=
  frame (FromPositiveSeries.fromPositiveSeries_distSpec E zeroSeries
    zeroOracle (zeroOracle_spec E)) (fun b => if b then ∞ else 0) I
example (E : CoPset) (I : IProp GF) :=
  frame (FromPositiveSeries.fromPositiveSeries_distSpec E unitSeries
    unitOracle (unitOracle_spec E)) (fun b => if b then 0 else ∞) I
example : FromPositiveSeries.bias zeroSeries = 0 := by
  apply Subtype.ext
  simp [FromPositiveSeries.bias, zeroSeries, zeroCoefficient,
    FromPositiveSeries.Coefficient.value]
example : FromPositiveSeries.bias unitSeries = 1 := by
  apply Subtype.ext
  simp [FromPositiveSeries.bias, unitSeries, unitCoefficient,
    FromPositiveSeries.Coefficient.value]
example (E : CoPset) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (ZetaThree.threeZetaThreeOverFour_distSpec E) F I
example : (FromPositiveSeries.bias ZetaThree.parameters : ℝ) =
    (3 : ℝ)/4 * ∑' n : ℕ, 1/((n : ℝ)+1)^3 := ZetaThree.bias_coe
example : (FromPositiveSeries.bias ZetaThree.parameters : ℝ) ≤ 15/16 := by
  rw [ZetaThree.bias_coe]
  have h := ZetaThree.zetaThree_le
  linarith
private theorem compensated :
    Real.exp (-(((2 : ℕ) : ℝ)/((1 : ℕ) : ℝ))) * ((4 : ℕ) : ℝ)/((1 : ℕ) : ℝ) ≤ 1 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) 3
  norm_num [Finset.sum_range_succ] at h
  norm_num only [Nat.cast_ofNat, div_one]
  rw [Real.exp_neg, mul_comm, ← div_eq_mul_inv]
  exact (div_le_one (Real.exp_pos 2)).mpr (by linarith)
omit [ProbLangDist.IsUniformInt rT] in
example (E : CoPset) (x y n : ℕ) (hy : 0 < y) (I : IProp GF) : I ⊢
    tglWp E pl(&Occil.Constants.expMinusBounds #int (x : ℤ) #int (y : ℤ) #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = RealEnclosure.encodeInterval
        (ExponentialEnclosure.interval x y hy n)⌝ ∗ I)) := by
  iintro HI
  iapply tglWp_wand
  isplitl []
  · iapply ExponentialEnclosure.twp_expMinusBounds E x y hy n
  iintro %v %hv
  subst v
  iframe HI
  itrivial
example (E : CoPset) (x y z t : ℕ) (hy : 0 < y) (ht : 0 < t)
    (h : Real.exp (-((x : ℝ)/y))*z/t ≤ 1) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (ExponentialRationalProduct.exponentialRationalProduct_distSpec E x y z t hy ht h) F I
example (E : CoPset) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (ExponentialRationalProduct.exponentialRationalProduct_distSpec E 2 1 4 1
    (by norm_num) (by norm_num) compensated) F I
example (E : CoPset) (I : IProp GF) :=
  frame (ExponentialRationalProduct.exponentialRationalProduct_distSpec E 0 1 1 1
    (by norm_num) (by norm_num) (by simp)) (fun b => if b then 0 else ∞) I
example (E : CoPset) (I : IProp GF) :=
  frame (ExponentialRationalProduct.exponentialRationalProduct_distSpec E 9 7 0 2
    (by norm_num) (by norm_num) (by simp)) (fun b => if b then ∞ else 0) I
example : ExponentialRationalProduct.bias 0 1 1 1 (by simp) = 1 := by
  apply Subtype.ext
  simp [ExponentialRationalProduct.bias]
example : ExponentialRationalProduct.bias 9 7 0 2 (by simp) = 0 := by
  apply Subtype.ext
  simp [ExponentialRationalProduct.bias]
#print axioms SampLib.ExponentialRationalProduct.exponentialRationalProduct_distSpec
#print axioms SampLib.ExponentialEnclosure.twp_expMinusBounds

#print axioms SampLib.FromPositiveSeries.fromPositiveSeries_distSpec
#print axioms SampLib.FromPositiveSeries.twp_fromPositiveSeries
#print axioms SampLib.FromPositiveSeries.Program.source_eq
#print axioms SampLib.twp_beta
#print axioms SampLib.UniformBag.twp_choice
#print axioms SampLib.ZetaThree.threeZetaThreeOverFour_distSpec
#print axioms SampLib.ZetaThree.bias_coe
#print axioms SampLib.ZetaThree.parameters

#print axioms SampLib.InverseEPlusRational.inverseEPlusRational_distSpec
#print axioms SampLib.EulerReciprocal.tight
#print axioms SampLib.EulerReciprocal.triple_eq
#print axioms SampLib.EulerReciprocal.center_ge_one
#print axioms SampLib.ExponentialEnclosure.remainder
#print axioms SampLib.ExponentialEnclosure.bounds
#print axioms SampLib.ExponentialEnclosure.tight
#print axioms SampLib.ExponentialEnclosure.numerator_ratio
end
end ExpansionFactoriesFinalReview
