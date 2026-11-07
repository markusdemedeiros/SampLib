import SampLib.PSRN.Syntax.ExponentialCount
import SampLib.Bernoulli.Complement
import SampLib.Latent.LatentDigits
import SampLib.PSRN.Support.Exponential.Logistic
import SampLib.PSRN.Laws.ExponentialDigitLaw
import SampLib.PSRN.Laws.ExponentialWholeFraction

/-! # Decay callbacks for the exponential constructor

The integer part uses the unit-scale decay. Each fractional digit uses the
decay at twice its current denominator and the original fair-selector loop.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.ExponentialCount

noncomputable section

abbrev stoppingBias (q : unitInterval) : unitInterval := unitInterval.symm q
abbrev law (q : unitInterval) := Geometric.law (stoppingBias q)

private theorem stopping_pos (q : unitInterval) (hq : (q : ℝ) < 1) :
    0 < (stoppingBias q : ℝ) := by
  change 0 < 1 - (q : ℝ)
  exact sub_pos.mpr hq

private theorem amplification_gt_one (q : unitInterval) (hq : (q : ℝ) < 1) :
    1 < Geometric.terminationFactor (stoppingBias q) := by
  change 1 < 1 + unitInterval.toNNReal (stoppingBias q)
  exact lt_add_of_pos_right _ (by exact_mod_cast stopping_pos q hq)

/-- Complementing the continuation turns decay survival into the geometric stopping recurrence. -/
theorem expectation (q : unitInterval) (hq : (q : ℝ) < 1)
    (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∫⁻ b, Geometric.coinCredit (stoppingBias q) F ε (!b) ∂RealCoin.law q) =
      Geometric.credit (stoppingBias q) F + ε := by
  rw [Complement.expectation_preservation]
  exact Geometric.lintegral_coinCredit (stoppingBias q) (stopping_pos q hq) F ε

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Starting from an arbitrary integer adds a geometric number of decay successes. -/
theorem twp_count (E : CoPset) (q : unitInterval) (hq : (q : ℝ) < 1)
    (decay : Val rT)
    (hdecay : IsDistSpec (GF := GF) E pl(&decay.fst #1) (RealCoin.law q) Val.bool)
    (whole : ℤ) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (Geometric.credit (stoppingBias q) F) -∗
      tglWp E pl(&(Program.countVal decay).fst #int whole)
        (fun result : Val rT => iprop(∃ n : ℕ,
          ⌜result = Val.int (whole + n)⌝ ∗ ↯ (F n))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert! %whole %F
  iapply ErrorCredit.Induction.simple hε (amplification_gt_one q hq) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ %whole %F Hcredit
  unfold Program.countVal Program.countCode
  twp_pures
  twp_bind pl(&decay.fst #1)
  icombine Hcredit Hterm as Hcredit
  isimp only [← expectation q hq F ε] at Hcredit
  iapply hdecay.wp (fun b => Geometric.coinCredit (stoppingBias q) F ε (!b))
    (measurable_of_countable _) _ $$ Hcredit
  iintro %b Hcredit
  cases b
  · isimp only [Bool.not_false, Geometric.coinCredit] at Hcredit
    ihave ⟨Hcredit, _⟩ := ErrorCredit.split $$ Hcredit
    twp_pures
    twp_value
    imodintro
    iexists 0
    iframe Hcredit
    ipureintro
    simp
  · isimp only [Bool.not_true, Geometric.coinCredit] at Hcredit
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    twp_pure
    twp_pure
    iapply tglWp_wand
    isplitl [IH Hcredit Hterm]
    · iapply IH $$ Hterm %(whole + 1) %(fun n => F (n + 1)) Hcredit
    iintro %result ⟨%n, %hn, Hcredit⟩
    iexists n + 1
    iframe Hcredit
    ipureintro
    rw [hn, add_assoc, add_comm (1 : ℤ), ← Nat.cast_add_one]

/-- The literal loop started at zero supplies the constructor's geometric whole part. -/
theorem count_distSpec (E : CoPset) (q : unitInterval) (hq : (q : ℝ) < 1)
    (decay : Val rT)
    (hdecay : IsDistSpec (GF := GF) E pl(&decay.fst #1) (RealCoin.law q) Val.bool) :
    IsDistSpec (GF := GF) E pl(&(Program.countVal decay).fst #0)
      (law q) (fun n : ℕ => Val.int (n : ℤ)) where
  spec F _ := by
    simpa only [Geometric.credit, zero_add] using
      wand_entails (twp_count E q hq decay hdecay 0 F)

end specification

end

end SampLib.ExponentialCount

open ProbLang

namespace SampLib.PSRNExponential

noncomputable section

/-- The callback's exact decay probability at a positive integer divisor. -/
def decayBias (rate : ℝ) (hrate : 0 < rate) (d : ℕ) (hd : 0 < d) : unitInterval :=
  ⟨Real.exp (-(rate / d)), (Real.exp_pos _).le,
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg hrate.le (by positivity)))⟩

theorem decayBias_lt_one (rate : ℝ) (hrate : 0 < rate) (d : ℕ) (hd : 0 < d) :
    (decayBias rate hrate d hd : ℝ) < 1 :=
  Real.exp_lt_one_iff.mpr (neg_neg_of_pos (div_pos hrate (by positivity)))

theorem whole_bias (rate : ℝ) (hrate : 0 < rate) :
    unitInterval.symm (decayBias rate hrate 1 (by decide)) =
      ExponentialDigits.wholeBias rate hrate := by
  apply Subtype.ext
  simp [unitInterval.symm, decayBias, ExponentialDigits.wholeBias]

theorem digit_bias (rate : ℝ) (hrate : 0 < rate) (n : ℕ) :
    ExponentialLogistic.bias (decayBias rate hrate (2 ^ n * 2) (by positivity)) =
      ExponentialDigits.bitBias rate (1 / 2 ^ n) := by
  apply Subtype.ext
  rw [ExponentialLogistic.bias_coe, ExponentialDigits.bitBias_coe_decay]
  have h : rate / ((2 ^ n * 2 : ℕ) : ℝ) = rate * (1 / 2 ^ n) / 2 := by
    push_cast
    ring
  simp only [decayBias, h]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Every call is an independent exact decay trial at the requested positive divisor. -/
structure IsDecaySpec (E : CoPset) (rate : ℝ) (hrate : 0 < rate) (decay : Val rT) : Prop where
  spec (d : ℕ) (hd : 0 < d) :
    IsDistSpec (GF := GF) E pl(&decay.fst #int (d : ℤ))
      (RealCoin.law (decayBias rate hrate d hd)) Val.bool

/-- The source's unchanged whole-part counter has the geometric strip law. -/
theorem whole_distSpec (E : CoPset) (rate : ℝ) (hrate : 0 < rate) (decay : Val rT)
    (hdecay : IsDecaySpec (GF := GF) E rate hrate decay) :
    IsDistSpec (GF := GF) E pl(&(ExponentialCount.Program.countVal decay).fst #0)
      (Geometric.law (ExponentialDigits.wholeBias rate hrate)) (fun k => Val.int (k : ℤ)) := by
  have h := ExponentialCount.count_distSpec E (decayBias rate hrate 1 (by decide))
    (decayBias_lt_one rate hrate 1 (by decide)) decay (hdecay.spec 1 (by decide))
  simpa only [ExponentialCount.law, ExponentialCount.stoppingBias, whole_bias] using h

variable [ProbLangDist.IsUniformInt rT]

/-- The actual digit closure supplies the fractional law's conditional next-bit kernel. -/
theorem digitSpec (E : CoPset) (rate : ℝ) (hrate : 0 < rate) (decay : Val rT)
    (hdecay : IsDecaySpec (GF := GF) E rate hrate decay)
    [MeasureTheory.IsProbabilityMeasure (ExponentialDigits.fraction rate)] :
    LatentDigits.IsNextDigitSpec (GF := GF) E (ExponentialDigits.fraction rate)
      ExponentialDigits.digits ExponentialDigits.measurable_digits
      (ExponentialLogistic.Program.digitVal decay) where
  coin p := by
    have := DigitPosterior.nextLaw_probability (ExponentialDigits.fraction rate)
      ExponentialDigits.measurable_digits p.val p.property
    change IsDistSpec (GF := GF) E
      pl(&(ExponentialLogistic.Program.digitVal decay).fst
        #int (UniformBag.rank p.val) #int (2 ^ p.val.length))
      (DigitPosterior.nextLaw (ExponentialDigits.fraction rate) ExponentialDigits.digits p.val)
      Val.bool
    have h := ExponentialLogistic.digit_distSpec E
      (decayBias rate hrate (2 ^ p.val.length * 2) (by positivity))
      decay (UniformBag.rank p.val) (2 ^ p.val.length)
      (by simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
        hdecay.spec (2 ^ p.val.length * 2) (by positivity))
    simpa only [ExponentialDigits.next_law rate hrate, digit_bias] using h

end specification

end

end SampLib.PSRNExponential
