import SampLib.IntegerPower
import SampLib.SupportedSpec
import SampLib.Distributions.LogUniformBuckets
import SampLib.Samplers.RndIntRange
import Samplers.Discrete.Tails

/-! # Logarithmic bucket sampling

Choose a magnitude level uniformly, then draw uniformly within its bucket.
The last bucket is clipped to the inclusive bound and retains one level's mass.
-/

open Set ProbLang
open scoped ENNReal

namespace SampLib.LogUniform

noncomputable section

section mathematics

open MeasureTheory Measure

/-- Zero is its own bucket; every positive level is an inclusive integer interval. -/
def bucket (maximum base level : ℕ) : Measure ℤ :=
  if level = 0 then dirac 0 else
    RndIntRange.law (lower maximum base level) (upper maximum base level)

instance (maximum base level : ℕ) : IsProbabilityMeasure (bucket maximum base level) := by
  unfold bucket
  split <;> infer_instance

/-- The finite mixture gives equal weight to every logarithmic level. -/
def law (maximum base : ℕ) : Measure ℤ :=
  (RndInt.law (lastLevel maximum base)).bind (bucket maximum base)

instance (maximum base : ℕ) : IsProbabilityMeasure (law maximum base) where
  measure_univ := by
    rw [law, Measure.bind_apply MeasurableSet.univ (measurable_of_countable _).aemeasurable]
    simp

/-- Equal-weight bucket expectations are precisely the log-uniform expectation. -/
theorem expectation (maximum base : ℕ) (F : ℤ → ℝ≥0∞) :
    ∫⁻ level, (∫⁻ z, F z ∂bucket maximum base level)
      ∂RndInt.law (lastLevel maximum base) = ∫⁻ z, F z ∂law maximum base := by
  rw [law, Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aemeasurable]

/-- Every logarithmic level carries the same mass, including a clipped last bucket. -/
theorem lintegral_law (maximum base : ℕ) (F : ℤ → ℝ≥0∞) :
    ∫⁻ z, F z ∂law maximum base =
      (∑ level ∈ Finset.range (lastLevel maximum base + 1),
        ∫⁻ z, F z ∂bucket maximum base level) / (lastLevel maximum base + 1) := by
  rw [← expectation, RndInt.expectation, Nat.cast_add, Nat.cast_one]

@[simp] theorem law_zero (base : ℕ) : law 0 base = dirac 0 := by
  apply Measure.ext_of_singleton
  intro z
  rw [← lintegral_indicator_one (measurableSet_singleton z), lintegral_law]
  simp [bucket]

/-- The inclusive level draw stays within the finite set of magnitude buckets. -/
theorem level_support (maximum base : ℕ) :
    ∀ᵐ level ∂RndInt.law (lastLevel maximum base), level ≤ lastLevel maximum base := by
  apply ae_iff_of_countable.mpr
  intro level hlevel
  by_contra h
  apply hlevel
  simp [RndInt.law, UniformInt.law, uniformOfFinset_apply_singleton,
    show ¬level < lastLevel maximum base + 1 by omega]

end mathematics

private def ceilingLoop {rT : Type _} (maximum base : ℕ) : Exp rT := pl%
  rec count power exponent := if #int (maximum : ℤ) + #1 <= power then exponent else
    count (power * #int (base : ℤ)) (exponent + #1)

private theorem power_cast (base exponent : ℕ) :
    (base : ℤ) ^ exponent = ((base ^ exponent : ℕ) : ℤ) := by
  norm_cast

private theorem integerPower_open {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.DiscreteExtra.integerPower = Occil.DiscreteExtra.integerPower :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem integerPower_close {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.DiscreteExtra.integerPower : Exp rT) =
      Occil.DiscreteExtra.integerPower :=
  Exp.closeRec_fresh x _ k (by simp [Occil.DiscreteExtra.integerPower, Exp.fv])

private theorem range_open {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.rndIntRange = Occil.rndIntRange :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem range_close {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.rndIntRange : Exp rT) = Occil.rndIntRange :=
  Exp.closeRec_fresh x _ k (by simp [Occil.rndIntRange, Exp.fv, RndInt.rndInt_fv])

attribute [local pl_step_simp] integerPower_open integerPower_close range_open range_close
  RndInt.rndInt_openRec RndInt.rndInt_closeRec

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem bound_test (maximum base exponent : ℕ) (hb : 1 < base)
    (h : lastLevel maximum base ≤ exponent) :
    decide ((maximum : ℤ) + 1 ≤ ((base ^ exponent : ℕ) : ℤ)) = true := by
  apply decide_eq_true
  change Nat.clog base (maximum + 1) ≤ exponent at h
  exact_mod_cast (Nat.clog_le_iff_le_pow hb).mp h

private theorem next_test (maximum base exponent : ℕ) (hb : 1 < base)
    (h : exponent < lastLevel maximum base) :
    decide ((maximum : ℤ) + 1 ≤ ((base ^ exponent : ℕ) : ℤ)) = false := by
  apply decide_eq_false
  change exponent < Nat.clog base (maximum + 1) at h
  have hp := (Nat.lt_clog_iff_pow_lt hb).mp h
  exact_mod_cast (not_le.mpr hp)

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_ceilingLoop (E : CoPset) (maximum base : ℕ) (hb : 1 < base)
    (fuel exponent : ℕ) (h : exponent + fuel = lastLevel maximum base) :
    ⊢ tglWp E pl(&(ceilingLoop maximum base) #int ((base ^ exponent : ℕ) : ℤ)
      #int (exponent : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (lastLevel maximum base : ℤ)⌝)) := by
  induction fuel generalizing exponent with
  | zero =>
    have he : exponent = lastLevel maximum base := by omega
    twp_pures
    rw [bound_test maximum base exponent hb (by omega)]
    twp_pures
    twp_value
    imodintro
    ipureintro
    subst exponent
    rfl
  | succ fuel ih =>
    have he : exponent < lastLevel maximum base := by omega
    twp_pures
    rw [next_test maximum base exponent hb he]
    iterate 3 twp_pure
    rw [show ((base ^ exponent : ℕ) : ℤ) * (base : ℤ) =
      ((base ^ (exponent + 1) : ℕ) : ℤ) by simp [pow_succ]]
    rw [← Nat.cast_add_one]
    twp_bind pl(&(ceilingLoop maximum base) #int ((base ^ (exponent + 1) : ℕ) : ℤ)
      #int ((exponent + 1 : ℕ) : ℤ))
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply ih (exponent + 1) (by omega)

private theorem base_test (base : ℕ) (hb : 1 < base) :
    decide ((base : ℤ) < 2) = false := decide_eq_false (by omega)

private theorem level_test {rT : Type _} [BEq rT] (level : ℕ) (hl : level ≠ 0) :
    ((BaseLit.int (level : ℤ) : BaseLit rT) == .int 0) = false := by
  change ((level : ℤ) == 0) = false
  simp [hl]

private theorem lower_test (maximum base level : ℕ) (hl : 0 < level)
    (hlevel : level ≤ lastLevel maximum base) :
    decide ((maximum : ℤ) < ((base ^ (level - 1) : ℕ) : ℤ)) = false := by
  apply decide_eq_false
  exact_mod_cast (not_lt.mpr (lower_pow_le maximum base level hl hlevel))

private theorem pred_cast (n : ℕ) (h : 0 < n) :
    (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) := by omega

private theorem min_cast (a b : ℕ) : min (a : ℤ) (b : ℤ) = ((min a b : ℕ) : ℤ) := by
  omega

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_min (E : CoPset) (x y : ℤ) :
    ⊢ tglWp E pl(if #int x < #int y then #int x else #int y)
      (fun v : Val rT => iprop(⌜v = Val.int (min x y)⌝)) := by
  twp_pures
  by_cases h : x < y
  · rw [decide_eq_true h]
    twp_pures
    twp_value
    imodintro
    ipureintro
    simp [h.le]
  · rw [decide_eq_false h]
    twp_pures
    twp_value
    imodintro
    ipureintro
    simp [le_of_not_gt h]

/-- Draw a logarithmic magnitude and then one uniform integer in its clipped bucket. -/
theorem twp_logUniform (E : CoPset) (maximum base : ℕ) (hb : 1 < base)
    (F : ℤ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ z, F z ∂law maximum base) -∗
      tglWp E pl(&Occil.DiscreteExtra.logUniform #int (maximum : ℤ) #int (base : ℤ))
        (fun v : Val rT => iprop(∃ z : ℤ, ⌜v = Val.int z⌝ ∗ ↯ (F z))) := by
  iintro Hcredit
  twp_pures
  rw [base_test base hb]
  simp only [Bool.or_false]
  iterate 2 twp_pure
  twp_bind pl(&(ceilingLoop maximum base) #1 #0)
  iapply tglWp_wand
  isplitl []
  · have hclog := twp_ceilingLoop (rT := rT) (GF := GF) E maximum base hb
      (lastLevel maximum base) 0 (by omega)
    simp only [pow_zero] at hclog
    iapply hclog
  iintro %v %hv
  subst v
  twp_bind pl(&Occil.rndInt #int (lastLevel maximum base : ℤ))
  isimp only [← expectation maximum base F] at Hcredit
  iapply ((RndInt.rndInt_distSpec E (lastLevel maximum base)).wp_supported
    (fun level => level ≤ lastLevel maximum base) ((Set.to_countable _).measurableSet)
    (level_support maximum base) (fun level => ∫⁻ z, F z ∂bucket maximum base level)
    (measurable_of_countable _) _) $$ Hcredit
  iintro %level %hlevel Hcredit
  twp_pures
  by_cases hl : level = 0
  · subst level
    twp_pures
    twp_value
    imodintro
    iexists 0
    isimp only [bucket, ite_true, MeasureTheory.lintegral_dirac] at Hcredit
    iframe Hcredit
    itrivial
  · have hpos : 0 < level := Nat.pos_of_ne_zero hl
    rw [level_test level hl]
    iterate 2 twp_pure
    rw [pred_cast level hpos]
    twp_bind pl(&Occil.DiscreteExtra.integerPower #int (base : ℤ)
      #int ((level - 1 : ℕ) : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply twp_integerPower E base (level - 1)
    iintro %v %hv
    subst v
    rw [power_cast]
    twp_pure
    twp_bind pl(&Occil.DiscreteExtra.integerPower #int (base : ℤ) #int (level : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply twp_integerPower E base level
    iintro %v %hv
    subst v
    rw [power_cast]
    twp_pure
    rw [pred_cast (base ^ level) (pow_pos (by omega) level)]
    twp_pure
    twp_pures
    rw [lower_test maximum base level hpos hlevel]
    iterate 2 twp_pure
    twp_bind pl(if #int (maximum : ℤ) < #int ((base ^ level - 1 : ℕ) : ℤ)
      then #int (maximum : ℤ) else #int ((base ^ level - 1 : ℕ) : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply twp_min E maximum ((base ^ level - 1 : ℕ) : ℤ)
    iintro %v %hv
    subst v
    rw [min_cast]
    twp_pure
    rw [← lower_eq_pow maximum base level hpos hlevel]
    isimp only [bucket, ite_eq_right hl] at Hcredit
    twp_bind pl(&Occil.rndIntRange #int (lower maximum base level : ℤ)
      #int (upper maximum base level : ℤ))
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply (RndIntRange.twp_rndIntRange E (lower maximum base level)
      (upper maximum base level) (by exact_mod_cast lower_le_upper maximum base level hb hpos)
      F) $$ Hcredit

/-- Typed log-uniform law for every nonnegative inclusive bound and integer base at least two. -/
theorem logUniform_distSpec (E : CoPset) (maximum base : ℕ) (hb : 1 < base) :
    IsDistSpec (GF := GF) E pl(&Occil.DiscreteExtra.logUniform
      #int (maximum : ℤ) #int (base : ℤ)) (law maximum base) Val.int where
  spec F _ := wand_entails (twp_logUniform E maximum base hb F)

end specification

end

end SampLib.LogUniform
