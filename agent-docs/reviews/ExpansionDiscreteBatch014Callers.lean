import SampLib.Samplers.DiscreteLaplace
import SampLib.Samplers.FloatingMultiply
import SampLib.Samplers.FastDiceRoller
import Metrology.Iris.LocalBI

/-! Independent discrete-Laplace, finite rounding and bit-recycling clients. -/

open Set ProbLang
open scoped ENNReal NNReal

namespace ExpansionDiscreteAudit

noncomputable section

section mathematics

open MeasureTheory Measure SampLib

example (F : ℤ → ℝ≥0∞) (ε : ℝ≥0∞) :
    DiscreteLaplace.signCredit 3 2 (by decide) (by decide) F ε 0 1 false =
      DiscreteLaplace.retryCredit 3 2 (by decide) (by decide) F ε := by
  simp [DiscreteLaplace.signCredit, DiscreteLaplace.magnitude]

example (F : ℤ → ℝ≥0∞) (ε : ℝ≥0∞) :
    DiscreteLaplace.signCredit 3 2 (by decide) (by decide) F ε 0 1 true = F 0 := by
  simp [DiscreteLaplace.signCredit, DiscreteLaplace.output, DiscreteLaplace.magnitude]

example (F : ℤ → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∑ r ∈ Finset.range 2, DiscreteLaplace.rankCredit 3 2 (by decide) (by decide) F ε r) / 2 ≤
      DiscreteLaplace.credit 3 2 (by decide) (by decide) F + ε :=
  DiscreteLaplace.expectation_preservation 3 2 (by decide) (by decide) F ε

example : BinaryRounding.round 20 2 = 16 := by decide
example : BinaryRounding.round 28 2 = 32 := by decide
example : BinaryRounding.round 24 2 = 24 := by decide
example : (List.range 8).map (FloatingMultiply.output 5 3 3) =
    [0, 0, 1, 2, 2, 3, 4, 4] := by decide
example : (List.range 8).map (FloatingMultiply.output 5 3 6) =
    [0, 0, 1, 1, 2, 3, 3, 4] := by decide

example : FloatingMultiply.law 5 3 3 {2} = (1 : ℝ≥0∞) / 4 := by
  rw [FloatingMultiply.law_singleton]
  have hc : ((Finset.range (2 ^ 3)).filter (fun word =>
      BinaryRounding.round (5 * word) 3 / 2 ^ 3 = 2)).card = 2 := by decide
  rw [hc]
  change (2 : ℝ≥0∞) / 8 = 1 / 4
  apply (ENNReal.div_eq_div_iff (by norm_num) (by finiteness)
    (by norm_num) (by finiteness)).2
  norm_num

example : FloatingMultiply.law 5 3 3 {3} = (1 : ℝ≥0∞) / 8 := by
  rw [FloatingMultiply.law_singleton]
  have hc : ((Finset.range (2 ^ 3)).filter (fun word =>
      BinaryRounding.round (5 * word) 3 / 2 ^ 3 = 3)).card = 1 := by decide
  rw [hc]
  norm_num

private theorem floating_cutoff_mass : FloatingMultiply.law 5 3 3 {5} = 0 := by
  rw [FloatingMultiply.law_singleton]
  have hc : ((Finset.range (2 ^ 3)).filter (fun word =>
      BinaryRounding.round (5 * word) 3 / 2 ^ 3 = 5)).card = 0 := by decide
  rw [hc]
  norm_num

example : (∫⁻ k, ({5} : Set ℕ).indicator (fun _ => ∞) k ∂FloatingMultiply.law 5 3 3) = 0 := by
  rw [lintegral_indicator_const (measurableSet_singleton _), floating_cutoff_mass, mul_zero]

example (F : ℕ → ℝ≥0∞) : (∫⁻ k, F k ∂FloatingMultiply.law 1 0 1) = F 0 := by
  rw [FloatingMultiply.expectation]
  norm_num [FloatingMultiply.output]

example (n b p : ℕ) : (∫⁻ _k, (∞ : ℝ≥0∞) ∂FloatingMultiply.law n b p) = ∞ := by simp

example : (∫⁻ k, (if k = 3 then ∞ else 0 : ℝ≥0∞) ∂UniformInt.law 3) = 0 := by
  rw [UniformInt.lintegral_law]
  norm_num

#print axioms SampLib.BinaryRounding.error_bound
#print axioms SampLib.BinaryRounding.tie_even
#print axioms SampLib.FloatingMultiply.law_singleton
#print axioms SampLib.DiscreteLaplace.expectation_preservation

end mathematics

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
private theorem frame {α : Type} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {E : CoPset} {e : Exp rT}
    {encode : α → Val rT} (h : IsDistSpec (GF := GF) E e μ encode)
    (F : α → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂μ) ∗ I -∗ tglWp E e
      (fun v : Val rT => iprop(∃ x : α, ⌜v = encode x⌝ ∗ ↯ (F x) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply (h.wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %x Hcredit
  iexists x
  iframe Hcredit HI
  itrivial

example (E : CoPset) (s t : ℕ) (hs : 0 < s) (ht : 0 < t)
    (F : ℤ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ z, F z ∂DiscreteLaplace.law s t hs ht) ∗ I -∗
      tglWp E pl(&Occil.DiscreteExtra.discreteLaplace #int (s : ℤ) #int (t : ℤ))
        (fun v : Val rT => iprop(∃ z : ℤ, ⌜v = Val.int z⌝ ∗ ↯ (F z) ∗ I)) :=
  frame (DiscreteLaplace.discreteLaplace_distSpec E s t hs ht) F I

example (E : CoPset) : IsDistSpec (GF := GF) E
    pl(&Occil.DiscreteExtra.discreteLaplace #2 #3)
    (DiscreteLaplace.law 2 3 (by decide) (by decide)) Val.int :=
  DiscreteLaplace.discreteLaplace_distSpec E 2 3 (by decide) (by decide)

example (E : CoPset) : IsDistSpec (GF := GF) E
    pl(&Occil.DiscreteExtra.discreteLaplace #3 #2)
    (DiscreteLaplace.law 3 2 (by decide) (by decide)) Val.int :=
  DiscreteLaplace.discreteLaplace_distSpec E 3 2 (by decide) (by decide)


example (E : CoPset) (n bits p : ℕ) (hn : 0 < n) (hb : n ≤ 2 ^ bits)
    (hp : 0 < p) (hbp : bits ≤ p) (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂FloatingMultiply.law n bits p) ∗ I -∗
      tglWp E pl(&Occil.WeightedVariants.floatingMultiply #int (n : ℤ)
        #int (bits : ℤ) #int (p : ℤ))
        (fun result : Val rT => iprop(∃ k : ℕ,
          ⌜result = Val.int (k : ℤ)⌝ ∗ ↯ (F k) ∗ I)) :=
  frame (FloatingMultiply.floatingMultiply_distSpec E n bits p hn hb hp hbp) F I

example (E : CoPset) : IsDistSpec (GF := GF) E
    pl(&Occil.WeightedVariants.floatingMultiply #1 #0 #1)
    (FloatingMultiply.law 1 0 1) (fun k : ℕ => Val.int (k : ℤ)) :=
  FloatingMultiply.floatingMultiply_distSpec E 1 0 1
    (by decide) (by decide) (by decide) (by decide)

omit [ProbLangDist.IsUniformInt rT] in
example (n : ℕ) :
    PureSteps (pl(&Occil.WeightedVariants.roundBinary #int (n : ℤ) #0) : Exp rT) pl(fail) :=
  RoundBinary.zero_precision_fails n

omit [ProbLangDist.IsUniformInt rT] in
private theorem pure_frame {E : CoPset} {e : Exp rT} {value : Val rT}
    (h : ⊢ tglWp E e (fun v => iprop(⌜v = value⌝))) (I : IProp GF) :
    ⊢ I -∗ tglWp E e (fun v => iprop(⌜v = value⌝ ∗ I)) := by
  iintro HI
  iapply tglWp_wand
  isplitl []
  · iapply h
  iintro %v %hv
  iframe HI
  itrivial

omit [ProbLangDist.IsUniformInt rT] in
example (E : CoPset) (value : ℕ) (I : IProp GF) :
    ⊢ I -∗ tglWp E pl(&Occil.WeightedVariants.bitLength #int (value : ℤ))
      (fun v => iprop(⌜v = Val.int (value.size : ℤ)⌝ ∗ I)) :=
  pure_frame (BitLength.twp_bitLength E value) I

omit [ProbLangDist.IsUniformInt rT] in
example (E : CoPset) (value p : ℕ) (hp : 0 < p) (I : IProp GF) :
    ⊢ I -∗ tglWp E pl(&Occil.WeightedVariants.roundBinary #int (value : ℤ) #int (p : ℤ))
      (fun v => iprop(⌜v = Val.int (BinaryRounding.round value p : ℤ)⌝ ∗ I)) :=
  pure_frame (RoundBinary.twp_roundBinary E value p hp) I

omit [ProbLangDist.IsUniformInt rT] in
example (E : CoPset) :
    ⊢ tglWp E pl(&Occil.WeightedVariants.bitLength #256)
      (fun v : Val rT => iprop(⌜v = Val.int 9⌝)) := by
  simpa only [show Nat.size 256 = 9 from by decide, Nat.cast_ofNat] using
    BitLength.twp_bitLength (rT := rT) (GF := GF) E 256

omit [ProbLangDist.IsUniformInt rT] in
example (E : CoPset) :
    ⊢ tglWp E pl(&Occil.WeightedVariants.roundBinary #28 #2)
      (fun v : Val rT => iprop(⌜v = Val.int 32⌝)) := by
  simpa only [show BinaryRounding.round 28 2 = 32 from by decide, Nat.cast_ofNat] using
    RoundBinary.twp_roundBinary (rT := rT) (GF := GF) E 28 2 (by decide)

example (E : CoPset) (n : ℕ) [NeZero n] (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ j, F j ∂UniformInt.law n) ∗ I -∗
      tglWp E pl(&Occil.fastDiceRoller #int (n : ℤ))
        (fun result : Val rT => iprop(∃ j : ℕ,
          ⌜result = Val.int (j : ℤ)⌝ ∗ ↯ (F j) ∗ I)) :=
  frame (FastDiceRoller.fastDiceRoller_distSpec E n) F I

omit [ProbLangDist.IsUniformInt rT] in
example (E : CoPset) (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ j, F j ∂UniformInt.law 1) ∗ I -∗
      tglWp E pl(&Occil.fastDiceRoller #1)
        (fun result : Val rT => iprop(∃ j : ℕ,
          ⌜result = Val.int (j : ℤ)⌝ ∗ ↯ (F j) ∗ I)) :=
  frame (FastDiceRoller.fastDiceRoller_one_distSpec E) F I

example (E : CoPset) : IsDistSpec (GF := GF) E
    pl(&Occil.fastDiceRoller #3) (UniformInt.law 3) (fun j : ℕ => Val.int (j : ℤ)) :=
  FastDiceRoller.fastDiceRoller_distSpec E 3

example (E : CoPset) : IsDistSpec (GF := GF) E
    pl(&Occil.fastDiceRoller #5) (UniformInt.law 5) (fun j : ℕ => Val.int (j : ℤ)) :=
  FastDiceRoller.fastDiceRoller_distSpec E 5

#print axioms SampLib.DiscreteLaplace.discreteLaplace_distSpec
#print axioms SampLib.FloatingMultiply.floatingMultiply_distSpec
#print axioms SampLib.BitLength.twp_bitLength
#print axioms SampLib.RoundBinary.twp_roundBinary
#print axioms SampLib.RoundBinary.zero_precision_fails
#print axioms SampLib.FastDiceRoller.fastDiceRoller_distSpec
#print axioms SampLib.FastDiceRoller.fastDiceRoller_one_distSpec

end

end ExpansionDiscreteAudit
