import SampLib.Discrete.BinomialBinary
import SampLib.Discrete.Cub
import SampLib.Weighted.FlatChoice
import SampLib.Weighted.LemireUniform
import SampLib.Discrete.Support.IntegerChoose
import Metrology.Iris.LocalBI

/-! Independent binary-binomial, ordinal, table and multiply-high clients. -/

open Set ProbLang
open scoped ENNReal NNReal

namespace ExpansionDiscreteAudit

noncomputable section

section mathematics

open MeasureTheory Measure SampLib

example (n b : ℕ) : BinomialBinary.law n 0 b = dirac 0 := by
  simp [BinomialBinary.law]

example (n b : ℕ) (hb : 0 < b) : BinomialBinary.law n b b = dirac n := by
  simp [BinomialBinary.law, BinomialBinary.bias_full b hb]

example (a b : ℕ) : BinomialBinary.law 0 a b = dirac 0 := rfl

example : (BinomialBinary.bias 1 3 : ℝ) = 1 / 3 := by
  norm_num [BinomialBinary.bias, Urn.bias, RationalCoin.bias]

example (F : ℕ → ℝ≥0∞) :
    (∫⁻ k, F k ∂BinomialBinary.law 2 1 2) = (F 0 + F 1 + F 1 + F 2) / 4 := by
  have h : BinomialBinary.bias 1 2 = VonNeumann.fairBias := by
    apply Subtype.ext
    norm_num [BinomialBinary.bias, Urn.bias, RationalCoin.bias, VonNeumann.fairBias]
  rw [BinomialBinary.law, h, ← BinomialHalfBits.expectation]
  have h1 : BinaryDigits.weight 1 = 1 := by simpa using BinaryDigits.weight_odd 0
  have h2 : BinaryDigits.weight 2 = 1 := by simpa [h1] using BinaryDigits.weight_even 1
  have h3 : BinaryDigits.weight 3 = 2 := by simpa [h1] using BinaryDigits.weight_odd 1
  norm_num [UniformInt.lintegral_law, Finset.sum_range_succ, h1, h2, h3]

example (n a b : ℕ) : (∫⁻ _k, (∞ : ℝ≥0∞) ∂BinomialBinary.law n a b) = ∞ := by
  simp

example : BinomialBinary.law 1 1 3 {1} = (1 : ℝ≥0∞) / 3 := by
  rw [Binomial.law_singleton]
  norm_num [RealCoin.pmf, BinomialBinary.bias_coe 1 3 (by decide) (by decide),
    ENNReal.ofReal_div_of_pos]

example : (∫⁻ k, (k : ℝ≥0∞) ∂BinomialBinary.law 3 1 3) = 1 := by
  rw [Binomial.mean]
  norm_num [BinomialBinary.bias_coe 1 3 (by decide) (by decide),
    ENNReal.ofReal_div_of_pos]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

example : Cub.law 3 1 0 = Measure.dirac 3 := by
  simp [Cub.law, Mixture.law, RealCoin.pmf,
    Measure.map_dirac' (measurable_of_countable _)]

example : Cub.law 3 1 1 = Measure.dirac 1 := by
  simp [Cub.law, Mixture.law, RealCoin.pmf,
    Measure.map_dirac' (measurable_of_countable _)]

example (ξ : unitInterval) : Cub.law 3 0 ξ = (UniformInt.law 3).map Nat.succ := by
  simp [Cub.law, Mixture.law, RealCoin.pmf]

example (m : ℕ) (p ξ : unitInterval) : (∫⁻ _k, (∞ : ℝ≥0∞) ∂Cub.law m p ξ) = ∞ := by
  simp

example : FlatChoice.table [0, 2, 0] 0 = [1, 1] := by decide
example : FlatChoice.table [1, 0, 2] 0 = [0, 2, 2] := by decide

example : WeightedChoice.law [0, 2, 0] {1} = 1 := by
  norm_num [WeightedChoice.law_singleton]
  exact ENNReal.div_self (by norm_num) (by norm_num)

example : (∫⁻ i, (if i = 1 then 0 else ∞ : ℝ≥0∞)
    ∂WeightedChoice.law [0, 2, 0]) = 0 := by
  simp [WeightedChoice.lintegral_law, WeightedChoice.weightedSum]

example : FlatChoice.table [3] 0 = [0, 0, 0] := by decide

example : MultiplyHigh.accepted 4 8 = Finset.range 8 := by decide

example : MultiplyHigh.accepted 5 8 = {1, 3, 4, 6, 7} := by decide

example : (MultiplyHigh.accepted 5 8).image (fun r => 5 * r / 8) = Finset.range 5 := by
  decide

example (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    LemireUniform.kernel 5 8 F ε 0 = (∫⁻ k, F k ∂UniformInt.law 5) + 2 * ε := by
  norm_num [LemireUniform.kernel]

example (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) : LemireUniform.kernel 5 8 F ε 7 = F 4 := by
  norm_num [LemireUniform.kernel]

example (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∫⁻ r, LemireUniform.kernel 5 8 F ε r ∂UniformInt.law 8) =
      (3 * ((∫⁻ k, F k ∂UniformInt.law 5) + 2 * ε) +
        F 0 + F 1 + F 2 + F 3 + F 4) / 8 := by
  norm_num [UniformInt.lintegral_law, Finset.sum_range_succ, LemireUniform.kernel]
  simp only [ENNReal.div_eq_inv_mul]
  ring

example (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∫⁻ r, LemireUniform.kernel 1 1 F ε r ∂UniformInt.law 1) = F 0 := by
  norm_num [UniformInt.lintegral_law, Finset.sum_range_succ, LemireUniform.kernel]

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


example (E : CoPset) (n a b : ℕ) (hb : 0 < b) (ha : a ≤ b)
    (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂BinomialBinary.law n a b) ∗ I -∗
      tglWp E pl(&Occil.DiscreteExtra.binomialBinary
        #int (n : ℤ) #int (a : ℤ) #int (b : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k) ∗ I)) :=
  frame (BinomialBinary.binomialBinary_distSpec E n a b hb ha) F I

#print axioms BinomialBinary.binomialBinary_distSpec
#print axioms BinomialBinary.expectation
#print axioms BinomialBinary.expectation_preservation
#print axioms BinomialBinary.remaining_mean

example (E : CoPset) (m a b c d : ℕ) (hm : 3 ≤ m) (hb : 0 < b)
    (ha : a ≤ b) (hd : 0 < d) (hc : c ≤ d) (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂Cub.law m (BinomialBinary.bias a b) (BinomialBinary.bias c d)) ∗ I -∗
      tglWp E pl(&Occil.DiscreteExtra.cub #int (m : ℤ) #int (a : ℤ)
        #int (b : ℤ) #int (c : ℤ) #int (d : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k) ∗ I)) :=
  frame (Cub.cub_distSpec E m a b c d hm hb ha hd hc) F I

example (E : CoPset) (ws : List ℕ) [NeZero ws.sum]
    (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law ws) ∗ I -∗
      tglWp E pl(&Occil.WeightedVariants.flatChoice
        &(listVal (fun n : ℕ => Val.int n) ws).fst #())
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int (i : ℤ)⌝ ∗ ↯ (F i) ∗ I)) :=
  frame (FlatChoice.flatChoice_distSpec E ws) F I

omit [ProbLangDist.IsUniformInt rT] in
example (E : CoPset) (n k : ℕ) (I : IProp GF) :
    ⊢ I -∗ tglWp E pl(&Occil.DiscreteExtra.choose #int (n : ℤ) #int (k : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (n.choose k : ℤ)⌝ ∗ I)) := by
  iintro HI
  iapply tglWp_wand
  isplitl []
  · iapply twp_integerChoose E n k
  iintro %v %hv
  iframe HI
  itrivial

omit [ProbLangDist.IsUniformInt rT] in
example (E : CoPset) :
    ⊢ tglWp E pl(&Occil.DiscreteExtra.choose #10 #3)
      (fun v : Val rT => iprop(⌜v = Val.int 120⌝)) := by
  have hc : Nat.choose 10 3 = 120 := by decide
  simpa only [hc, Nat.cast_ofNat] using twp_integerChoose (rT := rT) (GF := GF) E 10 3

omit [ProbLangDist.IsUniformInt rT] in
example (E : CoPset) :
    ⊢ tglWp E pl(&Occil.DiscreteExtra.choose #0 #0)
      (fun v : Val rT => iprop(⌜v = Val.int 1⌝)) := by
  simpa using twp_integerChoose (rT := rT) (GF := GF) E 0 0

omit [ProbLangDist.IsUniformInt rT] in
example (E : CoPset) :
    ⊢ tglWp E pl(&Occil.DiscreteExtra.choose #2 #3)
      (fun v : Val rT => iprop(⌜v = Val.int 0⌝)) := by
  simpa using twp_integerChoose (rT := rT) (GF := GF) E 2 3

#print axioms Cub.cub_distSpec
#print axioms Cub.expectation
#print axioms FlatChoice.flatChoice_distSpec
#print axioms FlatChoice.lookup
#print axioms twp_integerChoose

omit [ProbLangDist.IsUniformInt rT] in
example (E : CoPset) (n : ℕ) :
    ⊢ tglWp E pl(&Occil.DiscreteExtra.choose #int (n : ℤ) #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int 1⌝)) := by
  simpa using twp_integerChoose (rT := rT) (GF := GF) E n n

omit [ProbLangDist.IsUniformInt rT] in
example (E : CoPset) (n : ℕ) :
    ⊢ tglWp E pl(&Occil.DiscreteExtra.choose #int (n : ℤ) #0)
      (fun v : Val rT => iprop(⌜v = Val.int 1⌝)) := by
  simpa using twp_integerChoose (rT := rT) (GF := GF) E n 0

example (E : CoPset) (n bits : ℕ) [NeZero n] (hnw : n ≤ 2 ^ bits)
    (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂UniformInt.law n) ∗ I -∗
      tglWp E pl(&Occil.WeightedVariants.lemireUniform #int (n : ℤ) #int (bits : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k) ∗ I)) :=
  frame (LemireUniform.lemireUniform_distSpec E n bits hnw) F I

#print axioms LemireUniform.lemireUniform_distSpec
#print axioms LemireUniform.expectation
#print axioms MultiplyHigh.fibre
#print axioms MultiplyHigh.sum_accepted

end

end ExpansionDiscreteAudit
