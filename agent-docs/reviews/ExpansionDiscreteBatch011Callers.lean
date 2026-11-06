import SampLib.Uniform.UniformFromModulus
import SampLib.Discrete.NegativeMultinomial
import SampLib.Discrete.WalleniusHypergeometric
import Metrology.Iris.LocalBI

/-! Independent modulus-conversion and negative-multinomial clients. -/

open Set ProbLang
open scoped ENNReal NNReal

namespace ExpansionDiscreteAudit

noncomputable section

section mathematics

open MeasureTheory Measure SampLib

example : ModulusReduction.limit 5 2 = 4 := by decide
example : ModulusReduction.limit 6 2 = 4 := by decide
example : ModulusReduction.width 2 7 = 4 := by decide
example : ModulusReduction.width 2 4 = 2 := by decide
example : ModulusReduction.width 3 8 = 3 := by decide

example (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    ModulusReduction.smallKernel 5 2 F ε 0 = F 0 ∧
    ModulusReduction.smallKernel 5 2 F ε 2 = F 0 ∧
    ModulusReduction.smallKernel 5 2 F ε 3 = F 1 ∧
    ModulusReduction.smallKernel 5 2 F ε 4 =
      (∫⁻ k, F k ∂UniformInt.law 2) + 2 * ε := by
  norm_num [ModulusReduction.smallKernel, ModulusReduction.limit]

example (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ r, ModulusReduction.smallKernel 5 2 F ε r ∂UniformInt.law 5 ≤
      (∫⁻ k, F k ∂UniformInt.law 2) + ε :=
  ModulusReduction.small_expectation 5 2 (by decide) (by decide) F ε

example (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ high, (∫⁻ low, UniformRejection.kernel 7 F ε (4 * high + low)
      ∂UniformInt.law 4) ∂UniformInt.law 2 ≤
      (∫⁻ k, F k ∂UniformInt.law 7) + ε :=
  ModulusReduction.large_expectation 2 7 (by decide) (by decide) F ε

example (F : ℕ → ℝ≥0∞) :
    ∫⁻ high, (∫⁻ low, F (3 * high + low) ∂UniformInt.law 3)
      ∂UniformInt.law 3 = ∫⁻ k, F k ∂UniformInt.law 9 :=
  UniformRectangles.expectation 3 3 F

example : (∫⁻ k, (if k = 0 then 7 else ∞ : ℝ≥0∞) ∂UniformInt.law 1) = 7 := by
  rw [UniformInt.lintegral_law]
  norm_num

example (r s : ℕ) (ws : List ℕ) :
    (∫⁻ _cs, (∞ : ℝ≥0∞) ∂NegativeMultinomial.law r s ws) = ∞ := by simp

example (r s : ℕ) : NegativeMultinomial.law r s [] = dirac [] := by simp
example (s : ℕ) : NegativeMultinomial.law 0 s [0, 0] = dirac [0, 0] := by simp
example (r : ℕ) : NegativeMultinomial.law r 3 [0, 0] = dirac [0, 0] :=
  NegativeMultinomial.law_zero_weights r 3 [0, 0] (by decide) rfl

private theorem multinomial_nil : ([] : List ℕ).multinomial = 1 := rfl

private theorem negativeBinomial_one (p : unitInterval) :
    NegativeBinomial.law p 1 = Geometric.law p := by
  apply Measure.ext_of_lintegral
  intro F _
  change NegativeBinomial.credit p 1 F = _
  rw [NegativeBinomial.credit_succ]
  simp [NegativeBinomial.credit, NegativeBinomial.law, NegativeBinomial.firstCredit,
    Geometric.credit]

example : NegativeMultinomial.law 1 2 [1, 1] {[1, 0]} = (1 : ℝ≥0∞) / 8 := by
  rw [NegativeMultinomial.law_singleton 1 2 [1, 1] [1, 0] (by decide)]
  norm_num only [List.sum_cons, List.sum_nil, add_zero, zero_add]
  rw [negativeBinomial_one, Geometric.law,
    ProbabilityTheory.geometricMeasure_singleton (by
      intro h
      have := congrArg (fun p : unitInterval => (p : ℝ)) h
      norm_num [Urn.bias, RationalCoin.bias] at this),
    Multinomial.law_singleton 1 [1, 1] [1, 0] (by decide)]
  norm_num [Urn.bias, RationalCoin.bias, Multinomial.pmf, Multinomial.weightProduct,
    List.multinomial_cons, multinomial_nil]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

example (r : ℕ) :
    (∫⁻ cs, (if cs = [0, 0] then 4 else ∞ : ℝ≥0∞)
      ∂NegativeMultinomial.law r 3 [0, 0]) = 4 := by
  rw [NegativeMultinomial.law_zero_weights r 3 [0, 0] (by decide) rfl]
  simp

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

example (E : CoPset) (m n : ℕ) (hm : 2 ≤ m) [NeZero n]
    (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂UniformInt.law n) ∗ I -∗
      tglWp E pl(&Occil.uniformFromModulus #int (m : ℤ) #int (n : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k) ∗ I)) :=
  frame (UniformFromModulus.uniformFromModulus_distSpec E m n hm) F I

example (E : CoPset) (r s : ℕ) (ws : List ℕ) (hs : 0 < s)
    (F : List ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ cs, F cs ∂NegativeMultinomial.law r s ws) ∗ I -∗
      tglWp E pl(&Occil.DiscreteExtra.negativeMultinomial #int (r : ℤ)
        #int (s : ℤ) &(NatCounters.encode ws).fst)
        (fun v : Val rT => iprop(∃ cs : List ℕ,
          ⌜v = NatCounters.encode cs⌝ ∗ ↯ (F cs) ∗ I)) :=
  frame (NegativeMultinomial.negativeMultinomial_distSpec E r s ws hs) F I

example (E : CoPset) : IsDistSpec (GF := GF) E
    pl(&Occil.uniformFromModulus #2 #7) (UniformInt.law 7)
    (fun k : ℕ => Val.int (k : ℤ)) :=
  UniformFromModulus.uniformFromModulus_distSpec E 2 7 (by decide)

example (E : CoPset) : IsDistSpec (GF := GF) E
    pl(&Occil.uniformFromModulus #3 #3) (UniformInt.law 3)
    (fun k : ℕ => Val.int (k : ℤ)) :=
  UniformFromModulus.uniformFromModulus_distSpec E 3 3 (by decide)

example (E : CoPset) : IsDistSpec (GF := GF) E
    pl(&Occil.uniformFromModulus #2 #1) (UniformInt.law 1)
    (fun k : ℕ => Val.int (k : ℤ)) :=
  UniformFromModulus.uniformFromModulus_distSpec E 2 1 (by decide)

#print axioms SampLib.UniformFromModulus.uniformFromModulus_distSpec
#print axioms SampLib.ModulusReduction.small_expectation
#print axioms SampLib.ModulusReduction.large_expectation
#print axioms SampLib.UniformRectangles.expectation
#print axioms SampLib.NegativeMultinomial.negativeMultinomial_distSpec
#print axioms SampLib.NegativeMultinomial.conservation
#print axioms SampLib.NegativeMultinomial.law_singleton
#print axioms SampLib.Multinomial.trial_expectation

section walleniusMathematics

open MeasureTheory Measure SampLib

example : Wallenius.twoColorLaw 2 2 1 3 1 {2} = (9 : ℝ≥0∞) / 14 := by
  rw [Wallenius.twoColor_word, Measure.map_apply (measurable_of_countable _)
    (measurableSet_singleton _)]
  change Wallenius.wordLaw [2, 1] [3, 1] 2 {word | word.count 0 = 2} = _
  have hs := Wallenius.word_support [2, 1] [3, 1] 2 (by decide) rfl (by simp)
  have he : {word : List ℕ | word.count 0 = 2} =ᵐ[Wallenius.wordLaw [2, 1] [3, 1] 2]
      ({[0, 0]} : Set (List ℕ)) := by
    filter_upwards [hs] with word hw
    apply propext
    change word.count 0 = 2 ↔ word = [0, 0]
    constructor
    · intro hc
      have hr := List.replicate_count_eq_of_count_eq_length (hc.trans hw.1.symm)
      simpa [hc] using hr.symm
    · rintro rfl
      decide
  rw [measure_congr he]
  change Wallenius.wordLaw [2, 1] [3, 1] ([0, 0] : List ℕ).length {[0, 0]} = _
  rw [Wallenius.word_likelihood]
  norm_num [Wallenius.likelihood, Wallenius.ratio, Wallenius.weights, Wallenius.decrement]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

example : Wallenius.wordLaw [2, 1] [3, 1] 2 {[0, 1]} = (3 : ℝ≥0∞) / 14 := by
  change Wallenius.wordLaw [2, 1] [3, 1] ([0, 1] : List ℕ).length {[0, 1]} = _
  rw [Wallenius.word_likelihood]
  norm_num [Wallenius.likelihood, Wallenius.ratio, Wallenius.weights, Wallenius.decrement]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

example : Wallenius.wordLaw [2, 1] [3, 1] 2 {[1, 0]} = (1 : ℝ≥0∞) / 7 := by
  change Wallenius.wordLaw [2, 1] [3, 1] ([1, 0] : List ℕ).length {[1, 0]} = _
  rw [Wallenius.word_likelihood]
  norm_num [Wallenius.likelihood, Wallenius.ratio, Wallenius.weights, Wallenius.decrement]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

example (n ones zeros a b : ℕ) :
    (∫⁻ _k, (∞ : ℝ≥0∞) ∂Wallenius.twoColorLaw n ones zeros a b) = ∞ := by simp

example (F : ℕ → ℝ≥0∞) :
    (∫⁻ k, F k ∂Wallenius.twoColorLaw 0 0 0 3 2) = F 0 := by simp

example (F : List ℕ → ℝ≥0∞) :
    Wallenius.credit 0 [0, 2] [3, 2] [8, 5] F = F [8, 5] :=
  Wallenius.credit_zero [0, 2] [3, 2] [8, 5] rfl F

example : Wallenius.wordLaw [2, 1] [3, 1] 2 {[1, 1]} = 0 := by
  change Wallenius.wordLaw [2, 1] [3, 1] ([1, 1] : List ℕ).length {[1, 1]} = _
  rw [Wallenius.word_likelihood]
  norm_num [Wallenius.likelihood, Wallenius.ratio, Wallenius.weights, Wallenius.decrement]

end walleniusMathematics

example (E : CoPset) (n ones zeros a b : ℕ) (hn : n ≤ ones + zeros)
    (ha : 0 < a) (hb : 0 < b) (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂WalleniusHypergeometric.law n ones zeros a b) ∗ I -∗
      tglWp E pl(&Occil.DiscreteExtra.walleniusHypergeometric #int (n : ℤ)
        #int (ones : ℤ) #int (zeros : ℤ) #int (a : ℤ) #int (b : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k) ∗ I)) :=
  frame (WalleniusHypergeometric.walleniusHypergeometric_distSpec E n ones zeros a b hn ha hb) F I

omit [ProbLangDist.IsUniformInt rT] in
example (E : CoPset) : IsDistSpec (GF := GF) E
    pl(&Occil.DiscreteExtra.walleniusHypergeometric #0 #0 #0 #3 #2)
    (MeasureTheory.Measure.dirac (0 : ℕ)) (fun k : ℕ => Val.int (k : ℤ)) :=
  WalleniusHypergeometric.walleniusHypergeometric_zero_distSpec E 0 0 3 2 (by decide) (by decide)

example (E : CoPset) : IsDistSpec (GF := GF) E
    pl(&Occil.DiscreteExtra.walleniusHypergeometric #2 #0 #2 #3 #1)
    (WalleniusHypergeometric.law 2 0 2 3 1) (fun k : ℕ => Val.int (k : ℤ)) :=
  WalleniusHypergeometric.walleniusHypergeometric_distSpec E 2 0 2 3 1
    (by decide) (by decide) (by decide)

example (E : CoPset) : IsDistSpec (GF := GF) E
    pl(&Occil.DiscreteExtra.walleniusHypergeometric #2 #2 #0 #3 #1)
    (WalleniusHypergeometric.law 2 2 0 3 1) (fun k : ℕ => Val.int (k : ℤ)) :=
  WalleniusHypergeometric.walleniusHypergeometric_distSpec E 2 2 0 3 1
    (by decide) (by decide) (by decide)

#print axioms SampLib.WalleniusHypergeometric.walleniusHypergeometric_distSpec
#print axioms SampLib.WalleniusHypergeometric.walleniusHypergeometric_zero_distSpec
#print axioms SampLib.Wallenius.wordLaw_singleton
#print axioms SampLib.Wallenius.likelihood_product
#print axioms SampLib.Wallenius.twoColor_expectation

end

end ExpansionDiscreteAudit
