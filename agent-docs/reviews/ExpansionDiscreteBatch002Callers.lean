import SampLib.Weighted.UniformFormats
import SampLib.Discrete.NegativeHypergeometric
import SampLib.Discrete.Himanshu
import SampLib.Common.Laws.PoissonTree
import Metrology.Iris.LocalBI

/-! Independent clients, boundary laws, and infinite continuation credits. -/

open Set ProbLang
open scoped ENNReal

namespace ExpansionDiscreteAudit

noncomputable section

section mathematics

open MeasureTheory Measure SampLib

example : UniformInt.law 1 = dirac 0 := by
  simp [UniformInt.law, Measure.uniformOfFinset]

example (n : ℕ) [NeZero n] :
    (∫⁻ _k, (∞ : ℝ≥0∞) ∂UniformInt.law n) = ∞ := by simp

example (ones zeros : ℕ) (F : ℕ → ℝ≥0∞) :
    (∫⁻ k, F k ∂NegativeHypergeometric.law 0 ones zeros) = F 0 :=
  NegativeHypergeometric.expectation_zero ones zeros F

private theorem one_marked_no_failures (F : ℕ → ℝ≥0∞) :
    (∫⁻ k, F k ∂NegativeHypergeometric.law 1 1 0) = F 0 := by
  rw [NegativeHypergeometric.expectation 0 1 0 (by decide)]
  simp

example (F : ℕ → ℝ≥0∞) :
    (∫⁻ k, F k ∂NegativeHypergeometric.law 1 1 1) = (F 0 + F 1) / 2 := by
  rw [NegativeHypergeometric.expectation 0 1 1 (by decide)]
  rw [NegativeHypergeometric.expectation_zero,
    one_marked_no_failures (fun k => F (k + 1))]
  norm_num

example (r ones zeros : ℕ) :
    (∫⁻ _k, (∞ : ℝ≥0∞) ∂NegativeHypergeometric.law r ones zeros) = ∞ := by simp

example (n : ℕ) : Himanshu.law 1 n {0} = 1 := by
  have hb : IterateCoin.bias 1 n = 1 := by
    apply Subtype.ext
    simp [IterateCoin.bias]
  change ProbabilityTheory.geometricMeasure (IterateCoin.bias 1 n) {0} = 1
  have hone : (1 : unitInterval) ≠ 0 := by
    intro h
    have hh := congrArg Subtype.val h
    norm_num at hh
  rw [hb, ProbabilityTheory.geometricMeasure_singleton hone]
  norm_num

example (p : unitInterval) : Himanshu.law p 1 = Geometric.law p := by
  change ProbabilityTheory.geometricMeasure (IterateCoin.bias p 1) =
    ProbabilityTheory.geometricMeasure p
  congr 1
  apply Subtype.ext
  simp [IterateCoin.bias]

example (p : unitInterval) (n : ℕ) :
    (∫⁻ _k, (∞ : ℝ≥0∞) ∂Himanshu.law p n) = ∞ := by simp

private theorem two_div_six : (2 : ℝ≥0∞) / 6 = 1 / 3 := by
  apply (ENNReal.div_eq_div_iff (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)).2
  norm_num

example : PoissonTree.layer 2 ⟨0, 0, 0⟩ {0} = (1 : ℝ≥0∞) / 3 := by
  rw [PoissonTree.initial_layer_singleton]
  norm_num
  simpa only [one_div] using two_div_six

example : PoissonTree.layer 3 ⟨0, 0, 0⟩ {1} = (1 : ℝ≥0∞) / 3 := by
  rw [PoissonTree.initial_layer_singleton]
  norm_num
  simpa only [one_div] using two_div_six

example : PoissonTree.layer 4 ⟨0, 0, 0⟩ {0} = (1 : ℝ≥0∞) / 30 := by
  rw [PoissonTree.initial_layer_singleton]
  norm_num [show Even (4 : ℕ) from ⟨2, by norm_num⟩]
  have h : (4 : ℝ≥0∞) / 120 = 1 / 30 := by
    apply (ENNReal.div_eq_div_iff (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)).2
    norm_num
  simpa only [one_div] using h

example : PoissonTree.layer 3 ⟨0, 0, 0⟩ {0} = 0 := by
  rw [PoissonTree.initial_layer_singleton]
  norm_num [show ¬Even (3 : ℕ) by rintro ⟨k, hk⟩; omega]

example : PoissonTree.layer 3 ⟨0, 0, 0⟩ {4} = 0 := by
  rw [PoissonTree.initial_layer_singleton]
  norm_num

example : PoissonTree.law ⟨0, 0, 0⟩ Set.univ = 1 := by
  rw [PoissonTree.law_empty]
  simp

example : (∫⁻ _k, (∞ : ℝ≥0∞) ∂PoissonTree.law ⟨0, 0, 0⟩) = ∞ := by
  rw [PoissonTree.law_empty]
  simp

example : PoissonTree.credit ⟨1, 1, 0⟩ (fun _ => ∞) = ∞ := by
  rw [PoissonTree.initial_credit]
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


example (E : CoPset) (n : ℕ) [NeZero n] (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂UniformInt.law n) ∗ I -∗
      tglWp E pl(&Occil.Weighted.uniformRational #int (n : ℤ) #())
        (fun v : Val rT => iprop(∃ k : ℕ,
          ⌜v = Val.pair (Val.int (k : ℤ)) (Val.int (n : ℤ))⌝ ∗ ↯ (F k) ∗ I)) :=
  frame (UniformFormats.uniformRational_distSpec E n) F I

example (E : CoPset) (n : ℕ) [NeZero n] (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂UniformInt.law n) ∗ I -∗
      tglWp E pl(&Occil.Weighted.uniformFixed #int (n : ℤ) #())
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k) ∗ I)) :=
  frame (UniformFormats.uniformFixed_distSpec E n) F I

example (E : CoPset) (bits : ℕ) [NeZero (2 ^ bits)]
    (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂UniformInt.law (2 ^ bits)) ∗ I -∗
      tglWp E pl(&Occil.Weighted.uniformDyadic #int (bits : ℤ) #())
        (fun v : Val rT => iprop(∃ k : ℕ,
          ⌜v = Val.pair (Val.int (k : ℤ)) (Val.int ((2 ^ bits : ℕ) : ℤ))⌝ ∗ ↯ (F k) ∗ I)) :=
  frame (UniformFormats.uniformDyadic_distSpec E bits) F I

example (E : CoPset) (r ones zeros : ℕ) (h : r ≤ ones)
    (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂NegativeHypergeometric.law r ones zeros) ∗ I -∗
      tglWp E pl(&Occil.DiscreteExtra.negativeHypergeometric #int (r : ℤ)
        #int (ones : ℤ) #int (zeros : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k) ∗ I)) :=
  frame (NegativeHypergeometric.negativeHypergeometric_distSpec E r ones zeros h) F I

omit [ProbLangDist.IsUniformInt rT] in
example (E : CoPset) (p : unitInterval) (hp : 0 < (p : ℝ)) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (n : ℕ) (hn : 0 < n) (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂Himanshu.law p n) ∗ I -∗
      tglWp E pl(&Occil.DiscreteExtra.himanshu &coin.fst #int (n : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k) ∗ I)) :=
  frame (Himanshu.himanshu_distSpec E p hp coin hcoin n hn) F I

omit [ProbLangDist.IsUniformInt rT] in
example {α : Type} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] (E : CoPset) (e : Exp rT)
    (encode : α → Val rT) (h : IsDistSpec (GF := GF) E e μ encode)
    (P : α → Prop) (hP : MeasurableSet {x | P x}) (hs : ∀ᵐ x ∂μ, P x)
    (F : α → ℝ≥0∞) (hF : Measurable F) (I : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂μ) ∗ I -∗ tglWp E e
      (fun v : Val rT => iprop(∃ x : α,
        ⌜P x ∧ v = encode x⌝ ∗ ↯ (F x) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply (h.wp_supported P hP hs F hF _) $$ Hcredit
  iintro %x %hx Hcredit
  iexists x
  iframe Hcredit HI
  ipureintro
  exact ⟨hx, rfl⟩

#print axioms UniformFormats.uniformRational_distSpec
#print axioms UniformFormats.uniformFixed_distSpec
#print axioms UniformFormats.uniformDyadic_distSpec
#print axioms WeightedIntegerPower.twp_integerPower
#print axioms NegativeHypergeometric.negativeHypergeometric_distSpec
#print axioms NegativeHypergeometric.expectation
#print axioms IsDistSpec.wp_supported
#print axioms Himanshu.himanshu_distSpec
#print axioms PoissonTree.law_empty
#print axioms PoissonTree.credit_recurrence
#print axioms PoissonTree.initial_credit

end

end ExpansionDiscreteAudit
