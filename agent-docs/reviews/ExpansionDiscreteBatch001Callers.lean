import SampLib.Samplers.BetaBinomial
import SampLib.Samplers.RandomBits
import SampLib.Samplers.SymmetricGeometric
import Metrology.Iris.LocalBI

/-! Independent clients, boundary laws, and infinite continuation credits. -/

open Set ProbLang
open scoped ENNReal

namespace ExpansionDiscreteAudit

noncomputable section

section mathematics

open MeasureTheory Measure SampLib

example (a b c d : ℕ) : BetaBinomial.law 0 a b c d = dirac 0 := by
  simp [BetaBinomial.law, PolyaEggenberger.law, PolyaEggenberger.wordLaw,
    Measure.map_dirac' (measurable_of_countable _)]

example (n a b c d : ℕ) :
    (∫⁻ _k, (∞ : ℝ≥0∞) ∂BetaBinomial.law n a b c d) = ∞ := by simp

example : BetaBinomial.law 1 2 3 5 7 {1} = (14 : ℝ≥0∞) / 29 := by
  norm_num [BetaBinomial.law, PolyaEggenberger.law, PolyaEggenberger.wordLaw,
    Urn.bias, RealCoin.pmf, RationalCoin.bias, Measure.map_add, Measure.map_smul,
    Measure.map_dirac' (measurable_of_countable _)]
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  norm_num
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 29)]
  norm_num

example : UniformInt.law (2 ^ 0) = dirac 0 := by
  simp [UniformInt.law, Measure.uniformOfFinset]

example (n : ℕ) [NeZero (2 ^ n)] :
    (∫⁻ _k, (∞ : ℝ≥0∞) ∂UniformInt.law (2 ^ n)) = ∞ := by simp

example (p : unitInterval) (hp : 0 < (p : ℝ)) (n : ℕ) :
    SymmetricGeometric.law p {-1 - (n : ℤ)} =
      SymmetricGeometric.law p {((n + 1 : ℕ) : ℤ)} := by
  rw [SymmetricGeometric.neg_mass p hp, SymmetricGeometric.nonneg_mass p hp]

example : SymmetricGeometric.law 1 = dirac 0 := by
  apply Measure.ext_of_singleton
  intro z
  cases z with
  | ofNat n =>
    change SymmetricGeometric.law 1 {(n : ℤ)} = (dirac 0) {(n : ℤ)}
    rw [SymmetricGeometric.nonneg_mass 1 (by norm_num) n]
    cases n with
    | zero => norm_num [Pi.single_apply]
    | succ n =>
      norm_num [Pi.single_apply]
      omega
  | negSucc n =>
    have hz : Int.negSucc n = -1 - (n : ℤ) := by omega
    rw [hz, SymmetricGeometric.neg_mass 1 (by norm_num)]
    simp [show -1 - (n : ℤ) ≠ 0 by omega]

example (p : unitInterval) :
    (∫⁻ _z, (∞ : ℝ≥0∞) ∂SymmetricGeometric.law p) = ∞ := by simp

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

example (E : CoPset) (n a b c d : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂BetaBinomial.law n a b c d) ∗ I -∗
      tglWp E pl(&Occil.DiscreteExtra.betaBinomial #int (n : ℤ)
        #int (a : ℤ) #int (b : ℤ) #int (c : ℤ) #int (d : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k) ∗ I)) :=
  frame (BetaBinomial.betaBinomial_distSpec E n a b c d ha hb hc hd) F I

example (E : CoPset) (n : ℕ) [NeZero (2 ^ n)] (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂UniformInt.law (2 ^ n)) ∗ I -∗
      tglWp E pl(&Occil.Weighted.randomBits #int (n : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k) ∗ I)) := by
  exact frame (RandomBits.randomBits_distSpec E n) F I

example (E : CoPset) (p : unitInterval) (hp : 0 < (p : ℝ)) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : ℤ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ z, F z ∂SymmetricGeometric.law p) ∗ I -∗
      tglWp E pl(&Occil.DiscreteExtra.symmetricGeometric &coin.fst #())
        (fun v : Val rT => iprop(∃ z : ℤ, ⌜v = Val.int z⌝ ∗ ↯ (F z) ∗ I)) :=
  frame (SymmetricGeometric.symmetricGeometric_distSpec E p hp coin hcoin) F I

omit [ProbLangDist.IsUniformInt rT] in
example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law (unitInterval.symm p)) ∗ I -∗
      tglWp E pl(&(CoinComplement.callback coin).fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) :=
  frame (CoinComplement.distSpec E p coin hcoin) F I

#print axioms BetaBinomial.betaBinomial_distSpec
#print axioms RandomBits.randomBits_distSpec
#print axioms RandomBits.expectation
#print axioms SymmetricGeometric.symmetricGeometric_distSpec
#print axioms SymmetricGeometric.nonneg_mass
#print axioms SymmetricGeometric.neg_mass
#print axioms CoinComplement.distSpec

end

end ExpansionDiscreteAudit
