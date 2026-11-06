import SampLib.IntegerPower
import SampLib.Distributions.BinaryDigits
import SampLib.Samplers.Binomial
import SampLib.Samplers.UniformInt
import SampLib.Samplers.FairCoin
import Samplers.Discrete.Binomial

/-! # Counting fair bits in a uniform word

Even and odd words have the same high-bit distribution. Splitting the word
sum into those pairs is precisely the fair-binomial expectation recurrence.
-/

open Set ProbLang Finset
open scoped ENNReal

namespace SampLib.BinomialHalfBits

noncomputable section

abbrev law (n : ℕ) := Binomial.law VonNeumann.fairBias n

section mathematics

open MeasureTheory BinaryDigits

/-- Uniform binary words have the same digit-sum law as independent fair flips. -/
theorem expectation (n : ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ word, F (weight word) ∂UniformInt.law (2 ^ n) = ∫⁻ k, F k ∂law n := by
  induction n generalizing F with
  | zero => simp [UniformInt.lintegral_law, law, Binomial.law]
  | succ n ih =>
    rw [UniformInt.lintegral_law, pow_succ,
      show 2 ^ n * 2 = 2 * 2 ^ n by omega, sum_pairs]
    simp only [weight_even, weight_odd, sum_add_distrib]
    rw [← Binomial.expectation]
    simp only [RealCoin.lintegral_law, RealCoin.credit,
      Binomial.continuation, Bool.false_eq_true, ite_true, ite_false]
    rw [← ih (fun k => F (k + 1)), ← ih F]
    norm_num [RealCoin.pmf, VonNeumann.fairBias]
    simp only [UniformInt.lintegral_law, ENNReal.div_eq_inv_mul]
    rw [ENNReal.mul_inv (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0))
      (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ ∞))]
    rw [show ENNReal.ofReal (1 / 2 : ℝ) = (2 : ℝ≥0∞)⁻¹ from by
      norm_num [ENNReal.ofReal_div_of_pos]]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    ring

end mathematics

private def countLoop {rT : Type _} : Exp rT := pl%
  rec go bits total := if bits = #0 then total else
    go (bits / #2) (total + bits % #2)

private theorem word_test {rT : Type _} [BEq rT] (bits : ℕ) (hb : bits ≠ 0) :
    ((BaseLit.int (bits : ℤ) : BaseLit rT) == .int 0) = false := by
  change ((bits : ℤ) == 0) = false
  simp [hb]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem count_step (total bits : ℕ) (hb : 0 < bits) :
    total + bits % 2 + BinaryDigits.weight (bits / 2) = total + BinaryDigits.weight bits := by
  rw [BinaryDigits.weight_step bits hb]
  omega

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_countLoop (E : CoPset) (bits total : ℕ) :
    ⊢ tglWp E pl(&countLoop #int (bits : ℤ) #int (total : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int ((total + BinaryDigits.weight bits : ℕ) : ℤ)⌝)) := by
  induction bits using Nat.strong_induction_on generalizing total with
  | h bits ih =>
    by_cases hb : bits = 0
    · subst bits
      twp_pures
      twp_value
      imodintro
      ipureintro
      simp
    · have hpos : 0 < bits := Nat.pos_of_ne_zero hb
      have hdiv : bits / 2 < bits := Nat.div_lt_self hpos (by decide)
      iterate 4 twp_pure
      rw [word_test bits hb]
      iterate 4 twp_pure
      have h := ih (bits / 2) hdiv (total + bits % 2)
      rw [count_step total bits hpos] at h
      twp_bind pl(&countLoop #int ((bits / 2 : ℕ) : ℤ)
        #int ((total + bits % 2 : ℕ) : ℤ))
      iapply (tglWp_mono fun _ => tglWp_value)
      iapply h

/-- One uniform word supplies every independent fair bit at once. -/
theorem twp_binomialHalfBits (E : CoPset) (n : ℕ) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ k, F k ∂law n) -∗
      tglWp E pl(&Occil.DiscreteExtra.binomialHalfBits #int (n : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k))) := by
  iintro Hcredit
  iterate 3 twp_pure
  twp_bind pl(&Occil.DiscreteExtra.integerPower #2 #int (n : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply twp_integerPower E 2 n
  iintro %v %hv
  subst v
  rw [show (2 : ℤ) ^ n = ((2 ^ n : ℕ) : ℤ) by norm_cast]
  twp_bind pl(&Occil.uniformInt #int ((2 ^ n : ℕ) : ℤ))
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply (UniformInt.twp_uniformInt E (2 ^ n) (by positivity)
      (fun word => F (BinaryDigits.weight word)))
    isimp only [← expectation n F, UniformInt.lintegral_law] at Hcredit
    iexact Hcredit
  iintro %v ⟨%word, %hv, %hword, Hcredit⟩
  subst v
  iterate 2 twp_pure
  twp_bind pl(&countLoop #int (word : ℤ) #0)
  iapply tglWp_wand
  isplitl []
  · iapply twp_countLoop E word 0
  iintro %v %hv
  iapply (tglWp_value (v := v))
  iexists BinaryDigits.weight word
  iframe Hcredit
  ipureintro
  simpa only [Nat.zero_add] using hv

/-- Typed fair-binomial law, including the empty zero-bit word. -/
theorem binomialHalfBits_distSpec (E : CoPset) (n : ℕ) :
    IsDistSpec (GF := GF) E pl(&Occil.DiscreteExtra.binomialHalfBits #int (n : ℤ))
      (law n) (fun k : ℕ => Val.int (k : ℤ)) where
  spec F _ := wand_entails (twp_binomialHalfBits E n F)

end specification

end

end SampLib.BinomialHalfBits
