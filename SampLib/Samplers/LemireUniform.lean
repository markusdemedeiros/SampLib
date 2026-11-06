import SampLib.Samplers.RandomBits
import SampLib.WeightedIntegerPower
import SampLib.Distributions.MultiplyHigh
import Samplers.Weighted.Reductions

/-! # Lemire's multiply-high reduction

Equal accepted fibres give the uniform quotient law. The discarded low-word
tail has exactly the Euclidean remainder's size, less than half the source.
-/

open ProbLang Finset
open scoped ENNReal NNReal

namespace SampLib.LemireUniform

noncomputable section

section mathematics

open MeasureTheory

def kernel (n width : ℕ) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) (r : ℕ) : ℝ≥0∞ :=
  if n * r % width < width % n then (∫⁻ y, F y ∂UniformInt.law n) + 2 * ε
  else F (n * r / width)

/-- Equal accepted fibres preserve the target expectation and finance retries. -/
theorem expectation (n width : ℕ) (hn : 0 < n) (hnw : n ≤ width)
    (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ r, kernel n width F ε r ∂UniformInt.law width ≤
      (∫⁻ y, F y ∂UniformInt.law n) + ε := by
  let C := ∫⁻ y, F y ∂UniformInt.law n
  let q := width / n
  let t := width % n
  have hq : 0 < q := Nat.div_pos hnw hn
  have ht : t < n := Nat.mod_lt width hn
  have heq : t + n * q = width := Nat.mod_add_div width n
  have hnq : n ≤ n * q := by nlinarith
  have hwp : 0 < width := lt_of_lt_of_le hn hnw
  have hw : (width : ℝ≥0∞) ≠ 0 := by positivity
  have hwt : (width : ℝ≥0∞) ≠ ∞ := by finiteness
  have hreject : ((range width).filter
      (fun r => ¬width % n ≤ n * r % width)).card = t := by
    have hp := card_filter_add_card_filter_not (s := range width)
      (p := fun r => width % n ≤ n * r % width)
    rw [← MultiplyHigh.accepted, MultiplyHigh.card_accepted n width hn hnw,
      card_range] at hp
    dsimp [q] at heq
    omega
  have hsum : ∑ r ∈ range width, kernel n width F ε r =
      q * (∑ y ∈ range n, F y) + t * (C + 2 * ε) := by
    rw [← sum_filter_add_sum_filter_not (range width)
      (fun r => width % n ≤ n * r % width)]
    have hfirst : ∑ r ∈ MultiplyHigh.accepted n width, kernel n width F ε r =
        q * ∑ y ∈ range n, F y := by
      calc
        _ = ∑ r ∈ MultiplyHigh.accepted n width, F (n * r / width) :=
          sum_congr rfl fun r hr => by
            exact ite_eq_right (Nat.not_lt.mpr (mem_filter.mp hr).2)
        _ = _ := MultiplyHigh.sum_accepted n width hn hnw F
    rw [← MultiplyHigh.accepted, hfirst]
    have hlast : ∑ r ∈ (range width).filter
        (fun r => ¬width % n ≤ n * r % width), kernel n width F ε r =
          t * (C + 2 * ε) := by
      calc
        _ = ∑ _r ∈ (range width).filter
            (fun r => ¬width % n ≤ n * r % width), (C + 2 * ε) :=
          sum_congr rfl fun r hr => by
            simp only [kernel, C, ite_eq_left (Nat.lt_of_not_ge (mem_filter.mp hr).2)]
        _ = _ := by simp only [sum_const, nsmul_eq_mul, hreject]
    rw [hlast]
  have hcredit : (∑ y ∈ range n, F y) = n * C := by
    rw [show C = (∑ y ∈ range n, F y) / n from UniformInt.lintegral_law n F,
      ENNReal.mul_div_cancel (by positivity) (by finiteness)]
  have hparts : ((n * q : ℕ) + (t : ℝ≥0∞)) / width = 1 := by
    rw [← Nat.cast_add, Nat.add_comm (n * q) t, heq, ENNReal.div_self hw hwt]
  have hretry : ((2 * t : ℕ) : ℝ≥0∞) / width ≤ 1 := by
    rw [ENNReal.div_le_iff hw hwt, one_mul]
    exact_mod_cast (show 2 * t ≤ width by omega)
  rw [UniformInt.lintegral_law]
  calc
    _ = (((n * q : ℕ) + (t : ℝ≥0∞)) / width) * C +
        (((2 * t : ℕ) : ℝ≥0∞) / width) * ε := by
      rw [hsum, hcredit]
      simp only [Nat.cast_mul, Nat.cast_ofNat, ENNReal.div_eq_inv_mul]
      ring
    _ ≤ C + ε := by
      rw [hparts, one_mul]
      exact add_le_add le_rfl (mul_le_of_le_one_left' hretry)

private theorem valid_test (n bits : ℕ) (hn : 0 < n) (hnw : n ≤ 2 ^ bits) :
    (decide ((n : ℤ) ≤ 0) || decide ((2 : ℤ) ^ bits < n)) = false := by
  have hw : (n : ℤ) ≤ 2 ^ bits := by exact_mod_cast hnw
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
  omega

end mathematics

private def retry {rT : Type _} (n bits : ℕ) : Exp rT := pl%
  rec draw u :=
    let product := #int (n : ℤ) * &Occil.Weighted.randomBits #int (bits : ℤ);
    if product % #int ((2 ^ bits : ℕ) : ℤ) < #int ((2 ^ bits % n : ℕ) : ℤ)
    then draw #() else product / #int ((2 ^ bits : ℕ) : ℤ)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_retry (E : CoPset) (n bits : ℕ) (hn : 0 < n)
    (hnw : n ≤ 2 ^ bits) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ k, F k ∂UniformInt.law n) -∗
      tglWp E pl(&(retry n bits) #())
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε (by norm_num : 1 < (2 : ℝ≥0)) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  iterate 2 twp_pure
  simp only [RandomBits.randomBits_openRec, RandomBits.randomBits_closeRec]
  twp_bind pl(&Occil.Weighted.randomBits #int (bits : ℤ))
  icombine Hcredit Hterm as Htotal
  ihave Hkernel := ErrorCredit.weaken (expectation n (2 ^ bits) hn hnw F ε) $$ Htotal
  iapply ((RandomBits.randomBits_distSpec E bits).wp (kernel n (2 ^ bits) F ε)
    (measurable_of_countable _) _) $$ Hkernel
  iintro %k Hcredit
  twp_pures
  rw [← Nat.cast_mul, ← Int.natCast_mod]
  by_cases hk : n * k % (2 ^ bits) < 2 ^ bits % n
  · rw [show decide (((n * k % (2 ^ bits) : ℕ) : ℤ) <
      ((2 ^ bits % n : ℕ) : ℤ)) = true by exact_mod_cast decide_eq_true hk]
    twp_pure
    isimp only [kernel, ite_eq_left hk] at Hcredit
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    isimp [retry, Exp.close, Exp.closeRec] at IH
    simp only [RandomBits.randomBits_openRec, Int.natCast_mod, Nat.cast_pow,
      Nat.cast_ofNat]
    iapply IH $$ Hterm Hcredit
  · rw [show decide (((n * k % (2 ^ bits) : ℕ) : ℤ) <
      ((2 ^ bits % n : ℕ) : ℤ)) = false by exact decide_eq_false (by omega)]
    twp_pures
    twp_value
    imodintro
    iexists n * k / (2 ^ bits)
    isimp only [kernel, ite_eq_right hk] at Hcredit
    iframe Hcredit
    ipureintro
    exact Val.ext (by simp only [Int.natCast_div])

/-- Exact multiply-high reduction for every positive range fitting in the source word. -/
theorem lemireUniform_distSpec (E : CoPset) (n bits : ℕ) [NeZero n]
    (hnw : n ≤ 2 ^ bits) :
    IsDistSpec (GF := GF) E
      pl(&Occil.WeightedVariants.lemireUniform #int (n : ℤ) #int (bits : ℤ))
      (UniformInt.law n) (fun k : ℕ => Val.int (k : ℤ)) := by
  refine ⟨fun F _ => ?_⟩
  have hretry := twp_retry (rT := rT) (GF := GF) E n bits (NeZero.pos n) hnw F
  simp [retry, Exp.close, Exp.closeRec] at hretry
  iintro Hcredit
  iterate 2 twp_pure
  simp only [WeightedIntegerPower.integerPower_openRec,
    WeightedIntegerPower.integerPower_closeRec]
  twp_bind pl(&Occil.Weighted.integerPower #2 #int (bits : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply WeightedIntegerPower.twp_integerPower E 2 bits
  iintro %v %hv
  subst v
  twp_pures
  rw [valid_test n bits (NeZero.pos n) hnw]
  iterate 4 twp_pure
  simp only [RandomBits.randomBits_openRec, RandomBits.randomBits_closeRec]
  iapply hretry $$ Hcredit

end specification

end

end SampLib.LemireUniform
