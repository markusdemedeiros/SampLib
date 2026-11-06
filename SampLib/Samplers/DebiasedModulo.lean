import SampLib.Samplers.RandomBits
import SampLib.WeightedIntegerPower
import SampLib.Distributions.WordRotation
import Samplers.Weighted.Reductions

/-! # Uniform integers by discarding the incomplete low residue interval

The remaining words are complete, rotated residue cycles. The discarded prefix
has less than half the source mass, so retries can double termination credit.
-/

open ProbLang Finset
open scoped ENNReal NNReal

namespace SampLib.DebiasedModulo

noncomputable section

section mathematics

open MeasureTheory

def kernel (n width : ℕ) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  if k < width % n then (∫⁻ i, F i ∂UniformInt.law n) + 2 * ε else F (k % n)

/-- Complete residue cycles preserve output credit; the short prefix funds retries. -/
theorem expectation (n width : ℕ) (hn : 0 < n) (hnw : n ≤ width)
    (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ k, kernel n width F ε k ∂UniformInt.law width ≤
      (∫⁻ i, F i ∂UniformInt.law n) + ε := by
  let C := ∫⁻ i, F i ∂UniformInt.law n
  let q := width / n
  let t := width % n
  have hq : 0 < q := Nat.div_pos hnw hn
  have ht : t < n := Nat.mod_lt width hn
  have heq : t + n * q = width := Nat.mod_add_div width n
  have hnq : n ≤ n * q := by nlinarith
  have hwp : 0 < width := lt_of_lt_of_le hn hnw
  have hw : (width : ℝ≥0∞) ≠ 0 := by positivity
  have hwt : (width : ℝ≥0∞) ≠ ∞ := by finiteness
  have hsum : ∑ k ∈ range width, kernel n width F ε k =
      (t : ℝ≥0∞) * (C + 2 * ε) + q * ∑ j ∈ range n, F j := by
    rw [show range width = range (t + n * q) from congrArg range heq.symm,
      sum_range_add]
    have hprefix : ∑ k ∈ range t, kernel n width F ε k = t * (C + 2 * ε) := by
      simp only [kernel]
      rw [sum_congr rfl fun k hk => ite_eq_left (mem_range.mp hk)]
      simp [C, nsmul_eq_mul, mul_add]
    have hsuffix : ∑ k ∈ range (n * q), kernel n width F ε (t + k) =
        q * ∑ j ∈ range n, F j := by
      simp only [kernel, show ∀ k, ¬t + k < width % n from fun k => by omega,
        ite_false]
      exact WordRotation.sum_cycles n q t F
    rw [hprefix, hsuffix]
  have hcredit : (∑ j ∈ range n, F j) = n * C := by
    rw [show C = (∑ j ∈ range n, F j) / n from UniformInt.lintegral_law n F,
      ENNReal.mul_div_cancel (by positivity) (by finiteness)]
  have hparts : ((t : ℝ≥0∞) + n * q) / width = 1 := by
    rw [← Nat.cast_mul, ← Nat.cast_add, heq, ENNReal.div_self hw hwt]
  have hretry : ((2 * t : ℕ) : ℝ≥0∞) / width ≤ 1 := by
    rw [ENNReal.div_le_iff hw hwt, one_mul]
    exact_mod_cast (show 2 * t ≤ width by omega)
  rw [UniformInt.lintegral_law]
  calc
    _ = (((t : ℝ≥0∞) + n * q) / width) * C +
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
    let value := &Occil.Weighted.randomBits #int (bits : ℤ);
    if value < #int ((2 ^ bits % n : ℕ) : ℤ) then draw #()
    else value % #int (n : ℤ)

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
  by_cases hk : k < 2 ^ bits % n
  · rw [show decide ((k : ℤ) < ((2 ^ bits % n : ℕ) : ℤ)) = true by
      exact_mod_cast decide_eq_true hk]
    twp_pure
    isimp only [kernel, ite_eq_left hk] at Hcredit
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    isimp [retry, Exp.close, Exp.closeRec] at IH
    simp only [RandomBits.randomBits_openRec, Int.natCast_mod, Nat.cast_pow,
      Nat.cast_ofNat]
    iapply IH $$ Hterm Hcredit
  · rw [show decide ((k : ℤ) < ((2 ^ bits % n : ℕ) : ℤ)) = false by
      exact decide_eq_false (by omega)]
    twp_pures
    twp_value
    imodintro
    iexists k % n
    isimp only [kernel, ite_eq_right hk] at Hcredit
    iframe Hcredit
    ipureintro
    exact Val.ext (by simp only [Int.natCast_mod])

/-- Discarding the low incomplete residue interval gives an exact uniform draw. -/
theorem debiasedModulo_distSpec (E : CoPset) (n bits : ℕ) [NeZero n]
    (hnw : n ≤ 2 ^ bits) :
    IsDistSpec (GF := GF) E
      pl(&Occil.WeightedVariants.debiasedModulo #int (n : ℤ) #int (bits : ℤ))
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

end SampLib.DebiasedModulo
