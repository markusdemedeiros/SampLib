import SampLib.Weighted.Laws.LemireUniform
import SampLib.Weighted.RandomBits
import SampLib.Weighted.Support.WeightedIntegerPower
import Samplers.Weighted.Reductions

/-! # Lemire's multiply-high reduction

Equal accepted fibres give the uniform quotient law. The discarded low-word
tail has exactly the Euclidean remainder's size, less than half the source.
-/

open ProbLang Finset
open scoped ENNReal NNReal

namespace SampLib.LemireUniform

noncomputable section

private theorem valid_test (n bits : ℕ) (hn : 0 < n) (hnw : n ≤ 2 ^ bits) :
    (decide ((n : ℤ) ≤ 0) || decide ((2 : ℤ) ^ bits < n)) = false := by
  have hw : (n : ℤ) ≤ 2 ^ bits := by exact_mod_cast hnw
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
  omega

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
