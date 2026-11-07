import SampLib.Weighted.Laws.DivisionRejection
import SampLib.Core.Retry
import SampLib.Weighted.RandomBits
import SampLib.Weighted.Support.WeightedIntegerPower
import SampLib.Common.Laws.WordIntervals
import SampLib.Common.Laws.UniformRejection
import Samplers.Weighted.Reductions

/-! # Uniform integers by division with rejection

The accepted prefix consists of equally sized quotient blocks. Its incomplete
last block is discarded, and at least half of all source words remain.
-/

open ProbLang
open scoped ENNReal NNReal

namespace SampLib.DivisionRejection

noncomputable section

private theorem valid_test (n bits : ℕ) (hn : 0 < n) (hnw : n ≤ 2 ^ bits) :
    (decide ((n : ℤ) ≤ 0) || decide ((2 : ℤ) ^ bits < n)) = false := by
  have hw : (n : ℤ) ≤ 2 ^ bits := by exact_mod_cast hnw
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
  omega

private def retry {rT : Type _} (n bits : ℕ) : Exp rT := pl%
  rec draw u :=
    let value := &Occil.Weighted.randomBits #int (bits : ℤ) /
      #int ((2 ^ bits / n : ℕ) : ℤ);
    if value < #int (n : ℤ) then value else draw #()

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
  iapply Retry.twp_loop solve_not_value (by norm_num : 1 < (2 : ℝ≥0))
  iintro !> %ε %hε IH Hcredit
  iterate 2 twp_pure
  simp only [RandomBits.randomBits_openRec, RandomBits.randomBits_closeRec]
  twp_bind pl(&Occil.Weighted.randomBits #int (bits : ℤ))
  ihave Hkernel := ErrorCredit.weaken (expectation n (2 ^ bits) hn hnw F ε) $$ Hcredit
  iapply ((RandomBits.randomBits_distSpec E bits).wp (kernel n (2 ^ bits) F ε)
    (measurable_of_countable _) _) $$ Hkernel
  iintro %k Hcredit
  twp_pures
  rw [← Int.natCast_div]
  by_cases hk : k / (2 ^ bits / n) < n
  · rw [show decide (((k / (2 ^ bits / n) : ℕ) : ℤ) < (n : ℤ)) = true by
      exact_mod_cast decide_eq_true hk]
    twp_pures
    twp_value
    imodintro
    iexists k / (2 ^ bits / n)
    isimp only [kernel, ite_eq_left hk] at Hcredit
    iframe Hcredit
    itrivial
  · rw [show decide (((k / (2 ^ bits / n) : ℕ) : ℤ) < (n : ℤ)) = false by
      exact decide_eq_false (by omega)]
    twp_pure
    isimp only [kernel, ite_eq_right hk] at Hcredit
    isimp [retry, Exp.close, Exp.closeRec] at IH
    simp only [RandomBits.randomBits_openRec, Int.natCast_div, Nat.cast_pow,
      Nat.cast_ofNat]
    iapply IH $$ Hcredit

/-- Exact division rejection on every valid word width, including zero-bit words. -/
theorem divisionRejection_distSpec (E : CoPset) (n bits : ℕ) [NeZero n]
    (hnw : n ≤ 2 ^ bits) :
    IsDistSpec (GF := GF) E
      pl(&Occil.WeightedVariants.divisionRejection #int (n : ℤ) #int (bits : ℤ))
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

end SampLib.DivisionRejection
