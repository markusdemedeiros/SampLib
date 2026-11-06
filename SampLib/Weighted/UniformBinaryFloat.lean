import SampLib.Weighted.Laws.UniformBinaryFloat
import SampLib.Weighted.RandomBits
import SampLib.Uniform.FairCoin
import SampLib.Weighted.Support.WeightedIntegerPower
import SampLib.Core.SamplerStep

/-! # Capped binary floating-point pairs

The program returns an integer significand/exponent pair in a truncated binary
format. Its exact law is a capped fair-geometric prefix and an independent
uniform mantissa; reaching the cap returns zero.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.UniformBinaryFloat

noncomputable section

/-- The ProbLang representation retains the exact integer pair. -/
def encode {rT : Type _} (x : ℤ × ℤ) : Val rT := .pair (.int x.1) (.int x.2)

private def leading {rT : Type _} (precision cap : ℕ) : Exp rT := pl%
  rec leading zeros :=
    if #int (cap : ℤ) <= zeros then (#0, #0) else
      if &Occil.fairCoin #() then
        (&Occil.Weighted.integerPower #2 #int (precision : ℤ) +
          &Occil.Weighted.randomBits #int (precision : ℤ),
          -(zeros + #int (precision : ℤ) + #1))
      else leading (zeros + #1)

private def leadingValue {rT : Type _} (precision cap : ℕ) : Val rT :=
  ⟨leading precision cap, .fix (by is_lc), by is_lc⟩

private theorem leadingValue_fst {rT : Type _} (precision cap : ℕ) :
    (leadingValue (rT := rT) precision cap).fst = leading precision cap := rfl

private theorem at_cap (cap : ℕ) : decide ((cap : ℤ) ≤ cap) = true := by simp

private theorem before_cap (cap offset : ℕ) (h : offset < cap) :
    decide ((cap : ℤ) ≤ offset) = false := by simp; omega

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_leading (E : CoPset) (precision cap n offset : ℕ)
    (hi : offset + n = cap) (F : ℤ × ℤ → ℝ≥0∞) :
    ⊢ ↯ (credit precision n offset F) -∗
      tglWp E pl(&(leading (rT := rT) precision cap) #int (offset : ℤ))
        (fun v : Val rT => iprop(∃ x : ℤ × ℤ, ⌜v = encode x⌝ ∗ ↯ (F x))) := by
  induction n generalizing offset with
  | zero =>
    have he : offset = cap := by omega
    subst offset
    rw [credit_zero]
    iintro Hcredit
    rw [← leadingValue_fst]
    twp_step
    simp [Exp.open', Exp.openRec, Exp.close, Exp.closeRec, Var.internal.injEq]
    twp_pure
    twp_pure
    rw [at_cap]
    twp_pures
    twp_value
    imodintro
    iexists (0, 0)
    iframe Hcredit
    ipureintro
    exact Val.ext rfl
  | succ n IH =>
    have hc : offset < cap := by omega
    have hi' : (offset + 1) + n = cap := by omega
    iintro Hcredit
    rw [← leadingValue_fst]
    twp_step
    simp [Exp.open', Exp.openRec, Exp.close, Exp.closeRec, Var.internal.injEq]
    twp_pure
    twp_pure
    rw [before_cap cap offset hc]
    twp_pure
    twp_bind pl(&Occil.fairCoin #())
    isimp only [← expectation precision n offset F] at Hcredit
    iapply (FairCoin.fairCoin_distSpec E).wp (coinCredit precision n offset F)
      (measurable_of_countable _) _ $$ Hcredit
    iintro %b Hcredit
    cases b with
    | false =>
      twp_pure
      twp_pure
      rw [← Nat.cast_add_one, leadingValue_fst]
      isimp only [coinCredit] at Hcredit
      iapply IH (offset + 1) hi' $$ Hcredit
    | true =>
      iterate 4 twp_pure
      twp_bind pl(&Occil.Weighted.randomBits #int (precision : ℤ))
      isimp only [coinCredit] at Hcredit
      iapply (RandomBits.randomBits_distSpec E precision).wp
        (fun m => F (point precision offset m)) (measurable_of_countable _) _ $$ Hcredit
      iintro %m Hcredit
      twp_bind pl(&Occil.Weighted.integerPower #2 #int (precision : ℤ))
      iapply tglWp_wand
      isplitl []
      · iapply WeightedIntegerPower.twp_integerPower E 2 precision
      iintro %v %hv
      subst v
      twp_pure
      twp_value
      imodintro
      iexists point precision offset m
      iframe Hcredit
      ipureintro
      apply Val.ext
      simp [encode, point, Exp.ofVal, Nat.cast_add, Nat.cast_pow]

/-- The exact truncated-format law for every natural precision and leading-zero cap. -/
theorem uniformBinaryFloat_distSpec (E : CoPset) (precision maxZeros : ℕ) :
    IsDistSpec (GF := GF) E
      pl(&Occil.Weighted.uniformBinaryFloat #int (precision : ℤ) #int (maxZeros : ℤ) #())
      (law precision maxZeros) encode where
  spec F _ := by
    have hloop := twp_leading (rT := rT) (GF := GF) E precision maxZeros maxZeros 0
      (Nat.zero_add _) F
    simp [leading, Exp.close, Exp.closeRec, credit] at hloop
    iintro Hcredit
    iterate 8 twp_pure
    simp only [FairCoin.fairCoin_openRec, FairCoin.fairCoin_closeRec,
      RandomBits.randomBits_openRec, RandomBits.randomBits_closeRec,
      WeightedIntegerPower.integerPower_openRec, WeightedIntegerPower.integerPower_closeRec]
    iapply hloop $$ Hcredit

end specification

end

end SampLib.UniformBinaryFloat
