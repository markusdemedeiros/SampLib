import SampLib.Weighted.Laws.OneillUniform
import SampLib.Weighted.LemireUniform

/-! # O'Neill's lazy-threshold multiply-high reduction

The first product avoids threshold computation when its low word already
certifies acceptance. Subsequent draws use the same equal-fibre rejection law.
-/

open ProbLang
open scoped ENNReal NNReal

namespace SampLib.OneillUniform

noncomputable section

private theorem valid_test (n bits : ℕ) (hn : 0 < n) (hnw : n ≤ 2 ^ bits) :
    (decide ((n : ℤ) ≤ 0) || decide ((2 : ℤ) ^ bits < n)) = false := by
  have hw : (n : ℤ) ≤ 2 ^ bits := by exact_mod_cast hnw
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
  omega

private theorem word_cast (bits : ℕ) : ((2 ^ bits : ℕ) : ℤ) = (2 : ℤ) ^ bits := by
  simp only [Nat.cast_pow, Nat.cast_ofNat]

private def accept {rT : Type _} (n bits : ℕ) : Exp rT := pl%
  rec accept current :=
    if current % #int ((2 ^ bits : ℕ) : ℤ) < #int ((2 ^ bits % n : ℕ) : ℤ) then
      accept (#int (n : ℤ) * &Occil.Weighted.randomBits #int (bits : ℤ))
    else current / #int ((2 ^ bits : ℕ) : ℤ)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_draw (E : CoPset) (n bits : ℕ) (hn : 0 < n)
    (hnw : n ≤ 2 ^ bits) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ k, F k ∂UniformInt.law n) -∗
      tglWp E pl(&(accept n bits)
        (#int (n : ℤ) * &Occil.Weighted.randomBits #int (bits : ℤ)))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε (by norm_num : 1 < (2 : ℝ≥0)) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  twp_bind pl(&Occil.Weighted.randomBits #int (bits : ℤ))
  icombine Hcredit Hterm as Htotal
  ihave Hkernel := ErrorCredit.weaken
    (LemireUniform.expectation n (2 ^ bits) hn hnw F ε) $$ Htotal
  iapply ((RandomBits.randomBits_distSpec E bits).wp
    (LemireUniform.kernel n (2 ^ bits) F ε) (measurable_of_countable _) _) $$ Hkernel
  iintro %k Hcredit
  twp_pures
  rw [← Nat.cast_mul, ← Int.natCast_mod]
  by_cases hk : n * k % (2 ^ bits) < 2 ^ bits % n
  · rw [show decide (((n * k % (2 ^ bits) : ℕ) : ℤ) <
      ((2 ^ bits % n : ℕ) : ℤ)) = true by exact_mod_cast decide_eq_true hk]
    twp_pure
    isimp only [LemireUniform.kernel, ite_eq_left hk] at Hcredit
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    isimp [accept, Exp.close, Exp.closeRec] at IH
    simp only [RandomBits.randomBits_openRec, RandomBits.randomBits_closeRec,
      Int.natCast_mod, Nat.cast_pow, Nat.cast_ofNat]
    iapply IH $$ Hterm Hcredit
  · rw [show decide (((n * k % (2 ^ bits) : ℕ) : ℤ) <
      ((2 ^ bits % n : ℕ) : ℤ)) = false by exact decide_eq_false (by omega)]
    twp_pures
    twp_value
    imodintro
    iexists n * k / (2 ^ bits)
    isimp only [LemireUniform.kernel, ite_eq_right hk] at Hcredit
    iframe Hcredit
    ipureintro
    exact Val.ext (by simp only [Int.natCast_div])

private theorem twp_current (E : CoPset) (n bits k : ℕ) (hn : 0 < n)
    (hnw : n ≤ 2 ^ bits) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (LemireUniform.kernel n (2 ^ bits) F 0 k) -∗
      tglWp E pl(&(accept n bits) #int ((n * k : ℕ) : ℤ))
        (fun v : Val rT => iprop(∃ y : ℕ, ⌜v = Val.int (y : ℤ)⌝ ∗ ↯ (F y))) := by
  have hdraw := twp_draw (rT := rT) (GF := GF) E n bits hn hnw F
  simp [accept, Exp.close, Exp.closeRec] at hdraw
  iintro Hcredit
  twp_pures
  rw [← Int.natCast_mod]
  by_cases hk : n * k % (2 ^ bits) < 2 ^ bits % n
  · rw [show decide (((n * k % (2 ^ bits) : ℕ) : ℤ) <
      ((2 ^ bits % n : ℕ) : ℤ)) = true by exact_mod_cast decide_eq_true hk]
    twp_pure
    simp only [RandomBits.randomBits_openRec, RandomBits.randomBits_closeRec,
      Int.natCast_mod, Nat.cast_pow, Nat.cast_ofNat]
    isimp only [LemireUniform.kernel, ite_eq_left hk, mul_zero, add_zero] at Hcredit
    iapply hdraw $$ Hcredit
  · rw [show decide (((n * k % (2 ^ bits) : ℕ) : ℤ) <
      ((2 ^ bits % n : ℕ) : ℤ)) = false by exact decide_eq_false (by omega)]
    twp_pures
    twp_value
    imodintro
    iexists n * k / (2 ^ bits)
    isimp only [LemireUniform.kernel, ite_eq_right hk] at Hcredit
    iframe Hcredit
    ipureintro
    exact Val.ext (by simp only [Int.natCast_div])

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_threshold (E : CoPset) (n width : ℕ) (hnw : n ≤ width) :
    ⊢ tglWp E
      pl(if #int ((width - n : ℕ) : ℤ) < #int (n : ℤ)
        then #int ((width - n : ℕ) : ℤ) else
          let reduced := #int ((width - n : ℕ) : ℤ) - #int (n : ℤ);
          if reduced < #int (n : ℤ) then reduced else reduced % #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int ((width % n : ℕ) : ℤ)⌝)) := by
  have hresult := threshold_eq n width hnw
  unfold threshold at hresult
  twp_pures
  by_cases h₁ : width - n < n
  · rw [show decide (((width - n : ℕ) : ℤ) < (n : ℤ)) = true by
      exact_mod_cast decide_eq_true h₁]
    twp_pures
    twp_value
    imodintro
    ipureintro
    apply Val.ext
    rw [show width - n = width % n from by simpa only [ite_eq_left h₁] using hresult]
  · rw [show decide (((width - n : ℕ) : ℤ) < (n : ℤ)) = false by
      exact decide_eq_false (by omega)]
    iterate 2 twp_pure
    rw [← Nat.cast_sub (Nat.le_of_not_gt h₁)]
    twp_pures
    by_cases h₂ : width - n - n < n
    · rw [show decide (((width - n - n : ℕ) : ℤ) < (n : ℤ)) = true by
        exact_mod_cast decide_eq_true h₂]
      twp_pures
      twp_value
      imodintro
      ipureintro
      apply Val.ext
      rw [show width - n - n = width % n from by
        simpa only [ite_eq_right h₁, ite_eq_left h₂] using hresult]
    · rw [show decide (((width - n - n : ℕ) : ℤ) < (n : ℤ)) = false by
        exact decide_eq_false (by omega)]
      twp_pures
      twp_value
      imodintro
      ipureintro
      apply Val.ext
      rw [← Int.natCast_mod, show (width - n - n) % n = width % n from by
        simpa only [ite_eq_right h₁, ite_eq_right h₂] using hresult]

/-- Lazy threshold computation preserves the exact multiply-high uniform law. -/
theorem oneillUniform_distSpec (E : CoPset) (n bits : ℕ) [NeZero n]
    (hnw : n ≤ 2 ^ bits) :
    IsDistSpec (GF := GF) E
      pl(&Occil.WeightedVariants.oneillUniform #int (n : ℤ) #int (bits : ℤ))
      (UniformInt.law n) (fun k : ℕ => Val.int (k : ℤ)) := by
  refine ⟨fun F _ => ?_⟩
  have hcurrent (k : ℕ) := twp_current (rT := rT) (GF := GF)
    E n bits k (NeZero.pos n) hnw F
  simp [accept, Exp.close, Exp.closeRec] at hcurrent
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
  twp_pure
  simp only [RandomBits.randomBits_openRec, RandomBits.randomBits_closeRec]
  twp_bind pl(&Occil.Weighted.randomBits #int (bits : ℤ))
  ihave Hkernel := ErrorCredit.weaken
    (initial_expectation n (2 ^ bits) (NeZero.pos n) hnw F) $$ Hcredit
  iapply ((RandomBits.randomBits_distSpec E bits).wp
    (LemireUniform.kernel n (2 ^ bits) F 0) (measurable_of_countable _) _) $$ Hkernel
  iintro %k Hcredit
  twp_pures
  rw [← Nat.cast_mul, ← word_cast bits, ← Int.natCast_mod]
  by_cases hk : n * k % (2 ^ bits) < n
  · rw [show decide (((n * k % (2 ^ bits) : ℕ) : ℤ) < (n : ℤ)) = true by
      exact_mod_cast decide_eq_true hk]
    iterate 2 twp_pure
    rw [← Nat.cast_sub hnw]
    twp_pure
    twp_bind pl(if #int ((2 ^ bits - n : ℕ) : ℤ) < #int (n : ℤ)
      then #int ((2 ^ bits - n : ℕ) : ℤ) else
        let reduced := #int ((2 ^ bits - n : ℕ) : ℤ) - #int (n : ℤ);
        if reduced < #int (n : ℤ) then reduced else reduced % #int (n : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply twp_threshold E n (2 ^ bits) hnw
    iintro %v %hv
    subst v
    iterate 2 twp_pure
    simp only [Int.natCast_mod, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul,
      RandomBits.randomBits_openRec]
    iapply hcurrent k $$ Hcredit
  · rw [show decide (((n * k % (2 ^ bits) : ℕ) : ℤ) < (n : ℤ)) = false by
      exact decide_eq_false (by omega)]
    twp_pures
    twp_value
    imodintro
    iexists n * k / (2 ^ bits)
    isimp only [LemireUniform.kernel,
      ite_eq_right (safe_low n (2 ^ bits) _ (NeZero.pos n) (Nat.le_of_not_gt hk))]
      at Hcredit
    iframe Hcredit
    ipureintro
    exact Val.ext (by simp only [Int.natCast_div])

end specification

end

end SampLib.OneillUniform
