import SampLib.Common.Laws.BitRecycler

/-! # Fast Dice Roller

The program follows pointwise finite-horizon credits. The aggregate interval
identity compares the initial singleton state with the uniform law; arbitrarily
small cutoff mass removes the horizon.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.FastDiceRoller

noncomputable section

private def loop {rT : Type _} (n : ℕ) : Exp rT := pl%
  rec go v c :=
    let vv := v * #2;
    let cc := c * #2 + rand(#2, #());
    if #int (n : ℤ) <= vv then
      if cc < #int (n : ℤ) then cc else go (vv - #int (n : ℤ)) (cc - #int (n : ℤ))
    else go vv cc

private theorem double_cast (v : ℕ) : (v : ℤ) * 2 = ((v * 2 : ℕ) : ℤ) := by norm_cast

private theorem prefix_cast (c : ℕ) (b : ℤ) (hb : 0 ≤ b) :
    (c : ℤ) * 2 + b = ((c * 2 + b.toNat : ℕ) : ℤ) := by
  simp [Nat.cast_add, Nat.cast_mul, Int.toNat_of_nonneg hb]

private theorem sub_cast (v n : ℕ) (hn : n ≤ v) :
    (v : ℤ) - n = ((v - n : ℕ) : ℤ) := (Nat.cast_sub hn).symm

private theorem one_test {rT : Type _} [BEq rT] (n : ℕ) :
    ((BaseLit.int (n : ℤ) : BaseLit rT) == .int 1) = decide (n = 1) := by
  change decide ((n : ℤ) = 1) = decide (n = 1)
  exact decide_eq_decide.mpr (by omega)

private theorem positive_test (n : ℕ) (hn : 0 < n) : decide ((n : ℤ) ≤ 0) = false :=
  decide_eq_false (by exact_mod_cast not_le.mpr hn)

private theorem bit_bound (b : ℤ) (hb : 0 ≤ b ∧ b < 2) : b.toNat < 2 := by omega

private theorem one_expectation (F : ℕ → ℝ≥0∞) :
    (∫⁻ j, F j ∂UniformInt.law 1) = F 0 := by simp [UniformInt.lintegral_law]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_one (E : CoPset) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ j, F j ∂UniformInt.law 1) -∗ tglWp E pl(&Occil.fastDiceRoller #1)
      (fun result : Val rT => iprop(∃ j : ℕ, ⌜result = Val.int (j : ℤ)⌝ ∗ ↯ (F j))) := by
  iintro Hcredit
  twp_pures
  twp_value
  imodintro
  iexists 0
  isimp only [one_expectation] at Hcredit
  iframe Hcredit
  itrivial

/-- Finite induction follows each actual bit and retained rank. -/
private theorem twp_horizon (E : CoPset) (n T v c : ℕ) (hv : v < n) (hc : c < v)
    (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (BitRecycler.credit .lower n F T v c) -∗
      tglWp E pl(&(loop n) #int (v : ℤ) #int (c : ℤ))
        (fun result : Val rT => iprop(∃ j : ℕ, ⌜result = Val.int (j : ℤ)⌝ ∗ ↯ (F j))) := by
  induction T generalizing v c with
  | zero =>
    iintro Hcredit
    isimp only [BitRecycler.credit_zero] at Hcredit
    iexfalso
    iapply ErrorCredit.contradict le_rfl $$ Hcredit
  | succ T IH =>
    iintro Hcredit
    iterate 4 twp_pure
    rw [double_cast v]
    twp_pure
    twp_bind pl(rand(#2, #()))
    iapply (twp_rand_exp (ε₂ := BitRecycler.bitCredit .lower n T F v c) (by decide)
      (BitRecycler.expectation .lower n T F v c).le) $$ Hcredit
    iintro %b ⟨%hb, Hcredit⟩
    have hbNat := bit_bound b hb
    have hx := BitRecycler.expanded_lt v c b.toNat hc hbNat
    twp_pure
    simp only [Exp.ofVal]
    twp_pure
    rw [prefix_cast c b hb.1]
    iterate 2 twp_pure
    simp only [Int.ofNat_le]
    by_cases hwide : n ≤ v * 2
    · rw [decide_eq_true hwide]
      iterate 2 twp_pure
      simp only [Int.ofNat_lt]
      isimp only [BitRecycler.bitCredit, BitRecycler.kernel, ite_eq_left hwide] at Hcredit
      by_cases haccept : c * 2 + b.toNat < n
      · rw [decide_eq_true haccept]
        twp_pure
        twp_value
        imodintro
        iexists c * 2 + b.toNat
        isimp only [ite_eq_left haccept] at Hcredit
        iframe Hcredit
        ipureintro
        exact Val.ext rfl
      · rw [decide_eq_false haccept]
        iterate 3 twp_pure
        rw [sub_cast (v * 2) n hwide,
          sub_cast (c * 2 + b.toNat) n (Nat.le_of_not_gt haccept)]
        isimp only [ite_eq_right haccept] at Hcredit
        have hrec := IH (v * 2 - n) (c * 2 + b.toNat - n)
          (BitRecycler.residual_width_lt n v hv)
          (BitRecycler.lower_recycle_lt n (v * 2) (c * 2 + b.toNat)
            (Nat.le_of_not_gt haccept) hx)
        dsimp [loop, Exp.close, Exp.closeRec, Exp.ofVal] at hrec
        simp only [Exp.ofVal]
        iapply hrec $$ Hcredit
    · rw [decide_eq_false hwide]
      twp_pure
      isimp only [BitRecycler.bitCredit, BitRecycler.kernel, ite_eq_right hwide] at Hcredit
      have hrec := IH (v * 2) (c * 2 + b.toNat) (Nat.lt_of_not_ge hwide) hx
      simp [loop, Exp.close, Exp.closeRec, max_eq_left hb.1] at hrec
      isimp only [Exp.ofVal, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        Int.toNat_of_nonneg hb.1]
      iapply hrec $$ Hcredit

/-- A vanishing finite-horizon remainder proves total correctness with the exact uniform law. -/
theorem twp_fastDiceRoller (E : CoPset) (n : ℕ) (hn : 0 < n) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ j, F j ∂UniformInt.law n) -∗
      tglWp E pl(&Occil.fastDiceRoller #int (n : ℤ))
        (fun result : Val rT => iprop(∃ j : ℕ, ⌜result = Val.int (j : ℤ)⌝ ∗ ↯ (F j))) := by
  by_cases hOne : n = 1
  · subst n
    iapply twp_one E F
  · have hlarge : 1 < n := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn.ne', hOne⟩
    iintro Hcredit
    iterate 2 twp_pure
    rw [positive_test n hn]
    iterate 2 twp_pure
    rw [one_test n, decide_eq_false hOne]
    iterate 2 twp_pure
    iapply twp_err_pos solve_not_value
    iintro %ε %hε Hterm
    obtain ⟨T, hT⟩ := BitRecycler.exists_horizon n hn ε hε
    have hbudget := (BitRecycler.initial_bound .lower n hn hlarge T F).trans
      (add_le_add le_rfl hT)
    icombine Hcredit Hterm as Hcredit
    ihave Hcredit := ErrorCredit.weaken hbudget $$ Hcredit
    have hloop := twp_horizon (rT := rT) (GF := GF) E n T 1 0 hlarge (by decide) F
    simp [loop, Exp.close, Exp.closeRec] at hloop
    iapply hloop $$ Hcredit

/-- Exact uniform integers from independent fair bits, for every positive exclusive bound. -/
theorem fastDiceRoller_distSpec (E : CoPset) (n : ℕ) [NeZero n] :
    IsDistSpec (GF := GF) E pl(&Occil.fastDiceRoller #int (n : ℤ)) (UniformInt.law n)
      (fun j : ℕ => Val.int (j : ℤ)) where
  spec F _ := wand_entails (twp_fastDiceRoller E n (NeZero.pos n) F)

omit [ProbLangDist.IsUniformInt rT] in
/-- The singleton range returns zero without invoking a random primitive. -/
theorem fastDiceRoller_one_distSpec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.fastDiceRoller #1) (UniformInt.law 1)
      (fun j : ℕ => Val.int (j : ℤ)) where
  spec F _ := wand_entails (twp_one E F)

end specification

end

end SampLib.FastDiceRoller
