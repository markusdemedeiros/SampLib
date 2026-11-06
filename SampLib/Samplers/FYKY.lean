import SampLib.Distributions.BitRecycler
import Samplers.Weighted.Uniform
import Metrology.Iris.LocalBI

/-! # FYKY uniform bit recycling

The one-bit kernel assigns credit to each retained prefix. A finite-horizon
proof follows those individual credits; only their aggregate is compared with
the canonical uniform law. Vanishing cutoff mass removes the horizon.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.FYKY

noncomputable section

private def loop {rT : Type _} (n : ℕ) : Exp rT := pl%
  rec draw width value :=
    let w := width * #2;
    let v := value * #2 + rand(#2, #());
    if #int (n : ℤ) <= w then
      if w - #int (n : ℤ) <= v then v - (w - #int (n : ℤ))
      else draw (w - #int (n : ℤ)) v
    else draw w v

private theorem double_cast (v : ℕ) : (v : ℤ) * 2 = ((v * 2 : ℕ) : ℤ) := by norm_cast

private theorem prefix_cast (c : ℕ) (b : ℤ) (hb : 0 ≤ b) :
    (c : ℤ) * 2 + b = ((c * 2 + b.toNat : ℕ) : ℤ) := by
  simp [Nat.cast_add, Nat.cast_mul, Int.toNat_of_nonneg hb]

private theorem sub_cast (v n : ℕ) (hn : n ≤ v) :
    (v : ℤ) - n = ((v - n : ℕ) : ℤ) := (Nat.cast_sub hn).symm

private theorem le_test (a b : ℕ) : decide ((a : ℤ) ≤ b) = decide (a ≤ b) :=
  decide_eq_decide.mpr (by omega)

private theorem one_test {rT : Type _} [BEq rT] (n : ℕ) :
    ((BaseLit.int (n : ℤ) : BaseLit rT) == .int 1) = decide (n = 1) := by
  change decide ((n : ℤ) = 1) = decide (n = 1)
  exact decide_eq_decide.mpr (by omega)

private theorem positive_test (n : ℕ) (hn : 0 < n) : decide ((n : ℤ) ≤ 0) = false :=
  decide_eq_false (by omega)

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
    ⊢ ↯ (∫⁻ j, F j ∂UniformInt.law 1) -∗ tglWp E pl(&Occil.Weighted.fyky #1)
      (fun result : Val rT => iprop(∃ j : ℕ, ⌜result = Val.int (j : ℤ)⌝ ∗ ↯ (F j))) := by
  iintro Hcredit
  isimp only [one_expectation] at Hcredit
  twp_pures
  twp_value
  imodintro
  iexists 0
  iframe Hcredit
  itrivial

private theorem twp_horizon (E : CoPset) (n T v c : ℕ) (hv : v < n) (hc : c < v)
    (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (BitRecycler.credit .upper n F T v c) -∗
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
    iapply (twp_rand_exp (ε₂ := BitRecycler.bitCredit .upper n T F v c) (by decide)
      (BitRecycler.expectation .upper n T F v c).le) $$ Hcredit
    iintro %b ⟨%hb, Hcredit⟩
    have hbNat := bit_bound b hb
    twp_pure
    simp only [Exp.ofVal]
    twp_pure
    rw [prefix_cast c b hb.1]
    iterate 2 twp_pure
    rw [le_test n (v * 2)]
    by_cases hwide : n ≤ v * 2
    · rw [decide_eq_true hwide]
      iterate 2 twp_pure
      rw [sub_cast (v * 2) n hwide]
      twp_pure
      rw [le_test (v * 2 - n) (c * 2 + b.toNat)]
      isimp only [BitRecycler.bitCredit, BitRecycler.kernel, ite_eq_left hwide] at Hcredit
      by_cases haccept : v * 2 - n ≤ c * 2 + b.toNat
      · rw [decide_eq_true haccept]
        iterate 2 twp_pure
        rw [sub_cast (v * 2) n hwide]
        twp_pure
        rw [sub_cast (c * 2 + b.toNat) (v * 2 - n) haccept]
        twp_value
        imodintro
        iexists c * 2 + b.toNat - (v * 2 - n)
        isimp only [ite_eq_left haccept] at Hcredit
        iframe Hcredit
        ipureintro
        exact Val.ext rfl
      · rw [decide_eq_false haccept]
        iterate 2 twp_pure
        rw [sub_cast (v * 2) n hwide]
        isimp only [ite_eq_right haccept] at Hcredit
        have hrec := IH (v * 2 - n) (c * 2 + b.toNat)
          (BitRecycler.residual_width_lt n v hv) (Nat.lt_of_not_ge haccept)
        simp [loop, Exp.close, Exp.closeRec, max_eq_left hb.1] at hrec
        isimp only [Exp.ofVal, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
          Int.toNat_of_nonneg hb.1]
        iapply hrec $$ Hcredit
    · rw [decide_eq_false hwide]
      twp_pure
      isimp only [BitRecycler.bitCredit, BitRecycler.kernel, ite_eq_right hwide] at Hcredit
      have hrec := IH (v * 2) (c * 2 + b.toNat)
        (Nat.lt_of_not_ge hwide) (BitRecycler.expanded_lt v c b.toNat hc hbNat)
      simp [loop, Exp.close, Exp.closeRec, max_eq_left hb.1] at hrec
      isimp only [Exp.ofVal, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        Int.toNat_of_nonneg hb.1]
      iapply hrec $$ Hcredit

/-- Finite prefix credit and arbitrarily small cutoff mass establish the exact uniform law. -/
theorem twp_fyky (E : CoPset) (n : ℕ) (hn : 0 < n) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ j, F j ∂UniformInt.law n) -∗
      tglWp E pl(&Occil.Weighted.fyky #int (n : ℤ))
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
    have hbudget := (BitRecycler.initial_bound .upper n hn hlarge T F).trans
      (add_le_add le_rfl hT)
    icombine Hcredit Hterm as Hcredit
    ihave Hcredit := ErrorCredit.weaken hbudget $$ Hcredit
    have hloop := twp_horizon (rT := rT) (GF := GF) E n T 1 0 hlarge (by decide) F
    simp [loop, Exp.close, Exp.closeRec] at hloop
    iapply hloop $$ Hcredit

/-- Typed FYKY specification for every positive integer range. -/
theorem fyky_distSpec (E : CoPset) (n : ℕ) [NeZero n] :
    IsDistSpec (GF := GF) E pl(&Occil.Weighted.fyky #int (n : ℤ)) (UniformInt.law n)
      (fun j : ℕ => Val.int (j : ℤ)) where
  spec F _ := wand_entails (twp_fyky E n (NeZero.pos n) F)

omit [ProbLangDist.IsUniformInt rT] in
/-- The one-element range returns zero without invoking a random primitive. -/
theorem fyky_one_distSpec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.Weighted.fyky #1) (UniformInt.law 1)
      (fun j : ℕ => Val.int (j : ℤ)) where
  spec F _ := wand_entails (twp_one E F)

end specification

end

end SampLib.FYKY
