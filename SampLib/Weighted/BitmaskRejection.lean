import SampLib.Weighted.RandomBits
import SampLib.Weighted.Support.PowerOfTwoCeiling
import SampLib.Common.Laws.UniformRejection

/-! # Uniform integers by bitmask rejection

The candidate is a full binary word at the least enclosing power of two.
At least half its words are accepted, so rejected words can double retry credit.
-/

open ProbLang Finset
open scoped ENNReal NNReal

namespace SampLib.BitmaskRejection

noncomputable section

section mathematics

open MeasureTheory

/-- Uniform word proposals preserve the target credit and fund bounded rejection. -/
theorem expectation (n : ℕ) (hn : 0 < n) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ k, UniformRejection.kernel n F ε k
      ∂UniformInt.law (PowerOfTwoCeiling.width n) ≤
      (∫⁻ k, F k ∂UniformInt.law n) + ε := by
  rw [UniformInt.lintegral_law]
  exact UniformRejection.expectation n _ hn (PowerOfTwoCeiling.le_width n)
    (PowerOfTwoCeiling.width_le_double n hn) F ε

private theorem power_test (n : ℕ) : ((2 : ℤ) ^ (n + 1) == 1) = false := by
  apply beq_eq_false_iff_ne.mpr
  have hpos : (0 : ℤ) < 2 ^ n := by positivity
  rw [pow_succ]
  omega

private theorem power_half (n : ℕ) : (2 : ℤ) ^ (n + 1) / 2 = 2 ^ n := by
  rw [pow_succ]
  simp

private theorem prefix_cast (v : ℕ) (b : ℤ) (hb : 0 ≤ b) :
    (v : ℤ) * 2 + b = ((v * 2 + b.toNat : ℕ) : ℤ) := by
  simp [Nat.cast_add, Nat.cast_mul, Int.toNat_of_nonneg hb]

private theorem int_beq {rT : Type _} [BEq rT] (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = (a == b) := rfl

end mathematics

private def candidate {rT : Type _} : Exp rT := pl%
  rec bits remaining value := if remaining = #1 then value else
    bits (remaining / #2) (value * #2 + rand(#2, #()))

private theorem candidate_lc {rT : Type _} :
    (candidate : Exp rT).IsLocallyClosed := by is_lc

private theorem candidate_fv {rT : Type _} : (candidate : Exp rT).fv = ∅ := by
  simp [candidate, Exp.fv]

@[local simp] private theorem candidate_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e candidate = candidate := (Exp.open_lc k e _ candidate_lc).symm

@[local simp] private theorem candidate_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (candidate : Exp rT) = candidate :=
  Exp.closeRec_fresh x _ k (by simp [candidate_fv])

private def retry {rT : Type _} (n : ℕ) : Exp rT := pl%
  rec draw u :=
    let x := &candidate #int (PowerOfTwoCeiling.width n : ℤ) #0;
    if x < #int (n : ℤ) then x else draw #()

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_candidate (E : CoPset) (bits v : ℕ) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (RandomBits.credit bits v F) -∗
      tglWp E pl(&candidate #int ((2 : ℤ) ^ bits) #int (v : ℤ))
        (fun result : Val rT => iprop(∃ k : ℕ,
          ⌜result = Val.int (k : ℤ)⌝ ∗ ↯ (F k))) := by
  induction bits generalizing v with
  | zero =>
    iintro Hcredit
    twp_pures
    twp_value
    imodintro
    iexists v
    isimp only [RandomBits.credit_zero] at Hcredit
    iframe Hcredit
    itrivial
  | succ bits ih =>
    iintro Hcredit
    twp_pures
    rw [int_beq, power_test]
    twp_pure
    twp_bind pl(rand(#2, #()))
    iapply (twp_rand_exp (ε₂ := fun b => RandomBits.credit bits (v * 2 + b) F)
      (by norm_num) ?_) $$ Hcredit
    · exact le_of_eq (RandomBits.expectation bits v F)
    iintro %b ⟨%hb, Hcredit⟩
    twp_pure
    simp only [Exp.ofVal]
    iterate 2 twp_pure
    rw [power_half, prefix_cast v b hb.1]
    have hrec := ih (v * 2 + b.toNat)
    simp [candidate, Exp.close, Exp.closeRec, max_eq_left hb.1] at hrec
    isimp only [Exp.ofVal, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Int.toNat_of_nonneg hb.1]
    iapply hrec $$ Hcredit

private theorem candidate_distSpec (E : CoPset) (n : ℕ) :
    IsDistSpec (GF := GF) E pl(&candidate #int (PowerOfTwoCeiling.width n : ℤ) #0)
      (UniformInt.law (PowerOfTwoCeiling.width n)) (fun k : ℕ => Val.int (k : ℤ)) := by
  refine ⟨fun F _ => ?_⟩
  have h := twp_candidate (rT := rT) (GF := GF) E (Nat.clog 2 n) 0 F
  simp only [PowerOfTwoCeiling.width, Nat.cast_pow, Nat.cast_ofNat]
  iintro Hcredit
  iapply h
  isimp only [PowerOfTwoCeiling.width, UniformInt.lintegral_law,
    Nat.cast_pow, Nat.cast_ofNat] at Hcredit
  isimp only [RandomBits.credit, Nat.zero_mul, Nat.zero_add]
  iexact Hcredit

private theorem twp_retry (E : CoPset) (n : ℕ) (hn : 0 < n) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ k, F k ∂UniformInt.law n) -∗
      tglWp E pl(&(retry n) #())
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε (by norm_num : 1 < (2 : ℝ≥0)) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  iterate 2 twp_pure
  simp only [candidate_openRec, candidate_closeRec]
  twp_bind pl(&candidate #int (PowerOfTwoCeiling.width n : ℤ) #0)
  icombine Hcredit Hterm as Htotal
  ihave Hkernel := ErrorCredit.weaken (expectation n hn F ε) $$ Htotal
  iapply ((candidate_distSpec E n).wp (UniformRejection.kernel n F ε)
    (measurable_of_countable _) _) $$ Hkernel
  iintro %k Hcredit
  twp_pures
  by_cases hk : k < n
  · rw [show decide ((k : ℤ) < (n : ℤ)) = true by exact_mod_cast decide_eq_true hk]
    twp_pures
    twp_value
    imodintro
    iexists k
    isimp only [UniformRejection.kernel, ite_eq_left hk] at Hcredit
    iframe Hcredit
    itrivial
  · rw [show decide ((k : ℤ) < (n : ℤ)) = false by exact decide_eq_false (by omega)]
    twp_pure
    isimp only [UniformRejection.kernel, ite_eq_right hk] at Hcredit
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    isimp [retry, Exp.close, Exp.closeRec] at IH
    simp only [candidate_openRec]
    iapply IH $$ Hterm Hcredit

/-- Bitmask rejection is exactly uniform for every positive target width. -/
theorem bitmaskRejection_distSpec (E : CoPset) (n : ℕ) [NeZero n] :
    IsDistSpec (GF := GF) E pl(&Occil.Weighted.bitmaskRejection #int (n : ℤ))
      (UniformInt.law n) (fun k : ℕ => Val.int (k : ℤ)) := by
  refine ⟨fun F _ => ?_⟩
  have hretry := twp_retry (rT := rT) (GF := GF) E n (NeZero.pos n) F
  simp [retry, candidate, Exp.close, Exp.closeRec] at hretry
  iintro Hcredit
  twp_pure
  simp only [PowerOfTwoCeiling.powerOfTwoCeiling_openRec,
    PowerOfTwoCeiling.powerOfTwoCeiling_closeRec]
  twp_bind pl(&Occil.Weighted.powerOfTwoCeiling #int (n : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply PowerOfTwoCeiling.twp_powerOfTwoCeiling E n (NeZero.pos n)
  iintro %v %hv
  subst v
  iterate 3 twp_pure
  iapply hretry $$ Hcredit

end specification

end

end SampLib.BitmaskRejection
