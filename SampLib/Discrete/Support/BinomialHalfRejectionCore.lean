import SampLib.Discrete.Laws.BinomialHalfRejection
import SampLib.Discrete.Support.BinomialHalfBranchesSyntax
import SampLib.Discrete.Geometric
import SampLib.Discrete.UniformFin
import SampLib.Uniform.RationalCoin
import SampLib.Core.Retry

/-! # Bringmann's half-binomial rejection loop

Each round draws a geometric block, a uniform rank, and a fair sign, then flips
the acceptance coin. A rejected round retries with amplified termination credit.
-/

open ProbLang
open scoped ENNReal NNReal

namespace SampLib.BinomialHalfRejection

noncomputable section

open BinomialHalfEnvelope
open BinomialHalfProposal (candidate acceptance kernel factor)

def loop {rT : Type _} (n : ℕ) : Exp rT := pl%
  rec draw u :=
    let block := &Occil.geometric &Occil.fairCoin #();
    let offset := block * #int (width n : ℤ) + &Occil.uniformInt #int (width n : ℤ);
    let candidate := (if &Occil.fairCoin #() then #int (n : ℤ) / #2 + offset
                      else #int (n : ℤ) / #2 - offset - #1);
    if (candidate < #0) || (#int (n : ℤ) < candidate) then draw #() else
      let numerator := &Occil.DiscreteExtra.choose #int (n : ℤ) candidate *
        #int (width n : ℤ);
      let denominator := &Occil.DiscreteExtra.integerPower #2 (#int (n : ℤ) + #2 - block);
      if &Occil.rationalCoin numerator denominator then candidate else draw #()

private theorem loop_lc {rT : Type _} (n : ℕ) :
    (loop (rT := rT) n).IsLocallyClosed := by unfold loop; is_lc

private theorem valid_test (n : ℕ) (c : ℤ) (h : 0 ≤ c ∧ c ≤ n) :
    Bool.or (decide (c < 0)) (decide ((n : ℤ) < c)) = false := by
  simp [not_lt.mpr h.1, not_lt.mpr h.2]

private theorem invalid_test (n : ℕ) (c : ℤ) (h : ¬(0 ≤ c ∧ c ≤ n)) :
    Bool.or (decide (c < 0)) (decide ((n : ℤ) < c)) = true := by
  rcases not_and_or.mp h with h | h <;> simp [lt_of_not_ge h]

private theorem exponent_cast (n : ℕ) (hn : Even n) (block : ℕ) (rank : Fin (width n))
    (sign : Bool) (hvalid : 0 ≤ candidate n (block, rank, sign) ∧
      candidate n (block, rank, sign) ≤ n) :
    (n : ℤ) + 2 - block = ((n + 2 - block : ℕ) : ℤ) := by
  have hb := BinomialHalfProposal.candidate_bounds n (block, rank, sign)
    hvalid.1 hvalid.2
  have := block_le_middle hn hb.1 hb.2
  omega

private theorem power_cast (k : ℕ) : (2 : ℤ) ^ k = ((2 ^ k : ℕ) : ℤ) := by
  norm_cast

attribute [local pl_step_simp]
  BinomialHalfRejectionSyntax.geometric_openRec BinomialHalfRejectionSyntax.geometric_closeRec
  BinomialHalfRejectionSyntax.choose_openRec BinomialHalfRejectionSyntax.choose_closeRec
  BinomialHalfRejectionSyntax.power_openRec BinomialHalfRejectionSyntax.power_closeRec
  UniformInt.uniformInt_openRec UniformInt.uniformInt_closeRec
  FairCoin.fairCoin_openRec FairCoin.fairCoin_closeRec
  RationalCoin.rationalCoin_openRec RationalCoin.rationalCoin_closeRec

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
/-- Definitional alignment, with the normalized conclusion inferred from the proof. -/
abbrev loop_align (E : CoPset) (n : ℕ) (Φ : Val rT → IProp GF) := by
  have h : tglWp (rT := rT) (GF := GF) E pl(&(loop n) #()) Φ ⊢
      tglWp E pl(&(loop n) #()) Φ :=
    BI.BIBase.Entails.refl _
  conv at h =>
    rhs
    simp [loop, Exp.close, Exp.closeRec]
  exact h

omit [ProbLangDist.IsUniformInt rT] in
/-- Align the width returned by the source's square-root call. -/
abbrev loop_sqrt_align (E : CoPset) (n : ℕ) (Φ : Val rT → IProp GF) := by
  have h := loop_align (rT := rT) (GF := GF) E n Φ
  conv at h =>
    rhs
    simp only [width, Nat.cast_add_one]
  exact h

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_candidate (E : CoPset) (n block : ℕ) (rank : Fin (width n))
    (sign : Bool) :
    ⊢ tglWp E pl(if #bool sign then
      #int (n : ℤ) / #2 + #int (block * width n + rank : ℕ)
      else #int (n : ℤ) / #2 - #int (block * width n + rank : ℕ) - #1)
      (fun v : Val rT => iprop(⌜v = Val.int (candidate n (block, rank, sign))⌝)) := by
  cases sign <;> twp_pures <;> twp_value <;> imodintro <;> ipureintro
  · apply Val.ext
    simp only [candidate, Bool.false_eq_true, ↓reduceIte]
    congr 1
  · apply Val.ext
    simp only [candidate, ↓reduceIte]
    congr 1

private theorem coin_spec (E : CoPset) (n : ℕ) (hn : Even n)
    (t : ℕ × (Fin (width n) × Bool)) (hvalid : 0 ≤ candidate n t ∧ candidate n t ≤ n) :
    IsDistSpec (GF := GF) E pl(&Occil.rationalCoin
      #int (Nat.choose n (candidate n t).toNat * width n : ℕ)
      #int (2 ^ (n + 2 - t.1) : ℕ)) (RealCoin.law (bias n hn t)) Val.bool := by
  have hb := BinomialHalfProposal.candidate_bounds n t hvalid.1 hvalid.2
  have hbound := acceptance_bound hn hb.1 hb.2
  have ha : (0 : ℤ) ≤ (Nat.choose n (candidate n t).toNat * width n : ℕ) := by positivity
  have hd : (0 : ℤ) < (2 ^ (n + 2 - t.1) : ℕ) := by positivity
  have hab : ((Nat.choose n (candidate n t).toNat * width n : ℕ) : ℤ) ≤
      (2 ^ (n + 2 - t.1) : ℕ) := by exact_mod_cast hbound
  have heq : RationalCoin.bias _ _ ha hd hab = bias n hn t := by
    apply Subtype.ext
    simp [RationalCoin.bias, bias, acceptance, hvalid]
  rw [← heq]
  exact RationalCoin.rationalCoin_distSpec E _ _ ha hd hab

theorem twp_loop (E : CoPset) (n : ℕ) (hn : Even n) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ k, F k ∂law n) -∗
      tglWp E pl(&(loop n) #())
        (fun v : Val rT => iprop(∃ (k : ℕ), ⌜v = Val.int k⌝ ∗ ↯ (F k))) := by
  have : NeZero (width n) := ⟨Nat.ne_of_gt (width_pos n)⟩
  let coin : Val rT := ⟨Occil.fairCoin, by constructor; is_lc, by is_lc⟩
  have hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #())
      (RealCoin.law VonNeumann.fairBias) Val.bool := FairCoin.fairCoin_distSpec E
  have hgeo := Geometric.geometric_distSpec E VonNeumann.fairBias
    (by norm_num [VonNeumann.fairBias]) coin hcoin
  iapply Retry.twp_loop solve_not_value BinomialHalfProposal.one_lt_factor
  iintro !> %ε %hε IH Hcredit
  iterate 2 twp_pure
  twp_bind pl(&Occil.geometric &Occil.fairCoin #())
  isimp [← proposal_expectation n hn F ε] at Hcredit
  iapply hgeo.wp (blockCredit n F ε) (measurable_of_countable _) _ $$ Hcredit
  iintro %block Hcredit
  isimp only [blockCredit] at Hcredit
  twp_pure
  twp_bind pl(&Occil.uniformInt #int (width n : ℤ))
  iapply (UniformFin.uniformFin_distSpec E (width n)).wp
    (rankCredit n F ε block) (measurable_of_countable _) _ $$ Hcredit
  iintro %rank Hcredit
  isimp only [rankCredit] at Hcredit
  iterate 3 twp_pure
  rw [← Nat.cast_mul, ← Nat.cast_add]
  twp_bind pl(&Occil.fairCoin #())
  iapply hcoin.wp (signCredit n F ε block rank) (measurable_of_countable _) _ $$ Hcredit
  iintro %sign Hcredit
  twp_bind pl(if #bool sign then
    #int (n : ℤ) / #2 + #int (block * width n + rank : ℕ)
    else #int (n : ℤ) / #2 - #int (block * width n + rank : ℕ) - #1)
  iapply tglWp_wand
  isplitl []
  · iapply twp_candidate E n block rank sign
  iintro %v %hv
  subst v
  twp_pure
  iterate 3 twp_pure
  by_cases hvalid : 0 ≤ candidate n (block, rank, sign) ∧
      candidate n (block, rank, sign) ≤ n
  · rw [valid_test n _ hvalid]
    twp_pure
    twp_bind pl(&Occil.DiscreteExtra.choose #int (n : ℤ)
      #int (candidate n (block, rank, sign)))
    iapply tglWp_wand
    isplitl []
    · rw [← Int.toNat_of_nonneg hvalid.1]
      iapply twp_integerChoose E n (candidate n (block, rank, sign)).toNat
    iintro %v %hv
    subst v
    iterate 4 twp_pure
    rw [← Nat.cast_mul, exponent_cast n hn block rank sign hvalid]
    twp_bind pl(&Occil.DiscreteExtra.integerPower #2 #int (n + 2 - block : ℕ))
    iapply tglWp_wand
    isplitl []
    · iapply twp_integerPower E 2 (n + 2 - block)
    iintro %v %hv
    subst v
    twp_pure
    rw [power_cast]
    twp_bind pl(&Occil.rationalCoin
      #int (Nat.choose n (candidate n (block, rank, sign)).toNat * width n : ℕ)
      #int (2 ^ (n + 2 - block) : ℕ))
    isimp only [signCredit, ← coin_expectation n hn F ε (block, rank, sign)] at Hcredit
    iapply (coin_spec E n hn (block, rank, sign) hvalid).wp
      (coinCredit n F ε (block, rank, sign)) (measurable_of_countable _) _ $$ Hcredit
    iintro %accepted Hcredit
    cases accepted
    · twp_pure
      isimp only [coinCredit, Bool.false_eq_true, ↓reduceIte] at Hcredit
      iapply loop_align E n
        (fun v : Val rT => iprop(∃ (k : ℕ), ⌜v = Val.int k⌝ ∗ ↯ (F k)))
      iapply IH $$ Hcredit
    · twp_pure
      twp_value
      imodintro
      iexists (candidate n (block, rank, sign)).toNat
      isimp only [coinCredit, ↓reduceIte] at Hcredit
      iframe Hcredit
      ipureintro
      exact congrArg Val.int (Int.toNat_of_nonneg hvalid.1).symm
  · rw [invalid_test n _ hvalid]
    twp_pure
    isimp only [signCredit, rejected_credit n F ε _ hvalid] at Hcredit
    iapply loop_align E n
      (fun v : Val rT => iprop(∃ (k : ℕ), ⌜v = Val.int k⌝ ∗ ↯ (F k)))
    iapply IH $$ Hcredit

end specification

end

end SampLib.BinomialHalfRejection
