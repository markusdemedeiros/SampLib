import SampLib.Weighted.Support.SuccinctChoice
import SampLib.Weighted.Laws.EnvelopeRejection

/-! # Dense and packed proposal loops for succinct categorical choice

Both loops propose a uniform index, read its weight, and share one rational acceptance
step. The packed loop decodes the weight from its 20-bit or 32-bit field first.
-/

open ProbLang
open scoped ENNReal NNReal

namespace SampLib.SuccinctChoice

noncomputable section

theorem length_pos (ws : List ℕ) (ht : 0 < ws.sum) : 0 < ws.length :=
  List.length_pos_of_sum_ne_zero ws ht.ne'

theorem offset_cast (ws : List ℕ) (i : ℕ) :
    32 * (PackedWeights.wideBefore ws i : ℤ) +
      20 * ((i : ℤ) - PackedWeights.wideBefore ws i) =
      ((32 * PackedWeights.wideBefore ws i +
        20 * (i - PackedWeights.wideBefore ws i) : ℕ) : ℤ) := by
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul,
    Nat.cast_sub (PackedWeights.wideBefore_le ws i)]
  rfl

theorem flag_test {rT : Type} [BEq rT] (ws : List ℕ) (i : ℕ) (hi : i < ws.length) :
    ((BaseLit.int (((PackedWeights.mask ws : ℤ) / 2 ^ i) % 2) : BaseLit rT) == .int 1) =
      decide (PackedWeights.Wide ws[i]) := by
  have h : (((PackedWeights.mask ws : ℤ) / 2 ^ i) % 2) = (PackedWeights.flag ws[i] : ℤ) := by
    exact_mod_cast PackedWeights.mask_bit ws i hi
  change ((((PackedWeights.mask ws : ℤ) / 2 ^ i) % 2) == (1 : ℤ)) = _
  rw [h]
  by_cases hw : PackedWeights.Wide ws[i] <;> simp [PackedWeights.flag, hw]

theorem decode_cast (ws : List ℕ) (hfit : ∀ w ∈ ws, w < 2 ^ 32)
    (i : ℕ) (hi : i < ws.length) :
    ((PackedWeights.bits ws : ℤ) /
      2 ^ (32 * PackedWeights.wideBefore ws i + 20 * (i - PackedWeights.wideBefore ws i))) %
        2 ^ PackedWeights.width ws[i] = (ws.get ⟨i, hi⟩ : ℤ) := by
  have h := PackedWeights.decode ws hfit i hi
  rw [PackedWeights.decoded_width ws i hi] at h
  exact_mod_cast h

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open scoped SampLib.SuccinctChoice.Program
open WeightedRejection (factor coinCredit proposalCredit)

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec Program.weights_closeRec

omit [ProbLangDist.IsUniformInt rT] in
theorem twp_width (E : CoPset) (w : ℕ) :
    ⊢ tglWp E pl(if #bool (decide (PackedWeights.Wide w)) then #32 else #20)
      (fun v : Val rT => iprop(⌜v = Val.int (PackedWeights.width w : ℤ)⌝)) := by
  by_cases h : PackedWeights.Wide w
  · rw [decide_eq_true h]
    twp_pures
    twp_value
    imodintro
    ipureintro
    simp only [PackedWeights.width, ite_eq_left h, Nat.cast_ofNat]
  · rw [decide_eq_false h]
    twp_pures
    twp_value
    imodintro
    ipureintro
    simp only [PackedWeights.width, ite_eq_right h, Nat.cast_ofNat]

/-- Both representations share the same rational acceptance and retry step. -/
theorem twp_accept (E : CoPset) (ws : List ℕ) (m : ℕ) (hm : 0 < m)
    (hbound : ∀ w ∈ ws, w ≤ m) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞)
    (i : Fin ws.length) (retry : Exp rT) :
    ⊢ (↯ (factor ws m * ε) -∗ ↯ (∫⁻ j, F j ∂WeightedChoice.law ws) -∗
        tglWp E pl(&retry #())
          (fun v => iprop(∃ j : ℕ, ⌜v = Val.int (j : ℤ)⌝ ∗ ↯ (F j)))) -∗
      ↯ (proposalCredit ws m F ε i) -∗
      tglWp E pl(if &Occil.rationalCoin #int (ws.get i : ℤ) #int (m : ℤ)
        then #int (i.val : ℤ) else &retry #())
        (fun v => iprop(∃ j : ℕ, ⌜v = Val.int (j : ℤ)⌝ ∗ ↯ (F j))) := by
  have hcoin := RationalCoin.rationalCoin_distSpec (rT := rT) (GF := GF) E
    (ws.get i) m (Int.natCast_nonneg _) (by exact_mod_cast hm)
    (by exact_mod_cast hbound _ (List.get_mem ..))
  iintro Hretry Hcredit
  twp_bind pl(&Occil.rationalCoin #int (ws.get i : ℤ) #int (m : ℤ))
  isimp only [← EnvelopeRejection.coin_expectation ws m hm hbound F ε i,
    ← RealCoin.lintegral_law] at Hcredit
  iapply (hcoin.wp (coinCredit ws m F ε i) (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  cases b with
  | false =>
    twp_pure
    isimp only [coinCredit, Bool.false_eq_true, ite_false] at Hcredit
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    iapply Hretry $$ Hterm Hcredit
  | true =>
    twp_pure
    twp_value
    imodintro
    iexists i.val
    isplit
    · ipureintro
      rfl
    isimp only [coinCredit, ite_true] at Hcredit
    iexact Hcredit

/-- Direct uniform-index proposals with the common envelope credit. -/
theorem twp_dense (E : CoPset) (ws : List ℕ) (m : ℕ) (ht : 0 < ws.sum)
    (hm : 0 < m) (hbound : ∀ w ∈ ws, w ≤ m) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law ws) -∗
      tglWp E pl(&(Program.dense ws (m : ℤ)) #())
        (fun v => iprop(∃ i : ℕ, ⌜v = Val.int (i : ℤ)⌝ ∗ ↯ (F i))) := by
  have hn := length_pos ws ht
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε (EnvelopeRejection.one_lt_factor ws m hn hm) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  iterate 2 twp_pure
  twp_bind pl(&Occil.uniformInt #int (ws.length : ℤ))
  icombine Hcredit Hterm as Htotal
  ihave Hsample := ErrorCredit.weaken
    (WeightedRejection.expectation ws m ht hm hbound F ε) $$ Htotal
  iapply tglWp_wand
  isplitl [Hsample]
  · iapply UniformInt.twp_uniformInt E ws.length hn (proposalCredit ws m F ε) $$ Hsample
  iintro %v ⟨%i, %hv, %hi, Hcredit⟩
  subst v
  twp_pure
  twp_bind pl(&Occil.getAt &(listVal (fun n : ℕ => Val.int n) ws).fst #int (i : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply twp_getAt E (fun n : ℕ => Val.int n) ws ⟨i, hi⟩
  iintro %v %hv
  subst v
  isimp only [Exp.ofVal]
  iapply twp_accept E ws m hm hbound F ε ⟨i, hi⟩ (Program.dense ws (m : ℤ)) $$ IH Hcredit

/-- Packed proposals decode the same weight before using the same acceptance rule. -/
theorem twp_packed (E : CoPset) (ws : List ℕ) (m : ℕ) (ht : 0 < ws.sum)
    (hm : 0 < m) (hbound : ∀ w ∈ ws, w ≤ m) (hfit : ∀ w ∈ ws, w < 2 ^ 32)
    (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law ws) -∗
      tglWp E pl(&(Program.packed (ws.length : ℤ) (m : ℤ)
        (PackedWeights.bits ws : ℤ) (PackedWeights.mask ws : ℤ)) #())
        (fun v => iprop(∃ i : ℕ, ⌜v = Val.int (i : ℤ)⌝ ∗ ↯ (F i))) := by
  have hn := length_pos ws ht
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε (EnvelopeRejection.one_lt_factor ws m hn hm) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  iterate 2 twp_pure
  twp_bind pl(&Occil.uniformInt #int (ws.length : ℤ))
  icombine Hcredit Hterm as Htotal
  ihave Hsample := ErrorCredit.weaken
    (WeightedRejection.expectation ws m ht hm hbound F ε) $$ Htotal
  iapply tglWp_wand
  isplitl [Hsample]
  · iapply UniformInt.twp_uniformInt E ws.length hn (proposalCredit ws m F ε) $$ Hsample
  iintro %v ⟨%i, %hv, %hi, Hcredit⟩
  subst v
  twp_pure
  twp_bind pl(&Program.count #int (i : ℤ) #int (PackedWeights.mask ws : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply twp_count E i (PackedWeights.mask ws)
  iintro %v %hv
  subst v
  rw [← PackedWeights.wideBefore]
  iterate 6 twp_pure
  rw [offset_cast ws i]
  twp_bind pl(&Occil.Weighted.integerPower #2 #int (i : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply WeightedIntegerPower.twp_integerPower E 2 i
  iintro %v %hv
  subst v
  iterate 2 twp_pure
  twp_bind pl(#int (((PackedWeights.mask ws : ℤ) / 2 ^ i) % 2) = #1)
  iapply tglWp_wand
  isplitl []
  · iapply KnownIntegerComparison.twp_eq E (((PackedWeights.mask ws : ℤ) / 2 ^ i) % 2) 1
      (decide (PackedWeights.Wide ws[i])) (flag_test (rT := rT) ws i hi)
  iintro %v %hv
  subst v
  twp_bind pl(if #bool (decide (PackedWeights.Wide ws[i])) then #32 else #20)
  iapply tglWp_wand
  isplitl []
  · iapply twp_width E ws[i]
  iintro %v %hv
  subst v
  twp_pure
  twp_bind pl(&Occil.Weighted.integerPower #2 #int (PackedWeights.width ws[i] : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply WeightedIntegerPower.twp_integerPower E 2 (PackedWeights.width ws[i])
  iintro %v %hv
  subst v
  twp_bind pl(&Occil.Weighted.integerPower #2
    #int ((32 * PackedWeights.wideBefore ws i + 20 * (i - PackedWeights.wideBefore ws i) : ℕ) : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply WeightedIntegerPower.twp_integerPower E 2
      (32 * PackedWeights.wideBefore ws i + 20 * (i - PackedWeights.wideBefore ws i))
  iintro %v %hv
  subst v
  iterate 3 twp_pure
  rw [decode_cast ws hfit i hi]
  iapply twp_accept E ws m hm hbound F ε ⟨i, hi⟩
    (Program.packed (ws.length : ℤ) (m : ℤ) (PackedWeights.bits ws : ℤ)
      (PackedWeights.mask ws : ℤ)) $$ IH Hcredit

end specification

end

end SampLib.SuccinctChoice
