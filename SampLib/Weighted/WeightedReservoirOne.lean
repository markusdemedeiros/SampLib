import SampLib.Weighted.Laws.WeightedReservoirOne
import SampLib.Common.WeightedValidation
import SampLib.Uniform.RationalCoin
import SampLib.Common.Laws.Urn
import Samplers.Weighted.Reservoir

/-! # One-item weighted reservoirs

A previously selected label represents one virtual item carrying all previously seen
weight. The remaining items compete with that item by their own weights.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.WeightedReservoirOne

noncomputable section

private def loop {rT : Type _} : Exp rT := pl%
  rec visit xs total selected index := case! xs
    | inl(v) => selected
    | inr(p) =>
      let next := total + fst(p);
      if next = #0 then visit (snd(p)) next selected (index + #1) else
        if &Occil.rationalCoin (fst(p)) next then
          visit (snd(p)) next index (index + #1)
        else visit (snd(p)) next selected (index + #1)

private theorem int_beq {rT : Type _} [BEq rT] (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = (a == b) := rfl

private theorem zero_test (total w : ℕ) (hz : total + w = 0) :
    ((total : ℤ) + w == 0) = true := by
  have h : (total : ℤ) + w = 0 := by exact_mod_cast hz
  simp [h]

private theorem positive_test (total w : ℕ) (hz : total + w ≠ 0) :
    ((total : ℤ) + w == 0) = false := by
  apply beq_eq_false_iff_ne.mpr
  omega

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem coin_distSpec (E : CoPset) (total w : ℕ) (hp : 0 < total + w) :
    IsDistSpec (rT := rT) (GF := GF) E
      pl(&Occil.rationalCoin #int (w : ℤ) #int ((total : ℤ) + w))
      (RealCoin.law (Urn.bias w total)) Val.bool := by
  have hp' : 0 < w + total := by omega
  have ha : (0 : ℤ) ≤ w := by omega
  have hd : (0 : ℤ) < (total : ℤ) + w := by exact_mod_cast hp
  have hab : (w : ℤ) ≤ (total : ℤ) + w := by omega
  have hb : Urn.bias w total = RationalCoin.bias w ((total : ℤ) + w) ha hd hab := by
    apply Subtype.ext
    simp only [Urn.bias, dite_eq_left hp', RationalCoin.bias,
      Int.cast_add, Int.cast_natCast]
    rw [add_comm (w : ℝ) (total : ℝ)]
  rw [hb]
  exact RationalCoin.rationalCoin_distSpec E w ((total : ℤ) + w) ha hd hab

private theorem twp_loop (E : CoPset) (ws : List ℕ) (total : ℕ)
    (selected : ℤ) (offset : ℕ) (hs : 0 < total + ws.sum) (F : ℤ → ℝ≥0∞) :
    ⊢ ↯ (credit total selected ws offset F) -∗
      tglWp E pl(&loop &(listVal (fun n : ℕ => Val.int n) ws).fst
        #int (total : ℤ) #int selected #int (offset : ℤ))
        (fun v : Val rT => iprop(∃ i : ℤ, ⌜v = Val.int i⌝ ∗ ↯ (F i))) := by
  induction ws generalizing total selected offset with
  | nil =>
    have hp : 0 < total := by simpa using hs
    iintro Hcredit
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    iexists selected
    isimp only [credit_nil total selected hp offset F] at Hcredit
    iframe Hcredit
    itrivial
  | cons w ws ih =>
    iintro Hcredit
    simp only [listVal]
    simp [loop, Exp.close, Exp.closeRec]
    twp_pures
    rw [int_beq]
    by_cases hz : total + w = 0
    · rw [zero_test total w hz]
      isimp only [zero_step total w selected ws offset hz F] at Hcredit
      iterate 3 twp_pure
      have hrec := ih (total + w) selected (offset + 1)
        (by simpa [List.sum_cons, Nat.add_assoc] using hs)
      simp [loop, Exp.close, Exp.closeRec] at hrec
      isimp [Exp.ofVal]
      iapply hrec $$ Hcredit
    · rw [positive_test total w hz]
      have hp : 0 < total + w := Nat.pos_of_ne_zero hz
      twp_pure
      simp only [RationalCoin.rationalCoin_openRec]
      twp_pure
      twp_bind pl(&Occil.rationalCoin #int (w : ℤ) #int ((total : ℤ) + w))
      isimp only [← expectation total w selected ws offset hp F,
        ← RealCoin.lintegral_law] at Hcredit
      iapply ((coin_distSpec E total w hp).wp (continuation total w selected ws offset F)
        (measurable_of_countable _) _) $$ Hcredit
      iintro %b Hcredit
      cases b
      · isimp only [continuation, Bool.false_eq_true, ite_false] at Hcredit
        iterate 3 twp_pure
        have hrec := ih (total + w) selected (offset + 1)
          (by simpa [List.sum_cons, Nat.add_assoc] using hs)
        simp [loop, Exp.close, Exp.closeRec] at hrec
        isimp [Exp.ofVal]
        iapply hrec $$ Hcredit
      · isimp only [continuation, ite_true] at Hcredit
        iterate 3 twp_pure
        have hrec := ih (total + w) (offset : ℤ) (offset + 1)
          (by simpa [List.sum_cons, Nat.add_assoc] using hs)
        simp [loop, Exp.close, Exp.closeRec] at hrec
        isimp [Exp.ofVal]
        iapply hrec $$ Hcredit

/-- The returned integer label has probability proportional to its input weight. -/
theorem weightedReservoirOne_distSpec (E : CoPset) (ws : List ℕ) [NeZero ws.sum] :
    IsDistSpec (GF := GF) E pl(&Occil.Weighted.weightedReservoirOne
      &(listVal (fun n : ℕ => Val.int n) ws).fst #()) (law ws) Val.int := by
  refine ⟨fun F _ => ?_⟩
  have hloop := twp_loop (rT := rT) (GF := GF) E ws 0 (-1) 0
    (by simpa using NeZero.pos ws.sum) F
  simp [loop, Exp.close, Exp.closeRec] at hloop
  iintro Hcredit
  isimp only [← initial_credit] at Hcredit
  iterate 2 twp_pure
  twp_bind pl(&Occil.Weighted.validWeights &(listVal (fun n : ℕ => Val.int n) ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply WeightedValidation.twp_validWeights E ws (NeZero.pos ws.sum)
  iintro %v %hv
  subst v
  iterate 2 twp_pure
  isimp [Exp.ofVal]
  iapply hloop $$ Hcredit

end specification

end

end SampLib.WeightedReservoirOne
