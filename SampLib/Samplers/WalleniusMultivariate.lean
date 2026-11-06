import SampLib.Distributions.Wallenius
import SampLib.NatUrnOps
import SampLib.SupportedSpec
import SampLib.Syntax.Urns
import SampLib.ProofMode.BindFrom

/-! # Weighted sampling without replacement from a multicolor urn -/

open ProbLang
open scoped ENNReal SampLib.UrnTerms

namespace SampLib.WalleniusMultivariate

noncomputable section

private def loop {rT : Type _} [ProbLangℝ rT] (odds : List ℕ) : Exp rT := pl%
  rec take remaining population result :=
    if remaining = #0 then result else
      let color := &Occil.weightedChoice
        (&Occil.DiscreteExtra.urnWeights population &(NatCounters.encode odds).fst);
      take (remaining - #1) (&Occil.DiscreteExtra.adjustCounter population color (-#1))
        (&Occil.DiscreteExtra.incrementCounter result color)

section mathematics

open MeasureTheory

private theorem add_zeros_left (xs : List ℕ) :
    List.zipWith (· + ·) (List.replicate xs.length 0) xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs IH =>
    simpa only [List.length_cons, List.replicate_succ, List.zipWith_cons_cons, Nat.zero_add]
      using congrArg (List.cons x) IH

private theorem initial_credit (n : ℕ) (pop odds : List ℕ) (F : List ℕ → ℝ≥0∞) :
    Wallenius.credit n pop odds (List.replicate pop.length 0) F =
      ∫⁻ ys, F ys ∂Wallenius.law n pop odds := by
  rw [Wallenius.credit]
  apply lintegral_congr_ae
  filter_upwards [Wallenius.support_length n pop odds] with ys hys
  rw [← hys, add_zeros_left]

end mathematics

private theorem request_test (n : ℕ) (pop : List ℕ) (hn : n ≤ pop.sum) :
    decide ((pop.sum : ℤ) < (n : ℤ)) = false :=
  decide_eq_false (by exact_mod_cast not_lt.mpr hn)

private theorem index_acc (pop acc : List ℕ) (i : ℕ) (hlen : acc.length = pop.length)
    (hi : i < pop.length) : i < acc.length := by omega

private theorem positive_at (pop : List ℕ) (i : ℕ) (hi : i < pop.length)
    (hp : 0 < pop[i]?.getD 0) : 0 < pop[i] := by
  simpa [List.getElem?_eq_getElem hi] using hp

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_loop (E : CoPset) (n : ℕ) (pop odds acc : List ℕ)
    (hn : n ≤ pop.sum) (hlen : pop.length = odds.length) (hodds : ∀ o ∈ odds, 0 < o)
    (hacc : acc.length = pop.length) (F : List ℕ → ℝ≥0∞) :
    ⊢ ↯ (Wallenius.credit n pop odds acc F) -∗
      tglWp E pl(&(loop odds) #int (n : ℤ) &(NatCounters.encode pop).fst
        &(NatCounters.encode acc).fst)
        (fun v : Val rT => iprop(∃ ys : List ℕ, ⌜v = NatCounters.encode ys⌝ ∗ ↯ (F ys))) := by
  induction n generalizing pop acc with
  | zero =>
    iintro Hcredit
    isimp [loop, Exp.close, Exp.closeRec, ClosedExp.openRec, ClosedExp.closeRec]
    twp_pures
    iapply (tglWp_value_of_toVal (Val.toVal?_fst (NatCounters.encode acc)))
    iexists acc
    isimp only [Wallenius.credit_zero pop odds acc hacc F] at Hcredit
    iframe Hcredit
    itrivial
  | succ n IH =>
    have hs := Wallenius.request_weight_pos pop odds n hn hlen hodds
    let : NeZero (Wallenius.weights pop odds).sum := ⟨hs.ne'⟩
    have hweights := NatUrnOps.twp_urnWeights (rT := rT) (GF := GF) E pop odds hlen.le
    iintro Hcredit
    isimp [loop, Exp.close, Exp.closeRec, ClosedExp.openRec, ClosedExp.closeRec]
    iterate 6 twp_pure
    simp only [ClosedExp.openRec]
    twp_bind_from hweights
    iapply tglWp_wand
    isplitl []
    · iapply hweights
    iintro %v %hv
    subst v
    twp_bind pl(&Occil.weightedChoice &(NatCounters.encode (Wallenius.weights pop odds)).fst)
    isimp only [← Wallenius.first_color_expectation pop odds n hn hlen hodds acc F] at Hcredit
    iapply ((WeightedChoice.weightedChoice_distSpec E (Wallenius.weights pop odds)).wp_supported
      (fun i => i < pop.length ∧ 0 < pop[i]?.getD 0) (Set.to_countable _).measurableSet
      (Wallenius.selected pop odds hlen)
      (fun i => Wallenius.credit n (Wallenius.decrement pop i) odds (Wallenius.increment acc i) F)
      (measurable_of_countable _) _) $$ Hcredit
    iintro %i %hi Hcredit
    have hinc := NatCounters.twp_incrementCounter (rT := rT) (GF := GF) E acc i
      (index_acc pop acc i hacc hi.1)
    have hdec := NatCounters.twp_decrementCounter (rT := rT) (GF := GF) E pop i hi.1
      (positive_at pop i hi.1 hi.2)
    have hnext := IH (pop := Wallenius.decrement pop i) (acc := Wallenius.increment acc i)
      (Wallenius.remaining_request pop i n hi.2 hn) (by simpa [Wallenius.decrement] using hlen)
      (by simpa [Wallenius.decrement, Wallenius.increment] using hacc)
    simp [loop, Exp.close, Exp.closeRec, ClosedExp.closeRec] at hnext
    twp_pure
    twp_bind_from hinc
    iapply tglWp_wand
    isplitl []
    · iapply hinc
    iintro %v %hv
    subst v
    twp_pure
    twp_bind_from hdec
    iapply tglWp_wand
    isplitl []
    · iapply hdec
    iintro %v %hv
    subst v
    twp_pure
    rw [add_sub_cancel_right]
    simp only [ClosedExp.openRec, Exp.ofVal]
    iapply hnext $$ Hcredit

/-- Validate the urn, initialize its counts, and preserve the canonical Wallenius expectation. -/
theorem twp_walleniusMultivariate (E : CoPset) (n : ℕ) (pop odds : List ℕ)
    (hn : n ≤ pop.sum) (hlen : pop.length = odds.length) (hodds : ∀ o ∈ odds, 0 < o)
    (F : List ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ ys, F ys ∂Wallenius.law n pop odds) -∗
      tglWp E pl(&Occil.DiscreteExtra.walleniusMultivariate #int (n : ℤ)
        &(NatCounters.encode pop).fst &(NatCounters.encode odds).fst)
        (fun v : Val rT => iprop(∃ ys : List ℕ, ⌜v = NatCounters.encode ys⌝ ∗ ↯ (F ys))) := by
  have hloop := twp_loop (rT := rT) (GF := GF) E n pop odds
    (List.replicate pop.length 0) hn hlen hodds (by simp) F
  simp [loop, Exp.close, Exp.closeRec, ClosedExp.closeRec] at hloop
  have hvalid := NatUrnOps.twp_validUrn (rT := rT) (GF := GF) E pop odds hlen hodds
  iintro Hcredit
  isimp [Occil.DiscreteExtra.walleniusMultivariate, Exp.close, Exp.closeRec,
    ClosedExp.openRec, ClosedExp.closeRec]
  iterate 3 twp_pure
  twp_bind pl(&Occil.sumInts &(NatCounters.encode pop).fst)
  iapply tglWp_wand
  isplitl []
  · iapply WeightedChoice.twp_sumInts E pop
  iintro %v %hv
  subst v
  twp_pures
  rw [request_test n pop hn, Bool.false_or]
  twp_pure
  twp_bind_from hvalid
  iapply tglWp_wand
  isplitl []
  · iapply hvalid
  iintro %v %hv
  subst v
  iterate 2 twp_pure
  simp only [ClosedExp.openRec]
  twp_bind pl(&Occil.length &(NatCounters.encode pop).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_length E _ pop
  iintro %v %hv
  subst v
  twp_bind pl(&Occil.DiscreteExtra.zeroCounters #int (pop.length : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply NatCounters.twp_zeroCounters E pop.length
  iintro %v %hv
  subst v
  simp only [Exp.ofVal]
  isimp only [← initial_credit n pop odds F] at Hcredit
  iapply hloop $$ Hcredit

/-- Exact multicolor Wallenius counts on the full natural finite-urn domain. -/
theorem walleniusMultivariate_distSpec (E : CoPset) (n : ℕ) (pop odds : List ℕ)
    (hn : n ≤ pop.sum) (hlen : pop.length = odds.length) (hodds : ∀ o ∈ odds, 0 < o) :
    IsDistSpec (GF := GF) E pl(&Occil.DiscreteExtra.walleniusMultivariate #int (n : ℤ)
      &(NatCounters.encode pop).fst &(NatCounters.encode odds).fst)
      (Wallenius.law n pop odds) NatCounters.encode where
  spec F _ := wand_entails (twp_walleniusMultivariate E n pop odds hn hlen hodds F)

end specification

end

end SampLib.WalleniusMultivariate
