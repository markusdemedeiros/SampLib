import SampLib.SortedChoicePreparation
import SampLib.Distributions.SortedEnvelope
import SampLib.Samplers.InclusiveOffset
import SampLib.Distributions.IntegerIntervals
import SampLib.Distributions.WeightedSupport
import SampLib.Distributions.WeightedPositiveSupport

/-! # CTE verification of sorted dyadic categorical rejection -/

open ProbLang
open scoped ENNReal NNReal

namespace SampLib.SortedChoice

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open scoped SampLib.SortedChoice.Program

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec Program.weights_closeRec

omit [ProbLangDist.IsUniformInt rT] in
/-- The source's proposal index reverses the offset in the ascending orientation. -/
private theorem twp_index (E : CoPset) (n k r : ℕ) (asc : Bool) (hk : k < n.size)
    (hr : r < DyadicGroups.width n k) :
    ⊢ tglWp E pl(if #bool asc
        then #int (n : ℤ) - #1 - #int ((DyadicGroups.lower k : ℤ) + r - 1)
        else #int ((DyadicGroups.lower k : ℤ) + r - 1))
      (fun v : Val rT => iprop(⌜v = Val.int
        (SortedWeights.index n asc (GroupedEnvelope.position k r) : ℤ)⌝)) := by
  have ho := DyadicGroups.offset_lt n k r hk hr
  have hl := DyadicGroups.lower_pos k
  cases asc <;> twp_pures <;> twp_value <;> imodintro <;> ipureintro
  · change Val.int ((DyadicGroups.lower k : ℤ) + r - 1) =
      Val.int ((DyadicGroups.lower k - 1 + r : ℕ) : ℤ)
    congr 1
    omega
  · change Val.int ((n : ℤ) - 1 - ((DyadicGroups.lower k : ℤ) + r - 1)) =
      Val.int ((n - 1 - (DyadicGroups.lower k - 1 + r) : ℕ) : ℤ)
    congr 1
    omega

/-- A proposal is accepted with probability weight/envelope; rejection pays for a retry. -/
private theorem twp_accept (E : CoPset) (ws : List ℕ) (asc : Bool)
    (hs : ws.Pairwise (SortedWeights.Ordered asc)) (k r : ℕ) (hk : k < ws.length.size)
    (hr : r < DyadicGroups.width ws.length k) (he : 0 < SortedWeights.envelope ws asc k)
    (F : ℕ → ℝ≥0∞) (R : ℝ≥0∞) (retry : Exp rT) :
    ⊢ (↯ R -∗ tglWp E pl(&retry #())
        (fun v => iprop(∃ i : ℕ, ⌜v = Val.int (i : ℤ)⌝ ∗ ↯ (F i)))) -∗
      ↯ (GroupedEnvelope.candidateCredit ws.length (SortedWeights.value ws asc)
        (SortedWeights.envelope ws asc) (fun i => F (SortedWeights.index ws.length asc i))
        R k r) -∗
      tglWp E pl(if &Occil.rationalCoin
          (&Occil.getAt &(listVal (fun n : ℕ => Val.int n) ws).fst
            #int (SortedWeights.index ws.length asc (GroupedEnvelope.position k r) : ℤ))
          (&Occil.getAt &(listVal (fun n : ℕ => Val.int n) ws).fst
            #int (SortedWeights.pivot ws.length asc k : ℤ))
        then #int (SortedWeights.index ws.length asc (GroupedEnvelope.position k r) : ℤ)
        else &retry #())
        (fun v => iprop(∃ i : ℕ, ⌜v = Val.int (i : ℤ)⌝ ∗ ↯ (F i))) := by
  have hi : SortedWeights.index ws.length asc (GroupedEnvelope.position k r) < ws.length :=
    SortedWeights.index_lt _ _ asc (DyadicGroups.offset_lt ws.length k r hk hr)
  have hp := SortedWeights.pivot_lt ws.length k asc hk
  have hw := SortedWeights.envelope_bound ws asc hs k r hk hr
  have hcoin := RationalCoin.rationalCoin_distSpec (rT := rT) (GF := GF) E
    (SortedWeights.value ws asc (GroupedEnvelope.position k r))
    (SortedWeights.envelope ws asc k) (Int.natCast_nonneg _) (by exact_mod_cast he)
    (by exact_mod_cast hw)
  iintro Hretry Hcredit
  twp_bind pl(&Occil.getAt &(listVal (fun n : ℕ => Val.int n) ws).fst
    #int (SortedWeights.pivot ws.length asc k : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply twp_getAt E (fun n : ℕ => Val.int n) ws ⟨_, hp⟩
  iintro %v %hv
  subst v
  twp_bind pl(&Occil.getAt &(listVal (fun n : ℕ => Val.int n) ws).fst
    #int (SortedWeights.index ws.length asc (GroupedEnvelope.position k r) : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply twp_getAt E (fun n : ℕ => Val.int n) ws ⟨_, hi⟩
  iintro %v %hv
  subst v
  have hvalue : ws.get ⟨_, hi⟩ = SortedWeights.value ws asc (GroupedEnvelope.position k r) := by
    simp [SortedWeights.value, List.getElem?_eq_getElem hi]
  have henvelope : ws.get ⟨_, hp⟩ = SortedWeights.envelope ws asc k := by
    simp [SortedWeights.envelope, List.getElem?_eq_getElem hp]
  simp only [Exp.ofVal, hvalue, henvelope]
  twp_bind pl(&Occil.rationalCoin
    #int (SortedWeights.value ws asc (GroupedEnvelope.position k r) : ℤ)
    #int (SortedWeights.envelope ws asc k : ℤ))
  isimp only [← GroupedEnvelope.candidate_coin ws.length _ _ _ R k r he hw,
    ← RealCoin.lintegral_law] at Hcredit
  iapply (hcoin.wp _ (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  cases b with
  | false =>
    twp_pure
    isimp only [Bool.false_eq_true, ite_false] at Hcredit
    iapply Hretry $$ Hcredit
  | true =>
    twp_pure
    isimp only [ite_true] at Hcredit
    twp_value
    imodintro
    iexists SortedWeights.index ws.length asc (GroupedEnvelope.position k r)
    iframe Hcredit
    itrivial

/-- The group callback is used conditionally on every retry. -/
theorem twp_loop (E : CoPset) (ws : List ℕ) (asc : Bool) [NeZero ws.sum]
    [NeZero (envelopes ws asc).sum] (hs : ws.Pairwise (SortedWeights.Ordered asc))
    (hdraw : IsDistSpec (GF := GF) E
      pl(&Occil.Weighted.fastLoadedDiceRoller
        &(listVal (fun n : ℕ => Val.int n) (envelopes ws asc)).fst #())
      (WeightedChoice.law (envelopes ws asc)) (fun k => Val.int (k : ℤ)))
    (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law ws) -∗
      tglWp E pl(&(Program.loop ws (envelopes ws asc) asc) #())
        (fun v => iprop(∃ i : ℕ, ⌜v = Val.int (i : ℤ)⌝ ∗ ↯ (F i))) := by
  have ht : 0 < ws.sum := Nat.pos_of_ne_zero (NeZero.ne _)
  have htotal : 0 < envelopeTotal ws asc := by
    simpa only [GroupedEnvelope.masses_sum] using envelopes_pos ws asc ht hs
  have hsupport := (WeightedChoice.ae_lt_length (envelopes ws asc)).and
    (WeightedChoice.ae_pos_weight (envelopes ws asc))
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε (GroupedEnvelope.one_lt_factor _ htotal) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  iterate 2 twp_pure
  twp_bind pl(&Occil.Weighted.fastLoadedDiceRoller
    &(listVal (fun n : ℕ => Val.int n) (envelopes ws asc)).fst #())
  icombine Hcredit Hterm as Htotal
  ihave Hsample := ErrorCredit.weaken (expectation_preservation ws asc ht hs F ε) $$ Htotal
  iapply (hdraw.wp_supported
    (fun k => k < (envelopes ws asc).length ∧ 0 < (envelopes ws asc)[k]?.getD 0)
    (Set.to_countable _).measurableSet hsupport (groupCredit ws asc F ε)
    (measurable_of_countable _) _) $$ Hsample
  iintro %k %hk Hcredit
  have hkn : k < ws.length.size := by simpa only [GroupedEnvelope.masses_length] using hk.1
  have he : 0 < SortedWeights.envelope ws asc k := by
    have hm : 0 < GroupedEnvelope.mass ws.length (SortedWeights.envelope ws asc) k := by
      simpa [envelopes, GroupedEnvelope.masses, hkn] using hk.2
    exact Nat.pos_of_mul_pos_left hm
  twp_pure
  twp_bind pl(&Occil.Weighted.integerPower #2 #int (k : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply WeightedIntegerPower.twp_integerPower E 2 k
  iintro %v %hv
  subst v
  have hpow : (2 : ℤ) ^ k = (DyadicGroups.lower k : ℤ) := by simp [DyadicGroups.lower]
  rw [hpow]
  twp_pure
  twp_bind pl(if #int (ws.length : ℤ) < #2 * #int (DyadicGroups.lower k : ℤ) - #1
    then #int (ws.length : ℤ) else #2 * #int (DyadicGroups.lower k : ℤ) - #1)
  iapply tglWp_wand
  isplitl []
  · iapply twp_upper E ws.length (DyadicGroups.lower k) (DyadicGroups.lower_pos k)
  iintro %v %hv
  subst v
  have hu : min ws.length (2 * DyadicGroups.lower k - 1) = DyadicGroups.upper ws.length k := by
    simp [DyadicGroups.upper, DyadicGroups.lower, pow_succ, mul_comm]
  rw [hu]
  twp_pure
  twp_bind pl(&Occil.rndIntRange #int (DyadicGroups.lower k : ℤ)
    #int (DyadicGroups.upper ws.length k : ℤ))
  let R := (∫⁻ i, F i ∂WeightedChoice.law ws) +
    GroupedEnvelope.factor (envelopeTotal ws asc) * ε
  let K := GroupedEnvelope.candidateCredit ws.length (SortedWeights.value ws asc)
    (SortedWeights.envelope ws asc) (fun i => F (SortedWeights.index ws.length asc i)) R k
  have hK : (∫⁻ r, K r ∂RndInt.law (DyadicGroups.upper ws.length k - DyadicGroups.lower k)) =
      groupCredit ws asc F ε k := GroupedEnvelope.candidate_expectation _ _ _ _ _ _
  have hrange := InclusiveOffset.rndIntRange_distSpec (rT := rT) (GF := GF) E
    (DyadicGroups.lower k) (DyadicGroups.upper ws.length k)
    (by exact_mod_cast DyadicGroups.lower_le_upper ws.length k hkn)
  have hdiff : ((DyadicGroups.upper ws.length k : ℤ) - DyadicGroups.lower k).toNat =
      DyadicGroups.upper ws.length k - DyadicGroups.lower k := by omega
  simp only [hdiff] at hrange
  isimp only [← hK] at Hcredit
  iapply (hrange.wp_supported (fun r => r < DyadicGroups.width ws.length k)
    (Set.to_countable _).measurableSet (UniformInt.ae_lt (DyadicGroups.width ws.length k)) K
    (measurable_of_countable _) _) $$ Hcredit
  iintro %r %hr Hcredit
  iterate 2 twp_pure
  twp_bind pl(if #bool asc
    then #int (ws.length : ℤ) - #1 - #int ((DyadicGroups.lower k : ℤ) + r - 1)
    else #int ((DyadicGroups.lower k : ℤ) + r - 1))
  iapply tglWp_wand
  isplitl []
  · iapply twp_index E ws.length k r asc hkn hr
  iintro %v %hv
  subst v
  twp_pure
  twp_bind pl(if #bool asc then #int (ws.length : ℤ) - #int (DyadicGroups.lower k : ℤ)
    else #int (DyadicGroups.lower k : ℤ) - #1)
  iapply tglWp_wand
  isplitl []
  · iapply twp_pivot E ws.length k asc hkn
  iintro %v %hv
  subst v
  twp_pure
  ihave Hretry : (↯ R -∗ tglWp E pl(&(Program.loop ws (envelopes ws asc) asc) #())
    (fun v => iprop(∃ i : ℕ, ⌜v = Val.int (i : ℤ)⌝ ∗ ↯ (F i)))) $$ [IH]
  · iintro Hretry
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hretry
    iapply IH $$ Hterm Hcredit
  iapply twp_accept E ws asc hs k r hkn hr he F R (Program.loop ws (envelopes ws asc) asc)
    $$ Hretry Hcredit

end

end SampLib.SortedChoice
