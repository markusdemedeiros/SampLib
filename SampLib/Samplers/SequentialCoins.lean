import SampLib.SupportedSpec
import SampLib.WeightedValidation
import SampLib.Samplers.RationalCoin
import SampLib.Distributions.Urn
import Samplers.Weighted.Choice

/-! # Sequential conditional categorical coins

The first category has its normalized weight; after rejection the remaining
weights are renormalized. Zero-weight suffixes are unreachable.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.SequentialCoins

noncomputable section

section mathematics

open MeasureTheory

/-- Categorical credit translated by the number of categories already visited. -/
def credit (ws : List ℕ) (offset : ℕ) (F : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ i, F (offset + i) ∂WeightedChoice.law ws

/-- Credit conditional on accepting or skipping the first category. -/
def continuation (ws : List ℕ) (offset : ℕ) (F : ℕ → ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then F offset else credit ws (offset + 1) F

/-- Renormalization of the remaining categories preserves the categorical expectation. -/
theorem expectation (w : ℕ) (ws : List ℕ) (hs : 0 < w + ws.sum)
    (offset : ℕ) (F : ℕ → ℝ≥0∞) :
    RealCoin.credit (Urn.bias w ws.sum) (continuation ws offset F) =
      credit (w :: ws) offset F := by
  rw [RealCoin.credit, Urn.pmf_true w ws.sum hs, Urn.pmf_false w ws.sum hs]
  simp only [continuation, ite_true, Bool.false_eq_true, ite_false]
  have hshift : (fun i => F (offset + (i + 1))) = fun i => F ((offset + 1) + i) := by
    funext i
    congr 1
    omega
  have hcons : credit (w :: ws) offset F =
      ((w : ℝ≥0∞) * F offset +
        WeightedChoice.weightedSum ws (fun i => F ((offset + 1) + i))) /
        ((w : ℝ≥0∞) + ws.sum) := by
    simp only [credit, WeightedChoice.lintegral_law, WeightedChoice.weightedSum,
      List.sum_cons, Nat.add_zero, Nat.cast_add, hshift]
  rw [hcons]
  have htail : WeightedChoice.weightedSum ws (fun i => F ((offset + 1) + i)) =
      ws.sum * credit ws (offset + 1) F := by
    by_cases hz : ws.sum = 0
    · rw [← WeightedChoice.rank_partition, hz]
      simp
    · rw [credit, WeightedChoice.lintegral_law,
        ENNReal.mul_div_cancel (by positivity) (by finiteness)]
  rw [htail]
  simp only [ENNReal.div_eq_inv_mul]
  ring

private theorem possible_failure (w : ℕ) (ws : List ℕ) (hs : 0 < w + ws.sum) :
    ∀ᵐ b ∂RealCoin.law (Urn.bias w ws.sum), b = false → 0 < ws.sum := by
  by_cases hz : ws.sum = 0
  · have hw : 0 < w := by omega
    have hb : Urn.bias w ws.sum = 1 := by
      rw [hz]
      apply Subtype.ext
      simp [Urn.bias, hw, RationalCoin.bias, hw.ne']
    simp [hb, RealCoin.law, RealCoin.pmf]
  · exact Filter.Eventually.of_forall fun _ _ => Nat.pos_of_ne_zero hz

end mathematics

private theorem remaining_cast (w s : ℕ) :
    ((w + s : ℕ) : ℤ) - w = (s : ℤ) := by omega

private def loop {rT : Type _} : Exp rT := pl%
  rec choose xs remaining index := case! xs
    | inl(v) => fail
    | inr(p) => if &Occil.rationalCoin (fst(p)) remaining then index else
        choose (snd(p)) (remaining - fst(p)) (index + #1)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_loop (E : CoPset) (ws : List ℕ) (offset : ℕ)
    (hs : 0 < ws.sum) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (credit ws offset F) -∗
      tglWp E pl(&loop &(listVal (fun n : ℕ => Val.int n) ws).fst
        #int (ws.sum : ℤ) #int (offset : ℤ))
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int (i : ℤ)⌝ ∗ ↯ (F i))) := by
  induction ws generalizing offset with
  | nil => simp at hs
  | cons w ws ih =>
    have ht : 0 < w + ws.sum := by simpa using hs
    have hcoin : IsDistSpec (GF := GF) E
        pl(&Occil.rationalCoin #int (w : ℤ) #int ((w + ws.sum : ℕ) : ℤ))
        (RealCoin.law (Urn.bias w ws.sum)) Val.bool := by
      simpa only [Urn.bias, dite_eq_left ht, Nat.cast_add] using
        RationalCoin.rationalCoin_distSpec (GF := GF) E w (w + ws.sum)
          (by omega) (by omega) (by omega)
    iintro Hcredit
    simp only [listVal, List.sum_cons]
    iterate 7 twp_pure
    twp_bind pl(&Occil.rationalCoin #int (w : ℤ) #int ((w + ws.sum : ℕ) : ℤ))
    isimp only [← expectation w ws ht offset F, ← RealCoin.lintegral_law] at Hcredit
    iapply (hcoin.wp_supported (fun b => b = false → 0 < ws.sum)
      (Set.to_countable _).measurableSet (possible_failure w ws ht)
      (continuation ws offset F) (measurable_of_countable _) _) $$ Hcredit
    iintro %b %hb Hcredit
    cases b
    · isimp only [continuation, Bool.false_eq_true, ite_false] at Hcredit
      iterate 5 twp_pure
      rw [remaining_cast]
      have hrec := ih (offset + 1) (hb rfl)
      simp [loop, Exp.close, Exp.closeRec] at hrec
      isimp [Exp.ofVal]
      iapply hrec $$ Hcredit
    · twp_pures
      twp_value
      imodintro
      iexists offset
      isimp only [continuation, ite_true] at Hcredit
      iframe Hcredit
      itrivial

/-- Sequential conditional coins realize the normalized categorical law. -/
theorem sequentialCoins_distSpec (E : CoPset) (ws : List ℕ) [NeZero ws.sum] :
    IsDistSpec (GF := GF) E pl(&Occil.WeightedVariants.sequentialCoins
      &(listVal (fun n : ℕ => Val.int n) ws).fst #())
      (WeightedChoice.law ws) (fun i : ℕ => Val.int (i : ℤ)) := by
  refine ⟨fun F _ => ?_⟩
  have hloop := twp_loop (rT := rT) (GF := GF) E ws 0 (NeZero.pos ws.sum) F
  simp [loop, Exp.close, Exp.closeRec, credit] at hloop
  iintro Hcredit
  iterate 2 twp_pure
  twp_bind pl(&Occil.Weighted.validWeights &(listVal (fun n : ℕ => Val.int n) ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply WeightedValidation.twp_validWeights E ws (NeZero.pos ws.sum)
  iintro %v %hv
  subst v
  iterate 2 twp_pure
  simp only [RationalCoin.rationalCoin_openRec, RationalCoin.rationalCoin_closeRec,
    WeightedValidation.sumInts_openRec, WeightedValidation.sumInts_closeRec]
  twp_bind pl(&Occil.sumInts &(listVal (fun n : ℕ => Val.int n) ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply WeightedChoice.twp_sumInts E ws
  iintro %v %hv
  subst v
  isimp [Exp.ofVal]
  iapply hloop $$ Hcredit

end specification

end

end SampLib.SequentialCoins
