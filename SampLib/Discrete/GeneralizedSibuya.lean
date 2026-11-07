import SampLib.Discrete.Laws.GeneralizedSibuya
import SampLib.Discrete.InversePolya
import SampLib.Discrete.Laws.InverseUrnOne
import Samplers.Discrete.Tails

/-! # Generalized Sibuya variates with positive rational parameters

The reciprocal hazards are first-marked urn hazards after clearing denominators.
Their harmonic cumulative hazard proves termination throughout alpha < nu+1.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.GeneralizedSibuya

noncomputable section

open MeasureTheory (lintegral_map)

private theorem denominator_cast (D : Parameters) (n : ℕ) :
    (D.alphaDenominator : ℤ) * (D.nuNumerator + ((n + 1 : ℕ) : ℤ) * D.nuDenominator) =
      (marked D : ℤ) + (unmarked D + n * reinforcement D : ℕ) := by
  exact_mod_cast denominator_eq D n

private theorem numerator_cast (D : Parameters) :
    (D.alphaNumerator : ℤ) * D.nuDenominator = (marked D : ℤ) :=
  (Nat.cast_mul _ _).symm

private def loop {rT : Type _} (D : Parameters) : Exp rT :=
  .fix (.lam (pl% if &Occil.rationalCoin
    (#int (D.alphaNumerator : ℤ) * #int (D.nuDenominator : ℤ))
    (#int (D.alphaDenominator : ℤ) *
      (#int (D.nuNumerator : ℤ) + {Exp.bvar 0} * #int (D.nuDenominator : ℤ))) then
      {Exp.bvar 0} else {Exp.bvar 1} ({Exp.bvar 0} + #1)))

private theorem valid_test (D : Parameters) :
    Bool.or
      (Bool.or
        (Bool.or
          (Bool.or (decide ((D.alphaNumerator : ℤ) ≤ 0))
            (decide ((D.alphaDenominator : ℤ) ≤ 0))) false)
        (decide ((D.nuDenominator : ℤ) ≤ 0)))
      (decide ((D.alphaDenominator : ℤ) * (D.nuNumerator + D.nuDenominator) ≤
        (D.alphaNumerator : ℤ) * D.nuDenominator)) = false := by
  have ha : decide ((D.alphaNumerator : ℤ) ≤ 0) = false :=
    decide_eq_false (by exact_mod_cast D.alphaNumerator_pos.not_ge)
  have hb : decide ((D.alphaDenominator : ℤ) ≤ 0) = false :=
    decide_eq_false (by exact_mod_cast D.alphaDenominator_pos.not_ge)
  have hd : decide ((D.nuDenominator : ℤ) ≤ 0) = false :=
    decide_eq_false (by exact_mod_cast D.nuDenominator_pos.not_ge)
  have hmargin : ¬(D.alphaDenominator : ℤ) * (D.nuNumerator + D.nuDenominator) ≤
      (D.alphaNumerator : ℤ) * D.nuDenominator := by
    exact_mod_cast D.admissible.not_ge
  rw [ha, hb, hd, decide_eq_false hmargin]
  rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private def post (F : ℕ → ℝ≥0∞) (v : Val rT) : IProp GF :=
  iprop(∃ (k : ℕ), ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k))

private theorem coin_spec (E : CoPset) (D : Parameters) (n : ℕ) :
    IsDistSpec (GF := GF) E
      pl(&Occil.rationalCoin #int (marked D : ℤ)
        #int ((marked D : ℤ) + (unmarked D + n * reinforcement D : ℕ)))
      (RealCoin.law (Urn.bias (marked D) (unmarked D + n * reinforcement D))) Val.bool := by
  have ha := marked_pos D
  have ht : 0 < marked D + (unmarked D + n * reinforcement D) := by omega
  simpa only [Urn.bias, dite_eq_left ht, Nat.cast_add] using
    RationalCoin.rationalCoin_distSpec (GF := GF) E (marked D : ℤ)
      ((marked D : ℤ) + (unmarked D + n * reinforcement D : ℕ))
      (by omega) (by omega) (by omega)

private theorem twp_step (E : CoPset) (D : Parameters) (F : ℕ → ℝ≥0∞)
    (n : ℕ) (credit : ℝ≥0∞)
    (next : ⊢ ↯ credit -∗ tglWp E pl(&(loop D) #int ((n + 2 : ℕ) : ℤ)) (post F)) :
    ⊢ ↯ ((1 - continuation D n) * F (n + 1) + continuation D n * credit) -∗
      tglWp E pl(&(loop D) #int ((n + 1 : ℕ) : ℤ)) (post F) := by
  iintro Hcredit
  iterate 6 twp_pure
  rw [denominator_cast, numerator_cast]
  simp only [RationalCoin.rationalCoin_openRec]
  twp_bind pl(&Occil.rationalCoin #int (marked D : ℤ)
    #int ((marked D : ℤ) + (unmarked D + n * reinforcement D : ℕ)))
  isimp only [← InversePolya.coin_expectation (marked D) (unmarked D)
    (reinforcement D) n (marked_pos D) (fun j => F (j + 1)) credit] at Hcredit
  iapply ((coin_spec E D n).wp (InversePolya.kernel (fun j => F (j + 1)) n credit)
    (measurable_of_countable _) _) $$ Hcredit
  iintro %color Hcredit
  cases color
  · iterate 2 twp_pure
    rw [← Nat.cast_add_one, show n + 1 + 1 = n + 2 by omega]
    isimp only [InversePolya.kernel, Bool.false_eq_true, ite_false] at Hcredit
    simp only [loop] at next
    iapply next $$ Hcredit
  · twp_pures
    twp_value
    imodintro
    isimp only [post]
    iexists (n + 1)
    isimp only [InversePolya.kernel, ite_true] at Hcredit
    iframe Hcredit
    itrivial

/-- Exact generalized Sibuya law throughout the source's rational parameter domain. -/
theorem generalizedSibuya_distSpec (E : CoPset) (D : Parameters) :
    IsDistSpec (GF := GF) E
      pl(&Occil.DiscreteExtra.generalizedSibuya #int (D.alphaNumerator : ℤ)
        #int (D.alphaDenominator : ℤ) #int (D.nuNumerator : ℤ) #int (D.nuDenominator : ℤ))
      (law D) (fun k : ℕ => Val.int (k : ℤ)) where
  spec F hF := by
    iintro Hcredit
    isimp only [law, lintegral_map hF (measurable_of_countable _),
      Nat.succ_eq_add_one, InverseUrn.law_one, UrnWaiting.law] at Hcredit
    twp_pures
    rw [valid_test D]
    iterate 2 twp_pure
    simp only [RationalCoin.rationalCoin_openRec, RationalCoin.rationalCoin_closeRec]
    have h := AbsorbingChain.twp_of_survival (rT := rT) (GF := GF) E
      (fun n => pl(&(loop D) #int ((n + 1 : ℕ) : ℤ))) (post F) (continuation D)
      (fun n => (1 - continuation D n) * F (n + 1))
      (fun n => ∫⁻ k, F (k + 1) ∂AbsorbingChain.stopLaw (continuation D) n)
      (fun n => AbsorbingChain.stopLaw_expectation _ n (fun k => F (k + 1)))
      (twp_step E D F) 0 rfl (UrnWaiting.absorbs _ _ _ (marked_pos D))
    simp only [loop, Nat.zero_add, Nat.cast_one] at h
    unfold post at h
    iapply h $$ Hcredit

end specification

end

end SampLib.GeneralizedSibuya
