import SampLib.LatentFractionalPowerKernel
import SampLib.LatentCoinConstantProgram
import SampLib.StatefulAbsorbingChain
import SampLib.Samplers.FractionalPower

/-! # Fractional powers of a coin sharing an owned latent world -/

open ProbLang MeasureTheory
open scoped ENNReal

namespace SampLib.LatentReal.CoinFractionalPower

noncomputable section

private theorem exponent_pos (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    0 < (FractionalPower.exponent a b ha hab : ℝ) :=
  div_pos (by exact_mod_cast ha) (by exact_mod_cast lt_of_lt_of_le ha hab)

private theorem hazard_positive (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) (n : ℕ) :
    (0 : ℤ) < (b : ℤ) * ((n : ℤ) + 1) := by
  have hb : (0 : ℤ) < b := by exact_mod_cast lt_of_lt_of_le ha hab
  positivity

private theorem hazard_bounded (a b : ℕ) (hab : a ≤ b) (n : ℕ) :
    (a : ℤ) ≤ (b : ℤ) * ((n : ℤ) + 1) := by
  have habz : (a : ℤ) ≤ b := by exact_mod_cast hab
  have hb : (0 : ℤ) ≤ b := by positivity
  nlinarith

private theorem hazard_bias_eq (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) (n : ℕ) :
    RationalCoin.bias (a : ℤ) ((b : ℤ) * ((n : ℤ) + 1)) (by positivity)
      (hazard_positive a b ha hab n) (hazard_bounded a b hab n) =
      FractionalPower.hazardBias (FractionalPower.exponent a b ha hab) n := by
  apply Subtype.ext
  simp only [RationalCoin.bias, FractionalPower.hazardBias, FractionalPower.exponent,
    Int.cast_mul, Int.cast_natCast, Int.cast_add, Int.cast_one, div_div]

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

private theorem hazard_spec (E : CoPset) (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) (n : ℕ) :
    IsDistSpec (GF := GF) E
      pl(&Occil.rationalCoin #int (a : ℤ) #int ((b : ℤ) * ((n : ℤ) + 1)))
      (RealCoin.law (FractionalPower.hazardBias (FractionalPower.exponent a b ha hab) n))
      Val.bool := by
  simpa only [hazard_bias_eq a b ha hab n] using
    RationalCoin.rationalCoin_distSpec (GF := GF) E (a : ℤ) ((b : ℤ) * ((n : ℤ) + 1))
      (by positivity) (hazard_positive a b ha hab n) (hazard_bounded a b hab n)

private theorem twp_round (E : CoPset) (D : Model Ω S)
    (owns : Val rT → S → IProp GF) (φ : Ω → unitInterval)
    (coin : Val rT → Val rT) (hcoin : IsLatentCoinSpec E D owns φ coin)
    (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) (source : Val rT)
    (G : Bool → Ω → ℝ≥0∞) (hG : ∀ bit, Measurable (G bit)) (n : ℕ) (c : ℝ≥0∞)
    (hnext : ∀ s, ⊢ owns source s -∗
      ↯ ((∫⁻ x, tail φ (FractionalPower.exponent a b ha hab) G (n + 1) x
        ∂D.posterior s) + c) -∗
      tglWp E pl(&(FractionalPower.Program.loop (coin source) a b)
        #int (((n + 1 : ℕ) : ℤ) + 1)) (LatentCoin.post D owns source s G)) (s : S) :
    ⊢ owns source s -∗
      ↯ ((∫⁻ x, tail φ (FractionalPower.exponent a b ha hab) G n x ∂D.posterior s) +
        retryBound (FractionalPower.exponent a b ha hab) n * c) -∗
      tglWp E pl(&(FractionalPower.Program.loop (coin source) a b) #int ((n : ℤ) + 1))
        (LatentCoin.post D owns source s G) := by
  let r := FractionalPower.exponent a b ha hab
  iintro Hstate Hcredit
  ihave Hcredit := ErrorCredit.weaken
    (expectation_budget D s hcoin.measurable_bias r G hG n c) $$ Hcredit
  twp_pures
  isimp only [RationalCoin.rationalCoin_openRec, RationalCoin.rationalCoin_closeRec]
  twp_bind pl(&(coin source).fst #())
  iapply hcoin.wp source s (inputCredit φ r G n c)
    (measurable_inputCredit hcoin.measurable_bias r hG n c) _ $$ Hstate Hcredit
  iintro %bit %t %hst Hstate Hcredit
  cases bit
  · let H : Bool → Ω → ℝ≥0∞ := fun hazard x =>
      FractionalPower.hazardCredit (fun bit => G bit x) (tail φ r G (n + 1) x + c) hazard
    have hH : ∀ hazard, Measurable (H hazard) := by
      intro hazard
      cases hazard
      · exact (measurable_tail hcoin.measurable_bias r hG (n + 1)).add measurable_const
      · exact hG false
    have hcredit : (∫⁻ x, inputCredit φ r G n c false x ∂D.posterior t) =
        LatentCoin.credit D t (fun _ => FractionalPower.hazardBias r n) H := rfl
    isimp only [hcredit] at Hcredit
    twp_pure
    twp_pure
    twp_bind pl(&Occil.rationalCoin #int (a : ℤ) #int ((b : ℤ) * ((n : ℤ) + 1)))
    iapply (LatentCoin.constantProgramSpec E D owns (FractionalPower.hazardBias r n) _
      (hazard_spec E a b ha hab n)).wp source t H hH _ $$ Hstate Hcredit
    iintro %hazard %u %htu Hstate Hcredit
    cases hazard
    · have hcredit : (∫⁻ x, H false x ∂D.posterior u) =
          (∫⁻ x, tail φ r G (n + 1) x ∂D.posterior u) + c := by
        change (∫⁻ x, tail φ r G (n + 1) x + c ∂D.posterior u) = _
        rw [lintegral_add_left (measurable_tail hcoin.measurable_bias r hG (n + 1))]
        simp
      isimp only [hcredit] at Hcredit
      twp_pure
      twp_pure
      rw [← Nat.cast_add_one]
      iapply tglWp_wand
      isplitl [Hstate Hcredit]
      · have hresume := hnext u
        simp only [FractionalPower.Program.loop, FractionalPower.Program.loopCode] at hresume
        iapply hresume $$ Hstate Hcredit
      iintro %v Hpost
      iapply LatentCoin.post_weaken D owns source s u G v (D.refines_trans hst htu) $$ Hpost
    · isimp only [H, FractionalPower.hazardCredit, ite_true] at Hcredit
      twp_pures
      twp_value
      imodintro
      iapply LatentCoin.post_return D owns source s u false G (D.refines_trans hst htu)
      iframe Hstate Hcredit
  · isimp only [inputCredit, FractionalPower.inputCredit, ite_true] at Hcredit
    twp_pures
    twp_value
    imodintro
    iapply LatentCoin.post_return D owns source s t true G hst
    iframe Hstate Hcredit

/-- Every round retains the shared source, while vanishing survival funds termination. -/
theorem twp_loop (E : CoPset) (D : Model Ω S)
    (owns : Val rT → S → IProp GF) (φ : Ω → unitInterval)
    (coin : Val rT → Val rT) (hcoin : IsLatentCoinSpec E D owns φ coin)
    (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) (source : Val rT) (s : S)
    (G : Bool → Ω → ℝ≥0∞) (hG : ∀ bit, Measurable (G bit)) :
    ⊢ owns source s -∗
      ↯ (LatentCoin.credit D s (bias φ (FractionalPower.exponent a b ha hab)) G) -∗
      tglWp E pl(&(FractionalPower.Program.loop (coin source) a b) #1)
        (LatentCoin.post D owns source s G) := by
  have h := StatefulAbsorbingChain.twp_of_survival E
    (fun n => pl(&(FractionalPower.Program.loop (coin source) a b) #int ((n : ℤ) + 1)))
    (owns source) (fun t => LatentCoin.post D owns source t G)
    (fun n t => ∫⁻ x, tail φ (FractionalPower.exponent a b ha hab) G n x ∂D.posterior t)
    (retryBound (FractionalPower.exponent a b ha hab))
    (twp_round E D owns φ coin hcoin a b ha hab source G hG) 0 (by rfl)
    (absorbs _ (exponent_pos a b ha hab)) s
  simpa only [initial_credit D s φ _ (exponent_pos a b ha hab) G,
    Nat.cast_zero, zero_add] using h

/-- The actual fractional factory preserves arbitrary bit/latent continuation credits. -/
theorem fractionalPower_latentCoinProgramSpec (E : CoPset) (D : Model Ω S)
    (owns : Val rT → S → IProp GF) (φ : Ω → unitInterval)
    (coin : Val rT → Val rT) (hcoin : IsLatentCoinSpec E D owns φ coin)
    (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    IsLatentCoinProgramSpec E D owns (bias φ (FractionalPower.exponent a b ha hab))
      (fun source =>
        pl(&Occil.fractionalPower &(coin source).fst #int (a : ℤ) #int (b : ℤ) #())) where
  measurable_bias := measurable_bias hcoin.measurable_bias _
  spec source s G hG := by
    iintro ⟨Hstate, Hcredit⟩
    rw [← FractionalPower.Program.source_fst (rT := rT)]
    twp_pures
    have hguard : (decide ((a : ℤ) ≤ 0) || decide ((b : ℤ) < a)) = false := by
      have haz : (0 : ℤ) < a := by exact_mod_cast ha
      have habz : (a : ℤ) ≤ b := by exact_mod_cast hab
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_le, not_lt]
      exact ⟨haz, habz⟩
    rw [hguard]
    twp_pure
    twp_pure
    isimp only [RationalCoin.rationalCoin_openRec]
    ieval (change _ ⊢ tglWp E pl(&(FractionalPower.Program.loop (coin source) a b) #1) _)
    iapply twp_loop E D owns φ coin hcoin a b ha hab source s G hG $$ Hstate Hcredit

end

end SampLib.LatentReal.CoinFractionalPower
