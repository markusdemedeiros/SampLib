import SampLib.Latent.LatentCoinSpec
import SampLib.Continuous.IterateCoin

/-! # Finite conjunction of coins over one owned latent world -/

open ProbLang MeasureTheory
open scoped ENNReal

namespace SampLib.LatentReal.CoinIteration

noncomputable section

variable {Ω S : Type} [MeasurableSpace Ω]

def bias (φ : Ω → unitInterval) (n : ℕ) (x : Ω) : unitInterval :=
  IterateCoin.bias (φ x) n

def continuation (φ : Ω → unitInterval) (n : ℕ) (G : Bool → Ω → ℝ≥0∞)
    (b : Bool) (x : Ω) : ℝ≥0∞ :=
  IterateCoin.continuation (φ x) n (fun bit => G bit x) b

theorem measurable_bias {φ : Ω → unitInterval} (hφ : Measurable φ) (n : ℕ) :
    Measurable (bias φ n) := by
  unfold bias IterateCoin.bias
  fun_prop

theorem measurable_continuation {φ : Ω → unitInterval} (hφ : Measurable φ)
    (n : ℕ) {G : Bool → Ω → ℝ≥0∞} (hG : ∀ b, Measurable (G b)) (b : Bool) :
    Measurable (continuation φ n G b) := by
  cases b
  · exact hG false
  · exact LatentCoin.measurable_kernel (measurable_bias hφ n) hG

/-- Conditioning on the same world turns successive successes into powers pointwise. -/
theorem expectation (D : Model Ω S) (s : S) (φ : Ω → unitInterval)
    (n : ℕ) (G : Bool → Ω → ℝ≥0∞) :
    LatentCoin.credit D s φ (continuation φ n G) =
      LatentCoin.credit D s (bias φ (n + 1)) G := by
  apply lintegral_congr
  intro x
  exact (RealCoin.lintegral_law _ _).symm.trans (IterateCoin.expectation (φ x) n _)

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- All-successes iteration retains one source cache and every joint continuation. -/
theorem iterateCoin_latentCoinProgramSpec (E : CoPset) (D : Model Ω S)
    (owns : Val rT → S → IProp GF) (φ : Ω → unitInterval)
    (coin : Val rT → Val rT) (hcoin : IsLatentCoinSpec E D owns φ coin) (n : ℕ) :
    IsLatentCoinProgramSpec E D owns (bias φ n)
      (fun source => pl(&Occil.iterateCoin &(coin source).fst #int (n : ℤ))) where
  measurable_bias := measurable_bias hcoin.measurable_bias n
  spec source s G hG := by
    induction n generalizing s G with
    | zero =>
      iintro ⟨Hstate, Hcredit⟩
      have hzero : LatentCoin.credit D s (bias φ 0) G = ∫⁻ x, G true x ∂D.posterior s := by
        apply lintegral_congr
        intro x
        exact IterateCoin.credit_zero (φ x) _
      isimp only [hzero] at Hcredit
      twp_pures
      twp_value
      imodintro
      iapply LatentCoin.post_return D owns source s s true G (D.refines_refl s)
      iframe Hstate Hcredit
    | succ n ih =>
      iintro ⟨Hstate, Hcredit⟩
      isimp only [← expectation D s φ n G] at Hcredit
      twp_pures
      twp_bind pl(&(coin source).fst #())
      iapply hcoin.wp source s (continuation φ n G)
        (measurable_continuation hcoin.measurable_bias n hG) _ $$ Hstate Hcredit
      iintro %bit %t %hst Hstate Hcredit
      cases bit
      · isimp only [continuation, IterateCoin.continuation, Bool.false_eq_true, ite_false]
          at Hcredit
        twp_pures
        twp_value
        imodintro
        iapply LatentCoin.post_return D owns source s t false G hst
        iframe Hstate Hcredit
      · isimp only [continuation, IterateCoin.continuation, ite_true] at Hcredit
        twp_pure
        twp_pure
        rw [Nat.cast_add_one, add_sub_cancel_right]
        twp_bind pl(&Occil.iterateCoin &(coin source).fst #int (n : ℤ))
        iapply (tglWp_mono fun _ => tglWp_value)
        iapply tglWp_wand
        isplitl [Hstate Hcredit]
        · have hcredit : (∫⁻ x, IterateCoin.credit (φ x) n (fun bit => G bit x)
              ∂D.posterior t) = LatentCoin.credit D t (bias φ n) G := rfl
          isimp only [hcredit] at Hcredit
          iapply ih t G hG
          iframe Hstate Hcredit
        iintro %v Hpost
        iapply LatentCoin.post_weaken D owns source s t G v hst $$ Hpost

end

end SampLib.LatentReal.CoinIteration
