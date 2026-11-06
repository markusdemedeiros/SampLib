import SampLib.LatentFractionalPower
import SampLib.LatentIterateCoin
import SampLib.PSRN.PSRNPowerCoin

/-! # Rational coin powers preserve the complete shared latent world -/

open ProbLang MeasureTheory
open scoped ENNReal

namespace SampLib.LatentReal.CoinRationalPower

noncomputable section

variable {Ω S : Type} [MeasurableSpace Ω]

def bias (φ : Ω → unitInterval) (a b : ℕ) (hb : 0 < b) (x : Ω) : unitInterval :=
  RationalPower.bias (φ x) a b hb

def firstCredit (φ : Ω → unitInterval) (a b : ℕ) (hb : 0 < b)
    (G : Bool → Ω → ℝ≥0∞) (bit : Bool) (x : Ω) : ℝ≥0∞ :=
  if bit then LatentCoin.kernel (bias φ (a % b) b hb) G x else G false x

theorem measurable_bias {φ : Ω → unitInterval} (hφ : Measurable φ)
    (a b : ℕ) (hb : 0 < b) : Measurable (bias φ a b hb) := by
  unfold bias RationalPower.bias
  fun_prop

theorem measurable_firstCredit {φ : Ω → unitInterval} (hφ : Measurable φ)
    (a b : ℕ) (hb : 0 < b) {G : Bool → Ω → ℝ≥0∞}
    (hG : ∀ bit, Measurable (G bit)) (bit : Bool) :
    Measurable (firstCredit φ a b hb G bit) := by
  cases bit
  · exact hG false
  · exact LatentCoin.measurable_kernel (measurable_bias hφ (a % b) b hb) hG

/-- Integer successes and the residual fractional trial factor the power pointwise. -/
theorem expectation (D : Model Ω S) (s : S) (φ : Ω → unitInterval)
    (a b : ℕ) (hb : 0 < b) (G : Bool → Ω → ℝ≥0∞) :
    LatentCoin.credit D s (CoinIteration.bias φ (a / b)) (firstCredit φ a b hb G) =
      LatentCoin.credit D s (bias φ a b hb) G := by
  apply lintegral_congr
  intro x
  simpa only [LatentCoin.kernel, CoinIteration.bias, firstCredit, bias,
    CoinProduct.firstCredit, RealCoin.lintegral_law] using
    PSRNPowerCoin.expectation (φ x) a b hb
    (fun bit => G bit x)

private def source {rT : Type} : Val rT :=
  ⟨Occil.PSRN.powerCoin, .lam (by is_lc), by is_lc⟩

private theorem source_fst {rT : Type} :
    (source : Val rT).fst = Occil.PSRN.powerCoin := rfl

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Full conditional specification, including numerator zero and both input-bias endpoints. -/
theorem powerCoin_latentCoinProgramSpec (E : CoPset) (D : Model Ω S)
    (owns : Val rT → S → IProp GF) (φ : Ω → unitInterval)
    (coin : Val rT → Val rT) (hcoin : IsLatentCoinSpec E D owns φ coin)
    (a b : ℕ) (hb : 0 < b) :
    IsLatentCoinProgramSpec E D owns (bias φ a b hb)
      (fun state =>
        pl(&Occil.PSRN.powerCoin &(coin state).fst #int (a : ℤ) #int (b : ℤ) #())) where
  measurable_bias := measurable_bias hcoin.measurable_bias a b hb
  spec state s G hG := by
    iintro ⟨Hstate, Hcredit⟩
    rw [← source_fst (rT := rT)]
    twp_pures
    have hden : decide ((b : ℤ) ≤ 0) = false := by
      simp only [decide_eq_false_iff_not, not_le]
      exact_mod_cast hb
    rw [hden, Bool.false_or]
    twp_pure
    isimp only [FactorySyntax.iterateCoin_openRec, FactorySyntax.iterateCoin_closeRec]
    twp_pure
    rw [← Int.natCast_ediv]
    twp_bind pl(&Occil.iterateCoin &(coin state).fst #int ((a / b : ℕ) : ℤ))
    isimp only [← expectation D s φ a b hb G] at Hcredit
    iapply (CoinIteration.iterateCoin_latentCoinProgramSpec E D owns φ coin hcoin
      (a / b)).wp state s (firstCredit φ a b hb G)
      (measurable_firstCredit hcoin.measurable_bias a b hb hG) _ $$ Hstate Hcredit
    iintro %whole %t %hst Hstate Hcredit
    cases whole
    · isimp only [firstCredit, Bool.false_eq_true, ite_false]
        at Hcredit
      twp_pures
      twp_value
      imodintro
      iapply LatentCoin.post_return D owns state s t false G hst
      iframe Hstate Hcredit
    · have hcredit : (∫⁻ x, firstCredit φ a b hb G true x ∂D.posterior t) =
          LatentCoin.credit D t (bias φ (a % b) b hb) G := rfl
      isimp only [hcredit] at Hcredit
      twp_pures
      rw [← Int.natCast_emod]
      by_cases hzero : a % b = 0
      · rw [hzero]
        twp_pures
        twp_value
        imodintro
        have hcredit : LatentCoin.credit D t (bias φ 0 b hb) G =
            ∫⁻ x, G true x ∂D.posterior t := by
          apply lintegral_congr
          intro x
          simp [LatentCoin.kernel, bias, RationalPower.bias,
            RealCoin.credit, RealCoin.pmf]
        isimp only [hcredit] at Hcredit
        iapply LatentCoin.post_return D owns state s t true G hst
        iframe Hstate Hcredit
      · have hrem : ((BaseLit.int ((a % b : ℕ) : ℤ) : BaseLit rT) == .int 0) = false := by
          change (((a % b : ℕ) : ℤ) == 0) = false
          exact beq_eq_false_iff_ne.mpr (by exact_mod_cast hzero)
        rw [hrem]
        twp_pure
        isimp only [FractionalPower.Program.fractionalPower_openRec,
          FractionalPower.Program.fractionalPower_closeRec]
        have hbias : bias φ (a % b) b hb =
            CoinFractionalPower.bias φ
              (FractionalPower.exponent (a % b) b (Nat.pos_of_ne_zero hzero)
                (Nat.mod_lt a hb).le) := rfl
        isimp only [hbias] at Hcredit
        iapply tglWp_wand
        isplitl [Hstate Hcredit]
        · iapply (CoinFractionalPower.fractionalPower_latentCoinProgramSpec E D owns φ
            coin hcoin (a % b) b (Nat.pos_of_ne_zero hzero) (Nat.mod_lt a hb).le).spec
            state t G hG
          iframe Hstate Hcredit
        iintro %v Hpost
        iapply LatentCoin.post_weaken D owns state s t G v hst $$ Hpost

end

end SampLib.LatentReal.CoinRationalPower
