import SampLib.Samplers.AlternatingSeries
import SampLib.Samplers.IterateCoin
import SampLib.Distributions.TrigonometricFactoryParameters
import SampLib.TrigonometricCoefficients
import SampLib.Syntax.TrigonometricCallbacks
import Samplers.Bernoulli.Trigonometric

/-! # Trigonometric specializations of the alternating-series factory

The concrete coefficient callbacks compute integer factorials and powers. Their
analytic identification is kept in TrigonometricFactoryParameters.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.TrigonometricSeriesFactories

noncomputable section

open TrigonometricFactoryParameters

private def cosineCallback {rT : Type} : Val rT :=
  ⟨TrigonometricCoefficients.cosine, .lam (by is_lc), by is_lc⟩

private def sincCallback {rT : Type} (a b : ℤ) : Val rT :=
  ⟨TrigonometricCoefficients.sinc a b, .lam (by is_lc), by is_lc⟩

private def squaredCoin {rT : Type} (coin : Val rT) : Val rT :=
  ⟨.lam pl(&Occil.iterateCoin &coin.fst #2), .lam (by is_lc), by is_lc⟩

private instance factorial_closed {rT : Type} :
    ClosedExp (FactorialCallback.factorial : Exp rT) where
  lc := by is_lc
  fv := FactorialCallback.factorial_fv

private instance power_closed {rT : Type} :
    ClosedExp (Occil.FactoryExtra.intPower : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.FactoryExtra.intPower, Exp.fv]

private instance iterate_closed {rT : Type} : ClosedExp (Occil.iterateCoin : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.iterateCoin, Exp.fv]

private instance alternating_closed {rT : Type} :
    ClosedExp (Occil.FactoryExtra.alternatingSeries : Exp rT) where
  lc := by is_lc
  fv := by
    simp [Occil.FactoryExtra.alternatingSeries, Occil.newUniformBag, Exp.fv,
      UniformBag.uniformBagLess_fv, ClosedExp.closeRec, ClosedExp.fv]

private theorem parameter_nonneg (a b : ℕ) : (0 : ℚ) ≤ a / b := by positivity

private theorem parameter_le_six (a b : ℕ) (hb : 0 < b) (hab : a ≤ 6 * b) :
    (a : ℚ) / b ≤ 6 := by
  apply (div_le_iff₀ (by positivity : (0 : ℚ) < b)).mpr
  exact_mod_cast hab

def sincParameters (a b : ℕ) (hb : 0 < b) (hab : a ≤ 6 * b) :=
  sinc ((a : ℚ) / b) (parameter_nonneg a b) (parameter_le_six a b hb hab)

private theorem sinc_raw_value (a b : ℕ) (hb : 0 < b) (hab : a ≤ 6 * b) (n : ℕ) :
    (TrigonometricCoefficients.sincFraction (a : ℤ) b hb n).value =
      (sincParameters a b hb hab).coefficient n := by
  simpa only [sincParameters, sinc, Int.cast_natCast] using
    TrigonometricCoefficients.sincFraction_value (a : ℤ) b hb n

private theorem guard (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ 6 * b) :
    (Bool.or (Bool.or (decide ((a : ℤ) ≤ 0)) (decide ((b : ℤ) ≤ 0)))
      (decide (6 * (b : ℤ) < a))) = false := by
  have ha' : ¬(a : ℤ) ≤ 0 := by omega
  have hb' : ¬(b : ℤ) ≤ 0 := by omega
  have hab' : ¬6 * (b : ℤ) < a := by exact_mod_cast (not_lt.mpr hab)
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
  exact ⟨⟨ha', hb'⟩, hab'⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
private theorem squaredCoin_spec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&(squaredCoin coin).fst #())
      (RealCoin.law (p * p)) Val.bool where
  spec F hF := by
    have hs := (IterateCoin.iterateCoin_distSpec E p coin hcoin 2).spec F hF
    have hb : IterateCoin.bias p 2 = p * p := Subtype.ext (by
      simp [IterateCoin.bias, pow_two])
    simp only [IterateCoin.law, hb] at hs
    iintro Hcredit
    twp_pure
    simp only [ClosedExp.openRec]
    iapply hs $$ Hcredit

/-- The cosine coefficient has denominator (2n)!, so the analytic argument is sqrt(p). -/
theorem cosineSqrt_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.cosineSqrt &coin.fst #())
      (RealCoin.law (AlternatingSeries.meanBias cosine p)) Val.bool where
  spec F hF := by
    have hs := AlternatingSeries.alternatingSeries_distSpec E cosine
      TrigonometricCoefficients.cosineFraction
      (fun n => TrigonometricCoefficients.cosineFraction_value n) p coin cosineCallback hcoin
      (fun n => TrigonometricCoefficients.twp_cosineFraction E n)
    have hnext := hs.spec F hF
    simp only [cosineCallback] at hnext
    rw [TrigonometricCoefficients.cosine_eq_code] at hnext
    iintro Hcredit
    iterate 3 twp_pure
    simp only [ClosedExp.openRec, ClosedExp.closeRec]
    ieval (change _ ⊢ tglWp E (TrigonometricCallbacks.cosineCall coin.fst) _)
    rw [TrigonometricCallbacks.cosineCall_eq]
    iapply hnext $$ Hcredit

/-- One input flip per series degree realizes sinc(sqrt(c p)), including p=0. -/
theorem sincSqrtScaled_distSpec (E : CoPset) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≤ 6 * b) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.sincSqrtScaled &coin.fst #int (a : ℤ) #int (b : ℤ) #())
      (RealCoin.law (AlternatingSeries.meanBias (sincParameters a b hb hab) p)) Val.bool where
  spec F hF := by
    have hs := AlternatingSeries.alternatingSeries_distSpec E (sincParameters a b hb hab)
      (TrigonometricCoefficients.sincFraction (a : ℤ) b hb) (sinc_raw_value a b hb hab)
      p coin (sincCallback (a : ℤ) (b : ℤ)) hcoin
      (fun n => TrigonometricCoefficients.twp_sincFraction E (a : ℤ) b hb n)
    have hnext := hs.spec F hF
    simp only [sincCallback] at hnext
    rw [TrigonometricCoefficients.sinc_eq_code] at hnext
    iintro Hcredit
    iterate 10 twp_pure
    rw [guard a b ha hb hab]
    iterate 3 twp_pure
    simp only [ClosedExp.openRec, ClosedExp.closeRec]
    ieval (change _ ⊢ tglWp E (TrigonometricCallbacks.sincCall coin.fst a b) _)
    rw [TrigonometricCallbacks.sincCall_eq]
    iapply hnext $$ Hcredit

/-- Two input flips per degree replace p by p², giving sinc(p sqrt(c)). -/
theorem sincScaled_distSpec (E : CoPset) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≤ 6 * b) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.sincScaled &coin.fst #int (a : ℤ) #int (b : ℤ) #())
      (RealCoin.law (AlternatingSeries.meanBias (sincParameters a b hb hab) (p * p)))
      Val.bool where
  spec F hF := by
    have hs := AlternatingSeries.alternatingSeries_distSpec E (sincParameters a b hb hab)
      (TrigonometricCoefficients.sincFraction (a : ℤ) b hb) (sinc_raw_value a b hb hab)
      (p * p) (squaredCoin coin) (sincCallback (a : ℤ) (b : ℤ))
      (squaredCoin_spec E p coin hcoin)
      (fun n => TrigonometricCoefficients.twp_sincFraction E (a : ℤ) b hb n)
    have hnext := hs.spec F hF
    simp only [sincCallback] at hnext
    rw [TrigonometricCoefficients.sinc_eq_code] at hnext
    iintro Hcredit
    iterate 10 twp_pure
    rw [guard a b ha hb hab]
    iterate 3 twp_pure
    simp only [ClosedExp.openRec, ClosedExp.closeRec]
    ieval (change _ ⊢ tglWp E (TrigonometricCallbacks.sincCall
      (squaredCoin coin).fst a b) _)
    rw [TrigonometricCallbacks.sincCall_eq]
    iapply hnext $$ Hcredit

end specification

end

end SampLib.TrigonometricSeriesFactories
