import SampLib.Discrete.PoissonRational
import SampLib.Bernoulli.ProbabilityGeneratingFactory
import SampLib.Common.Laws.PoissonGenerating
import SampLib.Common.Laws.BernoulliMixture
import SampLib.Common.CoinComplement
import SampLib.Common.FactorySyntax
import Samplers.Bernoulli.Exponential

/-! # Poisson thinning for scaled negative-exponential coins -/

open Set ProbLang
open ENNReal (ofReal)
open scoped ENNReal NNReal

namespace SampLib.ExpMinusScaled

noncomputable section

/-- The bias `exp(-(x/y)*p)`. -/
def bias (p : unitInterval) (x y : ℕ) : unitInterval :=
  ⟨Real.exp (-(x : ℝ) / y * (p : ℝ)), (Real.exp_pos _).le,
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg x))
        (Nat.cast_nonneg _)) p.2.1)⟩

section mathematics

open MeasureTheory

abbrev law (p : unitInterval) (x y : ℕ) : Measure Bool :=
  ProbabilityGeneratingFactory.law (ProbabilityTheory.poissonMeasure (PoissonRational.rate x y))
    (unitInterval.symm p)

/-- A Poisson number of independent failures succeeds with the exponential bias. -/
theorem law_eq (p : unitInterval) (x y : ℕ) : law p x y = RealCoin.law (bias p x y) := by
  have hpgf := Distributions.lintegral_poisson_pow (PoissonRational.rate x y)
    (1 - (p : ℝ)) (sub_nonneg.mpr p.2.2)
  have hexp : (PoissonRational.rate x y : ℝ) * (1 - (p : ℝ) - 1) =
      -(x : ℝ) / y * (p : ℝ) := by
    simp only [PoissonRational.rate, NNReal.coe_div, NNReal.coe_natCast]
    ring
  rw [hexp] at hpgf
  apply BernoulliMixture.eq_bernoulli_of_apply_true
  rw [law, ProbabilityGeneratingFactory.law,
    Measure.bind_apply (measurableSet_singleton true) (measurable_of_countable _).aemeasurable]
  simpa [IterateCoin.law, IterateCoin.bias, RealCoin.law, RealCoin.pmf,
    unitInterval.coe_symm_eq, bias] using hpgf

/-- Conditioning on the Poisson count preserves arbitrary continuation credits. -/
theorem expectation (p : unitInterval) (x y : ℕ) (F : Bool → ℝ≥0∞) :
    ∫⁻ n, IterateCoin.credit (unitInterval.symm p) n F
      ∂ProbabilityTheory.poissonMeasure (PoissonRational.rate x y) =
      RealCoin.credit (bias p x y) F := by
  rw [ProbabilityGeneratingFactory.expectation_preservation]
  change ∫⁻ b, F b ∂law p x y = _
  rw [law_eq, RealCoin.lintegral_law]

end mathematics

theorem expMinusScaled_lc {rT : Type _} :
    (Occil.FactoryExtra.expMinusScaled : Exp rT).IsLocallyClosed := by is_lc

theorem expMinusScaled_fv {rT : Type _} :
    (Occil.FactoryExtra.expMinusScaled : Exp rT).fv = ∅ := by
  simp [Occil.FactoryExtra.expMinusScaled, Exp.fv, PoissonRational.poissonRational_fv,
    Occil.iterateCoin]

@[simp] theorem expMinusScaled_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.FactoryExtra.expMinusScaled = Occil.FactoryExtra.expMinusScaled :=
  (Exp.open_lc k e _ expMinusScaled_lc).symm

@[simp] theorem expMinusScaled_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.FactoryExtra.expMinusScaled : Exp rT) =
      Occil.FactoryExtra.expMinusScaled :=
  Exp.closeRec_fresh x _ k (by simp [expMinusScaled_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Draw the Poisson count, then test that every independent input flip fails. -/
theorem twp_expMinusScaled (E : CoPset) (p : unitInterval) (x y : ℕ) (hy : 0 < y)
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (bias p x y) F) -∗
      tglWp E pl(&Occil.FactoryExtra.expMinusScaled &coin.fst #int (x : ℤ) #int (y : ℤ) #())
        (fun v : Val rT => iprop(∃ r : Bool, ⌜v = Val.bool r⌝ ∗ ↯ (F r))) := by
  iintro Hcredit
  iterate 4 twp_pure
  simp only [PoissonRational.poissonRational_openRec, PoissonRational.poissonRational_closeRec,
    FactorySyntax.iterateCoin_openRec, FactorySyntax.iterateCoin_closeRec]
  twp_bind pl(&Occil.poissonRational #int (x : ℤ) #int (y : ℤ))
  isimp only [← expectation p x y F] at Hcredit
  iapply ((PoissonRational.poissonRational_distSpec E x y hy).wp
    (fun n => IterateCoin.credit (unitInterval.symm p) n F) (measurable_of_countable _) _)
    $$ Hcredit
  iintro %n Hcredit
  twp_pure
  simp only [FactorySyntax.iterateCoin_openRec]
  twp_bind pl(&Occil.iterateCoin &(CoinComplement.callback coin).fst #int (n : ℤ))
  iapply (tglWp_mono fun _ => tglWp_value)
  iapply (IterateCoin.twp_iterateCoin E (unitInterval.symm p) (CoinComplement.callback coin)
    (CoinComplement.distSpec E p coin hcoin) n F) $$ Hcredit

theorem expMinusScaled_distSpec (E : CoPset) (p : unitInterval) (x y : ℕ) (hy : 0 < y)
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.expMinusScaled &coin.fst #int (x : ℤ) #int (y : ℤ) #())
      (RealCoin.law (bias p x y)) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law] using
      wand_entails (twp_expMinusScaled E p x y hy coin hcoin F)

end specification

end

end SampLib.ExpMinusScaled
