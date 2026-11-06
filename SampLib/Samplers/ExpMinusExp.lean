import SampLib.Samplers.ExpDivThree
import SampLib.FactoryIntegerPower

/-! # Poisson thinning for a doubly exponential coin -/

open ProbLang
open scoped ENNReal

namespace SampLib.ExpMinusExp

noncomputable section

abbrev trialBias (p : unitInterval) (m : ℕ) : unitInterval :=
  IterateCoin.bias EulerScaledConstants.third m * ExpDivThree.bias p

abbrev bias (p : unitInterval) (m : ℕ) : unitInterval :=
  ExpMinusScaled.bias (trialBias p m) (3 ^ (m + 1)) 1

private theorem scaled_trial (p : unitInterval) (m : ℕ) :
    (3 : ℝ) ^ (m + 1) * (trialBias p m : ℝ) = Real.exp ((m : ℝ) + p) := by
  change (3 : ℝ) ^ (m + 1) *
    (((EulerScaledConstants.third : unitInterval) : ℝ) ^ m * (ExpDivThree.bias p : ℝ)) = _
  rw [ExpDivThree.bias_coe]
  simp only [EulerScaledConstants.third, EScaled.bias, Nat.cast_one, Nat.cast_ofNat, mul_one]
  rw [div_pow, pow_succ]
  field_simp
  rw [← Real.exp_nat_mul, Real.exp_add]
  simp

theorem bias_coe (p : unitInterval) (m : ℕ) :
    (bias p m : ℝ) = Real.exp (-Real.exp ((m : ℝ) + p)) := by
  simp only [bias, ExpMinusScaled.bias, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat, div_one]
  rw [neg_mul, scaled_trial]

private def thirdCoin {rT : Type} : Val rT :=
  ⟨Occil.Constants.eDivThree, .lam (by is_lc), by is_lc⟩

private def trial {rT : Type} (coin : Val rT) (m : ℕ) : Val rT :=
  ⟨.lam pl(if &Occil.iterateCoin &thirdCoin.fst #int (m : ℤ) then
    &Occil.FactoryExtra.expDivThree &coin.fst #() else #false), .lam (by is_lc), by is_lc⟩

private theorem pow_cast (m : ℕ) : (3 : ℤ) ^ (m + 1) = (3 ^ (m + 1) : ℕ) := by
  norm_cast

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

private instance power_closed : ClosedExp (Occil.FactoryExtra.intPower : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.FactoryExtra.intPower, Exp.fv]

private instance expDivThree_closed : ClosedExp (Occil.FactoryExtra.expDivThree : Exp rT) where
  lc := by is_lc
  fv := by
    simp [Occil.FactoryExtra.expDivThree, Exp.fv, ClosedExp.closeRec, ClosedExp.fv]

private instance poisson_closed : ClosedExp (Occil.poissonRational : Exp rT) where
  lc := PoissonRational.poissonRational_lc
  fv := PoissonRational.poissonRational_fv

private instance iteration_closed : ClosedExp (Occil.iterateCoin : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.iterateCoin, Exp.fv]

private theorem third_spec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&(thirdCoin : Val rT).fst #())
      (RealCoin.law EulerScaledConstants.third) Val.bool :=
  EulerScaledConstants.eDivThree_distSpec E

private theorem trial_spec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) (m : ℕ) :
    IsDistSpec (GF := GF) E pl(&(trial coin m).fst #()) (RealCoin.law (trialBias p m))
      Val.bool where
  spec F _ := by
    iintro Hcredit
    twp_pure
    twp_bind pl(&Occil.iterateCoin &(thirdCoin : Val rT).fst #int (m : ℤ))
    isimp only [← CoinProduct.expectation_preservation (IterateCoin.bias
      EulerScaledConstants.third m) (ExpDivThree.bias p) F] at Hcredit
    iapply ((IterateCoin.iterateCoin_distSpec E EulerScaledConstants.third
      thirdCoin (third_spec E) m).wp (CoinProduct.firstCredit (ExpDivThree.bias p) F)
      (measurable_of_countable _) _) $$ Hcredit
    iintro %r Hcredit
    cases r
    · twp_pures
      twp_value
      imodintro
      iexists false
      isimp only [CoinProduct.firstCredit, Bool.false_eq_true, ite_false] at Hcredit
      iframe Hcredit
      itrivial
    · twp_pure
      isimp only [CoinProduct.firstCredit, ite_true] at Hcredit
      iapply (ExpDivThree.expDivThree_distSpec E p coin hcoin).spec F
        (measurable_of_countable _) $$ Hcredit

/-- The Poisson mean times the trial bias is exactly `exp(m+p)`. -/
theorem twp_expMinusExp (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (m : ℕ) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (bias p m) F) -∗
      tglWp E pl(&Occil.FactoryExtra.expMinusExp &coin.fst #int (m : ℤ) #())
        (fun v : Val rT => iprop(∃ r : Bool, ⌜v = Val.bool r⌝ ∗ ↯ (F r))) := by
  iintro Hcredit
  iterate 5 twp_pure
  twp_bind pl(&Occil.FactoryExtra.intPower #3 (#int (m : ℤ) + #1))
  twp_pure
  rw [← Nat.cast_add_one]
  iapply tglWp_wand
  isplitl []
  · iapply FactoryIntegerPower.twp_intPower E 3 (m + 1)
  iintro %v %hv
  subst v
  isimp only [Exp.ofVal]
  rw [pow_cast m]
  twp_bind pl(&Occil.poissonRational #int ((3 ^ (m + 1) : ℕ) : ℤ) #1)
  isimp only [← ExpMinusScaled.expectation (trialBias p m) (3 ^ (m + 1)) 1 F] at Hcredit
  iapply ((PoissonRational.poissonRational_distSpec E (3 ^ (m + 1)) 1 (by decide)).wp
    (fun n => IterateCoin.credit (unitInterval.symm (trialBias p m)) n F)
    (measurable_of_countable _) _) $$ Hcredit
  iintro %n Hcredit
  iterate 2 twp_pure
  have hsample := IterateCoin.twp_iterateCoin E (unitInterval.symm (trialBias p m))
    (CoinComplement.callback (trial coin m))
    (CoinComplement.distSpec E (trialBias p m) (trial coin m) (trial_spec E p coin hcoin m)) n F
  twp_bind pl(&Occil.iterateCoin &(CoinComplement.callback (trial coin m)).fst #int (n : ℤ))
  iapply (tglWp_mono fun _ => tglWp_value)
  iapply hsample $$ Hcredit

theorem expMinusExp_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) (m : ℕ) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.expMinusExp &coin.fst #int (m : ℤ) #())
      (RealCoin.law (bias p m)) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law] using
      wand_entails (twp_expMinusExp E p coin hcoin m F)

end specification

end

end SampLib.ExpMinusExp
