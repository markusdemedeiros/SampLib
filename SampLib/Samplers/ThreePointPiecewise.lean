import SampLib.Samplers.MinimumHalf
import SampLib.CoinExpression
import Samplers.Bernoulli.Polynomials

/-! # The six three-point piecewise-linear factories -/

open ProbLang
open scoped ENNReal

namespace SampLib.MinimumComplement

noncomputable section

private def branch {rT : Type} (coin mu nu : Val rT) : Fin 6 → Exp rT
  | 0 => pl(if &nu.fst #() then
      if &mu.fst #() then &coin.fst #() else &Occil.FactoryExtra.minimumComplement &coin.fst #()
      else #false)
  | 1 => pl(if &Occil.fairCoin #() then &Occil.FactoryExtra.minimumComplement &coin.fst #()
      else if &mu.fst #() then &coin.fst #() else ~(&coin.fst #()))
  | 2 => pl(if &mu.fst #() then &Occil.FactoryExtra.minimumHalf &coin.fst #() else #false)
  | 3 => pl(if &mu.fst #() then ~(&coin.fst #())
      else &Occil.FactoryExtra.minimumComplement &coin.fst #())
  | 4 => pl(if &mu.fst #() then ~(&Occil.FactoryExtra.minimumComplement &coin.fst #())
      else ~(&coin.fst #()))
  | 5 => pl(if &mu.fst #() then ~(&Occil.FactoryExtra.minimumComplement &coin.fst #())
      else &coin.fst #())

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem branch_distSpec (E : CoPset) (p μ ν : unitInterval)
    (coin mu nu : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (hmu : IsDistSpec (GF := GF) E pl(&mu.fst #()) (RealCoin.law μ) Val.bool)
    (hnu : IsDistSpec (GF := GF) E pl(&nu.fst #()) (RealCoin.law ν) Val.bool)
    (mode : Fin 6) :
    IsDistSpec (GF := GF) E (branch coin mu nu mode)
      (RealCoin.law (piecewiseBias p μ ν mode)) Val.bool := by
  have hmin := minimumComplement_distSpec E p coin hcoin
  have hhalf := minimumHalf_distSpec E p coin hcoin
  have hnot := CoinExpression.negate E p _ hcoin
  have hnotmin := CoinExpression.negate E (bias p) _ hmin
  fin_cases mode
  · exact CoinExpression.conditional E _ 0 ν _ _ _
      (CoinExpression.conditional E p (bias p) μ _ _ _ hcoin hmin hmu)
      (CoinExpression.false_spec E) hnu
  · exact CoinExpression.conditional E (bias p) _ VonNeumann.fairBias _ _ _ hmin
      (CoinExpression.conditional E p (unitInterval.symm p) μ _ _ _ hcoin hnot hmu)
      (FairCoin.fairCoin_distSpec E)
  · exact CoinExpression.conditional E (halfBias p) 0 μ _ _ _ hhalf
      (CoinExpression.false_spec E) hmu
  · exact CoinExpression.conditional E (unitInterval.symm p) (bias p) μ _ _ _ hnot hmin hmu
  · exact CoinExpression.conditional E (unitInterval.symm (bias p)) (unitInterval.symm p)
      μ _ _ _ hnotmin hnot hmu
  · exact CoinExpression.conditional E (unitInterval.symm (bias p)) p μ _ _ _
      hnotmin hcoin hmu

theorem twp_threePointPiecewise (E : CoPset) (p μ ν : unitInterval)
    (coin mu nu : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (hmu : IsDistSpec (GF := GF) E pl(&mu.fst #()) (RealCoin.law μ) Val.bool)
    (hnu : IsDistSpec (GF := GF) E pl(&nu.fst #()) (RealCoin.law ν) Val.bool)
    (mode : Fin 6) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (piecewiseBias p μ ν mode) F) -∗
      tglWp E pl(&Occil.FactoryExtra.threePointPiecewise &coin.fst &mu.fst &nu.fst
        #int (mode.val : ℤ) #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iterate 5 twp_pure
  simp only [minimumComplement_openRec, minimumComplement_closeRec,
    minimumHalf_openRec, minimumHalf_closeRec, FairCoin.fairCoin_openRec,
    FairCoin.fairCoin_closeRec]
  isimp only [← RealCoin.lintegral_law] at Hcredit
  have hs := branch_distSpec E p μ ν coin mu nu hcoin hmu hnu mode
  fin_cases mode
  · iterate 2 twp_pure
    simp only [branch] at hs
    iapply hs.spec F (measurable_of_countable _) $$ Hcredit
  · iterate 4 twp_pure
    simp only [branch] at hs
    iapply hs.spec F (measurable_of_countable _) $$ Hcredit
  · iterate 6 twp_pure
    simp only [branch] at hs
    iapply hs.spec F (measurable_of_countable _) $$ Hcredit
  · iterate 8 twp_pure
    simp only [branch] at hs
    iapply hs.spec F (measurable_of_countable _) $$ Hcredit
  · iterate 10 twp_pure
    simp only [branch] at hs
    iapply hs.spec F (measurable_of_countable _) $$ Hcredit
  · iterate 12 twp_pure
    simp only [branch] at hs
    iapply hs.spec F (measurable_of_countable _) $$ Hcredit

/-- Each mode gives its documented three-point piecewise-linear coin law. -/
theorem threePointPiecewise_distSpec (E : CoPset) (p μ ν : unitInterval)
    (coin mu nu : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (hmu : IsDistSpec (GF := GF) E pl(&mu.fst #()) (RealCoin.law μ) Val.bool)
    (hnu : IsDistSpec (GF := GF) E pl(&nu.fst #()) (RealCoin.law ν) Val.bool)
    (mode : Fin 6) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.threePointPiecewise &coin.fst &mu.fst &nu.fst
        #int (mode.val : ℤ) #())
      (RealCoin.law (piecewiseBias p μ ν mode)) Val.bool where
  spec F _ := by
    rw [RealCoin.lintegral_law]
    exact wand_entails (twp_threePointPiecewise E p μ ν coin mu nu hcoin hmu hnu mode F)

end specification

end

end SampLib.MinimumComplement
