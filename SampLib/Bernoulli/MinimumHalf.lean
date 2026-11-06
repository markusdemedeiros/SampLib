import SampLib.Bernoulli.MinimumComplement

/-! # The minimum-half factory -/

open ProbLang
open scoped ENNReal

namespace SampLib.MinimumComplement

noncomputable section

theorem minimumHalf_lc {rT : Type} :
    (Occil.FactoryExtra.minimumHalf : Exp rT).IsLocallyClosed := by is_lc

theorem minimumHalf_fv {rT : Type} : (Occil.FactoryExtra.minimumHalf : Exp rT).fv = ∅ := by
  simp [Occil.FactoryExtra.minimumHalf, Exp.fv, FairCoin.fairCoin_fv,
    minimumComplement_fv]

@[simp] theorem minimumHalf_openRec {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.FactoryExtra.minimumHalf = Occil.FactoryExtra.minimumHalf :=
  (Exp.open_lc k e _ minimumHalf_lc).symm

@[simp] theorem minimumHalf_closeRec {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.FactoryExtra.minimumHalf : Exp rT) =
      Occil.FactoryExtra.minimumHalf :=
  Exp.closeRec_fresh x _ k (by simp [minimumHalf_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem twp_minimumHalf (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (halfBias p) F) -∗
      tglWp E pl(&Occil.FactoryExtra.minimumHalf &coin.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iterate 2 twp_pure
  simp only [minimumComplement_openRec, minimumComplement_closeRec,
    FairCoin.fairCoin_openRec, FairCoin.fairCoin_closeRec]
  twp_bind pl(&Occil.fairCoin #())
  isimp only [← mean_bias, ← RealCoin.lintegral_law,
    ← CoinMean.expectation_preservation] at Hcredit
  iapply ((FairCoin.fairCoin_distSpec E).wp (CoinConditional.firstCredit p (bias p) F)
    (measurable_of_countable _) _) $$ Hcredit
  iintro %a Hcredit
  cases a
  · twp_pure
    isimp only [CoinConditional.firstCredit, Bool.false_eq_true, ite_false] at Hcredit
    iapply (minimumComplement_distSpec E p coin hcoin).spec F (measurable_of_countable _) $$ Hcredit
  · twp_pure
    isimp only [CoinConditional.firstCredit, ite_true] at Hcredit
    iapply hcoin.spec F (measurable_of_countable _) $$ Hcredit

/-- The source samples `Bernoulli(min(p,1/2))`, including both input endpoints. -/
theorem minimumHalf_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.minimumHalf &coin.fst #())
      (RealCoin.law (halfBias p)) Val.bool where
  spec F _ := by
    rw [RealCoin.lintegral_law]
    exact wand_entails (twp_minimumHalf E p coin hcoin F)

end specification

end

end SampLib.MinimumComplement
