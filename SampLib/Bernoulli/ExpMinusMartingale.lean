import SampLib.Bernoulli.FactorialSeriesFactory

/-! # Exponential factory from the shared-uniform factorial engine -/

open ProbLang

namespace SampLib.ExpMinusMartingale

noncomputable section

theorem expMinusMartingale_lc {rT : Type} :
    (Occil.expMinusMartingale : Exp rT).IsLocallyClosed := by is_lc

theorem expMinusMartingale_fv {rT : Type} : (Occil.expMinusMartingale : Exp rT).fv = ∅ := by
  simp [Occil.expMinusMartingale, FactorialSeriesFactory.factorialSeriesFactory_fv, Exp.fv]

@[simp] theorem expMinusMartingale_openRec {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.expMinusMartingale = Occil.expMinusMartingale :=
  (Exp.open_lc k e _ expMinusMartingale_lc).symm

@[simp] theorem expMinusMartingale_closeRec {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.expMinusMartingale : Exp rT) = Occil.expMinusMartingale :=
  Exp.closeRec_fresh x _ k (by simp [expMinusMartingale_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The named wrapper inherits the concrete factorial-engine specification. -/
theorem expMinusMartingale_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.expMinusMartingale &coin.fst #())
      (RealCoin.law (FactorialSeriesFactory.bias .exp p)) Val.bool where
  spec F hF := by
    iintro Hcredit
    iterate 2 twp_pure
    simp only [FactorialSeriesFactory.factorialSeriesFactory_openRec,
      FactorialSeriesFactory.factorialSeriesFactory_closeRec]
    have h := (FactorialSeriesFactory.factorialSeriesFactory_distSpec
      (rT := rT) (GF := GF) E p .exp coin hcoin).spec F hF
    simp only [FactorialSeries.Mode.code] at h
    iapply h $$ Hcredit

end specification

end

end SampLib.ExpMinusMartingale
