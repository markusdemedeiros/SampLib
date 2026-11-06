import SampLib.Samplers.FactorialSeriesFactory

/-! # Cosine factory from the shared-uniform factorial engine -/

open ProbLang

namespace SampLib.CosineFactory

noncomputable section

theorem cosineFactory_lc {rT : Type} :
    (Occil.cosineFactory : Exp rT).IsLocallyClosed := by is_lc

theorem cosineFactory_fv {rT : Type} : (Occil.cosineFactory : Exp rT).fv = ∅ := by
  simp [Occil.cosineFactory, FactorialSeriesFactory.factorialSeriesFactory_fv, Exp.fv]

@[simp] theorem cosineFactory_openRec {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.cosineFactory = Occil.cosineFactory :=
  (Exp.open_lc k e _ cosineFactory_lc).symm

@[simp] theorem cosineFactory_closeRec {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.cosineFactory : Exp rT) = Occil.cosineFactory :=
  Exp.closeRec_fresh x _ k (by simp [cosineFactory_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The named wrapper inherits the concrete factorial-engine specification. -/
theorem cosineFactory_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.cosineFactory &coin.fst #())
      (RealCoin.law (FactorialSeriesFactory.bias .cos p)) Val.bool where
  spec F hF := by
    iintro Hcredit
    iterate 2 twp_pure
    simp only [FactorialSeriesFactory.factorialSeriesFactory_openRec,
      FactorialSeriesFactory.factorialSeriesFactory_closeRec]
    have h := (FactorialSeriesFactory.factorialSeriesFactory_distSpec
      (rT := rT) (GF := GF) E p .cos coin hcoin).spec F hF
    simp only [FactorialSeries.Mode.code] at h
    iapply h $$ Hcredit

end specification

end

end SampLib.CosineFactory
