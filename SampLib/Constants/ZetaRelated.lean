import SampLib.Constants.Laws.ZetaProductIntegralLaw
import SampLib.Constants.Support.ZetaReciprocal

/-! # The zeta coin from persistent geometric-bag trials -/

open ProbLang
open scoped ENNReal

namespace SampLib.ZetaRelated

noncomputable section

private theorem source_eq {rT : Type} :
    (Occil.Constants.zetaRelated : Exp rT) = (pl%
      fun k u,
        if k < #2 then fail else
          let create := &ZetaBags.create;
          let bags := create k;
          let product := &ZetaBags.product;
          &Occil.oneDivOnePlus (fun v, product bags) #()) := by
  kernel_rfl

private instance create_closed {rT : Type} : ClosedExp (ZetaBags.create : Exp rT) where
  lc := by is_lc
  fv := by simp [ZetaBags.create, Occil.newUniformBag, Exp.fv]

private instance product_closed {rT : Type} : ClosedExp (ZetaBags.product : Exp rT) where
  lc := by is_lc
  fv := by simp [ZetaBags.product, Occil.sampleGeometricBag, Occil.uniformBagStep,
    Occil.newUniformBag, Occil.fairCoin, Exp.fv]

private instance reciprocal_closed {rT : Type} :
    ClosedExp (Occil.oneDivOnePlus : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.oneDivOnePlus, Occil.fairCoin, Exp.fv]

private theorem guard (k : ℕ) (hk : 2 ≤ k) : decide ((k : ℤ) < 2) = false := by
  simp
  omega

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open LatentReal LatentReal.LatentCoin UniformVector

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

/-- The persistent bag product followed by the reciprocal factory samples the eta bias. -/
theorem zetaRelated_distSpec (E : CoPset) (k : ℕ) (hk : 2 ≤ k) :
    IsDistSpec (GF := GF) E pl(&Occil.Constants.zetaRelated #int (k : ℤ) #())
      (RealCoin.law (marginalBias k)) Val.bool where
  spec F _ := by
    iintro Hcredit
    rw [source_eq]
    iterate 3 twp_pure
    rw [guard k hk]
    iterate 2 twp_pure
    twp_bind pl(&(ZetaBags.create : Exp rT) #int (k : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply ZetaBags.twp_create E k
    iintro %v ⟨%roots, %hv, Hstate⟩
    subst v
    iterate 2 twp_pure
    isimp only [RealCoin.lintegral_law, ← expectation_eta k F, conditionalBias] at Hcredit
    ieval (
      change _ ⊢ tglWp E
        pl(&Occil.oneDivOnePlus &(ZetaBags.productCallback roots : Val rT).fst #()) _)
    have h := ZetaBags.twp_reciprocal (rT := rT) (GF := GF) E roots (initial k)
      (fun b _ => F b) (fun _ => measurable_const)
    iapply (tglWp_wand
      (Φ := post (world k) (fun _ => rootsOwns roots) Val.unit (initial k) (fun b _ => F b)))
    isplitl [Hstate Hcredit]
    · iapply h
      iframe Hstate Hcredit
    iintro %v Hpost
    isimp only [post] at Hpost
    icases Hpost with ⟨%b, %q, %hb, Hstate, Hcredit⟩
    rcases hb with ⟨rfl, _⟩
    isimp only [posterior_const] at Hcredit
    iexists b
    iframe Hcredit
    itrivial

end specification

end

end SampLib.ZetaRelated
