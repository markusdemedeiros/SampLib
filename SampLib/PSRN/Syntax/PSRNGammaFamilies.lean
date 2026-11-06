import SampLib.Core.Syntax.ClosedExp
import Metrology.TotalEris.WpTactics
import Samplers.PSRN.Distributions

/-! # Literal parameter openings for the named gamma-mixture constructors -/

open ProbLang

namespace SampLib.PSRNGammaFamilies.Program

private instance gamma_closed {rT : Type} : ClosedExp (Occil.PSRN.newGammaMixture : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

theorem twp_garima (E : CoPset) (n d : ℤ) (Φ : Val rT → IProp GF) :
    tglWp E pl(&Occil.PSRN.newGammaMixture #int (n + d) #int (n + 2 * d) #1 #2 #n #d #()) Φ ⊢
      tglWp E pl(&Occil.PSRN.newGarima #n #d #()) Φ := by
  iintro H
  iterate 6 twp_pure
  isimp only [Exp.ofVal]
  iexact H

theorem twp_igarima (E : CoPset) (n d : ℤ) (Φ : Val rT → IProp GF) :
    tglWp E pl(&Occil.PSRN.newGammaMixture #int (n + 2 * d) #int (n + 3 * d)
      #1 #2 #n #d #()) Φ ⊢ tglWp E pl(&Occil.PSRN.newIGarima #n #d #()) Φ := by
  iintro H
  iterate 7 twp_pure
  isimp only [Exp.ofVal]
  iexact H

theorem twp_weightedExponentialGamma (E : CoPset) (n d : ℤ) (Φ : Val rT → IProp GF) :
    tglWp E pl(&Occil.PSRN.newGammaMixture #n #int (n + d) #2 #3 #n #d #()) Φ ⊢
      tglWp E pl(&Occil.PSRN.newWeightedExponentialGamma #n #d #()) Φ := by
  iintro H
  iterate 4 twp_pure
  isimp only [Exp.ofVal]
  iexact H

theorem twp_xgamma (E : CoPset) (n d : ℤ) (Φ : Val rT → IProp GF) :
    tglWp E pl(&Occil.PSRN.newGammaMixture #n #int (n + d) #1 #3 #n #d #()) Φ ⊢
      tglWp E pl(&Occil.PSRN.newXgamma #n #d #()) Φ := by
  iintro H
  iterate 4 twp_pure
  isimp only [Exp.ofVal]
  iexact H

theorem twp_mirra (E : CoPset) (n d an ad : ℤ) (han : 0 < an) (had : 0 < ad)
    (Φ : Val rT → IProp GF) :
    tglWp E pl(&Occil.PSRN.newGammaMixture #int (n * n * ad)
      #int (an * d * d + n * n * ad) #1 #3 #n #d #()) Φ ⊢
      tglWp E pl(&Occil.PSRN.newMirra #n #d #an #ad #()) Φ := by
  iintro H
  iterate 8 twp_pure
  rw [show (decide (an ≤ 0) || decide (ad ≤ 0)) = false by
    simp [not_le.mpr han, not_le.mpr had]]
  iterate 8 twp_pure
  isimp only [Exp.ofVal]
  iexact H

end specification

end SampLib.PSRNGammaFamilies.Program
