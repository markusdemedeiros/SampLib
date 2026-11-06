import SampLib.Core.Syntax.ClosedExp
import Metrology.TotalEris.WpTactics
import Samplers.PSRN.Distributions

/-! # Literal openings for the Sushila and XLindley constructors -/

open ProbLang

namespace SampLib.PSRNLindleyFamilies.Program

private instance lindley_closed {rT : Type} : ClosedExp (Occil.PSRN.newLindley : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

private instance exponential_closed {rT : Type} :
    ClosedExp (Occil.PSRN.newExponential : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

private instance scale_closed {rT : Type} : ClosedExp (Occil.PSRN.scaleRational : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

private instance coin_closed {rT : Type} : ClosedExp (Occil.rationalCoin : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

theorem twp_sushila (E : CoPset) (n d a b : ℤ) (ha : 0 < a) (hb : 0 < b)
    (Φ : Val rT → IProp GF) :
    tglWp E pl(&Occil.PSRN.scaleRational (&Occil.PSRN.newLindley #n #d #()) #a #b) Φ ⊢
      tglWp E pl(&Occil.PSRN.newSushila #n #d #a #b #()) Φ := by
  iintro H
  iterate 8 twp_pure
  rw [show (decide (a ≤ 0) || decide (b ≤ 0)) = false by
    simp [not_le.mpr ha, not_le.mpr hb]]
  twp_pure
  iexact H

theorem twp_xlindley (E : CoPset) (n d : ℤ) (Φ : Val rT → IProp GF) :
    tglWp E pl(if &Occil.rationalCoin #n #int (n + d) then
      &Occil.PSRN.newExponential #n #d #() else &Occil.PSRN.newLindley #n #d #()) Φ ⊢
      tglWp E pl(&Occil.PSRN.newXLindley #n #d #()) Φ := by
  iintro H
  iterate 4 twp_pure
  iexact H

end specification

end SampLib.PSRNLindleyFamilies.Program
