import SampLib.Templates
import Samplers.Continuous
import Metrology.TotalEris.Examples.Samplers.RealDecrTrial
import Metrology.Iris.LocalBI

/-! # Decreasing uniform chains

Occil's chain is the upstream `DecrTrial` term. Its factorial-difference law and
CTE proof therefore apply directly, including starts at zero and one.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.DecreasingTrial

noncomputable section

open TotalEris.Examples

/-- Expected credit under the factorial-difference law, shifted by the initial count. -/
abbrev credit := RealDecrTrialCreditV

theorem implementation_eq {rT : Type _} :
    (Occil.decreasingTrial : Exp rT) = DecrTrial := rfl

theorem decreasingTrial_lc {rT : Type _} :
    (Occil.decreasingTrial : Exp rT).IsLocallyClosed := by is_lc

theorem decreasingTrial_fv {rT : Type _} :
    (Occil.decreasingTrial : Exp rT).fv = ∅ := by
  simp [Occil.decreasingTrial, Exp.fv]

@[simp] theorem decreasingTrial_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.decreasingTrial = Occil.decreasingTrial :=
  (Exp.open_lc k e _ decreasingTrial_lc).symm

@[simp] theorem decreasingTrial_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.decreasingTrial : Exp rT) = Occil.decreasingTrial :=
  Exp.closeRec_fresh x _ k (by simp [decreasingTrial_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
local bi (IProp GF)

/-- Reuse the verified identical chain, retaining its natural-valued output. -/
theorem twp_decreasingTrial (E : CoPset) (F : ℕ → ℝ≥0∞) (n : ℕ) (x : ℝ)
    (hx : 0 ≤ x ∧ x ≤ 1) :
    ⊢ ↯ (credit F n x) -∗
      tglWp E pl(&Occil.decreasingTrial #int (n : ℤ) #real x)
        (fun v : Val ℝ => iprop(∃ k : ℕ, ⌜v = Val.int k⌝ ∗ ↯ (F k))) := by
  iintro Hcredit
  rw [implementation_eq]
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply (twp_DecrTrial E F n x hx) $$ Hcredit
  iintro %v ⟨%k, %hv, Hcredit⟩
  iexists k
  iframe Hcredit
  ipureintro
  exact Val.ext hv

end specification

end

end SampLib.DecreasingTrial
