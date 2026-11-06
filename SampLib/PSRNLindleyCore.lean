import SampLib.PSRNGammaMixtureCore

/-! # The source's shape-one/shape-two Lindley mixture

Its rational selector weight is `rate/(rate+1)`. The constructor keeps the
selected component's entire latent world and every later observation state.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.PSRNLindley.Core

noncomputable section

open LatentReal
open scoped SampLib.PSRNGammaInteger.Program

def rate (a b : ℤ) : ℝ := (a : ℝ) / b

theorem rate_pos (a b : ℤ) (ha : 0 < a) (hb : 0 < b) : 0 < rate a b := by
  exact div_pos (by exact_mod_cast ha) (by exact_mod_cast hb)

private theorem weight_eq (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    RationalCoin.bias a (a + b) ha.le (add_pos ha hb) (by omega) =
      PSRNGammaMixtures.lindleyWeight (rate a b) (rate_pos a b ha hb) := by
  apply Subtype.ext
  dsimp [RationalCoin.bias, PSRNGammaMixtures.lindleyWeight, rate]
  push_cast
  field_simp

private theorem guard (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    (decide (a ≤ 0) || decide (b ≤ 0)) = false := by
  simp only [decide_eq_false (not_le.mpr ha), decide_eq_false (not_le.mpr hb), Bool.or_false]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

local instance mixture_closed : ClosedExp (Occil.PSRN.newGammaMixture : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

private theorem component_spec (E : CoPset) (a b : ℤ) (ha : 0 < a) (hb : 0 < b)
    (D : Model Ω S) (i : S) (O : Val rT → S → IProp GF)
    (hExp : IsLatentDistSpec E pl(&Occil.PSRN.newExponential #a #b #()) D i O) :
    IsLatentDistSpec E pl(&Occil.PSRN.newGammaMixture #a #int (a + b) #1 #2 #a #b #())
      (PSRNGammaMixture.Core.model
        (PSRNGammaMixtures.lindleyWeight (rate a b) (rate_pos a b ha hb)) D i 0 1)
      .initial (PSRNGammaMixture.Core.owns O 0 1) := by
  simpa only [weight_eq a b ha hb, Nat.zero_add, Nat.cast_one, Nat.reduceAdd,
    Nat.cast_ofNat] using
    PSRNGammaMixture.Core.mixture_latentDistSpec E a (a + b) ha.le (add_pos ha hb)
      (by omega) a b D i O hExp 0 1

/-- The unchanged Lindley constructor composes its two verified gamma branches. -/
theorem lindley_latentDistSpec (E : CoPset) (a b : ℤ) (ha : 0 < a) (hb : 0 < b)
    (D : Model Ω S) (i : S) (O : Val rT → S → IProp GF)
    (hExp : IsLatentDistSpec E pl(&Occil.PSRN.newExponential #a #b #()) D i O) :
    IsLatentDistSpec E pl(&Occil.PSRN.newLindley #a #b #())
      (PSRNGammaMixture.Core.model
        (PSRNGammaMixtures.lindleyWeight (rate a b) (rate_pos a b ha hb)) D i 0 1)
      .initial (PSRNGammaMixture.Core.owns O 0 1) := by
  have hmix := component_spec E a b ha hb D i O hExp
  refine ⟨hmix.oracle, ?_⟩
  intro F hF
  iintro Hcredit
  iterate 6 twp_pure
  rw [guard a b ha hb]
  twp_pure
  twp_pure
  isimp only [Exp.ofVal]
  iapply hmix.spec F hF $$ Hcredit

end specification

end

end SampLib.PSRNLindley.Core
