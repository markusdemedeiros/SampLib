import SampLib.PSRNGammaIntegerCore
import SampLib.LatentMixture
import SampLib.Samplers.RationalCoin
import SampLib.Distributions.PSRNGammaMixtures

/-! # The source's mixture of two positive integer gamma draws

The selector remains part of the latent world. Both endpoint weights are allowed;
subsequent observations retain the chosen component and its whole joint state.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.PSRNGammaMixture.Core

noncomputable section

open LatentReal
open scoped SampLib.PSRNGammaInteger.Program

section models

variable {Ω S : Type} [MeasurableSpace Ω]

def model (p : unitInterval) (D : Model Ω S) (i : S) (n m : ℕ) :=
  MixtureModel.model p (LatentGammaInteger.model D n) (LatentGammaInteger.model D m)
    (LatentGammaInteger.initial i n) (LatentGammaInteger.initial i m)

/-- Canonical gamma laws are mixed with the source selector's exact weight. -/
theorem model_law (p : unitInterval) (D : Model Ω S) (i : S) (rate : ℝ) (hrate : 0 < rate)
    (hD : D.law i = ProbabilityTheory.expMeasure rate) (n m : ℕ) :
    (model p D i n m).law .initial =
      PSRNGammaMixtures.law p ((n + 1 : ℕ) : ℝ) ((m + 1 : ℕ) : ℝ) rate := by
  rw [model, MixtureModel.law_initial,
    LatentGammaInteger.model_law D i rate hrate hD n,
    LatentGammaInteger.model_law D i rate hrate hD m]
  rfl

theorem measurable_error (p : unitInterval) (D : Model Ω S) (i : S)
    (hD : D.MeasurableError) (n m : ℕ) : (model p D i n m).MeasurableError := by
  intro precision
  exact ((LatentGammaInteger.measurable_error D hD n) precision).sumElim
    ((LatentGammaInteger.measurable_error D hD m) precision)

end models

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

local instance rational_closed : ClosedExp (Occil.rationalCoin : Exp rT) where
  lc := RationalCoin.rationalCoin_lc
  fv := RationalCoin.rationalCoin_fv

abbrev owns (O : Val rT → S → IProp GF) (n m : ℕ) :=
  Mixture.owns (PSRNGammaInteger.Core.owns O n) (PSRNGammaInteger.Core.owns O m)

/-- Execute the literal selector and whichever positive-shape constructor it chooses. -/
theorem mixture_latentDistSpec (E : CoPset) (wa wb : ℤ) (hwa : 0 ≤ wa) (hwb : 0 < wb)
    (hw : wa ≤ wb) (a b : ℤ) (D : Model Ω S) (i : S) (O : Val rT → S → IProp GF)
    (hExp : IsLatentDistSpec E pl(&Occil.PSRN.newExponential #a #b #()) D i O) (n m : ℕ) :
    IsLatentDistSpec E
      pl(&Occil.PSRN.newGammaMixture #wa #wb #int ((n + 1 : ℕ) : ℤ)
        #int ((m + 1 : ℕ) : ℤ) #a #b #())
      (model (RationalCoin.bias wa wb hwa hwb hw) D i n m) .initial (owns O n m) := by
  have hmix := Mixture.latentDistSpec E (RationalCoin.bias wa wb hwa hwb hw)
    pl(&Occil.rationalCoin #wa #wb)
    pl(&Occil.PSRN.newGammaInteger #int ((n + 1 : ℕ) : ℤ) #a #b)
    pl(&Occil.PSRN.newGammaInteger #int ((m + 1 : ℕ) : ℤ) #a #b)
    (LatentGammaInteger.model D n) (LatentGammaInteger.model D m)
    (LatentGammaInteger.initial i n) (LatentGammaInteger.initial i m)
    (PSRNGammaInteger.Core.owns O n) (PSRNGammaInteger.Core.owns O m)
    (RationalCoin.rationalCoin_distSpec E wa wb hwa hwb hw)
    (PSRNGammaInteger.Core.integer_latentDistSpec E a b D i O hExp n)
    (PSRNGammaInteger.Core.integer_latentDistSpec E a b D i O hExp m)
  refine ⟨hmix.oracle, ?_⟩
  intro F hF
  isimp only [model, owns]
  iintro Hcredit
  iterate 7 twp_pure
  iapply hmix.spec F hF $$ Hcredit

end specification

end

end SampLib.PSRNGammaMixture.Core
