import SampLib.PSRN.PSRNLindley
import SampLib.PSRN.Support.LatentRealConstructors
import SampLib.PSRN.Support.LatentMixture
import SampLib.PSRN.Laws.PSRNDistributionMixtures
import SampLib.PSRN.Syntax.PSRNLindleyFamilies

/-! # Sushila scaling and the exponential–Lindley mixture

Sushila scales the actual Lindley oracle by `a/b`; XLindley selects an exponential
with probability `θ/(θ+1)`, and a Lindley draw otherwise. Both keep every component
of the returned oracle's latent world.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.PSRNLindleyFamilies

noncomputable section

open LatentReal

abbrev rate := PSRNLindley.rate

theorem rate_pos (n d : ℤ) (hn : 0 < n) (hd : 0 < d) : 0 < rate n d :=
  PSRNRationalRateDecay.rate_pos n d hn hd

def sushilaModel (n d a b : ℤ) (hn : 0 < n) (hd : 0 < d) :=
  (PSRNLindley.model n d hn hd).scale ((a : ℝ) / b)

def selector (n d : ℤ) (hn : 0 < n) (hd : 0 < d) : unitInterval :=
  RationalCoin.bias n (n + d) hn.le (by omega) (by omega)

def xlindleyModel (n d : ℤ) (hn : 0 < n) (hd : 0 < d) :=
  MixtureModel.model (selector n d hn hd)
    (LatentExponential.model (rate n d) (rate_pos n d hn hd))
    (PSRNLindley.model n d hn hd) (LatentExponential.initial (rate n d)) .initial

section mathematics

open MeasureTheory ProbabilityTheory
open ENNReal (ofReal)

/-- Sushila is the positive scale family of Lindley distributions. -/
theorem sushila_model_law (n d a b : ℤ) (hn : 0 < n) (hd : 0 < d) :
    (sushilaModel n d a b hn hd).law .initial =
      (volume.withDensity (fun x => ofReal (PSRNGammaMixtures.lindleyPDFReal (rate n d) x))).map
        (fun x => x * ((a : ℝ) / b)) := by
  rw [sushilaModel, Model.scale_law, PSRNLindley.model_law_density]

/-- The XLindley selector is the Lindley weight `θ/(θ+1)`. -/
theorem selector_eq (n d : ℤ) (hn : 0 < n) (hd : 0 < d) :
    selector n d hn hd = PSRNGammaMixtures.lindleyWeight (rate n d) (rate_pos n d hn hd) := by
  apply Subtype.ext
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  dsimp [selector, RationalCoin.bias, PSRNGammaMixtures.lindleyWeight, rate,
    PSRNGammaInteger.rate]
  push_cast
  field_simp

/-- Exponential plus Lindley is again a shape-one/two mixture, with this weight. -/
def xlindleyWeight (θ : ℝ) (hθ : 0 < θ) : unitInterval :=
  ⟨θ * (θ + 2) / (θ + 1) ^ 2, by positivity,
    (div_le_one (by positivity)).mpr (by nlinarith)⟩

/-- The standard XLindley density. -/
def xlindleyPDFReal (θ x : ℝ) : ℝ :=
  if 0 ≤ x then θ ^ 2 * (2 + θ + x) / (1 + θ) ^ 2 * Real.exp (-(θ * x)) else 0

/-- Since `Exp(θ) = Γ(1,θ)`, the outer selector folds into Lindley's gamma mixture. -/
theorem xlindley_law (θ : ℝ) (hθ : 0 < θ) :
    let p := PSRNGammaMixtures.lindleyWeight θ hθ
    (ofReal (p : ℝ) • expMeasure θ) + (ofReal (1 - (p : ℝ)) • PSRNGammaMixtures.law p 1 2 θ) =
      PSRNGammaMixtures.law (xlindleyWeight θ hθ) 1 2 θ := by
  intro p
  have hp := p.2.1
  have hq := sub_nonneg.mpr p.2.2
  simp only [PSRNGammaMixtures.law, expMeasure, smul_add, smul_smul, ← add_assoc, ← add_smul,
    ← ENNReal.ofReal_mul hq, ← ENNReal.ofReal_add hp (mul_nonneg hq hp)]
  congr 3 <;> simp only [p, PSRNGammaMixtures.lindleyWeight, xlindleyWeight] <;>
    field_simp <;> ring

theorem xlindley_density (θ : ℝ) (hθ : 0 < θ) (x : ℝ) :
    PSRNDistributionMixtures.density (xlindleyWeight θ hθ) 1 2 θ x =
      ofReal (xlindleyPDFReal θ x) := by
  by_cases hx : 0 ≤ x
  · rw [PSRNDistributionMixtures.density_one_two _ hθ hx]
    simp only [xlindleyWeight, xlindleyPDFReal, ite_eq_left hx]
    congr 1
    field_simp
    ring
  · simp [PSRNDistributionMixtures.density, gammaPDF, gammaPDFReal, xlindleyPDFReal, hx]

/-- The actual outer selector gives XLindley's canonical density. -/
theorem xlindley_model_law (n d : ℤ) (hn : 0 < n) (hd : 0 < d) :
    (xlindleyModel n d hn hd).law .initial =
      volume.withDensity (fun x => ofReal (xlindleyPDFReal (rate n d) x)) := by
  rw [xlindleyModel, MixtureModel.law_initial, LatentExponential.initial_law,
    PSRNLindley.model_law, selector_eq, xlindley_law, PSRNGammaMixtures.law_eq_withDensity]
  congr 1
  funext x
  exact xlindley_density _ (rate_pos n d hn hd) x

end mathematics

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

abbrev sushilaOwns (n d a b : ℤ) :=
  scaleRationalOwns (PSRNLindley.owns (rT := rT) (GF := GF) n d) a b

abbrev xlindleyOwns (n d : ℤ) :=
  Mixture.owns (PSRNExponential.rationalOwns (rT := rT) (GF := GF) n d)
    (PSRNLindley.owns n d)

/-- Construction scales the Lindley oracle without observing its latent value. -/
theorem newSushila_latentDistSpec (E : CoPset) (n d a b : ℤ)
    (hn : 0 < n) (hd : 0 < d) (ha : 0 < a) (hb : 0 < b) :
    IsLatentDistSpec (GF := GF) E pl(&Occil.PSRN.newSushila #n #d #a #b #())
      (sushilaModel n d a b hn hd) .initial (sushilaOwns n d a b) where
  oracle := scaleRational_oracleSpec E _ _
    (PSRNLindley.newLindley_latentDistSpec E n d hn hd).oracle a b hb
  spec F hF := by
    iintro Hcredit
    isimp only [sushilaModel, Model.scale] at Hcredit
    iapply Program.twp_sushila E n d a b ha hb _
    twp_bind pl(&Occil.PSRN.newLindley #n #d #())
    iapply (PSRNLindley.newLindley_latentDistSpec E n d hn hd).wp F hF _ $$ Hcredit
    iintro %source %t %ht Hstate Hcredit
    isimp only [Exp.ofVal]
    iapply tglWp_wand
    isplitl [Hstate]
    · iapply twp_scaleRational E (PSRNLindley.owns n d) source t a b hb $$ Hstate
    iintro %v Hstate
    iexists t
    isimp only [sushilaModel, Model.scale]
    iframe Hstate Hcredit
    ipureintro
    exact ht

/-- The rational selector keeps the chosen component's complete latent posterior. -/
theorem newXLindley_latentDistSpec (E : CoPset) (n d : ℤ) (hn : 0 < n) (hd : 0 < d) :
    IsLatentDistSpec (GF := GF) E pl(&Occil.PSRN.newXLindley #n #d #())
      (xlindleyModel n d hn hd) .initial (xlindleyOwns n d) := by
  have hcore := Mixture.latentDistSpec (GF := GF) E (selector n d hn hd)
    pl(&Occil.rationalCoin #n #int (n + d))
    pl(&Occil.PSRN.newExponential #n #d #()) pl(&Occil.PSRN.newLindley #n #d #())
    _ _ _ _ _ _ (RationalCoin.rationalCoin_distSpec E n (n + d) hn.le (by omega) (by omega))
    (PSRNExponential.newExponential_latentDistSpec E n d hn hd)
    (PSRNLindley.newLindley_latentDistSpec E n d hn hd)
  unfold xlindleyModel
  refine ⟨hcore.oracle, ?_⟩
  intro F hF
  iintro Hcredit
  iapply Program.twp_xlindley E n d _
  iapply hcore.spec F hF $$ Hcredit

end specification

end

end SampLib.PSRNLindleyFamilies
