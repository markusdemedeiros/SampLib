import SampLib.PSRN.PSRNGammaMixture
import SampLib.PSRN.Laws.PSRNGammaFamilySelectors
import SampLib.PSRN.Syntax.PSRNGammaFamilies

/-! # Garima, i-Garima, xgamma, weighted exponential-gamma, and Mirra

Each constructor specializes the actual positive-integer gamma-mixture sampler.
The selected component remains part of the latent world through every later read.
-/

open ProbLang

namespace SampLib.PSRNGammaFamilies

noncomputable section

open LatentReal

def garimaModel (n d : ℤ) (hn : 0 < n) (hd : 0 < d) :=
  PSRNGammaMixture.model (garimaBias n d hn hd) 1 2 n d hn hd

def igarimaModel (n d : ℤ) (hn : 0 < n) (hd : 0 < d) :=
  PSRNGammaMixture.model (igarimaBias n d hn hd) 1 2 n d hn hd

def xgammaModel (n d : ℤ) (hn : 0 < n) (hd : 0 < d) :=
  PSRNGammaMixture.model (baseBias n d hn hd) 1 3 n d hn hd

def weightedExponentialGammaModel (n d : ℤ) (hn : 0 < n) (hd : 0 < d) :=
  PSRNGammaMixture.model (baseBias n d hn hd) 2 3 n d hn hd

def mirraModel (n d an ad : ℤ) (hn : 0 < n) (hd : 0 < d) (han : 0 < an) (had : 0 < ad) :=
  PSRNGammaMixture.model (mirraBias n d an ad hn hd han had) 1 3 n d hn hd

/-- Garima's selector is `(θ+1)/(θ+2)` at rate `θ=n/d`. -/
theorem garima_model_law (n d : ℤ) (hn : 0 < n) (hd : 0 < d) :
    (garimaModel n d hn hd).law .initial =
      PSRNGammaMixtures.law
        (PSRNGammaFamilyDensities.garimaWeight (rate n d) (rate_pos n d hn hd))
        1 2 (rate n d) := by
  rw [garimaModel, PSRNGammaMixture.model_law _ _ _ _ _ (by decide) (by decide) hn hd,
    garimaBias_eq]
  norm_num [rate, PSRNGammaMixture.rate, PSRNGammaInteger.rate]

theorem igarima_model_law (n d : ℤ) (hn : 0 < n) (hd : 0 < d) :
    (igarimaModel n d hn hd).law .initial =
      PSRNGammaMixtures.law
        (PSRNGammaFamilyDensities.igarimaWeight (rate n d) (rate_pos n d hn hd))
        1 2 (rate n d) := by
  rw [igarimaModel, PSRNGammaMixture.model_law _ _ _ _ _ (by decide) (by decide) hn hd,
    igarimaBias_eq]
  norm_num [rate, PSRNGammaMixture.rate, PSRNGammaInteger.rate]

theorem xgamma_model_law (n d : ℤ) (hn : 0 < n) (hd : 0 < d) :
    (xgammaModel n d hn hd).law .initial =
      PSRNGammaMixtures.law
        (PSRNGammaMixtures.lindleyWeight (rate n d) (rate_pos n d hn hd)) 1 3 (rate n d) := by
  rw [xgammaModel, PSRNGammaMixture.model_law _ _ _ _ _ (by decide) (by decide) hn hd,
    baseBias_eq]
  norm_num [rate, PSRNGammaMixture.rate, PSRNGammaInteger.rate]

theorem weightedExponentialGamma_model_law (n d : ℤ) (hn : 0 < n) (hd : 0 < d) :
    (weightedExponentialGammaModel n d hn hd).law .initial =
      PSRNGammaMixtures.law
        (PSRNGammaMixtures.lindleyWeight (rate n d) (rate_pos n d hn hd)) 2 3 (rate n d) := by
  rw [weightedExponentialGammaModel,
    PSRNGammaMixture.model_law _ _ _ _ _ (by decide) (by decide) hn hd, baseBias_eq]
  rfl

theorem mirra_model_law (n d an ad : ℤ) (hn : 0 < n) (hd : 0 < d)
    (han : 0 < an) (had : 0 < ad) :
    (mirraModel n d an ad hn hd han had).law .initial =
      PSRNGammaMixtures.law (PSRNGammaFamilyDensities.mirraWeight
        (rate n d) ((an : ℝ) / ad) (rate_pos n d hn hd)
        (div_pos (by exact_mod_cast han) (by exact_mod_cast had))) 1 3 (rate n d) := by
  rw [mirraModel, PSRNGammaMixture.model_law _ _ _ _ _ (by decide) (by decide) hn hd,
    mirraBias_eq]
  norm_num [rate, PSRNGammaMixture.rate, PSRNGammaInteger.rate]

section densities

open MeasureTheory
open ENNReal (ofReal)
open PSRNGammaFamilyDensities

/-- Each named mixture has its family's standard density. -/
theorem garima_model_law_density (n d : ℤ) (hn : 0 < n) (hd : 0 < d) :
    (garimaModel n d hn hd).law .initial =
      volume.withDensity (fun x => ofReal (garimaPDF (rate n d) x)) := by
  rw [garima_model_law, PSRNGammaMixtures.law_eq_withDensity]
  exact congrArg _ (funext (garima_density _ (rate_pos n d hn hd)))

theorem igarima_model_law_density (n d : ℤ) (hn : 0 < n) (hd : 0 < d) :
    (igarimaModel n d hn hd).law .initial =
      volume.withDensity (fun x => ofReal (igarimaPDF (rate n d) x)) := by
  rw [igarima_model_law, PSRNGammaMixtures.law_eq_withDensity]
  exact congrArg _ (funext (igarima_density _ (rate_pos n d hn hd)))

theorem xgamma_model_law_density (n d : ℤ) (hn : 0 < n) (hd : 0 < d) :
    (xgammaModel n d hn hd).law .initial =
      volume.withDensity (fun x => ofReal (xgammaPDF (rate n d) x)) := by
  rw [xgamma_model_law, PSRNGammaMixtures.law_eq_withDensity]
  exact congrArg _ (funext (xgamma_density _ (rate_pos n d hn hd)))

theorem weightedExponentialGamma_model_law_density (n d : ℤ) (hn : 0 < n) (hd : 0 < d) :
    (weightedExponentialGammaModel n d hn hd).law .initial =
      volume.withDensity (fun x => ofReal (weightedExponentialGammaPDF (rate n d) x)) := by
  rw [weightedExponentialGamma_model_law, PSRNGammaMixtures.law_eq_withDensity]
  exact congrArg _ (funext (weightedExponentialGamma_density _ (rate_pos n d hn hd)))

theorem mirra_model_law_density (n d an ad : ℤ) (hn : 0 < n) (hd : 0 < d)
    (han : 0 < an) (had : 0 < ad) :
    (mirraModel n d an ad hn hd han had).law .initial =
      volume.withDensity (fun x => ofReal (mirraPDF (rate n d) ((an : ℝ) / ad) x)) := by
  rw [mirra_model_law, PSRNGammaMixtures.law_eq_withDensity]
  exact congrArg _ (funext (mirra_density _ _ (rate_pos n d hn hd) _))

end densities

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem newGarima_latentDistSpec (E : CoPset) (n d : ℤ) (hn : 0 < n) (hd : 0 < d) :
    IsLatentDistSpec (rT := rT) (GF := GF) E pl(&Occil.PSRN.newGarima #n #d #())
      (garimaModel n d hn hd) .initial (PSRNGammaMixture.owns 1 2 n d) := by
  have hcore := PSRNGammaMixture.newGammaMixture_latentDistSpec (rT := rT) (GF := GF) E
    (n + d) (n + 2 * d) (by omega) (by omega) (by omega) 1 2 n d (by decide) (by decide) hn hd
  unfold garimaModel garimaBias
  refine ⟨hcore.oracle, ?_⟩
  intro F hF
  iintro Hcredit
  iapply Program.twp_garima E n d _
  iapply hcore.spec F hF $$ Hcredit

theorem newIGarima_latentDistSpec (E : CoPset) (n d : ℤ) (hn : 0 < n) (hd : 0 < d) :
    IsLatentDistSpec (rT := rT) (GF := GF) E pl(&Occil.PSRN.newIGarima #n #d #())
      (igarimaModel n d hn hd) .initial (PSRNGammaMixture.owns 1 2 n d) := by
  have hcore := PSRNGammaMixture.newGammaMixture_latentDistSpec (rT := rT) (GF := GF) E
    (n + 2 * d) (n + 3 * d) (by omega) (by omega) (by omega) 1 2 n d
    (by decide) (by decide) hn hd
  unfold igarimaModel igarimaBias
  refine ⟨hcore.oracle, ?_⟩
  intro F hF
  iintro Hcredit
  iapply Program.twp_igarima E n d _
  iapply hcore.spec F hF $$ Hcredit

theorem newXgamma_latentDistSpec (E : CoPset) (n d : ℤ) (hn : 0 < n) (hd : 0 < d) :
    IsLatentDistSpec (rT := rT) (GF := GF) E pl(&Occil.PSRN.newXgamma #n #d #())
      (xgammaModel n d hn hd) .initial (PSRNGammaMixture.owns 1 3 n d) := by
  have hcore := PSRNGammaMixture.newGammaMixture_latentDistSpec (rT := rT) (GF := GF) E
    n (n + d) hn.le (by omega) (by omega) 1 3 n d (by decide) (by decide) hn hd
  unfold xgammaModel baseBias
  refine ⟨hcore.oracle, ?_⟩
  intro F hF
  iintro Hcredit
  iapply Program.twp_xgamma E n d _
  iapply hcore.spec F hF $$ Hcredit

theorem newWeightedExponentialGamma_latentDistSpec (E : CoPset) (n d : ℤ)
    (hn : 0 < n) (hd : 0 < d) :
    IsLatentDistSpec (rT := rT) (GF := GF) E
      pl(&Occil.PSRN.newWeightedExponentialGamma #n #d #())
      (weightedExponentialGammaModel n d hn hd) .initial (PSRNGammaMixture.owns 2 3 n d) := by
  have hcore := PSRNGammaMixture.newGammaMixture_latentDistSpec (rT := rT) (GF := GF) E
    n (n + d) hn.le (by omega) (by omega) 2 3 n d (by decide) (by decide) hn hd
  unfold weightedExponentialGammaModel baseBias
  refine ⟨hcore.oracle, ?_⟩
  intro F hF
  iintro Hcredit
  iapply Program.twp_weightedExponentialGamma E n d _
  iapply hcore.spec F hF $$ Hcredit

theorem newMirra_latentDistSpec (E : CoPset) (n d an ad : ℤ) (hn : 0 < n) (hd : 0 < d)
    (han : 0 < an) (had : 0 < ad) :
    IsLatentDistSpec (rT := rT) (GF := GF) E pl(&Occil.PSRN.newMirra #n #d #an #ad #())
      (mirraModel n d an ad hn hd han had) .initial (PSRNGammaMixture.owns 1 3 n d) := by
  have hcore := PSRNGammaMixture.newGammaMixture_latentDistSpec (rT := rT) (GF := GF) E
    (n * n * ad) (an * d * d + n * n * ad) (by positivity) (by positivity)
    (le_add_of_nonneg_left (by positivity))
    1 3 n d (by decide) (by decide) hn hd
  unfold mirraModel mirraBias
  refine ⟨hcore.oracle, ?_⟩
  intro F hF
  iintro Hcredit
  iapply Program.twp_mirra E n d an ad han had _
  iapply hcore.spec F hF $$ Hcredit

end specification

end

end SampLib.PSRNGammaFamilies
