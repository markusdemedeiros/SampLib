import SampLib.Samplers.PSRNGammaFamilies
import SampLib.Samplers.PSRNLindleyFamilies

open ProbLang
open scoped ENNReal

namespace ReviewExactLatent010

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

private def readTwice (v : Val rT) (n m : ℕ) : Exp rT :=
  .app (.lam (.app (.lam (.pair (.bvar 1) (.bvar 0)))
    (.app v.fst (.lit (.int m))))) (.app v.fst (.lit (.int n)))

private def constructTwice (e : Exp rT) (n m : ℕ) : Exp rT :=
  .app (.lam (.app (.lam (.app (.lam (.pair (.bvar 1) (.bvar 0)))
    (.app (.bvar 1) (.lit (.int m))))) (.app (.bvar 0) (.lit (.int n))))) e

/-- Two aliases of one closure observe the same latent value and retain joint credit. -/
theorem reread (E : CoPset) (D : LatentReal.Model Ω S)
    (owns : Val rT → S → IProp GF) (h : LatentReal.IsOracleSpec E D owns)
    (v : Val rT) (s : S) (n m : ℕ) (F : Ω → ℝ≥0∞) (hF : Measurable F)
    (R : IProp GF) :
    ⊢ owns v s ∗ ↯ (∫⁻ x, F x ∂D.posterior s) ∗ R -∗
      tglWp E (readTwice v n m)
        (fun result : Val rT => iprop(∃ (t : S) (I J : LatentReal.RationalInterval),
          ⌜result = Val.pair (LatentReal.intervalVal I) (LatentReal.intervalVal J) ∧
            D.refines s t ∧ D.Encloses t n I ∧ D.Encloses t m J⌝ ∗
          owns v t ∗ ↯ (∫⁻ x, F x ∂D.posterior t) ∗ R)) := by
  iintro ⟨Hstate, Hcredit, HR⟩
  unfold readTwice
  twp_bind pl(&v.fst #int (n : ℤ))
  iapply (h.wp v s n F hF _) $$ Hstate Hcredit
  iintro %t %I %⟨hst, hI⟩ Hstate Hcredit
  twp_pure
  twp_bind pl(&v.fst #int (m : ℤ))
  iapply (h.wp v t m F hF _) $$ Hstate Hcredit
  iintro %u %J %⟨htu, hJ⟩ Hstate Hcredit
  twp_pures
  twp_value
  imodintro
  iexists u, I, J
  iframe Hstate Hcredit HR
  ipureintro
  exact ⟨rfl, D.refines_trans hst htu, D.encloses_refines htu hI, hJ⟩

/-- Initialization composes with arbitrary two-read continuations and caller resources. -/
theorem construct_and_reread (E : CoPset) (D : LatentReal.Model Ω S)
    (initial : S) (owns : Val rT → S → IProp GF) (e : Exp rT)
    (h : LatentReal.IsLatentDistSpec E e D initial owns) (n m : ℕ)
    (F : Ω → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂D.posterior initial) ∗ R -∗
      tglWp E (constructTwice e n m)
        (fun result : Val rT => iprop(∃ (v : Val rT) (t : S)
          (I J : LatentReal.RationalInterval),
          ⌜result = Val.pair (LatentReal.intervalVal I) (LatentReal.intervalVal J) ∧
            D.refines initial t ∧ D.Encloses t n I ∧ D.Encloses t m J⌝ ∗
          owns v t ∗ ↯ (∫⁻ x, F x ∂D.posterior t) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  unfold constructTwice
  twp_bind e
  iapply (h.wp F hF _) $$ Hcredit
  iintro %v %s %hinitial Hstate Hcredit
  twp_pure
  iapply tglWp_wand
  isplitl [Hstate Hcredit HR]
  · have hreads := reread E D owns h.oracle v s n m F hF R
    unfold readTwice at hreads
    iapply hreads
    iframe Hstate Hcredit HR
  iintro %result ⟨%t, %I, %J, %hresult, Hstate, Hcredit, HR⟩
  iexists v, t, I, J
  iframe Hstate Hcredit HR
  ipureintro
  exact ⟨hresult.1, D.refines_trans hinitial hresult.2.1, hresult.2.2⟩

section clients

variable [ProbLangDist.IsUniformInt rT]

open PSRNGammaFamilies in
example (E : CoPset) (n d : ℤ) (hn : 0 < n) (hd : 0 < d) (Q : IProp GF) :=
  fun (F : _ → ℝ≥0∞) (hF : Measurable F) =>
  construct_and_reread E _ _ _ _ (newGarima_latentDistSpec (rT := rT) (GF := GF) E n d hn hd)
    7 2 F hF Q

open PSRNGammaFamilies in
-- Smallest rate 1/1, infinite credit, precision zero twice.
example (E : CoPset) (Q : IProp GF) :=
  construct_and_reread E _ _ _ _ (newGarima_latentDistSpec (rT := rT) (GF := GF) E 1 1
    (by decide) (by decide)) 0 0 (fun _ => ∞) measurable_const Q

open PSRNGammaFamilies in
example (E : CoPset) (n d : ℤ) (hn : 0 < n) (hd : 0 < d) (Q : IProp GF) :=
  fun (F : _ → ℝ≥0∞) (hF : Measurable F) =>
  construct_and_reread E _ _ _ _ (newIGarima_latentDistSpec (rT := rT) (GF := GF) E n d hn hd)
    0 9 F hF Q

open PSRNGammaFamilies in
-- Unreduced rate 6/4.
example (E : CoPset) (Q : IProp GF) :=
  construct_and_reread E _ _ _ _ (newIGarima_latentDistSpec (rT := rT) (GF := GF) E 6 4
    (by decide) (by decide)) 5 1 (fun _ => ∞) measurable_const Q

open PSRNGammaFamilies in
example (E : CoPset) (n d : ℤ) (hn : 0 < n) (hd : 0 < d) (Q : IProp GF) :=
  fun (F : _ → ℝ≥0∞) (hF : Measurable F) =>
  construct_and_reread E _ _ _ _ (newXgamma_latentDistSpec (rT := rT) (GF := GF) E n d hn hd)
    3 8 F hF Q

open PSRNGammaFamilies in
-- Rate below one.
example (E : CoPset) (Q : IProp GF) :=
  construct_and_reread E _ _ _ _ (newXgamma_latentDistSpec (rT := rT) (GF := GF) E 1 9
    (by decide) (by decide)) 4 4 (fun _ => ∞) measurable_const Q

open PSRNGammaFamilies in
example (E : CoPset) (n d : ℤ) (hn : 0 < n) (hd : 0 < d) (Q : IProp GF) :=
  fun (F : _ → ℝ≥0∞) (hF : Measurable F) =>
  construct_and_reread E _ _ _ _
    (newWeightedExponentialGamma_latentDistSpec (rT := rT) (GF := GF) E n d hn hd) 6 0 F hF Q

open PSRNGammaFamilies in
-- Large rate 9/1.
example (E : CoPset) (Q : IProp GF) :=
  construct_and_reread E _ _ _ _
    (newWeightedExponentialGamma_latentDistSpec (rT := rT) (GF := GF) E 9 1
      (by decide) (by decide)) 1 6 (fun _ => ∞) measurable_const Q

open PSRNGammaFamilies in
example (E : CoPset) (n d an ad : ℤ) (hn : 0 < n) (hd : 0 < d) (han : 0 < an)
    (had : 0 < ad) (Q : IProp GF) :=
  fun (F : _ → ℝ≥0∞) (hF : Measurable F) =>
  construct_and_reread E _ _ _ _
    (newMirra_latentDistSpec (rT := rT) (GF := GF) E n d an ad hn hd han had) 2 5 F hF Q

open PSRNGammaFamilies in
-- Tiny alpha 1/1000 and alpha large 1000/1 at an unreduced rate.
example (E : CoPset) (Q : IProp GF) :=
  construct_and_reread E _ _ _ _
    (newMirra_latentDistSpec (rT := rT) (GF := GF) E 1 3 1 1000
      (by decide) (by decide) (by decide) (by decide)) 0 7 (fun _ => ∞) measurable_const Q

open PSRNGammaFamilies in
example (E : CoPset) (Q : IProp GF) :=
  construct_and_reread E _ _ _ _
    (newMirra_latentDistSpec (rT := rT) (GF := GF) E 4 2 1000 1
      (by decide) (by decide) (by decide) (by decide)) 7 0 (fun _ => ∞) measurable_const Q

open PSRNLindleyFamilies in
example (E : CoPset) (n d a b : ℤ) (hn : 0 < n) (hd : 0 < d) (ha : 0 < a) (hb : 0 < b)
    (Q : IProp GF) :=
  fun (F : _ → ℝ≥0∞) (hF : Measurable F) =>
  construct_and_reread E _ _ _ _
    (newSushila_latentDistSpec (rT := rT) (GF := GF) E n d a b hn hd ha hb) 8 3 F hF Q

open PSRNLindleyFamilies in
-- Shrinking unreduced scale 2/6 and expanding scale 7/1.
example (E : CoPset) (Q : IProp GF) :=
  construct_and_reread E _ _ _ _
    (newSushila_latentDistSpec (rT := rT) (GF := GF) E 3 7 2 6
      (by decide) (by decide) (by decide) (by decide)) 0 6 (fun _ => ∞) measurable_const Q

open PSRNLindleyFamilies in
example (E : CoPset) (Q : IProp GF) :=
  construct_and_reread E _ _ _ _
    (newSushila_latentDistSpec (rT := rT) (GF := GF) E 1 1 7 1
      (by decide) (by decide) (by decide) (by decide)) 6 6 (fun _ => ∞) measurable_const Q

open PSRNLindleyFamilies in
-- Arbitrary credit on the whole exponential-or-Lindley world.
example (E : CoPset) (n d : ℤ) (hn : 0 < n) (hd : 0 < d) (Q : IProp GF) :=
  fun (F : _ → ℝ≥0∞) (hF : Measurable F) =>
  construct_and_reread E _ _ _ _
    (newXLindley_latentDistSpec (rT := rT) (GF := GF) E n d hn hd) 9 1 F hF Q

open PSRNLindleyFamilies in
example (E : CoPset) (Q : IProp GF) :=
  construct_and_reread E _ _ _ _
    (newXLindley_latentDistSpec (rT := rT) (GF := GF) E 2 5
      (by decide) (by decide)) 0 0 (fun _ => ∞) measurable_const Q

end clients

section sushilaDensity

open MeasureTheory
open ENNReal (ofReal)

/-- Shanker et al. (2013): `θ²/(α(θ+1)) (1 + x/α) e^{-θx/α}` on `x ≥ 0`. -/
def sushilaPDF (θ α x : ℝ) : ℝ :=
  if 0 ≤ x then θ ^ 2 / (α * (θ + 1)) * (1 + x / α) * Real.exp (-(θ * x / α)) else 0

theorem map_mul_withDensity {c : ℝ} (hc : 0 < c) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (volume.withDensity f).map (fun x => x * c) =
      volume.withDensity (fun y => ofReal c⁻¹ * f (y / c)) := by
  have hφ : Measurable (fun x : ℝ => x * c) := by fun_prop
  have hg : Measurable (fun y : ℝ => ofReal c⁻¹ * f (y / c)) := by fun_prop
  ext s hs
  rw [Measure.map_apply hφ hs, withDensity_apply _ (hφ hs), withDensity_apply _ hs]
  have h1 : ∫⁻ y in s, ofReal c⁻¹ * f (y / c) ∂(volume.map (fun x => x * c)) =
      ∫⁻ x in (fun x => x * c) ⁻¹' s, ofReal c⁻¹ * f x := by
    rw [setLIntegral_map hs hg hφ]
    refine setLIntegral_congr_fun (hφ hs) fun x _ => ?_
    simp [mul_div_cancel_right₀ _ hc.ne']
  rw [Real.map_volume_mul_right hc.ne', Measure.restrict_smul, lintegral_smul_measure,
    abs_of_pos (inv_pos.mpr hc), lintegral_const_mul _ hf] at h1
  have hc' : ofReal c⁻¹ ≠ 0 := by simp [hc]
  exact ((ENNReal.mul_right_inj hc' ENNReal.ofReal_ne_top).mp h1).symm

/-- Reviewer check: the prover's pushforward law is Sushila's published density. -/
theorem sushila_model_law_density (n d a b : ℤ) (hn : 0 < n) (hd : 0 < d)
    (ha : 0 < a) (hb : 0 < b) :
    (PSRNLindleyFamilies.sushilaModel n d a b hn hd).law .initial =
      volume.withDensity (fun x => ofReal
        (sushilaPDF (PSRNLindleyFamilies.rate n d) ((a : ℝ) / b) x)) := by
  have hα : (0 : ℝ) < (a : ℝ) / b := div_pos (by exact_mod_cast ha) (by exact_mod_cast hb)
  have hθ := PSRNLindleyFamilies.rate_pos n d hn hd
  have hm : Measurable (fun x =>
      ofReal (PSRNGammaMixtures.lindleyPDFReal (PSRNLindleyFamilies.rate n d) x)) := by
    unfold PSRNGammaMixtures.lindleyPDFReal
    exact ENNReal.measurable_ofReal.comp
      (Measurable.ite measurableSet_Ici (by fun_prop) measurable_const)
  rw [PSRNLindleyFamilies.sushila_model_law, map_mul_withDensity hα hm]
  congr 1
  funext x
  set θ := PSRNLindleyFamilies.rate n d
  set α := (a : ℝ) / b
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hα.le)]
  congr 1
  by_cases hx : 0 ≤ x
  · simp only [PSRNGammaMixtures.lindleyPDFReal, sushilaPDF, div_nonneg hx hα.le, hx,
      ite_true]
    field_simp
  · have hx' : ¬ 0 ≤ x / α := not_le.mpr (div_neg_of_neg_of_pos (not_le.mp hx) hα)
    simp [PSRNGammaMixtures.lindleyPDFReal, sushilaPDF, hx, hx']

end sushilaDensity

-- The other published densities, pinned at concrete parameters.
example : (PSRNGammaFamilies.mirraModel 1 3 1 1000 (by decide) (by decide) (by decide)
    (by decide)).law .initial = MeasureTheory.volume.withDensity (fun x => ENNReal.ofReal
      (PSRNGammaFamilyDensities.mirraPDF (PSRNGammaFamilies.rate 1 3)
        ((1 : ℤ) / (1000 : ℤ) : ℝ) x)) :=
  PSRNGammaFamilies.mirra_model_law_density 1 3 1 1000
    (by decide) (by decide) (by decide) (by decide)

example : (PSRNLindleyFamilies.xlindleyModel 2 5 (by decide) (by decide)).law .initial =
    MeasureTheory.volume.withDensity (fun x => ENNReal.ofReal
      (PSRNLindleyFamilies.xlindleyPDFReal (PSRNLindleyFamilies.rate 2 5) x)) :=
  PSRNLindleyFamilies.xlindley_model_law 2 5 (by decide) (by decide)

#print axioms SampLib.PSRNGammaFamilies.newGarima_latentDistSpec
#print axioms SampLib.PSRNGammaFamilies.newIGarima_latentDistSpec
#print axioms SampLib.PSRNGammaFamilies.newXgamma_latentDistSpec
#print axioms SampLib.PSRNGammaFamilies.newWeightedExponentialGamma_latentDistSpec
#print axioms SampLib.PSRNGammaFamilies.newMirra_latentDistSpec
#print axioms SampLib.PSRNLindleyFamilies.newSushila_latentDistSpec
#print axioms SampLib.PSRNLindleyFamilies.newXLindley_latentDistSpec
#print axioms SampLib.PSRNGammaFamilies.garima_model_law_density
#print axioms SampLib.PSRNGammaFamilies.igarima_model_law_density
#print axioms SampLib.PSRNGammaFamilies.xgamma_model_law_density
#print axioms SampLib.PSRNGammaFamilies.weightedExponentialGamma_model_law_density
#print axioms SampLib.PSRNGammaFamilies.mirra_model_law_density
#print axioms SampLib.PSRNLindleyFamilies.sushila_model_law
#print axioms SampLib.PSRNLindleyFamilies.xlindley_model_law
#print axioms sushila_model_law_density
#print axioms construct_and_reread

end

end ReviewExactLatent010
