import SampLib.Samplers.PSRNOddsUniform
import SampLib.Samplers.PSRNRatioUniforms
import SampLib.Samplers.PSRNPowerUniform
import SampLib.Samplers.PSRNReciprocalPowerUniform

open ProbLang
open scoped ENNReal

namespace ReviewExactLatent011

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

open PSRNOddsUniform in
example (E : CoPset) (Q : IProp GF) :=
  fun (F : ℝ → ℝ≥0∞) (hF : Measurable F) =>
  construct_and_reread E _ _ _ _ (newOddsUniform_latentDistSpec (rT := rT) (GF := GF) E)
    9 2 F hF Q

open PSRNOddsUniform in
-- Infinite credit, precision zero twice.
example (E : CoPset) (Q : IProp GF) :=
  construct_and_reread E _ _ _ _ (newOddsUniform_latentDistSpec (rT := rT) (GF := GF) E)
    0 0 (fun _ => ∞) measurable_const Q

open PSRNRatioUniforms in
-- Arbitrary credit on the whole two-uniform product world.
example (E : CoPset) (Q : IProp GF) :=
  fun (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) =>
  construct_and_reread E _ _ _ _ (newRatioUniforms_latentDistSpec (rT := rT) (GF := GF) E)
    3 8 F hF Q

open PSRNRatioUniforms in
example (E : CoPset) (Q : IProp GF) :=
  construct_and_reread E _ _ _ _ (newRatioUniforms_latentDistSpec (rT := rT) (GF := GF) E)
    6 0 (fun _ => ∞) measurable_const Q

open PSRNPowerUniform in
example (E : CoPset) (a : ℤ) (b : ℕ) (hb : 0 < b) (Q : IProp GF) :=
  fun (F : ℝ → ℝ≥0∞) (hF : Measurable F) =>
  construct_and_reread E _ _ _ _ (newPowerUniform_latentDistSpec (rT := rT) (GF := GF) E a b hb)
    5 1 F hF Q

open PSRNPowerUniform in
-- Zero numerator: the constant branch, with a non-unit denominator.
example (E : CoPset) (Q : IProp GF) :=
  construct_and_reread E _ _ _ _
    (newPowerUniform_latentDistSpec (rT := rT) (GF := GF) E 0 7 (by decide))
    0 4 (fun _ => ∞) measurable_const Q

open PSRNPowerUniform in
-- Positive numerator, degree one: repeated squaring only.
example (E : CoPset) (Q : IProp GF) :=
  construct_and_reread E _ _ _ _
    (newPowerUniform_latentDistSpec (rT := rT) (GF := GF) E 5 1 (by decide))
    7 7 (fun _ => ∞) measurable_const Q

open PSRNPowerUniform in
-- Positive numerator, bisection root; also the pure root `a = 1`.
example (E : CoPset) (Q : IProp GF) :=
  construct_and_reread E _ _ _ _
    (newPowerUniform_latentDistSpec (rT := rT) (GF := GF) E 1 3 (by decide))
    2 6 (fun _ => ∞) measurable_const Q

open PSRNPowerUniform in
example (E : CoPset) (Q : IProp GF) :=
  construct_and_reread E _ _ _ _
    (newPowerUniform_latentDistSpec (rT := rT) (GF := GF) E 4 6 (by decide))
    1 0 (fun _ => ∞) measurable_const Q

open PSRNPowerUniform in
-- Negative numerator: reciprocal of a power, and of a root.
example (E : CoPset) (Q : IProp GF) :=
  construct_and_reread E _ _ _ _
    (newPowerUniform_latentDistSpec (rT := rT) (GF := GF) E (-1) 1 (by decide))
    4 9 (fun _ => ∞) measurable_const Q

open PSRNPowerUniform in
example (E : CoPset) (Q : IProp GF) :=
  construct_and_reread E _ _ _ _
    (newPowerUniform_latentDistSpec (rT := rT) (GF := GF) E (-3) 2 (by decide))
    8 3 (fun _ => ∞) measurable_const Q

open PSRNReciprocalPowerUniform in
example (E : CoPset) (a : ℤ) (b : ℕ) (hb : 0 < b) (Q : IProp GF) :=
  fun (F : ℝ → ℝ≥0∞) (hF : Measurable F) =>
  construct_and_reread E _ _ _ _
    (newReciprocalPowerUniform_latentDistSpec (rT := rT) (GF := GF) E a b hb) 6 2 F hF Q

open PSRNReciprocalPowerUniform in
-- Zero, positive-with-root and negative numerators.
example (E : CoPset) (Q : IProp GF) :=
  construct_and_reread E _ _ _ _
    (newReciprocalPowerUniform_latentDistSpec (rT := rT) (GF := GF) E 0 1 (by decide))
    0 0 (fun _ => ∞) measurable_const Q

open PSRNReciprocalPowerUniform in
example (E : CoPset) (Q : IProp GF) :=
  construct_and_reread E _ _ _ _
    (newReciprocalPowerUniform_latentDistSpec (rT := rT) (GF := GF) E 2 5 (by decide))
    3 7 (fun _ => ∞) measurable_const Q

open PSRNReciprocalPowerUniform in
example (E : CoPset) (Q : IProp GF) :=
  construct_and_reread E _ _ _ _
    (newReciprocalPowerUniform_latentDistSpec (rT := rT) (GF := GF) E (-2) 1 (by decide))
    9 1 (fun _ => ∞) measurable_const Q

end clients

section laws

open MeasureTheory

/-- Odds of a uniform: the shifted Pareto(1, 1) law, with its CDF `t / (1 + t)`. -/
example : PSRNOddsUniform.model.law [] =
    (ProbabilityTheory.paretoMeasure 1 1).map (fun x : ℝ => x - 1) :=
  PSRNOddsUniform.initial_law.trans UniformOdds.law_eq_shifted_pareto

example (t : ℝ) : PSRNOddsUniform.model.law [] (Set.Iic t) =
    ENNReal.ofReal (if 0 ≤ t then t / (1 + t) else 0) := by
  rw [PSRNOddsUniform.initial_law, UniformOdds.law_Iic]

/-- Occil's `U / V`: the quotient of two independent unit uniforms. -/
example : PSRNRatioUniforms.model.law PSRNRatioUniforms.initial =
    (DyadicPosterior.unitLaw.prod DyadicPosterior.unitLaw).map (fun z : ℝ × ℝ => z.1 / z.2) :=
  PSRNRatioUniforms.initial_law

/-- Occil's `U ^ (a / b)` and `U ^ (-a / b)`. -/
example (a : ℤ) (b : ℕ) (hb : 0 < b) : (PSRNPowerUniform.model a b).law [] =
    DyadicPosterior.unitLaw.map (fun u => u ^ ((a : ℝ) / b)) :=
  PSRNPowerUniform.initial_law a hb

example (a : ℤ) (b : ℕ) (hb : 0 < b) : (PSRNReciprocalPowerUniform.model a b).law [] =
    DyadicPosterior.unitLaw.map (fun u => u ^ (-(a : ℝ) / b)) :=
  PSRNReciprocalPowerUniform.initial_law a hb

/-- Reviewer check: the zero exponent is the point mass at one. -/
theorem power_zero_law (b : ℕ) (hb : 0 < b) :
    (PSRNPowerUniform.model 0 b).law [] = Measure.dirac 1 := by
  rw [PSRNPowerUniform.initial_law 0 hb]
  simp

/-- Reviewer check: the reciprocal power is the power with negated numerator. -/
theorem reciprocal_power_law (a : ℤ) (b : ℕ) (hb : 0 < b) :
    (PSRNReciprocalPowerUniform.model a b).law [] = (PSRNPowerUniform.model (-a) b).law [] := by
  rw [PSRNReciprocalPowerUniform.initial_law a hb, PSRNPowerUniform.initial_law (-a) hb]
  push_cast
  rfl

end laws

#print axioms SampLib.PSRNOddsUniform.newOddsUniform_latentDistSpec
#print axioms SampLib.PSRNRatioUniforms.newRatioUniforms_latentDistSpec
#print axioms SampLib.PSRNPowerUniform.newPowerUniform_latentDistSpec
#print axioms SampLib.PSRNReciprocalPowerUniform.newReciprocalPowerUniform_latentDistSpec
#print axioms SampLib.PSRNOddsUniform.initial_law
#print axioms SampLib.PSRNRatioUniforms.initial_law
#print axioms SampLib.PSRNPowerUniform.initial_law
#print axioms SampLib.PSRNReciprocalPowerUniform.initial_law
#print axioms power_zero_law
#print axioms reciprocal_power_law
#print axioms construct_and_reread

end

end ReviewExactLatent011
