import SampLib.PSRNExponential
import SampLib.PSRNExponentialCallbacks

open ProbLang
open scoped ENNReal

namespace ReviewExactLatent006

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
    (A : LatentReal.Representation D)
    (owns : Val rT → S → IProp GF) (h : LatentReal.IsRepresentedOracleSpec E D A owns)
    (v : Val rT) (s : S) (n m : ℕ) (F : Ω → ℝ≥0∞) (hF : Measurable F)
    (R : IProp GF) :
    ⊢ owns v s ∗ ↯ (∫⁻ x, F x ∂D.posterior s) ∗ R -∗
      tglWp E (readTwice v n m)
        (fun result : Val rT => iprop(∃ (t : S) (I J : LatentReal.RationalInterval),
          ⌜result = Val.pair (LatentReal.intervalVal I) (LatentReal.intervalVal J) ∧
            D.refines s t ∧ D.Encloses t n I ∧ D.Encloses t m J ∧
            A.Observed t n I ∧ A.Observed t m J⌝ ∗
          owns v t ∗ ↯ (∫⁻ x, F x ∂D.posterior t) ∗ R)) := by
  iintro ⟨Hstate, Hcredit, HR⟩
  unfold readTwice
  twp_bind pl(&v.fst #int (n : ℤ))
  iapply (h.wp v s n F hF _) $$ Hstate Hcredit
  iintro %t %I %⟨hst, hI, hRI⟩ Hstate Hcredit
  twp_pure
  twp_bind pl(&v.fst #int (m : ℤ))
  iapply (h.wp v t m F hF _) $$ Hstate Hcredit
  iintro %u %J %⟨htu, hJ, hRJ⟩ Hstate Hcredit
  twp_pures
  twp_value
  imodintro
  iexists u, I, J
  iframe Hstate Hcredit HR
  ipureintro
  exact ⟨rfl, D.refines_trans hst htu, D.encloses_refines htu hI, hJ,
    A.observed_refines htu hRI, hRJ⟩

/-- Initialization composes with arbitrary two-read continuations and caller resources. -/
theorem construct_and_reread (E : CoPset) (D : LatentReal.Model Ω S)
    (A : LatentReal.Representation D) (initial : S)
    (owns : Val rT → S → IProp GF) (e : Exp rT)
    (h : LatentReal.IsRepresentedDistSpec E e D A initial owns) (n m : ℕ)
    (F : Ω → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂D.posterior initial) ∗ R -∗
      tglWp E (constructTwice e n m)
        (fun result : Val rT => iprop(∃ (v : Val rT) (t : S)
          (I J : LatentReal.RationalInterval),
          ⌜result = Val.pair (LatentReal.intervalVal I) (LatentReal.intervalVal J) ∧
            D.refines initial t ∧ D.Encloses t n I ∧ D.Encloses t m J ∧
            A.Observed t n I ∧ A.Observed t m J⌝ ∗
          owns v t ∗ ↯ (∫⁻ x, F x ∂D.posterior t) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  unfold constructTwice
  twp_bind e
  iapply (h.forget.wp F hF _) $$ Hcredit
  iintro %v %s %hinitial Hstate Hcredit
  twp_pure
  iapply tglWp_wand
  isplitl [Hstate Hcredit HR]
  · have hreads := reread E D A owns h.oracle v s n m F hF R
    unfold readTwice at hreads
    iapply hreads
    iframe Hstate Hcredit HR
  iintro %result ⟨%t, %I, %J, %hresult, Hstate, Hcredit, HR⟩
  iexists v, t, I, J
  iframe Hstate Hcredit HR
  ipureintro
  exact ⟨hresult.1, D.refines_trans hinitial hresult.2.1, hresult.2.2⟩

section exponential

variable [ProbLangDist.IsUniformInt rT]

example (E : CoPset) (rate : ℝ) (hrate : 0 < rate) (decay : Val rT)
    (hdecay : PSRNExponential.IsDecaySpec (GF := GF) E rate hrate decay)
    (F : ℕ × ℝ → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :=
  construct_and_reread E (LatentExponential.model rate hrate)
    (LatentExponential.representation rate hrate) (LatentExponential.initial rate)
    (PSRNExponential.owns rate decay) pl(&Occil.PSRN.newExponentialFromDecay &decay.fst #())
    (PSRNExponential.newExponentialFromDecay_representedDistSpec E rate hrate decay hdecay)
    7 2 F hF R

example (E : CoPset) (R : IProp GF) :=
  construct_and_reread E
    (LatentExponential.model (2 / 3) (by norm_num))
    (LatentExponential.representation (2 / 3) (by norm_num))
    (LatentExponential.initial (2 / 3))
    (PSRNExponential.owns (2 / 3) (PSRNRationalRateDecay.value 2 3))
    pl(&Occil.PSRN.newExponentialFromDecay &(PSRNRationalRateDecay.value 2 3).fst #())
    (PSRNExponential.newExponentialFromDecay_representedDistSpec E _ _ _
      (PSRNExponential.rational_isDecaySpec E 2 3 (by decide) (by decide)))
    0 0 (fun _ => ∞) measurable_const R

/-- Even a continuation detecting a sampled whole coordinate retains its joint law. -/
example (E : CoPset) (R : IProp GF) :=
  construct_and_reread E
    (LatentExponential.model (3 / 2) (by norm_num))
    (LatentExponential.representation (3 / 2) (by norm_num))
    (LatentExponential.initial (3 / 2))
    (PSRNExponential.owns (3 / 2) (PSRNRationalRateDecay.value 3 2))
    pl(&Occil.PSRN.newExponentialFromDecay &(PSRNRationalRateDecay.value 3 2).fst #())
    (PSRNExponential.newExponentialFromDecay_representedDistSpec E _ _ _
      (PSRNExponential.rational_isDecaySpec E 3 2 (by decide) (by decide)))
    0 9 (fun z => if z.1 = 0 then ∞ else ENNReal.ofReal z.2)
    (Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
      measurable_const (ENNReal.measurable_ofReal.comp measurable_snd)) R

end exponential

#print axioms SampLib.PSRNExponential.newExponentialFromDecay_latentDistSpec
#print axioms SampLib.PSRNExponential.newExponentialFromDecay_representedDistSpec
#print axioms SampLib.PSRNExponential.representedOracleSpec
#print axioms SampLib.LatentExponential.initial_law
#print axioms SampLib.LatentExponential.representation
#print axioms SampLib.PSRNExponential.rational_isDecaySpec
#print axioms construct_and_reread

end

end ReviewExactLatent006
