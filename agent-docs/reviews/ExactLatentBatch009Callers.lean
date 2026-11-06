import SampLib.PSRN.PSRNRayleigh

open ProbLang
open scoped ENNReal

namespace ReviewExactLatent009

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

section rayleigh

variable [ProbLangDist.IsUniformInt rT]
open PSRNRayleigh

example (E : CoPset) (F : ℕ × ℝ → ℝ≥0∞) (hF : Measurable F) (Q : IProp GF) :=
  construct_and_reread E model model.dyadicRepresentation initial owns
    pl(&Occil.PSRN.newRayleigh #()) (newRayleigh_representedDistSpec E) 0 7 F hF Q

example (E : CoPset) (Q : IProp GF) :=
  construct_and_reread E model model.dyadicRepresentation initial owns
    pl(&Occil.PSRN.newRayleigh #()) (newRayleigh_representedDistSpec E)
    8 1 (fun _ => ∞) measurable_const Q

/-- Whole and fractional coordinates remain available after both square-root observations. -/
example (E : CoPset) (Q : IProp GF) :=
  construct_and_reread E model model.dyadicRepresentation initial owns
    pl(&Occil.PSRN.newRayleigh #()) (newRayleigh_representedDistSpec E)
    5 2 (fun z => if z.1 = 0 then ENNReal.ofReal z.2 else ∞)
    (Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
      (ENNReal.measurable_ofReal.comp measurable_snd) measurable_const) Q

end rayleigh

omit [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT] in
example : ProbabilityTheory.cdf PSRNRayleigh.law 0 = 0 := by
  rw [PSRNRayleigh.cdf_eq]
  norm_num

omit [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT] in
example : ProbabilityTheory.cdf PSRNRayleigh.law (-1) = 0 := by
  rw [PSRNRayleigh.cdf_eq]
  norm_num

#print axioms SampLib.PSRNRayleigh.newRayleigh_latentDistSpec
#print axioms SampLib.PSRNRayleigh.newRayleigh_representedDistSpec
#print axioms SampLib.PSRNRayleigh.model_law
#print axioms SampLib.PSRNRayleigh.cdf_eq
#print axioms construct_and_reread

end

end ReviewExactLatent009
