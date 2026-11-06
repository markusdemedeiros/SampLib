import SampLib.PSRN.PSRNReciprocalUniform

open ProbLang
open scoped ENNReal

namespace ReviewExactLatent005

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

section reciprocal

variable [ProbLangDist.IsUniformInt rT]
open SampLib.PSRNReciprocalUniform

/-- Starting at zero forces adaptive separation of a genuine uniform interval. -/
example (E : CoPset) (F : ℝ → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :=
  construct_and_reread E model representation [] owns
    pl(&Occil.PSRN.newReciprocalUniform #()) (newReciprocalUniform_representedDistSpec E)
    0 5 F hF R

example (E : CoPset) (R : IProp GF) :=
  construct_and_reread E model representation [] owns
    pl(&Occil.PSRN.newReciprocalUniform #()) (newReciprocalUniform_representedDistSpec E)
    9 0 (fun _ => ∞) measurable_const R

example (E : CoPset) (v : Val rT) (p : List Bool) (R : IProp GF) :=
  reread E model representation owns (representedOracleSpec E) v p 0 0
    (fun u : ℝ => if 1 / u ≤ 1 then ∞ else 0)
    (measurable_const.ite (measurableSet_le (measurable_const.div measurable_id)
      measurable_const) measurable_const) R

end reciprocal

omit [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT] in
example : SampLib.ReciprocalUniform.law (Set.Iic 1) = 0 := by
  rw [SampLib.ReciprocalUniform.law_Iic]
  norm_num

omit [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT] in
example : SampLib.ReciprocalUniform.law (Set.Iic (-2)) = 0 := by
  rw [SampLib.ReciprocalUniform.law_Iic]
  norm_num

omit [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT] in
example : (LatentUniform.interval [] 0).lower = 0 ∧
    (LatentUniform.interval [] 0).upper = 1  := ⟨rfl, rfl⟩

omit [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT] in
example : (∫⁻ y, (Set.Iic (1 : ℝ)).indicator (fun _ => ∞) y
    ∂SampLib.ReciprocalUniform.law) = 0 := by
  rw [MeasureTheory.lintegral_indicator measurableSet_Iic,
    MeasureTheory.setLIntegral_const, SampLib.ReciprocalUniform.law_Iic]
  norm_num

#print axioms SampLib.PSRNReciprocalUniform.newReciprocalUniform_latentDistSpec
#print axioms SampLib.PSRNReciprocalUniform.newReciprocalUniform_representedDistSpec
#print axioms SampLib.PSRNReciprocalUniform.initial_law
#print axioms SampLib.LatentReal.RepresentedReciprocal.twp_observe
#print axioms SampLib.LatentReal.RepresentedReciprocal.expectation_preservation
#print axioms SampLib.LatentReal.RepresentedReciprocal.tail_mass_tendsto_zero
#print axioms SampLib.ReciprocalUniform.law_eq_pareto
#print axioms construct_and_reread

end

end ReviewExactLatent005
