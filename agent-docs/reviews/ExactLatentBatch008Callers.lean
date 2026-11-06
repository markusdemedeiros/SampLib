import SampLib.PSRN.PSRNGammaInteger
import SampLib.PSRN.PSRNGammaMixture
import SampLib.PSRN.PSRNLindley

open ProbLang
open scoped ENNReal

namespace ReviewExactLatent008

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

section gamma

variable [ProbLangDist.IsUniformInt rT]

example (E : CoPset) (shape a b : ℤ) (hs : 0 < shape) (ha : 0 < a) (hb : 0 < b)
    (F : LatentGammaInteger.World (ℕ × ℝ) (PSRNGammaInteger.depth shape) → ℝ≥0∞)
    (hF : Measurable F) (Q : IProp GF) :=
  construct_and_reread E (PSRNGammaInteger.model shape a b ha hb)
    (PSRNGammaInteger.initial shape a b) (PSRNGammaInteger.owns shape a b)
    pl(&Occil.PSRN.newGammaInteger #shape #a #b)
    (PSRNGammaInteger.newGammaInteger_latentDistSpec E shape a b hs ha hb) 8 1 F hF Q

example (E : CoPset) (Q : IProp GF) :=
  construct_and_reread E (PSRNGammaInteger.model 1 2 5 (by decide) (by decide))
    (PSRNGammaInteger.initial 1 2 5) (PSRNGammaInteger.owns 1 2 5)
    pl(&Occil.PSRN.newGammaInteger #1 #2 #5)
    (PSRNGammaInteger.newGammaInteger_latentDistSpec E 1 2 5
      (by decide) (by decide) (by decide)) 0 0 (fun _ => ∞) measurable_const Q

example (E : CoPset) (Q : IProp GF) :=
  construct_and_reread E (PSRNGammaInteger.model 3 5 2 (by decide) (by decide))
    (PSRNGammaInteger.initial 3 5 2) (PSRNGammaInteger.owns 3 5 2)
    pl(&Occil.PSRN.newGammaInteger #3 #5 #2)
    (PSRNGammaInteger.newGammaInteger_latentDistSpec E 3 5 2
      (by decide) (by decide) (by decide)) 0 8 (fun _ => ∞) measurable_const Q

example (E : CoPset) (wa wb : ℤ) (hwa : 0 ≤ wa) (hwb : 0 < wb) (hw : wa ≤ wb)
    (left right a b : ℤ) (hl : 0 < left) (hr : 0 < right) (ha : 0 < a) (hb : 0 < b)
    (F : LatentGammaInteger.World (ℕ × ℝ) (PSRNGammaInteger.depth left) ⊕
      LatentGammaInteger.World (ℕ × ℝ) (PSRNGammaInteger.depth right) → ℝ≥0∞)
    (hF : Measurable F) (Q : IProp GF) :=
  construct_and_reread E
    (PSRNGammaMixture.model (RationalCoin.bias wa wb hwa hwb hw) left right a b ha hb)
    .initial (PSRNGammaMixture.owns left right a b)
    pl(&Occil.PSRN.newGammaMixture #wa #wb #left #right #a #b #())
    (PSRNGammaMixture.newGammaMixture_latentDistSpec E wa wb hwa hwb hw
      left right a b hl hr ha hb) 6 2 F hF Q

example (E : CoPset) (Q : IProp GF) :=
  construct_and_reread E
    (PSRNGammaMixture.model (RationalCoin.bias 0 7 (by decide) (by decide) (by decide))
      1 3 2 5 (by decide) (by decide))
    .initial (PSRNGammaMixture.owns 1 3 2 5)
    pl(&Occil.PSRN.newGammaMixture #0 #7 #1 #3 #2 #5 #())
    (PSRNGammaMixture.newGammaMixture_latentDistSpec E 0 7
      (by decide) (by decide) (by decide) 1 3 2 5
      (by decide) (by decide) (by decide) (by decide))
    0 5 (fun _ => ∞) measurable_const Q

example (E : CoPset) (Q : IProp GF) :=
  construct_and_reread E
    (PSRNGammaMixture.model (RationalCoin.bias 7 7 (by decide) (by decide) (by decide))
      3 1 5 2 (by decide) (by decide))
    .initial (PSRNGammaMixture.owns 3 1 5 2)
    pl(&Occil.PSRN.newGammaMixture #7 #7 #3 #1 #5 #2 #())
    (PSRNGammaMixture.newGammaMixture_latentDistSpec E 7 7
      (by decide) (by decide) (by decide) 3 1 5 2
      (by decide) (by decide) (by decide) (by decide))
    5 0 (fun _ => ∞) measurable_const Q

example (E : CoPset) (a b : ℤ) (ha : 0 < a) (hb : 0 < b)
    (F : (ℕ × ℝ) ⊕ ((ℕ × ℝ) × (ℕ × ℝ)) → ℝ≥0∞)
    (hF : Measurable F) (Q : IProp GF) :=
  construct_and_reread E (PSRNLindley.model a b ha hb) .initial (PSRNLindley.owns a b)
    pl(&Occil.PSRN.newLindley #a #b #())
    (PSRNLindley.newLindley_latentDistSpec E a b ha hb) 9 1 F hF Q

example (E : CoPset) (Q : IProp GF) :=
  construct_and_reread E (PSRNLindley.model 2 5 (by decide) (by decide))
    .initial (PSRNLindley.owns 2 5) pl(&Occil.PSRN.newLindley #2 #5 #())
    (PSRNLindley.newLindley_latentDistSpec E 2 5 (by decide) (by decide))
    0 0 (fun _ => ∞) measurable_const Q

end gamma

#print axioms SampLib.PSRNGammaInteger.newGammaInteger_latentDistSpec
#print axioms SampLib.PSRNGammaInteger.model_law
#print axioms SampLib.PSRNGammaMixture.newGammaMixture_latentDistSpec
#print axioms SampLib.PSRNGammaMixture.model_law
#print axioms SampLib.PSRNLindley.newLindley_latentDistSpec
#print axioms SampLib.PSRNLindley.model_law_density
#print axioms SampLib.GammaSuccessor.density_successor
#print axioms construct_and_reread

end

end ReviewExactLatent008
