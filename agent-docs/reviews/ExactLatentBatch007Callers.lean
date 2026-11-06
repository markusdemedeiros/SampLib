import SampLib.PSRN.Support.LatentRepresentedExponentialWrappers

open ProbLang
open scoped ENNReal

namespace ReviewExactLatent007

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

section integer

variable [ProbLangDist.IsUniformInt rT]
open PSRNExponential

example (E : CoPset) (a b : ℤ) (ha : 0 < a) (hb : 0 < b)
    (F : ℕ × ℝ → ℝ≥0∞) (hF : Measurable F) (Q : IProp GF) :=
  construct_and_reread E
    (LatentExponential.model ((a : ℝ) / b) (PSRNRationalRateDecay.rate_pos a b ha hb))
    (LatentExponential.representation ((a : ℝ) / b) (PSRNRationalRateDecay.rate_pos a b ha hb))
    (LatentExponential.initial ((a : ℝ) / b)) (rationalOwns a b)
    pl(&Occil.PSRN.newExponential #a #b #())
    (newExponential_representedDistSpec E a b ha hb) 6 1 F hF Q

example (E : CoPset) (x y : ℤ) (hy : 0 < y) (hxy : y < x)
    (F : ℕ × ℝ → ℝ≥0∞) (hF : Measurable F) (Q : IProp GF) :=
  construct_and_reread E
    (LatentExponential.model (PSRNLogRateDecay.rate x y) (PSRNLogRateDecay.rate_pos hy hxy))
    (LatentExponential.representation (PSRNLogRateDecay.rate x y)
      (PSRNLogRateDecay.rate_pos hy hxy))
    (LatentExponential.initial (PSRNLogRateDecay.rate x y)) (logRateOwns x y)
    pl(&Occil.PSRN.newExponentialLogRate #x #y #())
    (newExponentialLogRate_representedDistSpec E x y hy hxy) 0 7 F hF Q

example (E : CoPset) (Q : IProp GF) :=
  construct_and_reread E
    (LatentExponential.model (3 / 5) (by norm_num))
    (LatentExponential.representation (3 / 5) (by norm_num))
    (LatentExponential.initial (3 / 5)) (rationalOwns 3 5)
    pl(&Occil.PSRN.newExponential #3 #5 #())
    (newExponential_representedDistSpec E 3 5 (by decide) (by decide))
    0 0 (fun _ => ∞) measurable_const Q

example (E : CoPset) (Q : IProp GF) :=
  construct_and_reread E
    (LatentExponential.model (PSRNLogRateDecay.rate 3 2)
      (PSRNLogRateDecay.rate_pos (by decide) (by decide)))
    (LatentExponential.representation (PSRNLogRateDecay.rate 3 2)
      (PSRNLogRateDecay.rate_pos (by decide) (by decide)))
    (LatentExponential.initial (PSRNLogRateDecay.rate 3 2)) (logRateOwns 3 2)
    pl(&Occil.PSRN.newExponentialLogRate #3 #2 #())
    (newExponentialLogRate_representedDistSpec E 3 2 (by decide) (by decide))
    7 0 (fun _ => ∞) measurable_const Q

end integer

section unknown

variable [ProbLangDist ℝ] [ProbLangDist.IsUniformInt ℝ] [ProbLangDist.IsUniformReal ℝ]
  [ProbLangFFI ℝ] [ProbLangObs ℝ] [ErisGS ℝ hlc GF]

example (E : CoPset) (p : unitInterval) (hp : 0 < (p : ℝ)) (coin : Val ℝ)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : ℕ × ℝ → ℝ≥0∞) (hF : Measurable F) (Q : IProp GF) :=
  construct_and_reread E (LatentExponential.model (p : ℝ) hp)
    (LatentExponential.representation (p : ℝ) hp) (LatentExponential.initial (p : ℝ))
    (PSRNExponential.unknownRateOwns p coin)
    pl(&Occil.PSRN.newExponentialUnknownRate &coin.fst #())
    (PSRNExponential.newExponentialUnknownRate_representedDistSpec E p hp coin hcoin)
    5 2 F hF Q

private def trueCoin : Val ℝ := ⟨.lam (.lit (.bool true)), .lam (by is_lc), by is_lc⟩

omit [ProbLangDist.IsUniformInt ℝ] [ProbLangDist.IsUniformReal ℝ] in
private theorem trueCoin_spec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&trueCoin.fst #()) (RealCoin.law 1) Val.bool where
  spec F _ := by
    rw [RealCoin.lintegral_law]
    simp [RealCoin.credit, RealCoin.pmf]
    iintro Hcredit
    twp_pure
    twp_value
    imodintro
    iexists true
    iframe Hcredit
    itrivial

example (E : CoPset) (Q : IProp GF) :=
  construct_and_reread E (LatentExponential.model 1 (by norm_num))
    (LatentExponential.representation 1 (by norm_num)) (LatentExponential.initial 1)
    (PSRNExponential.unknownRateOwns 1 trueCoin)
    pl(&Occil.PSRN.newExponentialUnknownRate &trueCoin.fst #())
    (PSRNExponential.newExponentialUnknownRate_representedDistSpec E 1
      (by norm_num) trueCoin (trueCoin_spec E)) 0 8 (fun _ => ∞) measurable_const Q

end unknown

#print axioms SampLib.PSRNExponential.newExponential_latentDistSpec
#print axioms SampLib.PSRNExponential.newExponentialLogRate_latentDistSpec
#print axioms SampLib.PSRNExponential.newExponentialUnknownRate_latentDistSpec
#print axioms SampLib.PSRNExponential.newExponential_representedDistSpec
#print axioms SampLib.PSRNExponential.newExponentialLogRate_representedDistSpec
#print axioms SampLib.PSRNExponential.newExponentialUnknownRate_representedDistSpec
#print axioms construct_and_reread

end

end ReviewExactLatent007
