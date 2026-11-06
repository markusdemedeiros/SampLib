import SampLib.LatentRepresentedExponentialWrappers

open ProbLang
open scoped ENNReal

namespace ConcreteExponentialProducer

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
    (A : LatentReal.Representation D) (initial : S) (owns : Val rT → S → IProp GF)
    (e : Exp rT) (h : LatentReal.IsRepresentedDistSpec E e D A initial owns) (n m : ℕ)
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

example (E : CoPset) (a b : ℤ) (ha : 0 < a) (hb : 0 < b)
    (F : ℕ × ℝ → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :=
  construct_and_reread (rT := rT) (GF := GF) E
    (LatentExponential.model ((a : ℝ) / b) (PSRNRationalRateDecay.rate_pos a b ha hb))
    (LatentExponential.representation ((a : ℝ) / b) (PSRNRationalRateDecay.rate_pos a b ha hb))
    (LatentExponential.initial ((a : ℝ) / b)) (PSRNExponential.rationalOwns a b)
    pl(&Occil.PSRN.newExponential #a #b #())
    (PSRNExponential.newExponential_representedDistSpec E a b ha hb) 8 3 F hF R

example (E : CoPset) (x y : ℤ) (hy : 0 < y) (hxy : y < x)
    (F : ℕ × ℝ → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :=
  construct_and_reread (rT := rT) (GF := GF) E
    (LatentExponential.model (PSRNLogRateDecay.rate x y) (PSRNLogRateDecay.rate_pos hy hxy))
    (LatentExponential.representation (PSRNLogRateDecay.rate x y)
      (PSRNLogRateDecay.rate_pos hy hxy))
    (LatentExponential.initial (PSRNLogRateDecay.rate x y)) (PSRNExponential.logRateOwns x y)
    pl(&Occil.PSRN.newExponentialLogRate #x #y #())
    (PSRNExponential.newExponentialLogRate_representedDistSpec E x y hy hxy) 8 3 F hF R

example (E : CoPset) (R : IProp GF) :=
  construct_and_reread (rT := rT) (GF := GF) E
    (LatentExponential.model (((2 : ℤ) : ℝ) / 3)
      (PSRNRationalRateDecay.rate_pos 2 3 (by decide) (by decide)))
    (LatentExponential.representation (((2 : ℤ) : ℝ) / 3)
      (PSRNRationalRateDecay.rate_pos 2 3 (by decide) (by decide)))
    (LatentExponential.initial (((2 : ℤ) : ℝ) / 3)) (PSRNExponential.rationalOwns 2 3)
    pl(&Occil.PSRN.newExponential #2 #3 #())
    (PSRNExponential.newExponential_representedDistSpec E 2 3 (by decide) (by decide))
    0 0 (fun _ => ∞) measurable_const R

end integer

section unknown

variable [ProbLangDist ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
  [ProbLangDist.IsUniformInt ℝ] [ProbLangDist.IsUniformReal ℝ]
variable {hlcReal : HasLC} [ErisGS ℝ hlcReal GF]

example (E : CoPset) (p : unitInterval) (hp : 0 < (p : ℝ)) (coin : Val ℝ)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : ℕ × ℝ → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :=
  construct_and_reread (rT := ℝ) (GF := GF) E
    (LatentExponential.model (p : ℝ) hp) (LatentExponential.representation (p : ℝ) hp)
    (LatentExponential.initial (p : ℝ)) (PSRNExponential.unknownRateOwns p coin)
    pl(&Occil.PSRN.newExponentialUnknownRate &coin.fst #())
    (PSRNExponential.newExponentialUnknownRate_representedDistSpec E p hp coin hcoin) 8 3 F hF R

private def trueCallback : Val ℝ :=
  ⟨.lam (.lit (.bool true)), .lam (by is_lc), by is_lc⟩

omit [ProbLangDist.IsUniformInt ℝ] [ProbLangDist.IsUniformReal ℝ] in
private theorem true_callback_spec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&trueCallback.fst #()) (RealCoin.law 1) Val.bool where
  spec F _ := by
    iintro Hcredit
    twp_pure
    twp_value
    imodintro
    iexists true
    isimp [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf] at Hcredit
    iframe Hcredit
    itrivial

example (E : CoPset) (R : IProp GF) :=
  construct_and_reread (rT := ℝ) (GF := GF) E
    (LatentExponential.model (1 : ℝ) zero_lt_one)
    (LatentExponential.representation (1 : ℝ) zero_lt_one)
    (LatentExponential.initial (1 : ℝ)) (PSRNExponential.unknownRateOwns 1 trueCallback)
    pl(&Occil.PSRN.newExponentialUnknownRate &trueCallback.fst #())
    (PSRNExponential.newExponentialUnknownRate_representedDistSpec E 1 zero_lt_one
      trueCallback (true_callback_spec E)) 8 3 (fun _ => ∞) measurable_const R

end unknown

example (rate : ℝ) (hrate : 0 < rate) :
    (LatentExponential.model rate hrate).law (LatentExponential.initial rate) =
      ProbabilityTheory.expMeasure rate := LatentExponential.initial_law rate hrate

#print axioms SampLib.PSRNExponential.newExponential_representedDistSpec
#print axioms SampLib.PSRNExponential.newExponentialLogRate_representedDistSpec
#print axioms SampLib.PSRNExponential.newExponentialUnknownRate_representedDistSpec
#print axioms SampLib.LatentExponential.initial_law
#print axioms construct_and_reread

end

end ConcreteExponentialProducer
