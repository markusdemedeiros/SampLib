import SampLib.LatentConstantDigits

open ProbLang
open scoped ENNReal

namespace ReviewExactLatent004

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

section digits

open MeasureTheory (Measure IsProbabilityMeasure)
open SampLib.LatentDigits

variable [ProbLangDist.IsUniformInt rT]

example (E : CoPset) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (digits : Ω → ℕ → Bool) (hd : ∀ n, Measurable (fun x => digits x n))
    (nextBit : Val rT) (hnext : IsNextDigitSpec (GF := GF) E μ digits hd nextBit)
    (F : Ω → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :=
  construct_and_reread E (model μ digits hd) (initial μ digits) (owns μ digits nextBit)
    pl(&Occil.PSRN.newByDigits &nextBit.fst #())
    (newByDigits_latentDistSpec E μ digits hd nextBit hnext) 8 3 F hF R

example (E : CoPset) (μ : Measure Ω) [IsProbabilityMeasure μ] (b : Bool)
    (F : Ω → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :=
  construct_and_reread E (model μ (fun _ _ => b) (fun _ => measurable_const))
    (initial μ (fun _ _ => b)) (owns μ (fun _ _ => b) (constantCallback b))
    pl(&Occil.PSRN.newByDigits &(constantCallback b).fst #())
    (newByDigits_latentDistSpec E μ _ _ _ (constant_digitSpec E μ b)) 8 3 F hF R

example (E : CoPset) (μ : Measure Ω) [IsProbabilityMeasure μ] (b : Bool)
    (R : IProp GF) :=
  construct_and_reread E (model μ (fun _ _ => b) (fun _ => measurable_const))
    (initial μ (fun _ _ => b)) (owns μ (fun _ _ => b) (constantCallback b))
    pl(&Occil.PSRN.newByDigits &(constantCallback b).fst #())
    (newByDigits_latentDistSpec E μ _ _ _ (constant_digitSpec E μ b))
    0 0 (fun _ => ∞) measurable_const R

/-- Shorter observations preserve the entire physical cache, not just its law. -/
theorem cache_reread (E : CoPset) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (digits : Ω → ℕ → Bool) (hd : ∀ n, Measurable (fun x => digits x n))
    (nextBit : Val rT) (hnext : IsNextDigitSpec (GF := GF) E μ digits hd nextBit)
    (v : Val rT) (p : State μ digits) (F : Ω → ℝ≥0∞) (R : IProp GF) :
    ⊢ owns μ digits nextBit v p ∗
      ↯ (∫⁻ x, F x ∂DigitPosterior.law μ digits p.val) ∗ R -∗
      tglWp E (readTwice v 8 3) (fun result : Val rT => iprop(∃ q r : State μ digits,
        ⌜UniformBag.readRefines p.val 8 q.val ∧ r.val = q.val ∧
          result = Val.pair (LatentReal.intervalVal (LatentUniform.interval q.val 8))
            (LatentReal.intervalVal (LatentUniform.interval r.val 3))⌝ ∗
        owns μ digits nextBit v r ∗
        ↯ (∫⁻ x, F x ∂DigitPosterior.law μ digits r.val) ∗ R)) := by
  iintro ⟨Hstate, Hcredit, HR⟩
  unfold readTwice
  twp_bind pl(&v.fst #int (8 : ℤ))
  iapply tglWp_wand
  isplitl [Hstate Hcredit]
  · iapply twp_observe E μ digits hd nextBit hnext v p 8 F
    iframe Hstate Hcredit
  iintro %result ⟨%q, %⟨hq, hvalue⟩, Hstate, Hcredit⟩
  subst_vars
  twp_pure
  twp_bind pl(&v.fst #int (3 : ℤ))
  iapply tglWp_wand
  isplitl [Hstate Hcredit]
  · iapply twp_observe E μ digits hd nextBit hnext v q 3 F
    iframe Hstate Hcredit
  iintro %result ⟨%r, %⟨hr, hvalue⟩, Hstate, Hcredit⟩
  subst_vars
  twp_pures
  twp_value
  imodintro
  iexists q, r
  iframe Hstate Hcredit HR
  ipureintro
  have hlen : 8 ≤ q.val.length := by rw [hq.2]; exact Nat.le_max_right _ _
  have heq : r.val = q.val := by
    rcases hr.1 with ⟨tail, htail⟩
    have hlength := hr.2
    rw [Nat.max_eq_left (by omega)] at hlength
    have ht : tail.length = 0 := by
      rw [← htail, List.length_append] at hlength
      omega
    have : tail = [] := by cases tail <;> simp_all
    simpa [this] using htail.symm
  exact ⟨hq, heq, rfl⟩

end digits

#print axioms SampLib.LatentDigits.newByDigits_latentDistSpec
#print axioms SampLib.LatentDigits.twp_read
#print axioms SampLib.LatentDigits.twp_observe
#print axioms SampLib.LatentDigits.constant_digitSpec
#print axioms SampLib.LatentDigits.constant_initial_law
#print axioms construct_and_reread
#print axioms cache_reread

end

end ReviewExactLatent004
