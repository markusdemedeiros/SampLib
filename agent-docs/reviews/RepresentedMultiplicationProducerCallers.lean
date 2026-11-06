import SampLib.LatentRepresentedMultiplication

open ProbLang
open scoped ENNReal

namespace RepresentedMultiplicationProducer

open SampLib
open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open MeasureTheory (Measure IsProbabilityMeasure)

noncomputable section

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- Exact observations remain valid after shorter reads through the same physical handle. -/
theorem reread (E : CoPset) (D : LatentReal.Model Ω S) (A : LatentReal.Representation D)
    (owns : Val rT → S → IProp GF) (h : LatentReal.IsRepresentedOracleSpec E D A owns)
    (v : Val rT) (s : S) (F : Ω → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :
    iprop(owns v s ∗ ↯ (∫⁻ x, F x ∂D.posterior s) ∗ R) ⊢
      tglWp E (.app (.lam (.app v.fst (.lit (.int 3)))) (.app v.fst (.lit (.int 8))))
        (fun result => iprop(∃ (t : S) (I J : LatentReal.RationalInterval),
          ⌜result = LatentReal.intervalVal J ∧ A.Observed t 8 I ∧ A.Observed t 3 J⌝ ∗
          owns v t ∗ ↯ (∫⁻ x, F x ∂D.posterior t) ∗ R)) := by
  iintro ⟨Hstate, Hcredit, HR⟩
  twp_bind pl(&v.fst #8)
  iapply (h.wp v s 8 F hF _) $$ Hstate Hcredit
  iintro %t %I %hI Hstate Hcredit
  twp_pure
  iapply (h.wp v t 3 F hF _) $$ Hstate Hcredit
  iintro %u %J %hJ Hstate Hcredit
  iexists u, I, J
  iframe Hstate Hcredit HR
  ipureintro
  exact ⟨rfl, A.observed_refines hJ.1 hI.2.2, hJ.2.2⟩

private def squareAndRead (source : Val rT) : Exp rT :=
  .app (.lam (.app (.lam (.app (.bvar 1) (.lit (.int 3))))
    (.app (.bvar 0) (.lit (.int 8)))))
    (.app (.app Occil.PSRN.multiply source.fst) source.fst)

/-- Both operand reads and both later product queries retain the same owned world. -/
theorem aliased_square (E : CoPset) (D : LatentReal.Model Ω S)
    (A : LatentReal.Representation D) (P : S → IProp GF) (source : Val rT)
    (hsource : LatentReal.IsRepresentedViewSpec E D A P source) (s : S)
    (F : Ω → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :
    iprop(P s ∗ ↯ (∫⁻ x, F x ∂D.posterior s) ∗ R) ⊢
      tglWp E (squareAndRead source)
        (fun result => iprop(∃ (t : S) (I J : LatentReal.RationalInterval),
          ⌜result = LatentReal.intervalVal J ∧
            (LatentReal.Representation.multiply D D (.refl D) A A).Observed t 8 I ∧
            (LatentReal.Representation.multiply D D (.refl D) A A).Observed t 3 J⌝ ∗
          LatentReal.ViewOwns (LatentReal.multiplyVal source source) P
            (LatentReal.multiplyVal source source) t ∗
          ↯ (∫⁻ x, F x ∂D.posterior t) ∗ R)) := by
  have hmul := LatentReal.represented_multiply_oracleSpec E D D (.refl D) A A P
    source source hsource hsource
  iintro ⟨Hstate, Hcredit, HR⟩
  unfold squareAndRead
  twp_bind pl(&Occil.PSRN.multiply &source.fst &source.fst)
  iapply tglWp_wand
  isplitl [Hstate]
  · iapply LatentReal.twp_multiply E source source P s $$ Hstate
  iintro %v Hstate
  isimp only [LatentReal.ViewOwns] at Hstate
  icases Hstate with ⟨%hv, Hstate⟩
  subst v
  twp_pure
  have hread := reread E (D.multiply D (.refl D))
    (LatentReal.Representation.multiply D D (.refl D) A A)
    (LatentReal.ViewOwns (LatentReal.multiplyVal source source) P) hmul
    (LatentReal.multiplyVal source source) s F hF R
  simp only [LatentReal.Model.multiply] at hread
  iapply tglWp_wand
  isplitl [Hstate Hcredit HR]
  · iapply hread
    isplitl [Hstate]
    · isimp only [LatentReal.ViewOwns]
      iframe Hstate
    iframe Hcredit HR
  iintro %result ⟨%t, %I, %J, %hresult, Hstate, Hcredit, HR⟩
  iexists t, I, J
  iframe Hstate Hcredit HR
  ipureintro
  exact hresult

#print axioms SampLib.LatentReal.Representation.multiply
#print axioms SampLib.LatentReal.represented_multiply_oracleSpec
#print axioms aliased_square
#print axioms reread

end
end RepresentedMultiplicationProducer
