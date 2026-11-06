import SampLib.PSRN.Support.LatentRepresentedReciprocal

/-! Repeated alias reads retain one owner and agree on the actual represented interval. -/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal.RepresentedReciprocal.ProducerCallers

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

private def twice (v : Val rT) (n : ℕ) : Exp rT :=
  let call := .app v.fst (.lit (.int (n : ℤ)))
  .app (.lam (.app (.lam (.pair (.bvar 1) (.bvar 0))) call)) call

theorem repeated_alias (E : CoPset) (D : Model Ω S) (R : Representation D)
    (O : Val rT → S → IProp GF) (horacle : IsRepresentedOracleSpec E D R O)
    (v : Val rT) (s : S) (n : ℕ) (F : Ω → ℝ≥0∞) (hF : Measurable F) (Q : IProp GF) :
    iprop(owns D O v s ∗ ↯ (∫⁻ ω, F ω ∂(model D R).posterior s) ∗ Q) ⊢
      tglWp E (twice v n)
        (fun result : Val rT => iprop(∃ (t : S) (I : RationalInterval),
          ⌜result = Val.pair (intervalVal I) (intervalVal I) ∧ D.refines s t⌝ ∗
          owns D O v t ∗ ↯ (∫⁻ ω, F ω ∂(model D R).posterior t) ∗ Q)) := by
  iintro ⟨Hstate, Hcredit, HQ⟩
  have hspec := oracleSpec E D R O horacle
  twp_bind pl(&v.fst #int (n : ℤ))
  iapply hspec.wp v s n F hF _ $$ Hstate Hcredit
  iintro %t %I %hI Hstate Hcredit
  twp_pure
  twp_bind pl(&v.fst #int (n : ℤ))
  iapply hspec.wp v t n F hF _ $$ Hstate Hcredit
  iintro %u %J %hJ Hstate Hcredit
  have hfirst : ∀ᵐ ω ∂(model D R).posterior u, I = (representation D R).interval n ω :=
    (representation D R).observed_refines hJ.1 hI.2.2
  have heq : I = J := by
    obtain ⟨ω, hω, hω'⟩ := (hfirst.and hJ.2.2).exists
    exact hω.trans hω'.symm
  subst J
  twp_pures
  twp_value
  imodintro
  iexists u, I
  iframe Hstate Hcredit HQ
  ipureintro
  exact ⟨rfl, D.refines_trans hI.1 hJ.1⟩

/-- The actual constructor preserves an arbitrary frame before any observation takes place. -/
theorem constructor_framed (E : CoPset) (D : Model Ω S) (R : Representation D)
    (O : Val rT → S → IProp GF) (source : Val rT) (s : S)
    (hne : ∀ᵐ ω ∂D.posterior s, D.value ω ≠ 0) (F : Ω → ℝ≥0∞) (Q : IProp GF) :
    iprop(O source s ∗ ↯ (∫⁻ ω, F ω ∂D.posterior s) ∗ Q) ⊢
      tglWp E pl(&Occil.PSRN.reciprocal &source.fst)
        (fun result : Val rT => iprop(owns D O result s ∗
          ↯ (∫⁻ ω, F ω ∂(model D R).posterior s) ∗ Q)) := by
  iintro ⟨Hstate, Hcredit, HQ⟩
  iapply tglWp_wand
  isplitl [Hstate Hcredit]
  · iapply twp_reciprocal E D R O source s hne F
    iframe Hstate Hcredit
  iintro %result ⟨Hstate, Hcredit⟩
  iframe Hstate Hcredit HQ

#print axioms model
#print axioms representation
#print axioms twp_observe
#print axioms oracleSpec
#print axioms twp_reciprocal
#print axioms expectation_preservation
#print axioms tail_mass_tendsto_zero
#print axioms repeated_alias
#print axioms constructor_framed
#print axioms Program.source_eq

end

end SampLib.LatentReal.RepresentedReciprocal.ProducerCallers
