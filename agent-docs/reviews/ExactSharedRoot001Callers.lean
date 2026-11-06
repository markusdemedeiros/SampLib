import SampLib.LatentRootViews
import SampLib.PSRN.Support.LatentRootLaw
import SampLib.PSRN.Support.LatentRepresentedViews
import SampLib.PSRN.Support.LatentUniformRepresentation

open ProbLang
open scoped ENNReal

namespace ReviewExactSharedRoot001

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib SampLib.LatentReal

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

private def rootAndSource (source : Val rT) (degree n m : ℕ) : Exp rT :=
  .app (.lam (.app (.lam (.app (.lam (.pair (.bvar 1) (.bvar 0)))
    (.app source.fst (.lit (.int m))))) (.app (.bvar 0) (.lit (.int n)))))
    pl(&Occil.PSRN.root &source.fst #int (degree : ℤ))

/-- Source and root observations retain one physical state and their full joint world. -/
theorem root_and_source (E : CoPset) (D : Model Ω S) (A : Representation D)
    (hD : D.MeasurableError) (P : S → IProp GF) (source : Val rT)
    (hsource : IsRepresentedViewSpec E D A P source)
    (degree : ℕ) (hdegree : 2 ≤ degree) (s : S) (hadmissible : Root.Admissible D degree s)
    (n m : ℕ) (F : Ω → ℝ≥0∞) (hF : Measurable F) (Q : IProp GF) :
    ⊢ P s ∗ ↯ (∫⁻ x, F x ∂D.posterior s) ∗ Q -∗
      tglWp E (rootAndSource source degree n m)
        (fun result => iprop(∃ (t : S) (I J : RationalInterval),
          ⌜result = Val.pair (intervalVal I) (intervalVal J) ∧ D.refines s t ∧
            (D.nthRoot degree).Encloses t n I ∧
            (D.nthRoot degree).dyadicRepresentation.Observed t n I ∧
            D.Encloses t m J ∧ A.Observed t m J⌝ ∗
          P t ∗ ↯ (∫⁻ x, F x ∂D.posterior t) ∗ Q)) := by
  iintro ⟨Hstate, Hcredit, HQ⟩
  unfold rootAndSource
  twp_bind pl(&Occil.PSRN.root &source.fst #int (degree : ℤ))
  iapply tglWp_wand
  isplitl [Hstate]
  · iapply Root.Program.twp_root E source degree hdegree P s $$ Hstate
  iintro %root Hstate
  isimp only [ViewOwns] at Hstate
  icases Hstate with ⟨%hroot, Hstate⟩
  subst root
  twp_pure
  twp_bind pl(&(Root.Program.value source degree).fst #int (n : ℤ))
  have hroot := Root.represented_viewSpec E D hD P source hsource.forget degree hdegree
  ihave Hguard : Root.admissibleState D degree P s $$ [Hstate]
  · isimp only [Root.admissibleState]
    iframe Hstate
    itrivial
  have hread (Φ : Val rT → IProp GF) := hroot.wp s n F hF Φ
  simp only [Model.nthRoot] at hread
  iapply hread _ $$ Hguard Hcredit
  iintro %t %I %hI Hstate Hcredit
  twp_pure
  have hsource' := Root.represented_source_viewSpec E D A degree P source hsource
  twp_bind pl(&source.fst #int (m : ℤ))
  iapply hsource'.wp t m F hF _ $$ Hstate Hcredit
  iintro %u %J %hJ Hstate Hcredit
  twp_pures
  twp_value
  imodintro
  isimp only [Root.admissibleState] at Hstate
  icases Hstate with ⟨_, Hstate⟩
  iexists u, I, J
  iframe Hstate Hcredit HQ
  ipureintro
  exact ⟨rfl, D.refines_trans hI.1 hJ.1,
    (D.nthRoot degree).encloses_refines hJ.1 hI.2.1,
    (D.nthRoot degree).dyadicRepresentation.observed_refines hJ.1 hI.2.2,
    hJ.2.1, hJ.2.2⟩

section uniform

variable [ProbLangDist.IsUniformInt rT]

private theorem uniformView (E : CoPset) (source : Val rT) :
    IsRepresentedViewSpec (GF := GF) E LatentUniform.model LatentUniform.representation
      (LatentUniform.owns source) source where
  observe v p n F hF := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [ViewOwns] at Hstate
    icases Hstate with ⟨%hv, Hstate⟩
    subst v
    iapply (LatentUniform.representedOracleSpec E).wp source p n F hF _ $$ Hstate Hcredit
    iintro %t %I %hI Hstate Hcredit
    iexists t, I
    isplit
    · ipureintro
      exact ⟨rfl, hI⟩
    isplitl [Hstate]
    · isimp only [ViewOwns]
      iframe Hstate
    iexact Hcredit

/-- The original uniform remains observable after constructing and reading its square root. -/
example (E : CoPset) (source : Val rT) (F : ℝ → ℝ≥0∞)
    (hF : Measurable F) (Q : IProp GF) := by
  have : MeasureTheory.NullSingletonClass (LatentUniform.model.law []) := by
    rw [LatentUniform.model_initial_law]
    change MeasureTheory.NullSingletonClass
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ico 0 1))
    infer_instance
  have hadmissible := Root.Admissible.of_atomless LatentUniform.model 2 []
    ((DyadicPosterior.ae_mem_unit []).mono fun _ hx => hx.1)
  exact root_and_source E LatentUniform.model LatentUniform.representation
    (fun _ => measurable_const) (LatentUniform.owns source) source (uniformView E source)
    2 (by decide) [] hadmissible 5 2 F hF Q

end uniform

example : ¬ Root.Admissible (LatentRational.model 1 1) 2 () := by
  intro h
  have hboundary := h.2 1 1 (by decide) (by decide)
  simp [LatentRational.model] at hboundary

#print axioms SampLib.LatentReal.Root.twp_observe
#print axioms SampLib.LatentReal.Root.twp_bisect
#print axioms SampLib.LatentReal.Root.twp_bracket
#print axioms SampLib.LatentReal.Root.represented_viewSpec
#print axioms SampLib.LatentReal.Model.rayleigh_law
#print axioms SampLib.LatentReal.Model.rayleigh_admissible
#print axioms root_and_source

end

end ReviewExactSharedRoot001
