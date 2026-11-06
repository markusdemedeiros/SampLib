import SampLib.Common.Laws.AcceptedProposal
import SampLib.Core.Laws.IntegerIntervals
import SampLib.General.Support.IntegerThreshold
import SampLib.Core.GeneralSyntax
import SampLib.Core.SupportedSpec
import Samplers.General.Core

/-! # Rejection sampling from a bounded integer-grid density -/

open ProbLang
open scoped ENNReal

namespace SampLib.PdfRejection

noncomputable section

/-- A nonnegative integer height function bounded by a positive envelope. -/
structure Model where
  lower : ℤ
  upper : ℤ
  interval : lower < upper
  envelope : ℕ
  positive : 0 < envelope
  height : ℤ → ℕ
  bounded : ∀ x ∈ Set.Ico lower upper, height x ≤ envelope

section mathematics

open MeasureTheory

abbrev proposal (D : Model) := RndIntExcRange.law D.lower D.upper D.interval

/-- Outside the proposal interval, the arbitrary acceptance extension is zero. -/
def acceptance (D : Model) (x : ℤ) : unitInterval :=
  if hx : x ∈ Set.Ico D.lower D.upper then
    IntegerThreshold.bias (D.height x) D.envelope D.positive (D.bounded x hx)
  else 0

/-- Uniform proposal mass weighted by its integer-height acceptance probability. -/
abbrev law (D : Model) (hmass : AcceptedProposal.mass (proposal D) (acceptance D) ≠ 0) :=
  AcceptedProposal.law (proposal D) (acceptance D) hmass

/-- Credits returned by the acceptance comparison. -/
def coinCredit (D : Model) (hmass : AcceptedProposal.mass (proposal D) (acceptance D) ≠ 0)
    (F : ℤ → ℝ≥0∞) (ε : ℝ≥0∞) (x : ℤ) (b : Bool) : ℝ≥0∞ :=
  if b then F x else AcceptedProposal.credit (proposal D) (acceptance D) hmass F +
    AcceptedProposal.factor (proposal D) (acceptance D) * ε

private theorem coin_expectation (D : Model)
    (hmass : AcceptedProposal.mass (proposal D) (acceptance D) ≠ 0)
    (F : ℤ → ℝ≥0∞) (ε : ℝ≥0∞) (x : ℤ) (hx : x ∈ Set.Ico D.lower D.upper) :
    RealCoin.credit
      (IntegerThreshold.bias (D.height x) D.envelope D.positive (D.bounded x hx))
      (coinCredit D hmass F ε x) =
      AcceptedProposal.kernel (proposal D) (acceptance D) hmass F ε x := by
  simp [RealCoin.credit, RealCoin.pmf, coinCredit, AcceptedProposal.kernel,
    AcceptedProposal.weight, AcceptedProposal.rejectedWeight, acceptance, hx]

end mathematics

private theorem height_valid (D : Model) (x : ℤ) (hx : x ∈ Set.Ico D.lower D.upper) :
    decide ((D.envelope : ℤ) < (D.height x : ℤ)) = false := by
  exact decide_eq_false (by exact_mod_cast not_lt.mpr (D.bounded x hx))

private theorem interval_valid (D : Model) :
    Bool.or (decide (D.upper ≤ D.lower)) (decide ((D.envelope : ℤ) ≤ 0)) = false := by
  simp [not_le.mpr D.interval, D.positive.ne']

@[simp] private theorem uniform_subst {rT : Type _} (x : Var) (e : Exp rT) :
    Exp.subst Occil.uniformInt x e = Occil.uniformInt :=
  Exp.subst_fresh x _ e (by simp [UniformInt.uniformInt_fv])

@[simp] private theorem range_subst {rT : Type _} (x : Var) (e : Exp rT) :
    Exp.subst Occil.rndIntExcRange x e = Occil.rndIntExcRange :=
  Exp.subst_fresh x _ e (by simp [RndIntExcRange.rndIntExcRange_fv])

/-- Insert the callback after closing the retry loop's own binders. -/
private def loop {rT : Type _} (D : Model) (density : Val rT) : Exp rT :=
  Exp.subst (pl% rec retry u :=
    let x := &Occil.rndIntExcRange #int D.lower #int D.upper;
    let height := source x;
    if (height < #0) || (#int (D.envelope : ℤ) < height) then fail else
      if &Occil.uniformInt #int (D.envelope : ℤ) < height then x else retry #())
    (.named "source") density.fst

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_loop (E : CoPset) (D : Model) (density : Val rT)
    (hdensity : ∀ x ∈ Set.Ico D.lower D.upper,
      ⊢ tglWp E pl(&density.fst #int x)
        (fun v : Val rT => iprop(⌜v = Val.int (D.height x : ℤ)⌝)))
    (hmass : AcceptedProposal.mass (proposal D) (acceptance D) ≠ 0)
    (F : ℤ → ℝ≥0∞) :
    ⊢ ↯ (AcceptedProposal.credit (proposal D) (acceptance D) hmass F) -∗
      tglWp E pl(&(loop D density) #())
        (fun v : Val rT => iprop(∃ x : ℤ, ⌜v = Val.int x⌝ ∗ ↯ (F x))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε
    (AcceptedProposal.one_lt_factor (proposal D) (acceptance D) hmass) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  isimp [loop, Exp.subst, Exp.close, Exp.closeRec]
  iterate 2 twp_pure
  twp_bind pl(&Occil.rndIntExcRange #int D.lower #int D.upper)
  icombine Hcredit Hterm as Htotal
  ihave Hsample := ErrorCredit.weaken
    (AcceptedProposal.expectation_preservation (proposal D) (acceptance D)
      (measurable_of_countable _) hmass F (measurable_of_countable _) ε) $$ Htotal
  iapply ((RndIntExcRange.rndIntExcRange_distSpec E D.lower D.upper D.interval).wp_supported
    (fun x => x ∈ Set.Ico D.lower D.upper) measurableSet_Ico
    (RndIntExcRange.ae_mem D.lower D.upper D.interval)
    (AcceptedProposal.kernel (proposal D) (acceptance D) hmass F ε)
    (measurable_of_countable _) _) $$ Hsample
  iintro %x %hx Hcredit
  twp_pure
  twp_bind pl(&density.fst #int x)
  iapply tglWp_wand
  isplitl []
  · iapply hdensity x hx
  iintro %v %hv
  subst v
  twp_pures
  rw [height_valid D x hx, Bool.false_or]
  twp_pure
  simp only [UniformInt.uniformInt_openRec, GeneralSyntax.rndIntExcRange_openRec]
  twp_bind pl(&Occil.uniformInt #int (D.envelope : ℤ) < #int (D.height x : ℤ))
  isimp only [← coin_expectation D hmass F ε x hx, ← RealCoin.lintegral_law] at Hcredit
  iapply ((IntegerThreshold.threshold_distSpec E (D.height x) D.envelope D.positive
    (D.bounded x hx)).wp (coinCredit D hmass F ε x) (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  cases b
  · twp_pure
    isimp only [coinCredit, Bool.false_eq_true, ite_false] at Hcredit
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    isimp [loop, Exp.subst, Exp.close, Exp.closeRec] at IH
    iapply IH $$ Hterm Hcredit
  · twp_pures
    twp_value
    imodintro
    iexists x
    isimp only [coinCredit, ite_true] at Hcredit
    iframe Hcredit
    itrivial

/-- The grid-density rejection loop, with positive total acceptance mass. -/
theorem twp_pdfRejection (E : CoPset) (D : Model) (density : Val rT)
    (hdensity : ∀ x ∈ Set.Ico D.lower D.upper,
      ⊢ tglWp E pl(&density.fst #int x)
        (fun v : Val rT => iprop(⌜v = Val.int (D.height x : ℤ)⌝)))
    (hmass : AcceptedProposal.mass (proposal D) (acceptance D) ≠ 0)
    (F : ℤ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ x, F x ∂law D hmass) -∗
      tglWp E pl(&Occil.General.pdfRejection &density.fst #int D.lower #int D.upper
        #int (D.envelope : ℤ) #())
        (fun v : Val rT => iprop(∃ x : ℤ, ⌜v = Val.int x⌝ ∗ ↯ (F x))) := by
  have hloop := twp_loop (rT := rT) (GF := GF) E D density hdensity hmass F
  simp [loop, Exp.subst, Exp.close, Exp.closeRec] at hloop
  iintro Hcredit
  twp_pures
  rw [interval_valid D]
  iterate 2 twp_pure
  simp only [GeneralSyntax.rndIntExcRange_openRec, GeneralSyntax.rndIntExcRange_closeRec,
    UniformInt.uniformInt_openRec, UniformInt.uniformInt_closeRec]
  iapply hloop
  isimp only [AcceptedProposal.credit]
  iexact Hcredit

/-- Exact normalized grid law; the density callback is required only on proposals. -/
theorem pdfRejection_distSpec (E : CoPset) (D : Model) (density : Val rT)
    (hdensity : ∀ x ∈ Set.Ico D.lower D.upper,
      ⊢ tglWp E pl(&density.fst #int x)
        (fun v : Val rT => iprop(⌜v = Val.int (D.height x : ℤ)⌝)))
    (hmass : AcceptedProposal.mass (proposal D) (acceptance D) ≠ 0) :
    IsDistSpec (GF := GF) E pl(&Occil.General.pdfRejection &density.fst
      #int D.lower #int D.upper #int (D.envelope : ℤ) #()) (law D hmass) Val.int where
  spec F _ := wand_entails (twp_pdfRejection E D density hdensity hmass F)

end specification

end

end SampLib.PdfRejection
