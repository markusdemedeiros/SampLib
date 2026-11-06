import SampLib.Common.Laws.FiniteCDF
import SampLib.Core.GeneralSyntax
import Samplers.General.Core

/-! # Integer-grid CDF inversion by bisection -/

open ProbLang
open scoped ENNReal

namespace SampLib.InverseCDF

noncomputable section

open FiniteCDF

/-- Close search binders before inserting an arbitrary callback value. -/
private def loop {rT : Type _} (oracle : Val rT) (rank : ℤ) : Exp rT :=
  Exp.subst (pl% rec bisect lo hi :=
    if lo = hi then lo else
      let mid := lo + (hi - lo) / #2;
      if #int rank <= source mid then bisect lo mid else bisect (mid + #1) hi)
    (.named "source") oracle.fst

private theorem domain_test (D : Model) :
    Bool.or (decide ((D.scale : ℤ) ≤ 0)) (decide (D.upper < D.lower)) = false := by
  simp [D.positive.ne', not_lt.mpr D.nonempty]

private theorem equal_test {rT : Type _} [BEq rT] (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = decide (a = b) := by
  change (a == b) = decide (a = b)
  by_cases h : a = b <;> simp [h]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_search (E : CoPset) (D : Model) (oracle : Val rT)
    (horacle : ∀ x ∈ Set.Icc D.lower D.upper,
      ⊢ tglWp E pl(&oracle.fst #int x)
        (fun v : Val rT => iprop(⌜v = Val.int (D.cdf x)⌝)))
    (i : Fin D.scale) (w : Bracket D i) :
    ⊢ tglWp E pl(&(loop oracle ((i.val : ℤ) + 1)) #int w.lower #int w.upper)
      (fun v : Val rT => iprop(⌜v = Val.int (quantile D i)⌝)) := by
  induction w using (measure (fun w : Bracket D i => w.width)).wf.induction with
  | h w IH =>
    by_cases heq : w.lower = w.upper
    · isimp [loop, Exp.subst, Exp.close, Exp.closeRec]
      twp_pures
      rw [equal_test, decide_eq_true heq]
      twp_pures
      twp_value
      imodintro
      ipureintro
      rw [Bracket.done w heq]
    · have hlt := w.strict_of_ne heq
      isimp [loop, Exp.subst, Exp.close, Exp.closeRec]
      twp_pures
      rw [equal_test, decide_eq_false heq]
      twp_pures
      twp_bind pl(&oracle.fst #int w.midpoint)
      iapply tglWp_wand
      isplitl []
      · iapply horacle w.midpoint (w.midpoint_mem hlt)
      iintro %v %hv
      subst v
      twp_pure
      by_cases hc : (i.val : ℤ) + 1 ≤ D.cdf w.midpoint
      · rw [decide_eq_true hc]
        twp_pure
        have hnext := IH (w.left hlt hc) (w.left_width_lt hlt hc)
        simp [loop, Exp.subst, Exp.close, Exp.closeRec, Bracket.left, Bracket.midpoint] at hnext
        iapply hnext
      · rw [decide_eq_false hc]
        iterate 2 twp_pure
        have hnext := IH (w.right hlt hc) (w.right_width_lt hlt hc)
        simp [loop, Exp.subst, Exp.close, Exp.closeRec, Bracket.right, Bracket.midpoint] at hnext
        simp only [Exp.ofVal]
        iapply hnext

/-- The search follows one uniformly sampled interior CDF rank. -/
theorem twp_inverseCDF (E : CoPset) (D : Model) (oracle : Val rT)
    (horacle : ∀ x ∈ Set.Icc D.lower D.upper,
      ⊢ tglWp E pl(&oracle.fst #int x)
        (fun v : Val rT => iprop(⌜v = Val.int (D.cdf x)⌝)))
    (F : ℤ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ x, F x ∂law D) -∗
      tglWp E pl(&Occil.General.inverseCDF #int (D.scale : ℤ) &oracle.fst
        #int D.lower #int D.upper #())
        (fun v : Val rT => iprop(∃ x : ℤ, ⌜v = Val.int x⌝ ∗ ↯ (F x))) := by
  iintro Hcredit
  twp_pures
  rw [domain_test D]
  twp_pure
  twp_bind pl(&Occil.uniformInt #int (D.scale : ℤ))
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply (UniformInt.twp_uniformInt E D.scale D.positive
      (fun k => F (quantile D (position D k))))
    rw [FiniteCDF.expectation D F]
    iexact Hcredit
  iintro %v ⟨%k, %hv, %hk, Hcredit⟩
  subst v
  iterate 3 twp_pure
  have hsearch := twp_search (rT := rT) (GF := GF) E D oracle horacle
    ⟨k, hk⟩ (Bracket.initial D ⟨k, hk⟩)
  simp [loop, Exp.subst, Exp.close, Exp.closeRec, Bracket.initial] at hsearch
  rw [add_comm (k : ℤ) 1] at hsearch
  iapply tglWp_wand
  isplitl []
  · iapply hsearch
  iintro %v %hv
  iexists quantile D ⟨k, hk⟩
  isimp only [position_of_lt D k hk] at Hcredit
  iframe Hcredit
  ipureintro
  exact hv

/-- Exact CDF law, with arbitrary positive integer denominator and endpoint atoms. -/
theorem inverseCDF_distSpec (E : CoPset) (D : Model) (oracle : Val rT)
    (horacle : ∀ x ∈ Set.Icc D.lower D.upper,
      ⊢ tglWp E pl(&oracle.fst #int x)
        (fun v : Val rT => iprop(⌜v = Val.int (D.cdf x)⌝))) :
    IsDistSpec (GF := GF) E pl(&Occil.General.inverseCDF #int (D.scale : ℤ) &oracle.fst
      #int D.lower #int D.upper #()) (law D) Val.int where
  spec F _ := wand_entails (twp_inverseCDF E D oracle horacle F)

end specification

end

end SampLib.InverseCDF
