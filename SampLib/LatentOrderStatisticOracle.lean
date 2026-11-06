import SampLib.LatentOrderStatisticModel

/-! # Reading a selected order statistic

Every read focuses the selected root and restores the whole family. The rank
identity and physical aliases survive all later refinements by absolute continuity.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal.OrderStatistic

noncomputable section

section mathematics

open MeasureTheory

/-- The observed coordinate cell represents the rank under the refined posterior. -/
theorem read_observed (n k : ℕ) (hk : 0 < k ∧ k ≤ n) (s : State n) (i : Fin n)
    (bits : ℕ) (q : List Bool) (hq : UniformBag.readRefines (s.prefixes i) bits q)
    (hrank : ∀ᵐ x ∂UniformVector.law s.prefixes, UniformOrderStatistic.rank n k hk x = x i) :
    (model n k hk).Encloses (update s i q) bits (LatentUniform.interval q bits) ∧
      (representation n k hk).Observed (update s i q) bits (LatentUniform.interval q bits) := by
  have href := UniformVector.refines_update s.prefixes i q hq.1
  have hvalue := (UniformVector.law_refines href).ae_le hrank
  have hencloses := UniformVector.view_interval_encloses s.prefixes i q bits hq
  have hobserved := UniformVector.ae_coordinate (Function.update s.prefixes i q) i
    (P := fun x => LatentUniform.interval q bits = LatentUniform.dyadicInterval bits x)
    (by simpa only [Function.update_self, LatentUniform.representation, Representation.Observed,
        LatentUniform.model] using
      LatentUniform.interval_observed hq)
  constructor
  · filter_upwards [hvalue, hencloses] with x hx hI
    simpa only [model, update, UniformVector.view, UniformVector.world, hx] using hI
  · filter_upwards [hvalue, hobserved] with x hx hI
    change LatentUniform.interval q bits = LatentUniform.dyadicInterval bits
      (UniformOrderStatistic.rank n k hk x)
    simpa only [LatentUniform.representation, hx] using hI

end mathematics

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Aliased reads preserve every root and arbitrary credit on the joint vector. -/
theorem representedOracleSpec (E : CoPset) (n k : ℕ) (hk : 0 < k ∧ k ≤ n) :
    IsRepresentedOracleSpec (GF := GF) E (model n k hk) (representation n k hk)
      (owns n k hk) where
  observe v s bits F hF := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [owns] at Hstate
    ihave ⟨%roots, %i, %hselected, Hroots⟩ := Hstate
    rcases hselected with ⟨hmeta, rfl, hrank⟩
    isimp only [model] at Hcredit
    iapply tglWp_wand
    isplitl [Hroots Hcredit]
    · iapply UniformVector.twp_observe_coordinate E roots s.prefixes i bits F hF
      iframe Hroots Hcredit
    iintro %result ⟨%q, %hq, Hroots, Hcredit⟩
    rcases hq with ⟨hread, rfl⟩
    iexists update s i q, LatentUniform.interval q bits
    isplitl []
    · ipureintro
      exact ⟨rfl, refines_update s i q hread.1, read_observed n k hk s i bits q hread hrank⟩
    isplitr [Hcredit]
    · isimp only [owns, update]
      iexists roots, i
      iframe Hroots
      ipureintro
      exact ⟨hmeta, rfl, (UniformVector.law_refines
        (UniformVector.refines_update s.prefixes i q hread.1)).ae_le hrank⟩
    isimp only [model, update]
    iframe Hcredit

end specification

end

end SampLib.LatentReal.OrderStatistic
