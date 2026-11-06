import SampLib.Samplers.FastLoadedDiceRoller
import SampLib.Distributions.WeightedPositiveSupport

open ProbLang Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS MeasureTheory
open scoped ENNReal

namespace SampLib.ExactFastLoadedDiceCallers

noncomputable section

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem framed (E : CoPset) (ws : List ℕ) [NeZero ws.sum] (F : ℕ → ℝ≥0∞)
    (P : IProp GF) :
    iprop(P ∗ ↯ (∫⁻ i, F i ∂WeightedChoice.law ws)) ⊢
      tglWp E pl(&Occil.Weighted.fastLoadedDiceRoller
        &(listVal (fun w : ℕ => Val.int w) ws).fst #())
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int (i : ℤ)⌝ ∗ P ∗ ↯ (F i))) := by
  iintro ⟨HP, Hcredit⟩
  iapply ((FastLoadedDice.fastLoadedDiceRoller_distSpec E ws).wp
    F (measurable_of_countable _) _) $$ Hcredit
  iintro %i Hcredit
  iexists i
  iframe HP Hcredit
  itrivial

private def invalidCredit (ws : List ℕ) (i : ℕ) : ℝ≥0∞ :=
  if 0 < ws[i]?.getD 0 then 0 else ∞

/-- Infinite credit at every zero row and out-of-range label still has expectation zero. -/
private theorem invalid_expectation (ws : List ℕ) :
    (∫⁻ i, invalidCredit ws i ∂WeightedChoice.law ws) = 0 := by
  have ha := WeightedChoice.ae_pos_weight ws
  have hc : invalidCredit ws =ᵐ[WeightedChoice.law ws] (fun _ => 0) :=
    ha.mono (fun i hi => by simp only [invalidCredit, ite_eq_left hi])
  rw [lintegral_congr_ae hc]
  simp

/-- The public infinite-credit interface rules out the implicit dummy label too. -/
theorem positive_support (E : CoPset) (ws : List ℕ) [NeZero ws.sum] (P : IProp GF) :
    iprop(P ∗ ↯ 0) ⊢
      tglWp E pl(&Occil.Weighted.fastLoadedDiceRoller
        &(listVal (fun w : ℕ => Val.int w) ws).fst #())
        (fun v : Val rT => iprop(∃ i : ℕ,
          ⌜v = Val.int (i : ℤ) ∧ 0 < ws[i]?.getD 0⌝ ∗ P)) := by
  iintro ⟨HP, Hcredit⟩
  ihave Hsample := ErrorCredit.weaken (le_of_eq (invalid_expectation ws)) $$ Hcredit
  iapply ((FastLoadedDice.fastLoadedDiceRoller_distSpec E ws).wp
    (invalidCredit ws) (measurable_of_countable _) _) $$ Hsample
  iintro %i Hcredit
  by_cases h : 0 < ws[i]?.getD 0
  · iexists i
    iframe HP
    ipureintro
    exact ⟨rfl, h⟩
  · isimp only [invalidCredit, ite_eq_right h] at Hcredit
    iexfalso
    iapply ErrorCredit.contradict (by simp) $$ Hcredit

local instance : NeZero ([0, 1, 2, 0] : List ℕ).sum := ⟨by decide⟩
local instance : NeZero ([0, 1, 0] : List ℕ).sum := ⟨by decide⟩
local instance : NeZero ([0, 2, 2, 0] : List ℕ).sum := ⟨by decide⟩

example (E : CoPset) : IsDistSpec (GF := GF) E
    pl(&Occil.Weighted.fastLoadedDiceRoller
      &(listVal (fun w : ℕ => Val.int w) [0, 1, 2, 0]).fst #())
      (WeightedChoice.law [0, 1, 2, 0]) (fun i => Val.int (i : ℤ)) :=
  FastLoadedDice.fastLoadedDiceRoller_distSpec E [0, 1, 2, 0]

example (E : CoPset) : IsDistSpec (GF := GF) E
    pl(&Occil.Weighted.fastLoadedDiceRoller
      &(listVal (fun w : ℕ => Val.int w) [0, 1, 0]).fst #())
      (WeightedChoice.law [0, 1, 0]) (fun i => Val.int (i : ℤ)) :=
  FastLoadedDice.fastLoadedDiceRoller_distSpec E [0, 1, 0]

example (E : CoPset) : IsDistSpec (GF := GF) E
    pl(&Occil.Weighted.fastLoadedDiceRoller
      &(listVal (fun w : ℕ => Val.int w) [0, 2, 2, 0]).fst #())
      (WeightedChoice.law [0, 2, 2, 0]) (fun i => Val.int (i : ℤ)) :=
  FastLoadedDice.fastLoadedDiceRoller_distSpec E [0, 2, 2, 0]

#print axioms FastLoadedDice.fastLoadedDiceRoller_distSpec
#print axioms FastLoadedDice.twp_loop
#print axioms FastLoadedDice.twp_scan
#print axioms FastLoadedDiceCredits.expectation
#print axioms DdgContext.twp_of_columns
#print axioms framed
#print axioms positive_support

end

end SampLib.ExactFastLoadedDiceCallers
