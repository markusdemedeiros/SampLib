import SampLib.AliasTable
import SampLib.Syntax.Aliases

open ProbLang
open scoped ENNReal

namespace ReviewExactStructured002

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
/-- Private sampler state and unrelated resources survive arbitrary-credit calls. -/
theorem owned_frame {α : Type _} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {E : CoPset} {P : IProp GF} {e : Exp rT}
    {encode : α → Val rT} (h : IsOwnedDistSpec E P e μ encode)
    (F : α → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :
    ⊢ P ∗ ↯ (∫⁻ x, F x ∂μ) ∗ R -∗ tglWp E e
      (fun v : Val rT => iprop(∃ x : α, ⌜v = encode x⌝ ∗ P ∗ ↯ (F x) ∗ R)) := by
  iintro ⟨HP, Hcredit, HR⟩
  iapply (h.wp F hF _) $$ HP Hcredit
  iintro %x HP Hcredit
  iexists x
  iframe HP Hcredit HR
  itrivial

example (E : CoPset) (ws : List ℕ) [NeZero ws.sum]
    (t : AliasMass.Table ws.length ws.sum)
    (hmass : ∀ i, t.mass i = ws.length * ws.get i) (probability aliases : Loc)
    (F : ℕ → ℝ≥0∞) (R : IProp GF) :=
  owned_frame (AliasTable.voseDraw_ownedDistSpec (GF := GF) E ws (NeZero.pos ws.sum)
    t hmass probability aliases) F (measurable_of_countable _) R

private def draw (table : Val rT) : Val rT :=
  ⟨.lam pl(&Occil.WeightedVariants.voseDraw &table.fst #()), .lam (by is_lc), by is_lc⟩

private theorem draw_spec (E : CoPset) (ws : List ℕ) [NeZero ws.sum]
    (t : AliasMass.Table ws.length ws.sum)
    (hmass : ∀ i, t.mass i = ws.length * ws.get i) (probability aliases : Loc) :
    IsOwnedDistSpec (GF := GF) E (AliasTable.owns (rT := rT) t probability aliases)
      pl(&(draw (AliasTable.value ws.length ws.sum probability aliases)).fst #())
      (WeightedChoice.law ws) (fun i : ℕ => Val.int i) where
  spec F hF := by
    iintro Hinput
    twp_pure
    simp only [AliasSyntax.voseDraw_openRec]
    iapply (AliasTable.voseDraw_ownedDistSpec E ws (NeZero.pos ws.sum)
      t hmass probability aliases).spec F hF $$ Hinput

/-- Reusing one table gives the independent joint law while retaining ownership. -/
example (E : CoPset) (ws : List ℕ) [NeZero ws.sum]
    (t : AliasMass.Table ws.length ws.sum)
    (hmass : ∀ i, t.mass i = ws.length * ws.get i) (probability aliases : Loc)
    (count : ℕ) (F : (Fin count → ℕ) → ℝ≥0∞) (R : IProp GF) :=
  owned_frame (repeatSample_ownedDistSpec (GF := GF) E
    (AliasTable.owns (rT := rT) t probability aliases) (WeightedChoice.law ws)
    (fun i : ℕ => Val.int i) (draw (AliasTable.value ws.length ws.sum probability aliases))
    (draw_spec E ws t hmass probability aliases) count)
    F (measurable_of_countable _) R

private def sparse : AliasMass.Table 3 1 where
  threshold _ := 0
  target _ := 1
  threshold_le _ := by decide

private theorem sparse_mass : ∀ i : Fin ([0, 1, 0] : List ℕ).length,
    sparse.mass i = ([0, 1, 0] : List ℕ).length * ([0, 1, 0] : List ℕ).get i := by decide

local instance : NeZero ([0, 1, 0] : List ℕ).sum := ⟨by decide⟩

/-- Zero-weight columns can point to the sole positive category. -/
example (E : CoPset) (probability aliases : Loc) (F : ℕ → ℝ≥0∞) (R : IProp GF) :=
  owned_frame (AliasTable.voseDraw_ownedDistSpec (GF := GF) E [0, 1, 0] (by decide)
    sparse sparse_mass probability aliases) F (measurable_of_countable _) R

#print axioms SampLib.AliasTable.voseDraw_ownedDistSpec
#print axioms SampLib.AliasMass.expectation_range
#print axioms draw_spec
#print axioms sparse_mass

end

end ReviewExactStructured002
