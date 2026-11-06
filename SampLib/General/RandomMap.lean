import SampLib.General.Laws.Markov
import SampLib.Core.ProofMode.BindFrom
import SampLib.Core.ListEncoding
import SampLib.Core.MarkovTerms

/-! # Independent random transition maps

Each row independently chooses one destination. The resulting sampled mapping
can subsequently be applied to several states with the same randomness.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.RandomMap

noncomputable section

abbrev Row := MarkovChain.Row

section mathematics

open MeasureTheory Measure

/-- Independent categorical draws, one for each transition row. -/
def law : List Row → Measure (List ℕ)
  | [] => dirac []
  | r :: rs => ((law rs).prod (WeightedChoice.law r.val)).map (fun z => z.2 :: z.1)

instance (rows : List Row) : IsProbabilityMeasure (law rows) := by
  induction rows with
  | nil => dsimp [law]; infer_instance
  | cons r rs ih =>
    let : NeZero r.val.sum := ⟨r.property.ne'⟩
    constructor
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- Independent rows factor the map expectation into successive expectations. -/
theorem expectation (r : Row) (rs : List Row) (F : List ℕ → ℝ≥0∞) :
    ∫⁻ ys, (∫⁻ j, F (j :: ys) ∂WeightedChoice.law r.val) ∂law rs =
      ∫⁻ ys, F ys ∂law (r :: rs) := by
  let : NeZero r.val.sum := ⟨r.property.ne'⟩
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    lintegral_prod _ (measurable_of_countable _).aemeasurable]

end mathematics

private theorem encode_cons {rT : Type _} [ProbLangℝ rT] (j : ℕ) (ys : List ℕ) :
    pl(inr((#int (j : ℤ), &(listVal (fun n : ℕ => Val.int n) ys).fst))) =
      Exp.ofVal (listVal (fun n : ℕ => Val.int n) (j :: ys) : Val rT) := rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] MarkovTerms.weightedChoice_openRec
  MarkovTerms.weightedChoice_closeRec

def encodeRow (r : Row) : Val rT := listVal (fun n : ℕ => Val.int n) r.val

/-- Symbolic execution samples each row once, retaining every sampled destination. -/
theorem twp_randomMap (E : CoPset) (rows : List Row) (F : List ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ ys, F ys ∂law rows) -∗
      tglWp E pl(&Occil.General.randomMap &(listVal encodeRow rows).fst #())
        (fun v : Val rT => iprop(∃ ys : List ℕ,
          ⌜v = listVal (fun n : ℕ => Val.int n) ys⌝ ∗ ↯ (F ys))) := by
  induction rows generalizing F with
  | nil =>
    iintro Hcredit
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    iexists []
    isimp only [law, MeasureTheory.lintegral_dirac] at Hcredit
    iframe Hcredit
    ipureintro
    rfl
  | cons r rs ih =>
    let : NeZero r.val.sum := ⟨r.property.ne'⟩
    iintro Hcredit
    simp only [listVal]
    iterate 6 twp_pure
    have hnext := ih (fun ys => ∫⁻ j, F (j :: ys) ∂WeightedChoice.law r.val)
    simp [Occil.General.randomMap, Exp.close, Exp.closeRec] at hnext
    twp_bind_from hnext
    iapply tglWp_wand
    isplitl [Hcredit]
    · isimp only [← expectation r rs F] at Hcredit
      exact wand_entails hnext
    iintro %v ⟨%ys, %hv, Hcredit⟩
    subst v
    twp_pure
    twp_bind pl(&Occil.weightedChoice &(encodeRow r).fst)
    simp only [Exp.ofVal, encodeRow]
    iapply ((WeightedChoice.weightedChoice_distSpec E r.val).wp
      (fun j => F (j :: ys)) (measurable_of_countable _) _) $$ Hcredit
    iintro %j Hcredit
    twp_pures
    rw [encode_cons]
    iapply (tglWp_value (v := listVal (fun n : ℕ => Val.int n) (j :: ys)))
    iexists j :: ys
    iframe Hcredit
    ipureintro
    rfl

/-- The whole random mapping has the product of the normalized row laws. -/
theorem randomMap_distSpec (E : CoPset) (rows : List Row) :
    IsDistSpec (GF := GF) E pl(&Occil.General.randomMap &(listVal encodeRow rows).fst #())
      (law rows) (listVal (fun n : ℕ => Val.int n)) where
  spec F _ := wand_entails (twp_randomMap E rows F)

end specification

end

end SampLib.RandomMap
