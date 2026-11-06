import SampLib.General.PerfectFiniteChain
import SampLib.General.SliceSampler

open ProbLang
open scoped ENNReal

namespace ReviewExpansionStructured

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- A caller retains its own resource while spending the expected sampler credit. -/
theorem frame {α : Type _} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {E : CoPset} {e : Exp rT}
    {encode : α → Val rT} (h : IsDistSpec (GF := GF) E e μ encode)
    (F : α → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂μ) ∗ R -∗ tglWp E e
      (fun v : Val rT => iprop(∃ x : α, ⌜v = encode x⌝ ∗ ↯ (F x) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  iapply (h.wp F hF _) $$ Hcredit
  iintro %x Hcredit
  iexists x
  iframe Hcredit HR
  itrivial

open CouplingFromPast

private def climb : Map 3 := fun x => if x.val = 0 then 1 else 2

private theorem stationary_climb : Stationary (MeasureTheory.Measure.dirac climb)
    (MeasureTheory.Measure.dirac (2 : Fin 3)) := by
  unfold Stationary
  rw [MeasureTheory.Measure.dirac_bind (measurable_of_countable _) (2 : Fin 3)]
  unfold transition
  rw [MeasureTheory.Measure.map_dirac' (measurable_of_countable _)]
  rfl

private theorem coalescent_climb : ∃ L, 0 <
    (IIDList.law (MeasureTheory.Measure.dirac climb) L) {maps | Coalesces maps} := by
  refine ⟨2, ?_⟩
  have h : Coalesces [climb, climb] := by decide
  simpa [IIDList.law, MeasureTheory.Measure.dirac_prod_dirac,
    MeasureTheory.Measure.map_dirac' (measurable_of_countable _)] using
    (show (0 : ℝ≥0∞) < MeasureTheory.Measure.dirac [climb, climb]
      {maps | Coalesces maps} by
        rw [MeasureTheory.Measure.dirac_apply_of_mem
          (show [climb, climb] ∈ {maps : List (Map 3) | Coalesces maps} from h)]
        exact zero_lt_one)

private def climbRows : List MarkovChain.Row :=
  [⟨[0, 1, 0], by decide⟩, ⟨[0, 0, 1], by decide⟩, ⟨[0, 0, 1], by decide⟩]

private instance : NeZero climbRows.length := ⟨by decide⟩

private theorem categorical_one :
    WeightedChoice.law [0, 1, 0] = MeasureTheory.Measure.dirac 1 := by
  apply MeasureTheory.Measure.ext_of_lintegral
  intro F _
  simp [WeightedChoice.lintegral_law, WeightedChoice.weightedSum]

private theorem categorical_two :
    WeightedChoice.law [0, 0, 1] = MeasureTheory.Measure.dirac 2 := by
  apply MeasureTheory.Measure.ext_of_lintegral
  intro F _
  simp [WeightedChoice.lintegral_law, WeightedChoice.weightedSum]

private theorem climb_native : RandomMapSupport.law climbRows =
    MeasureTheory.Measure.dirac climb := by
  have hdecode : RandomMapSupport.decode 3 [1, 2, 2] = climb := by
    funext i
    fin_cases i <;> rfl
  simp only [RandomMapSupport.law, climbRows, RandomMap.law, categorical_one,
    categorical_two, MeasureTheory.Measure.dirac_prod_dirac]
  simp only [MeasureTheory.Measure.map_dirac' (measurable_of_countable _),
    MeasureTheory.Measure.dirac_prod_dirac]
  change (MeasureTheory.Measure.dirac [1, 2, 2]).map (RandomMapSupport.decode 3) = _
  rw [MeasureTheory.Measure.map_dirac' (measurable_of_countable _), hdecode]

private theorem climb_matrix_stationary :
    (MeasureTheory.Measure.dirac (2 : Fin climbRows.length)).bind
      (RandomMapSupport.kernel climbRows) = MeasureTheory.Measure.dirac 2 := by
  have hk : RandomMapSupport.kernel climbRows = transition (MeasureTheory.Measure.dirac climb) := by
    funext i
    rw [← RandomMapSupport.transition_eq_kernel, climb_native]
    rfl
  rw [hk]
  exact stationary_climb

private abbrev sampleClimb : Val rT :=
  ⟨.lam (mapVal climb).fst, .lam (by is_lc), by is_lc⟩

private theorem climb_spec (E : CoPset) : IsDistSpec (GF := GF) E
    pl(&(sampleClimb : Val rT).fst #()) (MeasureTheory.Measure.dirac climb) mapVal where
  spec F _ := by
    iintro Hcredit
    isimp only [MeasureTheory.lintegral_dirac] at Hcredit
    twp_pure
    iapply (tglWp_value_of_toVal (Val.toVal?_fst (mapVal climb)))
    iexists climb
    iframe Hcredit
    itrivial

example (E : CoPset) (F : Fin 3 → ℝ≥0∞) (R : IProp GF) :=
  frame (couplingFromPast_distSpec E (MeasureTheory.Measure.dirac climb)
    (MeasureTheory.Measure.dirac (2 : Fin 3)) stationary_climb coalescent_climb
    sampleClimb (climb_spec E)) F (measurable_of_countable _) R

example (E : CoPset) {n : ℕ} [NeZero n] (ρ : MeasureTheory.Measure (Map n))
    [MeasureTheory.IsProbabilityMeasure ρ] (π : MeasureTheory.Measure (Fin n))
    [MeasureTheory.IsProbabilityMeasure π] (hπ : Stationary ρ π)
    (hc : ∃ L, 0 < (IIDList.law ρ L) {maps | Coalesces maps}) (sample : Val rT)
    (hs : IsDistSpec (GF := GF) E pl(&sample.fst #()) ρ mapVal)
    (F : Fin n → ℝ≥0∞) (R : IProp GF) :=
  frame (couplingFromPast_distSpec E ρ π hπ hc sample hs) F (measurable_of_countable _) R

example (E : CoPset) (density lower upper initial : Val rT)
    (F : Unit → ℝ≥0∞) (R : IProp GF) :=
  frame (SliceSampler.sliceSampler_zero_distSpec E density lower upper initial)
    F (measurable_of_countable _) R

section integer_draws
variable [ProbLangDist.IsUniformInt rT]

example (E : CoPset) (rows : List MarkovChain.Row) [NeZero rows.length]
    (hs : ∀ r ∈ rows, r.val.length = rows.length)
    (π : MeasureTheory.Measure (Fin rows.length)) [MeasureTheory.IsProbabilityMeasure π]
    (hp : π.bind (RandomMapSupport.kernel rows) = π)
    (hc : ∃ L, 0 < (IIDList.law (RandomMapSupport.law rows) L)
      {maps | Coalesces maps}) (F : Fin rows.length → ℝ≥0∞) (R : IProp GF) :=
  frame (PerfectFiniteChain.perfectFiniteChain_distSpec E rows hs π hp hc)
    F (measurable_of_countable _) R

example (E : CoPset) (density initial : Val rT) (lower : ℤ) (width : ℕ) [NeZero width]
    (w : Fin width → ℕ) (cap : ℕ) (hp : 0 < cap) (ha : ∃ i, cap ≤ w i)
    (hinit : ⊢ tglWp E pl(&density.fst &initial.fst)
      (fun v : Val rT => iprop(⌜v = Val.int cap⌝)))
    (hd : ∀ i, ⊢ tglWp E pl(&density.fst &(SliceStep.encode lower i).fst)
      (fun v : Val rT => iprop(⌜v = Val.int (w i)⌝)))
    (n : ℕ) (F : Fin width → ℝ≥0∞) (R : IProp GF) :=
  frame (SliceSampler.sliceSampler_start_distSpec E density initial lower width w cap hp ha
    hinit hd n) F (measurable_of_countable _) R

example (E : CoPset) (F : Fin 3 → ℝ≥0∞) (R : IProp GF) := by
  have hs : ∀ r ∈ climbRows, r.val.length = climbRows.length := by
    intro r hr
    simp only [climbRows, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rfl
  have hc : ∃ L, 0 < (IIDList.law (RandomMapSupport.law climbRows) L)
      {maps | Coalesces maps} := by
    rw [climb_native]
    exact coalescent_climb
  exact frame (PerfectFiniteChain.perfectFiniteChain_distSpec E climbRows hs
    (MeasureTheory.Measure.dirac (⟨2, by decide⟩ : Fin climbRows.length))
    climb_matrix_stationary hc)
    F (measurable_of_countable _) R

end integer_draws

open MeasureTheory
open scoped Classical

example : ¬Coalesces [climb] := by decide
example : Coalesces [climb, climb] := by decide
example : (∫⁻ x : Fin 3, (if x = 2 then 7 else ∞ : ℝ≥0∞)
    ∂Measure.dirac (2 : Fin 3)) = 7 := by simp

private def sparse : Fin 3 → ℕ := ![0, 1, 2]

example : SliceLaw.level sparse 0 = {1, 2} := by decide
example : SliceLaw.level sparse 1 = {2} := by decide

example : SliceLaw.stepLaw sparse 2 (by decide) ⟨2, by decide⟩ {1} = 1 / 4 := by
  rw [SliceLaw.stepLaw, SliceLaw.heightMixture_singleton]
  have hlevel : SliceLaw.level sparse 0 = {1, 2} := by decide
  norm_num [sparse, Finset.sum_range_succ, hlevel]
  rw [div_eq_mul_inv, ← ENNReal.mul_inv (by simp) (by simp)]
  norm_num
  change ((SliceLaw.level sparse 0).card : ℝ≥0∞) * 2 = 4
  rw [hlevel]
  norm_num

example : (∫⁻ x : Fin 3, (if x = 0 then ∞ else 0 : ℝ≥0∞)
    ∂SliceLaw.stepLaw sparse 2 (by decide) ⟨2, by decide⟩) = 0 := by
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [SliceLaw.heightMixture_ae_positive sparse 2] with x hx
  have hne : x ≠ 0 := by intro h; subst x; norm_num [sparse] at hx
  simp [hne]

example (n : ℕ) : (SliceLaw.target sparse (by decide)).bind (SliceLaw.law sparse n) =
    SliceLaw.target sparse (by decide) := SliceLaw.iterate_invariant sparse (by decide) n

example : SliceLaw.heightMixture sparse 0 = 0 := by simp [SliceLaw.heightMixture]

#print axioms SampLib.CouplingFromPast.couplingFromPast_distSpec
#print axioms SampLib.PerfectFiniteChain.perfectFiniteChain_distSpec
#print axioms SampLib.CouplingFromPast.expectation
#print axioms SampLib.CouplingFromPast.Block.amplified_drift
#print axioms ErrorCredit.Induction.weighted
#print axioms SampLib.RandomMapSupport.typedRandomMap_distSpec
#print axioms SampLib.SliceSampler.sliceSampler_distSpec
#print axioms SampLib.SliceSampler.sliceSampler_start_distSpec
#print axioms SampLib.SliceSampler.sliceSampler_zero_distSpec
#print axioms SampLib.SliceStep.sliceStep_distSpec
#print axioms SampLib.SliceLaw.weighted_flux
#print axioms SampLib.SliceLaw.iterate_invariant

end
end ReviewExpansionStructured
