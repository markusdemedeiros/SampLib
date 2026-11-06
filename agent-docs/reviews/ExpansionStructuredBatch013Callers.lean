import SampLib.Syntax.Fenwick
import SampLib.Samplers.FenwickDraw
import SampLib.NewFenwick
import SampLib.FenwickSet
import SampLib.Samplers.CountableMetropolisHastings
import SampLib.Samplers.CountableMetropolis
import SampLib.LowBit
import SampLib.FenwickCategory
import SampLib.Distributions.FenwickSearch
import SampLib.PiBounds

open ProbLang
open scoped ENNReal

namespace ReviewExpansionStructured

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

open FenwickSyntax

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

/-- Private sampler ownership and an unrelated caller resource both survive. -/
theorem owned_frame {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
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

section integer_draws
variable [ProbLangDist.IsUniformInt rT]

example (E : CoPset) {n : ℕ} (w : Fin n → ℕ) [NeZero (List.ofFn w).sum]
    (total values tree : Loc) (F : ℕ → ℝ≥0∞) (R : IProp GF) :=
  owned_frame (FenwickDraw.fenwickDraw_ownedDistSpec E w total values tree)
    F (measurable_of_countable _) R

/-- A concrete allocation and draw exhibits an inhabited owned representation. -/
theorem new_then_draw (E : CoPset) (ws : List ℕ) [NeZero ws.sum]
    (F : ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law ws) ∗ R -∗
      tglWp E pl(let table := &Occil.WeightedVariants.newFenwick
        &(listVal FenwickTable.natVal ws).fst;
        &Occil.WeightedVariants.fenwickDraw table #())
        (fun v : Val rT => iprop(∃ total values tree : Loc, ∃ i : ℕ,
          ⌜v = FenwickTable.natVal i⌝ ∗ FenwickTable.owns ws.get total values tree ∗
            ↯ (F i) ∗ R)) := by
  let : NeZero (List.ofFn ws.get).sum :=
    ⟨by simpa only [List.ofFn_get] using NeZero.ne ws.sum⟩
  iintro ⟨Hcredit, HR⟩
  twp_bind pl(&Occil.WeightedVariants.newFenwick &(listVal FenwickTable.natVal ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply NewFenwick.twp_newFenwick E ws (NeZero.pos ws.sum)
  iintro %v ⟨%total, %values, %tree, %hv, Htable⟩
  subst v
  have hdraw := FenwickDraw.fenwickDraw_ownedDistSpec (GF := GF) E ws.get total values tree
  simp only [List.ofFn_get] at hdraw
  twp_pure
  simp only [fenwickDraw_closeRec, fenwickDraw_openRec]
  iapply (hdraw.wp F (measurable_of_countable _) _) $$ Htable Hcredit
  iintro %i Htable Hcredit
  iexists total, values, tree, i
  iframe Htable Hcredit HR
  itrivial

/-- A sampled category can be followed by a real read of the unchanged total cell. -/
theorem draw_then_total (E : CoPset) {n : ℕ} (w : Fin n → ℕ)
    [NeZero (List.ofFn w).sum] (total values tree : Loc) (F : ℕ → ℝ≥0∞) :
    ⊢ FenwickTable.owns w total values tree -∗
      ↯ (∫⁻ i, F i ∂WeightedChoice.law (List.ofFn w)) -∗
      tglWp E pl(let category := &Occil.WeightedVariants.fenwickDraw
        &(FenwickTable.value n total values tree).fst #(); (category, !#loc total))
        (fun v : Val rT => iprop(∃ i : ℕ,
          ⌜v = Val.pair (FenwickTable.natVal i)
            (FenwickTable.natVal (List.ofFn w).sum)⌝ ∗
          FenwickTable.owns w total values tree ∗ ↯ (F i))) := by
  iintro Htable Hcredit
  twp_bind pl(&Occil.WeightedVariants.fenwickDraw
    &(FenwickTable.value n total values tree).fst #())
  iapply ((FenwickDraw.fenwickDraw_ownedDistSpec E w total values tree).wp
    F (measurable_of_countable _) _) $$ Htable Hcredit
  iintro %i Htable Hcredit
  isimp only [FenwickTable.owns] at Htable
  ihave ⟨Htotal, Hvalues, Htree⟩ := Htable
  twp_pure
  twp_bind pl(!#loc total)
  iapply twp_load
  iframe Htotal
  iintro Htotal
  twp_value
  imodintro
  iexists i
  isimp only [FenwickTable.owns]
  iframe Htotal Hvalues Htree Hcredit
  ipureintro
  exact Val.ext rfl

local instance : NeZero ([0, 2, 0, 3, 0] : List ℕ).sum := ⟨by decide⟩

example (E : CoPset) (F : ℕ → ℝ≥0∞) (R : IProp GF) :=
  new_then_draw E [0, 2, 0, 3, 0] F R

private def draw (n : ℕ) (total values tree : Loc) : Val rT :=
  ⟨.lam (.app (.app Occil.WeightedVariants.fenwickDraw
    (FenwickTable.value n total values tree).fst) (.lit .unit)),
    .lam (by is_lc), by is_lc⟩

private theorem draw_spec (E : CoPset) {n : ℕ} (w : Fin n → ℕ)
    [NeZero (List.ofFn w).sum] (total values tree : Loc) :
    IsOwnedDistSpec (GF := GF) E (FenwickTable.owns w total values tree)
      pl(&(draw n total values tree).fst #())
      (WeightedChoice.law (List.ofFn w)) FenwickTable.natVal where
  spec F hF := by
    iintro Hinput
    twp_pure
    simp only [fenwickDraw_openRec]
    iapply (FenwickDraw.fenwickDraw_ownedDistSpec E w total values tree).spec F hF $$ Hinput

example (E : CoPset) {n : ℕ} (w : Fin n → ℕ) [NeZero (List.ofFn w).sum]
    (total values tree : Loc) (count : ℕ) (F : (Fin count → ℕ) → ℝ≥0∞) (R : IProp GF) :=
  owned_frame (repeatSample_ownedDistSpec (GF := GF) E
    (FenwickTable.owns w total values tree) (WeightedChoice.law (List.ofFn w))
    FenwickTable.natVal (draw n total values tree) (draw_spec E w total values tree) count)
    F (measurable_of_countable _) R

example (E : CoPset) (total values tree : Loc) :
    FenwickTable.owns (fun _ : Fin 1 => 7) total values tree ⊢
      tglWp E pl(&Occil.WeightedVariants.fenwickSet
        &(FenwickTable.value 1 total values tree).fst #0 #0)
        (fun v : Val rT => iprop(⌜v = Val.unit⌝ ∗
          FenwickTable.owns (fun _ : Fin 1 => 0) total values tree)) := by
  have h := FenwickSet.twp_fenwickSet (rT := rT) (GF := GF) E
    (fun _ : Fin 1 => 7) total values tree 0 0
  have hu : Function.update (fun _ : Fin 1 => 7) 0 0 = fun _ => 0 := by
    funext i
    fin_cases i
    rfl
  simpa only [hu, Fin.val_zero, Nat.cast_zero] using h

/-- Setting the last positive weight to zero leaves a valid, inhabited table. -/
example (E : CoPset) :
    ⊢ tglWp E pl(let table := &Occil.WeightedVariants.newFenwick
        &(listVal FenwickTable.natVal [7]).fst;
        &Occil.WeightedVariants.fenwickSet table #0 #0)
        (fun v : Val rT => iprop(∃ total values tree : Loc,
          ⌜v = Val.unit⌝ ∗ FenwickTable.owns (fun _ : Fin 1 => 0) total values tree)) := by
  have hget : ([7] : List ℕ).get = fun _ : Fin 1 => 7 := by
    funext i
    fin_cases i
    rfl
  have hupdate : Function.update (fun _ : Fin 1 => 7) 0 0 = fun _ => 0 := by
    funext i
    fin_cases i
    rfl
  twp_bind pl(&Occil.WeightedVariants.newFenwick &(listVal FenwickTable.natVal [7]).fst)
  iapply tglWp_wand
  isplitl []
  · iapply NewFenwick.twp_newFenwick E [7] (by decide)
  iintro %v ⟨%total, %values, %tree, %hv, Htable⟩
  subst v
  isimp only [hget] at Htable
  have hset := FenwickSet.twp_fenwickSet (rT := rT) (GF := GF) E
    (fun _ : Fin 1 => 7) total values tree 0 0
  simp only [hupdate, Fin.val_zero, Nat.cast_zero] at hset
  twp_pure
  simp only [fenwickSet_closeRec, fenwickSet_openRec]
  iapply tglWp_wand
  isplitl [Htable]
  · iapply hset $$ Htable
  iintro %v ⟨%hv, Htable⟩
  iexists total, values, tree
  iframe %hv Htable

end integer_draws

example : (∫⁻ i, (if i = 0 ∨ i = 2 ∨ i = 4 then ∞ else 0 : ℝ≥0∞)
    ∂WeightedChoice.law [0, 2, 0, 3, 0]) = 0 := by
  rw [WeightedChoice.lintegral_law]
  norm_num [WeightedChoice.weightedSum]

#print axioms SampLib.FenwickDraw.fenwickDraw_ownedDistSpec
#print axioms SampLib.NewFenwick.twp_newFenwick
#print axioms SampLib.FenwickSet.twp_fenwickSet
#print axioms SampLib.FenwickPropagation.twp_add
#print axioms SampLib.FenwickPropagation.twp_replace
#print axioms SampLib.Array.twp_store_vector_loc

end
end ReviewExpansionStructured

open ProbLang
open scoped ENNReal

namespace ReviewCountableExtensions

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

private theorem int_test {rT : Type _} [BEq rT] (x y : ℕ) :
    ((BaseLit.int ((x : ℤ) + 1) : BaseLit rT) == .int (y : ℤ)) = decide (x + 1 = y) := by
  change (((x : ℤ) + 1) == (y : ℤ)) = _
  rw [Bool.beq_eq_decide_eq]
  simp only [← Nat.cast_add_one, Int.natCast_inj]

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

private def natEncode (n : ℕ) : Val rT := .int n

private def targetValue : Val rT := ⟨pl(fun x, #1), .lam (by is_lc), by is_lc⟩
private def shiftValue : Val rT := ⟨pl(fun x, x + #1), .lam (by is_lc), by is_lc⟩
private def ratioValue : Val rT :=
  ⟨pl(fun x y, if x + #1 = y then (#1, #1) else (#0, #1)),
    .lam (by is_lc), by is_lc⟩

private def shiftProposal : CountableMetropolisHastings.Proposal ℕ where
  numerator x y := if x + 1 = y then 1 else 0
  denominator _ _ := 1
  denominator_pos _ _ := zero_lt_one
  measure x := MeasureTheory.Measure.dirac (x + 1)
  probability _ := inferInstance
  singleton x y := by simp [Pi.single_apply, eq_comm]

private theorem target_spec (E : CoPset) (x : ℕ) :
    ⊢ tglWp E pl(&(targetValue : Val rT).fst &(natEncode x).fst)
      (fun v : Val rT => iprop(⌜v = Val.int 1⌝)) := by
  twp_pures
  twp_value
  imodintro
  itrivial

private theorem shift_spec (E : CoPset) (x : ℕ) :
    IsDistSpec (GF := GF) E pl(&(shiftValue : Val rT).fst &(natEncode x).fst)
      (MeasureTheory.Measure.dirac (x + 1)) natEncode where
  spec F _ := by
    iintro Hcredit
    isimp only [MeasureTheory.lintegral_dirac] at Hcredit
    twp_pures
    twp_value
    imodintro
    iexists x + 1
    iframe Hcredit
    ipureintro
    apply Val.ext
    simp [natEncode, Nat.cast_add_one]

private theorem ratio_spec (E : CoPset) (x y : ℕ) :
    ⊢ tglWp E pl(&(ratioValue : Val rT).fst &(natEncode x).fst &(natEncode y).fst)
      (fun v : Val rT => iprop(⌜v = Val.pair (Val.int (shiftProposal.numerator x y))
        (Val.int (shiftProposal.denominator x y))⌝)) := by
  twp_pures
  rw [int_test]
  by_cases h : x + 1 = y
  · rw [decide_eq_true h]
    twp_pures
    twp_value
    imodintro
    ipureintro
    simp [shiftProposal, h]
  · rw [decide_eq_false h]
    twp_pures
    twp_value
    imodintro
    ipureintro
    simp [shiftProposal, h]

example (E : CoPset) (target proposal q initial : Val rT)
    (F : Unit → ℝ≥0∞) (R : IProp GF) :=
  frame (CountableMetropolisHastings.metropolisHastings_zero_distSpec E
    target proposal q initial) F (measurable_of_countable _) R

example (E : CoPset) (target proposal initial : Val rT)
    (F : Unit → ℝ≥0∞) (R : IProp GF) :=
  frame (CountableMetropolis.metropolis_zero_distSpec E target proposal initial)
    F (measurable_of_countable _) R

section integer_draws
variable [ProbLangDist.IsUniformInt rT]

example {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (E : CoPset) (w : α → ℕ) (p : CountableMetropolisHastings.Proposal α)
    (encode : α → Val rT) (target proposal q : Val rT)
    (ht : ∀ x, ⊢ tglWp E pl(&target.fst &(encode x).fst)
      (fun v : Val rT => iprop(⌜v = Val.int (w x)⌝)))
    (hq : ∀ x y, ⊢ tglWp E pl(&q.fst &(encode x).fst &(encode y).fst)
      (fun v : Val rT => iprop(⌜v = Val.pair (Val.int (p.numerator x y))
        (Val.int (p.denominator x y))⌝)))
    (hp : ∀ x, IsDistSpec (GF := GF) E pl(&proposal.fst &(encode x).fst) (p.measure x) encode)
    (n : ℕ) (x : α) (hx : 0 < w x) (F : α → ℝ≥0∞) (R : IProp GF) :=
  frame (CountableMetropolisHastings.metropolisHastings_distSpec E w p encode
    target proposal q ht hq hp n x hx) F (measurable_of_countable _) R

example {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (E : CoPset) (w : α → ℕ) (μ : α → MeasureTheory.Measure α)
    [∀ x, MeasureTheory.IsProbabilityMeasure (μ x)]
    (encode : α → Val rT) (target proposal : Val rT)
    (ht : ∀ x, ⊢ tglWp E pl(&target.fst &(encode x).fst)
      (fun v : Val rT => iprop(⌜v = Val.int (w x)⌝)))
    (hp : ∀ x, IsDistSpec (GF := GF) E pl(&proposal.fst &(encode x).fst) (μ x) encode)
    (n : ℕ) (x : α) (hx : 0 < w x) (F : α → ℝ≥0∞) (R : IProp GF) :=
  frame (CountableMetropolis.metropolis_distSpec E w μ encode target proposal ht hp n x hx)
    F (measurable_of_countable _) R

example (E : CoPset) (n x : ℕ) (F : ℕ → ℝ≥0∞) (R : IProp GF) :=
  frame (CountableMetropolisHastings.metropolisHastings_distSpec E (fun _ => 1)
    shiftProposal natEncode targetValue shiftValue ratioValue (target_spec E)
    (ratio_spec E) (shift_spec E) n x zero_lt_one) F (measurable_of_countable _) R

example (E : CoPset) (n x : ℕ) (F : ℕ → ℝ≥0∞) (R : IProp GF) :=
  frame (CountableMetropolis.metropolis_distSpec E (fun _ : ℕ => 1)
    (fun x => MeasureTheory.Measure.dirac (x + 1)) natEncode targetValue shiftValue
    (target_spec E) (shift_spec E) n x zero_lt_one) F (measurable_of_countable _) R

end integer_draws

open MeasureTheory

private theorem rejects (x : ℕ) :
    MetropolisRatio.kernel (fun _ => 1) shiftProposal.toRatios shiftProposal.measure x =
      Measure.dirac x := by
  have hreverse : x + 1 + 1 ≠ x := by omega
  simp [MetropolisRatio.kernel, shiftProposal,
    Measure.dirac_bind (measurable_of_countable _), MetropolisRatio.selection,
    Metropolis.bias, Metropolis.acceptance, MetropolisRatio.weight, RealCoin.pmf, hreverse]

private theorem advances (x : ℕ) :
    MetropolisRatio.kernel (fun _ : ℕ => 1) CountableMetropolis.ratios
      (fun y => Measure.dirac (y + 1)) x = Measure.dirac (x + 1) := by
  simp [MetropolisRatio.kernel, Measure.dirac_bind (measurable_of_countable _),
    MetropolisRatio.selection, CountableMetropolis.ratios, MetropolisRatio.weight,
    Metropolis.bias, Metropolis.acceptance, RealCoin.pmf]

private theorem mh_stays (n x : ℕ) :
    CountableMetropolisHastings.law (fun _ => 1) shiftProposal n x = Measure.dirac x := by
  induction n with
  | zero => rfl
  | succ n IH =>
    change (MetropolisRatio.kernel (fun _ => 1) shiftProposal.toRatios shiftProposal.measure x).bind
      (CountableMetropolisHastings.law (fun _ => 1) shiftProposal n) = _
    rw [rejects, Measure.dirac_bind (measurable_of_countable _), IH]

private theorem metro_advances (n x : ℕ) : CountableMetropolis.law (fun _ => 1)
    (fun y => Measure.dirac (y + 1)) n x = Measure.dirac (x + n) := by
  induction n generalizing x with
  | zero => rfl
  | succ n IH =>
    change (MetropolisRatio.kernel (fun _ : ℕ => 1) CountableMetropolis.ratios
      (fun y => Measure.dirac (y + 1)) x).bind
      (CountableMetropolis.law (fun _ => 1) (fun y => Measure.dirac (y + 1)) n) = _
    rw [advances, Measure.dirac_bind (measurable_of_countable _), IH]
    congr 1
    omega

example (n x : ℕ) : (∫⁻ y, (if y = x then 7 else ∞ : ℝ≥0∞)
    ∂CountableMetropolisHastings.law (fun _ => 1) shiftProposal n x) = 7 := by
  rw [mh_stays]
  simp

example (n x : ℕ) : (∫⁻ y, (if y = x + n then 7 else ∞ : ℝ≥0∞)
    ∂CountableMetropolis.law (fun _ => 1) (fun y => Measure.dirac (y + 1)) n x) = 7 := by
  rw [metro_advances]
  simp

#print axioms mh_stays
#print axioms metro_advances
#print axioms SampLib.CountableMetropolisHastings.metropolisHastings_distSpec
#print axioms SampLib.CountableMetropolis.metropolis_distSpec
#print axioms SampLib.CountableMetropolisHastings.proposal_support
#print axioms SampLib.CountableMetropolisHastings.metropolisHastings_zero_distSpec
#print axioms SampLib.CountableMetropolis.metropolis_zero_distSpec

end
end ReviewCountableExtensions

open ProbLang

namespace ReviewFenwickSupport

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example (E : CoPset) (n : ℕ) (hn : 0 < n) (R : IProp GF) :
    ⊢ R -∗ tglWp E pl(&Occil.WeightedVariants.lowBit #int (n : ℤ))
      (fun v => iprop(⌜v = Val.int (FenwickMath.lowBit n)⌝ ∗ R)) := by
  iintro HR
  iapply tglWp_wand
  isplitl []
  · iapply SampLib.LowBit.twp_lowBit E n hn
  iintro %v %hv
  iframe %hv HR

open FenwickMath
private def weights : Fin 5 → ℕ := ![0, 2, 0, 3, 0]

private theorem univ_five : (Finset.univ : Finset (Fin 5)) = {0, 1, 2, 3, 4} := by decide
private theorem bit_two : lowBit 2 = 2 := lowBit_aligned (i := 0) (a := 1) (by decide)
private theorem bit_three : lowBit 3 = 1 := lowBit_odd 1
private theorem bit_four : lowBit 4 = 4 := lowBit_aligned (i := 0) (a := 2) (by decide)
private theorem bit_five : lowBit 5 = 1 := lowBit_odd 2

example : lowBit 12 = 4 := lowBit_aligned (i := 8) (a := 2) (by decide)

private theorem cell_two : cell weights 2 = 2 := by
  norm_num [cell, interval, bit_two, weights, univ_five,
    Finset.filter_insert, Finset.filter_singleton]
private theorem cell_three : cell weights 3 = 0 := by
  norm_num [cell, interval, bit_three, weights, univ_five,
    Finset.filter_insert, Finset.filter_singleton]
private theorem cell_four : cell weights 4 = 5 := by
  norm_num [cell, interval, bit_four, weights, univ_five,
    Finset.filter_insert, Finset.filter_singleton]
example : cell weights 5 = 0 := by
  norm_num [cell, interval, bit_five, weights, univ_five,
    Finset.filter_insert, Finset.filter_singleton]

example : (cell (Function.update weights 1 0) 4 : ℤ) = 3 := by
  rw [cell_update_int]
  rw [cell_four]
  norm_num [contains, bit_four, weights]
example : (cell (Function.update weights 1 0) 2 : ℤ) = (cell weights 2 : ℤ) - 2 := by
  rw [cell_update_int]
  rw [cell_two]
  norm_num [contains, bit_two, weights]
example : (cell (Function.update weights 1 0) 3 : ℤ) = cell weights 3 := by
  rw [cell_update_int]
  rw [cell_three]
  norm_num [contains, bit_three, weights]

private theorem selected : Selects weights 2 3 := by
  norm_num [Selects, prefixSum, weights, univ_five,
    Finset.filter_insert, Finset.filter_singleton]

example : SearchInvariant weights 2 3 0 3 0 := by
  have h0 : SearchInvariant weights 2 3 8 0 2 :=
    SearchInvariant.initial weights selected ⟨3, rfl⟩ (by decide)
  have h1 : SearchInvariant weights 2 3 4 0 2 :=
    h0.skip selected (by decide) (by decide)
  have h2 : SearchInvariant weights 2 3 2 0 2 :=
    h1.stay selected (by decide) (by norm_num [cell_four])
  have h3 : SearchInvariant weights 2 3 1 2 0 := by
    simpa only [Nat.zero_add, cell_two, Nat.reduceSub] using
      h2.advance selected (by decide) (by norm_num [cell_two])
  simpa only [Nat.reduceAdd, cell_three, Nat.sub_zero] using
    h3.advance selected (by decide) (by norm_num [cell_three])

example : SampLib.WeightedChoice.category (List.ofFn weights) 2 = 3 := by decide

#print axioms SampLib.LowBit.twp_lowBit
#print axioms FenwickMath.cell_update_int
#print axioms FenwickMath.exists_selects
#print axioms FenwickMath.selects_unique
#print axioms FenwickMath.SearchInvariant.advance
#print axioms FenwickMath.SearchInvariant.stay
#print axioms SampLib.FenwickCategory.category_selects

end ReviewFenwickSupport

open ProbLang
namespace ReviewPiBoundsSupport
open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Deterministic gateways retain arbitrary caller resources and need no random primitive. -/
theorem pure_frame {E : CoPset} {e : Exp rT} {result : Val rT}
    (h : ⊢ tglWp E e (fun v => iprop(⌜v = result⌝))) (R : IProp GF) :
    ⊢ R -∗ tglWp E e (fun v => iprop(⌜v = result⌝ ∗ R)) := by
  iintro HR
  iapply tglWp_wand
  isplitl []
  · iapply h
  iintro %v %hv
  iframe %hv HR

example (E : CoPset) (q n : ℕ) (hq : 2 ≤ q) (hn : 1 ≤ n) (R : IProp GF) :=
  pure_frame (SampLib.PiBounds.twp_arctanReciprocalBounds E q n hq hn) R

example (E : CoPset) (n : ℕ) (R : IProp GF) :=
  pure_frame (SampLib.PiBounds.twp_piBounds E n) R

example (E : CoPset) : ⊢ tglWp E pl(&Occil.Constants.arctanReciprocalBounds #2 #1)
    (fun v : Val rT => iprop(⌜v = SampLib.PiBounds.encodeTriple (22, (24, 48))⌝)) := by
  simpa [SampLib.PiBounds.arctanRaw, SampLib.PiBounds.numerator,
    SampLib.PiBounds.denominator, SampLib.PiBounds.termDenominator, SampLib.PiBounds.sign]
    using SampLib.PiBounds.twp_arctanReciprocalBounds (rT := rT) (GF := GF) E 2 1
      (by decide) (by decide)

example : SampLib.PiBounds.arctanRaw 2 1 = (22, (24, 48)) := by
  norm_num [SampLib.PiBounds.arctanRaw, SampLib.PiBounds.numerator,
    SampLib.PiBounds.denominator, SampLib.PiBounds.termDenominator, SampLib.PiBounds.sign]

example : SampLib.PiBounds.arctanRaw 2 2 = (3520, (3568, 7680)) := by
  norm_num [SampLib.PiBounds.arctanRaw, SampLib.PiBounds.numerator,
    SampLib.PiBounds.denominator, SampLib.PiBounds.termDenominator, SampLib.PiBounds.sign]

example : 0 < (SampLib.PiBounds.piRaw 0).2.2 := SampLib.PiBounds.piRaw_den_pos 0

#print axioms SampLib.PiBounds.twp_arctanReciprocalBounds
#print axioms SampLib.PiBounds.twp_piBounds
#print axioms SampLib.PiBounds.piRaw_den_pos


end ReviewPiBoundsSupport
