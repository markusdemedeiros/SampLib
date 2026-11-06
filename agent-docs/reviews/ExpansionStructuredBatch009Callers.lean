import SampLib.Combinatorial.Derangement
import SampLib.General.MetropolisHastings
import SampLib.General.Metropolis
import SampLib.Weighted.Support.AliasTable
import SampLib.Core.ArrayVector

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

example {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (E : CoPset) (P : IProp GF) (μ : MeasureTheory.Measure α)
    [MeasureTheory.IsProbabilityMeasure μ] (encode : α → Val rT) (sample : Val rT)
    (hs : IsOwnedDistSpec E P pl(&sample.fst #()) μ encode) (n : ℕ)
    (F : (Fin n → α) → ℝ≥0∞) (R : IProp GF) :
    ⊢ P ∗ ↯ (∫⁻ ys, F ys ∂SampleWithReplacement.law μ n) ∗ R -∗
      tglWp E pl(&Occil.repeatSample &sample.fst #int (n : ℤ))
        (fun v : Val rT => iprop(∃ ys : Fin n → α,
          ⌜v = listVal encode (List.ofFn ys)⌝ ∗ P ∗ ↯ (F ys) ∗ R)) :=
  owned_frame (repeatSample_ownedDistSpec E P μ encode sample hs n)
    F (measurable_of_countable _) R

private def readSampler (l : Loc) : Val rT :=
  ⟨pl(fun u, !(#loc l)), .lam (by is_lc), by is_lc⟩

section integer_draws
variable [ProbLangDist.IsUniformInt rT]

private theorem read_owned (E : CoPset) (l : Loc) :
    IsOwnedDistSpec (GF := GF) E (appHeapFrag l (Val.int 7))
      pl(&(readSampler (rT := rT) l).fst #()) (MeasureTheory.Measure.dirac (7 : ℤ)) Val.int where
  spec F _ := by
    iintro ⟨Hheap, Hcredit⟩
    isimp only [MeasureTheory.lintegral_dirac] at Hcredit
    twp_pure
    iapply twp_load
    iframe Hheap
    iintro Hheap
    iexists (7 : ℤ)
    iframe Hheap Hcredit
    itrivial

example (E : CoPset) (l : Loc) (n : ℕ)
    (F : (Fin n → ℤ) → ℝ≥0∞) (R : IProp GF) :
    ⊢ appHeapFrag l (Val.int 7) ∗
      ↯ (∫⁻ ys, F ys ∂SampleWithReplacement.law (MeasureTheory.Measure.dirac (7 : ℤ)) n) ∗ R -∗
      tglWp E pl(&Occil.repeatSample &(readSampler (rT := rT) l).fst #int (n : ℤ))
        (fun v : Val rT => iprop(∃ ys : Fin n → ℤ,
          ⌜v = listVal Val.int (List.ofFn ys)⌝ ∗ appHeapFrag l (Val.int 7) ∗ ↯ (F ys) ∗ R)) :=
  owned_frame (repeatSample_ownedDistSpec E (appHeapFrag l (Val.int 7))
    (MeasureTheory.Measure.dirac (7 : ℤ)) Val.int (readSampler l) (read_owned E l) n)
    F (measurable_of_countable _) R

example (E : CoPset) (ws : List ℕ) [NeZero ws.sum]
    (t : AliasMass.Table ws.length ws.sum) (hm : ∀ i, t.mass i = ws.length * ws.get i)
    (probability aliases : Loc) (F : ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ AliasTable.owns t probability aliases ∗ (↯ (∫⁻ i, F i ∂WeightedChoice.law ws)) ∗ R -∗
      tglWp E pl(&Occil.WeightedVariants.voseDraw
        &(AliasTable.value ws.length ws.sum probability aliases).fst #())
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int i⌝ ∗
          AliasTable.owns t probability aliases ∗ ↯ (F i) ∗ R)) :=
  owned_frame (AliasTable.voseDraw_ownedDistSpec E ws (NeZero.pos ws.sum) t hm probability aliases)
    F (measurable_of_countable _) R

example {α : Type*} (E : CoPset) (l : Loc) {n : ℕ} (encode : α → Val rT)
    (a : Fin n → α) (i : Fin n) (x : α) (R : IProp GF) :
    ⊢ Array.owns l (List.ofFn (encode ∘ a)) ∗ R -∗
      tglWp E pl((#loc l +ₗ #int (i.val : ℤ)) ← &(encode x).fst)
        (fun v : Val rT => iprop(⌜v = Val.unit⌝ ∗
          Array.owns l (List.ofFn (encode ∘ Function.update a i x)) ∗ R)) := by
  iintro ⟨Harray, HR⟩
  iapply tglWp_wand
  isplitl [Harray]
  · iapply (Array.twp_store_vector E l encode a i x) $$ Harray
  iintro %v ⟨%hv, Harray⟩
  iframe Harray HR
  itrivial

example (E : CoPset) (n : ℕ) (hn : n ≠ 1)
    (F : Equiv.Perm (Fin n) → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ σ, F σ ∂DerangementLaw.law n hn) ∗ R -∗
      tglWp E pl(&Occil.derangement #int (n : ℤ))
        (fun v : Val rT => iprop(∃ σ : Equiv.Perm (Fin n),
          ⌜v = Derangement.output n σ⌝ ∗ ↯ (F σ) ∗ R)) :=
  frame (Derangement.derangement_distSpec E n hn) F (measurable_of_countable _) R

example {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]
    (E : CoPset) (w : α → ℕ) (p : MetropolisHastings.Proposal α)
    (encode : α → Val rT) (target proposal q : Val rT)
    (ht : ∀ x, ⊢ tglWp E pl(&target.fst &(encode x).fst)
      (fun v : Val rT => iprop(⌜v = Val.int (w x)⌝)))
    (hq : ∀ x y, ⊢ tglWp E pl(&q.fst &(encode x).fst &(encode y).fst)
      (fun v : Val rT => iprop(⌜v = Val.pair (Val.int (p.numerator x y))
        (Val.int (p.denominator x y))⌝)))
    (hp : ∀ x, IsDistSpec (GF := GF) E pl(&proposal.fst &(encode x).fst)
      (Metropolis.proposal (MetropolisHastings.stochastic p) x) encode)
    (n : ℕ) (x : α) (hx : 0 < w x) (F : α → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ z, F z ∂MetropolisHastings.law w p n x) ∗ R -∗
      tglWp E pl(&Occil.General.metropolisHastings &target.fst &proposal.fst &q.fst
        &(encode x).fst #int (n : ℤ))
        (fun v : Val rT => iprop(∃ z : α, ⌜v = encode z⌝ ∗ ↯ (F z) ∗ R)) :=
  frame (MetropolisHastings.metropolisHastings_distSpec E w p encode target proposal q
    ht hq hp n x hx) F (measurable_of_countable _) R

example {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]
    (E : CoPset) (w : α → ℕ) (p : Metropolis.Proposal α)
    (encode : α → Val rT) (target proposal : Val rT)
    (ht : ∀ x, ⊢ tglWp E pl(&target.fst &(encode x).fst)
      (fun v : Val rT => iprop(⌜v = Val.int (w x)⌝)))
    (hp : ∀ x, IsDistSpec (GF := GF) E pl(&proposal.fst &(encode x).fst)
      (Metropolis.proposal p x) encode)
    (n : ℕ) (x : α) (hx : 0 < w x) (F : α → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ z, F z ∂SymmetricMetropolis.law w p n x) ∗ R -∗
      tglWp E pl(&Occil.General.metropolis &target.fst &proposal.fst
        &(encode x).fst #int (n : ℤ))
        (fun v : Val rT => iprop(∃ z : α, ⌜v = encode z⌝ ∗ ↯ (F z) ∗ R)) :=
  frame (SymmetricMetropolis.metropolis_distSpec E w p encode target proposal ht hp n x hx)
    F (measurable_of_countable _) R

end integer_draws

example (E : CoPset) (target proposal q initial : Val rT)
    (F : Unit → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (F ()) ∗ R -∗ tglWp E
      pl(&Occil.General.metropolisHastings &target.fst &proposal.fst &q.fst &initial.fst #0)
      (fun v : Val rT => iprop(∃ u : Unit, ⌜v = initial⌝ ∗ ↯ (F u) ∗ R)) := by
  simpa using frame (MetropolisHastings.metropolisHastings_zero_distSpec E
    target proposal q initial) F (measurable_of_countable _) R

example (E : CoPset) (target proposal initial : Val rT)
    (F : Unit → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (F ()) ∗ R -∗ tglWp E
      pl(&Occil.General.metropolis &target.fst &proposal.fst &initial.fst #0)
      (fun v : Val rT => iprop(∃ u : Unit, ⌜v = initial⌝ ∗ ↯ (F u) ∗ R)) := by
  simpa using frame (SymmetricMetropolis.metropolis_zero_distSpec E target proposal initial)
    F (measurable_of_countable _) R

open MeasureTheory Equiv

example (n : ℕ) (hn : n ≠ 1) :
    (∫⁻ _ : Perm (Fin n), (∞ : ℝ≥0∞) ∂DerangementLaw.law n hn) = ∞ := by simp

example : DerangementLaw.law 0 (by decide) = Measure.dirac (Equiv.refl (Fin 0)) := by
  apply Measure.ext_of_lintegral
  intro F _
  have hF : F = fun _ => F (Equiv.refl (Fin 0)) :=
    funext (fun σ => congrArg F (Subsingleton.elim σ _))
  rw [hF]
  simp


private def doubleSwap : Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3

private theorem doubleSwap_good : doubleSwap ∈ derangements (Fin 4) := by
  intro i
  fin_cases i <;> decide

example : DerangementLaw.law 4 (by decide) {doubleSwap} = (9 : ℝ≥0∞)⁻¹ := by
  rw [DerangementLaw.law_singleton, ite_eq_left doubleSwap_good]
  have hc : numDerangements 4 = 9 := by decide
  norm_num [hc]

example : DerangementLaw.law 4 (by decide) {(1 : Perm (Fin 4))} = 0 := by
  have hbad : (1 : Perm (Fin 4)) ∉ derangements (Fin 4) := by
    intro h
    exact h 0 rfl
  simp [DerangementLaw.law_singleton, hbad]

example (F : Bool → ℝ≥0∞) :
    (∫⁻ b, F b ∂RealCoin.law (CappedRationalCoin.bias 0 2 (by decide) (by decide))) =
      F false := by
  simp [CappedRationalCoin.bias, RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf]

example (F : Bool → ℝ≥0∞) :
    (∫⁻ b, F b ∂RealCoin.law (CappedRationalCoin.bias 5 2 (by decide) (by decide))) =
      F true := by
  norm_num [CappedRationalCoin.bias, RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf]

private def flipProposal : MetropolisHastings.Proposal Bool where
  numerator x y := if y = !x then 1 else 0
  denominator _ _ := 1
  denominator_pos _ _ := by decide
  total x := by cases x <;> simp

private def zeroTarget (b : Bool) : ℕ := if b then 0 else 1

private theorem flip_proposal (x : Bool) :
    Metropolis.proposal (MetropolisHastings.stochastic flipProposal) x = Measure.dirac (!x) := by
  cases x <;> simp [Metropolis.proposal, MetropolisHastings.stochastic, flipProposal]

private theorem reject_zero : MetropolisHastings.kernel zeroTarget flipProposal false =
    Measure.dirac false := by
  rw [MetropolisHastings.kernel, Metropolis.kernel, flip_proposal,
    Measure.dirac_bind (measurable_of_countable _)]
  simp [Metropolis.selection, Metropolis.bias, Metropolis.acceptance, zeroTarget,
    MetropolisHastings.stochastic, flipProposal, RealCoin.pmf]

private theorem rejects_all (n : ℕ) : MetropolisHastings.law zeroTarget flipProposal n false =
    Measure.dirac false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (MetropolisHastings.kernel zeroTarget flipProposal false).bind
      (MetropolisHastings.law zeroTarget flipProposal n) = _
    rw [reject_zero, Measure.dirac_bind (measurable_of_countable _), ih]

example (n : ℕ) : (∫⁻ b, (if b then ∞ else 7 : ℝ≥0∞)
    ∂MetropolisHastings.law zeroTarget flipProposal n false) = 7 := by
  rw [rejects_all]
  simp

example {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]
    (w : α → ℕ) (p : MetropolisHastings.Proposal α) (h : 0 < ∑ x, w x) (n : ℕ) :
    (MetropolisHastings.target w h).bind (MetropolisHastings.law w p n) =
      MetropolisHastings.target w h := MetropolisHastings.invariant w p h n

example {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]
    (w : α → ℕ) (p : Metropolis.Proposal α) (hs : ∀ x y, p.mass x y = p.mass y x)
    (h : 0 < ∑ x, w x) (n : ℕ) :
    (SymmetricMetropolis.target w h).bind (SymmetricMetropolis.law w p n) =
      SymmetricMetropolis.target w h := SymmetricMetropolis.invariant w p hs h n

example {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]
    (w : α → ℕ) (p : MetropolisHastings.Proposal α) (n : ℕ) (x : α) :
    (∫⁻ _ : α, (∞ : ℝ≥0∞) ∂MetropolisHastings.law w p n x) = ∞ := by simp

private def aliasExample : AliasMass.Table 2 4 where
  threshold := ![2, 4]
  target := ![1, 1]
  threshold_le i := by fin_cases i <;> decide

private theorem alias_mass : ∀ i, aliasExample.mass i = ([1, 3] : List ℕ).length *
    ([1, 3] : List ℕ).get i := by
  intro i
  fin_cases i <;>
    norm_num [AliasMass.Table.mass, AliasMass.Table.incoming, aliasExample, Fin.sum_univ_two]

example : (∑ i : Fin 2, aliasExample.columnCredit (fun k => if k = 0 then 1 else 0) i) / 2 =
    (1 : ℝ≥0∞) / 4 := by
  have h := AliasMass.expectation [1, 3] (by decide) aliasExample alias_mass
    (fun k => if k = 0 then 1 else 0)
  simpa [WeightedChoice.lintegral_law, WeightedChoice.weightedSum] using h

example : (∑ i : Fin 2, aliasExample.columnCredit (fun k => if k = 2 then ∞ else 0) i) / 2 =
    (0 : ℝ≥0∞) := by
  have h := AliasMass.expectation [1, 3] (by decide) aliasExample alias_mass
    (fun k => if k = 2 then ∞ else 0)
  simpa [WeightedChoice.lintegral_law, WeightedChoice.weightedSum] using h

end
end ReviewExpansionStructured

#print axioms SampLib.Derangement.derangement_distSpec
#print axioms SampLib.DerangementLaw.law_singleton
#print axioms SampLib.Shuffle.shuffleVector_distSpec
#print axioms SampLib.MetropolisHastings.metropolisHastings_distSpec
#print axioms SampLib.MetropolisHastings.metropolisHastings_zero_distSpec
#print axioms SampLib.SymmetricMetropolis.metropolis_distSpec
#print axioms SampLib.SymmetricMetropolis.metropolis_zero_distSpec
#print axioms SampLib.Metropolis.accepted_flux
#print axioms SampLib.MetropolisHastings.invariant
#print axioms SampLib.SymmetricMetropolis.invariant
#print axioms SampLib.IsOwnedDistSpec.wp
#print axioms SampLib.repeatSample_ownedDistSpec
#print axioms SampLib.Array.twp_store_vector
#print axioms SampLib.AliasTable.voseDraw_ownedDistSpec
#print axioms SampLib.AliasMass.expectation
