import SampLib.Samplers.AliasSamples
import SampLib.Samplers.Bootstrap
import SampLib.Samplers.PermutationSamples
import SampLib.Samplers.LatinHypercube
import SampLib.Samplers.GroupedPermutation
import SampLib.Samplers.WeakComposition
import SampLib.BetaStep

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

example (E : CoPset) (F : (Fin 2 → Unit) → ℝ≥0∞) (R : IProp GF) :=
  frame (Bootstrap.bootstrap_empty_distSpec E (fun x : ℤ => (Val.int x : Val rT)) 2)
    F (measurable_of_countable _) R

local instance : NeZero ([7, 7] : List ℤ).length := ⟨by decide⟩

local instance : NeZero ([1, 0, 1] : List ℕ).sum := ⟨by decide⟩

section integer_draws
variable [ProbLangDist.IsUniformInt rT]

example (E : CoPset) (ws : List ℕ) [NeZero ws.sum] (n : ℕ)
    (F : (Fin n → ℕ) → ℝ≥0∞) (R : IProp GF) :=
  frame (AliasSamples.aliasSamples_distSpec E ws n) F (measurable_of_countable _) R

example (E : CoPset) (F : (Fin 2 → ℕ) → ℝ≥0∞) (R : IProp GF) :=
  frame (AliasSamples.aliasSamples_distSpec E [1, 0, 1] 2)
    F (measurable_of_countable _) R

example (E : CoPset) (F : (Fin 0 → ℕ) → ℝ≥0∞) (R : IProp GF) :=
  frame (AliasSamples.aliasSamples_distSpec E [1, 0, 1] 0)
    F (measurable_of_countable _) R

example (E : CoPset) (F : (Fin 2 → (Fin 2 → Fin 2)) → ℝ≥0∞) (R : IProp GF) :=
  frame (Bootstrap.bootstrap_distSpec E (fun x : ℤ => (Val.int x : Val rT)) [7, 7] 2)
    F (measurable_of_countable _) R

example (E : CoPset) (F : (Fin 0 → Equiv.Perm (Fin 0)) → ℝ≥0∞) (R : IProp GF) :=
  frame (PermutationSamples.permutationSamples_distSpec E
    (fun x : ℤ => (Val.int x : Val rT)) [] 0) F (measurable_of_countable _) R

example (E : CoPset) (F : List (List ℤ) → ℝ≥0∞) (R : IProp GF) :=
  frame (LatinHypercube.latinHypercube_distSpec E 1 1 2 (by decide) (by decide) (by decide))
    F (measurable_of_countable _) R

section grouped
local instance : MeasurableSpace (List (List ℤ)) := ⊤

example (E : CoPset) (F : List (List ℤ) → ℝ≥0∞) (R : IProp GF) :=
  frame (GroupedPermutation.groupedPermutation_distSpec E
    (fun x : ℤ => (Val.int x : Val rT)) [] [0, 0] (by decide))
    F (measurable_of_countable _) R

end grouped

section weak
local instance : MeasurableSpace (List ℤ) := ⊤

example (E : CoPset) (F : List ℤ → ℝ≥0∞) (R : IProp GF) :=
  frame (WeakComposition.weakComposition_distSpec E 3 0 (by decide))
    F (measurable_of_countable _) R

end weak

end integer_draws

open MeasureTheory
open scoped Classical

example : AliasSamples.law [1, 0, 1] 0 = Measure.dirac Fin.elim0 := rfl

example : (∫⁻ xs, (if List.ofFn xs = [0, 2] then 1 else 0 : ℝ≥0∞)
    ∂AliasSamples.law [1, 0, 1] 2) = 1 / 4 := by
  simp_rw [AliasSamples.law,
    SampleWithReplacement.lintegral_law_succ _ _ _ (measurable_of_countable _)]
  simp only [SampleWithReplacement.law, lintegral_dirac]
  simp_rw [WeightedChoice.lintegral_law]
  norm_num [WeightedChoice.weightedSum, List.ofFn_succ]
  rw [div_eq_mul_inv, ← ENNReal.mul_inv (by simp) (by simp)]
  norm_num

example : (∫⁻ xs, (if List.ofFn xs = [1, 1] then ∞ else 0 : ℝ≥0∞)
    ∂AliasSamples.law [1, 0, 1] 2) = 0 := by
  simp_rw [AliasSamples.law,
    SampleWithReplacement.lintegral_law_succ _ _ _ (measurable_of_countable _)]
  simp only [SampleWithReplacement.law, lintegral_dirac]
  simp_rw [WeightedChoice.lintegral_law]
  norm_num [WeightedChoice.weightedSum, List.ofFn_succ]

example (n : ℕ) :
    (∫⁻ _, (∞ : ℝ≥0∞) ∂AliasSamples.law [1, 0, 1] n) = ∞ := by simp

#print axioms SampLib.Bootstrap.bootstrap_distSpec
#print axioms SampLib.Bootstrap.bootstrap_empty_distSpec
#print axioms SampLib.PermutationSamples.permutationSamples_distSpec
#print axioms SampLib.LatinHypercube.latinHypercube_distSpec
#print axioms SampLib.GroupedPermutation.groupedPermutation_distSpec
#print axioms SampLib.WeakComposition.weakComposition_distSpec
#print axioms SampLib.AliasSamples.aliasSamples_distSpec
#print axioms SampLib.WalkerSetup.twp_setup
#print axioms SampLib.WalkerFind.twp_find
#print axioms SampLib.WalkerBalance.twp_prepare
#print axioms SampLib.WalkerDraw.draw_ownedDistSpec
#print axioms SampLib.WalkerAlias.State.pending_transfer_lt
#print axioms SampLib.WalkerAlias.State.valid_transfer
#print axioms SampLib.WalkerAlias.State.terminal_mass

end
end ReviewExpansionStructured

namespace ReviewNamedBeta

open ProbLang Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]
local bi (IProp GF)

example (E : CoPset) (K : Ectx rT) (body : Exp rT) (v : Val rT)
    (hc : (Exp.lam body).IsLocallyClosed) (Φ : Val rT → IProp GF) (R : IProp GF) :
    iprop(tglWp E (K.fill (Exp.open' body v.fst)) Φ ∗ R) ⊢
      tglWp E (K.fill (.app (.lam body) v.fst)) (fun w => iprop(Φ w ∗ R)) := by
  iintro ⟨Hbody, HR⟩
  iapply (SampLib.twp_beta E K body v hc _)
  iapply tglWp_wand
  isplitl [Hbody]
  · iexact Hbody
  iintro %w Hpost
  iframe Hpost HR

#print axioms SampLib.twp_beta

end ReviewNamedBeta
