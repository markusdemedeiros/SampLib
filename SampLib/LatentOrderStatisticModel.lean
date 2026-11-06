import SampLib.UniformVector
import SampLib.LatentUniformRepresentation
import SampLib.Distributions.UniformOrderStatisticLaw

/-! # A selected rank in one owned uniform world

The posterior retains every coordinate. Once construction chooses a physical
handle, refinement preserves its identity and the entire family of aliases.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal.OrderStatistic

noncomputable section

/-- Physical handles become fixed when the constructor returns. -/
structure State (n : ℕ) where
  prefixes : Fin n → List Bool
  selected : Option ((Fin n → Loc) × Fin n)

/-- Before construction no coordinate has been selected. -/
def initial (n : ℕ) : State n := ⟨fun _ => [], none⟩

/-- Observations reveal more digits without changing any returned alias. -/
def Refines {n : ℕ} (s t : State n) : Prop :=
  UniformVector.Refines s.prefixes t.prefixes ∧
    (s.selected = none ∨ s.selected = t.selected)

section mathematics

open MeasureTheory

/-- The value is the canonical rank of the entire shared uniform vector. -/
def model (n k : ℕ) (hk : 0 < k ∧ k ≤ n) : Model (Fin n → ℝ) (State n) where
  posterior s := UniformVector.law s.prefixes
  probability _ := inferInstance
  value := UniformOrderStatistic.rank n k hk
  measurable_value := UniformOrderStatistic.measurable_rank n k hk
  refines := Refines
  refines_refl s := ⟨fun _ => List.prefix_refl _, Or.inr rfl⟩
  refines_trans hst htu := ⟨fun i => (hst.1 i).trans (htu.1 i), by
    rcases hst.2 with hs | hs
    · exact Or.inl hs
    · rcases htu.2 with ht | ht
      · exact Or.inl (hs.trans ht)
      · exact Or.inr (hs.trans ht)⟩
  absolutelyContinuous h := UniformVector.law_refines h.1
  error bits _ := (2 ^ bits : ℝ)⁻¹
  error_tendsto _ := Filter.Eventually.of_forall fun _ =>
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))

/-- The same dyadic cell convention is used before and after selection. -/
def representation (n k : ℕ) (hk : 0 < k ∧ k ≤ n) : Representation (model n k hk) where
  interval bits x := LatentUniform.dyadicInterval bits (UniformOrderStatistic.rank n k hk x)
  measurable_lower _ := Int.measurable_floor.comp (by fun_prop)
  measurable_upper _ := (Int.measurable_floor.comp (by fun_prop)).add_const 1
  measurable_denominator _ := measurable_const
  approximates _ := Filter.Eventually.of_forall fun _ => LatentUniform.dyadicInterval_approximates _

/-- Construction represents the standard beta order-statistic law. -/
theorem model_initial_law (n k : ℕ) (hk : 0 < k ∧ k ≤ n) :
    (model n k hk).law (initial n) =
      ProbabilityTheory.betaMeasure (k : ℝ) ((n + 1 - k : ℕ) : ℝ) :=
  UniformOrderStatistic.rank_law n k hk

/-- A coordinate read retains the selected physical identity. -/
def update {n : ℕ} (s : State n) (i : Fin n) (q : List Bool) : State n :=
  ⟨Function.update s.prefixes i q, s.selected⟩

theorem refines_update {n : ℕ} (s : State n) (i : Fin n) (q : List Bool)
    (hq : s.prefixes i <+: q) : Refines s (update s i q) :=
  ⟨UniformVector.refines_update s.prefixes i q hq, Or.inr rfl⟩

end mathematics

section ownership

open Iris Iris.BI Iris.ProofMode

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
variable {GF : BundledGFunctors} [AppGS rT GF]
local bi (IProp GF)

/-- The selected handle denotes the rank, and all original roots remain owned. -/
def owns (n k : ℕ) (hk : 0 < k ∧ k ≤ n) (v : Val rT) (s : State n) : IProp GF :=
  iprop(∃ (roots : Fin n → Loc) (i : Fin n),
    ⌜s.selected = some (roots, i) ∧ v = LatentUniform.value (roots i) ∧
      ∀ᵐ x ∂UniformVector.law s.prefixes, UniformOrderStatistic.rank n k hk x = x i⌝ ∗
    UniformVector.rootsOwns roots s.prefixes)

end ownership

end

end SampLib.LatentReal.OrderStatistic
