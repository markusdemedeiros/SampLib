import SampLib.Core.ListEncoding
import SampLib.Uniform.UniformInt
import Samplers.Combinatorial.Basic
import Metrology.Iris.LocalBI

/-!
# Uniform list choice

The mathematical output is a uniformly sampled position, encoded by its list
entry. Equal entries retain their separate positions and hence multiplicities.
-/

open Set ProbLang
open scoped ENNReal

namespace SampLib.Choice

noncomputable section

section distribution

open MeasureTheory

/-- Extend an in-range natural position to a total finite-index map. -/
def position (n : ℕ) [NeZero n] (k : ℕ) : Fin n :=
  ⟨k % n, Nat.mod_lt _ (NeZero.pos n)⟩

theorem position_of_lt {n : ℕ} [NeZero n] (k : ℕ) (hk : k < n) :
    position n k = ⟨k, hk⟩ := Fin.ext (Nat.mod_eq_of_lt hk)

/-- Uniform finite-position law. -/
def law (n : ℕ) [NeZero n] : Measure (Fin n) :=
  (UniformInt.law n).map (position n)

instance (n : ℕ) [NeZero n] : IsProbabilityMeasure (law n) where
  measure_univ := by
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- The lookup's continuation credit is averaged over positions. -/
theorem lintegral_law (n : ℕ) [NeZero n] (F : Fin n → ℝ≥0∞) :
    ∫⁻ i, F i ∂law n = (∑ k ∈ Finset.range n, F (position n k)) / n := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    UniformInt.lintegral_law]

end distribution

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF] {α : Type _}
local bi (IProp GF)

/-- CTE specification for any nonempty list, with arbitrary element values. -/
theorem twp_choice (E : CoPset) (encode : α → Val rT) (xs : List α)
    [NeZero xs.length] (F : Fin xs.length → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ i, F i ∂law xs.length) -∗
      tglWp E pl(&Occil.choice &(listVal encode xs).fst)
        (fun v : Val rT => iprop(∃ i : Fin xs.length,
          ⌜v = encode (xs.get i)⌝ ∗ ↯ (F i))) := by
  iintro Hcredit
  twp_pure
  twp_bind pl(&Occil.length &(listVal encode xs).fst)
  iapply tglWp_wand
  isplitl []
  · iapply (twp_length E encode xs)
  iintro %v %hv
  subst v
  twp_bind pl(&Occil.uniformInt #int (xs.length : ℤ))
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply (UniformInt.twp_uniformInt E xs.length (NeZero.pos xs.length)
      (fun k => F (position xs.length k)))
    rw [← lintegral_law]
    iexact Hcredit
  iintro %v ⟨%k, %hv, %hk, Hcredit⟩
  subst v
  twp_bind pl(&Occil.getAt &(listVal encode xs).fst #int (k : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply (twp_getAt E encode xs ⟨k, hk⟩)
  iintro %v %hv
  iapply (tglWp_value (v := v))
  iexists ⟨k, hk⟩
  isimp only [position_of_lt k hk] at Hcredit
  iframe Hcredit
  ipureintro
  exact hv

/-- Typed specification using latent positions and their list entries. -/
theorem choice_distSpec (E : CoPset) (encode : α → Val rT) (xs : List α)
    [NeZero xs.length] :
    IsDistSpec (GF := GF) E pl(&Occil.choice &(listVal encode xs).fst)
      (law xs.length) (fun i => encode (xs.get i)) where
  spec F _ := wand_entails (twp_choice E encode xs F)

end specification

end

end SampLib.Choice
