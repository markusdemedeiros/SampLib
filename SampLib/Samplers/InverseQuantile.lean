import SampLib.Samplers.Choice
import Samplers.General.Core

/-! # Quantiles on a uniform interior probability grid -/

open ProbLang
open scoped ENNReal

namespace SampLib.InverseQuantile

noncomputable section

section mathematics

open MeasureTheory

variable {α : Type _} [MeasurableSpace α]

/-- Push the uniform interior-grid positions through the supplied quantile. -/
def law (n : ℕ) [NeZero n] (quantile : Fin n → α) : Measure α :=
  (Choice.law n).map quantile

instance (n : ℕ) [NeZero n] (quantile : Fin n → α) :
    IsProbabilityMeasure (law n quantile) where
  measure_univ := by
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- The quantile expectation is the average over the interior ranks. -/
theorem expectation (n : ℕ) [NeZero n] (quantile : Fin n → α)
    (F : α → ℝ≥0∞) (hF : Measurable F) :
    (∑ k ∈ Finset.range n, F (quantile (Choice.position n k))) / n =
      ∫⁻ x, F x ∂law n quantile := by
  rw [law, lintegral_map hF (measurable_of_countable _), Choice.lintegral_law]

end mathematics

private theorem scale_test (n : ℕ) [NeZero n] :
    decide (((n + 1 : ℕ) : ℤ) ≤ 1) = false := by
  exact decide_eq_false (by have := NeZero.pos n; omega)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {α : Type _} [MeasurableSpace α]
local bi (IProp GF)

/-- The input scale is `n+1`, so its interior ranks are precisely `1,…,n`. -/
theorem twp_inverseQuantile (E : CoPset) (n : ℕ) [NeZero n]
    (quantile : Fin n → α) (encode : α → Val rT) (callback : Val rT)
    (hquantile : ∀ i : Fin n,
      ⊢ tglWp E pl(&callback.fst #int ((n + 1 : ℕ) : ℤ) #int ((i.val + 1 : ℕ) : ℤ))
        (fun v : Val rT => iprop(⌜v = encode (quantile i)⌝)))
    (F : α → ℝ≥0∞) (hF : Measurable F) :
    ⊢ ↯ (∫⁻ x, F x ∂law n quantile) -∗
      tglWp E pl(&Occil.General.inverseQuantile #int ((n + 1 : ℕ) : ℤ) &callback.fst #())
        (fun v : Val rT => iprop(∃ x : α, ⌜v = encode x⌝ ∗ ↯ (F x))) := by
  iintro Hcredit
  twp_pures
  rw [scale_test n]
  twp_pure
  twp_pure
  rw [Nat.cast_add_one, add_sub_cancel_right]
  twp_bind pl(&Occil.uniformInt #int (n : ℤ))
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply (UniformInt.twp_uniformInt E n (NeZero.pos n)
      (fun k => F (quantile (Choice.position n k))))
    rw [expectation n quantile F hF]
    iexact Hcredit
  iintro %v ⟨%k, %hv, %hk, Hcredit⟩
  subst v
  twp_pures
  have hcallback := hquantile ⟨k, hk⟩
  simp only [Nat.cast_add_one] at hcallback
  rw [add_comm (k : ℤ) 1] at hcallback
  twp_bind pl(&callback.fst #int ((n : ℤ) + 1) #int (1 + (k : ℤ)))
  iapply tglWp_wand
  isplitl []
  · iapply hcallback
  iintro %v %hv
  iapply (tglWp_value (v := v))
  iexists quantile ⟨k, hk⟩
  isimp only [Choice.position_of_lt k hk] at Hcredit
  iframe Hcredit
  ipureintro
  exact hv

/-- Typed quantile pushforward on every nonempty interior probability grid. -/
theorem inverseQuantile_distSpec (E : CoPset) (n : ℕ) [NeZero n]
    (quantile : Fin n → α) (encode : α → Val rT) (callback : Val rT)
    (hquantile : ∀ i : Fin n,
      ⊢ tglWp E pl(&callback.fst #int ((n + 1 : ℕ) : ℤ) #int ((i.val + 1 : ℕ) : ℤ))
        (fun v : Val rT => iprop(⌜v = encode (quantile i)⌝))) :
    IsDistSpec (GF := GF) E
      pl(&Occil.General.inverseQuantile #int ((n + 1 : ℕ) : ℤ) &callback.fst #())
      (law n quantile) encode where
  spec F hF := wand_entails (twp_inverseQuantile E n quantile encode callback hquantile F hF)

end specification

end

end SampLib.InverseQuantile
