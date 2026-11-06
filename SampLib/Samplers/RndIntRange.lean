import SampLib.Samplers.RndInt
import Samplers.Uniform
import Metrology.Iris.LocalBI

/-! # Uniform integers on an inclusive interval -/

open Set ProbLang
open scoped ENNReal

namespace SampLib.RndIntRange

noncomputable section

section mathematics

open MeasureTheory

/-- Shift the inclusive uniform offset law to the requested integer interval. -/
def law (lo hi : ℤ) : Measure ℤ :=
  (RndInt.law (hi - lo).toNat).map (fun k : ℕ => lo + (k : ℤ))

instance (lo hi : ℤ) : IsProbabilityMeasure (law lo hi) := by
  unfold law
  infer_instance

/-- Translation transports the offset expectation to the interval law. -/
theorem expectation (lo hi : ℤ) (F : ℤ → ℝ≥0∞) :
    ∫⁻ k, F (lo + (k : ℤ)) ∂RndInt.law (hi - lo).toNat = ∫⁻ z, F z ∂law lo hi := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]

end mathematics

private theorem range_test (lo hi : ℤ) (h : lo ≤ hi) : decide (hi < lo) = false :=
  decide_eq_false (not_lt.mpr h)

private theorem width_eq (lo hi : ℤ) (h : lo ≤ hi) : hi - lo = ((hi - lo).toNat : ℤ) :=
  (Int.toNat_of_nonneg (sub_nonneg.mpr h)).symm

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem twp_rndIntRange (E : CoPset) (lo hi : ℤ) (h : lo ≤ hi) (F : ℤ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ z, F z ∂law lo hi) -∗ tglWp E pl(&Occil.rndIntRange #lo #hi)
      (fun v : Val rT => iprop(∃ z : ℤ, ⌜v = Val.int z⌝ ∗ ↯ (F z))) := by
  iintro Hcredit
  twp_pures
  rw [range_test lo hi h]
  twp_pure
  twp_pure
  rw [width_eq lo hi h]
  twp_bind pl(&Occil.rndInt #int ((hi - lo).toNat : ℤ))
  isimp only [← expectation lo hi F] at Hcredit
  iapply ((RndInt.rndInt_distSpec E (hi - lo).toNat).wp
    (fun k => F (lo + (k : ℤ))) (measurable_of_countable _) _) $$ Hcredit
  iintro %k Hcredit
  twp_pures
  twp_value
  imodintro
  iexists lo + (k : ℤ)
  iframe Hcredit
  itrivial

/-- The entire nonempty inclusive interval, including singleton intervals. -/
theorem rndIntRange_distSpec (E : CoPset) (lo hi : ℤ) (h : lo ≤ hi) :
    IsDistSpec (GF := GF) E pl(&Occil.rndIntRange #lo #hi) (law lo hi) Val.int where
  spec F _ := wand_entails (twp_rndIntRange E lo hi h F)

end specification

end

end SampLib.RndIntRange
