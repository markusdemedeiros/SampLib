import SampLib.Samplers.UniformInt
import Samplers.Uniform
import Metrology.Iris.LocalBI

/-! # Uniform integers on a half-open interval -/

open Set ProbLang
open scoped ENNReal

namespace SampLib.RndIntExcRange

noncomputable section

section mathematics

open MeasureTheory

/-- Shift the exclusive uniform offset law to `[lo, hi)`. -/
def law (lo hi : ℤ) (_h : lo < hi) : Measure ℤ :=
  (UniformInt.law (hi - lo).toNat).map (fun k : ℕ => lo + (k : ℤ))

instance (lo hi : ℤ) (h : lo < hi) : IsProbabilityMeasure (law lo hi h) := by
  let : NeZero (hi - lo).toNat := ⟨by omega⟩
  unfold law
  infer_instance

/-- Translation transports the offset expectation to the interval law. -/
theorem expectation (lo hi : ℤ) (h : lo < hi) (F : ℤ → ℝ≥0∞) :
    ∫⁻ k, F (lo + (k : ℤ)) ∂UniformInt.law (hi - lo).toNat = ∫⁻ z, F z ∂law lo hi h := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]

end mathematics

private theorem range_test (lo hi : ℤ) (h : lo < hi) : decide (lo < hi) = true :=
  decide_eq_true h

private theorem width_eq (lo hi : ℤ) (h : lo < hi) : hi - lo = ((hi - lo).toNat : ℤ) :=
  (Int.toNat_of_nonneg (sub_nonneg.mpr h.le)).symm

private theorem width_ne_zero (lo hi : ℤ) (h : lo < hi) : (hi - lo).toNat ≠ 0 := by
  omega

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem twp_rndIntExcRange (E : CoPset) (lo hi : ℤ) (h : lo < hi) (F : ℤ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ z, F z ∂law lo hi h) -∗ tglWp E pl(&Occil.rndIntExcRange #lo #hi)
      (fun v : Val rT => iprop(∃ z : ℤ, ⌜v = Val.int z⌝ ∗ ↯ (F z))) := by
  let : NeZero (hi - lo).toNat := ⟨width_ne_zero lo hi h⟩
  iintro Hcredit
  twp_pures
  rw [range_test lo hi h]
  twp_pure
  twp_pure
  rw [width_eq lo hi h]
  twp_bind pl(&Occil.uniformInt #int ((hi - lo).toNat : ℤ))
  isimp only [← expectation lo hi h F] at Hcredit
  iapply ((UniformInt.uniformInt_distSpec E (hi - lo).toNat).wp
    (fun k => F (lo + (k : ℤ))) (measurable_of_countable _) _) $$ Hcredit
  iintro %k Hcredit
  twp_pures
  twp_value
  imodintro
  iexists lo + (k : ℤ)
  iframe Hcredit
  itrivial

/-- The full nonempty half-open interval. -/
theorem rndIntExcRange_distSpec (E : CoPset) (lo hi : ℤ) (h : lo < hi) :
    IsDistSpec (GF := GF) E pl(&Occil.rndIntExcRange #lo #hi) (law lo hi h) Val.int where
  spec F _ := wand_entails (twp_rndIntExcRange E lo hi h F)

end specification

end

end SampLib.RndIntExcRange
