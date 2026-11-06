import SampLib.Samplers.PoissonRational
import Samplers.Discrete.Compound

/-! # Differences of independent Poisson counts -/

open ProbLang
open scoped ENNReal NNReal

namespace SampLib.Skellam

noncomputable section

section mathematics

open MeasureTheory

/-- The Skellam law is the signed difference of two independent Poisson counts. -/
def law (left right : ℝ≥0) : Measure ℤ :=
  ((ProbabilityTheory.poissonMeasure left).prod
    (ProbabilityTheory.poissonMeasure right)).map (fun z => (z.1 : ℤ) - z.2)

instance (left right : ℝ≥0) : IsProbabilityMeasure (law left right) where
  measure_univ := by
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- Independence supplies the successive credits for the two Poisson draws. -/
theorem expectation (left right : ℝ≥0) (F : ℤ → ℝ≥0∞) :
    (∫⁻ x, ∫⁻ y, F ((x : ℤ) - y) ∂ProbabilityTheory.poissonMeasure right
      ∂ProbabilityTheory.poissonMeasure left) = ∫⁻ z, F z ∂law left right := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    lintegral_prod _ (measurable_of_countable _).aemeasurable]

end mathematics

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem twp_skellam (E : CoPset) (a b c d : ℕ) (hb : 0 < b) (hd : 0 < d)
    (F : ℤ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ z, F z ∂law (PoissonRational.rate a b) (PoissonRational.rate c d)) -∗
      tglWp E pl(&Occil.DiscreteExtra.skellam
        #int (a : ℤ) #int (b : ℤ) #int (c : ℤ) #int (d : ℤ))
        (fun v : Val rT => iprop(∃ z : ℤ, ⌜v = Val.int z⌝ ∗ ↯ (F z))) := by
  iintro Hcredit
  iterate 4 twp_pure
  simp only [PoissonRational.poissonRational_openRec,
    PoissonRational.poissonRational_closeRec]
  twp_bind pl(&Occil.poissonRational #int (a : ℤ) #int (b : ℤ))
  isimp only [← expectation (PoissonRational.rate a b) (PoissonRational.rate c d) F]
    at Hcredit
  iapply ((PoissonRational.poissonRational_distSpec E a b hb).wp
    (fun x => ∫⁻ y, F ((x : ℤ) - y) ∂ProbabilityTheory.poissonMeasure
      (PoissonRational.rate c d)) (measurable_of_countable _) _) $$ Hcredit
  iintro %x Hcredit
  twp_pure
  simp only [PoissonRational.poissonRational_openRec]
  twp_bind pl(&Occil.poissonRational #int (c : ℤ) #int (d : ℤ))
  iapply ((PoissonRational.poissonRational_distSpec E c d hd).wp
    (fun y => F ((x : ℤ) - y)) (measurable_of_countable _) _) $$ Hcredit
  iintro %y Hcredit
  twp_pures
  twp_value
  imodintro
  iexists (x : ℤ) - y
  iframe Hcredit
  itrivial

theorem skellam_distSpec (E : CoPset) (a b c d : ℕ) (hb : 0 < b) (hd : 0 < d) :
    IsDistSpec (GF := GF) E pl(&Occil.DiscreteExtra.skellam
      #int (a : ℤ) #int (b : ℤ) #int (c : ℤ) #int (d : ℤ))
      (law (PoissonRational.rate a b) (PoissonRational.rate c d)) Val.int where
  spec F _ := wand_entails (twp_skellam E a b c d hb hd F)

end specification

end

end SampLib.Skellam
