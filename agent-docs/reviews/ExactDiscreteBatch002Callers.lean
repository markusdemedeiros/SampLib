import SampLib.Discrete.InversePolya
import SampLib.Discrete.BetaNegativeBinomial
import SampLib.Discrete.WaringYule
import SampLib.Discrete.YuleSimon

open ProbLang
open scoped ENNReal

namespace ReviewExactDiscrete002

noncomputable section

open SampLib

/-- Unreduced rational shapes are accepted; both shapes here equal one half. -/
private def shapes : BetaNegativeBinomial.Parameters :=
  ⟨2, 4, 3, 6, by decide, by decide, by decide, by decide⟩

example : BetaNegativeBinomial.law shapes 1 {0} = (1 : ℝ≥0∞) / 2 := by
  rw [BetaNegativeBinomial.mass shapes 0 0]
  norm_num [shapes, BetaNegativeBinomial.marked, BetaNegativeBinomial.unmarked,
    BetaNegativeBinomial.reinforcement, InverseUrn.positiveMass,
    InverseUrn.coefficient, InverseUrn.rising, PolyaEggenberger.rising, Nat.choose,
    ENNReal.ofReal_div_of_pos]

/-- Subunit shapes require no finite-mean assumption for these exact masses. -/
example : WaringYule.law shapes {1} = (1 : ℝ≥0∞) / 8 := by
  rw [WaringYule.mass shapes 1]
  norm_num [shapes, BetaNegativeBinomial.marked, BetaNegativeBinomial.unmarked,
    BetaNegativeBinomial.reinforcement, InverseUrn.positiveMass,
    InverseUrn.coefficient, InverseUrn.rising, PolyaEggenberger.rising, Nat.choose,
    ENNReal.ofReal_div_of_pos]

/-- Zero reinforcement reduces to an ordinary negative-binomial count. -/
example : InverseUrn.law 3 1 2 0 (by decide) {2} = (8 : ℝ≥0∞) / 81 := by
  rw [InverseUrn.mass_positive 2 1 2 0 2 (by decide)]
  norm_num [InverseUrn.positiveMass, InverseUrn.coefficient,
    InverseUrn.rising, PolyaEggenberger.rising, Nat.choose, ENNReal.ofReal_div_of_pos]

example : InverseUrn.law 5 2 0 9 (by decide) {1} = 0 := by
  rw [InverseUrn.mass_positive 4 2 0 9 1 (by decide)]
  norm_num [InverseUrn.positiveMass, InverseUrn.coefficient,
    InverseUrn.rising, PolyaEggenberger.rising, Nat.choose, ENNReal.ofReal_div_of_pos]

example : InverseUrn.law 0 1 0 0 (by decide) = MeasureTheory.Measure.dirac 0 := rfl

example : YuleSimon.law 2 3 (by decide) (by decide) {2} = (3 : ℝ≥0∞) / 20 := by
  rw [YuleSimon.mass 2 3 1 (by decide) (by decide)]
  norm_num [InverseUrn.positiveMass, InverseUrn.coefficient,
    InverseUrn.rising, PolyaEggenberger.rising, Nat.choose, ENNReal.ofReal_div_of_pos]

example : YuleSimon.law 2 3 (by decide) (by decide) {0} = 0 := by
  rw [YuleSimon.law, MeasureTheory.Measure.map_apply (measurable_of_countable _)
    (measurableSet_singleton _)]
  have hpre : Nat.succ ⁻¹' ({0} : Set ℕ) = ∅ := by
    ext n
    simp
  simp only [hpre, MeasureTheory.measure_empty]

section callers

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
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

example (E : CoPset) (r a b c : ℕ) (ha : 0 < a) (F : ℕ → ℝ≥0∞) (R : IProp GF) :=
  frame (InversePolya.inversePolya_distSpec E r a b c ha)
    F (measurable_of_countable _) R

example (E : CoPset) (D : BetaNegativeBinomial.Parameters) (r : ℕ)
    (F : ℕ → ℝ≥0∞) (R : IProp GF) :=
  frame (BetaNegativeBinomial.betaNegativeBinomial_distSpec E D r)
    F (measurable_of_countable _) R

example (E : CoPset) (D : BetaNegativeBinomial.Parameters)
    (F : ℕ → ℝ≥0∞) (R : IProp GF) :=
  frame (WaringYule.waringYule_distSpec E D) F (measurable_of_countable _) R

example (E : CoPset) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (F : ℕ → ℝ≥0∞) (R : IProp GF) :=
  frame (YuleSimon.yuleSimon_distSpec E a b ha hb) F (measurable_of_countable _) R

example (E : CoPset) (F : ℕ → ℝ≥0∞) (R : IProp GF) :=
  frame (InversePolya.inversePolya_distSpec E 0 1 0 0 (by decide))
    F (measurable_of_countable _) R

example (E : CoPset) (F : ℕ → ℝ≥0∞) (R : IProp GF) :=
  frame (BetaNegativeBinomial.betaNegativeBinomial_distSpec E shapes 0)
    F (measurable_of_countable _) R

example (E : CoPset) (R : IProp GF) :=
  frame (WaringYule.waringYule_distSpec E shapes) (fun _ => ∞) measurable_const R

end callers

#print axioms SampLib.InversePolya.inversePolya_distSpec
#print axioms SampLib.BetaNegativeBinomial.betaNegativeBinomial_distSpec
#print axioms SampLib.WaringYule.waringYule_distSpec
#print axioms SampLib.YuleSimon.yuleSimon_distSpec
#print axioms SampLib.UrnWaiting.absorbs
#print axioms SampLib.InverseUrn.mass_positive

end

end ReviewExactDiscrete002
