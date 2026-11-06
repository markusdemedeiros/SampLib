import SampLib.Weighted.SuccinctChoice

open ProbLang Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open scoped ENNReal

namespace SuccinctAuthorChecks

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example (E : CoPset) (ws : List ℕ) [NeZero ws.sum] (hw : SampLib.SuccinctChoice.Admissible ws)
    (F : ℕ → ℝ≥0∞) (R : IProp GF) :
    ↯ (∫⁻ i, F i ∂SampLib.WeightedChoice.law ws) ∗ R ⊢
      tglWp E pl(&Occil.WeightedVariants.succinctChoice
        &(SampLib.listVal (fun n : ℕ => Val.int n) ws).fst #())
        (fun v => iprop(∃ i : ℕ, ⌜v = Val.int (i : ℤ)⌝ ∗ ↯ (F i) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  iapply ((SampLib.SuccinctChoice.succinctChoice_distSpec E ws hw).wp F
    (measurable_of_countable _) _) $$ Hcredit
  iintro %i Hcredit
  iexists i
  iframe Hcredit HR
  ipureintro
  rfl

private def packed : List ℕ := [0, 0, 2 ^ 20]
private def mixed : List ℕ := [0, 0, 0, 0, 2 ^ 20, 2 ^ 20 - 1]
private def huge : List ℕ := [2 ^ 40]

local instance : NeZero packed.sum := ⟨by decide⟩
local instance : NeZero mixed.sum := ⟨by decide⟩
local instance : NeZero huge.sum := ⟨by decide⟩

example : ¬2 ^ 19 * packed.length ≤ packed.sum := by decide
example : ¬2 ^ 19 * mixed.length ≤ mixed.sum := by decide

example (E : CoPset) :
    SampLib.IsDistSpec (GF := GF) E pl(&Occil.WeightedVariants.succinctChoice
      &(SampLib.listVal (fun n : ℕ => Val.int n) packed).fst #())
      (SampLib.WeightedChoice.law packed) (fun i : ℕ => Val.int (i : ℤ)) := by
  exact SampLib.SuccinctChoice.succinctChoice_distSpec E packed (Or.inr (by norm_num [packed]))

example (E : CoPset) :
    SampLib.IsDistSpec (GF := GF) E pl(&Occil.WeightedVariants.succinctChoice
      &(SampLib.listVal (fun n : ℕ => Val.int n) mixed).fst #())
      (SampLib.WeightedChoice.law mixed) (fun i : ℕ => Val.int (i : ℤ)) := by
  exact SampLib.SuccinctChoice.succinctChoice_distSpec E mixed (Or.inr (by norm_num [mixed]))

example (E : CoPset) :
    SampLib.IsDistSpec (GF := GF) E pl(&Occil.WeightedVariants.succinctChoice
      &(SampLib.listVal (fun n : ℕ => Val.int n) huge).fst #())
      (SampLib.WeightedChoice.law huge) (fun i : ℕ => Val.int (i : ℤ)) := by
  exact SampLib.SuccinctChoice.succinctChoice_distSpec E huge (Or.inl (by norm_num [huge]))

example : (∫⁻ i, (if i = 0 then ∞ else 0) ∂SampLib.WeightedChoice.law packed) = 0 := by
  rw [SampLib.WeightedChoice.lintegral_law]
  simp [packed, SampLib.WeightedChoice.weightedSum, ENNReal.zero_div]

example (i : ℕ) (hi : i < ([0, 2 ^ 20 - 1, 2 ^ 20, 2 ^ 32 - 1] : List ℕ).length) :
    let ws : List ℕ := [0, 2 ^ 20 - 1, 2 ^ 20, 2 ^ 32 - 1]
    SampLib.PackedWeights.bits ws /
      2 ^ (32 * SampLib.PackedWeights.wideBefore ws i +
        20 * (i - SampLib.PackedWeights.wideBefore ws i)) %
      2 ^ (if SampLib.PackedWeights.mask ws / 2 ^ i % 2 = 1 then 32 else 20) = ws[i] := by
  exact SampLib.PackedWeights.decode _ (by norm_num) i hi

#print axioms SampLib.SuccinctChoice.succinctChoice_distSpec
#print axioms SampLib.SuccinctChoice.twp_succinctChoice
#print axioms SampLib.SuccinctChoice.twp_pack
#print axioms SampLib.PackedBits.decode
#print axioms SampLib.PackedBits.count_encode
#print axioms SampLib.PackedWeights.decode
#print axioms SampLib.KnownIntegerComparison.twp_le
#print axioms SampLib.KnownIntegerComparison.twp_eq

end SuccinctAuthorChecks
