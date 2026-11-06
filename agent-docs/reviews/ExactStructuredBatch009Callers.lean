import SampLib.Weighted.SuccinctChoice

open ProbLang
open scoped ENNReal

namespace ReviewExactStructured009

noncomputable section

open SampLib Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem framed (E : CoPset) (ws : List ℕ) [NeZero ws.sum]
    (hwords : SuccinctChoice.Admissible ws) (F : ℕ → ℝ≥0∞) (Q : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law ws) ∗ Q -∗
      tglWp E pl(&Occil.WeightedVariants.succinctChoice
        &(listVal (fun n : ℕ => Val.int n) ws).fst #())
        (fun result => iprop(∃ i : ℕ, ⌜result = Val.int (i : ℤ)⌝ ∗ ↯ (F i) ∗ Q)) := by
  iintro ⟨Hcredit, HQ⟩
  iapply ((SuccinctChoice.succinctChoice_distSpec E ws hwords).wp
    F (measurable_of_countable _) _) $$ Hcredit
  iintro %i Hcredit
  iexists i
  iframe Hcredit HQ
  itrivial

example (E : CoPset) (F : ℕ → ℝ≥0∞) (Q : IProp GF) := by
  have : NeZero ([0, 3, 1] : List ℕ).sum := ⟨by norm_num⟩
  exact framed E [0, 3, 1] (Or.inr (by norm_num)) F Q

/-- Dense input uses the direct branch even when a weight exceeds every packed field. -/
example (E : CoPset) (Q : IProp GF) := by
  have : NeZero ([2 ^ 40, 0] : List ℕ).sum := ⟨by norm_num⟩
  exact framed E [2 ^ 40, 0] (Or.inl (by norm_num)) (fun _ => ∞) Q

/-- A sparse population containing both a wide field and zero still uses the packed branch. -/
example (E : CoPset) (Q : IProp GF) := by
  have : NeZero ([2 ^ 20, 1, 0, 2] : List ℕ).sum := ⟨by norm_num⟩
  exact framed E [2 ^ 20, 1, 0, 2] (Or.inr (by norm_num)) (fun _ => ∞) Q

end

open SampLib

example : PackedWeights.width (2 ^ 20 - 1) = 20 ∧ PackedWeights.width (2 ^ 20) = 32 := by
  norm_num [PackedWeights.width, PackedWeights.Wide]

example : PackedWeights.bits [7, 2 ^ 20, 0] / 2 ^ 20 % 2 ^ 32 = 2 ^ 20 := by
  norm_num [PackedWeights.bits, PackedBits.encode, PackedWeights.width, PackedWeights.Wide]

example : PackedWeights.wideBefore [7, 2 ^ 20, 0] 2 = 1 := by
  rw [PackedWeights.wideBefore_eq]
  norm_num [PackedWeights.flag, PackedWeights.Wide]

/-- The exact packed-word guard excludes an overflowing sparse field. -/
example : ¬ SuccinctChoice.Admissible (2 ^ 32 :: List.replicate 8192 0) := by
  rintro (hd | hf)
  · have hlength : (2 ^ 32 :: List.replicate 8192 0).length = 8193 := by
      rw [List.length_cons, List.length_replicate]
    have hsum : (2 ^ 32 :: List.replicate 8192 0 : List ℕ).sum = 2 ^ 32 := by
      rw [List.sum_cons, List.sum_replicate]
      simp only [nsmul_eq_mul, mul_zero, add_zero]
    rw [hlength, hsum] at hd
    norm_num at hd
  · exact (Nat.lt_irrefl _) (hf _ (List.mem_cons_self))

example : (∫⁻ i, (if i = 0 then ∞ else 0)
    ∂WeightedChoice.law [0, 3, 1]) = 0 := by
  rw [WeightedChoice.lintegral_law]
  norm_num [WeightedChoice.weightedSum]

#print axioms SampLib.SuccinctChoice.succinctChoice_distSpec
#print axioms SampLib.SuccinctChoice.twp_succinctChoice
#print axioms SampLib.SuccinctChoice.twp_pack
#print axioms SampLib.PackedWeights.decode
#print axioms SampLib.EnvelopeRejection.coin_expectation
#print axioms framed

end ReviewExactStructured009
