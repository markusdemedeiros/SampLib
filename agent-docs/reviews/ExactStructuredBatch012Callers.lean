import SampLib.Samplers.OptimalDraw

open ProbLang
open scoped ENNReal

namespace ReviewExactStructured012

noncomputable section

open SampLib OptimalTable OptimalEncoding Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- A hand-made table, as the source tuple `(matrix, (k, (l, rejected)))`. -/
abbrev tableArg {n : ℕ} (rows : Fin n → ℕ) (k l : ℕ) (rejected : ℤ) : Exp rT :=
  (OptimalMatrix.Table.value ⟨List.ofFn rows, k, l, rejected⟩ : Val rT).fst

/-- The public spec frames an arbitrary resource on every valid table. -/
theorem framed (E : CoPset) {n : ℕ} (rows : Fin n → ℕ) (k l : ℕ) (hl : l < k)
    (rejected : ℤ) (hroot : ∑ i, weight k l (rows i) = denominator k l)
    [NeZero (acceptedMass rows k l rejected)] (F : ℕ → ℝ≥0∞) (Q : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law (accepted rows k l rejected)) ∗ Q -∗
      tglWp E pl(&Occil.WeightedVariants.optimalDraw &(tableArg rows k l rejected) #())
        (fun result => iprop(∃ i : ℕ, ⌜result = Val.int (i : ℤ)⌝ ∗ ↯ (F i) ∗ Q)) := by
  iintro ⟨Hcredit, HQ⟩
  iapply ((optimalDraw_distSpec E rows k l hl rejected hroot).wp
    F (measurable_of_countable _) _) $$ Hcredit
  iintro %i Hcredit
  iexists i
  iframe Hcredit HQ
  itrivial

/-- k = 2, l = 0 (D = 3), no rejection label, rows [1, 2]. -/
example (E : CoPset) (F : ℕ → ℝ≥0∞) (Q : IProp GF) := by
  have : NeZero (acceptedMass ![1, 2] 2 0 (-1)) := ⟨by decide +kernel⟩
  exact framed E ![1, 2] 2 0 (by norm_num) (-1) (by decide +kernel) F Q

/-- Rejection probability 2/3 > 1/2: the factor `1 + A/D` still pays the restart. -/
example (E : CoPset) (Q : IProp GF) := by
  have : NeZero (acceptedMass ![1, 2] 2 0 1) := ⟨by decide +kernel⟩
  exact framed E ![1, 2] 2 0 (by norm_num) 1 (by decide +kernel) (fun _ => ∞) Q

/-- Certain all-ones row at k = 2, l = 1, a zero row, and an out-of-range label 7. -/
example (E : CoPset) (F : ℕ → ℝ≥0∞) (Q : IProp GF) := by
  have : NeZero (acceptedMass ![3, 0] 2 1 7) := ⟨by decide +kernel⟩
  exact framed E ![3, 0] 2 1 (by norm_num) 7 (by decide +kernel) F Q

/-- Rows above `2^k` are read only through their scanned low bits. -/
example (E : CoPset) (F : ℕ → ℝ≥0∞) (Q : IProp GF) := by
  have : NeZero (acceptedMass ![1 + 4, 2 + 8] 2 0 (-1)) := ⟨by decide +kernel⟩
  exact framed E ![1 + 4, 2 + 8] 2 0 (by norm_num) (-1) (by decide +kernel) F Q

end

open SampLib OptimalTable

/-- The rejected label carries no output mass. -/
example : accepted ![1, 1, 1] 2 0 2 = [1, 1, 0] := by decide +kernel

/-- Excluded: a certain rejected row has no accepted mass. -/
example : acceptedMass ![3, 0] 2 1 0 = 0 := by decide +kernel

/-- Excluded: masses summing below one. -/
example : ∑ i, weight 2 0 (![1, 1] i) ≠ OptimalEncoding.denominator 2 0 := by decide +kernel

/-- The table built by preprocessing is one valid instance (rows [1,0,5,1], k=3, l=1). -/
example : ∑ i, weight 3 1 (![1, 0, 5, 1] i) = OptimalEncoding.denominator 3 1 ∧
    accepted ![1, 0, 5, 1] 3 1 3 = [1, 0, 4, 0] := by decide +kernel

#print axioms SampLib.OptimalTable.optimalDraw_distSpec
#print axioms SampLib.OptimalTable.twp_root
#print axioms SampLib.OptimalTable.restart_expectation
#print axioms ReviewExactStructured012.framed

end ReviewExactStructured012
