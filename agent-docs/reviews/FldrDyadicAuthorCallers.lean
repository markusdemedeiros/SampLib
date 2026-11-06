import SampLib.Distributions.FldrDyadic

namespace FldrDyadicAuthorCallers

open SampLib

private def weights : Fin 3 → ℕ := ![1, 2, 1]

private theorem total : ∑ i, weights i = 2 ^ 2 := by decide

example : KnuthYaoColumns.alive weights 4 2 = 0 :=
  FldrDyadic.alive_zero weights 2 2 total le_rfl

example : KnuthYaoColumns.alive weights 4 100 = 0 :=
  FldrDyadic.alive_zero weights 2 100 total (by omega)

example : FldrDyadic.place 0 0 = 0 := by decide
example : FldrDyadic.place 2 0 = 2 := by decide
example : FldrDyadic.place 2 1 = 1 := by decide
example : FldrDyadic.place 2 2 = 0 := FldrDyadic.place_vanishes 2 2 le_rfl

example : KnuthYaoColumns.column weights 4 0 1 = 1 := by decide
example : KnuthYaoColumns.column weights 4 1 1 = 0 := by decide

example : FldrDyadic.padded [1, 2] 4 = [1, 2, 1] := rfl
example : (FldrDyadic.padded [1, 2] 4).sum = 4 :=
  FldrDyadic.sum_padded [1, 2] 4 (by decide)

example (k d w : ℕ) (hd : d < k) :
    w / FldrDyadic.place k d % 2 = (w * 2 ^ (d + 1) / 2 ^ k) % 2 :=
  FldrDyadic.digit w k d hd

end FldrDyadicAuthorCallers

#print axioms SampLib.FldrDyadic.place_eq
#print axioms SampLib.FldrDyadic.place_half
#print axioms SampLib.FldrDyadic.column
#print axioms SampLib.FldrDyadic.alive_zero
#print axioms SampLib.FldrDyadic.sum_padded
#print axioms SampLib.FldrDyadic.padded_lt
