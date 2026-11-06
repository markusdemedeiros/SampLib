module

public import SampLib.Distributions.SplittingPPSBounds

@[expose] public section

open SampLib.SplittingPPS

private def nontrivial : List Item := [(2, 0), (3, 1), (7, 2), (8, 3)]

example : (nontrivial[1]'(by decide)).1 < 10 ∧ 0 < (nontrivial[2]'(by decide)).1 :=
  interior_boundaries nontrivial 2 2 10 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

example : 0 < min (10 - 3) 7 ∧ min (10 - 3) 7 ≤ 10 ∧ 10 - min (10 - 3) 7 < 10 :=
  split_amount_bounds 10 3 7 (by decide) (by decide)

example : ∀ a ∈ adjust 7 2 nontrivial, a.1 ≤ 3 :=
  adjust_bounded nontrivial 2 10 7 (by decide) (by decide)
    (by decide) (by decide) (by decide)

example : ((adjust 7 2 nontrivial).map Prod.fst).sum = 2 * (10 - 7) :=
  residual_mass 7 2 2 10 nontrivial (by decide) (by decide) (by decide)

example : (adjust 7 2 nontrivial).Pairwise ordered := adjust_ordered 7 2 nontrivial

example : ((adjust 7 2 nontrivial).map Prod.snd).Perm (nontrivial.map Prod.snd) :=
  adjust_labels 7 2 nontrivial

private def tied : List Item := [(1, 0), (1, 1), (1, 2), (1, 3)]

example : (tied[1]'(by decide)).1 < 2 ∧ 0 < (tied[2]'(by decide)).1 :=
  interior_boundaries tied 2 2 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def deterministic : List Item := [(0, 0), (1, 1)]

example : (deterministic[0]'(by decide)).1 < 1 ∧ 0 < (deterministic[1]'(by decide)).1 :=
  interior_boundaries deterministic 1 1 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

#print axioms SampLib.SplittingPPS.sorted_boundaries
#print axioms SampLib.SplittingPPS.interior_boundaries
#print axioms SampLib.SplittingPPS.split_amount_bounds
#print axioms SampLib.SplittingPPS.adjust_bounded
#print axioms SampLib.SplittingPPS.adjust_labels
