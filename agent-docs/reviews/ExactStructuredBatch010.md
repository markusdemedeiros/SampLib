# Independent exact sampler review: ExactStructuredBatch010

Reviewer: `/root/review_exact_b`. Both accepted as plain `IsDistSpec`, classification core,
law `WeightedChoice.law ws` on original integer position labels.

## `Occil.Weighted.fastLoadedDiceRoller`

Public spec `SampLib.FastLoadedDice.fastLoadedDiceRoller_distSpec` in
`SampLib.Samplers.FastLoadedDiceRoller`, SHA-256
`43af143ad4e0f81f49dec79fa296cfb0c846c9b8561668e47add1212de1dd461`.

Domain: every finite natural-weight list with positive total, including zero rows, certain rows
and singletons. Negative or zero-total inputs fail `validWeights`, so the domain is complete.

Source match. `Syntax/FastLoadedDice.source_eq` checks the literal term by `kernel_rfl`. The
source pads the total to `2^clog2 total` and scans the original rows, then one implicit row
`(padded - total) / place % 2`. That row restarts from `draw (padded/2) 0`. The proof models it
as `augmented ws P = ws ++ [P - sum]`. `source_columns` shows that the source bits equal the
dyadic matrix columns at every depth `d < k`. `extended` pays `credit + 2ε` on the dummy label
and never returns it; `twp_scan`'s nil case spends exactly the caller's restart rule. A certain
row returns early through the shared `KnuthYao.find` shortcut. Without a certain row, the total
is at least 2, so the starting place is positive. `depth_lt` proves that the `place <= 0` fail
branch is unreachable.

Mathematics. `FastLoadedDiceCredits.expectation` is one short calc: padding mass `P - T ≤ P/2`
gives `E ≤ C(F) + ε` with retry credit `C + 2ε`. Termination uses
`ErrorCredit.Induction.simple (k := 2)`. The finite matrix walk reuses the DDG cutoff/liminf
argument (`DdgContext.twp_of_columns`), which keeps the linear restart capability. All credits
stay in ENNReal.

## `Occil.WeightedVariants.sortedChoice`

Public spec `SampLib.SortedChoice.sortedChoice_distSpec` in `SampLib.Samplers.SortedChoice`,
SHA-256 `b941da3c35ea08595b001baacbea71d7361f45063a6aa7869ca7378b836ab827`.

Domain: every positive-total monotone list (`SortedWeights.Sorted`: nondecreasing or
nonincreasing). This includes zero rows, constant lists, all-zero envelope groups and the
length-one shortcut. The source orients by `w[0] <= w[n-1]` and then checks adjacent pairs. A
list that is not monotone has a violating adjacent pair in the chosen orientation, including
equal-endpoint cases like [2,0,2], so it fails. The domain is therefore complete.

Source match. `twp_open` goes through `source_eq` (`kernel_rfl`), and `twp_groups` computes
exactly `GroupedEnvelope.masses`. Every retry calls the FLDR `IsDistSpec` above through
`hdraw.wp_supported`, so no scalar-marginal shortcut is used. The proof then uses the
inclusive-range spec for `rndIntRange`, the source index reversal and `rationalCoin(w, pivot)`.
`envelope_bound` shows that the pivot dominates its group.

Mathematics. `GroupedEnvelope.expectation_preservation` treats each group as a rectangle of
true weights plus unused tickets. Accepted mass pays `C(F)`, and the spare mass `S/D` funds
retry amplification by the factor `1 + 1/D`. A zero-envelope group contributes zero even with
infinite credit. `SortedChoice.expectation_preservation` only relabels the orientation.

Inline facts in `SortedChoice.twp_loop` (`hkn`, `he`, `hpow`, `hu`, `hdiff`): these are
one-line bound and cast normalizations that the next rule application needs. They are not
expectation reasoning. That reasoning lives entirely in `expectation_preservation` and
`candidate_expectation`. Accepted proofs (SuccinctChoice, VonNeumann) use the same pattern, so
this does not violate "keep mathematical work outside the main twp_* theorem".

## Checks

Both targets build warning-free through `lean_gate.py`. All lines are at most 100 columns, with
no debugging residue. `#print axioms` for both public specs, both `twp_loop`s, both expectation
lemmas and all three caller theorems shows only `propext, Classical.choice, Quot.sound`.

Independent caller `ExactStructuredBatch010Callers.lean` frames an arbitrary Iris resource `Q`
through each spec. `composed` sequences FLDR, then sortedChoice, under an arbitrary joint credit
`G i j`, paying the second call conditionally on the first result. It covers these boundaries:

- FLDR: [0,1,2,0] with infinite credit (padding 3→4), [1,0,3] (no padding), the certain row
  [0,0,9,0], the singleton [5], and [3,0,0,0,0,0,0,2].
- sortedChoice: [4,2,1,0], [0,0,1,3] with infinite credit, [2,2,2], [3], [5,0,0,0,0,0,0]
  (zero envelope groups), [0,…,0,1] (length 9, four groups), and [9,7,7,4,2,1,0] inside
  `composed`.

Pure checks confirm the augmented matrix for padding, envelopes [9,14,16] and [5,0,0], zero
cost for infinite credit on zero rows and the dummy label, and that [1,2,1] and [2,0,2] fall
outside `Sorted`.

The receipt binds the full local source closure, the caller hash and the dependency context.
