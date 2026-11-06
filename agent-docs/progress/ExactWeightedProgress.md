# Exact weighted sampler work

> Round-2 working notes, kept as a record and not updated since 2026-11-06. For current
> status see [LAWS.md](../../LAWS.md) and [the deferral list](../ExactCampaignDeferrals.md).

Owner: `prove_weighted`. Original scope: 12 entries in ExactVerificationCampaign.
`knuthYao` and `fastLoadedDiceRoller` transferred to `prove_powers`;
`optimalChoice` and `optimalDraw` transferred to `prove_constants`;
`recycledUniform` and `recycledSamples` transferred to `prove_series` for parallel work.

## Accepted; sources frozen

- `Occil.WeightedVariants.voseDraw`: existing owned interface, independently accepted in
  [ExactStructuredBatch002](../reviews/ExactStructuredBatch002.json). Retained state and independent
  repeated calls checked; no fresh proof claimed.
- `Occil.Weighted.inclusionSystematic`: new exact joint-law CTE proof, independently accepted in
  [ExactStructuredBatch003](../reviews/ExactStructuredBatch003.json). Positive-total natural weights,
  count≤population size and count*weight≤total; sample has exactly count labels, each inclusion
  probability is count*weight/total. Separate count0 theorem covers empty/all-zero populations
  without requiring the uniform-int primitive. Frozen modules: Distributions/SystematicPPS,
  Syntax/InclusionSystematic, Samplers/InclusionSystematic.

- `Occil.Weighted.inclusionSplitting`: exact ordered joint law and CTE independently accepted in
  [ExactStructuredBatch005](../reviews/ExactStructuredBatch005.json). Same natural-weight PPS
  domain; zero/full boundary cases included, and a separate no-uniform-int zero-size spec
  covers empty/all-zero populations. Finite denominator descent proves total correctness.
  Exact size, distinct labels and every prescribed inclusion probability are exposed.
  All12 math/source/CTE modules are frozen, including separately reviewed Bounds/Marginals.

- `Occil.Weighted.hanHoshi`: exact canonical categorical law independently accepted in
  [ExactStructuredBatch007](../reviews/ExactStructuredBatch007.json), for every positive-total
  natural-weight vector including zero rows and certain outcomes. Whole-cell certification
  settles a dyadic posterior; finite CDF boundary bands prove almost-sure termination with
  arbitrary infinite credits. All9 math/source/CTE modules are frozen.

- `Occil.WeightedVariants.succinctChoice`: exact canonical categorical law independently
  accepted in [ExactStructuredBatch009](../reviews/ExactStructuredBatch009.json). Complete source
  domain: positive-total natural weights and either2^19*len≤sum or every weight<2^32.
  Exact mixed-width decode and both dense/packed rejection loops are verified; arbitrary∞
  credits and dense weights beyond2^32 are included. All8 own closure modules are frozen.

## Ready for independent review (round 2, team `weighted`)

- `Occil.Weighted.fastLoadedDiceRoller`: `SampLib.FastLoadedDice.fastLoadedDiceRoller_distSpec`
  in `SampLib.Samplers.FastLoadedDiceRoller`; plain `IsDistSpec`; core. Domain: every finite
  natural-weight list with positive total, including zero rows and certain rows. Same
  `WeightedChoice.law` and labels as `knuthYao`. The padded matrix is walked through
  `DdgContext.twp_of_columns`; the implicit rejection row has mass at most 1/2, so retries use
  `ErrorCredit.Induction.simple (k := 2)` (`FastLoadedDiceRoot`). Round-2 edits: fixed the
  halving cast in the wrapper, removed debug `logInfo` lines, and dropped unused syntax helpers.
- `Occil.WeightedVariants.sortedChoice`: `SampLib.SortedChoice.sortedChoice_distSpec` in
  `SampLib.Samplers.SortedChoice`; plain `IsDistSpec`; core. Domain: every positive-total
  natural-weight list that is monotone (`SortedWeights.Sorted`: nondecreasing or nonincreasing),
  including zero rows, constant lists and the length-one shortcut. Unsorted lists make the
  source `fail`, so this is the complete domain. The group draw uses the FLDR `IsDistSpec`
  above at every retry. Termination factor `1 + 1/total envelope`; one expectation lemma,
  `SortedChoice.expectation_preservation` (`Distributions/SortedEnvelope`). Round 2 finished `SortedChoice.twp_loop` (index
  step and coin acceptance step) and added the source wrapper.
- `optimalChoice` accepted (Batch011); general `optimalDraw` resubmitted: see
  [ExactOptimalProgress](ExactOptimalProgress.md).

Checks: each target builds clean through `lean_gate.py`. `#print axioms` gives only
`propext, Classical.choice, Quot.sound`. Shared caller
`reviews/WeightedRound2Callers.lean` frames an arbitrary resource, covering FLDR on
[0,1,2,0] (padding 3→4, with infinite credit on zero rows and the dummy label), [0,0,9,0],
[1,0,3] and [5], and sortedChoice on [4,2,1,0], [0,0,1,3] (infinite credit), [2,2,2], [3]
and [9,7,7,4,2,1,0].
The older `reviews/ExactFastLoadedDiceCallers.lean` (not ours) does not elaborate. Its framed
statements fail to parse `∗` under `iprop`. Use the round-2 caller instead.

## In progress

- `recycledUniform`, `recycledSamples`: transferred to `prove_series`, who now owns both
  EntropyPool modules and their author caller. Handoff includes full fixed-state joint-kernel,
  finite-leaf tail and averaged-pool IID-batch plan. Checked joint quotient/remainder rectangle identity in
  `Distributions/EntropyPool.lean`; checked deterministic accepted-rectangle heap lemma
  in `SampLib/EntropyPool.lean`; its author caller passes, including the concrete
  pool(0,2) dependency example. A fixed concrete pool is **not** conditionally uniform. Do not
  assume an unchanged-predicate `IsOwnedDistSpec` for each draw; use joint output/residual-state
  credits, then a batch theorem starting from pool(0,1).

No implementation sources changed. Supporting lemmas and drafts are not completed samplers.
Every Lean process goes through `agent-scripts/lean_gate.py`; poll existing sessions until terminal.
