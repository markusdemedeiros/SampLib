# Independent exact sampler review: ExactStructuredBatch011

Reviewer: `/root/review_exact_a`. Accepted core theorem
`SampLib.Optimal.optimalChoice_distSpec` (plain `IsDistSpec`), proof file
`SampLib/Samplers/OptimalChoice.lean`, SHA-256
`25a858d89237ff490b3960e5330a291e225a83b456317bf6a2de706edae2d60a`. Source
`code/Samplers/Weighted/Optimal.lean` hashes to the approved repaired bytes
`a9b71b1c8b8bfa72602ac4693c83ff2eb0dccb5a98fab661d37c7c534aa44571`
([repair review](ExactOptimalSourceRepair001.md)).

Domain: every finite natural-weight list with positive total, as integer list values.
This includes zero rows, a certain row (the repaired all-ones endpoint), the
length-one shortcut, exact totals `2^k-2^l` and padded totals with an appended
rejection label. Law: `WeightedChoice.law ws` on original position labels, for
arbitrary measurable ENNReal continuation credit, including infinity. Negative or
zero-total inputs make the source `fail` and are correctly excluded.

`Occil.WeightedVariants.optimalDraw` (`optimalDraw_distSpec`) is not accepted here;
see the final section.

## Mathematics

- `Distributions/OptimalEncoding`: with `A=2^l` and `P=2^(k-l)`, the row encoder
  and cyclic decoder are inverse on `[0, A(P-1)]`. The endpoint uses `AP-1`, so the
  certain row is all ones and fits `k` bits.
- `Distributions/OptimalCyclic`: `tail_zero` compares the scaled binary prefix
  identities at depths `k` and `l`. They agree after one block, which yields the
  exact row mass `decode/D`. The absolute-depth `column` matches the source's jump
  back to `l`.
- `Distributions/OptimalCredits`: the remaining row masses sum to the live-rank
  count. This gives the width identity, a uniform bound by `n`, and one-bit
  conservation of arbitrary ENNReal row credit.
- `Distributions/OptimalParameters`: the source's denominator search keeps a valid
  witness `l<k`, `D=2^k-2^l>=total`. With `selected_le_twice`, the rejection
  probability is at most 1/2.
- `Distributions/OptimalRejection.expectation`: one short `calc` covers termination.
  A rejection leaf receives `C+2ε`, so the expectation is at most `C+ε`.

All credits stay in ENNReal. Real numbers appear only for the finite row masses, and
these are moved to NNReal with an explicit proof of nonnegativity.

## Program proofs

Each proof is straight-line symbolic execution:

- `twp_optimalMatrix` runs validation, sum, bitLength, power, the parameter loop,
  padding, the rejection index and the encoder.
- `twp_scan` does structural recursion over rows.
- `twp_round` takes one `rand(2)`, one scan, then branches to restart, return or
  the next column.
- `twp_walk` instantiates the finite-horizon DDG rule (`DdgContext`), and the
  linear restart capability `R` survives.
- `twp_root` uses `twp_err_pos` and `ErrorCredit.Induction.simple (k := 2)`.
- `twp_choice` follows the source: validation, then the length test, then either
  the singleton credit lemma or the matrix and the draw.

Kernel `rfl` checks the source views in `Syntax/Optimal*` against the canonical
terms. Lines stay within 100 columns. The targeted build has no warnings.

There is some leftover scaffolding: `drawSource`/`draw_source_eq`,
`draw_sourceCode_eq`, `matrix_source_eq`, `Program.walk`/`walk_eq`,
`selected_positive` and `OptimalCyclic.columns_list` are unused. This is a minor
cleanup item and does not block acceptance.

## Checks

- Build: `lake build SampLib.Samplers.OptimalChoice` passes with no warnings.
- Caller: [ExactStructuredBatch011Callers.lean](ExactStructuredBatch011Callers.lean)
  compiles with `lake env lean`.
  - It frames an arbitrary Iris resource.
  - It composes two independent draws, funding the second per first outcome.
  - It covers `[2,0]` (certain row behind cycle start 1), `[0,0,5]` with infinite
    credit everywhere, the singleton `[7]` and the padded non-dyadic `[1,0,4]`.
  - Kernel `decide` checks confirm `create [2,0] = ([3,0],2,1,-1)` and
    `create [1,0,4] = ([1,0,5,1],3,1,3)`, and that `[3,3]` needs no rejection row.
  - Infinite credit on zero-weight and padding labels integrates to 0.
- Axioms: the public spec, `twp_optimalMatrix`, `twp_root`, `twp_walk`,
  `restart_expectation` and both caller theorems use only `propext`,
  `Classical.choice` and `Quot.sound`.

## Not accepted: optimalDraw

The domain of `optimalDraw_distSpec` covers only tables of the form
`Table.value (create ws)`, so it is incomplete for a sampler that takes a table
argument:

- LAWS.md lists the row as "valid table required". The source docstring
  describes `optimalDraw` as a traversal of any finite cyclic probability matrix.
- Accepted precedent states table samplers over semantically valid tables.
  `voseDraw_ownedDistSpec` accepts every alias table with the correct mass, not
  only the output of `voseTable`. `cumulativeDraw_distSpec` accepts every CDF `Model`.
- `OptimalWalk.twp_walk` already handles arbitrary rows `Fin n → ℕ`, any `l<k`,
  any rejection label and only `Σ tail = 1`. Only `twp_root`/`restart_expectation`
  and the public theorem specialize to `create ws`.

A complete domain would allow arbitrary rows, any `l<k`, row masses summing to 1,
and either no rejection label or a label whose row mass is below 1. Its law would
be the normalized row masses with that label removed. The retry factor would be
`1/(1-p_rej)` instead of 2. As stated, the theorem is a corollary of the
`optimalChoice` proof, not a specification of `optimalDraw`.
