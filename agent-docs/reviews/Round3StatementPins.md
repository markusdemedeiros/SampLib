# Round 3 statement check

The round 3 refactor keeps every accepted public statement. This record shows how we
checked it and why the statement pins come from the refactored tree, not from the base.

## Method

`agent-scripts/statement_pins.py` fingerprints each accepted public spec: its type and the
type and body of every `SampLib` definition it mentions, followed transitively. Proofs are
erased, and private names are read as their user-facing names.

We computed the fingerprints in a built checkout of the base commit `8f819b7` and in the
refactored tree. 44 of the specs differed. For each one, we printed every part in both trees
and compared them after erasing binder names, which do not affect meaning.

## Findings

Two differences were real, and we reverted both:

- `SampLib.TwoLevelChoice.twoLevelChoice_distSpec` took `[ProbLangDist.IsUniformInt rT]`
  earlier in its binder list. The spec file now declares it in its original place.
- `SampLib.UniformBag.rank` lost a Mathlib import, so `2 ^ n` on integers used the core
  power instance instead of `Monoid.toNPow`. `SampLib.Latent.Laws.UniformBag` now imports
  `Mathlib.Algebra.Group.Int.Defs`, which restores the original instance.

The other 41 specs differ only in ways that keep their meaning:

- **Measurable space on integers.** Laws that moved out of program-side modules no longer
  see ProbLang's `instMeasurableSpaceLbl`, so they use mathlib's `Int.instMeasurableSpace`.
  Both are `⊤`, and `rfl` proves them equal:
  `example : (instMeasurableSpaceLbl : MeasurableSpace ℤ) = Int.instMeasurableSpace := rfl`.
- **Shared matcher.** `SampLib.PSRNGammaInteger.Core.owns` now reuses the compiler-generated
  matcher `SampLib.LatentGammaInteger.World.match_1`. Its body equals that of the base's
  `SampLib.PSRNGammaInteger.Core.owns.match_1`.

After we mapped these two substitutions, every part of every spec matched the base exactly.

We made both reverts after the reviewers drafted their records. Each revert restores the
base form of a statement and leaves every proof unchanged. We therefore recomputed only the
proof hashes and source snapshots in the records that cover those files, with
`refactor_receipts.py`, and left their reviewer, evidence, and checks unchanged.

For the same reason, we restored `SampLib.ContinuedFraction.unique_value`, which a
historical caller cites and the refactor had removed as a duplicate. It keeps its original
statement and now follows from `SampLib.RealContinuedFraction.unique_value`. Only the source
snapshots in `Round3ConstantsHistorical.json` changed as a result.

## Pins

Because those substitutions change the fingerprint but not the statement, we pinned the
refactored tree. From now on, `statement_pins.py` and the exact-proof audit reject any change
to these fingerprints.
