# Expansion discrete review: immutable batch 015

Reviewer: `/root/expand_review_discrete`.

This receipt corrects two classifications from core to **derived**. It accepts no
additional sampler identity: the cumulative discrete-review count remains 48,
now comprising 38 core and 10 derived entries. Original receipts and callers
remain immutable. Canonical campaign promotion is managed separately by root.

`cumulativeChoice` deterministically validates and builds a prefix table, then
calls the already-counted `cumulativeDraw` engine. `rationalChoice`
deterministically validates and normalizes fractions, then calls the
already-counted `weightedChoice` engine. The pure preprocessing proofs remain
valuable but introduce no new stochastic engine. These are classification
corrections, with no source, domain or mathematical-law change.

## `Occil.Weighted.cumulativeChoice` — derived

Public specification: `SampLib.CumulativeChoice.cumulativeChoice_distSpec`.

Unchanged source SHA-256: `2937a52a25c464a1ca82748aaa9c6093104d675b7a735efa24328b0766a544ac`.

Prior complete review: `agent-docs/reviews/ExpansionDiscreteBatch010.json`.

## `Occil.Weighted.rationalChoice` — derived

Public specification: `SampLib.RationalChoice.rationalChoice_distSpec`.

Unchanged source SHA-256: `f00ed8bd4d4c6855cd638a2e9483abc0abcf7aa8bcea9ed03e8647a3ef187b03`.

Prior complete review: `agent-docs/reviews/ExpansionDiscreteBatch012.json`.

## Retained verification

The current proof/import closures equal the originals exactly, and all original
caller hashes match. Batch010 retains CumulativeChoice's plateau/zero-weight,
exact-mass, infinite-credit and generic framing checks. Batch012 retains
RationalChoice's exact rational proportions, unreduced fractions, singleton,
zero-weight infinite-credit and generic framing checks. Both prior receipts and
caller artifacts are pinned again as supporting evidence here.

The new immutable Batch015 caller checks the same complete public signatures
and prints their transitive axioms: only propext, Classical.choice and Quot.sound.
No implementation, proof source, original receipt or original caller was edited.
