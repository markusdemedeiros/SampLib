# Expansion discrete review: immutable batch 007

Reviewer: `/root/expand_review_discrete`. Three accepted core samplers.

## `Occil.Weighted.weightedReservoirOne` — accepted (core)

Public specification: `SampLib.WeightedReservoirOne.weightedReservoirOne_distSpec`.

Source SHA-256: `5601626f681bdede30b4d8c3a2e2cb76022d46cb5ecdc901cf616a0c5c2e428d`.

The canonical categorical law is mapped to integer labels. The previously selected integer represents one virtual item carrying the processed prefix weight. Conservation of the competing label weights is the central expectation identity. Initial prefix weight zero removes sentinel -1 even for infinite continuation credit. Reviewer feedback moved the rational-coin bias/cast conversion into a private specification helper; its final proof uses an explicit subtype equality followed by the exact existing coin specification. Tests check infinite sentinel credit contributes zero, [0,2,0] has expectation F1 for arbitrary ENNReal F, a leading-zero initial state and generic resource framing.

## `Occil.WeightedVariants.divisionRejection` — accepted (core)

Public specification: `SampLib.DivisionRejection.divisionRejection_distSpec`.

Source SHA-256: `2af2a3374cc3912680a884b57c13e151178fe2c24328810d3714fcb6eae6ab46`.

The accepted source prefix consists of n equally sized quotient blocks; the incomplete upper interval is rejected. Grouping complete blocks proves the canonical UniformInt(n) target credit. The rejected interval occupies at most half the word range, funding the ordinary factor-two retry proof. Tests check n3/width4 rejection at word3, the full n5/width8 kernel with exactly three rejected upper words, arbitrary-ENNReal quotient-block expectations, the zero-bit singleton endpoint, infinite credits and generic frames.

## `Occil.WeightedVariants.debiasedModulo` — accepted (core)

Public specification: `SampLib.DebiasedModulo.debiasedModulo_distSpec`.

Source SHA-256: `3e4157f707f0e7f6e069f737aa9adcd7e0eb88d97862c372b4e805617772d91e`.

Discarding the incomplete low prefix t=width%n leaves complete residue cycles rotated by t. Finite rotation and block sums prove each label has equal accepted multiplicity; only finite positive normalization coefficients are cancelled. Rejection occupies at most half the source range, so the CTE proof uses the standard doubled-credit retry. Tests distinguish low-prefix rejection from division rejection: at n5/width8 words0,1,2 are rejected and original word5 returns residue0. The complete numerical kernel, n3/width4 word3 returning0, zero-bit singleton, arbitrary infinite credits and frames are checked.

## Supporting finite-word mathematics

WordIntervals groups a finite range into consecutive rectangular blocks and proves uniform quotient and residue expectations. WordRotation identifies a cyclically shifted residue sum by a finite rotation argument, then applies the block decomposition. Width-zero extensions remain correct where stated; positive finite coefficients are required exactly at cancellation sites. Every identity accepts arbitrary ENNReal continuation values, including infinity, and no continuation is converted to real arithmetic.

Support hashes:

- `SampLib.Distributions.WordIntervals`: `b2cb0d0c72cdcb662ba9a7b3cbe73505705de648269c784f70220a5729b3f06c`.
- `SampLib.Distributions.WordRotation`: `18290d61ba8156f0e53be0e4c18ac523daab50b5359e3d2c1a812fc4205ec759`.

## Validation

Independent gated builds of included modules passed without warnings at default heartbeats. Working and immutable copied caller artifacts compile without warnings. Printed public specifications and new expectation/helper lemmas depend only on propext, Classical.choice and Quot.sound. Source formatting and whitespace pass. All targets are normalized probability laws with typed integer encoders, arbitrary measurable ENNReal credits and arbitrary unrelated Iris resources.
