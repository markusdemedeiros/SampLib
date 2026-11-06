# Final independent expansion counting audit

Reviewer: `/root/expand_review_discrete`. Snapshot: 2026-11-06, after canonical
promotion of Factories014, Structured014 and Discrete015. This is an independent
read-only count, coverage and source-context audit.

| Item | Verified result |
| --- | --- |
| Frozen baseline | 47 sampler names |
| Accepted additions | 169: 110 core, 59 derived |
| Accepted total | 216 distinct names |
| Scoped expansion | 171: 169 accepted, two excluded, zero pending |
| Canonical review receipts | 48 |
| Current source/support paths checked | 502 |
| Frozen baseline source paths checked | 83 |

`verify_expansion_state(..., require_complete=True)` passes and returns 169.
All 169 addition names, public specifications and primary-review selections are
unique. The 214 manifest candidate records plus the two original baseline
entries give 216 names; no baseline sampler is counted again as an addition.

The reviewer unions contain 170 rows for 169 names. Their sole duplicate is
`Occil.Weighted.uniformBinaryFloat`, signed independently by two reviewers at
the same frozen source hash. Only its assigned primary is canonical.

All current primary receipts pass `verify_receipt`, including recomputed local
import closures, proof/support hashes, immutable caller hashes and review
contexts. All five pinned configuration/policy files and all 13 clean Git
dependency revisions match. The frozen baseline log still hashes to
`b0fba389b9bf7831f5174ba2e66808c8aaa7ff5a2be355e793371debf5944425`;
its names and all 47 baseline proof closures remain unchanged.

The corrected thin wrappers are derived: Metropolis, Bootstrap,
PermutationSamples, LatinHypercube, GroupedPermutation, CumulativeChoice and
RationalChoice. UniformRational, UniformFixed and UniformDyadic remain derived.
The current Metropolis/MH primary wrappers require `Countable`, correcting the
earlier finite-wrapper/domain mismatch. Current promoted receipts, rather than
superseded historical source/classification records, were checked.

No identical accepted runtime declaration bodies were found. Deterministic
counters, validation, choose/power, rounding/bit-length, table constructors and
selectors do not increase the count. Alias/Vose draw helpers remain uncounted;
fenwickDraw counts once as an owned categorical sampler, preserving its
representation invariant. KernelDensityVector retains its shared-center random
dependence and is not a thin repetition of scalar KernelDensity.

The two exclusions are `Occil.General.sliceStep` (reviewed supporting transition,
counted through sliceSampler) and `Occil.FactoryExtra.linearLowProbability`
(incorrect advertised law with recorded counterexample evidence). Neither is
silently left pending or counted as accepted.

Counting-snapshot SHA-256 values:

- VerificationCampaign.json:
  `9190781501cb54f11439f655b8a3478eaac9e035146e25725025e9842a50cf49`
- ExpansionCampaign.json:
  `0d6ce9732cc71a4f5ad7cc15b674ab336c34355908645c1b19a9ddc21ae0fef5`

No proof, receipt, caller or manifest was edited. Lean was used only to parse
imports for the snapshot checks; the separate full compiled specification,
caller and axiom audit is recorded in
[ExpansionCheckpoint010Final.log](ExpansionCheckpoint010Final.log).
