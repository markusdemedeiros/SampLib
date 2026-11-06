# Independent expansion counting audit

Reviewer: `/root/expand_review_discrete`. Read-only assessment of **Checkpoint008**,
recorded on 2026-11-06. These are historical checkpoint counts, not a claim about
later campaign state or completion.

## Counts and coverage

- The frozen baseline contains 47 sampler names.
- The 171 scoped expansion rows comprise 159 accepted, 10 assigned and two
  excluded entries. Thus the accepted suite contains **206 named samplers**.
- At this checkpoint the additions were labelled 115 core and 44 derived. These
  labels agree between canonical rows and their primary cumulative receipts;
  the Metropolis correction below remains pending.
- The three cumulative reviewer files contain 160 rows but only 159 distinct
  names. The sole duplicate is `Occil.Weighted.uniformBinaryFloat`, independently
  signed by both the discrete and structured reviewers at the same frozen hash.
  Canonical integration retains the assigned primary review and counts it once.
- Canonical sampler names and public-spec names are unique. Shared proof modules
  for UniformFormats and WordReductions contain separate named source samplers;
  module sharing does not create additional counts.

The 10 pending rows are aliasSamples, fenwickDraw, fromPositiveSeries, eScaled,
inverseEPlusRational, exponentialRationalProduct, piAffine, reciprocalPiScaled,
threeZetaThreeOverFour and eOverPi, under their namespaces in
[ExpansionCampaign.json](../ExpansionCampaign.json). Their existence or partial
proofs do not constitute acceptance.

## Counting boundaries

Deterministic counters, validation, lookup, choose/power, bit-length and rounding
helpers are absent from the accepted sampler-name set. Alias/Vose draw helpers
and selectors are not counted separately. `sliceStep` remains reviewed support
for the single counted `sliceSampler` technique. The other exclusion is the
incorrect advertised law of `FactoryExtra.linearLowProbability`; both exclusion
reasons have concrete evidence in the ledger.

The first source pass found no identical accepted declaration bodies. Its
classification check was too narrow: focusing on literal aliases missed thin
repetition wrappers. The post-checkpoint addendum below corrects that finding.
This is a source/counting review, not a theorem that different programs can
never be extensionally equivalent.

## Frozen evidence and context

The baseline audit log still has SHA-256
`b0fba389b9bf7831f5174ba2e66808c8aaa7ff5a2be355e793371debf5944425`,
and its 47 names equal the frozen baseline list. All 83 distinct source paths
in the baseline snapshots match their recorded hashes. The six old review
receipt contexts and the two original baseline records remain unchanged.

Across all 44 canonical review receipts, caller hashes, recorded source/support
hashes for **443 distinct paths**, and review contexts match current files.
The five pinned configuration/policy files match, and all 13 Git dependency
checkouts match manifest revisions with no tracked or untracked Lean changes.
These checks independently compare stored hashes and metadata; the full compiled
specification/caller/axiom audit is the separately recorded
[Checkpoint008 log](ExpansionCheckpoint008.log), which passed all 206 specs.

`verify_expansion_state` independently returns 159. With `require_complete=True`
it correctly refuses completion with:

```text
Expansion still has 10 unassessed or unfinished candidates
```

The additional-sampler minimum is therefore not a completion certificate.

## Pending Metropolis correction

At Checkpoint008, `Occil.General.metropolis` is labelled core, although
[its runtime definition](../../code/Samplers/General/Core.lean#L273) directly
specializes metropolisHastings with the constant proposal ratio `(1,1)`.
Under the thin-wrapper counting policy its label should be derived.

Its recorded domain also says countable encoded states, whereas the accepted
[Metropolis wrapper](../../SampLib/Samplers/Metropolis.lean#L29) requires
`Fintype α`. This overstates that theorem's domain. Root and the primary reviewer
are preparing countable wrappers and a new immutable correction receipt; this
note does not sign those changes or treat the correction as complete.

No existing signed proof, caller or receipt was edited by this audit.

## Post-Checkpoint008 classification addendum

The structured reviewer identified two missed wrappers. Direct source and proof
inspection confirms both should be **derived**:

- [bootstrap](../../code/Samplers/General/DataModels.lean#L16) computes the data
  length and repeats the already-counted sampleWithReplacement sampler.
- [permutationSamples](../../code/Samplers/General/DataModels.lean#L23) repeats
  the already-counted shuffle sampler.

Their proofs specialize `repeatSample_distSpec`; neither introduces another
sampling engine. The primary reviewer is preparing a new immutable correction
receipt, finalWalker014. These are metadata corrections with no added sampler
count. The historical Checkpoint008 counts above are deliberately retained.

Applying the same criterion identifies four further derived candidates:

- `General.latinHypercube`
  ([Points:160](../../code/Samplers/General/Points.lean#L160)) repeats the counted
  latinHypercube1D sampler, then deterministically transposes.
- `General.groupedPermutation`
  ([DataModels:38](../../code/Samplers/General/DataModels.lean#L38)) calls shuffle
  once, then deterministically partitions.
- `Weighted.cumulativeChoice`
  ([Tables:42](../../code/Samplers/Weighted/Tables.lean#L42)) builds a deterministic
  prefix table, then calls counted cumulativeDraw.
- `Weighted.rationalChoice`
  ([Tables:64](../../code/Samplers/Weighted/Tables.lean#L64)) deterministically
  normalizes fractions, then calls counted weightedChoice.

The structured reviewer is assessing the first two. Root agreed with derived
classification for the last two. The new immutable
[Discrete015 correction receipt](ExpansionDiscreteBatch015.json) now records
both changes, retaining the original proof hashes, domains, receipts and caller
evidence. Its fresh public clients and all 48 cumulative discrete-review receipt
closures pass. Canonical promotion is managed separately by root after its
active audit. These changes are not counted as additional samplers.

The last two are from this reviewer's own stream. Their substantial pure helper
proofs do not introduce another stochastic engine and should not determine the
core label. Their sampler specifications and mathematical validity are unchanged.
UniformFixed and UniformDyadic were already labelled derived, as was
UniformRational; no correction is needed for those format wrappers.

Calibration matters in the other direction. kernelDensityVector chooses one
shared center and then draws independent coordinate jitters; repeating scalar
kernelDensity would redraw the center for each coordinate and give a different
joint law. latinHypercube1D adds a fresh shuffle after stratification. These
remain reasonable core compositions. voseSamples counts the entire alias-table
technique once, while its table/draw helpers remain uncounted. couplingFromPast
adds coalescence/history/retry logic rather than merely repeating a sampler.

The addendum itself edits only this unsigned note. Separately authorized new
correction evidence does not amend any original signed proof, caller or receipt;
canonical classification updates remain root's responsibility.
