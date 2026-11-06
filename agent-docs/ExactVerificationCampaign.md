# Exact verification campaign tracking

The ledger, [ExactVerificationCampaign.json](ExactVerificationCampaign.json), sets the
authoritative scope: 137 named entries from the frozen [queue](ExactVerificationQueue.md).
The ledger keeps missing proofs, known defects, and existing support theorems distinct. A
finding never silently removes an item from the user's goal.

Each candidate records its owner, status, intended public specification, proof kind,
reviewer, domain, and immutable review receipt. This campaign starts at `clutch-lean`
commit `06a7b3e2`. Historical receipts keep their original context, and the campaign
never rewrites them. The baseline records the earlier 216-entry campaign and the original
hashes of the implementation files. You can add new proof files without changing the
original algorithm. Coordinate any necessary implementation repair before you change the
baseline.

The low-probability linear factory now uses the half-margin
[repair](reviews/ExactLowProbabilitySourceRepair001.md), which has an independent review.
The campaign keeps the original bytes and the baseline hash. `implementation_repair_reviews`
records the exact replacement and its independent review. That record never accepts a
sampler proof or renews a stale transitive snapshot. The repaired named sampler has a
full-domain public [specification](../SampLib/Bernoulli/LinearLowProbability.lean) and
[interpreter regressions](reviews/LowProbabilityRuntime001.json).

The optimal-matrix encoder also has a probability-one
[repair](reviews/ExactOptimalSourceRepair001.md) with an independent review. The repair
replaces an overflowing row with the all-ones cyclic representation, and the review archive
keeps the original source bytes. This repair alone accepts neither optimal sampler proof.
No earlier accepted proof closure contains the changed implementation file.

## Review handoff

Owners report a built proof module, the public spec, the complete input domain, and the
expected classification (`core`, `derived`, or `support`). Reviewers independently inspect
the mathematics and the straight-line CTE proof. They compile a caller that exercises
arbitrary framed resources and the relevant boundaries, and they print the exact
transitive axioms.

Reviewers give their artifacts immutable numbered names under `agent-docs/reviews/`. For
example, `ExactFactoriesBatch001.json` comes with its Markdown evidence and its Lean
caller. Do not overwrite a receipt after acceptance. After edits, issue a new numbered
receipt.

A receipt has this shape. All hashes are full SHA-256 hashes.

```json
{
  "reviewer": "/root/review_exact_a",
  "context": "the object returned by proof_dependencies.review_context()",
  "caller_evidence": "agent-docs/reviews/ExactFactoriesBatch001Callers.lean",
  "caller_sha256": "...",
  "support": [],
  "accepted": [
    {
      "sampler": "Occil.example",
      "proof_module": "SampLib.Bernoulli.Example",
      "public_spec": "SampLib.Example.example_distSpec",
      "spec_kind": "plain",
      "classification": "core",
      "reviewed_domain": "Complete input domain and output encoding",
      "sha256": "...",
      "review_evidence": "agent-docs/reviews/ExactFactoriesBatch001.md",
      "checks": ["source", "build", "axioms", "caller", "boundaries", "protocol"],
      "source_snapshot": "the object returned by source_snapshot(module, implementation)"
    }
  ]
}
```

The quoted placeholders stand for actual JSON objects in a real receipt. `spec_kind`
supports these interfaces:

- `plain`: `IsDistSpec`.
- `owned`: `IsOwnedDistSpec`.
- `latent_coin`: `UniformBag.IsCoinSpec`, which keeps the shared uniform and the heap.
- `latent_real`: `LatentReal.IsLatentDistSpec`, which bundles construction with future
  observations of the actual returned oracle.
- `latent_vector`: `LatentReal.IsLatentVectorSpec`, which keeps one joint world and the
  returned coordinate handles.
- `conditional_coin`: `LatentReal.IsLatentCoinProgramSpec`, which keeps arbitrary joint
  credits on the output and the latent values over a refined source posterior.

Real, vector, and conditional-coin receipts require `observation` and `aliases`. Vector
receipts also require `joint` and `coordinates`, and conditional-coin receipts require
`joint`. The structural auditor opens the source lambda of the conditional program before
it checks the exact sampler head. It rejects premises that assume the sampler's own
specification. A scalar marginal law cannot replace these protocols. Any other stateful
interface needs an explicit auditor extension before acceptance.

The prose review must name the exact public spec and the proof hash. The receipt binds
the entire project-local import closure, not only the direct proof file. A change to
shared support invalidates every affected receipt, even when the text of the top-level
proof stays the same. Coordinate such changes before a review pass.

## Integration

When an independent receipt is ready, the ledger owner runs this command:

```sh
python3 agent-scripts/lean_gate.py -- python3 agent-scripts/integrate_exact_receipt.py \
  agent-docs/reviews/ExactStructuredBatch001.json
```

The helper validates every acceptance before it changes the new ledger. It keeps earlier
receipt paths on rollover and reports missing public-root imports. It does not edit the
historic campaign, the root imports, or the public indexes. The helper normalizes reviewer
identities, so short team names and canonical `/root/` names cannot bypass the
independence check.

## Reproducible audit

For a cheap check of the metadata and receipts, run this command. It does not claim Lean
validation.

```sh
python3 agent-scripts/lean_gate.py -- python3 agent-scripts/audit_exact_sampler_proofs.py \
  --metadata-only
```

For the full audit of the current state, run this command under the shared memory gate:

```sh
python3 agent-scripts/lean_gate.py -- python3 agent-scripts/audit_exact_sampler_proofs.py
```

The full audit builds the project and checks in Lean the exact theorem and program heads
and any circular premises. It checks transitive axioms, compiles every independent caller,
and rechecks the sources and context after compilation. Add `--require-complete` only for
the final audit that confirms all 137 entries. A successful intermediate audit certifies
only the accepted rows that it reports. It does not imply that the entire goal is done.

## Historical dependency revalidation

`exact_baseline.py` creates a separate compatibility overlay for the 216 earlier
specifications. It leaves the original campaign and its 48 review receipts untouched. The
overlay records the current source snapshots and context. It reruns every specification
head, the axiom checks, and all 49 independent caller artifacts. It does not
assert that the historical reviewers inspected a different upstream checkout.

After the sources are stable, run this command with a fresh numbered pair of output and
log files:

```sh
python3 agent-scripts/lean_gate.py -- python3 agent-scripts/exact_baseline.py \
  --output agent-docs/reviews/ExactBaselineRevalidation001.json \
  --log agent-docs/reviews/ExactBaselineRevalidation001.log \
  > agent-docs/reviews/ExactBaselineRevalidation001.log 2>&1
```

A whole-file hash update cannot silently allow a change to an implementation file. Such a
change needs an independent source-change review in the current context. The review lists
each affected historical sampler with its original and current transitive snapshots. It
also attests that the direct definition and the reviewed domain of each sampler are
unchanged. Pass that evidence to the command with `--source-change-review PATH`. A changed
sampler definition needs a full new proof review instead of this conservative migration
path.

`validate_baseline_overlay()` checks all overlay evidence against the current worktree and
then returns the exact public proof paths. Public generators can use that result without
weakening or rewriting any historical receipt. The `baseline_revalidation` field of the
ledger selects the current immutable overlay, and
`python3 agent-scripts/exact_baseline.py --check` checks that selected record.

## Moving modules

Receipts pin each reviewed file by its path, so a plain move voids them. To move modules,
run this command from a clean tree:

```sh
python3 agent-scripts/relocation.py --apply MOVES.json --output agent-docs/relocations/NNN.json
```

The command moves the files and rewrites their import lines and the Markdown links that you
name. It then records the hash of every changed file before and after the move. The audits
translate recorded modules, snapshots, and contexts through these records.
`python3 agent-scripts/relocation.py --check` replays each record from its base commit, so
a record cannot hide an edit to proof text. Like receipts, records are immutable.
