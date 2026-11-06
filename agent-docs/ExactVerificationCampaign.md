# Exact verification campaign tracking

The authoritative scope is [ExactVerificationCampaign.json](ExactVerificationCampaign.json):
137 named entries from the frozen [queue](ExactVerificationQueue.md). Missing proofs,
known defects, and existing support theorems remain distinct. A finding does not
silently remove an item from the user's goal.

Each candidate has its owner, status, intended public specification, proof kind,
reviewer, domain, and immutable review receipt. This campaign starts at clutch
`06a7b3e2`; historical receipts retain their original context and are not rewritten.
The baseline records the prior 216-entry campaign and the original implementation
file hashes. New proof files may be added without changing the original algorithm.
Any necessary implementation repair must be coordinated before changing the baseline.

The low-probability linear factory now uses the independently reviewed half-margin
[repair](reviews/ExactLowProbabilitySourceRepair001.md). Its original bytes and
baseline hash are retained. `implementation_repair_reviews` records the exact
replacement and independent review; it never accepts a sampler proof or renews a
stale transitive snapshot. The repaired named sampler has a full-domain public
[specification](../SampLib/Samplers/LinearLowProbability.lean) and
[interpreter regressions](reviews/LowProbabilityRuntime001.json).

The optimal-matrix encoder also has an independently reviewed probability-one
[repair](reviews/ExactOptimalSourceRepair001.md). It replaces an overflowing row
with the all-ones cyclic representation, keeping the original source bytes in the
review archive. This repair alone accepts neither optimal sampler proof. No prior
accepted proof closure contains the changed implementation file.

## Review handoff

Owners report a built proof module, public spec, complete input domain, and expected
classification (`core`, `derived`, or `support`). Reviewers independently inspect the
mathematics and straight-line CTE proof, compile a caller exercising arbitrary framed
resources and relevant boundaries, and print exact transitive axioms.

Reviewer-owned artifacts use immutable numbered names under `agent-docs/reviews/`,
for example `ExactFactoriesBatch001.json`, its Markdown evidence and Lean caller.
Do not overwrite a receipt after acceptance; issue a new numbered receipt after edits.

A receipt has this shape (all hashes are full SHA-256):

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
      "proof_module": "SampLib.Samplers.Example",
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

The quoted placeholders denote actual JSON objects in a real receipt. `spec_kind`
supports these interfaces:

- `plain`: `IsDistSpec`.
- `owned`: `IsOwnedDistSpec`.
- `latent_coin`: `UniformBag.IsCoinSpec`, retaining the shared uniform and heap.
- `latent_real`: `LatentReal.IsLatentDistSpec`, bundling construction with future
  observations of the actual returned oracle.
- `latent_vector`: `LatentReal.IsLatentVectorSpec`, retaining one joint world and
  the returned coordinate handles.
- `conditional_coin`: `LatentReal.IsLatentCoinProgramSpec`, retaining arbitrary
  joint output/latent credits over a refined source posterior.

Real, vector and conditional-coin receipts require `observation` and `aliases`;
vector receipts also require `joint` and `coordinates`, and conditional coins
require `joint`. The structural auditor opens the conditional program's source
lambda before checking its exact sampler head and rejects premises assuming that
sampler's own specification. A scalar marginal law cannot replace these protocols.
Other stateful interfaces need an explicit auditor extension before acceptance.

The prose review must identify the exact public spec and proof hash. The receipt
binds the entire project-local import closure, not only the direct proof file. Shared
support changes invalidate all affected receipts, even if the top-level proof stays
textually unchanged. Coordinate such changes before a review pass.

## Integration

After an independent receipt is ready, the ledger owner runs:

```sh
python3 agent-scripts/lean_gate.py -- python3 agent-scripts/integrate_exact_receipt.py \
  agent-docs/reviews/ExactStructuredBatch001.json
```

The helper validates every acceptance before mutating the new ledger, preserves prior
receipt paths on rollover, and reports missing public-root imports. It does not edit
the historic campaign, root imports or public indexes. Reviewer identities are
normalized so short team names and canonical `/root/` names cannot bypass independence.

## Reproducible audit

Cheap metadata/receipt check (does not claim Lean validation):

```sh
python3 agent-scripts/lean_gate.py -- python3 agent-scripts/audit_exact_sampler_proofs.py \
  --metadata-only
```

Full current-state audit, under the shared memory gate:

```sh
python3 agent-scripts/lean_gate.py -- python3 agent-scripts/audit_exact_sampler_proofs.py
```

The full audit builds the project, checks exact theorem/program heads and circular
premises in Lean, checks transitive axioms, compiles every independent caller, and
rechecks sources/context after compilation. Add `--require-complete` only for the
final all-137 completion audit. An intermediate successful audit certifies only the
accepted rows it reports; it does not imply the entire goal is done.

## Historical dependency revalidation

`exact_baseline.py` creates a separate compatibility overlay for the prior 216
specifications. It leaves the original campaign and 48 review receipts untouched.
The overlay records current source snapshots/context and reruns all specification
heads, axioms and 49 independent caller artifacts. It does not assert that the
historical reviewers inspected a different upstream checkout.

Run after sources are stable, with a fresh numbered output/log pair:

```sh
python3 agent-scripts/lean_gate.py -- python3 agent-scripts/exact_baseline.py \
  --output agent-docs/reviews/ExactBaselineRevalidation001.json \
  --log agent-docs/reviews/ExactBaselineRevalidation001.log \
  > agent-docs/reviews/ExactBaselineRevalidation001.log 2>&1
```

An implementation-file change cannot be silently allowed by a whole-file hash
update. A current-context independent source-change review must list each affected
historical sampler, its original/current transitive snapshots, and attest that its
direct sampler definition and reviewed domain are unchanged. The command accepts
such evidence with `--source-change-review PATH`; changed sampler definitions need
full new proof review instead of that conservative migration path.

`validate_baseline_overlay()` returns the exact public proof paths after checking
all overlay evidence against the current worktree. Public generators can consume
that result without weakening or rewriting any historical receipt.
The ledger's `baseline_revalidation` selects the current immutable overlay;
`python3 agent-scripts/exact_baseline.py --check` checks that selected record.
