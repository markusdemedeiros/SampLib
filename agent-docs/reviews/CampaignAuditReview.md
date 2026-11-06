# Independent campaign-auditor review

Reviewer: `/root/prove_coin_combinators`. Scope: the completion claims supported
by `agent-scripts/audit_sampler_proofs.py` and `VerificationCampaign.json`.
The shared script and manifest were not edited during this review.
Initial script SHA256:
`a7c3c7423de5e50cb164dca0893bdb01c7c75ea91a1d20567083663bfba824ad`.

## Assessment

The initial audit is useful evidence for source freshness, importability,
normalization through `IsDistSpec`, and transitive axiom safety. It is not yet a
sufficient completion gate for the user's request. Its mathematical/style
acceptance must remain grounded in independent reviewer evidence.

The findings below were sent to root while the auditor was being strengthened.
They describe the initial checker, not an approval of a later revision. The final
auditor needs a fresh run and regression checks after integration.

## Confirmed false positives

The standalone file `/tmp/campaign-audit-review/FalsePositive.lean` contains the
initial auditor's actual `LEAN_HEADER` and two counterexamples. It compiles
without warnings and emits `SPEC_OK` and standard-only axiom lists for both:

1. `CampaignAuditFalsePositive.unrelated` verifies the unit literal. The named
   `Occil.complement` appears only in a reflexive conditional inside its encoder.
   Searching the entire `IsDistSpec` conclusion therefore counts the wrong
   program.
2. `CampaignAuditFalsePositive.circular` returns an assumed copy of its entire
   desired specification. Its target is a stuck call with unit in place of a
   coin. The theorem is logically valid under that impossible assumption, but
   verifies no sampler from actual input conditions.

The payload without the old header is saved as
`/tmp/campaign-audit-review/FalsePositivePayload.lean.txt`, so the final checker
can be tested against the same cases.

### Required type-checker changes

- Find `IsDistSpec`'s program argument by the structure parameter named `e`,
  rather than searching its law, encoder, and other arguments. There are
  currently 16 structure parameters, with `e` at zero-based index 12; derive this
  dynamically rather than relying on the present arity.
- Check the object-language application's function spine for the named sampler.
  A sampler merely occurring as an argument or nested helper does not establish
  that the theorem verifies that sampler's own call.
- Inspect opened theorem premises. Reject an assumed copy of the whole result;
  also flag premises assuming an `IsDistSpec` for the same concrete target.
  Abstract callback specs remain legitimate input contracts.
- Use an opened telescope when comparing premise/result expressions; simply
  stripping binders leaves loose bound variables with differing indices.

Arbitrary semantic preconditions still require human review. Syntax checks alone
cannot establish that a domain is full, useful, or nonvacuous.

## Evidence and freshness gaps

### Bind review acceptance to the exact artifact

The initial checker accepts any existing evidence path and unequal owner/reviewer
strings. It does not verify that the document accepts this sampler, spec, source
hash, or domain. Require nonempty identities and a reviewer-owned structured
receipt binding those fields, the acceptance decision, evidence path, and checks
performed. Missing, pending, unrelated, or superseded evidence must fail.

### Freeze the reviewed dependencies

Hashing only a proof file misses changes to its sampler implementation,
`Templates`, distribution laws, encoders, and other imported proof helpers. Such
changes can alter the meaning of an unchanged theorem and invalidate the review.
Snapshot the project-local transitive source closure and implementation source,
with dependency/toolchain configuration. The receipt should record what the
reviewer actually checked; recomputing hashes after a change is not a fresh
review.

Pinned commits alone do not detect dirty dependency worktrees. Verify actual
checkout revisions and cleanliness, or record tracked-diff hashes, for proof
infrastructure whose contents can affect soundness or semantics.

## Counting and integration gaps

- Audit both baseline proofs, with source/config snapshots and actual public
  specs, while excluding them from the new-sampler count. The initial checker
  only excludes baseline names from accepted rows; it never verifies the two
  proofs counted toward the desired suite of 32.
- Preserve the literal goal of at least 30 new proofs. A reduced manifest target
  must not silently redefine completion. Check the total target as well.
- Require distinct public specifications as well as distinct sampler names,
  unless a justified multi-result certificate is explicitly represented.
- Remove the redundant top-level `accepted` list or enforce exact agreement with
  rows whose status is accepted.
- Validate status/required-field schema and ensure implementation paths exist and
  correspond to the implementation being counted. The initial script ignores
  the `implementation` field.
- Clearly classify reserve or abandoned candidates at completion. An accepted
  count does not explain whether remaining assigned entries are required work,
  alternatives, or intentionally abandoned poor fits.

## Smaller robustness suggestions

- Match `SPEC_OK` output by exact theorem/sampler pairs rather than only counting
  lines; associate each axiom result with its expected theorem.
- Accept the no-axiom output format as an empty axiom set, while continuing to
  reject `sorryAx` and any nonstandard axioms.
- Capture build warnings as well as audit-command warnings. Record a full default
  `lake build` separately if the script deliberately builds only `SampLib`.
- Preserve a machine-readable audit result containing the actual checked types,
  source/dependency fingerprints, review receipts, counts, and command outcomes.
  This makes the completion claim inspectable without relying on prose alone.

## Completion criterion

Acceptance requires the final gate to reject the counterexamples, validate exact
reviewed artifacts and baselines, and pass on at least 30 distinct new sampler
specifications. Independent source review must still establish mathematical law,
full useful domain, arbitrary ENNReal credits, and the requested obvious CTE
program proof with one clear expectation argument. The auditor supports these
judgments; it cannot substitute for them.

## Re-review of the revised checker

Reviewed audit-script SHA256:
`f4fc7870b8238a4265b4eaa2cfdcd59ada491794ccdaffa8013dd0e90d17ab2b`.
Reviewed dependency-helper SHA256:
`4b236622d718c13e46aab7ce01cbd236b244bfcad4ae69385df3b60d06c6a5d6`.

The revised design materially strengthens the completion evidence:

- It locates the `e` parameter and follows the object-language application spine.
- It checks exact spec/sampler output pairs and theorem-specific axiom output,
  including the empty-axiom format.
- It enforces literal minima of 30 new and 32 total, distinct public specs,
  accepted-list consistency, and both baseline identities/specifications.
- Reviewer-owned structured receipts bind accepted entries to source hashes,
  named checks, prose evidence, transitive project snapshots, configuration, and
  clean pinned dependency checkouts.
- Full builds reject warnings; completion additionally compiles three persistent
  caller files.

### Original regression cases: fixed

`/tmp/campaign-audit-review/RevisedFalsePositive.lean` uses the revised
`LEAN_HEADER` with the original counterexample payload. Lean rejects both audit
commands for the intended reasons:

- The unit-literal spec does not specify a call to `Occil.complement`.
- The direct circular spec assumes its own concrete sampler in a premise.

No `SPEC_OK` is emitted for either. Their proof terms themselves remain ordinary
valid Lean proofs; rejection comes from the stronger campaign gate.

### Remaining material weaknesses at this revision

1. **Reducible aliases can hide circular assumptions.**
   `/tmp/campaign-audit-review/AliasedCircular.lean` introduces
   `abbrev desired E := IsDistSpec ... target ...`, then returns
   `h : desired E` as the desired specification. The revised raw-premise scan
   still emits `SPEC_OK` and a standard-only axiom list. The same happens for
   `h : True ∧ desired E` in `NestedCircular.lean`. Normalize reducible aliases
   while recursively inspecting premises, with cycle/fuel control. Outer-only
   weak-head reduction does not handle the conjunction case. Independent review
   must still assess arbitrary semantic domain assumptions; a complete semantic
   non-vacuity test is not possible by this syntactic filter.
2. **The regex does not capture the actual entire import closure.**
   A valid file with indented header imports compiles cleanly:
   `/tmp/campaign-audit-review/IndentedImport.lean`. The dependency helper's
   column-zero regex misses those imports. An isolated source-snapshot test with
   indented imports of `A` and `B` returns only `Main.lean` and the implementation,
   omitting both imported sources. The current campaign modules appear to use
   simple column-zero imports, so this is not an observed stale accepted proof;
   it is a gap in the claimed closure guarantee. Prefer Lean's available
   `--src-deps` parser output or explicitly cover/reject unsupported import forms.

### Further evidence binding

The caller-file gate checks existence and successful compilation, but an emptied
caller file also compiles. Bind persistent caller/evidence file hashes in the
reviewer receipts so that the final checks are the ones independently reviewed.
Binding the reviewed domain text would also prevent manifest descriptions from
drifting while the underlying proof hash remains unchanged.

These findings were sent promptly to root. No shared implementation was changed
by this reviewer. This revision is substantially stronger, but the two remaining
material cases require resolution or an explicitly narrower claim before the
final completion gate is treated as settled.

## Final regression review: resolved

The following exact final files were reviewed and tested:

- `audit_sampler_proofs.py`:
  `e23620ee71dabf01f1e7e7614ff6be53388a713e615e0562c3691af654b16208`
- `proof_dependencies.py`:
  `422cc12ed2d8d8ecd52ba7707d0316219f810d4369dae3610ba5a928c0674b6b`
- `parse_lean_imports.lean`:
  `d3194368c5cec11a1242474b83d5a25110dfab1775cd30c2b03946dfd1cf138b`

The final `LEAN_HEADER` SHA256 is
`59346a6f1e3589702dce8f6ae63bde472adf7dbe92a3ca450ef675fbbefc5c9c`.
The tests below used that exact header, without a replacement import list or
local modification. An intermediate overloaded Boolean-operator error was
reported and fixed before these final tests.

### Four rejected counterexamples and two accepted real specs

`/tmp/campaign-audit-review/ApprovedFinalFalsePositives.lean` now rejects all four
known counterexamples, with exactly the intended audit errors and no `SPEC_OK`:

- The unrelated unit-literal specification fails the program-head check.
- The directly assumed target specification fails the premise check.
- The reducible-alias assumption fails the premise check.
- The conjunction containing that alias fails the premise check.

Lean exits with status 1, as expected for these four intentional rejections.
The log is `approved-false-positives.log` in the same temporary directory.

`ApprovedFinalPositive.lean` exits with status 0, without warnings, and emits the
correct `SPEC_OK` pairs for both `CoinProduct.coinProduct_distSpec` and
`UniformSum.uniformSum_distSpec`. Both report only the three standard axioms.
These exercise a callback combinator and a finite recursive sampler. The log is
`approved-positive.log`.

### Actual import parsing and snapshot regression

The final helper uses Lean's `Lean.Elab.parseImports`, rather than the earlier
regex. `IndentedImport.lean` and `ValidAllImport.lean` independently compile with
valid indented and `import all` syntax. `SnapshotRegression.py` tests the actual
helper on an isolated project fixture containing both forms:

- Its snapshot contains the main module, both imported project modules, and the
  implementation source.
- Modifying an imported source changes the snapshot.
- Changing an already cached header to import another project module refreshes
  the parsed header and adds the new dependency to the snapshot.

All assertions pass; `final-snapshot.log` records `SNAPSHOT_OK`,
`DEPENDENCY_CHANGE_DETECTED`, and `HEADER_CACHE_INVALIDATION_OK`.

### Final assessment

The demonstrated structural and import-closure weaknesses above are resolved in
these final revisions. Source inspection also confirms that reviewer-owned
caller hashes and support-file hashes are checked, and accepted source snapshots,
baseline snapshots, and dependency/configuration context are checked again after
compilation. The earlier unresolved assessment is superseded by this section.
No demonstrated material structural issue remains within this checker's stated
scope. Domain adequacy, mathematical interpretation, and proof quality remain
independent source-review judgments; these finite structural checks do not decide
arbitrary logical non-vacuity.

A separate cross-check of `SampLib/README.md`'s 35-row law/domain index found no
material overclaim relative to the inspected theorem signatures. In particular,
the empty-input zero-draw statement is supported by the separate public zero-draw
spec, and the full-domain coin formulas agree with the verified laws. The count
of 33 new and two baseline proofs agrees with the final campaign roster. This
review's local regression evidence is separate from root's full completion run.
