# Exact deferred rejection review, batch 002

Reviewer: `/root/review_exact_b`. Accepted
`SampLib.PSRNRejection.newRejection_latentDistSpec` in `SampLib/Samplers/PSRNRejection.lean`,
SHA-256 `9f945860fbd67150ce1a0ef408065e6eacedeeefb31a26031adeb0f16f08e8f1`. Classification: core; interface: latent real.

## Conditional law and actual retained oracle

The proposal has a normalized joint latent posterior. The event contract applies
to that same candidate and returns both its refined physical ownership and the
observed event fact with arbitrary Boolean/latent-dependent continuation credit.
No unconditional marginal coin law is substituted for conditional acceptance.

The target's initial law is the proposal conditioned on acceptance. An accepted
state retains its original refined proposal posterior. Its recorded acceptance
fact and absolute continuity show this posterior is absolutely continuous with
the initial conditional law. Future reads retain that fact and the same candidate
handle, rather than redrawing a fresh value or dropping its shared state.

The explicit initial conditional state owns no observable oracle; construction
must produce a genuinely accepted state. The public theorem supplies the complete
concrete observation protocol, not merely a constructor-credit certificate.

## Expectation preservation and CTE structure

The single branch kernel gives accepted candidates output credit and rejected
candidates the conditional expected output credit plus amplified termination
credit. Its preservation inequality reuses the independently proved generic
rejection identity. Positive acceptance mass gives a finite amplification factor
greater than one, including acceptance mass one.

The actual retry induction appears once in `LatentRejectionKernel`: sample a
proposal, run its conditional event test, then return the same oracle or spend the
amplified retry credit. A constructor-only payload interface factors this logic
for reuse by genuine vector protocols; payload alone is not accepted as a sampler
specification. The scalar wrapper additionally proves all accepted-oracle reads.
No hypothesis assumes correctness of the concrete `newRejection` program.

## Independent nontrivial caller

The [independent fixture](ExactLatentBatch002Callers.lean) proves an actual callback
that queries the candidate uniform's first cached bit and accepts exactly the
lower half-cell. This event specification works at every prior cache and for
arbitrary joint credit G(b,u). The callback is independently proved from the
concrete prefix observation and posterior head-bit identity. Its acceptance mass
is proved exactly one half, so both acceptance and retry branches are substantive.

A concrete fresh-uniform proposal is passed to the actual rejection sampler.
The fixture then observes the returned accepted handle at precision three, or at
zero with infinite credit, retaining an arbitrary caller resource. The callback
and later observation use aliases of the same candidate; accepted posterior
ownership is preserved through both. This independently exercises actual
construction, conditional acceptance and subsequent oracle use.

Independent targeted build, warning-free caller compilation, latent exact-head
and noncircular-premise audit passed. The public theorem, actual retry CTE kernel,
event callback, half-mass certificate and constructor/read caller have only
`propext`, `Classical.choice`, `Quot.sound` axioms. The auditor reports `SPEC_OK`
for exactly `Occil.PSRN.newRejection`; commands are in `ExactLatentBatch002.log`.

The immutable receipt snapshots all project-local source/support, caller hash and
current `06a7b3e2` dependency context. Historical receipts are unchanged.
Domain: Any actual deferred proposal constructor with a normalized joint latent model, measurable positive-mass event and resource-preserving conditional event-test specification on that same latent world. The actual accepted oracle and its refined posterior/ownership are retained; arbitrary measurable joint ENNReal credits are supported.
