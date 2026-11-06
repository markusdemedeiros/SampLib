# Agent documents

Working documents for the verification campaigns. Start with the
[proof standard](VerifyingSamplers.md); the [library layout](../SampLib/README.md#layout)
explains where proofs live.

## Standards and guides

- [VerifyingSamplers.md](VerifyingSamplers.md): the proof-quality standard and workflow.
  Its hash is part of every review's dependency context.
- [LatentObservationDomains.md](LatentObservationDomains.md): termination domains for
  lazy-real observations.
- [LatentUniformProofs.md](LatentUniformProofs.md): the shared latent-uniform posterior
  argument.

## Exact campaign (current)

- [ExactVerificationCampaign.md](ExactVerificationCampaign.md): spec kinds, review
  handoff, integration, audits and module moves.
- [ExactVerificationQueue.md](ExactVerificationQueue.md): the frozen 137-entry scope.
  Its hash is pinned by the ledger.
- [ExactVerificationCampaign.json](ExactVerificationCampaign.json): the ledger. Update it
  only through `agent-scripts/integrate_exact_receipt.py`.
- [ExactCampaignDeferrals.md](ExactCampaignDeferrals.md): the 17 open samplers and why.
- [progress/](progress): round-2 team notes, kept as a record.

## Earlier campaigns

- [VerificationCampaign.json](VerificationCampaign.json): the original 216-sampler ledger.
  Its hash is pinned, so it never changes.
- [ExpansionCampaign.json](ExpansionCampaign.json),
  [ExpansionAudit.json](ExpansionAudit.json),
  [VerificationAudit.json](VerificationAudit.json): the expansion campaign's ledger and
  audit summaries.

## Reviews and moves

- [reviews/](reviews): immutable receipts (`.json`), review prose (`.md`), reviewer
  callers (`Callers.lean`) and audit logs. File names follow the batch, for example
  `ExactLatentBatch011.json` with `ExactLatentBatch011.md` and
  `ExactLatentBatch011Callers.lean`. Paths inside a review are as of that review.
- [relocations/](relocations): records of module moves. The audits read reviews through
  them, so old reviews still bind to moved files.

## Observations

- [ScalingObservations.md](ScalingObservations.md): size of the proofs and review
  record, and problems found while reorganizing the library.

## Source data and plans

- [OccilSources.json](OccilSources.json), [OccilInventory.json](OccilInventory.json): the
  scraped Occil articles and their sampler inventory.
- [SamplerLaws.json](SamplerLaws.json): the curated laws behind [LAWS.md](../LAWS.md).
- [ProbLangWishlist.md](ProbLangWishlist.md),
  [NativeRealImplementationPlan.md](NativeRealImplementationPlan.md): language and
  implementation plans.
