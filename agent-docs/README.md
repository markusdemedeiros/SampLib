# Agent documents

This directory holds the working documents of the verification campaigns. Start with the
[proof standard](VerifyingSamplers.md). To find where a proof lives, see the
[library layout](../SampLib/README.md#layout).

## Standards and guides

- [VerifyingSamplers.md](VerifyingSamplers.md): The proof-quality standard and workflow.
  Every review records the hash of this file as part of its dependency context.
- [LatentObservationDomains.md](LatentObservationDomains.md): The termination domains of
  lazy-real observations.
- [LatentUniformProofs.md](LatentUniformProofs.md): The posterior argument that the
  latent-uniform proofs share.

## Current exact campaign

- [ExactVerificationCampaign.md](ExactVerificationCampaign.md): Spec kinds, review
  handoff, integration, audits, and module moves.
- [ExactVerificationQueue.md](ExactVerificationQueue.md): The frozen scope of 137 entries.
  The ledger pins the hash of this file.
- [ExactVerificationCampaign.json](ExactVerificationCampaign.json): The ledger. Change it
  only through `agent-scripts/integrate_exact_receipt.py`.
- [ExactCampaignDeferrals.md](ExactCampaignDeferrals.md): The 17 open samplers, with the
  reason that each one is deferred.
- [progress/](progress): Notes from the round-2 teams, kept as a record.

## Earlier campaigns

- [VerificationCampaign.json](VerificationCampaign.json): The ledger of the original
  216-sampler suite. Its hash is pinned, so this file never changes.
- [ExpansionCampaign.json](ExpansionCampaign.json),
  [ExpansionAudit.json](ExpansionAudit.json), and
  [VerificationAudit.json](VerificationAudit.json): The ledger and audit summaries of the
  expansion campaign.

## Reviews and moves

- [reviews/](reviews): Immutable receipts (`.json`), review reports (`.md`), reviewer
  callers (`Callers.lean`), and audit logs. Files are named after their batch. For
  example, the `ExactLatentBatch011` batch has `ExactLatentBatch011.json`,
  `ExactLatentBatch011.md`, and `ExactLatentBatch011Callers.lean`. Paths inside a review
  are the paths at the time of that review.
- [relocations/](relocations): Records of module moves. The audits read each review
  through these records, so a review still applies after the files that it covers move.

## Observations

- [ScalingObservations.md](ScalingObservations.md): The size of the proofs and of the
  review record, and the problems that the 2026 reorganization exposed.

## Source data and plans

- [OccilSources.json](OccilSources.json) and [OccilInventory.json](OccilInventory.json):
  The Occil articles and the sampler inventory taken from them.
- [SamplerLaws.json](SamplerLaws.json): The curated laws that [LAWS.md](../LAWS.md)
  displays.
- [ProbLangWishlist.md](ProbLangWishlist.md) and
  [NativeRealImplementationPlan.md](NativeRealImplementationPlan.md): Plans for the
  language and for the implementations.
