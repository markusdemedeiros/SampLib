# Dirichlet and simplex verification

> Round-2 working notes, kept as a record and not updated since 2026-11-06. For current
> status see [LAWS.md](../../LAWS.md) and [the deferral list](../ExactCampaignDeferrals.md).

Owned by `prove_constants_pi`; full source rows are still pending.

## Frozen support

- `Distributions/PSRNDirichletLaw`: normalized independent unit-rate gamma law;
  positive common sum, positive coordinates, sum one, singleton point mass;
  simplex is the shape-one exponential construction.
- `Distributions/PSRNDirichletTransport`: transport a complete gamma-vector law
  through the one common normalization, with arbitrary ENNReal joint credits.
- `LatentCoordinateSum{Model,}` and `Syntax/PSRNCoordinateSum`: the actual local
  `rec total xs` closure, its shared model, constructor, and observation protocol.
- `LatentRepresentedViews`, `LatentRepresentedAddition`,
  `LatentRepresentedCoordinateSum`: exact deterministic interval certificates for
  fixed views, rational constants, addition, and the common sum.
- `LatentRepresentedProduct`, `LatentRepresentedVectorSpec`: represented product
  coordinates and a vector protocol retaining one whole-world ownership.

Own alias, empty/singleton, infinite-credit callers and standard-axiom checks passed.
No accepted source or existing shared support was changed.

## In progress

- `Distributions/FiniteProductPosterior`: dependent finite-product AC and
  coordinate disintegration/update. Built; not frozen yet.
- `LatentPiModel`: common world and coordinate views for heterogeneous component
  models, including the exact product of their observable laws. Built; not frozen.
- `LatentPiOwnership` / `LatentPiCoordinate`: focus one component resource, then
  restore its updated state and the full joint credit. Checking.

## Source dependencies

Core owns the strong decay-based exponential constructor. Geometry owns its
rational-rate wrapper, the positive-rational gamma constructor, and the represented
reciprocal observer. The sum certificates above feed reciprocal directly.

A generic enclosure with shrinking error cannot bound arbitrary coarse inverse
intervals. Use `LatentRepresentedSpec` and the actual deterministic interval
schedule; never infer a reciprocal envelope from the weaker old protocol alone.

For dimension one, the actual source returns the constant unit oracle before
allocating gamma/exponential components. A semantic product world may remain
unobserved: retain its initial joint credit, use a constant-one coordinate view,
and use `PSRNDirichletLaw.law_singleton` for the canonical law. Physical ownership
for this branch can assert the constant handle and initial state; it need not
invent heap allocations.

`drafts/PSRNNormalizedSingleton.lean` is an unfinished source-normalization
experiment, not a checked proof. Broad `twp_pures` expanded unused constructor
branches to 8 GB. Use cached `CurriedStep` source LC/opening facts and discard
unused conditional branches before any broad reduct normalization. No heartbeat
increase or admitted proof was introduced.

## Current normalization checkpoint

The finite Π model, ownership, coordinate observer, and actual `repeatSample`
allocation are clean and frozen. Their hashes, together with the fixed reciprocal
and shared division view, are in `/tmp/pi-normalization-support.sha256`.
Producer callers exercise generic worlds, frames, infinite credits, and n=0/1.
Reviewer B's preliminary semantic read is green; final support closure should be
pinned with an actual downstream sampler.

New, clean normalization modules (not frozen yet):

- `LatentDivideCoordinates`: actual recursive source constructor, one invariant P.
- `LatentNormalizationModel`: quotient views and canonical normalized-Gamma law.
- `LatentNormalizedCoordinates`: existentially retains original handles and their
  single ownership; every quotient reads the same sum under arbitrary joint F.
- `LatentNormalizationConstructor`: actual local sum followed by divideCoordinates.
- `Syntax/PSRNSimplex`: actual source correspondence and cached opening equations.

`NormalizationProducerCallers.lean` passes, with only the standard three axioms.
`newSimplex` can close against the concrete represented Exp(1) constructor now.
The singleton branch allocates no Exponentials: use a virtual prior world with
constant-one represented coordinates and pure ownership, then identify its law.
The full rational Gamma source dependency belongs to Exp; it awaits geometry's
complementary-subunit Beta/Johnk proof. Do not replace that constructor by an
assumed scalar Gamma law in the final Dirichlet theorem.
