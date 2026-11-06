# Independent deferred floor support review

Reviewer: `/root/review_exact_b`. Support only; no additional sampler counted.
Reviewed full source and mathematics of Floor.twp_floorScaled_view and twp_floorScaled.

- `SampLib/PSRNFloor.lean`: `05c9eb091120d46d0d5177316e8256ab4bd942b8fc77a83412978de32116c554`.
- `SampLib/Syntax/PSRNFloor.lean`: `27e0573a5912d10c51164c1c62a981e06b72addb09e916f6d9290ccd6fc09e06`.
- `SampLib/Distributions/LatentReal/FloorKernel.lean`: `08084db7c1bb624bd71829540ba6a0e55845f0387f008e1b60927a23719bab2d`.
- `SampLib/Distributions/LatentReal/FloorUncertainty.lean`: `c4afef61175d54e25276d8611ce73e63ed453c0d528746d12d029fc933dc838f`.

The positive integer scale preserves interval endpoint order. Exact Euclidean
integer quotients equal real floor at both endpoints, including negative values.
If these quotients agree, the latent integer is resolved throughout the current
posterior. If they differ, the source lies within scaled observation error of a
floor-cell boundary. A measurable margin to the nearest boundary is positive
almost everywhere under the EXPLICIT AvoidsGrid hypothesis. Dominated convergence
therefore supplies a finite uncertainty horizon, with arbitrary joint integer/world
continuation credit and no finiteness assumption. The actual loop retains one
owned source through every read and uses that horizon credit at unresolved retry.

Independent targeted build and caller pass warning-free in ExactSharedFloor001.log.
The generic actual-source caller retains arbitrary joint G(integer,world) and
unrelated Iris frame. Concrete atomic NEGATIVE source -1/2 with scale3 returns
floor -2, showing that neither a continuous source nor a nonnegative value is
required. It is tested with infinity and with infinity requested on every
impossible integer: the latter expected input credit is zero. A grid atom at1
is separately shown outside this sufficient theorem domain; no claim is made
that every shrinking oracle terminates on a grid boundary. Exact-point boundary
oracles may instead admit a separate direct rule.

Both public interfaces, expectation identity and independent client checks have
only propext, Classical.choice and Quot.sound axioms. Later concrete sampler
receipts must snapshot the full support closure and prove the required grid
avoidance or an independent stronger boundary certificate.
