# Scaling observations

Notes from reorganizing the library on 2026-11-06, for judging how CTE verification
holds up at scale. Counts are for the tree as of that date.

## Size

| | Files | Lines |
| --- | --- | --- |
| Occil implementations (`code/`) | — | 8,186 |
| CTE proofs (`SampLib/`) | 970 modules | 121,647 |
| Review artifacts (`agent-docs/reviews/`) | 603 | 112,516 |

The proofs cover 336 accepted samplers: 216 from the earlier campaigns and 120 from the
exact campaign. That is about 15 lines of proof per line of source. Most of that bulk is
mathematics and loop invariants, not the public specs:

| Folder | Modules | Public specs | `Laws/` | `Support/` + `Syntax/` |
| --- | --- | --- | --- | --- |
| Bernoulli | 230 | 97 | 80 | 53 |
| PSRN | 167 | 21 | 33 | 113 |
| Weighted | 147 | 35 | 60 | 52 |
| Discrete | 104 | 46 | 43 | 15 |
| General | 83 | 49 | 21 | 13 |
| Constants | 81 | 39 | 33 | 9 |
| Combinatorial, Continuous, Uniform | 49 | 36 | 10 | 3 |
| Core, Common, Latent (shared) | 106 | — | 45 | 9 |

Lazy reals (PSRN) are the outlier: 113 helper modules behind 21 public specs.

## Findings

1. **Reviews pin paths.** Each receipt hashes its proof's whole import closure by file path.
   That makes reviews hard to fake, but any move or rename voids every review that
   depends on the file, up to all 336. The [relocation records](relocations) work around
   this: they prove a move changed only import lines and links, and the audits read
   reviews through them.
2. **Callers could compile against stale build output.** Two current review callers
   (`ExactLatentBatch004Callers`, `ExpansionStructuredBatch013Callers`) imported eight
   modules that `lake build` no longer built. The audit's `lake env lean` succeeded
   anyway, using `.olean` files left behind by older builds. The eight modules now build
   as part of the library. The audit should build each caller's imports itself.
3. **Dead code piles up.** 45 library modules no longer built, and 9 more files were left
   by stopped work, together about 5% of the library. They now sit in [`attic/`](../attic).
4. **Sharing is real but shallow.** 106 modules serve several families. Families also
   use each other's public specs: Constants imports Bernoulli 37 times, and many laws
   import `RealCoin` or `UniformInt`.
5. **Proofs near the heartbeat limit depend on their module name.** The move renamed
   modules without changing proof text, and `SampLib/OptimalScan.lean` then timed out
   (200,000 heartbeats at line 79). Building the identical file as `SampLib.OptimalScan`
   passes, and so does building it outside any module. Under `SampLib.Weighted.OptimalScan`,
   `SampLib.Weighted.Support.OptimalScan` or `SampLib.Weighted.Support.OptimalScanX` it
   fails. The module name feeds the names of generated declarations, which seems to be
   enough to change elaboration. Raising the limit would change the proof and void two
   reviews, so the module stays at its old path.
6. **Instructions go stale.** The suite README pointed at `audit_sampler_proofs.py`, which
   can no longer pass at the current dependency pin, and round-2 progress notes still
   said "awaiting review" after acceptance. Both are fixed or marked.
