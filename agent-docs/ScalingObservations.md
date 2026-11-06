# Scaling observations

These notes come from the reorganization of the library on 6 November 2026. Use them to
judge how continuous TotalEris (CTE) verification holds up at scale. All counts describe
the tree on that date.

## Size

The following table compares the size of the source, the proofs, and the review record:

| Artifact | Files | Lines |
| --- | --- | --- |
| Occil implementations (`code/`) | Not counted | 8,186 |
| CTE proofs (`SampLib/`) | 970 modules | 121,647 |
| Review artifacts (`agent-docs/reviews/`) | 603 | 112,516 |

The proofs cover 336 accepted samplers: 216 from the earlier campaigns and 120 from the
exact campaign. The library has about 15 lines of proof for each line of source. Most of
these lines are mathematics and loop invariants, not public specs:

| Directory | Modules | Public specs | `Laws/` | `Support/` and `Syntax/` |
| --- | --- | --- | --- | --- |
| Bernoulli | 230 | 97 | 80 | 53 |
| PSRN | 167 | 21 | 33 | 113 |
| Weighted | 147 | 35 | 60 | 52 |
| Discrete | 104 | 46 | 43 | 15 |
| General | 83 | 49 | 21 | 13 |
| Constants | 81 | 39 | 33 | 9 |
| Combinatorial, Continuous, and Uniform | 49 | 36 | 10 | 3 |
| Core, Common, and Latent (shared) | 106 | None | 45 | 9 |

Lazy reals (PSRN) stand out: 113 helper modules support only 21 public specs.

## Findings

The reorganization exposed these problems:

1. **Reviews pin file paths.** Each receipt hashes the whole import closure of its proof,
   keyed by file path. This design makes reviews hard to fake. However, any move or
   rename voids every review that depends on the moved file, which can be all 336. The
   [relocation records](relocations) remove this obstacle. Each record proves that a move
   changed only import lines and links, and the audits read reviews through the records.
2. **Review callers compiled against stale build output.** Two current review callers,
   `ExactLatentBatch004Callers` and `ExpansionStructuredBatch013Callers`, imported eight
   modules that `lake build` no longer built. The audit still passed, because
   `lake env lean` used `.olean` files that older builds had left behind. The eight
   modules now build as part of the library. The audit needs to build the imports of each
   caller itself.
3. **Dead code accumulates.** The library held 45 modules that no longer built, and
   stopped work left nine more files. Together, these files made up about 5% of the
   library. They now live in the [attic](../attic).
4. **Families share code, but only shallowly.** 106 modules serve several families.
   Families also use the public specs of other families. For example, Constants imports
   Bernoulli 37 times, and many laws import `RealCoin` or `UniformInt`.
5. **A proof near the heartbeat limit depends on its module name.** The move renamed
   modules without changing any proof text, yet `OptimalScan` then exceeded 200,000
   heartbeats at line 79. The identical file builds as `SampLib.OptimalScan` and as a
   stand-alone file. It fails as `SampLib.Weighted.OptimalScan`,
   `SampLib.Weighted.Support.OptimalScan`, and `SampLib.Weighted.Support.OptimalScanX`.
   The module name becomes part of the names of generated declarations, which appears to
   be enough to change elaboration. A higher limit would change the proof and void two
   reviews, so the module stays at its old path.
6. **Instructions go stale.** The suite README told readers to run
   `audit_sampler_proofs.py`, which can no longer pass at the current dependency pin. The
   round-2 progress notes still said "awaiting review" after the proofs were accepted. The
   README now names the current audits, and each progress note carries a warning.
