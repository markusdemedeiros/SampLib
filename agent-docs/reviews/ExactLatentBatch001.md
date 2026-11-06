# Exact deferred sampler review, batch 001

Reviewer: `/root/review_exact_b`. Accepted
`SampLib.LatentUniform.newUniform_latentDistSpec` in `SampLib/LatentUniform.lean`, SHA-256 `0ac202f892546ce47dafbb8b61307d250bfcf7868cb11d13432769f235781199`.
Classification: core. Interface: `SampLib.LatentReal.IsLatentDistSpec`.

## Mathematical law and actual representation

The source allocates a cached fair-digit stream and returns its actual interval-
oracle closure. `model_initial_law` identifies its latent law with the normalized
unit-uniform measure. An observation at precision n returns the integer-rational
interval determined by the first n digits, enclosing the same value with width
2^(-n). The posterior support and affine-rank identities prove this enclosure;
absolute continuity transfers every earlier enclosure through later refinements.
The target is a deferred real, not a fictitious real literal returned by the code.

The concrete `twp_observe` calls the existing posterior-aware cached-prefix rule,
then the verified integer-power evaluator. It retains the same physical root and
integral of the arbitrary continuation credit under the refined posterior. It
covers shorter rereads even when more digits are already cached. The allocation
proof and observation wrapper are straight-line symbolic execution. No unknown
concrete oracle-correctness premise occurs in the public constructor theorem.

## Protocol review and multiple passes

`Model` supplies normalized joint posteriors, a measurable represented value,
transitive absolutely-continuous refinement and vanishing enclosure error.
`IsOracleSpec` relates actual closure applications to refined states/enclosures
and arbitrary measurable ENNReal credits on the whole latent space. Its resource
continuation supports aliases without duplicating owned state or asserting fresh
independent outputs on repeated reads.

Review identified that a constructor preserving only the unchanged initial
posterior would be too strong for eager mixture/acceptance decisions. The shared
interface was generalized before acceptance: construction may return a refined
state with its corresponding posterior credit. The uniform constructor chooses
the initial empty cache. Later transformations and rejection may expose genuine
construction-time observations without changing this reviewed protocol.

## Independent checks

The independent [caller fixture](ExactLatentBatch001Callers.lean) constructs the
actual uniform and observes the same returned closure twice at precisions eight
then three. Both enclosure facts hold under the final posterior, using absolute
continuity rather than an independence assumption. It also exercises precision
zero twice, arbitrary latent-dependent continuation credit, infinite credit and
an unrelated linear Iris resource. Small structural call templates avoid named-
variable capture when inserting an arbitrary locally closed value.

Independent targeted build, warning-free caller compilation and latent public-
spec structural audit all passed. The audit reports `SPEC_OK` for exactly
`Occil.PSRN.newUniform`, with an explicit latent interface and noncircular theorem
premises. Constructor, concrete observation, initial-law theorem and both generic
caller lemmas have only `propext`, `Classical.choice`, and `Quot.sound` axioms.
Full command evidence is in `ExactLatentBatch001.log`.

The JSON receipt pins the entire project-local proof/source closure, caller hash
and installed `clutch-lean` `06a7b3e2` review context. Historical receipts remain
unchanged. This proves ideal deferred-uniform semantics; it makes no Float-rounding
claim. Domain: Construction of one ideal unit-uniform deferred real; every natural observation precision, including zero and repeated/decreasing reads, through aliases of the same returned closure. The actual heap root and arbitrary measurable joint posterior ENNReal credit are preserved.
