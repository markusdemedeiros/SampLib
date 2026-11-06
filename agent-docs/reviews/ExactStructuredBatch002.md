# Exact structured sampler review, batch 002

Reviewer: `/root/review_exact_b`. Accepted existing interface:
`SampLib.AliasTable.voseDraw_ownedDistSpec` in `SampLib/AliasTable.lean`, SHA-256 `18963a0ba6a5e216c05ccd8ae8b247867e61608f954c26de34edc71e52021a60`.

## Source, mathematics and program logic

The source reads a uniformly chosen column. A self-alias column returns immediately;
otherwise one uniformly sampled integer ticket selects the threshold or alias.
`AliasMass.expectation_range` identifies that two-stage credit average with the
normalized categorical law by gathering incoming integer mass. Its argument
handles arbitrary ENNReal continuation credits; no finiteness restriction or
conversion to real-valued credit occurs.

The CTE theorem executes the table fields, array reads and branch tests in source
order, calling the integer-uniform rule at each draw. Both owned arrays are
returned on every branch. The only mass hypothesis is a mathematical table
invariant, not an assumed distribution specification of the concrete draw.
This is existing supporting verification promoted to a separately reviewed
interface, not newly counted mathematical sampling work.

## Independent checks

A targeted `lake build SampLib.AliasTable` passed. The independently compiled
[caller fixture](ExactStructuredBatch002Callers.lean) is warning-free and exercises:

- arbitrary measurable ENNReal credit and an unrelated linear caller resource;
- independent repetition through one retained table, with the full joint vector law;
- an explicit sparse `[0,1,0]` table with zero thresholds and both self/non-self aliases.

The structural public-spec auditor reports `SPEC_OK` for the exact source sampler,
checks an owned distribution interface and excludes circular correctness premises.
The public theorem and its central expectation lemma have only the standard
`propext`, `Classical.choice` and `Quot.sound` axioms. The fixture's derived caller
and finite sparse-table certificate also have only those axioms. Full command
output is retained in `ExactStructuredBatch002.log`.

The immutable JSON receipt records the current `06a7b3e2` dependency context,
caller hash and complete project-local source closure. Historical receipts remain
unchanged. Parameter domain: Every finite natural weight list with positive total and every owned alias table whose category mass equals length times the corresponding weight; zero-weight categories are allowed and both arrays are retained.
