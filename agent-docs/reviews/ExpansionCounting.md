# Expansion counting decisions

Count named sampler specifications independently accepted by a reviewer. Label
thin wrappers as derived. Deterministic helpers, resource interfaces, and
supporting transition routines do not increase the sampler count.

A distinct stateful sampling technique may use `IsOwnedDistSpec`: it requires
and preserves an explicit representation invariant while exchanging arbitrary
continuation credits under a normalized law. `Occil.WeightedVariants.fenwickDraw`
is such a categorical sampler. Its audit uses a separate owned-specification
command and requires the same head, circularity, source, axiom, and caller checks.
Concrete initialize-then-draw clients establish usable ownership; no heap-free
specification or added runtime wrapper is substituted. A draw helper of an
already counted technique, such as `voseDraw`, remains uncounted.

## Slice sampling

`Occil.General.sliceStep` is the supporting transition called by
`Occil.General.sliceSampler`: see the
[transition and iteration terms](../../code/Samplers/General/Core.lean#L294).
Count this technique once through `sliceSampler`. Keep the step's normalized
kernel, CTE proof, invariance argument, and caller checks as reviewed support.

Its expansion-ledger disposition is `rejected` with kind `support_only` because
it is excluded from the counted sampler set. This is a counting decision, not a
mathematical failure or permission to omit the supporting proof. The author and
structured reviewer both agreed to this classification before acceptance.
