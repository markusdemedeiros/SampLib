# Factory expansion review: batch 012

Reviewer: `/root/expand_review_factories`.

All four sampler modules passed independent targeted builds without warnings. The immutable caller compiles warning-free, exercises arbitrary resource frames and boundary/infinite-credit cases, and prints exactly the three standard axioms for all 17 inspected theorems.

## Occil.FactoryExtra.expMinusShifted

Accepted `SampLib.ExpMinusShifted.expMinusShifted_distSpec`, SHA-256 `4a58c7953a2158338266e73795b579bbc0f8c4061846bc2dcaed3188bb688f25`.

The actual rational and shared-uniform martingale exponential samplers are drawn independently. Their product gives exactly exp(-(a/b+p)); one expectation lemma reuses CoinProduct and exponent addition. Execution follows the two literal source branches. Independent public clients retain arbitrary callbacks, frames and ENNReal output credits and check the zero-shift endpoint law.

## Occil.FactoryExtra.tanhHalfShifted

Accepted `SampLib.TanhHalfShifted.tanhHalfShifted_distSpec`, SHA-256 `e99dc2da9718a54629647cdb79d773ff3b0626d8c13826d3729816c94ff2ecb5`.

The actual shifted exponential callback feeds the verified one-minus-over-one-plus factory. The real identity identifies its bias as tanh((a/b+p)/2). A structural lambda preserves callback free variables, and the CTE theorem is direct known-specification composition. Independent clients check arbitrary frames, zero and nonzero exact endpoints, and infinite credit on the impossible true output at zero shift/input.

## Occil.FactoryExtra.expMinusShiftPower

Accepted `SampLib.ExpMinusShiftPower.expMinusShiftPower_distSpec`, SHA-256 `4b26485154438a21799dc1ed7b48dc588046242a8f7742cede5d70d339539d28`.

The actual finite loop multiplies binomial factors exp(-choose(k,i)*m^(k-i)*p^i). The independent binomial theorem identifies the final law exp(-(m+p)^k), retaining the standard zero-power convention. A central expectation removes one monomial from the remaining exponent, and finite induction executes the literal loop. The generic exponential-operation contract is discharged by the concrete martingale sampler, not left as a public assumption. Deterministic choose and integer-power helpers verify their actual source. Independent clients frame arbitrary resources, cover m=0/k=0 including0^0, a nontrivial shifted square, and infinite impossible-output credit.

## Occil.Constants.fromApproximateDigits

Accepted `SampLib.FromApproximateDigits.fromApproximateDigits_distSpec`, SHA-256 `a407752f4a38057030a98d97a5c4bdad271dd51daaf5f3c2a4fadf459270e456`.

A normalized arbitrary-radix posterior cell replaces each digit prefix. Exact b-way averaging preserves every measurable ENNReal kernel. Settled guards certify the correct Boolean; unresolved prefixes occupy precisely two neighboring cells. One fixed finite horizon enclosure fits any positive error budget and supplies unit credit on an unresolved horizon. The program proof is one round plus finite backward induction, with source-index arithmetic and guard facts prepared outside execution. Independent clients include an actual oracle retaining free read (colliding with the recursive template name), arbitrary resource frames and infinite off-support credit. The legal base2,p0,approximation=1 fixture has both first digits retry and initial horizon credit exactly1, ruling out a false one-round half-probability argument. Negative radix cells also retain normalization and zero mass for infinite off-support credit.

## Shared support

All support was independently source-reviewed and re-elaborated warning-free under ordinary project heartbeat defaults. FactoryChoose checks exact rising-product integer division and the out-of-range zero case. The binomial tail law is independent of the loop recurrence; the generic loop contract is concretely instantiated in the public theorem. Routine index transports are explicit before execution. RadixPosterior normalizes every positive-denominator cell, including negative integer positions, and proves the exact finite partition identity. ApproximateDigits reuses the frozen BoundsKernel indicator budget and supplies all settled/horizon facts without a conditional retry assumption.

The immutable caller is `agent-docs/reviews/ExpansionFactoriesBatch012Callers.lean`, SHA-256 `1561c6bbd221c10d9a087bf520440325efed6db38690a64bf31c8d6a7fbdb8e5`.
