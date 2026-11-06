# Splitting-PPS marginal-credit support review

Reviewer: `/root/review_exact_b`. This accepts supporting mathematics only;
it is not a sampler or a substitute for a joint splitting law.

Reviewed source: `SampLib/Distributions/SplittingPPSMarginals.lean`,
SHA-256 `9009c2dc1803d4bd706bc3d555d84214e7732823559de9bedf6fdf866fa01a44`.

`numeratorCredit_split` decomposes every selected numerator as amount plus its
natural residual before casting into ENNReal. The selected-block sum and residual
credit therefore reconstruct the original labelled credit even when the credit
function is infinite. Sorting is handled by an explicit permutation and does not
change the sum. No subtraction of arbitrary ENNReal credits occurs.

`inclusion_credit_expectation` normalizes the same identity. The sole cancellation
is the positive finite natural residual denominator; `amount<denominator` proves
it is nonzero. This remains valid for zero amount and infinite continuation
credits. Arbitrary labels and cutoff positions are permitted; duplicate labels
simply aggregate their numerator contributions.

The independent `ExactSplittingMarginals001Callers.lean` compiled warning-free.
It exercises the unrestricted identities, zero numerator against infinite credit,
a zero split with potentially infinite selected-block sum and a positive residual
normalization. Both public support theorems use only `propext`, `Classical.choice`
and `Quot.sound`, as recorded in `ExactSplittingMarginals001.log`.

The mathematical argument is short, direct and suitable for the eventual
splitting sampler proof. Full joint law, source CTE execution and termination
remain separate obligations before that sampler can be accepted.
