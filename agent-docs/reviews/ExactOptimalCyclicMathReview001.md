# Cyclic probability-matrix mathematics: independent design review

Reviewer: `/root`. This is supporting mathematical review, not final acceptance
of optimalDraw/optimalChoice. `review_exact_a` retains concrete preprocessing,
ordered scans, linear restart resources, full source domains and caller review.

The bit sequence is the source's actual finite prefix followed by its repeated
last block. `column_initial`, `column_succ` and `column_cycle` express precisely
that schedule; l<k keeps every inspected exponent nonnegative. BinaryTail sums
the actual bits with dyadic discounts. Nonnegativity, boundedness by one and the
one-bit recurrence are proved from a summable geometric majorant.

At the end of the first k columns, the scaled tail identity is
`2^k*T(0)=E+T(k)`. At the prefix boundary it is
`2^l*T(0)=floor(E/2^(k-l))+T(l)`. Periodicity equates the remaining tails.
Subtracting these finite scalar equations identifies the row mass with its exact
cyclic decoder divided by `2^k-2^l`. The repaired encoder fits k bits and decodes
the original numerator, including the all-ones probability-one endpoint. There
is no assumption that every binary expansion terminates, and zero rows stay zero.

Summing the row recurrence identifies the total remaining row mass with the
natural live-rank count. Its nonnegativity first justifies the natural subtraction;
this prevents a truncated subtraction from hiding a Kraft inequality. Each row
has at most unit remaining mass, so the live count is at most the number of rows
at every depth. Together with dyadic path mass this supplies the finite-cutoff
vanishing bound used by the separate DDG logic, without a finite mean-runtime
assumption or a per-period geometric estimate.

Exact finite row coefficients are moved to NNReal and ENNReal only after their
scalar recurrence. `row_expectation` then distributes multiplication over
arbitrary continuation credits. In particular a zero row multiplied by infinite
credit remains zero; no continuity claim for a vanishing coefficient times
infinity is used. The finite-cutoff limit and actual scan-state invariant remain
obligations of the imported DDG/source proof, not consequences claimed here.

The optional dummy row is the final index; when no padding is needed its rejection
index is -1 and cannot equal a natural label. Padding preserves every original
weighted credit and adds exactly `(D-W)*restartCredit`. With restart credit
`C+2*epsilon`, the coefficient of C becomes `(W+D-W)/D=1`, while the coefficient
of epsilon is at most one from `W<=D<=2W`. All cancellations use positive finite
natural W,D. This is valid for C or epsilon infinite; subtraction is restricted
to natural weights. Doubling is a uniform valid outer termination factor.

No correctness or mathematical presentation revisions requested. The finite
coefficient/tail proof and arbitrary-credit lift are separated clearly. Inspected
hashes:

- `SampLib/Distributions/OptimalCyclic.lean`: `d8a8c66f9f953d6403d6ab9f16989d08b7a63b7f17861c139385dce8e231730c`
- `SampLib/Distributions/OptimalCredits.lean`: `28c6083c093a779fe64d557c636672fe366053de96e297afc25146ddece8a0c1`
- `SampLib/Distributions/OptimalRejection.lean`: `6e5a62cf66ecd0ec424cfce28bf0725a0368c1d53dd5c5f10788a41f1dcd5d6e`
- `SampLib/Distributions/BinaryTail.lean`: `3aca9d89ea00a3668e56ce6e67d53e1bd0ad7c94c0965448cf90a218849244f3`
- `SampLib/Distributions/OptimalEncoding.lean`: `ccb03cc22b4f262a57873e60fe0a77b331c82790e3e147d6bbf9334e5f6f2b9b`
