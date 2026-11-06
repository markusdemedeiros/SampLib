# Minimum-complement mathematics: independent design review

Reviewer: `/root`. This is a supporting mathematical review; concrete source
execution, public callers, exact-head checks and axioms remain with
`review_exact_a` before sampler acceptance.

The seven modules expose the argument clearly. The acceptance coefficient
cancels the binomial sampling coefficient; shifting the surviving band leaves a
complete binomial expansion and gives `(4p(1-p))^m/2`, independently of padding.
Admissibility is proved separately: the coefficient ratio is symmetric and
increases to the middle. The two parity-specific central-binomial recurrences
imply sixteenfold growth of `n * middle(n)^2` every two rows. Telescoping and
`2m <= 3r` give the needed factor-two bound. Actual padding `floor(2m/3)+1`
is positive and satisfies that inequality. No asymptotic approximation is used.

For the fair pending-level walk, set `t=2sqrt(p(1-p))` and take the smaller root
`h=(1-sqrt(1-t^2))/t`. The total definition at `t=0` satisfies the same
division-free quadratic identity `2h=t(1+h^2)`. The harmonic output coefficient
`t^(s+1)h^k/2` is initially `min(p,1-p)` and, at absorption after `2m-1` steps,
is exactly the conditional binomial probability. The absorption identity
requires `m>0`; the concrete source must establish that invariant.

Termination does not assume a finite global mean hitting time. At a ghost upper
barrier `B`, escape credit `k/B` is harmonic and pays one at the barrier.
The bounded potential `k(B-k)+1` loses one in conditional expectation and funds
amplification `(B^2+1)/B^2 > 1`. Moving the barrier out makes initial escape
credit vanish; choosing local slack `delta/(2B)` also makes its initial potential
cost at most `delta/2`. The combined Budget.expectation keeps output, escape and
termination credits in one inequality, matching the actual up/down transition.
The barrier is a proof device and must not alter the source walk.

The kernel lifts these identities using Boolean mixtures and ENNReal integrals;
continuation credits are never converted to reals. Thus infinite credits and
zero-probability outputs remain sound. Endpoint checks in the definitions cover
`p=0`, `p=1`, and the critical fair case `p=1/2` (where `t=h=1`). The square-root
and quadratic arguments do not divide by a parameter without a zero case.

No mathematical correctness or presentation revisions requested. The small
algebraic automation blocks stay in mathematical support, outside the main CTE
argument. Inspected source hashes:

- `SampLib/Distributions/MinimumComplementBarrier.lean`: `9e2eb9792b0ddffbdfdd06c06bd67b714ec860a786aaf0613ced00f06f07fa9c`
- `SampLib/Distributions/MinimumComplementBinomial.lean`: `4da583ec60a4287e008fec0860052a117c697109475543157a0198d7a768adc3`
- `SampLib/Distributions/MinimumComplementBudget.lean`: `687c860a7c1d55eee93641e188fac87238b07defe800b748062687f184064148`
- `SampLib/Distributions/MinimumComplementCentral.lean`: `25469ea8a303bc8581c13903ac1db742d88008f4c99c7b99c87f4864fda441cb`
- `SampLib/Distributions/MinimumComplementCoefficients.lean`: `2f1a2ad5ab387663b33543378bb2eac0aac08b1eefb25e3e87cfa588708a72f6`
- `SampLib/Distributions/MinimumComplementKernel.lean`: `8f3f3f3bddfb0334470c6cb52e1bb1189ae2de25d66472d0780668b01bd9b52a`
- `SampLib/Distributions/MinimumComplementWalk.lean`: `0bbabb7656447b1faa1d1314284377da4c8c778c6cdf8d180390790393b5d2d2`
