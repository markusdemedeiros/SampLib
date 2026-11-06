# Johnk beta mathematics: independent design review

Reviewer: `/root/prove_general`; author: `/root/review_exact_a`. This covers the
pure mathematics. Final acceptance of the actual Beta program remains with
`review_exact_b`.

For every `a,b>0`, independent Beta(a,1) and Beta(b,1) proposals are accepted by
the strict event `x+y<1`, returning `x/(x+y)`. Removing their exponential tilts
expresses the power densities through unit-rate gamma densities. On the accepted
positive quadrant the sum constraint also supplies both proposal support bounds.

The previously reviewed beta–gamma coordinate transformation separates sum and
proportion. Restoring the tilt on `0<s<1` gives a normalized Beta(a+b,1) radial
factor. Its scalar integral leaves acceptance mass
`c = a*b/(a+b)*beta a b`, strictly positive throughout the stated domain. Thus the
restricted proposal pushforward is exactly `ofReal c • betaMeasure a b`;
normalizing yields the canonical Beta(a,b) measure.

All continuation credit remains in ENNReal, including infinite values. Finite
scalar cancellations involve only positive gamma normalizers. The exceptional
`x=0`, `y=0`, and `s=0` boundaries are removed explicitly almost everywhere,
covering shapes with singular endpoint densities. The strict guard is preserved.

Independent target and caller checks pass warning-free with only the standard
three axioms. The caller additionally derives `ofReal c≤1` for all positive
shapes and checks `c(1,1)=1/2`. No mathematical revisions requested. Concrete
source review must still establish fresh independent proposals, the acceptance
protocol, and shared ownership through division.

Inspected source: `SampLib/Distributions/JohnkBeta.lean`,
`da7384f6042238a444cf8c8a01a87b163a423e75a4bc6b081f535e6a1c0022a6`.
Its coordinate-transform dependency matches the prior root-reviewed
`BetaExponentialProduct.lean` hash
`07df269948dbb45e5f599458d6c98e6223267402ed07306527d23d9c2042dc30`.
Checks: `ExactJohnkBetaMathCallers001.lean`, `ExactJohnkBetaMathReview001.log`.
