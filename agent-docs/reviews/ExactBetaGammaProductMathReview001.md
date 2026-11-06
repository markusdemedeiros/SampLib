# Beta–gamma product mathematics: independent design review

Reviewer: `/root`; author: `/root/review_exact_a`. This reviews the pure
mathematical argument. The author does not independently accept it; final concrete
Gamma/Beta sampler source and client acceptance remains with `review_exact_b`.

The central theorem transforms arbitrary joint nonnegative extended-real credit
under two independent gamma densities. First translating y to s-x and applying
Tonelli isolates the sum s. For positive s, scaling x=s*u contributes Jacobian s;
the density identity factors the result into Beta(a,b) and Gamma(a+b,rate).
For negative s the original joint density vanishes pointwise. The remaining
s=0 boundary is Lebesgue-null. The u=0 and u=1 endpoints are likewise removed
explicitly, so shapes singular at zero do not require false pointwise endpoint
identities.

The scalar factorization expands the classical beta/gamma constants, combines
positive-base real powers, and uses exponential additivity. Gamma normalizers
and the rate are positive under the complete domain a,b,rate>0. All division and
cancellation happens in this finite scalar calculation. No output continuation
credit is converted to a real or subtracted.

Marginalizing the second gamma factor uses its normalized integral one. This
yields the full beta-times-gamma pushforward identity, not merely an equality of
means. Specializing b=1-a makes the sum-shape exactly one and identifies the
exponential factor for every 0<a<1 and positive rate. The arbitrary measurable
ENNReal expectation formulation follows the same joint argument and remains
valid for infinite credits and infinite credit on impossible negative outputs.
Concrete programs must still establish the required independent beta/exponential
draws and retain their joint world through multiplication.

The change of variables is implemented through standard translation, Tonelli and
one-dimensional Lebesgue scaling lemmas; it avoids an opaque multivariate
Jacobian tactic. The proof structure displays the mathematical argument clearly.
No correctness or mathematical presentation revisions requested.

Inspected source: `SampLib/Distributions/BetaExponentialProduct.lean`: `07df269948dbb45e5f599458d6c98e6223267402ed07306527d23d9c2042dc30`.
