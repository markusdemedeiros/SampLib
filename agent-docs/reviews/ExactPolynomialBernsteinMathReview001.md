# Polynomial Bernstein mathematics: independent design review

Reviewer: `/root`. This reviews the exact conversion and degree-existence
argument. `review_exact_a` retains concrete source conversion/check/search,
public-domain and arbitrary-credit caller acceptance.

The source coefficients are exactly
`b(n,k)=sum_j a(j)*choose(k,j)/choose(n,j)`, not samples f(k/n) of a Bernstein
approximation. The binomial factorial-moment identity proves exact evaluation:
`choose(k,j)*bernstein(n,k)` shifts to
`choose(n,j)*x^j*bernstein(n-j,k-j)`. Terms k<j vanish and the remaining Bernstein
basis sums to one. Division uses the positive coefficient choose(n,j) only when
j<=n. Exchanging the two finite sums gives the actual input polynomial without
an approximation or probabilistic correctness premise. Constants, degree zero
and input endpoints are included.

For fixed j, the elevated coefficient ratios are values on the degree-n grid of
a continuous falling-product function. Each normalized factor
`(x-i/n)/(1-i/n)` converges to the coordinate function in C([0,1],R), and finite
products and sums preserve that convergence. The grid identity is exact even
when k<j: falling factorials supply the necessary zero. It also handles the
formally defined small degrees; uniform convergence needs only the eventual
large-degree regime, not a false denominator-positivity assertion at every n.

The continuous-map compact-open argument is an economical way to express the
uniform probability margin. If the target polynomial is strictly inside (0,1)
on the compact unit interval, its continuous-map neighborhood stays inside that
open interval. Uniform convergence therefore puts every elevated grid coefficient
in (0,1) at all sufficiently large degrees. Intersecting with n>=degree gives a
finite admissible degree for the actual increasing search.

Strict boundedness is a sufficient automatic-search corollary. The operational
proof can separately use any finite admissible-degree witness, covering examples
with endpoint zeros or ones when their actual elevated coefficients permit it.
These statements do not claim that every nonnegative polynomial, including one
with an isolated interior zero, admits a nontrivial terminating Bernoulli factory.
No verification obligation is hidden in a desired-law assumption.

Both files use standard finite binomial identities and continuous-map convergence
lemmas, with short local algebra. The argument is clear and mathematically useful.
No correctness or mathematical presentation revisions requested. Inspected hashes:

- `SampLib/Distributions/PolynomialBernstein.lean`: `fc124e445f31b91d0e1895b2b036a7d22442e631b05a77d0b9fef91641a01ef1`
- `SampLib/Distributions/PolynomialBernsteinElevation.lean`: `c2e882270d29cf42307edd2bdb1cbcc8146292849bcbd78c49369f4c15f9e276`
