# Critical coin mathematics: independent design pass

Reviewer: `/root`. This reviews the supporting argument, not a sampler acceptance.
The final continued-logarithm source theorem, caller and axiom checks remain with
`review_exact_a`.

The finite true/false return masses match the actual fair two-call recursion in
`continuedLogarithm`: one fair branch samples the coefficient coin; the other
calls the tail, returning false on success and retrying the current position on
failure. Final coefficients bypass recursion. Reachable indices stop at the first
final coefficient.

Writing the missing mass as $d_i=1-t_i-f_i$, its exact next-depth recurrence is
$d'_i=(d_{i+1}+f_{i+1}d_i)/2$.
Since $f_{i+1}\le1-d_{i+1}$, a common bound $d_i\le s$ propagates to
$s-s^2/2$. The proved bound $s_n\le2/(n+2)$ supplies almost-sure termination
without a finite expected-time assumption. Bounding each return mass by the
canonical continued-fraction mass and squeezing the deficit identifies both
limits. The canonical bias satisfies $p_i=a_i/(1+p_{i+1})$.

The arbitrary-credit transport deliberately works in NNReal/ENNReal. Positive
true bias justifies multiplication by infinite true credit. At bias one, the
finite false mass is identically zero; the explicit endpoint case avoids the
invalid general continuity claim at $0\cdot\infty$.

The generic CTE theorem is a finite-tree induction from contradictory unit error
credit, followed by `twp_err_liminf`. The concrete sampler must still prove its
one-layer execution step and nonvalue condition; neither is assumed here to
establish a concrete sampler law.

**Required presentation polish:** expose the missing-mass recurrence in the pure
math file and use it to explain or streamline `missing_le`; its current product
lower-bound proof is correct but makes the branching comparison harder to see.
The final source instantiation must remain straightforward symbolic execution.

Inspected source hashes (before that requested polish):

- `SampLib/Distributions/CriticalBranching.lean`: `42d7ee1eb7f3d1f7cb9a2c8fa56117264668d851464276fa99b386cb0480a2f0`
- `SampLib/Distributions/CriticalCoin.lean`: `0b52502f999a436f60317897f575c2bdaa89964682a682d024133153a43d117e`
- `SampLib/Distributions/CriticalCoinKernel.lean`: `bc6b0d5ac02f110bf41c15505729337a29af1a03e1ed23a519387120f3447f3f`
- `SampLib/CriticalCoinRecursion.lean`: `ffa80012823a26df632a7ac7bb448d6ed67ff4d2d01e0fe621de46a54ec2cb3a`
