# Exact factories batch 016

Reviewer: `/root/review_exact_a`.

This core continued-fraction verification covers the full finite coefficient domain of the actual source. Backward induction first establishes the tail law; at each position, the only remaining recursion is a retry with probability at most d/(a+d)<1. The arbitrary-credit mixture identity gives the backward fraction b/(a+d*tail). Terminal flags stop evaluation early. Neither finite proof nor public specification assumes the desired concrete sampler law, finite credits, scale<=numerator, or a uniform global retry bound. The companion infinite-stream theorem uses a bounded weighted state potential under the explicit sufficient progress condition d<=b<=a, with canonical continued-fraction uniqueness. Arbitrary positive infinite coefficients are deliberately excluded from that companion claim; some such streams fail to terminate.

Independent callers apply both public interfaces while retaining arbitrary Iris resources and arbitrary extended credits. The actual finite callback with coefficients (1,1,8,false) then (1,2,100,true) executes and has law1/5, demonstrating coverage beyond the infinite-progress subclass. The mathematical expectation and local amplification retain credits in ENNReal, including infinity. The finite theorem, program proof and companion infinite theorem print only standard axioms. These are two explicit domains of one catalogue sampler, not two new sampler entries.

## Accepted sources

- `Occil.Constants.rationalContinuedFraction`: `SampLib.FiniteRationalContinuedFraction.rationalContinuedFraction_finite_distSpec`; source SHA256 `2c1a521825502b8dcf664db6dfced97e4dfd61ad2275e1eb52dd4cd6d81a3f6b`.

## Evidence

Independent caller: [ExactFactoriesBatch016Callers.lean](ExactFactoriesBatch016Callers.lean).
The caller compiled without warnings or errors under the pinned `06a7b3e2` dependency context.
Every printed public specification uses only `propext`, `Classical.choice`, `Quot.sound`.
The receipt binds the complete project-local source closure and configuration/dependency context.
All direct implementation source files are unchanged from the frozen campaign baseline.
