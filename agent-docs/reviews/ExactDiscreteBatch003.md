# Exact discrete sampler review, batch 003

Reviewer: `/root/review_exact_b`. Accepted core theorem
`SampLib.GeneralizedSibuya.generalizedSibuya_distSpec`, SHA-256 `afac9b71cb6d4ce70f4b3da21faee1087d81f7584dde79932524a1c717a78d20`.

Domain: All positive rational alpha and nonnegative rational nu with alpha < nu+1, represented by unreduced natural numerator/positive denominator pairs. Includes nu=0 and alpha>1 where admissible. Output is positive; no finite-mean assumption.

Clearing the rational denominators turns the source's reciprocal hazard into
exactly the first-marked urn hazard. The target law is independently defined
as one plus its proper waiting count, with a canonical rising-product singleton
mass. Its harmonic lower bound proves vanishing survival even in infinite-mean
regimes. The expectation identity handles arbitrary ENNReal credit, including
zero-probability branches multiplied by infinity.

The actual source loop retains its original numerator multiplication. Named
numerator/denominator arithmetic identifies each rational coin with the urn
hazard. The CTE proof is the stop/continue symbolic step followed by the existing
finite-horizon survival rule; no concrete target-law or termination premise is
assumed. This is a genuine source proof, not only a measure-theoretic statement.

Independent targeted build, exact-head/noncircular audit and caller passed
warning-free. The caller retains arbitrary Iris frame and arbitrary credit,
including infinity, and tests nu=0 with alpha=1/2, alpha=3/2 with nu=1, canonical
atoms and exclusion of output zero. Both public spec and mass theorem use only
propext, Classical.choice and Quot.sound. ExactDiscreteBatch003.log preserves
commands and outputs. The immutable receipt binds the full local source closure,
independent caller and current clutch06a7b3e dependency context.
