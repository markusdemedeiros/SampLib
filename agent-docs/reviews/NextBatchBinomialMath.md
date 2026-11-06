# Independent binomial mathematics review

Reviewer: `/root`. Author: `/root/review_next_batch`.

Accepted `SampLib.Binomial.law_singleton`, `law_eq_binomial`, and
`lintegral_eq_sum` in `SampLib/Distributions/Binomial.lean`, SHA-256
`332a0b32e0d14943ce264f1c35d85558c615bea81eec88194e5c53e20112124d`.
The import bridge `SampLib/Distributions/BinomialMeasure.lean` has SHA-256
`35eba0a09d4cf117121ca3776843a39c78048b921e3182fccb44b05083c35373`.

The point-mass induction is Pascal's identity, with separate boundary and
out-of-support cases. It works at both endpoint biases and uses ENNReal
semiring identities without cancellation of potentially infinite values.
Equality of singleton masses identifies the existing independent-trial law
with mathlib's binomial measure. The finite expectation formula then follows
from mathlib's sum of weighted Dirac measures, for arbitrary ENNReal credits.
These results identify the law independently of the sampling program.

The bridge only publicly imports mathlib's module; it introduces no declarations.
The support build is warning-free. Independent endpoint and infinite-credit
checks compile in `NextBatchBinomialMathCallers.lean`, SHA-256
`fbd4e3699dbcce1b7b6f3e9c2c9ef7dd327a77e1dd9566f23a8b0ae039c76ad3`.
All three public lemmas depend only on `propext`, `Classical.choice`, and
`Quot.sound`. The persistent callers are included in the complete proof audit.
