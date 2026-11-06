# Low-probability linear margin repair

Status: the canonical one-line repair is applied; its final public transport is
`SampLib.LinearLowProbability.linearLowProbability_distSpec`.

The sibling `SampLib.LowProbabilityRepair.algorithm` has a complete CTE proof in
`SampLib/Samplers/LowProbabilityRepair.lean`. It retains the advertised domain
`μ = (a/b)p ≤ ρ = m/n < 1/2`, including zero and contracting cases.

Apply this one-line change to `code/Samplers/Bernoulli/Linear.lean` only after the
current review-context migration is coordinated:

```diff
-          &linear coin (a * n) (b * #2 * m) (n - m) n #()
+          &linear coin (a * n) (b * #2 * m) #1 #2 #()
```

The inner bias is `μ/(2ρ) ≤ 1/2`. Its current margin is `1-ρ`, which demands the
unjustified stronger bound `μ/(2ρ) ≤ ρ`. The half-margin establishes the verified
inner factory's complete precondition. Conditioning on the logistic and rational
selectors gives output bias `μ`; the arbitrary-credit preservation lemma uses
these two mixtures directly.

After that patch, the canonical term and the sibling algorithm should be equal
by `rfl`; transport the public proof through that equality. The current canonical
term is not marked verified. The formal margin counterexample establishes a
contract mismatch; the existing rational upper-bound certificate remains the
separate evidence that the original output law is actually wrong.

Suggested closed runtime regressions, with a fresh rational coin callback:

| Input probability | a | b | m | n | Expected result |
| --- | ---: | ---: | ---: | ---: | --- |
| 1/8 | 2 | 1 | 1 | 4 | Bernoulli(1/4), old defect boundary |
| 3/16 | 2 | 1 | 2 | 5 | Bernoulli(3/8), expanding interior |
| 1/2 | 1 | 2 | 1 | 4 | Bernoulli(1/4), contracting boundary |
| 0 | 2 | 1 | 0 | 1 | Always false, zero upper bound |
| 0 | 2 | 1 | 1 | 4 | Always false, expanding zero bias |
| 1/8 | 2 | 1 | 1 | 2 | Guard failure, unchanged invalid domain |

Run both interpreters with matching seeds and check equality of the returned bit
streams, plus the existing binomial-frequency check for the first three cases.
These are runtime regressions, not statistical detection of the original defect:
the certified bias gap in the first case is only about `2.26e-7`, far below the
resolution of an ordinary regression batch.
