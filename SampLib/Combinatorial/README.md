# Combinatorial

This directory holds the proofs for collection sampling, shuffles, and permutations.

For how the directories fit together, see the [library layout](../README.md#layout).

## Verified samplers (12)

Each of these samplers has an accepted proof in this directory:

| Sampler | Law | Proof | Code |
| --- | --- | --- | --- |
| `Occil.choice` | $\frac1n\sum_i\delta_{x_i}$ | [Choice](Choice.lean) | [Basic.lean](../../code/Samplers/Combinatorial/Basic.lean#L11) |
| `Occil.derangement` | $\mathrm{Unif}\{\pi\in S_n:\forall i,\pi(i)\ne i\}$ | [Derangement](Derangement.lean) | [Permutations.lean](../../code/Samplers/Combinatorial/Permutations.lean#L30) |
| `Occil.flipBits` | $(b_i\mathbin{\oplus}\mathrm{Bern}_i(p))_i$ | [FlipBits](FlipBits.lean) | [Permutations.lean](../../code/Samplers/Combinatorial/Permutations.lean#L39) |
| `Occil.positiveComposition` | $\mathrm{Unif}\{x\in\mathbb N_{>0}^n:\sum_i x_i=t\}$ | [PositiveComposition](PositiveComposition.lean) | [Basic.lean](../../code/Samplers/Combinatorial/Basic.lean#L86) |
| `Occil.randomGraph` | $G(n,p)$ | [RandomGraph](RandomGraph.lean) | [Basic.lean](../../code/Samplers/Combinatorial/Basic.lean#L105) |
| `Occil.reservoir` | $\mathrm{Unif}\{I\subseteq[n]:\lvert I\rvert=k\}\ \text{(unordered)}$ | [Reservoir](Reservoir.lean) | [Basic.lean](../../code/Samplers/Combinatorial/Basic.lean#L65) |
| `Occil.sampleInOrder` | $\mathrm{Unif}\{I\subseteq[n]:\lvert I\rvert=k\}$ | [SampleInOrder](SampleInOrder.lean) | [Basic.lean](../../code/Samplers/Combinatorial/Basic.lean#L25) |
| `Occil.sampleWithReplacement` | $\left(\frac1n\sum_i\delta_{x_i}\right)^{\otimes k}$ | [SampleWithReplacement](SampleWithReplacement.lean) | [Basic.lean](../../code/Samplers/Combinatorial/Basic.lean#L14) |
| `Occil.sampleWithoutReplacement` | $\mathrm{Unif}(\text{ordered distinct positions})$ | [SampleWithoutReplacement](SampleWithoutReplacement.lean) | [Basic.lean](../../code/Samplers/Combinatorial/Basic.lean#L17) |
| `Occil.sattolo` | $\mathrm{Unif}(\text{single }n\text{-cycles})$ | [Sattolo](Sattolo.lean) | [Permutations.lean](../../code/Samplers/Combinatorial/Permutations.lean#L12) |
| `Occil.shuffle` | $\mathrm{Unif}(S_n)$ | [Shuffle](Shuffle.lean) | [Basic.lean](../../code/Samplers/Combinatorial/Basic.lean#L47) |
| `Occil.weakComposition` | $\mathrm{Unif}\{x\in\mathbb N^n:\sum_i x_i=t\}$ | [WeakComposition](WeakComposition.lean) | [Basic.lean](../../code/Samplers/Combinatorial/Basic.lean#L95) |

## Contents

The directory holds these modules:

- Top level: 12 modules
- [`Laws/`](Laws): 6 modules with target laws, kernels, and expectation lemmas
- [`Syntax/`](Syntax): 1 modules with unfolding lemmas for the `pl%` source terms
- [`Support/`](Support): 2 modules with CTE loop invariants and other program-level helpers

---

`python3 agent-scripts/law_index.py` generates this file.
