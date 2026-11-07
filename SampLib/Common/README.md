# Common

This directory holds the laws and helpers that several families share, together with every helper that they import.

For how the directories fit together, see the [library layout](../README.md#layout).

## Verified samplers (2)

Each of these samplers has an accepted proof in this directory:

| Sampler | Law | Proof | Code |
| --- | --- | --- | --- |
| `Occil.DiscreteExtra.rationalPowerCoin` | $\mathrm{Bern}(p^{a/b})$ | [RationalPower](RationalPower.lean) | [Tails.lean](../../code/Samplers/Discrete/Tails.lean#L21) |
| `Occil.FactoryExtra.rationalPower` | $\mathrm{Bern}\!\left(p^{a/b}\right)$ | [RationalPower](RationalPower.lean) | [Powers.lean](../../code/Samplers/Bernoulli/Powers.lean#L15) |

## Contents

The directory holds these modules:

- Top level: 8 modules
- [`Laws/`](Laws): 33 modules with target laws, kernels, and expectation lemmas
- [`Syntax/`](Syntax): 3 modules with unfolding lemmas for the `pl%` source terms

---

`python3 agent-scripts/law_index.py` generates this file.
