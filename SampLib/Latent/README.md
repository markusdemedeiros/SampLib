# Latent

This directory holds the shared lazy-real machinery: the latent spec kinds, worlds, views, and uniform bags.

For how the directories fit together, see the [library layout](../README.md#layout).

## Verified samplers (2)

| Sampler | Law | Proof | Code |
| --- | --- | --- | --- |
| `Occil.PSRN.newByDigits` | $\mathsf{Lazy}[\text{digit-oracle real}]$ | [LatentDigits](LatentDigits.lean) | [Uniform.lean](../../code/Samplers/PSRN/Uniform.lean#L52) |
| `Occil.PSRN.newUniform` | $\mathsf{Lazy}[\mathrm{Unif}(0,1)]$ | [LatentUniform](LatentUniform.lean) | [Core.lean](../../code/Samplers/PSRN/Core.lean#L43) |

## Contents

- Top level: 25 modules
- [`Laws/`](Laws): 10 modules with target laws, kernels, and expectation lemmas
- [`Syntax/`](Syntax): 1 modules with unfolding lemmas for the `pl%` source terms

---

`python3 agent-scripts/law_index.py` generates this file.
