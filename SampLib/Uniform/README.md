# Uniform

This directory holds the proofs for uniform integers and primitive coins.

For how the directories fit together, see the [library layout](../README.md#layout).

## Verified samplers (9)

| Sampler | Law | Proof | Code |
| --- | --- | --- | --- |
| `Occil.fairCoin` | $\mathrm{Bern}\!\left(\frac12\right)$ | [FairCoin](FairCoin.lean) | [Uniform.lean](../../code/Samplers/Uniform.lean#L57) |
| `Occil.fastDiceRoller` | $\mathrm{Unif}\{0,\ldots,n-1\}$ | [FastDiceRoller](FastDiceRoller.lean) | [Uniform.lean](../../code/Samplers/Uniform.lean#L26) |
| `Occil.rationalCoin` | $\mathrm{Bern}\!\left(a/b\right)$ | [RationalCoin](RationalCoin.lean) | [Uniform.lean](../../code/Samplers/Uniform.lean#L60) |
| `Occil.realCoin` | $\mathrm{Bern}\!\left(p\right)$ | [RealCoin](RealCoin.lean) | [Uniform.lean](../../code/Samplers/Uniform.lean#L67) |
| `Occil.rndInt` | $\mathrm{Unif}\{0,\ldots,h\}$ | [RndInt](RndInt.lean) | [Uniform.lean](../../code/Samplers/Uniform.lean#L16) |
| `Occil.rndIntExcRange` | $\mathrm{Unif}\{\ell,\ldots,h-1\}$ | [RndIntExcRange](RndIntExcRange.lean) | [Uniform.lean](../../code/Samplers/Uniform.lean#L22) |
| `Occil.rndIntRange` | $\mathrm{Unif}\{\ell,\ldots,h\}$ | [RndIntRange](RndIntRange.lean) | [Uniform.lean](../../code/Samplers/Uniform.lean#L19) |
| `Occil.uniformFromModulus` | $\mathrm{Unif}\{0,\ldots,n-1\}$ | [UniformFromModulus](UniformFromModulus.lean) | [Uniform.lean](../../code/Samplers/Uniform.lean#L39) |
| `Occil.uniformInt` | $\mathrm{Unif}\{0,\ldots,n-1\}$ | [UniformInt](UniformInt.lean) | [Uniform.lean](../../code/Samplers/Uniform.lean#L12) |

## Contents

- Top level: 9 modules
- [`Laws/`](Laws): 3 modules with target laws, kernels, and expectation lemmas

---

`python3 agent-scripts/law_index.py` generates this file.
