# Weighted

This directory holds the proofs for weighted choice: tables, trees, alias and optimal samplers, and entropy recycling.

For how the directories fit together, see the [library layout](../README.md#layout).

## Verified samplers (38)

Each of these samplers has an accepted proof in this directory:

| Sampler | Law | Proof | Code |
| --- | --- | --- | --- |
| `Occil.Weighted.bitmaskRejection` | $\mathrm{Unif}\{0,\ldots,n-1\}$ | [BitmaskRejection](BitmaskRejection.lean) | [Uniform.lean](../../code/Samplers/Weighted/Uniform.lean#L25) |
| `Occil.Weighted.cumulativeChoice` | $\mathrm{Cat}(w)$ | [CumulativeChoice](CumulativeChoice.lean) | [Tables.lean](../../code/Samplers/Weighted/Tables.lean#L42) |
| `Occil.Weighted.cumulativeDraw` | $\mathrm{Cat}(w)$ | [CumulativeDraw](CumulativeDraw.lean) | [Tables.lean](../../code/Samplers/Weighted/Tables.lean#L30) |
| `Occil.Weighted.fastLoadedDiceRoller` | $\mathrm{Cat}(w)$ | [FastLoadedDiceRoller](FastLoadedDiceRoller.lean) | [Trees.lean](../../code/Samplers/Weighted/Trees.lean#L47) |
| `Occil.Weighted.fyky` | $\mathrm{Unif}\{0,\ldots,n-1\}$ | [FYKY](FYKY.lean) | [Uniform.lean](../../code/Samplers/Weighted/Uniform.lean#L37) |
| `Occil.Weighted.hanHoshi` | $\mathrm{Cat}(w)$ | [HanHoshi](HanHoshi.lean) | [Trees.lean](../../code/Samplers/Weighted/Trees.lean#L73) |
| `Occil.Weighted.inclusionSplitting` | $\lvert S\rvert=k,\quad\Pr(i\in S)=kw_i/\sum_jw_j\ \text{(marginals)}$ | [InclusionSplitting](InclusionSplitting.lean) | [Reservoir.lean](../../code/Samplers/Weighted/Reservoir.lean#L44) |
| `Occil.Weighted.inclusionSystematic` | $\lvert S\rvert=k,\quad\Pr(i\in S)=kw_i/\sum_jw_j\ \text{(marginals)}$ | [InclusionSystematic](InclusionSystematic.lean) | [Reservoir.lean](../../code/Samplers/Weighted/Reservoir.lean#L86) |
| `Occil.Weighted.knuthYao` | $\mathrm{Cat}(w)$ | [KnuthYao](KnuthYao.lean) | [Trees.lean](../../code/Samplers/Weighted/Trees.lean#L28) |
| `Occil.Weighted.moduloReduction` | $(x\mapsto x\bmod n)_*\mathrm{Unif}\{0,\ldots,2^b-1\}$ | [WordReductions](WordReductions.lean) | [Reductions.lean](../../code/Samplers/Weighted/Reductions.lean#L16) |
| `Occil.Weighted.multiplyShift` | $(x\mapsto\lfloor nx/2^b\rfloor)_*\mathrm{Unif}\{0,\ldots,2^b-1\}$ | [WordReductions](WordReductions.lean) | [Reductions.lean](../../code/Samplers/Weighted/Reductions.lean#L22) |
| `Occil.Weighted.randomBits` | $\mathrm{Unif}\{0,\ldots,2^k-1\}$ | [RandomBits](RandomBits.lean) | [Uniform.lean](../../code/Samplers/Weighted/Uniform.lean#L16) |
| `Occil.Weighted.rationalChoice` | $\mathrm{Cat}(w)$ | [RationalChoice](RationalChoice.lean) | [Tables.lean](../../code/Samplers/Weighted/Tables.lean#L64) |
| `Occil.Weighted.recycledSamples` | $\mathrm{Unif}\{0,\ldots,n-1\}^{\otimes k}$ | [RecycledSamples](RecycledSamples.lean) | [Uniform.lean](../../code/Samplers/Weighted/Uniform.lean#L71) |
| `Occil.Weighted.recycledUniform` | $\mathrm{Unif}\{0,\ldots,n-1\}$ | [RecycledUniform](RecycledUniform.lean) | [Uniform.lean](../../code/Samplers/Weighted/Uniform.lean#L53) |
| `Occil.Weighted.uniformBinaryFloat` | $\text{binary grid uniform approximation}$ | [UniformBinaryFloat](UniformBinaryFloat.lean) | [Uniform.lean](../../code/Samplers/Weighted/Uniform.lean#L95) |
| `Occil.Weighted.uniformDyadic` | $(K,2^b),\ K\sim\mathrm{Unif}\{0,\ldots,2^b-1\}$ | [UniformFormats](UniformFormats.lean) | [Uniform.lean](../../code/Samplers/Weighted/Uniform.lean#L83) |
| `Occil.Weighted.uniformFixed` | $\mathrm{Unif}\{0,\ldots,s-1\}$ | [UniformFormats](UniformFormats.lean) | [Uniform.lean](../../code/Samplers/Weighted/Uniform.lean#L88) |
| `Occil.Weighted.uniformRational` | $(K,m),\ K\sim\mathrm{Unif}\{0,\ldots,m-1\}$ | [UniformFormats](UniformFormats.lean) | [Uniform.lean](../../code/Samplers/Weighted/Uniform.lean#L79) |
| `Occil.Weighted.weightedReservoirOne` | $\mathrm{Cat}(w)$ | [WeightedReservoirOne](WeightedReservoirOne.lean) | [Reservoir.lean](../../code/Samplers/Weighted/Reservoir.lean#L17) |
| `Occil.WeightedVariants.debiasedModulo` | $\mathrm{Unif}\{0,\ldots,n-1\}$ | [DebiasedModulo](DebiasedModulo.lean) | [Reductions.lean](../../code/Samplers/Weighted/Reductions.lean#L84) |
| `Occil.WeightedVariants.divisionRejection` | $\mathrm{Unif}\{0,\ldots,n-1\}$ | [DivisionRejection](DivisionRejection.lean) | [Reductions.lean](../../code/Samplers/Weighted/Reductions.lean#L73) |
| `Occil.WeightedVariants.fenwickDraw` | $\mathrm{Cat}(w)$ | [FenwickDraw](FenwickDraw.lean) | [Dynamic.lean](../../code/Samplers/Weighted/Dynamic.lean#L68) |
| `Occil.WeightedVariants.flatChoice` | $\mathrm{Cat}(w)$ | [FlatChoice](FlatChoice.lean) | [Choice.lean](../../code/Samplers/Weighted/Choice.lean#L56) |
| `Occil.WeightedVariants.floatingMultiply` | $\left(x\mapsto\lfloor\mathrm{round}_p(nx)/2^b\rfloor\right)_*\mathrm{Unif}\{0,\ldots,2^b-1\}$ | [FloatingMultiply](FloatingMultiply.lean) | [Reductions.lean](../../code/Samplers/Weighted/Reductions.lean#L66) |
| `Occil.WeightedVariants.lemireUniform` | $\mathrm{Unif}\{0,\ldots,n-1\}$ | [LemireUniform](LemireUniform.lean) | [Reductions.lean](../../code/Samplers/Weighted/Reductions.lean#L38) |
| `Occil.WeightedVariants.oneillUniform` | $\mathrm{Unif}\{0,\ldots,n-1\}$ | [OneillUniform](OneillUniform.lean) | [Reductions.lean](../../code/Samplers/Weighted/Reductions.lean#L96) |
| `Occil.WeightedVariants.optimalChoice` | $\mathrm{Cat}(w)$ | [OptimalChoice](OptimalChoice.lean) | [Optimal.lean](../../code/Samplers/Weighted/Optimal.lean#L73) |
| `Occil.WeightedVariants.optimalDraw` | $\mathrm{Cat}(w)$ | [OptimalDraw](OptimalDraw.lean) | [Optimal.lean](../../code/Samplers/Weighted/Optimal.lean#L53) |
| `Occil.WeightedVariants.sequentialCoins` | $\mathrm{Cat}(w)$ | [SequentialCoins](SequentialCoins.lean) | [Choice.lean](../../code/Samplers/Weighted/Choice.lean#L18) |
| `Occil.WeightedVariants.sortedChoice` | $\mathrm{Cat}(w)$ | [SortedChoice](SortedChoice.lean) | [Rejection.lean](../../code/Samplers/Weighted/Rejection.lean#L17) |
| `Occil.WeightedVariants.succinctChoice` | $\mathrm{Cat}(w)$ | [SuccinctChoice](SuccinctChoice.lean) | [Rejection.lean](../../code/Samplers/Weighted/Rejection.lean#L53) |
| `Occil.WeightedVariants.twoLevelChoice` | $\mathrm{Cat}(w)$ | [TwoLevelChoice](TwoLevelChoice.lean) | [Choice.lean](../../code/Samplers/Weighted/Choice.lean#L31) |
| `Occil.WeightedVariants.voseDraw` | $\mathrm{Cat}(w)$ | [AliasTable](Support/AliasTable.lean) | [Aliases.lean](../../code/Samplers/Weighted/Aliases.lean#L57) |
| `Occil.WeightedVariants.voseSamples` | $\mathrm{Cat}(w)^{\otimes k}$ | [VoseSamples](VoseSamples.lean) | [Aliases.lean](../../code/Samplers/Weighted/Aliases.lean#L68) |
| `Occil.aliasSamples` | $\mathrm{Cat}(w)^{\otimes k}$ | [AliasSamples](AliasSamples.lean) | [Sequential.lean](../../code/Samplers/Weighted/Sequential.lean#L42) |
| `Occil.weightedRejection` | $\mathrm{Cat}(w)$ | [WeightedRejection](WeightedRejection.lean) | [Sequential.lean](../../code/Samplers/Weighted/Sequential.lean#L12) |
| `Occil.weightedWithoutReplacement` | $\Pr(i_1,\ldots,i_k)=\prod_{j=1}^k\frac{w_{i_j}}{\sum_{i\notin\{i_1,\ldots,i_{j-1}\}}w_i}$ | [WeightedWithoutReplacement](WeightedWithoutReplacement.lean) | [Sequential.lean](../../code/Samplers/Weighted/Sequential.lean#L26) |

## Contents

The directory holds these modules:

- Top level: 35 modules
- [`Laws/`](Laws): 60 modules with target laws, kernels, and expectation lemmas
- [`Syntax/`](Syntax): 14 modules with unfolding lemmas for the `pl%` source terms
- [`Support/`](Support): 38 modules with CTE loop invariants and other program-level helpers

---

`python3 agent-scripts/law_index.py` generates this file.
