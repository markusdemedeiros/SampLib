# Expansion discrete review

Reviewer: `/root/expand_review_discrete`.

Accepted immutable batches:

- [Batch 001](ExpansionDiscreteBatch001.md): BetaBinomial, RandomBits, SymmetricGeometric.

- [Batch 002](ExpansionDiscreteBatch002.md): uniformRational, uniformFixed,
  uniformDyadic, NegativeHypergeometric, Himanshu.

- [Batch 003](ExpansionDiscreteBatch003.md): moduloReduction, multiplyShift,
  SequentialCoins, BinomialHalfBits, PoissonOne.

- [Batch 004](ExpansionDiscreteBatch004.md): PoissonRational, BitmaskRejection.

- [Batch 005](ExpansionDiscreteBatch005.md): CompoundPoisson, Skellam,
  NeymanTypeA, PolyaAeppli, ZeroTruncatedPoisson.

- [Batch 006](ExpansionDiscreteBatch006.md): MultivariatePoisson, LogUniform.

- [Batch 007](ExpansionDiscreteBatch007.md): WeightedReservoirOne,
  DivisionRejection, DebiasedModulo.

- [Batch 008](ExpansionDiscreteBatch008.md): BinomialBinary, Cub,
  FlatChoice, LemireUniform.

- [Batch 009](ExpansionDiscreteBatch009.md): Borel, OneillUniform,
  FisherHypergeometric.

- [Batch 010](ExpansionDiscreteBatch010.md): LogarithmicSeries, Multinomial,
  WeightedWithoutReplacement, CumulativeDraw, CumulativeChoice.

- [Batch 011](ExpansionDiscreteBatch011.md): UniformFromModulus, NegativeMultinomial,
  WalleniusHypergeometric.

- [Batch 012](ExpansionDiscreteBatch012.md): RationalChoice, UniformBinaryFloat.

- [Batch 013](ExpansionDiscreteBatch013.md): FisherMultivariate, TwoLevelChoice, FYKY.

- [Batch 014](ExpansionDiscreteBatch014.md): DiscreteLaplace, FloatingMultiply,
  FastDiceRoller.

- [Batch 015](ExpansionDiscreteBatch015.md): CumulativeChoice and RationalChoice
  classification corrections only; no additional sampler count.

`ExpansionDiscreteCandidates.json` contains cumulative root-ready metadata.
`ExpansionDiscreteCallers.lean` is the editable next-batch workspace; accepted
receipts always refer to immutable batch-specific callers.
