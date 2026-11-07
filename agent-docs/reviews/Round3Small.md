# Round 3 review: Uniform, Continuous, Combinatorial, and Core

Reviewer: `round3_review_small`. Base commit: `8f819b7`. Scope: `SampLib/Uniform/`,
`SampLib/Continuous/`, `SampLib/Combinatorial/`, and `SampLib/Core/`, except
`Core/Retry.lean` and `Core/Laws/Retry.lean`, which another reviewer covers.

## Verdict

I accept all four directories. Every proof below keeps its public statement, builds
without warnings, and reads at least as clearly as before.

## Public specs and new proof hashes

The `refactor_receipts.py --list` run lists 35 stale historical proofs and no stale
exact-campaign rows. Each row gives the sampler, the public spec, and the SHA-256 hash of
the current proof file.

| Sampler | Public spec | Proof hash |
| --- | --- | --- |
| `Occil.uniformInt` | `SampLib.UniformInt.uniformInt_distSpec` | `2e98026bfad60f17f2aed50857a1fb5d46b583894d25a29e66d563bd4502b63e` |
| `Occil.rndInt` | `SampLib.RndInt.rndInt_distSpec` | `7ae2ca3c44b23d69dc1c421020e5d6161cff879fb0eef77ef70fa25dd89be258` |
| `Occil.rndIntRange` | `SampLib.RndIntRange.rndIntRange_distSpec` | `e7ce95b66881cebce351d22e1877471695cb7227af815a23c5b589ad4463465a` |
| `Occil.rndIntExcRange` | `SampLib.RndIntExcRange.rndIntExcRange_distSpec` | `307d0ed81175b2ecf7d187a4ef8ec156da67a1578c9e9dcd0f22ced9775b8077` |
| `Occil.fairCoin` | `SampLib.FairCoin.fairCoin_distSpec` | `30da46b90898325cb41ca2977c15b932b412b32f6d5dc00ba063300a7d070781` |
| `Occil.rationalCoin` | `SampLib.RationalCoin.rationalCoin_distSpec` | `30955f5b4a08f319faa777ebc284b0b2c0b37ca736abcc238e2f9d61bc581937` |
| `Occil.geometricFailures` | `SampLib.GeometricFailures.geometricFailures_distSpec` | `792b6293980ed3656d21816fba7a3ba602f8324efbe61cbdc79c5bb913755192` |
| `Occil.iterateCoin` | `SampLib.IterateCoin.iterateCoin_distSpec` | `c0ffa1e10c63c718938a8daa65c45ba4a64169883492115bd80c8199d800abe4` |
| `Occil.uniformMin` | `SampLib.UniformMin.uniformMin_distSpec` | `c50b73da9279b9dc9c3bc53ed042e04159483eecbe6a851266a14962305d3717` |
| `Occil.uniformMax` | `SampLib.UniformMax.uniformMax_distSpec` | `62bcfa07b1f7163be9133458b6581792f5f6b2cd428aa74098027659fe427a38` |
| `Occil.uniformSum` | `SampLib.UniformSum.uniformSum_distSpec` | `a212e5499fcef20eced159c642f55a16e80cd3c9295a06f387d52a300acabbe3` |
| `Occil.mixture` | `SampLib.Mixture.mixture_distSpec` | `4ac9f596891da0cf979039e159883997bffa2ba8894e78bd27565fcd3ef21cba` |
| `Occil.rejection` | `SampLib.Rejection.rejection_distSpec` | `39df22b41e3f964c72f6aeb0a16ac109c747a89e52d57117133e10d163aca40c` |
| `Occil.choice` | `SampLib.Choice.choice_distSpec` | `a09eb2ce36822fd422cfe7d75e47020b6900bdc516364cadcf936d120859f126` |
| `Occil.sampleWithReplacement` | `SampLib.SampleWithReplacement.sampleWithReplacement_distSpec` | `3dab991328cd65ba32e0ed99ed22b40b6c3db16b9b680312d20c7ede36a1f4cb` |
| `Occil.sampleWithoutReplacement` | `SampLib.SampleWithoutReplacement.sampleWithoutReplacement_distSpec` | `85c9530c1b9f18e9a4af83a1393289e99b3fb54e615d209519fc6076d6399135` |
| `Occil.sampleInOrder` | `SampLib.SampleInOrder.sampleInOrder_distSpec` | `feddede9204dbe83a59f3f0345f4f792c23866360df350b87d3179f1edfd4c1a` |
| `Occil.exponential` | `SampLib.Exponential.exponential_distSpec` | `d15af1664d1009c313ff717162122453fac186c4ee156d042fc4e24d31f9f37e` |
| `Occil.laplace` | `SampLib.Laplace.laplace_distSpec` | `e4d1be6424f0a5f8f0876ce1772084b525b96d00926399de104e0fab004a81ad` |
| `Occil.erlang` | `SampLib.Erlang.erlang_distSpec` | `8e2b85440523370f9db54fd112d7546e6203ea25e5df174392bd4e7dec2e0768` |
| `Occil.flipBits` | `SampLib.FlipBits.flipBits_distSpec` | `5bfe4d6596022865268628736145606f1fbe9f211894000a520383ffe85fff49` |
| `Occil.expHalfCoin` | `SampLib.ExpHalfCoin.expHalfCoin_distSpec` | `561f83345ce8c0784d6e8fda5167e9966a93268b6d97fe04d495b6ddba8971bc` |
| `Occil.gaussianInteger` | `SampLib.GaussianInteger.gaussianInteger_distSpec` | `b496f3e7e9adce1659525f9ecb8235696edb886fa00cd518dc77d55443bb90b3` |
| `Occil.gaussian` | `SampLib.Gaussian.gaussian_distSpec` | `f2af434970e7a31066ea5bf05c4f5fc559e01a26bc55133b8811978bf1a748f8` |
| `Occil.orderStatistic` | `SampLib.OrderStatistic.orderStatistic_distSpec` | `63061d4c50c021896ea4a4fb507d203f4af97a6bf02d449f4a6ed433a2586b4f` |
| `Occil.shuffle` | `SampLib.Shuffle.shuffle_distSpec` | `40c308d087f68859456c706781d772ad6b19f20527a9ef1910173978924e6413` |
| `Occil.positiveComposition` | `SampLib.PositiveComposition.positiveComposition_distSpec` | `b35d277ea978e4c174cc2a668eb71be736e86df3a13d6be001d4aff37696b880` |
| `Occil.weakComposition` | `SampLib.WeakComposition.weakComposition_distSpec` | `a9b44eb503d47ab234224b3df7dd3da0444bf449f8b60ac55063fb92b431c929` |
| `Occil.sattolo` | `SampLib.Sattolo.sattolo_distSpec` | `1cf8118463bf6ce88f3beebf777f3f58e9dafca5baac2e31cc3d3c883be8a166` |
| `Occil.randomGraph` | `SampLib.RandomGraph.randomGraph_distSpec` | `77e9c91be98518f6aef63288da5e2a2e96a66e9f7d41da140af8d1fba981c404` |
| `Occil.reservoir` | `SampLib.Reservoir.reservoir_distSpec` | `8604fb6a38d3b18b69901acda652f87c97e7f7e9a85ffeaf7f6c7838bc77d452` |
| `Occil.uniformFromModulus` | `SampLib.UniformFromModulus.uniformFromModulus_distSpec` | `cc1da14310c2e7c89dd327b750408df985520b9c266edf9589e795a5a9d88317` |
| `Occil.derangement` | `SampLib.Derangement.derangement_distSpec` | `352d3af3eee812e1b8ddbcda2e31d0e225ead7197d934df1a3903f3b9f579b89` |
| `Occil.fastDiceRoller` | `SampLib.FastDiceRoller.fastDiceRoller_distSpec` | `e7acbf00015c380bc363e66743cf610e1fa028c0603f81a9297791d955bf9db6` |
| `Occil.realCoin` | `SampLib.RealCoin.realCoin_distSpec` | `fe06f7612f50b7b17e67d94d9b112d8c8733a387c17b3961ab10711d95481253` |

## What I checked

- **Statements.** No public spec, `law`, `credit`, `output`, or `bias` definition changes
  its name, namespace, or body. Moved definitions keep their fully qualified names. A
  line-by-line comparison of the diff shows that every removed line reappears in a new
  module, apart from the retry migrations below, the rewritten `Rejection` conservation
  proof, and `private` modifiers that the split had to drop. Statement equality rests on
  the lead's mechanical pin check with `statement_pins.py`.
- **Retry migrations.** `UniformFromModulus` (both loops), `Exponential`
  (`twp_loop_forall`), `Gaussian`, `GaussianInteger`, and `Rejection` now use
  `Retry.twp_loop`. Each migration follows the recipe: the round body stays the same, and
  the retry branch passes `Hcredit` straight to the hypothesis. `GaussianSelector` and
  `GeometricFailures` keep `ErrorCredit.Induction.simple`, as the retry brief directs.
- **Rejection mathematics.** `Rejection.expectation_preservation` now applies
  `Retry.lintegral_kernel_le` and `Retry.mul_factor_le_one`. The statement stays the same,
  and the proof is shorter.
- **Math and Iris split.** Every `Laws/` module in scope imports only mathlib, `Laws/`
  modules, and the `Metrology.ProbLang` measure modules. This round fixes the earlier leaks
  in `Combinatorial/Laws/Compositions`, `Combinatorial/Laws/RandomGraph`,
  `Core/Laws/FiniteGrid`, and `Core/Laws/IntegerIntervals`. The `Reservoir` scan loop
  moves to `Combinatorial/Support/ReservoirScan`, and the spec file keeps only symbolic
  execution.
- **Hygiene.** No `sorry`, `admit`, `axiom`, `native_decide`, or `set_option` appears in
  scope. No line exceeds 100 columns. Every new module opens with a `/-! # Title`
  docstring.
- **Build.** `lake build` of every module that the 15 caller files import succeeds with no
  warnings.
- **Callers.** These caller files compile through the gate with no errors and no
  warnings: `CoinCallers`, `DiscreteCallers`, `ExpansionDiscreteBatch011Callers`,
  `ExpansionDiscreteBatch014Callers`, `ExpansionStructuredBatch001Callers`,
  `ExpansionStructuredBatch002Callers`, `ExpansionStructuredBatch003Callers`,
  `ExpansionStructuredBatch004Callers`, `ExpansionStructuredBatch005Callers`,
  `ExpansionStructuredBatch007Callers`, `ExpansionStructuredBatch009Callers`,
  `ExpansionStructuredBatch014Callers`, `NextBatchContinuousCallers`,
  `NextBatchFiniteCallers`, and `StructuredCallers`.

## Nits

None of these nits blocks acceptance.

- The split turns some former `private` helpers into public declarations, for example
  `RationalCoin.zero_credit`, `SampleWithReplacement.measurable_cons`, and
  `Reservoir.ticketCredit`. Cross-module use requires this change. Several of these
  helpers lack a docstring.
- `Rejection.terminationFactor` duplicates `Retry.factor (μ s)` by definition. The proof
  now relies on that definitional equality, so the shared name would read more clearly.
- Several `Continuous/Laws/` modules keep a redundant `section mathematics` wrapper.
- `Combinatorial/Shuffle.lean` keeps a `section mathematics` that holds encoding lemmas.
  `Sattolo.lean` renames its matching section to `encoding`.
- The family README files still give the old `Laws/` and `Support/` module counts. For
  example, `Uniform/README.md` lists 3 `Laws/` modules, and the directory now holds 9.
- `Continuous/Laws/Gaussian.lean` still imports
  `Metrology.TotalEris.Examples.Samplers.Gaussian`. This leak predates the round.
- In `Exponential`, `Gaussian`, `GaussianInteger`, and `Rejection`, the migrated proofs
  name `%hε` but never use it. `UniformFromModulus` writes `%_` instead.
