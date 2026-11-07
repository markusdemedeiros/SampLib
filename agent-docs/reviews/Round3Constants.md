# Round 3 review: Constants

Reviewer: `round3_review_constants`. Base commit: `8f819b7`.

## Scope

This review covers every file under `SampLib/Constants/` and the 45 samplers in the lead's
sampler list for this group.

## Result

The refactor is accepted. Every change keeps the theorem it proves and reads at least as
clearly as before.

## Public specs and proof hashes

The table lists every stale public spec and its new proof hash, exactly as
`refactor_receipts.py --list` prints them.

| Record | Sampler | Public spec | Proof hash |
| --- | --- | --- | --- |
| Exact (`/root/review_exact_a`) | `Occil.Constants.continuedLogarithm` | `SampLib.ContinuedLogarithm.continuedLogarithm_distSpec` | `8a0a0a10107fa253d1170594343da4c4932f311c540676019061f5e0b0424f80` |
| Exact (`/root/review_exact_a`) | `Occil.Constants.rationalContinuedFraction` | `SampLib.FiniteRationalContinuedFraction.rationalContinuedFraction_finite_distSpec` | `ad9f8af051c711af36c3b58b97d6f88ff8b24d9a4049a19c806fd555477ab3ed` |
| Exact (`/root/review_exact_a`) | `Occil.Constants.eContinuedFraction` | `SampLib.EContinuedFraction.eContinuedFraction_distSpec` | `613a1eecb604ef93dc523e8e73c810f0af4596398e1c7761f82ba128fa105821` |
| Exact (`/root/review_exact_a`) | `Occil.Constants.eDivThree` | `SampLib.EulerScaledConstants.eDivThree_distSpec` | `f2652d778ffc544ddb6c13429ab8cbe032926cbdc7142a459d6572524036fe53` |
| Exact (`/root/review_exact_a`) | `Occil.Constants.eMinusTwo` | `SampLib.EulerAffineConstants.eMinusTwo_distSpec` | `10962fe5f5f2ea9d2295daff68728e3448e01127b14c2e7a3c17f264af197ea9` |
| Exact (`/root/review_exact_a`) | `Occil.Constants.eMinusTwoContinuedFraction` | `SampLib.EContinuedFractionConstants.eMinusTwoContinuedFraction_distSpec` | `5b6e6fe63fd69f45efa96120b9245e4ed26c0d79d59541786c56d2ff9c1c2377` |
| Exact (`/root/review_exact_a`) | `Occil.Constants.eQuarter` | `SampLib.EulerScaledConstants.eQuarter_distSpec` | `f2652d778ffc544ddb6c13429ab8cbe032926cbdc7142a459d6572524036fe53` |
| Exact (`/root/review_exact_a`) | `Occil.Constants.inverseEPlus` | `SampLib.InverseEPlus.inverseEPlus_distSpec` | `2af09d4f6a033863658c1731936e3cb871c750f7d9441cfcd1edf03339351f25` |
| Exact (`/root/review_exact_a`) | `Occil.Constants.inverseEPlusContinuedFraction` | `SampLib.EContinuedFractionConstants.inverseEPlusContinuedFraction_distSpec` | `5b6e6fe63fd69f45efa96120b9245e4ed26c0d79d59541786c56d2ff9c1c2377` |
| Exact (`/root/review_exact_a`) | `Occil.Constants.tanhHalf` | `SampLib.TanhHalf.tanhHalf_distSpec` | `e80d5774e1948899a131edbe786a2f5b33e75010a187280d1c13a66e1a40f688` |
| Exact (`/root/review_exact_a`) | `Occil.Constants.threeMinusE` | `SampLib.EulerAffineConstants.threeMinusE_distSpec` | `10962fe5f5f2ea9d2295daff68728e3448e01127b14c2e7a3c17f264af197ea9` |
| Exact (`/root/review_exact_a`) | `Occil.Constants.arctanRationalOverRatio` | `SampLib.ArctanRationalOverRatio.arctanRationalOverRatio_distSpec` | `2e0b507798e0e027a239fd2663b1340217143e31e194bd659b3af3eca8625266` |
| Exact (`/root/review_exact_a`) | `Occil.Constants.fourOverThreePi` | `SampLib.PiConstants.fourOverThreePi_distSpec` | `ad901ceedd0666de40ed27b61111a5690693f234f56c9e2d89c887dc94496666` |
| Exact (`/root/review_exact_a`) | `Occil.Constants.inversePi` | `SampLib.PiConstants.inversePi_distSpec` | `ad901ceedd0666de40ed27b61111a5690693f234f56c9e2d89c887dc94496666` |
| Exact (`/root/review_exact_a`) | `Occil.Constants.inverseSqrtPi` | `SampLib.InverseSqrtPi.inverseSqrtPi_distSpec` | `ac1ab85c5a9eddfef534ac17b2fbb020a1087ed790bd91b21277861c2f701e4e` |
| Exact (`/root/review_exact_a`) | `Occil.Constants.logPiOverPi` | `SampLib.LogPiOverPi.logPiOverPi_distSpec` | `d303b057378b59de724c95c3df4c93b4251c3cb2564e3c9f8db987deb7631330` |
| Exact (`/root/review_exact_a`) | `Occil.Constants.piMinusThree` | `SampLib.PiConstants.piMinusThree_distSpec` | `ad901ceedd0666de40ed27b61111a5690693f234f56c9e2d89c887dc94496666` |
| Exact (`/root/review_exact_a`) | `Occil.Constants.piMinusThreeOverFour` | `SampLib.PiConstants.piMinusThreeOverFour_distSpec` | `ad901ceedd0666de40ed27b61111a5690693f234f56c9e2d89c887dc94496666` |
| Exact (`/root/review_exact_a`) | `Occil.Constants.piQuarter` | `SampLib.PiConstants.piQuarter_distSpec` | `ad901ceedd0666de40ed27b61111a5690693f234f56c9e2d89c887dc94496666` |
| Exact (`/root/review_exact_a`) | `Occil.Constants.piQuarterMinusHalf` | `SampLib.PiConstants.piQuarterMinusHalf_distSpec` | `ad901ceedd0666de40ed27b61111a5690693f234f56c9e2d89c887dc94496666` |
| Exact (`/root/review_exact_a`) | `Occil.Constants.piTwelfth` | `SampLib.PiConstants.piTwelfth_distSpec` | `ad901ceedd0666de40ed27b61111a5690693f234f56c9e2d89c887dc94496666` |
| Exact (`/root/review_exact_a`) | `Occil.Constants.erfRatio` | `SampLib.ErfRatio.erfRatio_distSpec` | `5a6bc8fe797c5b373c76ec089ad633afae29bbda90e9c620ef7769722d65f045` |
| Exact (`/root/review_exact_a`) | `Occil.Constants.eulerMascheroni` | `SampLib.EulerMascheroni.eulerMascheroni_distSpec` | `8bdd97b4beb07e2279a9024fcca93785a3a03720baf9c1e91c0ac7e4fa08e523` |
| Exact (`/root/review_exact_a`) | `Occil.Constants.logOnePlusRational` | `SampLib.LogOnePlusRational.logOnePlusRational_distSpec` | `f3730cd368cd06c00f7458455357e0eb7c653c112692c111a5f144babfad8b2a` |
| Exact (`/root/review_exact_a`) | `Occil.Constants.lowerGammaIntegerRatio` | `SampLib.LowerGammaIntegerRatio.lowerGammaIntegerRatio_distSpec` | `b4665d6d021cb6a744b478ec99a59127b551422344702204d2038c9adc7f3d03` |
| Exact (`/root/review_exact_a`) | `Occil.Constants.rationalIntegerPower` | `SampLib.RationalIntegerPower.rationalIntegerPower_distSpec` | `0b006eb4b0d045ab6f5cdf989fd28d31b8b0f7e057f188d2e0055a492ed24dd7` |
| Exact (`/root/review_exact_a`) | `Occil.Constants.zetaRelated` | `SampLib.ZetaRelated.zetaRelated_distSpec` | `8f30cc33ca2f4e3c0f2bf7d2fe83b9dce626b496e2777662d52421042a0999c5` |
| Historical | `Occil.Constants.fromDigits` | `SampLib.FromDigits.fromDigits_distSpec` | `dec88e22a89e2fae64e846aac508d70998a652b810eba4cc20b25377bf270702` |
| Historical | `Occil.Constants.algebraicRoot` | `SampLib.AlgebraicRoot.algebraicRoot_distSpec` | `99e52df60ce3dc70e194e4087e0ee4a6f7413c7019748800a30258e44970f081` |
| Historical | `Occil.Constants.inverseGoldenRatio` | `SampLib.InverseGoldenRatio.inverseGoldenRatio_distSpec` | `207eccfef820530db20ac12841cee4c66b1094d51a6563702c7543c764cda841` |
| Historical | `Occil.Constants.sqrtTwoMinusOne` | `SampLib.SqrtTwoMinusOne.sqrtTwoMinusOne_distSpec` | `fd3e7a3ef27cbfb6e59916c0ab9e06df452551b048429e7ae038ddf32e219b50` |
| Historical | `Occil.Constants.inverseSqrtTwo` | `SampLib.InverseSqrtTwo.inverseSqrtTwo_distSpec` | `39cc57f1c1247b1224bc6fcdff394362ed6d0798247cd92b4ac8151cae5be03d` |
| Historical | `Occil.Constants.goldenFamily` | `SampLib.GoldenFamily.goldenFamily_distSpec` | `6eb40c9ee271b2342c03eb35b3bff22631cbcce6f72c32df08d3e3e5358370ab` |
| Historical | `Occil.Constants.generalizedContinuedFraction` | `SampLib.ContinuedFraction.generalizedContinuedFraction_distSpec` | `0ab825c80b84a471e0ac35ab4778e25589490f3c457b0e9131cb68a45a33e659` |
| Historical | `Occil.Constants.continuedFraction` | `SampLib.SimpleContinuedFraction.continuedFraction_distSpec` | `49586ed1d394208e1dded96e23f992cd94c88940ae631bcb89f9f44b7832a458` |
| Historical | `Occil.Constants.fromBounds` | `SampLib.FromBounds.fromBounds_distSpec` | `36e125d6841c3dfb76609374fae9dde4e1aaf9eccc70831cac6ceac1e61ab379` |
| Historical | `Occil.Constants.fromApproximateDigits` | `SampLib.FromApproximateDigits.fromApproximateDigits_distSpec` | `5bd1fb8e82c07aadc173475aee04c70702ce6a6da9f38136511bd82cfb90f4a1` |
| Historical | `Occil.Constants.eScaled` | `SampLib.EScaled.eScaled_distSpec` | `53cea91edf943d859ec5a5a8a790fed27e0966f77d7ac651475a455b1e694768` |
| Historical | `Occil.Constants.eOverPi` | `SampLib.EulerPi.eOverPi_distSpec` | `b9ef39d0d05df49f068533c71e63f122adbdc46a8b61ea584e7769c6c4c118cb` |
| Historical | `Occil.Constants.piAffine` | `SampLib.PiAffine.piAffine_distSpec` | `38b6e5006861519912e6fe51393e2180b2366870d35c04cb225e151f5cb1fe28` |
| Historical | `Occil.Constants.reciprocalPiScaled` | `SampLib.ReciprocalPiScaled.reciprocalPiScaled_distSpec` | `afa6d842813a9c6a3ea65fc403f31a98fd7c932841d06ba7b6ebe9280fe3e64e` |
| Historical | `Occil.Constants.inverseEPlusRational` | `SampLib.InverseEPlusRational.inverseEPlusRational_distSpec` | `3dcda790dafed59c7b0224fe043366fab86d4e1949631cada5a1d019bf903964` |
| Historical | `Occil.Constants.exponentialRationalProduct` | `SampLib.ExponentialRationalProduct.exponentialRationalProduct_distSpec` | `4d88df42de674c777d23fb9cc19c55cb9239fb617ebaa6e38529552944a86cfe` |
| Historical | `Occil.Constants.fromPositiveSeries` | `SampLib.FromPositiveSeries.fromPositiveSeries_distSpec` | `203ec2c0c0829a22cb45282ede360fb61c9164306ed52dc089b2c15100aa35f6` |
| Historical | `Occil.Constants.threeZetaThreeOverFour` | `SampLib.ZetaThree.threeZetaThreeOverFour_distSpec` | `5e9b3f737c1392d4fe75846b765656d6349908c6cdeea5f0b599ea519018d1fc` |

## What I checked

- **Statements.** No public statement changes in the diff. Every moved definition, such as
  `RationalContinuedFraction.Coefficient`, `value`, `potential`, and `Reachable`,
  `FiniteRationalContinuedFraction.Coefficient`, `AlgebraicRoot.Cell`, and
  `FromBounds.encodeInterval`, keeps its fully qualified name and body. A
  declaration-matching pass over the whole diff finds no changed body among the moved
  declarations. `ContinuedFraction.value` keeps its body; only the proof of
  `exists_value`, which it names, changes. Statement equality rests on the lead's
  mechanical pin check with `statement_pins.py`, which was still in progress when I wrote
  this report.
- **Moves.** The mathematics of `AlgebraicRoot`, `FiniteRationalContinuedFraction`,
  `GeneralizedContinuedFraction`, `RationalContinuedFraction`, and `LatentCoinReciprocal`
  moves to new `Laws/` modules under the same namespaces. `Laws/EulerSondow.lean` splits
  off `Laws/EulerSondowTail.lean`. The potential bounds move to
  `Laws/RealContinuedFractionBudget.lean`. Program encodings move from `Laws/` to
  `Support/EulerEncodings.lean` and `Support/FromBoundsEncoding.lean`. The four
  `EulerHyperbolic` endpoint lemmas become public only because the moved `encode` lemma
  uses them.
- **Deduplication.** `Laws/ContinuedFraction.lean` drops its private copy of the
  convergence argument (Lipschitz pairs, nested prefixes, unique value) and the budget
  bounds. It now proves `value_eq` and derives each bound from `RealContinuedFraction`.
  The three copies of `initial_budget` collapse into the `Laws/` modules.
- **Heartbeat overrides.** The refactor removes three of six overrides (`EContinuedFraction`
  and both in `FiniteRationalContinuedFraction`). In `RationalContinuedFraction`,
  `GeneralizedContinuedFraction`, and `ContinuedLogarithm`, the remaining override moves
  from the whole recursive proof onto a short `twp_entry` lemma. That lemma runs only the
  straight-line coefficient read and guard, and ends in a `round` term that names the rest
  of the source. Lean checks `round` against the program by `change`, so it cannot drift.
  I judge this an improvement: the costly step now has a name and a small scope, the
  credit proofs read as one round, and `RationalContinuedFraction.twp_entry` serves
  `FiniteRationalContinuedFraction` too, which removes its two overrides (one at
  1,600,000). No new `set_option` appears.
- **Retry lemma.** `AlgebraicRoot`, `ErfRatio`, `FiniteRationalContinuedFraction`,
  `FromDigits`, and `LowerGammaIntegerRatio` use `Retry.twp_loop` or
  `Retry.twp_loop_forall`. Each round body is unchanged, and each retry branch passes its
  credit straight to the induction hypothesis. The remaining users of the old idiom
  (`LogPiOverPi`, `Support/LatentCoinReciprocal.lean`, and
  `Support/SquaredDecreasingChain.lean`) are on the brief's list of proofs to leave.
- **Math and program split.** Every `Laws/` module imports only mathlib, other `Laws/`
  modules, and `SampLib.Core.Laws.*`. No `Laws/` module states a `tglWp`, `pl%`, or
  `Val` lemma.
- **Hygiene.** No file in scope contains `sorry`, `admit`, `axiom`, or `native_decide`.
  No line exceeds 100 columns, and `git diff --check` is clean.
- **Build.** `lake build` of all 39 top-level `SampLib.Constants` modules succeeds with no
  errors or warnings.
- **Callers and axioms.** The reviewer caller files `ExactFactoriesBatch001Callers.lean`,
  `002`, `003`, `007`, `008`, `014`, `015`, `016`, `018`, `025`, and `026` compile with no
  errors and no warnings. Their `#print axioms` output lists only `propext`,
  `Classical.choice`, and `Quot.sound`.

## Nits

These nits do not block acceptance.

- `GeneralizedContinuedFraction.lean` makes `round` and `twp_entry` public, but only that
  file uses them. `ContinuedLogarithm.lean` keeps its pair private.
- `Laws/RealContinuedFractionBudget.lean` is untracked in git. Add it before you commit.
- `Laws/ZetaProductIntegral.lean` has no `/-! # Title` docstring. This predates the round.
- `Laws/EulerContinuedFraction.lean` has 255 lines. This predates the round.
- The `ContinuedLogarithm` entry lemma adds about 40 lines for no net override removal.
  It still reads better, since the credit proof no longer interleaves the opening steps.
