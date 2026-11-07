# Round 3 review: Bernoulli files M to Z

This review covers the round-3 refactor of the files under `SampLib/Bernoulli/` (any
subdirectory) whose names start with M through Z. The base commit is `8f819b7`. The reviewer
did not write the refactor.

## Verdict

The reviewer accepts the refactor. Every change is correct and at least as clear as before.
The nits below do not block acceptance.

## Accepted public specs

The reviewer re-binds these public specs at the proof hashes that
`refactor_receipts.py --list` prints. Each hash is the full SHA-256 hash of the proof file.

### Exact-campaign rows (`/root/review_exact_a`)

| Sampler | Public spec | Proof hash |
| --- | --- | --- |
| `Occil.FactoryExtra.polynomial` | `SampLib.PolynomialFactory.polynomial_distSpec` | `842e1e54790f4f1d192d10a3ba6fa2e8cb3804dc8fa7532883c55722baa4da2a` |
| `Occil.FactoryExtra.rationalFunction` | `SampLib.PolynomialFactory.rationalFunction_distSpec` | `7ce5f1628d82ee609144b946145cac7e3ae2b5ad4780209f6dbf3bef40c0fd13` |
| `Occil.FactoryExtra.threePointPiecewise` | `SampLib.MinimumComplement.threePointPiecewise_distSpec` | `654ba7594aa381e815cb744d79487d2fd698bf264f4dbf6185446272153aad1a` |
| `Occil.FactoryExtra.twoCoinPower` | `SampLib.TwoCoinPower.twoCoinPower_distSpec` | `e2388f150b12768e3c38312e50966a8cf857dfaf6171872ae8a585c13ae43e52` |
| `Occil.FactoryExtra.minimumComplement` | `SampLib.MinimumComplement.minimumComplement_distSpec` | `7d5185fb008ce8a413a0422bada8eeed256bb15b3511d99814fb452e642381b5` |
| `Occil.FactoryExtra.minimumHalf` | `SampLib.MinimumComplement.minimumHalf_distSpec` | `6e5ff69f90fa27e7dee830c85dd3c69380c5ea4a3d2d4816003f318d56f38efc` |
| `Occil.FactoryExtra.powerSeriesHazards` | `SampLib.PowerSeriesHazards.powerSeriesHazards_distSpec` | `631202783470aed16695006436b0b5ba07b45c77e6cb563859ccd275b70c85e1` |
| `Occil.FactoryExtra.cosineSqrt` | `SampLib.TrigonometricSeriesFactories.cosineSqrt_distSpec` | `04ef229b3b1548ea46fda1539a4385533008800c32330523ab5b0328b1318c23` |
| `Occil.FactoryExtra.pOverTangent` | `SampLib.POverTangent.pOverTangent_distSpec` | `e5c4a891f87c29a9affea3279fad8f48e8cb63352b69c58569d8f028f9b5fa51` |
| `Occil.FactoryExtra.sincScaled` | `SampLib.TrigonometricSeriesFactories.sincScaled_distSpec` | `04ef229b3b1548ea46fda1539a4385533008800c32330523ab5b0328b1318c23` |
| `Occil.FactoryExtra.sincSqrtScaled` | `SampLib.TrigonometricSeriesFactories.sincSqrtScaled_distSpec` | `04ef229b3b1548ea46fda1539a4385533008800c32330523ab5b0328b1318c23` |
| `Occil.sampleGeometricBag` | `SampLib.SampleGeometricBag.sampleGeometricBag_coinSpec` | `f0f6e252438c62483d0127a2279a2982b8b2abb79d335283b69d6053ac619179` |

### Historical rows

| Sampler | Public spec | Proof hash |
| --- | --- | --- |
| `Occil.oneDivOnePlus` | `SampLib.OneDivOnePlus.oneDivOnePlus_distSpec` | `9440758e458d81818d2f613250706e18b8e0323e10304ef6183ed3b1b4e16dcb` |
| `Occil.probabilityGeneratingFactory` | `SampLib.ProbabilityGeneratingFactory.probabilityGeneratingFactory_distSpec` | `bc947c46ba35e5e22051cc732cfa717a4ed608cbb8137f101a49fb21ba08927a` |
| `Occil.FactoryExtra.oneMinusOverOnePlus` | `SampLib.OneMinusOverOnePlus.oneMinusOverOnePlus_distSpec` | `7eab942062aaedfb2c0fb6a1149df23f8d1b5ce349c1c84e08455c4c2a3fa71d` |
| `Occil.FactoryExtra.onePlusHalf` | `SampLib.OnePlusHalf.onePlusHalf_distSpec` | `e95adadf1efd5ed03f32055afe866cf707fd3d488bc67d2413e49fe9c9d9cd1c` |
| `Occil.FactoryExtra.pLogInverse` | `SampLib.PLogInverse.pLogInverse_distSpec` | `0a3e65e889d47786a0092925c3db4f417668293fbf5190bceec85956e2ac0243` |
| `Occil.FactoryExtra.oneDivTwoMinus` | `SampLib.OneDivTwoMinus.oneDivTwoMinus_distSpec` | `e5ac38c72dcc1046a36e6ab45a68fc351045c8957520713dcb22cda208f51b12` |
| `Occil.FactoryExtra.reciprocalLogistic` | `SampLib.ReciprocalLogistic.reciprocalLogistic_distSpec` | `25e9614577e0419771978321c16d32275a5ec92eaf939840050a22f04dc91f82` |
| `Occil.FactoryExtra.positivePowerSeries` | `SampLib.PositivePowerSeries.positivePowerSeries_distSpec` | `2a5e2e0fd1ae7a9fbf57b67d782128fcd289f4d139f87e66255d64dc57008c1e` |
| `Occil.FactoryExtra.oddsProduct` | `SampLib.OddsProduct.oddsProduct_distSpec` | `996be8c7f055b7f367a4902f272b6a0ca123860cda07ed934657b3134d2a10e1` |
| `Occil.FactoryExtra.polylogarithm` | `SampLib.Polylogarithm.polylogarithm_distSpec` | `94091cf11ba9615dfd6144ae0a8265dab0a04bf335e8ff6581fec264d2ca639d` |
| `Occil.FactoryExtra.sigmoidDerivative` | `SampLib.SigmoidDerivative.sigmoidDerivative_distSpec` | `10271736856cd562e1d2d0e51206ca7fed0547c8b870880cc83962e177b5f31c` |
| `Occil.FactoryExtra.sigmoidRational` | `SampLib.SigmoidRational.sigmoidRational_distSpec` | `d72759957f28954fe0eec8dcd5ed9f3e87dd8a2dffaf5e99687dc14eccb1d1c9` |
| `Occil.FactoryExtra.tanhRational` | `SampLib.TanhRational.tanhRational_distSpec` | `f2af7eaf4f77cbd181fd51d0ef39dd1be212e35370c5ee13c710bf9052a05704` |
| `Occil.FactoryExtra.reciprocalAffine` | `SampLib.ReciprocalAffine.reciprocalAffine_distSpec` | `b42e3fcfe94cbf278b431d53e70d184e617461ef6034f3d8cc4967ad85033799` |
| `Occil.FactoryExtra.reciprocalAffinePower` | `SampLib.ReciprocalAffinePower.reciprocalAffinePower_distSpec` | `6b9cf732e9695db078f95103ebe2ed2e9ec678c93b9196c772c153e3f5eb1565` |
| `Occil.FactoryExtra.offsetRace` | `SampLib.OffsetRace.offsetRace_distSpec` | `b5a46bf3bf53a9c748f0a4e248e7227a6299133fb9e56302a490c1597c6a3237` |
| `Occil.FactoryExtra.reciprocalExpAffine` | `SampLib.ReciprocalExpAffine.reciprocalExpAffine_distSpec` | `b01ae2e89990cc1cbc2f13aaac0e7d7a03ec7f000685981330f74607858cef07` |
| `Occil.FactoryExtra.tanhScaled` | `SampLib.TanhScaled.tanhScaled_distSpec` | `2e8dfb4a3fe936975c1310125c0d2c73bd497f4e2efa9177b61a3fd204f4b9c5` |
| `Occil.FactoryExtra.sigmoidScaled` | `SampLib.SigmoidScaled.sigmoidScaled_distSpec` | `59732fff134fa3140a1ee2d80784caa90a023630903260d0bf783fdac386f644` |
| `Occil.FactoryExtra.twoCoin` | `SampLib.TwoCoin.twoCoin_distSpec` | `3e0b92ac31e50e3aeba39dec6cf39e895f4e203f3b730a46bf9a6ac4cff370ff` |
| `Occil.FactoryExtra.subtraction` | `SampLib.Subtraction.subtraction_distSpec` | `e6c17a48b89b751411028103f2076e23aa969045fbf3c5e725932d860ecb15d2` |
| `Occil.sineFactory` | `SampLib.SineFactory.sineFactory_distSpec` | `94cb79cf2ce87c265a48f10da6454d6d81cdf7260510b2c9f61620180db2ad79` |
| `Occil.FactoryExtra.tanhHalfShifted` | `SampLib.TanhHalfShifted.tanhHalfShifted_distSpec` | `51d776a1aaed9cc2a3db748c892bf236dfdc18f02ef86d9c8bcd06158e1fe522` |
| `Occil.vonNeumann` | `SampLib.VonNeumann.vonNeumann_distSpec` | `20c5d951426b2c5a01de19eefba7d1e8a9010484c0ea80ceb11adf47ad765aab` |

## What the reviewer checked

- **Statements.** The diff changes no public spec and no definition in a spec type. Moved
  definitions keep their fully qualified names, namespaces, and bodies. Statement equality
  rests on the lead's mechanical pin check with `agent-scripts/statement_pins.py`; this
  review found nothing suspicious.
- **Moved mathematics.** The reviewer compared each new `Laws/` module with the text that it
  replaces: `OffsetRace`, `OneDivOnePlus`, `PLogInverse`, `ReciprocalAffine`, `Subtraction`,
  `TwoCoin`, `TwoCoinPower`, and `VonNeumann`. The bodies are verbatim. Some helpers lose
  `private` because the spec file now uses them from another module.
- **Program-side encodings.** `encodeTriple`, `encodeInterval`, and their lemmas move from
  `Laws/RealEnclosure`, `Laws/PiBoundsState`, `Laws/PiProbability`, and
  `Laws/ReciprocalPiProbability` to the new `Support/RealEnclosureEncoding` and
  `Support/PiEncodings`, with unchanged names and bodies.
- **Retry migrations.** `OddsProduct`, `OneDivOnePlus`, `OneMinusOverOnePlus`,
  `ReciprocalAffine`, `TwoCoin`, and `VonNeumann` now use `Retry.twp_loop`, following the
  plain recipe. The round bodies stay the same, and the retry branch applies `IH` directly.
- **Duplicate removed.** `OffsetRace` drops its private copy of the affine rank callback
  and uses `Support/AffineRankCoin`, whose `body` and `callback` match the deleted copy.
- **Heartbeat overrides.** `ReciprocalAffine`, `ReciprocalAffinePower`, and `TwoCoin` drop
  `set_option maxHeartbeats`. No file in scope adds a `set_option`, `sorry`, `axiom`,
  `admit`, or `native_decide`.
- **The bar.** No `Laws/` module in scope imports a spec, `Support/`, `Syntax/`, Iris, or
  program-logic module. Every changed file has a `/-! # Title` docstring, and no line exceeds
  100 columns. `git diff --check` reports no whitespace errors.
- **Build.** `lake build --no-build SampLib` reports every target up to date, so the whole
  library builds from the current sources.
- **Callers and axioms.** Every caller artifact for these samplers compiles with
  `lake env lean` through the memory gate, with no errors and no warnings. Every printed
  axiom set is `[propext, Classical.choice, Quot.sound]`. The callers are `CoinCallers.lean`, `StructuredCallers.lean`, `NextBatchWeightedFactoriesCallers.lean`, `ExpansionFactoriesBatch001Callers.lean`, `ExpansionFactoriesBatch002Callers.lean`, `ExpansionFactoriesBatch003Callers.lean`, `ExpansionFactoriesBatch004Callers.lean`, `ExpansionFactoriesBatch005Callers.lean`, `ExpansionFactoriesBatch006Callers.lean`, `ExpansionFactoriesBatch010Callers.lean`, `ExpansionFactoriesBatch011Callers.lean`, `ExpansionFactoriesBatch012Callers.lean`, `ExactFactoriesBatch005Callers.lean`, `ExactFactoriesBatch010Callers.lean`, `ExactFactoriesBatch012Callers.lean`, `ExactFactoriesBatch017Callers.lean`, `ExactFactoriesBatch023Callers.lean`, `ExactFactoriesBatch027Callers.lean`, `ExactFactoriesBatch030Callers.lean`, and `DiscreteCallers.lean`.

## Scope note

Several listed samplers are stale only through transitive dependencies outside this scope,
for example `Common/` and Bernoulli files A to L. Other reviewers cover those changes. This
review attests to the changes in its own scope and to the caller and axiom checks above.

## Nits

- `Laws/OffsetRace.lean` makes `normalizer`, `normalizer_pos`, `left_coe`, `right_coe`, and
  `sum_coe` public, but only that module uses them. They can stay `private`.
- `Laws/OffsetRace.lean` gives `total_pos`, `left_bound`, and `right_bound` no docstrings.
- `ReciprocalAffinePower.lean:11-12` keeps two blank lines where the heartbeat override was.
- `Laws/TwoCoin.lean` writes both "portkey" and "Portkey"; one spelling reads better.
- `OddsProduct.lean` and `OneMinusOverOnePlus.lean` still hold their expectation lemmas in
  the spec file. The refactor did not move them; this is a candidate for a later pass.
