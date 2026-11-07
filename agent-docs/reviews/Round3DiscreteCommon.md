# Round 3 review: Discrete and Common

Reviewer `round3_review_discrete` re-reviews the round-3 refactor of `SampLib/Discrete/` and
`SampLib/Common/` against base commit `8f819b7`.

## Verdict

Accepted. Every change moves code into a `Laws/` module, splits a file by topic, removes a
heartbeat override or a dead lemma, or migrates a retry proof to the shared lemma. Each
proof is still a clear proof of the same theorem.

## Proofs and new hashes

The following table lists every stale public spec and its new proof hash, exactly as
`refactor_receipts.py --list` prints them.

| Sampler | Public spec | Record | Proof hash |
| --- | --- | --- | --- |
| `Occil.FactoryExtra.rationalPower` | `SampLib.RationalPower.rationalPower_distSpec` | Exact (A) | `686c19d494d5886d7c943f3ba51eed0f76f40e5f3eb08860a754b9dbed7d997a` |
| `Occil.DiscreteExtra.binomialHalfRejection` | `SampLib.BinomialHalfRejection.binomialHalfRejection_distSpec` | Exact (B) | `2aedd9b256644e23905fdfc6e82738802a5cdfc882f00afc68e41d591c14f87e` |
| `Occil.DiscreteExtra.betaNegativeBinomial` | `SampLib.BetaNegativeBinomial.betaNegativeBinomial_distSpec` | Exact (B) | `3967a7f9fdf5ea7a72a52b78315a329014b73a0ae43aeace67514d6f7ea19992` |
| `Occil.DiscreteExtra.inversePolya` | `SampLib.InversePolya.inversePolya_distSpec` | Exact (B) | `e23402a263f076eb50263c43de5d5d9e09269fa7f80e68a596ea28189162d753` |
| `Occil.DiscreteExtra.polyaRational` | `SampLib.PolyaRational.polyaRational_distSpec` | Exact (B) | `25fd93d60a5450a125ecd636b8b080f94059c6a2d6159317a10f312e0836f406` |
| `Occil.DiscreteExtra.waringYule` | `SampLib.WaringYule.waringYule_distSpec` | Exact (B) | `eb27d1b7c15cdd70612b865b33e70f58d5ccc0ab98d7ad662e796d7662c4b03a` |
| `Occil.DiscreteExtra.yuleSimon` | `SampLib.YuleSimon.yuleSimon_distSpec` | Exact (B) | `7055f240d5df2ca30562fb4917a1c4226ffd97eb17e6d7b11e3f4a3b7d625636` |
| `Occil.DiscreteExtra.generalizedGeometric` | `SampLib.GeneralizedGeometric.generalizedGeometric_distSpec` | Exact (B) | `3bca73aa077fb01e4f45f29d1347d376d15c0b2f68c46739476922516659af96` |
| `Occil.DiscreteExtra.generalizedSibuya` | `SampLib.GeneralizedSibuya.generalizedSibuya_distSpec` | Exact (B) | `b42f3221cef3f1d6273c1e791ff43cd2c560adcc4da8d8ffb108290a6afa92b3` |
| `Occil.DiscreteExtra.rationalPowerCoin` | `SampLib.RationalPower.rationalPowerCoin_distSpec` | Exact (A) | `686c19d494d5886d7c943f3ba51eed0f76f40e5f3eb08860a754b9dbed7d997a` |
| `Occil.DiscreteExtra.zeta` | `SampLib.Zeta.zeta_distSpec` | Exact (B) | `8b07c344a171ba5554af27b0ff85c9d8c885a14e0e5dc79ba321e83a0e1790c3` |
| `Occil.DiscreteExtra.zipf` | `SampLib.Zipf.zipf_distSpec` | Exact (B) | `8aff3252095ddd4cd8c23d5ac408dbd90db28f8f67ee82bf62d429c0ff00ace2` |
| `Occil.binomial` | `SampLib.Binomial.binomial_distSpec` | Historical | `f9851a195b1ebfa79f2f387d91b1cf07885209b76e94f9232c220118bbc37f90` |
| `Occil.boundedGeometric` | `SampLib.BoundedGeometric.boundedGeometric_distSpec` | Historical | `7dcc647501fcfdc94cf881d6dc78385814dd0f553eb2c55474499aadd400f6d1` |
| `Occil.randomWalk` | `SampLib.RandomWalk.randomWalk_distSpec` | Historical | `e8e7c02ecc1384896ffa0c5c2df46d73444bc4040375eb16fba5ad53cfe2e3a3` |
| `Occil.geometric` | `SampLib.Geometric.geometric_distSpec` | Historical | `b48ce7fe63b918b46fd807543e32fa90d253621c086d1a3b10434a2f4c22c680` |
| `Occil.negativeBinomial` | `SampLib.NegativeBinomial.negativeBinomial_distSpec` | Historical | `b8f7dec04ac9f1a791197a69d01fa8fd43d2f3bb8f686bbaadcd6269615d85e3` |
| `Occil.weightedChoice` | `SampLib.WeightedChoice.weightedChoice_distSpec` | Historical | `8fab5daabcabb73557dcbcdf53bb9c855993bd11732b3ca202967725e525fcd4` |
| `Occil.dice` | `SampLib.Dice.dice_distSpec` | Historical | `32e0e35014ede0c321bc5da9c99623f6215b52581e2b15a2dccde2b5470152c8` |
| `Occil.hypergeometric` | `SampLib.Hypergeometric.hypergeometric_distSpec` | Historical | `6ffc1810da2517c1ef5d191af81a2e4ec8a957b4c932740e10f9ba8c16073bed` |
| `Occil.polyaEggenberger` | `SampLib.PolyaEggenberger.polyaEggenberger_distSpec` | Historical | `f456f6c9369ceecc85a28a388f5d4cba201b92d3b6f4751bd71d1521ca1a21ad` |
| `Occil.DiscreteExtra.betaBinomial` | `SampLib.BetaBinomial.betaBinomial_distSpec` | Historical | `3024ee20a932c066a6c7129262681ef8e503b5ab7cdc6f22cdbb75831aca62bd` |
| `Occil.DiscreteExtra.symmetricGeometric` | `SampLib.SymmetricGeometric.symmetricGeometric_distSpec` | Historical | `2dcd96f92d06bf0b41c45fd08857691a42cb3557a981eb1747945d90d47e3189` |
| `Occil.DiscreteExtra.negativeHypergeometric` | `SampLib.NegativeHypergeometric.negativeHypergeometric_distSpec` | Historical | `f14c31b1c342ef35b455f978a1469703cb39a7b49428ef1f6b5b18aa06c217ca` |
| `Occil.DiscreteExtra.himanshu` | `SampLib.Himanshu.himanshu_distSpec` | Historical | `d29e0d3bb01aff500f7e21df5c87181492d02810d1e99666376212c7c7e9baae` |
| `Occil.DiscreteExtra.binomialHalfBits` | `SampLib.BinomialHalfBits.binomialHalfBits_distSpec` | Historical | `9f453a18ef71819d3dad361d9ba89e6f745d3018b7308282527469a2d5c1bbcd` |
| `Occil.poissonOne` | `SampLib.PoissonOne.poissonOne_distSpec` | Historical | `a38a9799d8e2f218697c5cf4bb86fd0d73563498ca0663ead25ca46ff36fc25d` |
| `Occil.poissonRational` | `SampLib.PoissonRational.poissonRational_distSpec` | Historical | `90375dee6329b33bc75ef99a4b858b77d9580a0d53caa2dc5b1994cf3b644664` |
| `Occil.DiscreteExtra.compoundPoisson` | `SampLib.CompoundPoisson.compoundPoisson_distSpec` | Historical | `eb443dbc613fd377d29c93a28c1041cb271f1137000026a9e32bd70df526a2d4` |
| `Occil.DiscreteExtra.skellam` | `SampLib.Skellam.skellam_distSpec` | Historical | `3bc99d5a9988a58ddef43cf386f26cb1c0e1c3afa5c5a8756c998ae1ecbf7c6b` |
| `Occil.DiscreteExtra.neymanTypeA` | `SampLib.NeymanTypeA.neymanTypeA_distSpec` | Historical | `a5db7ed644e26061b84bed6f0d819f006651c5d7d3b8b40d3281a7c365a75084` |
| `Occil.DiscreteExtra.polyaAeppli` | `SampLib.PolyaAeppli.polyaAeppli_distSpec` | Historical | `09079be726e97c8a81e7243227ceb248822a34cdf737371cabaec6fcc994de21` |
| `Occil.DiscreteExtra.zeroTruncatedPoisson` | `SampLib.ZeroTruncatedPoisson.zeroTruncatedPoisson_distSpec` | Historical | `17c048dc124eebaf9e604db5f0923a4e5c604951a73c5dcca812568d2fe62b3b` |
| `Occil.DiscreteExtra.multivariatePoisson` | `SampLib.MultivariatePoisson.multivariatePoisson_distSpec` | Historical | `580d576d26b8e6fcc57786d1bf1f03ac4117415797295c0322b610e3c70a05c4` |
| `Occil.DiscreteExtra.logUniform` | `SampLib.LogUniform.logUniform_distSpec` | Historical | `420d6b05cdee93f96284662edebaf4c5ff421090181f192b5ebb7f244db960aa` |
| `Occil.DiscreteExtra.binomialBinary` | `SampLib.BinomialBinary.binomialBinary_distSpec` | Historical | `2f6759a06ec64a3b616edba2edfb0ad60ac46996fee370daaf0b19718e1a422b` |
| `Occil.DiscreteExtra.cub` | `SampLib.Cub.cub_distSpec` | Historical | `9922e3999c0eb22995e735e408d6fbfccd75b167c421e399becb426bca435579` |
| `Occil.DiscreteExtra.borel` | `SampLib.Borel.borel_distSpec` | Historical | `ff0b12e6292607bf36ad1d6bb7a71547db3608cfee2d501ba738ea58076a00c2` |
| `Occil.DiscreteExtra.fisherHypergeometric` | `SampLib.FisherHypergeometric.fisherHypergeometric_distSpec` | Historical | `e1c5bebe64c2f45f1d59cdaf956c7d0e54e9f04f90a219c4f9917264cf198da4` |
| `Occil.DiscreteExtra.logarithmicSeries` | `SampLib.LogarithmicSeries.logarithmicSeries_distSpec` | Historical | `adccc8c8d5720c2fc7cdd3aa5085e03f559e580fe8a3c3f1a180f67411a811fa` |
| `Occil.multinomial` | `SampLib.Multinomial.multinomial_distSpec` | Historical | `a8075d4845d710b09da4cae22c55122b85a71b61d07870e4b45f54eec63508cf` |
| `Occil.DiscreteExtra.negativeMultinomial` | `SampLib.NegativeMultinomial.negativeMultinomial_distSpec` | Historical | `1475a0d5af79d953712e01116ce579db764b7b1f50ab9bdc04101f64e7b129fe` |
| `Occil.DiscreteExtra.walleniusHypergeometric` | `SampLib.WalleniusHypergeometric.walleniusHypergeometric_distSpec` | Historical | `58fa4a37281a4e8372068c9d71dbd3948a7004503e4a569705ecc27556511c2a` |
| `Occil.DiscreteExtra.walleniusMultivariate` | `SampLib.WalleniusMultivariate.walleniusMultivariate_distSpec` | Historical | `29cc7488cf38e19ec539118bc57db02e79360455bb52e37abca3ed9de651c54f` |
| `Occil.DiscreteExtra.multivariateHypergeometric` | `SampLib.MultivariateHypergeometric.multivariateHypergeometric_distSpec` | Historical | `39e66a4acb0752f7568f9d6e25f770c3c3fd23e6ea190311e1be90f67dde8055` |
| `Occil.DiscreteExtra.fisherMultivariate` | `SampLib.FisherMultivariate.fisherMultivariate_distSpec` | Historical | `e9e92a997b762fa7a8769ed9e6747c2248e09cc7efe026a1587d7484c63908a5` |
| `Occil.DiscreteExtra.discreteLaplace` | `SampLib.DiscreteLaplace.discreteLaplace_distSpec` | Historical | `611c1af72a22fb5d492d9b3bb69929fdf3934e233a35474539dd7d2e3b3038dd` |

## What the reviewer checked

- **Statements.** The statement check rests on the lead's mechanical pin check with
  `agent-scripts/statement_pins.py`, which the lead is still confirming. The reviewer found
  nothing suspicious. Each new `Laws/` module uses the namespace of the spec file that its
  declarations came from, so moved definitions such as `law` keep their fully qualified
  names.
- **Moved code.** A line-level comparison of the diff and the new files shows that every
  removed line reappears unchanged, apart from module headers, imports, docstrings, and the
  `private` modifier that a cross-module move requires. The remaining differences are the
  retry migrations, the two heartbeat removals, and four deleted lemmas.
- **Deleted lemmas.** `BinaryRounding.round_of_dvd`, `BitRecycler.upper_output_lt`,
  `PoissonTree.potential_bound`, and `AbsorbingChain.stopLaw_singleton` have no users in
  the repository. The re-export shims `Common/Laws/BinomialMeasure` and
  `Common/Laws/PoissonMeasure` are gone, and no module imports them.
- **Moved modules.** `Common/FractionalPowerCore` moves to `Common/Laws/FractionalPowerCore`
  with an identical body. `Discrete/Laws/NegativeBinomialStep` becomes
  `Discrete/Laws/NegativeBinomial` and gains the law from the spec file. No public spec
  file moves.
- **Retry migrations.** `DiscreteLaplace`, `FisherMultivariate`, `Geometric`
  (`Retry.twp_loop_forall`), `LogarithmicSeries`, `PolyaRational`, `ZeroTruncatedPoisson`,
  `Zeta`, `Zipf`, and `Support/BinomialHalfRejectionCore` now use the shared retry lemma.
  Each follows the shared recipe: the round starts with the combined credit, and the retry
  branch passes the amplified credit to `IH` without a split. `Borel`, `BinomialBinary`,
  `PoissonOne`, and `NegativeMultinomial` keep their hand-rolled proofs. The first three are
  on the exclusion list, and the last quantifies over several loop variables and a
  remaining-success potential.
- **Heartbeats.** The overrides in `BetaBinomial` and `Cub` are gone. `Cub` now states the
  six unfolding lemmas that the proof was searching for. No new `set_option`, `sorry`,
  `admit`, `axiom`, or `native_decide` appears in either directory.
- **Math and Iris split.** No `Laws/` module in either directory imports a spec,
  `Support/`, or `Syntax/` module, Iris, or the program logic. Modules that imported spec
  files at the base, such as `Laws/DyadicProposal`, `Laws/InverseUrnMass`,
  `Laws/LogarithmicSeries`, `Common/Laws/ListProduct`, and `Common/Laws/FiniteCDF`, now
  import `Laws/` modules instead.
- **Build.** `lake build` of every module in both directories and every import of the
  callers below succeeds with no warnings.
- **Callers and axioms.** These callers compile through the memory gate with no errors and
  no warnings: `ExactFactoriesBatch017Callers`, `ExactDiscreteBatch001Callers` through
  `ExactDiscreteBatch006Callers`, `DiscreteCallers`, `NextBatchWeightedFactoriesCallers`,
  `NextBatchFiniteCallers`, `ExpansionDiscreteCallers`, `ExpansionDiscreteBatch001Callers`
  through `ExpansionDiscreteBatch006Callers`, `ExpansionDiscreteBatch008Callers` through
  `ExpansionDiscreteBatch011Callers`, `ExpansionStructuredBatch012Callers`,
  `ExpansionDiscreteBatch013Callers`, and `ExpansionDiscreteBatch014Callers`. Every printed
  axiom set is a subset of `propext`, `Classical.choice`, and `Quot.sound`.

## Nits

These nits do not block acceptance.

- `Discrete/PolyaRational.lean:216` keeps its `set_option maxHeartbeats 1000000 in` from
  the base.
- `Discrete/FisherMultivariate.lean` has 285 lines, above the 250-line target (290 at the
  base).
- Seven `Discrete/Laws/` modules and `Common/Laws/ListProduct` import
  `Metrology.ProbLang.Discrete`. That module holds measure instances for ProbLang types, not
  program logic, and `Weighted/Laws/SplittingPPSLaw` sets a precedent.
- `Common/Laws/AlternatingFactorial`, `Common/Laws/Exponential`, and
  `Common/Laws/ExponentialFactory` still import `Metrology.TotalEris.Examples.Samplers`
  modules. The refactor leaves these base-era imports unchanged.
- Some spec docstrings, such as `Discrete/Hypergeometric.lean:6-9`, restate the law that
  the matching `Laws/` docstring already describes, instead of the CTE proof.
- The module counts in `Discrete/README.md` and `Common/README.md` are stale.
- `agent-docs/relocations/Relocation001.json` still maps to
  `SampLib.Common.FractionalPowerCore` and `SampLib.Discrete.Laws.NegativeBinomialStep`.
