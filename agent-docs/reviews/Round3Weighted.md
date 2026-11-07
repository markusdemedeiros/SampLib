# Round 3 review: Weighted

Reviewer `round3_review_weighted` re-reviews the round-3 refactor of `SampLib/Weighted/`
against base commit `8f819b7`. `SampLib/OptimalScan.lean` is unchanged from the base.

## Verdict

Accepted. Every change moves code, splits a file by topic, removes a heartbeat override, or
migrates a retry proof to the shared lemma. Each proof is still a clear proof of the same
theorem.

## Proofs and new hashes

The following table lists every stale public spec and its new proof hash, exactly as
`refactor_receipts.py --list` prints them.

| Sampler | Public spec | Record | Proof hash |
| --- | --- | --- | --- |
| `Occil.WeightedVariants.voseDraw` | `SampLib.AliasTable.voseDraw_ownedDistSpec` | Exact (B) | `0356fbedef3039f447ae5908106f480f9e6f20dd201357b58a972afaa34f14db` |
| `Occil.WeightedVariants.optimalChoice` | `SampLib.Optimal.optimalChoice_distSpec` | Exact (A) | `e6302d292ec9d92d111706e17b2847e85014767d8bc7dacc5df0fd8b5a406547` |
| `Occil.WeightedVariants.optimalDraw` | `SampLib.OptimalTable.optimalDraw_distSpec` | Exact (A) | `59dba21dbc5f4fccdea40726f063d51b7ace12c0d231a0eeccec6216870be194` |
| `Occil.WeightedVariants.sortedChoice` | `SampLib.SortedChoice.sortedChoice_distSpec` | Exact (B) | `c660db5d60ae7820a42ad27acd24a7ce4a319f7cf24dba022778c4fe248e8cb0` |
| `Occil.WeightedVariants.succinctChoice` | `SampLib.SuccinctChoice.succinctChoice_distSpec` | Exact (B) | `2a14d11d001dcae2dac8cb114407bbf6d727f799844e19078525cc6a6837c194` |
| `Occil.Weighted.inclusionSplitting` | `SampLib.InclusionSplitting.inclusionSplitting_distSpec` | Exact (B) | `432849d43be63264c4ecbdb9133d4243d7cf826cb2928557ea3e4118b5a3b874` |
| `Occil.Weighted.inclusionSystematic` | `SampLib.InclusionSystematic.inclusionSystematic_distSpec` | Exact (B) | `a949361dd70ecefed41093a1296a47111abba57d9288cd98566b8653405e7bca` |
| `Occil.Weighted.fastLoadedDiceRoller` | `SampLib.FastLoadedDice.fastLoadedDiceRoller_distSpec` | Exact (B) | `a3cff0e8c8e14e8c594c99bc29a8b7c39b37a5c6a0af43fe10460c9fad3f007e` |
| `Occil.Weighted.hanHoshi` | `SampLib.HanHoshi.hanHoshi_distSpec` | Exact (B) | `7609a5fa6266af55020a8e707cca2e955f9a0d43c62f314c38a3464167499f03` |
| `Occil.Weighted.knuthYao` | `SampLib.KnuthYao.knuthYao_distSpec` | Exact (B) | `540f52556747fad2799f9807b267a470ee62eeed206276dd07847c20320e85e1` |
| `Occil.Weighted.recycledSamples` | `SampLib.RecycledSamples.recycledSamples_distSpec` | Exact (B) | `78f6d985224f0f98bfc10c4150ddc04a4462326dd67ddb232382c551c0e8595b` |
| `Occil.Weighted.recycledUniform` | `SampLib.RecycledUniform.recycledUniform_ownedDistSpec` | Exact (B) | `5adf332059a8df3a91423259eebe88f5fceed7d361e03a8222c9fcf772f85c64` |
| `Occil.weightedRejection` | `SampLib.WeightedRejection.weightedRejection_distSpec` | Historical | `336e3200341bbdb43280f56bdb23915cd8161bd0355bb9cfd09043c446276f71` |
| `Occil.Weighted.randomBits` | `SampLib.RandomBits.randomBits_distSpec` | Historical | `5a4965f5879067dcda4f820f22aa97948f0be07531b1c04d2f78ea2eb859dd0b` |
| `Occil.Weighted.uniformRational` | `SampLib.UniformFormats.uniformRational_distSpec` | Historical | `2e5ea0d529659fbed1bc0856823d0706be6ce56f3069fa62cdca87dfde4024a4` |
| `Occil.Weighted.uniformFixed` | `SampLib.UniformFormats.uniformFixed_distSpec` | Historical | `2e5ea0d529659fbed1bc0856823d0706be6ce56f3069fa62cdca87dfde4024a4` |
| `Occil.Weighted.uniformDyadic` | `SampLib.UniformFormats.uniformDyadic_distSpec` | Historical | `2e5ea0d529659fbed1bc0856823d0706be6ce56f3069fa62cdca87dfde4024a4` |
| `Occil.Weighted.moduloReduction` | `SampLib.WordReductions.moduloReduction_distSpec` | Historical | `47d510250f3d50d994ea8657df1f9fc37a9c4bb04df7046513a856eff4f492d9` |
| `Occil.Weighted.multiplyShift` | `SampLib.WordReductions.multiplyShift_distSpec` | Historical | `47d510250f3d50d994ea8657df1f9fc37a9c4bb04df7046513a856eff4f492d9` |
| `Occil.WeightedVariants.sequentialCoins` | `SampLib.SequentialCoins.sequentialCoins_distSpec` | Historical | `01f31d867424cd4f3a60651d6ede4a365591b1ebe2693e5480c7c7173f1d3a75` |
| `Occil.Weighted.bitmaskRejection` | `SampLib.BitmaskRejection.bitmaskRejection_distSpec` | Historical | `d8457330069db0eea061e9546a816a2596916fde17e8896189130a193a033dc0` |
| `Occil.Weighted.weightedReservoirOne` | `SampLib.WeightedReservoirOne.weightedReservoirOne_distSpec` | Historical | `91cc8758ca5fe3f85cf53e6052c40fa62752ac5b9056c48b7f921b4d76ac9a47` |
| `Occil.WeightedVariants.divisionRejection` | `SampLib.DivisionRejection.divisionRejection_distSpec` | Historical | `987450a912db5d5451ca54fc53d476a6b57f2824d23afdc575b2e37a29d38b19` |
| `Occil.WeightedVariants.debiasedModulo` | `SampLib.DebiasedModulo.debiasedModulo_distSpec` | Historical | `48a04d9416e131546fac9d39c3cd33a5c1dd77d423bfd9d97d24773aede876d2` |
| `Occil.WeightedVariants.flatChoice` | `SampLib.FlatChoice.flatChoice_distSpec` | Historical | `6f3eab5a479decfe5826b08911e5bfc8e64b8abfd41835e89fc7c5b95b7fadf1` |
| `Occil.WeightedVariants.lemireUniform` | `SampLib.LemireUniform.lemireUniform_distSpec` | Historical | `0a14f680373deb4c236dade445a169470354cf85d9ecaa3e3f37375f29649df6` |
| `Occil.WeightedVariants.oneillUniform` | `SampLib.OneillUniform.oneillUniform_distSpec` | Historical | `c8b5ed207f7cedca16b2f468b8e07524729497748f0833f1c44bf4dad74c0221` |
| `Occil.weightedWithoutReplacement` | `SampLib.WeightedWithoutReplacement.weightedWithoutReplacement_distSpec` | Historical | `5de50e46b07422b1a325b9fa86f7c9f5b145974cc277b590dbc6c27d27929e49` |
| `Occil.Weighted.cumulativeDraw` | `SampLib.CumulativeDraw.cumulativeDraw_distSpec` | Historical | `ffa3975fed2367ff32e4efee0a434fb9a7d961d272b755af8faa0999a645e8d3` |
| `Occil.Weighted.cumulativeChoice` | `SampLib.CumulativeChoice.cumulativeChoice_distSpec` | Historical | `aedcd5b5a2fe0862299e39d40eb7556cf5da1598871c2de5395da7d814b675c9` |
| `Occil.Weighted.rationalChoice` | `SampLib.RationalChoice.rationalChoice_distSpec` | Historical | `96bd7bcdcf82bcaa3b7aad5beedda1329df76f44942c502e21b0187a91f3e087` |
| `Occil.Weighted.uniformBinaryFloat` | `SampLib.UniformBinaryFloat.uniformBinaryFloat_distSpec` | Historical | `275b419cf972c220edfa0e0d5a28f9372e74b8bafacb4d659617c134cf1349ef` |
| `Occil.WeightedVariants.voseSamples` | `SampLib.VoseSamples.voseSamples_distSpec` | Historical | `434821f1d84c31aaa832c8483a0f58d2392f83ae80fb9555277a48a3e6df8027` |
| `Occil.WeightedVariants.twoLevelChoice` | `SampLib.TwoLevelChoice.twoLevelChoice_distSpec` | Historical | `e0a3aaa0d4727050edb7d1ca46d586cab86ec372aa77842a6a9deb37cc6da84c` |
| `Occil.Weighted.fyky` | `SampLib.FYKY.fyky_distSpec` | Historical | `6bff1b3b779ddd5293240468b81d1396626e309767eb89cc1d65a28670a3783b` |
| `Occil.WeightedVariants.floatingMultiply` | `SampLib.FloatingMultiply.floatingMultiply_distSpec` | Historical | `52f27b5818b1638cb709b801b797861a7e3851c49b5fbc2429e255a6d53c131f` |
| `Occil.WeightedVariants.fenwickDraw` | `SampLib.FenwickDraw.fenwickDraw_ownedDistSpec` | Historical | `28988616dc8b18bf0afc13774b5745d470b24f4cc392e55a9869a76c813cfca6` |
| `Occil.aliasSamples` | `SampLib.AliasSamples.aliasSamples_distSpec` | Historical | `bf0c9332660c4231c3e7fb5b77c7388f73370106568879cdab71f688dbf1ede1` |

## What the reviewer checked

- **Statements.** The statement check rests on the lead's mechanical pin check with
  `agent-scripts/statement_pins.py`, which the lead is still confirming. The reviewer found
  nothing suspicious. Moved definitions that appear in public types, such as
  `WeightedReservoirOne.law`, `PowerOfTwoCeiling.width`, and `CumulativeDraw.cumulative`,
  keep their fully qualified names and bodies.
- **Moved code.** A line-level comparison of the diff shows that every removed line
  reappears unchanged, apart from module headers, imports, and the `private` modifier that
  a cross-module move requires.
- **Retry migrations.** `BitmaskRejection`, `DebiasedModulo`, `DivisionRejection`,
  `LemireUniform`, `OneillUniform`, `WeightedRejection`, `Support/SortedChoice`, and
  `Support/SuccinctChoiceProposal` now use `Retry.twp_loop`. Each follows the shared
  recipe: the round starts with the combined credit, and the retry branch passes the
  amplified credit to `IH` without a split. The remaining hand-rolled proofs
  (`OptimalDraw`, `Support/OptimalDraw`, `Support/FastLoadedDiceRoot`) are on the exclusion
  list.
- **Duplicates.** `Laws/EnvelopeRejection` no longer imports the `WeightedRejection` spec
  file. The private duplicates `one_lt_factor` and `coin_expectation` in `WeightedRejection`
  are gone, and the spec uses `EnvelopeRejection`'s copies. A local `length_pos` gives way to
  `List.length_pos_of_sum_ne_zero`.
- **Heartbeats.** The three `set_option maxHeartbeats` overrides in `InclusionSplitting` and
  `WeightedRejection` are removed. No new `set_option`, `sorry`, `admit`, `axiom`, or
  `native_decide` appears.
- **Laws purity.** No `Laws/` module imports a spec, `Support/`, `Syntax/`, Iris, or program
  logic module. Three `Laws/` modules import `Metrology.ProbLang.Discrete`, which only
  provides measurable-singleton instances.
- **Layout.** Every new or changed module starts with a `/-! #` docstring. No line exceeds
  100 columns. The splits of `VoseBalance`, `VoseTable`, `EntropyPoolAbsorption`, and
  `Fenwick` follow topic boundaries and keep each part under 250 lines.
- **Build.** `lake build` of all 173 modules in `SampLib/Weighted/` plus
  `SampLib.OptimalScan` succeeds with no warnings or errors. No module outside these
  directories imports them.
- **Axioms.** `#print axioms` on all 38 public specs reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
- **Callers.** The ten caller files `ExactStructuredBatch002Callers.lean`, `003`, `005`,
  `007`, `008`, `009`, `010`, `011`, `012`, and `013` compile with no errors and no warnings.

## Nits

These nits do not block acceptance.

- `Support/SuccinctChoiceProposal.lean:18` keeps a public forwarding lemma `length_pos`.
  Call `List.length_pos_of_sum_ne_zero` directly, as `WeightedRejection` does.
- `Support/TwoLevelChoice.lean` turns four private `ClosedExp` instances into global
  instances. Other `Syntax/` modules declare these as `scoped instance`.
- `Laws/EnvelopeRejection.lean` holds the `SampLib.WeightedRejection` namespace. Addendum A
  names that module `Laws/WeightedRejection`.
- `InclusionSplitting.lean` still has 326 lines, above the 250-line target.
- `Laws/LemireUniform.lean` uses the British spelling "fibres"; IBM style uses "fibers".
- `Laws/FenwickDraw.lean` and `Laws/CumulativeDraw.lean` hold one declaration each.
