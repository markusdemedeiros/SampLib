# Round 3 review: General family

Reviewer: `round3_review_general`. Base commit: `8f819b7`.

## Scope

This review covers every file under `SampLib/General/` and the 42 samplers in the lead's
sampler list for this group.

## Result

The refactor is accepted. Every change keeps the theorem it proves and reads at least as
clearly as before.

Statement equality rests on the lead's mechanical pin check
(`agent-scripts/statement_pins.py`). This review found nothing that suggests a changed
statement, but it did not rerun that check.

## Public specs and proof hashes

The table lists every stale public spec and its new proof hash, exactly as
`refactor_receipts.py --list` prints them.

| Record | Sampler | Public spec | Proof hash |
| --- | --- | --- | --- |
| Exact (`/root/review_exact_b`) | `Occil.General.incompleteInformation` | `SampLib.IncompleteInformation.incompleteInformation_distSpec` | `be4442e3df693c6efe1537b657659a728eca2db846e79aceea1a6b5997fcfc47` |
| Exact (`/root/review_exact_b`) | `Occil.General.markovStep` | `SampLib.MarkovChain.markovStep_distSpec` | `56224c487a39afd990278b97b5ddb0c216cb2834ad804f2576688b414714cc4e` |
| Exact (`/root/review_exact_b`) | `Occil.General.refinedCDFComparison` | `SampLib.RefinedCDFComparison.refinedCDFComparison_coinSpec` | `cc5db5533d56dc693a93dc40aacffe117307c23716bb1ac2210d77780baf81f3` |
| Exact (`/root/review_exact_b`) | `Occil.General.refinedCoin` | `SampLib.RefinedCoin.refinedCoin_distSpec` | `4f295b295ae530c47796fb47db6ff4997060919b0db089c0c1552a15cec6f085` |
| Exact (`/root/review_exact_b`) | `Occil.General.shapeRejection` | `SampLib.ShapeRejection.shapeRejection_distSpec` | `0594bc45de1a3b6978372c6284c825c80173104514879801d6fb49c201216df2` |
| Historical | `Occil.General.generativeModel` | `SampLib.GenerativeModel.generativeModel_distSpec` | `e04f29b2b31f2b41f85f79c4218f5b53e138749bfd744147deb83debb237f6db` |
| Historical | `Occil.General.inverseQuantile` | `SampLib.InverseQuantile.inverseQuantile_distSpec` | `3fa39ac80c62ed88fc12c655a2c92885eb02b2845a3bf56811b69f91ac45aa99` |
| Historical | `Occil.General.kernelDensity` | `SampLib.KernelDensity.kernelDensity_distSpec` | `cc9a28307658df8aa10afdcacdfb0bcd9b41d7d7c5cca01fa44194f01bcc9deb` |
| Historical | `Occil.General.uniformBoxPoint` | `SampLib.UniformBoxPoint.uniformBoxPoint_distSpec` | `194a6161cf02426342ca588d6a7c5754c9aca77b914463987a4f19f960ae32b8` |
| Historical | `Occil.General.stoppedSum` | `SampLib.StoppedSum.stoppedSum_distSpec` | `8ced74539fef37287738c941ae37864851aa8d7dc9e7767849a1d1fbcd5a0e70` |
| Historical | `Occil.General.episodes` | `SampLib.Episodes.episodes_distSpec` | `0066bd14bde02fb71fc850c3927e8d77e6e0017039d70d7b4e101e4c7c5da11c` |
| Historical | `Occil.General.kernelDensityVector` | `SampLib.KernelDensityVector.kernelDensityVector_distSpec` | `02e452fe971a1021754cc49c610c3c224a89cdf5a991826700b2df8b3e97dcce` |
| Historical | `Occil.General.stratified1D` | `SampLib.Stratified1D.stratified1D_distSpec` | `1b1abd9a16488d9796b7b754c7373030dd8db87e1171e244e6ea61ec227f6603` |
| Historical | `Occil.General.randomString` | `SampLib.RandomString.randomString_distSpec` | `3313ba6dd576a64f64347ff79b3380848c207a677f4059e9766d3e2ddcde7b9c` |
| Historical | `Occil.General.randomDateTime` | `SampLib.RandomDateTime.randomDateTime_distSpec` | `2df496c142f5c78a8233f98a2d48ee461dc95c2e83a9588cb8ef38d94fa8aedb` |
| Historical | `Occil.General.bootstrap` | `SampLib.Bootstrap.bootstrap_distSpec` | `153238f19394a828d8aa34518d8112077f36db3cde5c60dcd6c3c9e54f3e6345` |
| Historical | `Occil.General.histogram` | `SampLib.Histogram.histogram_distSpec` | `4085bae2465cb68cb118b6f657378316b9ab692184fadba81665c628f9112477` |
| Historical | `Occil.General.latinHypercube1D` | `SampLib.LatinHypercube1D.latinHypercube1D_distSpec` | `36d47323b21a7ff4867c05ea32a1c208b1deb3ff926810696918b95f3e47cddf` |
| Historical | `Occil.General.stratifiedBox` | `SampLib.StratifiedBox.stratifiedBox_distSpec` | `62ff5d41f35519a4429c48a91a9c96200acc129a707df1179ef8198c1e27e34a` |
| Historical | `Occil.General.classifiedModel` | `SampLib.ClassifiedModel.classifiedModel_distSpec` | `7a4fc1d37afb22d00212cd9a3198d785e68efe943861e050ca5f005bc8429783` |
| Historical | `Occil.General.markovChain` | `SampLib.MarkovChain.markovChain_distSpec` | `56224c487a39afd990278b97b5ddb0c216cb2834ad804f2576688b414714cc4e` |
| Historical | `Occil.General.randomMap` | `SampLib.RandomMap.randomMap_distSpec` | `64a86fab170603d5b36b2eda67f7450c1dedc8290f702372d7f5b53af51421f6` |
| Historical | `Occil.General.randomWalkPath` | `SampLib.RandomWalkPath.randomWalkPath_distSpec` | `fd343452143c56d98ef648810b0b68db00d674946dcd346d90d205117ce9149e` |
| Historical | `Occil.General.permutationSamples` | `SampLib.PermutationSamples.permutationSamples_distSpec` | `80ddafde745354277b34f8caed60a1de0c78621ec028e5ee013d8dc45c4d4d5a` |
| Historical | `Occil.General.stoppedMinimum` | `SampLib.StoppedMinimum.stoppedMinimum_distSpec` | `930024504d48a9a98d255a5487b8a00889336d5f31d690f25c2b9a2a937763c0` |
| Historical | `Occil.General.stoppedMaximum` | `SampLib.StoppedMaximum.stoppedMaximum_distSpec` | `036d85be5eac5e223e78adaaf685e3ea5abf0e1c91dcc9ddce59bae7e288e2f9` |
| Historical | `Occil.General.markovTrajectory` | `SampLib.MarkovTrajectory.markovTrajectory_distSpec` | `a7bb9341b74fba2a2b5640c94ed35d89f966aa07f57a4d896195f05545335a9c` |
| Historical | `Occil.General.gibbsSweep` | `SampLib.GibbsSweep.gibbsSweep_distSpec` | `e25e287f37cfe0555fab079fc06c4b08d9c2a7aff816dd1ef49f2364c0668430` |
| Historical | `Occil.General.randomScanGibbs` | `SampLib.RandomScanGibbs.randomScanGibbs_distSpec` | `69a383b12c345b9802e709ef35e56ad1872454415b0b527bc73fb2ba9db44b40` |
| Historical | `Occil.General.permutationTest` | `SampLib.PermutationTest.permutationTest_distSpec` | `15b0f86d7a448d8eb3c29bf910116fee32b0094a13f833732b855b7294dc3c73` |
| Historical | `Occil.General.groupedPermutation` | `SampLib.GroupedPermutation.groupedPermutation_distSpec` | `4e93a11c0de3a3d87b53779c95eaa95b84f6aeb1969bc41c0a628bbdeaeea636` |
| Historical | `Occil.General.pdfRejection` | `SampLib.PdfRejection.pdfRejection_distSpec` | `eed1834ce06c0980475e7cad4b46a2728b60254625bb5c6b2b85286689dde72c` |
| Historical | `Occil.General.latinHypercube` | `SampLib.LatinHypercube.latinHypercube_distSpec` | `0156fc68192a28cda2547d587782cf41559a769415778bcd31c62fd688420a2e` |
| Historical | `Occil.General.inverseCDF` | `SampLib.InverseCDF.inverseCDF_distSpec` | `516c320bfff5a31180199ec1190c20ce68fd4034cef8820f33e5de5dd138a3f8` |
| Historical | `Occil.General.metropolisHastings` | `SampLib.CountableMetropolisHastings.metropolisHastings_distSpec` | `6f35ca9f960573f8e48b2f96a5faf10e90fad2ed734c8ef801628d5b0e6e7c2d` |
| Historical | `Occil.General.metropolis` | `SampLib.CountableMetropolis.metropolis_distSpec` | `49e4965cfebccc8a7f39a1bdc916f765e88c804454fe07f14ed60e9400d0ae13` |
| Historical | `Occil.General.discreteCDF` | `SampLib.DiscreteCDF.discreteCDF_distSpec` | `61518eb56a1bf57b72767e5dc4f69f8b3baf62aac126fa057bd94e3c0d5f56df` |
| Historical | `Occil.General.piecewiseConstant` | `SampLib.PiecewiseConstant.piecewiseConstant_distSpec` | `e069789fbfe27bc2f10fcc08825a201935fcf15ddb474f394afb36ee70ccf682` |
| Historical | `Occil.General.piecewiseLinear` | `SampLib.PiecewiseLinear.piecewiseLinear_distSpec` | `2a4984af3f35b407098b4efb914c55f03c0ad59da2fef32c5b4f8f539c40def0` |
| Historical | `Occil.General.couplingFromPast` | `SampLib.CouplingFromPast.couplingFromPast_distSpec` | `7e9a5c64ab9c5f22f94a5791e22c6793c3965642ab5289d7ac528dcd0e043e2d` |
| Historical | `Occil.General.perfectFiniteChain` | `SampLib.PerfectFiniteChain.perfectFiniteChain_distSpec` | `d7db40992ed81f94bfd305e6c577101c4c651781042e530a98db8eabaf0a62b1` |
| Historical | `Occil.General.sliceSampler` | `SampLib.SliceSampler.sliceSampler_distSpec` | `2ca9ff02c0fa96167d86533f78615a69c3927381f2da73c57f16e5b407903667` |

## What this review checked

- **Moved definitions.** A line-by-line comparison of the removed and added text in
  `git diff 8f819b7 -- SampLib/General/` shows that every moved definition, instance, and
  lemma keeps its name, namespace, and body. The only differences are dropped
  `section mathematics` wrappers, new module headers, and `private` modifiers that a move
  across modules forces.
- **New `Laws/` modules.** The refactor adds 24 `Laws/` modules and extends
  `Laws/CouplingFromPast`. It deletes `Laws/LatinHypercubeSupport`, whose lemma now lives
  in `Laws/LatinHypercube1D`. The transitive import closure of every `General/Laws/`
  module contains only mathlib, `Laws/` modules, `SampLib.Core.Laws`, and the measurable
  instances of `Metrology.ProbLang.Discrete`, `Measure`, and `Reals`. It contains no spec,
  `Support/`, or `Syntax/` module and no Iris or TotalEris module. The earlier leaks
  through `Laws/FiniteKernels`, `Laws/IIDList`, `Laws/Metropolis`, `Laws/MetropolisRatio`,
  `Laws/PiecewiseConstant`, `Laws/RandomMapSupport`, `Laws/RepeatedSupport`,
  `Laws/StoppedExtrema`, `Laws/LinearBin`, and `Laws/LatinHypercubeSupport` are gone.
- **Spec files.** Each public spec file now holds the encoding, the program proof, and the
  public theorem. Its mathematics moved to `Laws/<Name>`.
- **Retry migrations.** `PdfRejection` and `Support/LinearBinSampling` now use
  `Retry.twp_loop`. Both follow the plain recipe: the retry credit is
  `credit + factor * ε`, and the explicit credit split and combine steps are gone.
  `CouplingFromPast` uses weighted induction and `Support/RefinedComparison` uses a finite
  horizon, so neither fits the shared lemma.
- **Heartbeat overrides.** The refactor removes all six overrides, in `LatinHypercube`,
  `MarkovChain`, `MetropolisKernel`, `PermutationTest`, `StratifiedBox`, and
  `Support/RefinedComparison`. Two proofs now state the normalization they need
  (`Shuffle.shuffle_openRec` and `UniformBag.uniformBagLess_openRec`). `StratifiedBox`
  registers its unfolding lemmas as local `pl_step_simp` rules and adds the one-line
  lemma `sampler_fst`. No `set_option`, `sorry`, `admit`, `axiom`, or `native_decide`
  remains in `SampLib/General/`.
- **Syntax split.** `Syntax/RefinedComparisonOpen` takes the three `twp_open_*` lemmas
  from `Syntax/RefinedComparison` without change.
- **Layout.** Every file starts with a `/-! #` title, no line exceeds 100 columns, and the
  largest file has 257 lines. `git diff --check` reports nothing.
- **Build.** `lake build` through the memory gate succeeds for every module in
  `SampLib/General/` and every caller import (4581 jobs, no warnings).
- **Callers.** These caller files compile through the gate with no errors and no
  warnings: `ExactStructuredBatch001Callers.lean`, `ExactStructuredBatch004Callers.lean`,
  `ExpansionStructuredBatch001Callers.lean` to `ExpansionStructuredBatch006Callers.lean`,
  `ExpansionStructuredBatch008Callers.lean` to `ExpansionStructuredBatch011Callers.lean`,
  `ExpansionStructuredBatch013Callers.lean`, `ExpansionStructuredBatch014Callers.lean`, and
  `ExpansionStructuredCallers.lean`. Every printed axiom list is
  `[propext, Classical.choice, Quot.sound]`.

## Nits

These nits do not block acceptance.

- `ClassifiedModel.length_ne_zero` and `CappedRationalCoin.bias_full` became public, but
  only their own `Laws/` file uses them. They can stay `private`.
- Four touched `Laws/` modules (`FiniteKernels`, `GenerativeModel`, `ListMapSampling`,
  and `StoppedSum`) use the `module` header with `public import`. The other new `Laws/`
  modules use plain `import`. One style per family reads better.
- `CappedRationalCoin.bias`, `Stratified1D.boundary`, and `PdfRejection.proposal` have no
  docstring, as before the move.
- Several spec files now import a sibling spec (for example `SampLib.Discrete.WeightedChoice`)
  that they used to get through a leaking `Laws/` import. The imports are correct; they
  only make the dependency explicit.
