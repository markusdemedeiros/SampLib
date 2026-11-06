# Factory expansion review: batch 010

Reviewer: `/root/expand_review_factories`.

All six sampler modules passed independent targeted builds without warnings. The immutable caller compiles warning-free, exercises arbitrary resource frames and boundary/infinite-credit cases, and prints exactly the three standard axioms for all 10 inspected theorems.

## Occil.FactoryExtra.linearPower

Accepted `SampLib.LinearPower.linearPower_distSpec`, SHA-256 `a750afb64fab584805fb393de66c420a6f50c9ee0a31e34fb5ae5e7b969e23ab`.

Finite iteration of the verified linear callback gives the exact independent power law. The zero branch executes before inspecting any coefficient, margin or callback. Structural lambda insertion preserves arbitrary callback free variables. Independent clients frame arbitrary resources and instantiate zero power with invalid coefficients and infinite credit on its impossible false outcome.

## Occil.FactoryExtra.addition

Accepted `SampLib.Addition.addition_distSpec`, SHA-256 `9e4cce8eb3dccc2ef9a1427a8e0415e7732dad0eb36f4fb44589c4f575b89763`.

The existing mean coin has probability (p+q)/2; the full-domain Linear factory doubles it. A separate real ratio identity establishes the law. The program proof is direct callback composition and source beta execution. The independent framed client retains arbitrary callbacks and output credits; a quarter-plus-quarter test checks the exact expanding margin boundary.

## Occil.FactoryExtra.subtraction

Accepted `SampLib.Subtraction.subtraction_distSpec`, SHA-256 `40b20f54cb53685cf42fc128ce118ecedf4db8776e5bfc4db7555f76e0c612e0`.

Complementing the first callback, adding the second and negating the result gives p-q. The single expectation reuses the checked complement lemma for arbitrary ENNReal credits. Execution follows those three known idioms. The independent framed client and exact one-minus-half endpoint-margin test check callback order and result orientation.

## Occil.FactoryExtra.division

Accepted `SampLib.Division.division_distSpec`, SHA-256 `8315b402a0db1f1aa8f7c70a4b2af6aa59fb0b37febd6c5785cab1993cab2208`.

The actual source races the numerator against the verified denominator-minus-numerator callback. The positive gap guarantees exit, and the accepted-mass ratio is q/p. A structural adapter preserves callback free variables. Independent framed clients explicitly follow the source numerator-first argument order, check a half-over-quarter ratio, and test infinite true-output credit at zero numerator.

## Occil.FactoryExtra.affine

Accepted `SampLib.AffineFactory.affine_distSpec`, SHA-256 `f1b6c2db9780d4f2d03239b56bf01c200f0de380172c934a488e1aaf81fa0b98`.

A rational mixture first adds the constant offset, then the verified Linear factory scales it. The normalized mixed probability and independent real ratio identity give exactly (x/y+p)/(a/b). Selector bounds are prepared before execution; callback hygiene uses a structural lambda. Independent clients retain arbitrary frames and callbacks, test the expanding equality boundary and the contracting branch with negative numerator and zero denominator margin arguments.

## Occil.FactoryExtra.affineRatio

Accepted `SampLib.AffineRatio.affineRatio_distSpec`, SHA-256 `ed5f4dbcdf14520af20452fdee73778bc97c0fea13575eee20038f9c91b3629b`.

The target is (x/y+q)/(a/b+p). The direct branch partitions four uniform-rank intervals into explicit success/failure/retry masses, identifies their normalized ratio, and pays retry amplification via BernoulliRetry. The other branch draws two affine rank coins with common normalization and invokes Division using exactly the supplied normalized gap. Both original source branches are verified. Independent clients cover arbitrary frames and callbacks, direct equality with bias one and invalid margins, zero offsets, non-direct exact gap equality and infinite off-support credit.

## Shared support

All support was independently source-reviewed. LinearFactorySyntax isolates the verified adaptive factory as a locally closed value and proves fresh-name/opening facts without restricting caller callbacks. The existing complement and finite-iteration syntax helpers remain unchanged. All six new proof files independently re-elaborate warning-free under ordinary project heartbeat defaults.

The immutable caller is `agent-docs/reviews/ExpansionFactoriesBatch010Callers.lean`, SHA-256 `1e910d84b6d0fc526dfe8771eafcaeeefdc636ef358a63bc3bf51df661eeeac2`.
