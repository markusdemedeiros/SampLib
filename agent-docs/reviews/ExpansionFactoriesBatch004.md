# Factory expansion review: batch 004

Reviewer: `/root/expand_review_factories`.

All eight modules passed independent targeted builds without warnings. The immutable caller compiles warning-free, exercises arbitrary resource frames and boundary/infinite-credit cases, and prints exactly the three standard axioms for all 16 inspected theorems.

## Occil.FactoryExtra.reciprocalAffine

Accepted `SampLib.ReciprocalAffine.reciprocalAffine_distSpec`, SHA-256 `24cd1370f7c53a7ab7fcbf82a6ff072cfade4677e121b51f135f14ebf7f34428`.

The interval trial has accepted true width d, accepted false width c-d+s*p, and retry width s*(1-p). Its central expectation identifies the normalized law d/(c+s*p) via BernoulliRetry and funds retries with a strict amplification factor. All arithmetic concerns finite coefficients; continuation credits remain arbitrary ENNReal. The CTE proof follows uniform rank, the three ranges, the input callback, and the retry credit split. Independent clients cover arbitrary framing, zero numerator, maximal numerator at both input endpoints, and infinite off-support credit.

## Occil.FactoryExtra.reciprocalAffinePower

Accepted `SampLib.ReciprocalAffinePower.reciprocalAffinePower_distSpec`, SHA-256 `10d5c9063b743b6e4e4aade710f512b086a43dddba3b993d804e97b314e12801`.

A structural callback feeds the reciprocal-affine specification to IterateCoin, yielding the exact independent power law. Zero repetitions are also specified with invalid rational parameters and no callback contract or uniform-integer assumption, matching the actual early return. Independent clients test arbitrary resource frames for both interfaces and zero-count infinite off-support credit. No auxiliary deterministic metadata helper is counted as a sampler.

## Occil.FactoryExtra.inverseQuadratic

Accepted `SampLib.InverseQuadratic.inverseQuadratic_distSpec`, SHA-256 `fc98d7ba69139a9fdfbc7a419447dc0b03d224b5b6bd1005ec98e33b445b5afc`.

A rational selector mixes p and p squared; a finite algebraic identity turns the verified reciprocal-affine bias into 1/(1+(m+p)^2). The mathematical polynomial substitution is isolated before execution. Program logic composes the selector, callback or two fresh draws, and reciprocal factory. Independent resource clients and endpoint checks cover m=0, p=0/1, a positive shift, and infinite credit outside the deterministic-true endpoint.

## Occil.Constants.sqrtTwoMinusOne

Accepted `SampLib.SqrtTwoMinusOne.sqrtTwoMinusOne_distSpec`, SHA-256 `dfb57af5f411260521e425e80e345f559316c7690b2d7d4238188ff6a104a70e`.

The quadratic is factored as (n-pD)(n+pD+2D), with the second factor strictly positive for every positive denominator. The concrete integer-sign oracle then instantiates the already reviewed algebraic-root engine. Program logic is deterministic oracle execution followed by that engine. Independent clients preserve arbitrary resources and check the exact canonical root and a rational sign test.

## Occil.Constants.inverseSqrtTwo

Accepted `SampLib.InverseSqrtTwo.inverseSqrtTwo_distSpec`, SHA-256 `9d047e6cb9c14d2030719262fa8efb4db144e7ed803d18810c122e371272cf9c`.

The quadratic factors as 2(n-pD)(n+pD), and positivity of the cofactor fixes the oracle orientation. The root is the canonical real inverse square root, with no assumed sampler or approximation. The CTE wrapper composes deterministic sign execution with the algebraic-root specification. Independent clients check arbitrary framing, the exact real bias, and a rational oracle sign.

## Occil.Constants.goldenFamily

Accepted `SampLib.GoldenFamily.goldenFamily_distSpec`, SHA-256 `2be70c1c078f1740373ad6d607ceb8aa4c304002f838e0936fbe6bbc812e6216`.

The canonical shape is (m+sqrt(m^2+4*ell))/2. Its reciprocal satisfies ell*p^2+m*p=1 and lies strictly inside the unit interval. A single quadratic factorization and positive-cofactor argument on the reachable unit-interval domain prove the concrete oracle. Finite independent root repetitions yield the explicit shape^(-k) law. Independent clients instantiate both signed families, frame arbitrary resources, check the negative-power identity, and test zero repetitions with infinite off-support credit.

## Occil.FactoryExtra.offsetRace

Accepted `SampLib.OffsetRace.offsetRace_distSpec`, SHA-256 `61e729ba2100e7e5095be24946a0f6b504cc4f49e5773f3a847004987961c789`.

Each callback partitions a common uniform rank into certain success, an input coin, and certain failure. The expectation sums interval widths using normalized Bernoulli credits. Racing the two affine callbacks cancels the positive common normalization and gives (x/y+q)/(a/b+p+x/y+q). The program proof literally follows the three callback cases and invokes BernoulliRace. Independent callers retain arbitrary resources and cover zero offsets with both opposite deterministic inputs, two certain inputs, and nonzero unequal rational offsets.

## Occil.FactoryExtra.logOverAffine

Accepted `SampLib.LogOverAffine.logOverAffine_distSpec`, SHA-256 `f61d45f51022be3a4f035bdc150752760b593b686a8ee0c104d2f13cf0d8f39a`.

The reciprocal-affine coin is strictly positive and supplies the geometric reciprocal-count construction. The existing logarithmic expectation and reciprocal substitution identify log(a/b+p)/(a/b+p). The program proof calls the inner geometric sampler, returns false at count zero, and otherwise invokes the rational coin. Independent clients frame arbitrary resources and test the zero logarithmic endpoint with infinite success credit.

## Shared support

All support was independently read. SamplerStep applies the same kernel-checked pure context rule as upstream twp_pure while preserving a symbolic reduct; independent callers exercise both nested-context beta reduction and recursive beta reduction. It introduces no new axioms or proof search. BernoulliRetry and FactorySyntax remain frozen reviewed support. GoldenFamily derives its canonical radical bounds and quadratic identity separately from program logic. AlgebraicConstants and IntegerSign remain the frozen exact-root and deterministic-sign bridges.

The immutable caller is `agent-docs/reviews/ExpansionFactoriesBatch004Callers.lean`, SHA-256 `6186f2484777b86cf568c162050940e7a481e7ae17b88efd0714dea8747bbd00`.
