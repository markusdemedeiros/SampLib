# Factory expansion review: batch 005

Reviewer: `/root/expand_review_factories`.

All three modules passed independent targeted builds without warnings. The immutable caller compiles warning-free, exercises arbitrary resource frames and boundary/infinite-credit cases, and prints exactly the three standard axioms for all 10 inspected theorems.

## Occil.expMinusFactory

Accepted `SampLib.ExpMinusFactory.expMinusFactory_distSpec`, SHA-256 `9a5bd78d1ab4ecea97f7df2a43d003a2d4f379dc429dbea48e8f90d5375874ab`.

The scalar first-step flip mass is the FTC identity integral_0^x p*exp(-p*y)=1-exp(-p*x). BernoulliMixture lifts it to arbitrary parity continuation credits, and a separate continuation-mass bound supplies termination credit. After the first uniform, all later thresholds lie below a strict cap B<1, with amplification 1/B. The CTE proof follows the uniform comparison, callback, parity change, and explicit retry split. A compact structural recursive AST is definitionally checked against the actual source and preserves arbitrary callback free variables. Independent clients frame arbitrary resources, identify the exact exponential bias, and check deterministic input zero with infinite off-support credit.

## Occil.FactoryExtra.expTimesComplement

Accepted `SampLib.ExpTimesComplement.expTimesComplement_distSpec`, SHA-256 `9eb446cec88c694d607c793e0ebe3d8e99386dd638a4f9665700b8d84ea318a8`.

The success probability at positive count and threshold x is (1-p)*exp(p*x). A scalar FTC identity identifies the first-step mixture, and BernoulliMixture lifts it without finite-credit assumptions. The special initial count zero is handled separately before the strict first-uniform cap funds tail termination. The program proof follows the input callback, count test, uniform ordering, and retry split; equality in the ordering is handled by the actual non-strict continuation kernel. Independent clients preserve arbitrary resources and test both deterministic input endpoints with infinite off-support credits.

## Occil.FactoryExtra.reciprocalExpAffine

Accepted `SampLib.ReciprocalExpAffine.reciprocalExpAffine_distSpec`, SHA-256 `041d07ff18efd96b35946037be8fd533818fd33c029f091d40792e2567ec687c`.

The verified rational-exponential coin is passed as the actual callback to reciprocalAffine. A finite reciprocal identity identifies the explicit target probability, while program logic is callback execution followed by the verified outer factory. The parameter domain matches the runtime reciprocal guard and rational-exponential guard. Independent clients frame arbitrary resources and check x=0 at the minimal and a larger affine offset.

## Shared support

All support was independently read. ExponentialFactory isolates a general FTC identity, scalar decay and growth kernels, and strict-cap amplification; the input endpoints require no division by p. BernoulliMixture remains the frozen normalized-measure bridge to arbitrary ENNReal credits. WeightedAmplification is separately reviewed foundation support for future multi-call recursive proofs: finite down-induction on an amplification exponent reaches contradictory owned credit using t>=1; the inductive hypothesis is boxed using only the persistent step assumption, never duplicated linear resources. Independent caller tests retain an arbitrary frame and instantiate infinite initial credit; the theorem has only the standard three axioms. It is not counted as a sampler.

The immutable caller is `agent-docs/reviews/ExpansionFactoriesBatch005Callers.lean`, SHA-256 `9cce976294534c410645babf4d204149b185156fb2074598217ca3a1152f5d5a`.
