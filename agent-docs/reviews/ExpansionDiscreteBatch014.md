# Expansion discrete review: immutable batch 014

Reviewer: `/root/expand_review_discrete`. Three accepted core samplers.

## `Occil.DiscreteExtra.discreteLaplace` — accepted (core)

Public specification: `SampLib.DiscreteLaplace.discreteLaplace_distSpec`.

Source SHA-256: `cfba7e6140bc8a0e11b646fe6e830e80961a927c7fa3f5aff65c908fe1dbc55d`.

The independent standard two-sided geometric law has atom coefficient(s,t)*exp(-s/t)^natAbs(z). Its analytic residue/quotient reindexing, reflected atoms, normalization and nonunit rates were independently reviewed and tested in Batch012. New continuation mathematics moves the exponential remainder test before independent geometric whole/sign draws and supplies one accepted-proposal conservation inequality for both retry sites. Main CTE follows that source order and returns the signed integer quotient or retries. Independent actual callers frame arbitrary signed-output credits and resources at generic rates, and explicitly instantiate rates2/3 and3/2. A negative-zero test with nonzero whole part confirms rejection happens after division; the positive sign retains F(0).

## `Occil.WeightedVariants.floatingMultiply` — accepted (core)

Public specification: `SampLib.FloatingMultiply.floatingMultiply_distSpec`.

Source SHA-256: `b6775a103c59a6c33dc6c4681787ea4a7d8c997bffd85032c7d336bb030ed86d`.

The exact biased finite law counts source-word preimages under independently specified nearest/even binary rounding followed by modulus division. The mathematical rounding API gives quantum spacing, exact-fit and exact-divisible behavior, even midpoint ties and half-quantum error bounds with unbounded exponents. Main CTE composes deterministic exponentiation, a verified uniform binary word and deterministic rounding. Independent tests distinguish the precision3 map[0,0,1,2,2,3,4,4] from the precision6 unrounded map[0,0,1,1,2,3,3,4] for n5/width8, check masses1/4 and1/8 and infinite credit off the finite image, and verify midpoint20→16 versus28→32. Weak-language framed bit-length/rounding clients, zero-precision helper failure, zero-bit positive-precision singleton and arbitrary-resource main callers pass. No hardware IEEE or continuous-uniform claim is made.

## `Occil.fastDiceRoller` — accepted (core)

Public specification: `SampLib.FastDiceRoller.fastDiceRoller_distSpec`.

Source SHA-256: `63a857ab1a5c083342b54deba9fc3d32e6ef7c367b78b48c400365b6e316907b`.

The public target is the independently normalized UniformInt law. Pointwise finite-horizon credits describe retained states; the bulk interval identity already accepted with FYKY in Batch013 bounds the initial state by uniform output credit plus an exponentially vanishing cutoff tail. This lower orientation emits the first n ranks and recycles the upper residue. Main CTE follows one bit at a time, derives contradiction from cutoff credit1, and removes the horizon with an arbitrary positive error budget. Independent callers frame arbitrary ENNReal continuations and resources, exercise non-power-of-two bounds3 and5, check infinite off-support credit and use the singleton theorem without UniformInt. No individual retained state is assumed to have a uniform output law.

## Supporting mathematics and deterministic code

The canonical DiscreteLaplace law was accepted in Batch012; this receipt adds the actual program and its credit-order bridge. Tonelli moves the exponential test ahead of the independent whole/sign variables, while the rejected negative-zero case uses total coin mass one. The same accepted-proposal factor pays for both retries. All continuation values remain ENNReal.

BinaryRounding independently characterizes unbounded-exponent binary quantization and exact nearest/even ties, including overflow to the next binade. BitLength and RoundBinary are deterministic supporting programs with generic resource-frame clients and no UniformInt requirement. Their reusable ClosedExp instances replace routine opening/closing lemma forests. The exact invalid zero-precision helper failure is explicit; the sampler theorem does not claim the outer-valid zero-format corner succeeds. FiniteImage and the checked SamplerStep tactic were already independently accepted.

BitRecycler was accepted with actual FYKY in Batch013, including source review and independent bulk, horizon, cutoff and infinite-credit tests. Its lower orientation now supports the actual FastDiceRoller consumer; the shared helper is not counted again.

Support hashes:

- `SampLib.Distributions.DiscreteLaplace`: `7030d9a2dbe32b43f8cc5e4dcd1abe032e9958fe6a07e8247556053642bafe13`.
- `SampLib.Distributions.DiscreteLaplaceCredits`: `aaa4b8b73f2a1d404b55237b76dc338c396253d33088e73d6eccbd21a88c94e2`.
- `SampLib.Distributions.BinaryRounding`: `0d4f0f9cda41c5b3314618d3cf913f48efd321546abe7a1a2fc194b270490729`.
- `SampLib.BitLength`: `a8aed177c3ca6dc83000c60570b7b38e284aec63560cc62dd6ff33a99c16a685`.
- `SampLib.RoundBinary`: `f7eca5e37fed462f486817a0fe2bd758c0094e82c3b7140f2e0b679bf8768dab`.
- `SampLib.Distributions.FiniteImage`: `328b7c1bb979e28c2b5e164f437f5dec0bae5ffa97c2ff0843b4c8e12ae254cf`.
- `SampLib.SamplerStep`: `a3e143551b2719b11170456de08e0c193059c00b6b8dafabe3c747c03eb52335`.
- `SampLib.Distributions.BitRecycler`: `2a2d0ac5f23a634c9dedfb6e13c9dca85a7d4c862bb97a447ba3e0aecacfce80`.

## Validation

Independent gated module builds passed without warnings. Working and immutable copied clients compile without warnings. Public specs, central expectation lemmas, analytic identification, exact singleton proportions, accepted-proposal conservation and support lemmas depend only on propext, Classical.choice and Quot.sound. Source widths and whitespace pass. All targets are normalized with typed integer encoders, arbitrary measurable ENNReal credits and unrelated resources retained through calls.
