# Expansion discrete review: immutable batch 005

Reviewer: `/root/expand_review_discrete`. Three core and two derived samplers.

## `Occil.DiscreteExtra.compoundPoisson` — accepted (core)

Public specification: `SampLib.CompoundPoisson.compoundPoisson_distSpec`.

Source SHA-256: `6b28cdaf07f34276bf5a5ce187e21b623a51111ea5ab1cf01a941d426af9243d`.

The independent target is a Poisson mixture of finite sums of independent signed jumps. A finite product-map law supplies the accumulator expectation; the main expectation conditions on the independent Poisson count. The CTE loop is natural induction and one abstract callback call per jump. Tests explicitly use negative deterministic jumps, a negative accumulated total, zero Poisson rate, infinite credits and resource framing. A generic caller specializes the latent type to integers with jump=id, ensuring the theorem covers arbitrary signed jump laws.

## `Occil.DiscreteExtra.skellam` — accepted (core)

Public specification: `SampLib.Skellam.skellam_distSpec`.

Source SHA-256: `f771c2542fc5c26f3b1aadf369ef43a33b1f49b2b3612d1a0e92a5f3b90ae9c8`.

The canonical signed difference of two independent Poisson counts is a measurable image of their product law. The central expectation is the standard map/product integral, and the program logic consists of the two verified Poisson calls and subtraction. Independent tests check both rates zero, a zero left rate producing a nonpositive integer law, infinite credit and resource framing.

## `Occil.DiscreteExtra.neymanTypeA` — accepted (derived)

Public specification: `SampLib.NeymanTypeA.neymanTypeA_distSpec`.

Source SHA-256: `9ff44093c4c6e41368237eb8f17c9d2608fd7d1d8caa91d302034d60e8cd76eb`.

A concrete composition of CompoundPoisson with a verified Poisson cluster callback. Both rates include zero. The independent target is the standard Poisson-cluster law, and the proof transparently constructs the callback specification and delegates to the signed compound theorem. Zero count-rate and generic framed clients are independently checked.

## `Occil.DiscreteExtra.polyaAeppli` — accepted (derived)

Public specification: `SampLib.PolyaAeppli.polyaAeppli_distSpec`.

Source SHA-256: `b6427c85b7e18d3af788c8948805d57233e78ff4da5ebd07099488cfd944763a`.

A concrete composition of CompoundPoisson with a positive-geometric jump callback. The target uses jump size n+1, making the support convention explicit. The callback uses a fresh rational coin at every geometric trial. Tests check zero Poisson rate and the success-probability-one endpoint, plus generic framing.

## `Occil.DiscreteExtra.zeroTruncatedPoisson` — accepted (core)

Public specification: `SampLib.ZeroTruncatedPoisson.zeroTruncatedPoisson_distSpec`.

Source SHA-256: `bc94248df598d4001371d7fb9eaae8134b2e0a3ec53d25a7403e2af784484fbd`.

The independent target is the canonical Poisson law conditioned on positive counts. A positive singleton at one proves the acceptance mass is nonzero; the existing normalized Rejection expectation supplies the sole retry budget identity. The CTE guard/draw/zero-retry proof uses the established amplification idiom. Tests check zero atom mass, infinite continuation credit only at the excluded zero output, constant infinite expectation and framed clients.

## Validation

Independent gated five-module build passed without warnings (4259 jobs). Working and immutable copied callers compile without warnings. Public specifications and central mathematical lemmas depend only on propext, Classical.choice and Quot.sound. Source formatting and whitespace checks pass. All laws are normalized probability measures with typed signed-integer encoders where appropriate. Continuations range over arbitrary measurable ENNReal values, including infinity. Derived specifications are categorized explicitly; no additional core algorithm is claimed for them.
