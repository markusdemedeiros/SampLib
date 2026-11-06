# Exact structured sampler review, batch 006

Reviewer: `/root/review_exact_b`. Accepted derived theorem
`SampLib.PSRNPowerCoin.powerCoin_distSpec`, SHA-256 `3ec10c19c5a2c08ffe09db4c401c04ee246e104d74fb52c78168af5e5deb8ba4`.

Domain: Every nonnegative natural numerator and positive natural denominator, with any input Bernoulli probability in the closed unit interval and a correctly specified ordinary input-coin callback. Includes p=0, p=1, exponent zero with0^0=1, integral and fractional exponents, and arbitrary ENNReal continuation credits.

The independent rational-power target uses quotient/remainder factorization:
whole power times residual fractional power equals the desired power, including
base zero and exponent zero. The existing CoinProduct expectation transfers
arbitrary ENNReal continuation credit through the whole-result short circuit.
That is the single mathematical expectation lemma in the new proof. The zero
residual's credit is exactly the true branch's credit, with no0×infinity mistake.

The proof executes the actual Occil.PSRN.powerCoin source, validates its denominator,
caches the actual iterateCoin result, returns false on failure, and either returns
true for zero residual or executes the existing fractionalPowerCoin engine.
Program logic consists of these straight-line named specification calls and
branches. Actual source syntax is preserved, and no correctness premise about
the desired concrete powerCoin term is assumed. The abstract input coin's law
is an independent callback contract, not an averaged latent-coin replacement.

Independent targeted build, exact-head/noncircular audit and caller pass
warning-free. The client retains arbitrary F and an unrelated Iris resource.
Actual always-false/always-true callbacks exercise0^0, mixed whole/fractional
powers, pure fractional powers, exact integral powers, both input endpoints,
infinity and infinity requested on impossible outputs. Pure endpoint identities
are checked as well. Public spec, expectation, power factorization and independent
client axiom checks use only propext, Classical.choice and Quot.sound.
ExactStructuredBatch006.log retains commands and outputs. The immutable receipt
binds full local support, independent caller and clutch06a7b3e dependency context.
