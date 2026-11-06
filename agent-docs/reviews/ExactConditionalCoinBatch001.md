# Exact conditional sampler review, batch 001

Reviewer: `/root/review_exact_b`. Accepted core theorem
`SampLib.LatentReal.Coin.coin_programSpec`, SHA-256 `58a3c01266e12ada888393ca65db7de4686252968feccdecb9107bfc23b9d714`.

Domain: Any owned deferred real model with measurable observation errors and a valid source observation protocol. Every finite real source value is allowed, including arbitrary atoms and values outside the unit interval; the conditional output bias is clamp(value,0,1). The same source ownership, refined posterior and arbitrary measurable output/world ENNReal credit are retained. Repeated trials keep their common latent dependency.

## Full conditional law

The target is a conditional coin PROGRAM specification, not a marginal Bernoulli
law at the average source value. Each call allocates a fresh independent deferred
uniform and compares it with the original source in their full product world.
The uniform threshold identity is applied pointwise to the source value, including
clamping below0 or above1; Tonelli gives arbitrary joint output/source credit.
A fresh nonatomic uniform is almost surely distinct from EVERY measurable source
value, even an atomic one. Thus the shared-world less theorem supplies termination
without a source atomlessness or grid-avoidance hypothesis.

The actual comparison threads one combined ownership. At return, its full product
posterior is retained long enough to integrate out the unused fresh uniform;
only then is its resource discarded. The original source ownership and its actual
refined state remain. This preserves dependence in later calls. Source opening
and unit-callback syntax are certified separately, preserving named variables.
No desired concrete coin law or whole sampler correctness appears in the premises:
the source oracle is an independent compositional input contract.

## Independent client and validation

The independent client executes the ACTUAL Occil.PSRN.coin source twice on the
SAME source handle. It retains arbitrary joint H(firstbit,secondbit,world), source
ownership/refinement and an unrelated Iris frame. Its initial budget is the
nested conditional Bernoulli kernel, with no marginal-independence shortcut.
The generic structural client normalizes only a symbolic locally closed program
leaf and compiles at default heartbeats.

Concrete instantiations use the same cached uniform source on both trials and
exact atomic rational sources, including values outside[0,1]. Infinity is tested.
A separate formal calculation shows both-true kernel p² and, for uniform latent p,
its expectation1/3. This distinguishes the retained dependency from two independent
marginal fair coins. Impossible outputs at clamped values-1 and2 contribute zero
even when their requested continuation credit is infinite.

Independent targeted build, caller and conditional_coin exact-head/noncircular
signature audit all pass warning-free. The auditor instantiates the program's
source lambda and checks the actual Occil.PSRN.coin application head. Both public
program/callback specs, threshold expectation, AE distinctness, independent
repeated client and1/3 moment have only propext, Classical.choice and Quot.sound
axioms. ExactConditionalCoinBatch001.log retains commands and outputs. The immutable
receipt binds all local support, independent caller and clutch06a7b3e context.
