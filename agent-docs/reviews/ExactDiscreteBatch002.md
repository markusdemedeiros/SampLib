# Exact discrete sampler review, batch 002

Reviewer: `/root/review_exact_b`. Accepted public interfaces:

- `SampLib.InversePolya.inversePolya_distSpec`: SHA-256 `4a958247cccdd2bd0ab7a8a9ecb5dff8211f41370b962e5d4f9c9b6e7b1a3dff`; core. All natural success counts, unmarked counts and reinforcements, with positive marked count; includes zero requested successes, no unmarked balls and zero reinforcement. No finite-mean assumption.
- `SampLib.BetaNegativeBinomial.betaNegativeBinomial_distSpec`: SHA-256 `d0f9c60b6e956b7bd0bd0434b8d225e1ef47d211248c6956998cef2b0077e85e`; derived. All natural success counts and positive rational beta shapes represented by arbitrary positive numerator/denominator pairs, including unreduced and subunit shapes.
- `SampLib.WaringYule.waringYule_distSpec`: SHA-256 `97194f39e9d8687e3fe91274928dcf380c6b00eae66f058de9b9927f57bc3cec`; derived. Positive rational alpha and beta, including subunit and unreduced shapes; zero-based failures before the first marked draw.
- `SampLib.YuleSimon.yuleSimon_distSpec`: SHA-256 `a9f5d465d184ab070e14acddc5a0a3625f3d64f2bd33a154e109c7f8db2db22e`; derived. Any positive rational shape, including subunit and unreduced shapes; positive integer output, obtained by adding one to the beta-geometric failure count.

## Mathematical law and termination

The inverse urn law is defined independently as the finite composition of
first-marked waiting laws. Each waiting law is normalized: its marked hazard
is bounded below by a positive multiple of the harmonic sequence, so the
surviving failure product tends to zero. This argument allows infinite mean
waiting time and requires no geometric contraction.

The first-draw expectation separates an immediate marked draw from a reinforced
failure, retaining arbitrary nonnegative extended-real continuation credit.
Outer induction on the requested successes supplies the marked continuation;
the indexed finite-horizon absorbing-chain rule discharges the failure loop.
The canonical rising-product singleton mass is proved separately by the urn
recurrence and Pascal/rising identities. It identifies the beta-negative-binomial
specialization, its one-success Waring law and positive-shift Yule–Simon law.
All arguments retain zero reinforcement and zero unmarked population where stated.

## Actual source and CTE

The actual inversePolya source is symbolically executed through its guard and
rational coin. The two Boolean branches invoke the respective failure
continuation and lower-success induction hypothesis, with explicit natural
state-update identities. Mathematical credit identities and survival are named
separately. Wrappers clear rational shape denominators, specialize one success,
or add one to the returned integer. None assumes its own concrete sampler law.
The source implementation is unchanged.

## Independent validation

Each of the four modules was independently targeted-built. Exact-head and
noncircular-premise audits report SPEC_OK for all four actual source terms.
The independent caller fixture retains an arbitrary Iris resource and arbitrary
ENNReal credit through every public interface. It exercises zero requested
successes and infinity, plus canonical singleton masses for unreduced subunit
shapes, zero reinforcement, no unmarked balls, and Yule's excluded zero output.
These checks include both heavy-tail and deterministic boundary regimes.

All caller checks and builds are warning-free. The four public interfaces,
harmonic absorption and canonical mass theorem use only propext,
Classical.choice and Quot.sound. Commands and outputs are preserved in
ExactDiscreteBatch002.log. The immutable receipt binds exact local source
closures, independent caller and the current clutch06a7b3e dependency context.
