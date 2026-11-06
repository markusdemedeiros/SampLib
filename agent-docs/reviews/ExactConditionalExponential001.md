# Independent conditional exponential support review

Reviewer: `/root/review_exact_b`. Supporting interface review only; no new sampler counted.
Reviewed `SampLib.LatentReal.CoinExponential.exponential_programSpec` and
`exponential_coinSpec`, with full mathematics and actual unchanged-source loop.

- `SampLib/LatentCoinSpec.lean`: `06d0ed0f744c9a7f75a64e3f22d9e636b1611aa88719f6264ca90952e92631a5`.
- `SampLib/LatentExponentialKernel.lean`: `80d1eb0ae792529c337244fb880350a7d3244e611df9f76055004685b4d3b512`.
- `SampLib/LatentCoinExponential.lean`: `509b027d078dc5dfd5a57130742821c894d5dac03b3eb1aa02684e52d6f1527b`.
- `SampLib/LatentCoinConstants.lean`: `944d08cf386c3387401d59c0084dc30921687191b9ccb2f19e3a77d83f615209`.

The exponential conservation identity is applied at each latent point before
Tonelli exchanges joint integrals. Arbitrary measurable G(bit,latent), including
infinite values and zero-weight infinity, remains in the continuation kernel.
The first fresh uniform selects a strict cap below one; one amplification factor
then applies uniformly to every latent bias in the unit interval. Input bias
atoms at zero or one need no continuity, floor, or atomlessness hypothesis.
The actual loop threads source ownership and its refined posterior through each
input callback, feeds that state to recursion and weakens only the refinement
relation on return. Source callbacks are structurally inserted without named
variable capture. The callback specialization uses the same protocol.

Independent targeted build and caller fixture pass warning-free; log is
ExactConditionalExponential001.log. The fixture retains arbitrary unrelated R
and joint G through the actual expMinusFactory term. Concrete actual constant
input callbacks instantiate both atomic input endpoints and infinity; an
impossible output with infinite requested credit contributes exactly zero.
Public program/callback specs, expectation identity and independent caller use
only propext, Classical.choice and Quot.sound. The caller hash and source hashes
can be included in the transitive snapshot of any later concrete sampler review.
