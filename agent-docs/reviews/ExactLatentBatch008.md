# Independent gamma and Lindley review, batch 008

Reviewer: `/root/review_exact_b`. Accepted theorems:

- `SampLib.PSRNGammaInteger.newGammaInteger_latentDistSpec`, SHA-256 `e474d53afed7e53e0369a05e7877a4277abfb71b38cd2dfee43fe8e3c7ee8bf0`.
- `SampLib.PSRNGammaMixture.newGammaMixture_latentDistSpec`, SHA-256 `a2e19057e5eea01ccf88b50f8f94e36b462659b87b86e42005f6e66f964827a2`.
- `SampLib.PSRNLindley.newLindley_latentDistSpec`, SHA-256 `49cce8c840477a50245049031328ad4fe9bbb6830b369b8f6a9a481d5f3c1971`.

## Expectation and canonical laws

The mathematical convolution argument factors the common exponential out of the
gamma/exponential density product. What remains is the integrable power integral
from0 to x. Positive shape is sufficient, even below one; Gamma's recurrence
absorbs the denominator. This proves Gamma(shape,rate)+Exp(rate) is exactly
Gamma(shape+1,rate), in both source orders and for arbitrary ENNReal continuations.
The zero-fold analytic sum is separately Dirac0; it is never confused with the
actual integer-gamma source, which rejects shape zero.

The integer source has depth shape-1. Depth zero allocates ONE exponential;
each successor allocates a new exponential before recursing, and returns the
actual addition closure over their independent product worlds. The initial-law
induction therefore gives the canonical gamma shape, with no off-by-one or
empty-sum convention. Every observer retains all component caches exactly once.
The common product ownership is passed sequentially through addition, preserving
arbitrary F on the ENTIRE nested product, not just F of the observable sum.

The mixture source executes a rational selector and only the selected positive-
shape constructor. Its latent world is a DISJOINT SUM with the weighted prior;
selection refines to a positive-mass component. Supported coin execution excludes
the zero-weight branch at selector endpoints, even if F there is infinite.
The target law is the exact weighted sum of the two canonical gamma measures.
Lindley's selector a/(a+b) equals rate/(rate+1); expanding its shape-one/shape-two
gamma mixture gives the canonical density
rate^2/(rate+1)*(1+x)*exp(-rate*x) for x>=0 and zero below0. Normalization follows
from the proved probability mixture, rather than a supplied target-law premise.

## Actual source and program logic

Review covered the positive-shape convolution mathematics, nested product model,
actual recursive integer source and its observer, selected-component mixture
model/CTE, Lindley weight/density, concrete wrappers and literal source gateways.
The source's exponential-first evaluation order is preserved. Named syntax
opening entailments isolate recursive AST alignment. The main CTE follows the
ordinary exponential -> recursive gamma -> addition idiom, or selector -> chosen
gamma, and finally Lindley's concrete mixture call. Every independent base
constructor premise in the reusable Core rules is discharged in the public
statements using the already verified concrete rational exponential sampler.
No desired gamma/mixture/Lindley sampler law or oracle spec is assumed.

## Independent callers

The independent clients construct EACH actual source, then read the SAME returned
closure twice with arbitrary joint latent F and an unrelated Iris frame. Generic
integer and mixture clients quantify over every component coordinate, not only
the sum or selected observable. Cases include shapes1 and3, rates2/5 and5/2,
precision0, refinement and shorter rereads, both selector endpoints0/7 and7/7,
and infinite credits. The generic Lindley client retains its selector and all
chosen exponential coordinates. All eight printed public, canonical-law,
convolution-density and independent-client axiom checks use only propext,
Classical.choice and Quot.sound.

Final independent targeted builds, client and all three exact-head/noncircular
signature audits pass warning-free at default settings. ExactLatentBatch008.log
retains commands/output. This immutable receipt binds the exact source/support
closures, independent caller and dependency context.
