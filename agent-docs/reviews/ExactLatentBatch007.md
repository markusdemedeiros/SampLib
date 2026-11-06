# Independent exponential rate-interface review, batch 007

Reviewer: `/root/review_exact_b`. Accepted derived theorems:

- `SampLib.PSRNExponential.newExponential_latentDistSpec`, SHA-256 `0dc2498969045cca81529efd13722e118231bd8eddfdf1c74835c92f60d2f868`.
- `SampLib.PSRNExponential.newExponentialLogRate_latentDistSpec`, SHA-256 `5ac652646901aae0e1f2db97cac6ad4ce1bfac0cdda7c3280156a68a98165f60`.
- `SampLib.PSRNExponential.newExponentialUnknownRate_latentDistSpec`, SHA-256 `a9dad0f95000ba50ff9b442cbd9d218f571810e2f5e8aef1d402131801c45d40`.

The domains are exactly positive rational rates, positive logarithmic rates
log(x/y) with0<y<x, and unknown bias0<p<=1 supplied by an independent ordinary
coin contract. The unknown-bias implementation requires real ProbLang and its
UniformReal primitive; no such extra primitive is required for the two rational
factory interfaces. No desired constructor or oracle specification is a premise.

## Callback mathematics and source execution

The rational wrapper gives divisor d the exact negative-exponential rational
trial exp(-a/(b*d)). The logarithmic wrapper takes the actual y/x rational coin
to the1/d rational power; the real logarithm/rpow identity proves this equals
exp(-log(x/y)/d). The unknown-bias wrapper thins an actual p-coin by1/d and calls
the verified exponential factory, producing exp(-p/d). In every case the callback
contract is derived for ALL positive natural divisors used by the whole counter
and conditional fractional-digit constructor. The unknown input coin contract is
an independent reusable compositional assumption; no supplied correctness premise
mentions a whole exponential sampler.

Each original wrapper validates its concrete integer parameters where applicable,
then calls the already reviewed FromDecay source with that exact derived callback.
Named source-opening certificates preserve arbitrary callback free variables.
The main CTE is straight-line guard execution followed by the established base
constructor. Its returned source ownership is literally the whole/fraction
ownership for the chosen callback. The stronger represented theorem combines
this concrete constructor with the same proved actual observer. The common
canonical model-law theorem identifies Exp(rate); no new target law is postulated.

## Independent callers

The independent client constructs EACH actual wrapper and reads the SAME returned
closure twice, retaining both exact represented intervals, both enclosures,
refined source ownership, arbitrary joint F(whole,fraction) and an unrelated Iris
resource. Generic rational6->1, logarithmic0->7 and unknown5->2 queries exercise
shorter rereads and refinement. Concrete rational3/5 and logarithmic3/2 callers
exercise infinite credits; a fully proved actual always-true input coin instantiates
unknown p=1 with infinite credit. The excluded unknown p=0 case is not claimed:
its whole-part counter need not stop.

Final independent targeted build, caller and all three actual-head/noncircular
signature audits pass warning-free at default settings. All six weak/strong
public theorem checks and the generic repeated client use only propext,
Classical.choice and Quot.sound. ExactLatentBatch007.log retains commands/output.
The immutable receipt binds each exact local source/support closure, the separate
strong-forward module, independent caller and dependency context.
