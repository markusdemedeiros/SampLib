# Independent shared-root support review

Reviewer: `/root/review_exact_b`. This is uncounted compositional support, not an
additional completed original sampler. Reviewed public interfaces include
`SampLib.LatentReal.Root.twp_observe`, `Root.representedOracleSpec`,
`Root.represented_viewSpec` and the actual constructor `Root.Program.twp_root`.
Exact source/support/context hashes are retained in ExactSharedRoot001.json.

The sufficient domain is explicit: degree>=2, AE nonnegative source value and AE
avoidance of EVERY nonnegative rational degree-th-power threshold. Absolute
continuity transports this domain through every actual source observation.
Atomlessness suffices but is not required. No theorem claims that a merely
shrinking oracle resolves comparisons against its own boundary atoms; an exact
rational-one source is formally shown outside this sufficient domain.

The actual observer constructs powers fixing the dyadic grid, expands an upper
bracket by doubling, then bisects a finite integer gap. The comparison callback
computes the exact integer numerator power, constructs its rational threshold
and invokes the independently verified shared-world Less protocol. Every query
consumes the SAME physical P and retains full latent-world F. No resampling or
independent-marginal assumption occurs.

Bracket termination charges one credit on a tail band of the positive function
1/(1+abs(sourceValue)). Finite source values make that band mass tend to zero,
without a global source bound or a finite runtime moment. The mathematical
expectation lemma simply adds this tail mass to arbitrary ENNReal F. At the
selected unresolved horizon the posterior owns a whole contradictory credit;
at success it keeps all F. Strict upper and weak lower power brackets then
identify both the enclosure and the EXACT dyadic floor cell after finite
integer bisection. Pointwise root/power monotonicity supplies the analytic bridge.

The polished main CTE now reads named begin -> two exact powers -> bracket ->
bisection -> return; all raw syntax and closure alignment lives in certified
source-stage helpers. Review included those helpers and literal original root
construction, shared source/root views, measurable model/errors and exact dyadic
representation. The canonical Rayleigh root-map and its Exp1-scale2 threshold
domain were separately read and checked; no concrete Rayleigh sampler is
counted by this support review.

The independent client executes the ACTUAL root constructor, observes that root,
then observes the ORIGINAL source handle under ONE P. It retains both exact
represented intervals, both enclosures, arbitrary whole-world F and an unrelated
Iris resource. A concrete shared uniform source/square-root instance is included.
Thus returning a fresh independent source or duplicating source ownership cannot
satisfy the tested interface. An explicit rational boundary exclusion is checked.
Final independent RootViews/RootLaw targets and caller pass warning-free at default
settings. All seven printed main, bracket, bisection, shared-view, canonical-law,
AE-domain and client axiom checks use only propext, Classical.choice and Quot.sound.
ExactSharedRoot001.log retains commands and output. Later concrete receipts must
still instantiate the domain and snapshot this closure.
