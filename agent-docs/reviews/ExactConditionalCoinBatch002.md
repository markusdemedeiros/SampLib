# Independent conditional sampler review, batch 002

Reviewer: `/root/review_exact_b`. Accepted core theorem
`SampLib.LatentReal.ExpMinusCoin.expMinusCoin_programSpec`, SHA-256 `93709efaaa4747f79aa838f46d8a3748117406278822da69a6d47a7540af69cb`.

Domain: An owned deferred real oracle with measurable errors, AE nonnegative values, and either global AE avoidance of the integer grid or global AE first-observation error zero. The conditional bias is exp(-value) almost everywhere. The same source ownership and admissibility invariant are retained with arbitrary measurable joint output/world ENNReal credit, including infinity.

The actual source reads its integer floor, constructs the fractional residual with
rational subtraction, and combines the integer expMinusRational coin with the
conditional expMinusFactory of the residual coin. The mathematical kernel first
uses the floor decomposition pointwise in the original latent world, then
integrates the full output/world credit. No marginal-average substitution occurs.
The globally total bias exp(-max(0,value)) agrees with exp(-value) almost everywhere
on the retained domain.

Termination of floor is substantive. Grid avoidance is a sufficient domain;
shrinking intervals alone are insufficient at integer atoms. The separate new
exact-floor rule proves that AE zero error at the first observation forces equal
endpoints and immediate resolution. This admits exact rational zero and other
exact integer oracles without altering the accepted grid-null floor theorem.
The public domain is a GLOBAL disjunction of these two alternatives, not a
pointwise mixture of them. In particular an all-ones digit representation of one
with intervals approaching from below is not admitted merely by nonnegativity.
The invariant is transported under posterior absolute continuity and retained
with physical source ownership through every operation.

Review covered the exact-floor lemma, floor-split expectation, literal source
opening, straight-line main CTE, callback wrapper and admissibility transport.
The only source correctness assumptions describe the independent input oracle.
No desired expMinusCoin or whole conditional output-law premise is assumed.

Independent callers execute the actual program twice on one source, preserving
arbitrary joint H(firstbit,secondbit,world), refined source ownership and an
unrelated Iris frame. Concrete exact rational zero proves the actual true result
with exactly its continuation budget; impossible false infinity costs zero.
A rational half exercises the grid-avoidance alternative. Infinite credit and
the distinction between excluded zero-grid avoidance and admitted exact-zero
error are checked explicitly. Targeted build, client and conditional exact-head/
noncircular-premise audit pass warning-free. Printed main, kernel, exact-floor and
client axiom checks use only propext, Classical.choice and Quot.sound; the source
correspondence uses only propext. The immutable receipt binds exact source/support,
caller and dependency context. ExactConditionalCoinBatch002.log retains commands
and output.
