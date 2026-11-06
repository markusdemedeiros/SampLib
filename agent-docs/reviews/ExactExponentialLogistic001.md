# Independent exponential-digit logistic source support review

Reviewer: `/root/review_exact_b`. Root-authored support independently reviewed;
no new sampler counted. Public `SampLib.ExponentialLogistic.digit_distSpec`,
production `SampLib/PSRNExponentialLogistic.lean`, SHA-256 `894362aef0fd6700cf266ca1facc47c51b3cc8f1e0d7ce1ce7cf70b7012fe551`.

The actual fair-selector source returns false on its first branch, true after
a successful decay call on the other branch, and retries after decay failure.
Its success probability is q/(1+q), not its complement. The existing signed
LogisticFactory expectation pays at most one-half retry mass and a fixed factor2,
for every q in the CLOSED unit interval and every ENNReal continuation.

The helper specifies precisely the actual callback at twice the supplied integer
denominator; the seen prefix argument is consumed and ignored by this particular
exponential law. Raw syntax inserts the arbitrary callback after binder closure,
and literal sourceTemplate correspondence plus named beta/opening entailments
connect this to the actual exponential constructor callback. The CTE loop is
straight-line fair selector, input callback, accept/return or funded retry.
No desired digit-sampler or exponential law is assumed as a whole-program premise.

Independent targeted build and client pass warning-free in
ExactExponentialLogistic001.log. The client preserves arbitrary F and unrelated
Iris frame, including infinity. ACTUAL constant false/true decay callbacks test
q0 and q1, negative ignored seen, zero and negative denominator arguments where
the callback contract permits them, and a null true output with infinite credit.
Source equality, loop/spec and independent callback/client proofs have only
propext, Classical.choice and Quot.sound axioms. Later concrete exponential
sampler acceptance must bind the full source closure and original source opening.
