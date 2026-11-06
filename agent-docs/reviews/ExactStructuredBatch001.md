# Exact structured sampler review, batch 001

Reviewer: `/root/review_exact_b`. Both entries passed source/specification review,
independent targeted builds, structural public-spec audits and the independently
compiled [caller fixture](ExactStructuredBatch001Callers.lean). All printed axioms
are exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Mathematical and program-logic review

`markovStep` uses verified list lookup and categorical sampling. The public theorem
requires only positive row totals and a valid selected index; no square-matrix
assumption is smuggled into this one-step law. Its CTE proof is straight-line
lookup followed by the verified weighted draw, with normalization supplied by the
existing categorical expectation theorem. This is existing support promoted to
an independently reviewed interface, not newly invented sampling mathematics.

`shapeRejection` is a derived wrapper. Its three binder steps and explicit named
closedness normalization expose generic rejection. The latter's conditional-law
expectation inequality and termination amplification supply the substantive proof;
no desired-law premise about the concrete wrapper is present. This is composition,
so duplicating the generic preservation argument would obscure its purpose.

## Caller and boundary coverage

The fixture exercises arbitrary measurable ENNReal credits and an unrelated linear
Iris resource through both public continuation rules. It checks first and last
valid indices of a rectangular matrix containing zero weights and a singleton
row. A closed always-accepting predicate exercises acceptance mass one without a
uniform-integer assumption. The theorem domains retain arbitrary masks and the
current ghost-state context. Infinite credits are not converted to reals.

## Exact accepted artifacts

- `SampLib.MarkovChain.markovStep_distSpec` in `SampLib.Samplers.MarkovChain`: `325114027310e598ac3353f76dd5d3abd357f3c3e135e01b1ec9e2b197a74b89`. Classification: support. Domain: Any finite list of positive-total nonnegative integer rows and any valid row index; rectangular matrices and zero weights are permitted.
- `SampLib.ShapeRejection.shapeRejection_distSpec` in `SampLib.Samplers.ShapeRejection`: `c5522cc5bd5d4d37f505fdaa32c935bc2d2274ac23ea86b856e9648d5a15ed55`. Classification: derived. Domain: Any probability proposal on a measurable output type, measurable positive-mass acceptance set (including mass one), a proposal IsDistSpec and a correct deterministic membership-test specification.

The immutable JSON receipt pins every project-local dependency and the current
`06a7b3e2` dependency context. Historical review receipts were not modified.
