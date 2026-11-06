# Expansion discrete review: immutable batch 003

Reviewer: `/root/expand_review_discrete`. Five accepted core samplers.

## `Occil.Weighted.moduloReduction` — accepted (core)

Public specification: `SampLib.WordReductions.moduloReduction_distSpec`.

Source SHA-256: `4e1627c09bc4e85a0c7a837be2c29d001e62434253ac10fdf3f2b0abb02fab6a`.

The canonical finite image of a uniform binary word under remainder, with exact preimage-cardinality singleton masses. This is explicitly the generally biased finite law. Tests distinguish its masses from multiply-shift at target5/word8, cover a target larger than the source, zero bits, infinite off-image credit, and framed clients.

## `Occil.Weighted.multiplyShift` — accepted (core)

Public specification: `SampLib.WordReductions.multiplyShift_distSpec`.

Source SHA-256: `4e1627c09bc4e85a0c7a837be2c29d001e62434253ac10fdf3f2b0abb02fab6a`.

The canonical finite image under floor(word*target/width), with exact preimage-cardinality singleton masses. No false uniformity claim is made. Tests distinguish target5/word8 masses from modulo reduction and show the missing label2 for target6/word4; zero bits, infinity, and framing are checked.

## `Occil.WeightedVariants.sequentialCoins` — accepted (core)

Public specification: `SampLib.SequentialCoins.sequentialCoins_distSpec`.

Source SHA-256: `fb7cccce8ce4162d8f839e3cef195414f2d2abed72f6f39e10d8cc63237d08b4`.

Conditional renormalization of the remaining categorical weights is the central mathematical identity. The supported-spec continuation supplies positive suffix mass after an actual failed coin; following reviewer feedback the impossible zero-suffix branch was removed from the CTE proof. Symbolic execution is list induction with ordinary continuations. Tests check [0,2,0], infinite credit away from its sole positive label, and arbitrary framed resources.

## `Occil.DiscreteExtra.binomialHalfBits` — accepted (core)

Public specification: `SampLib.BinomialHalfBits.binomialHalfBits_distSpec`.

Source SHA-256: `97ac81abdbfee3148ab6ad7c554071abf9dc0936db8e2bdb408f787908fea4cf`.

Even/odd uniform binary-word ranks identify their digit sums with the canonical fair-binomial recurrence. Deterministic power and digit-count loops are separately verified, while the main sampler composes their specifications. Tests check the zero-trial Dirac law and the full two-trial arbitrary-ENNReal expectation (F0+F1+F1+F2)/4, including infinite values and resource framing.

## `Occil.poissonOne` — accepted (core)

Public specification: `SampLib.PoissonOne.poissonOne_distSpec`.

Source SHA-256: `be9f7c42e774e57f5a2a2429b21679eaf2ea3b7fdb23c721b65b0176fc5b1f97`.

The previously reviewed independent tree law is identified with Mathlib Poisson(1). A single rank-kernel expectation combines absorption and the auxiliary size-minus-boundary termination potential; expected auxiliary credit contracts at size>=2. CTE uses one uniform rank followed by obvious stop/up/down cases, fixed-credit amplification, and an initial literal step. Infinite continuation values never enter real arithmetic. Independent clients check framing, infinite expectation, and the canonical zero atom exp(-1).

## Supporting mathematics

FiniteImage gives a normalized uniform-image measure and exact cardinality PMFs. WeightedValidation verifies natural-weight validation and integer-list summation. IntegerPower verifies the actual multiplication accumulator for all integer bases and natural exponents. BinaryDigits supplies even/odd population-count identities and paired finite sums.

AcceptedProposal gives the independent normalized density accepted from a proposal probability measure: its acceptance/rejection masses sum to one, and retry factor 1+acceptance mass contracts error credit. It handles arbitrary measurable ENNReal continuations and acceptance one. Tests check acceptance zero mass and the certain-acceptance law equal to the original measure. No arbitrary continuation is converted to real arithmetic.

Support hashes:

- `SampLib.Distributions.FiniteImage`: `328b7c1bb979e28c2b5e164f437f5dec0bae5ffa97c2ff0843b4c8e12ae254cf`.
- `SampLib.WeightedValidation`: `6d06663d8a9c838913038370a3ffdccf145a2e7ebc835bdca6469a6f64ba8866`.
- `SampLib.IntegerPower`: `5e738a4f8fcb4d9a2fb783392e96eee4791009f3b34ee1f9e813ec754a1ff0d8`.
- `SampLib.Distributions.BinaryDigits`: `0f0566ca8ad3e73231335e9b5ceff2f8a20853e0f08caab9ad8891697e03fc8e`.
- `SampLib.Distributions.AcceptedProposal`: `50b48e4e04a8c984c230f5301ca090c7088abbb4f090084ec6d9dc497583a803`.

## Validation

Independent gated module builds passed without warnings (4263 jobs). Working and immutable copied callers compile without warnings. Public specifications, central mathematical lemmas, and support lemmas printed by the caller depend only on propext, Classical.choice and Quot.sound. Source formatting and whitespace were independently inspected. All target measures are normalized, and all specifications admit arbitrary measurable ENNReal credits.
