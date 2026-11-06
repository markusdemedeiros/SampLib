# Independent review of finite samplers

Reviewer: `/root/review_next_batch/review_finite_next`.

The source review follows `agent-docs/VerifyingSamplers.md`. The accompanying
`NextBatchFiniteCallers.lean` compiles independent framed clients, boundary laws,
infinite-credit examples, and axiom checks. Receipts bind the reviewed source and
its project-local import closure to those checks.

## Dice

Accepted `SampLib.Dice.dice_distSpec` at SHA-256
`7bf709bfb710432fd7c10c189b440aed08720281f747edb8ce7b5e47a2e4cee2`.

The target is the convolution of independent uniform dice on `1, …, sides`,
encoded as a natural-valued integer literal. It covers all natural trial counts
and positive sides, including zero dice and one-sided dice. The expectation lemma
is the product-measure/Fubini identity for the sum, valid for arbitrary ENNReal
credits. It does not assume finite continuation expectations. The product order
matches ProbLang's right-to-left evaluation: recursive rest, then current die.

The CTE proof is induction followed by deterministic execution, the recursive
specification, and the uniform-integer specification. No mathematical search or
algebra is hidden in symbolic execution. The public theorem has no assumed sampler
specification and is a small typed wrapper.

Independent checks passed: `lake build SampLib.Samplers.Dice`; caller compilation;
zero-dice law; deterministic one-sided law for every count; constant-infinite
credit; preservation of an arbitrary framed Iris resource; `git diff --check`.
Core, public theorem, and expectation lemma use only `propext`, `Classical.choice`,
and `Quot.sound`.

## Ordered sampling without replacement

Accepted `SampLib.SampleWithoutReplacement.sampleWithoutReplacement_distSpec` at SHA-256
`8fc52ead9f3d8383445ced90a5c4bb20eb47e1fcf96e3909f3ea8515df37b07b`.

The target is uniform over finite selections of remaining-list positions, with
cardinality `length.descFactorial k` and reciprocal falling-factorial singleton
mass. This independently characterizes uniform ordered position selections;
equal input values retain separate latent choices. All `0 ≤ k ≤ length` inputs
are covered, including zero draws from an empty list. The output encoder decodes
the chosen positions into the original entries.

The expectation lemma partitions the uniform selection space by its first
position and uses the equal tail cardinalities. A small rank adapter matches the
existing uniform-integer primitive. The deterministic removal lemma proves the
actual `removeAt` implementation. The main CTE proof then follows length check,
uniform position, removal, recursion, and cons, with no probabilistic reasoning
hidden in deterministic execution.

Independent module build and caller compilation passed without warnings. Checks
include the zero-draw point mass for every input, two distinct latent choices
when sampling both positions of `[x,x]`, constant-infinite credit on every valid
domain, and a framed public-specification client retaining arbitrary Iris
resources. The expectation, singleton law, core, and public theorem use only the
three standard axioms. Full-length selections are included in the quantified
valid-domain client and falling-factorial characterization.

## Sampling in input order

Accepted `SampLib.SampleInOrder.sampleInOrder_distSpec` at SHA-256
`aad71a14bb97ff122e111ba8b350870e7be701b0f4ef3c7e50a181f8bb278c9c`.

The target averages `List.sublistsLen k` over the binomial number of position
subsets. It covers every natural `k ≤ length`, including empty input with zero
draws and selection of the entire input. Duplicated values retain the
multiplicity of the position subsets that produce them. No countability or
measurable-space assumption on input values is required; the output-list
measurable space is discrete.

The central expectation lemma is Pascal's partition into subsets including or
excluding the first position. Its coefficient lemmas express the familiar
binomial ratios; all continuation credits remain ENNReal, with no finiteness
restriction. Symbolic execution follows one uniform-rank draw and the selected
recursive branch. The named local loop is definitionally the original program's
loop; there is no assumed callback specification or implementation replacement.

Independent clean build and compiled caller checks passed. Tests cover the zero
and full-selection point masses for arbitrary inputs, duplicate-entry input
`[x,x]` selecting one item (point mass at `[x]`), constant-infinite continuation
credit, and preservation of arbitrary framed Iris resources. Public theorem and
expectation use only the standard three axioms. Requested formatting, bounded
pure-step runs, and removal of an unnecessary direct mathlib import were addressed.

## Hypergeometric urn

Accepted `SampLib.Hypergeometric.hypergeometric_distSpec` at SHA-256
`22f6a190e8646bee92d8f68e1a974255049dbf479378d01ebe5e50316e9e436a`.

The target counts marked balls in a uniform ordered selection of distinct labelled
balls from the input urn. It is independently specified through the uniform
selection law, rather than through the sampler's own transition recurrence. The
expectation argument groups selections by the first ball's color and identifies
the resulting erased urns. It then assigns infinite credit to impossible colors;
zero probability times infinite credit is zero, so exhausted-color branches can
be discharged without restricting the domain.

The CTE proof is finite induction, one rational-coin specification, the selected
recursive branch, and an increment for marked draws. The valid domain is precisely
natural `n, ones, zeros` with `n ≤ ones + zeros`; this includes an empty zero-draw
urn, absent colors, and drawing the entire population. The typed result is the
natural marked count encoded as an integer literal.

Independent clean build, framed caller, infinite credit, zero-draw point mass,
empty urn, exhausted marked color, and full-population specification clients all
passed. The core, public theorem, grouping expectation, and impossible-color
credit adapter use only the three standard axioms.

## Pólya–Eggenberger urn

Accepted `SampLib.PolyaEggenberger.polyaEggenberger_distSpec` at SHA-256
`fc92d8cab94044e64e2995d3eb98337959f024fa7e2f3230858315751c6f7bec`.

The target counts marked colors in a reinforced urn. Beyond the recursive
construction, `word_mass` proves the independent rising-product characterization
of every color word; its mass depends only on the two color counts. This supplies
the exchangeable urn law and includes zero reinforcement. The expectation lemma
pushes the first-color partition through the counting map, while the CTE proof
only executes the rational draw, updated-urn recursion, and returned count.

The full terminating natural-input domain is `n = 0 ∨ 0 < ones + zeros`, with any
natural reinforcement. Absent colors and zero reinforcement remain valid; an empty
urn is included exactly when no draws are requested. All continuation credits are
arbitrary ENNReal values. The law's arbitrary extension to nonzero draws from an
empty urn does not broaden the program theorem.

Independent checks passed: clean module build, arbitrary framed public client,
constant-infinite credit, zero-draw point masses, empty zero-draw urn, absent-color
zero-reinforcement client, the independent-trial word probability `2/9` for initial
urn `(1,2)` with no reinforcement, and equality of the two mixed-color word masses
under reinforcement. All core/specification/expectation/word-mass axioms are the
three standard axioms.

## Shared urn proportions

Reviewed `SampLib.Distributions.Urn`: the nonempty-urn bias and its exact marked and
unmarked ENNReal probabilities. Its only use of the empty-urn bias is a total
mathematical extension; public program domains exclude invalid draws. Both PMF
lemmas were independently checked for standard axioms. This support is included
in the transitive snapshots and separately bound in the receipt.
