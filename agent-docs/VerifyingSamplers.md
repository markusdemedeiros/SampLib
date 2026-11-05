# Verifying and polishing an Occil sampler

This note records the user's proof-quality standard and the workflow established
with `realCoin` and von Neumann extraction. Keep working on the current sampler
until its proof meets that standard; add another only when requested.

## The standard

Morally, a sampler proof has two parts:

- **Program logic:** show a deep appreciation for CTE's simplicity. The proof must
  be obvious, straight-line symbolic execution under known idioms. Each step
  should perform a small, recognizable logical operation.
- **Expectation preservation:** show the underlying mathematical argument clearly
  enough to be useful to an expert reader. Prefer standard mathlib lemmas and
  concise algebra over mechanical expansion or a transcript of debugging.

Minimize everything else. A successful build establishes acceptance by Lean;
quality also depends on the specification, mathematical explanation, abstraction,
and presentation. Shorter code is useful when it makes those clearer.

## 1. Inspect the implementation and choose the specification

Read the actual `pl%` term, its source correspondence, and the installed CTE rules.
Prove the existing algorithm. Do not quietly change its implementation, domain,
comparison strictness, or numerical interpretation to simplify a proof.

Separate mathematical reals, explicit fixed-point approximations, and Float
execution. An exact-real proof does not verify the Float interpreter's rounding.
Use the weakest language assumptions needed: an algorithm using abstract coin
calls need not assume the uniform-real primitive.

Use [SampLib/Templates.lean](../SampLib/Templates.lean):

```lean
IsDistSpec (GF := GF) E e μ encode
```

Here `μ` is a normalized probability measure on a measurable output type and
`encode` produces ProbLang values. The spec accepts arbitrary measurable credits
`F : α → ℝ≥0∞`, including unbounded and infinite credits. It is relative to the
current ghost state and mask, so callers can compose it inside another proof.

State the complete input domain and output representation. For callback-based
algorithms, assume the callback's distribution specification instead of inspecting
its implementation. Use that specification at every call; a statement about a
single unconditional marginal is not enough to justify independence.

Keep the top-level theorem a small `IsDistSpec` wrapper around the CTE proof.
The user considers adequacy corollaries rote and wants them omitted. Do not
reintroduce real-valued output encodings just to use upstream `IsDistSpec'`.

## 2. Work out the mathematics first

For arbitrary continuation credit `F`, identify:

1. The expected output credit `C(F) = ∫⁻ x, F x ∂μ`.
2. The credit assigned to each random outcome, including conditional expectations
   between successive draws.
3. The single expectation-preservation identity needed by the program proof.

For a retrying algorithm, the mathematical argument must cover termination too.
For example, von Neumann extraction has retry probability
`q = p² + (1-p)²`, with `0 < q < 1` for `0 < p < 1`. Assign auxiliary credit `ε`
so that retries receive `k * ε`, where `k = 1/q > 1`. The combined kernel must
satisfy `E[K] = C(F) + ε`; the identity `q * k = 1` accounts for termination
credit. A distributional recurrence alone does not prove almost-sure termination.

Make this argument recognizable in one expectation-preservation lemma. Local
identities and a short `calc` are often better than many global helper lemmas.
Keep separate domain and amplification facts only where the program proof needs
an explicit fact to apply a rule.

Search the installed mathlib before writing set extensionality or expanding
integrals by hand. For threshold kernels, `lintegral_piecewise`, constant-integral
lemmas, standard interval intersections, and
`restrict_Ico_eq_restrict_Icc` can replace indicator decompositions and manual
endpoint proofs. The last equality relies on null endpoints.

Algebraic automation is welcome here: `simp`, `norm_num`, `ring`, `nlinarith`,
and `positivity` should expose or discharge the mathematics. Avoid giant lists
of Boolean evaluation lemmas. Transport finite probability coefficients between
reals, nonnegative reals, and ENNReal deliberately; do not turn arbitrary
continuation credits into real numbers, which would mishandle infinity.

## 3. Write the CTE proof as symbolic execution

Keep mathematical work outside the main `twp_*` theorem. Its steps should be:

- Introduce the expected credit.
- Execute deterministic steps with `twp_pure` or `twp_pures`.
- Focus a random operation or callback with `twp_bind`.
- Redistribute credits using a primitive rule or an abstract `IsDistSpec`.
- Substitute the returned value and follow the program's branches.
- Return the continuation credit, or apply the recursive hypothesis.

For a verified callback, the usual continuation idiom is:

```lean
iapply (hcoin.wp F hF _) $$ Hcredit
iintro %x Hcredit
```

Frame unrelated resources through the call. Do not accidentally spend them while
supplying the sampler's expected credit.

For recursive termination, use `twp_err_pos` and
`ErrorCredit.Induction.simple`. Revert distribution credit before introducing the
persistent amplification step, so that linear resources are not duplicated. Split
continuation and amplified termination credits explicitly on the retry branch.
Keep the final distribution specification free of auxiliary termination slack.

Avoid search, backtracking, algebra, or clever automation in the program proof.
Do not golf away meaningful logical steps. If an application needs a normalization
fact, give it the precise fact rather than a large `simp` call.

ProbLang binders can leave `openRec`/`closeRec` wrappers around closed constants.
Normalize them using local-closedness and freshness facts when necessary. A
`twp_bind` followed by `tglWp_mono`/`tglWp_value` can handle a return continuation.
Do not unfold an entire verified sampler to work around a binding issue.

## 4. Clean and polish

Preserve the main program-logic argument while polishing supporting mathematics.
Make any necessary interface adjustment explicit and check the remaining proof
for accidental changes; a source comparison is useful.

- Prefer one central expectation lemma to a forest of forwarding lemmas.
- Put retry probability and amplification facts in a termination section.
- State conservation for arbitrary credits, without unnecessary finiteness bounds.
- Use concise comments explaining intent or an invariant; omit tactic narration.
- Keep section order aligned with the mathematical argument and program proof.
- Keep line lengths, indentation, blank lines, and theorem continuations consistent
  with the surrounding Lean files. Target at most 100 columns.

Open namespaces locally and in an order that avoids notation conflicts. Select
protected names explicitly, for example `open ENNReal (ofReal)`. Open measure theory
in the mathematical sections and Iris in the specification section. `Set` and
`Measure` both have `restrict_apply`; retaining `Measure.restrict_apply` is clearer
than forcing an ambiguous unqualified name. Parenthesize measure scalar products
when Iris's resource-composition notation interferes with `•`.

## 5. Validate the final artifact

Run the checks appropriate to a proof-only change:

```sh
lake build
git diff --check
```

Inspect warnings as well as the exit code. Check the main theorem and public spec
with `#print axioms`; their transitive dependencies should contain no `sorryAx`
or newly introduced axioms. The completed examples use only `propext`,
`Classical.choice`, and `Quot.sound`.

Compile a caller example using the public spec, ideally by composing with a
previously verified sampler. Check that the continuation rule preserves an
arbitrary Iris resource. Exercise relevant parameter boundaries when included in
the domain. Do not add excluded endpoints merely to make tests convenient.

Interpreter statistics are separate implementation evidence. Re-running those
suites is unnecessary when only proofs and comments changed. Do not present
statistical agreement as formal verification.

Update proof navigation and descriptions without changing sampler-index coverage.
The README header is also stored in `agent-scripts/readme_index.py`; keep both
copies consistent. Report what was proved, its assumptions, and the checks run.

## References

- [Reusable specs](../SampLib/Templates.lean): `IsDistSpec` and its continuation rule.
- [Threshold Bernoulli](../SampLib/Samplers/RealCoin.lean): a continuous credit split.
- [Von Neumann extraction](../SampLib/Samplers/VonNeumann.lean): abstract calls,
  retry credit, and amplification induction.
- Installed upstream examples under
  `.lake/packages/clutch-lean/Metrology/TotalEris/Examples/Samplers/`, particularly
  `BernoulliGeometric.lean` and `NegExp.lean`, for established recursive idioms.
