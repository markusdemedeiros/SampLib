# ProbLang wishlist

Baseline: `clutch-lean` commit `54e780e4`. Native language operators only.
Target exact-real sampler terms; fixed-point/grid approximations are excluded.

## Implement upstream

- **Real arithmetic:** add `ProbLangℝ.realMul` and `realDiv`; enable real operands
  for existing `BinOp.mult`, `BinOp.div` and `BinOp.minus` (subtraction uses add/neg).
- **Floor:** add `ProbLangℝ.realFloor : T → Int` and `UnOp.floor`.
  Evaluation returns an integer literal; real-operand typing returns `Ty.int`.
- **Elementary functions:** add `realLog`, `realSqrt`, `realExp`, `realSin`,
  `realCos`, `realAtan : T → T` to `ProbLangℝ`, with corresponding `UnOp`
  constructors, `pl%` notation and evaluation cases returning real literals.
- **Pi:** add `ProbLangℝ.realPi : T`; notation can expand to an existing real
  literal. Its ℝ interpretation must be `Real.pi`.
- **Derived library operations:** ceiling from floor; tangent from sin/cos;
  positive-base real powers from `exp (y * log x)`. State zero-base conventions.

For each addition, ship the ℝ instance and equations, measurability fields in
`LawfulProbLangℝ`, typing, concrete reduction lemmas and generic pure-step/CTE
support. Supply executable `Float` operations through `ProbLangℝ`; wire both
interpreters through the shared operator evaluator. Keep mathematical ℝ laws
separate from runtime rounding and nonfinite behavior.

Use Mathlib's total division convention for ℝ. Provide guarded log/sqrt rules
and specify runtime domain failures. Test operator typing, guarded boundaries,
negative floor inputs and agreement between the two evaluators.

## Also useful upstream

- Preserve named lambda/fix bodies in pure steps; reuse closedness certificates
  and diagnose unresolved parameters before expensive normalization.
- Return the heap with results, or run an observation callback before discarding it.
- Per-run fuel, explicit returned/stuck/exhausted outcomes, injectable RNG,
  replayable draws and bit/step/allocation counters.

**Agent note — unlocks:** exact-real inverse transforms, Box–Muller/polar normals,
gamma/beta, Cauchy, Weibull/Pareto, stable laws, copulas and geometric transforms.
PSRN and integer/Bernoulli algorithms still need our owned latent-oracle,
joint-credit and entropy-pool proofs; keep that project work separate from this handoff.
