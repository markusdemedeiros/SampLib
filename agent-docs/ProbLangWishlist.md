# ProbLang wishlist

This wishlist targets `clutch-lean` commit `06a7b3e2`, the current pin, and asks only for
native language operators. It aims at exact-real sampler terms and excludes fixed-point and
grid approximations.

## Shipped

The pin already ships the real operators that earlier versions of this list asked for. All
paths are under `.lake/packages/clutch-lean/Metrology/ProbLang/`.

| Item | Provided by |
| --- | --- |
| `realMul`, `realDiv`, `realFloor`, `realLog`, `realSqrt`, `realExp`, `realSin`, `realCos`, `realAtan`, and `realPi` in `ProbLangℝ` | `Syntax/Syntax.lean` |
| Derived `realCeil`, `realTan`, and `realPow`, with the zero-base convention `0 ^ y = 1` stated | `Syntax/Syntax.lean` |
| Total division at ℝ (`r / 0 = 0`), and total `log` and `sqrt` | `Syntax/Syntax.lean` |
| Measurability fields for every operator in `LawfulProbLangℝ` | `Syntax/Syntax.lean` |
| `UnOp` constructors and evaluation cases, and real operands for `BinOp.minus`, `BinOp.mult`, and `BinOp.div` | `Syntax/Syntax.lean` |
| Typing, with `floor` returning `Ty.int` and the other operators returning `Ty.real` | `Syntax/Types.lean` |
| `pl%` notation, including `floor(`, `ceil(`, `tan(`, `pow(`, and `#pi` | `Syntax/Notation.lean` |
| The ℝ instance (`realPi` is `Real.pi`), reduction lemmas, and guarded lemmas for `log` and `sqrt` | `Reals.lean` |
| Generic pure-step support for every unary operator (`pureExec_unop`) | `DetStep.lean` |
| Executable `Float` operations through `ProbLangℝ` | `Interp/BigStepIO.lean` |
| A `run` entry point that returns the final state, heap included, with the value | `Interp/BigStepIO.lean` |
| Tests of typing, guarded boundaries, and negative floor inputs | `Test/Reals.lean` |

## Still missing

The current pin still lacks these features:

- Specify the runtime domain failures and nonfinite results of the `Float` operations, for
  example `log` and `sqrt` of negative inputs. The ℝ laws stay total and separate from
  runtime rounding.
- Preserve named lambda and fix bodies in pure steps. Reuse closedness certificates, and
  diagnose unresolved parameters before expensive normalization.
- Return the heap from the sample runner, which uses `eval` and drops the state, or run an
  observation callback before the runner discards the heap.
- Add per-run fuel, explicit outcomes (returned, stuck, or exhausted), an injectable random
  number generator (RNG), replayable draws, and counters for bits, steps, and allocations.
  The interpreter now raises an IO error on a stuck term and draws from `IO.rand`.

**Agent note:** The shipped operators unlock exact-real inverse transforms, Box-Muller and
polar normals, gamma and beta, Cauchy, Weibull and Pareto, stable laws, copulas, and
geometric transforms. Partially sampled random number (PSRN), integer, and Bernoulli
algorithms still need the latent-oracle, joint-credit, and entropy-pool proofs that this
project owns. Keep that project work separate from this handoff.
