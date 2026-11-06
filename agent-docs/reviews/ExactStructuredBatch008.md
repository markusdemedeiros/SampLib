# Independent exact sampler review: ExactStructuredBatch008

Reviewer: `/root/review_exact_b`. Accepted core theorem `SampLib.KnuthYao.knuthYao_distSpec`, SHA-256 `9139a8ce544bc30f02728c2a5b4125865ce5f577dc064e119b790a7d51020b1b`.

Domain: Every finite natural-weight list with positive total, including zero weights, certain rows, dyadic and non-dyadic probabilities. The full canonical weighted-choice law uses original position labels. All measurable ENNReal output credit, including infinity, is allowed.

The actual certain-row scan handles a weight equal to the total before entering the binary tree. Otherwise each weight is strictly below total, and concrete quotient/remainder columns give one live root and fewer live ranks than rows at every depth. The actual matrix-column scan partitions leaf ranks and retained ranks; the fair-bit step implements their exact rank recurrence.

The finite-horizon DDG argument retains each leaf continuation and gives each surviving rank one contradictory credit at the horizon. Its aggregate budget is bounded by the desired row expectation plus the number of rows times 2^-h. This residual is independent of F and tends to zero. NNReal remainder coefficients multiply arbitrary ENNReal continuations directly; zero rows remain in the literal finite sum, so zero times infinity is preserved. No finite continuation expectation, runtime moment, hypothetical matrix or desired sampler-law premise is assumed.

Review covered concrete columns, coefficient recurrence, aggregate bound, finite scan and loop CTE, deterministic certain-row handling, literal source correspondence and full public theorem. Symbolic execution uses named source-opening and loop-alignment certificates. The original implementation is unchanged.

The independent client executes the actual head with arbitrary F and unrelated Iris frame. Concrete clients include non-dyadic [0,1,0,4] with infinite credit on both zero rows and zero initial budget, certain [0,0,9,0], and dyadic [1,0,1]. Pure fixtures check exact columns, exhaustion and the certain-row scan. All seven printed public, loop, DDG, column, expectation and client axiom checks use only propext, Classical.choice and Quot.sound.

Independent targeted build, caller and exact-head/noncircular-premise audit pass warning-free; ExactStructuredBatch008.log retains commands and output. The immutable receipt binds the exact local source/support closure, caller and dependency context.
