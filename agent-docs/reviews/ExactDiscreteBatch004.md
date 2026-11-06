# Independent exact sampler review: ExactDiscreteBatch004

Reviewer: `/root/review_exact_b`. Accepted core theorem `SampLib.BinomialHalfRejection.binomialHalfRejection_distSpec`, SHA-256 `3e04b91a288a1272e26694046c138450db1f300db57b51a056c48ca31837ab0e`.

Domain: Every natural number of trials, including zero, small sizes, odd sizes and even sizes. The target is the canonical fair binomial law. UniformInt is the only random primitive assumption; arbitrary ENNReal continuation credit, including infinity, is supported.

The proposal samples a geometric block, a uniform rank in width floor(sqrt(n))+1, and a fair sign. The positive and negative integer candidates form an explicit bijection, giving the exact proposal atom. The binomial envelope bounds the actual acceptance fraction, including the small even case where the width exceeds the midpoint. Multiplying proposal and acceptance cancels pointwise to exactly one sixteenth of the canonical binomial expectation. Invalid candidates are rejected before any natural-index conversion. All cancellations retain arbitrary ENNReal F and zero times infinity.

The rejection loop therefore has rejection mass fifteen sixteenths and exact error-credit amplification sixteen fifteenths. Small sizes execute the actual bit sum; odd sizes sample the source's fair bit before recursively sampling n-1; even sizes execute the actual Newton integer-square-root helper and the certified rejection loop. The outer induction covers every n. Source-opening and recursive loop alignment are isolated in named certificates; the program proof contains straightforward branch execution and calls to established rules. Repeated raw AST normalization lists were removed during review.

The independent client retains arbitrary F and an unrelated Iris frame. Actual calls cover n=0 through 6 and infinite continuation credit on even and odd branches. Pure checks include the n=4 width=3 boundary, both candidate signs, invalid proposal rejection, accepted mass one sixteenth, canonical out-of-range zero mass and the n=0 point mass. All six printed sampler, proposal, accepted-moment, envelope, integer-square-root and client axiom checks use only propext, Classical.choice and Quot.sound.

Independent targeted build, caller and exact-head/noncircular-premise audit pass warning-free; ExactDiscreteBatch004.log retains commands and output. The immutable receipt binds the exact local source/support closure, caller and dependency context.
