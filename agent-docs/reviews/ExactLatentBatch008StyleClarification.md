# Gamma batch 008: source-alignment clarification

The source-style sentence in ExactLatentBatch008.md should read: named syntax
builders and a single explicit `ieval (change … Program.recursiveBranch …)`
alignment isolate the recursive stage; the predecessor arithmetic is a named
pure equality. The final Core does **not** use the experimental opening entailment.

That experiment was removed because matching its inferred AST introduced costly
unification. The original one-line alignment names a stage without exposing raw
AST, arithmetic or broad simplification. It meets the straight-line proof standard.
The accepted source snapshots, caller, builds, exact-head audits and laws are
unchanged; this clarifies the prose description of the final implementation.
