import Samplers.Weighted
import Samplers.Weighted.Optimal
import Samplers.Weighted.Rejection
import Samplers.Weighted.Aliases
import Samplers.Weighted.Choice
import Samplers.Weighted.Dynamic

/-! Compatibility entry point for static and mutable weighted-choice structures.

The original `Occil.WeightedVariants` names remain available. Algorithms live in
focused `Samplers.Weighted.*` modules; no machine-model space or parallel-performance
bounds are claimed for their interpreter heap representation.
-/
