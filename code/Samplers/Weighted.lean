import Samplers.More
import Samplers.Weighted.Core
import Samplers.Weighted.Uniform
import Samplers.Weighted.Reductions
import Samplers.Weighted.Tables
import Samplers.Weighted.Trees
import Samplers.Weighted.Reservoir

/-! Compatibility entry point for integer-weight and uniform-format algorithms.

Implementations are grouped in `Samplers.Weighted.*` by their arithmetic,
preprocessing, entropy consumption, and inclusion-sampling techniques.
-/
