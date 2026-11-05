-- Discrete primitives, collections, and weighted selection.
import Samplers.Uniform
import Samplers.Data
import Samplers.Discrete.All
import Samplers.Combinatorial
import Samplers.Weighted.All

-- Exact coin factories and ideal continuous primitives.
import Samplers.Bernoulli
import Samplers.Lazy
import Samplers.Continuous
import Samplers.Continuous.Rejection
import Samplers.Constants

-- Explicit fixed-point approximations and structured distributions.
import Samplers.Numeric
import Samplers.Numerical.All
import Samplers.Multivariate

-- General sampling schemes, finite models, and lazy real observations.
import Samplers.General
import Samplers.PSRN

/-! The complete sampler library. Individual family modules can be imported
when a smaller dependency surface is useful. -/
