module

public import SampLib.PSRN.Laws.PSRNDistributionMixtures

@[expose] public section

/-! # Standard densities of the named integer-gamma mixture families -/

open ProbabilityTheory
open scoped ENNReal

namespace SampLib.PSRNGammaFamilyDensities

noncomputable section

/-- Garima's exponential-component probability. -/
def garimaWeight (θ : ℝ) (hθ : 0 < θ) : unitInterval :=
  ⟨(θ + 1) / (θ + 2), by positivity,
    (div_le_one (by positivity)).mpr (by linarith)⟩

/-- i-Garima's exponential-component probability. -/
def igarimaWeight (θ : ℝ) (hθ : 0 < θ) : unitInterval :=
  ⟨(θ + 2) / (θ + 3), by positivity,
    (div_le_one (by positivity)).mpr (by linarith)⟩

/-- Mirra's exponential-component probability, with its second positive parameter. -/
def mirraWeight (θ α : ℝ) (hθ : 0 < θ) (hα : 0 < α) : unitInterval :=
  ⟨θ ^ 2 / (α + θ ^ 2), by positivity,
    (div_le_one (by positivity)).mpr (by linarith)⟩

def garimaPDF (θ x : ℝ) : ℝ :=
  if 0 ≤ x then θ / (θ + 2) * (θ + 1 + θ * x) * Real.exp (-(θ * x)) else 0

def igarimaPDF (θ x : ℝ) : ℝ :=
  if 0 ≤ x then θ / (θ + 3) * (θ + 2 + θ * x) * Real.exp (-(θ * x)) else 0

def xgammaPDF (θ x : ℝ) : ℝ :=
  if 0 ≤ x then θ ^ 2 / (θ + 1) * (1 + θ * x ^ 2 / 2) * Real.exp (-(θ * x)) else 0

def weightedExponentialGammaPDF (θ x : ℝ) : ℝ :=
  if 0 ≤ x then θ ^ 3 / (2 * (θ + 1)) * x * (2 + x) * Real.exp (-(θ * x)) else 0

def mirraPDF (θ α x : ℝ) : ℝ :=
  if 0 ≤ x then θ ^ 3 / (α + θ ^ 2) * (1 + α * x ^ 2 / 2) * Real.exp (-(θ * x)) else 0

/-- The shape-one/two selector gives the standard Garima density. -/
theorem garima_density (θ : ℝ) (hθ : 0 < θ) (x : ℝ) :
    PSRNDistributionMixtures.density (garimaWeight θ hθ) 1 2 θ x =
      ENNReal.ofReal (garimaPDF θ x) := by
  by_cases hx : 0 ≤ x
  · rw [PSRNDistributionMixtures.density_one_two _ hθ hx]
    simp only [garimaWeight, garimaPDF, ite_eq_left hx]
    congr 1
    field_simp
    ring
  · simp [PSRNDistributionMixtures.density, gammaPDF, gammaPDFReal, garimaPDF, hx]

/-- The shifted selector gives the standard i-Garima density. -/
theorem igarima_density (θ : ℝ) (hθ : 0 < θ) (x : ℝ) :
    PSRNDistributionMixtures.density (igarimaWeight θ hθ) 1 2 θ x =
      ENNReal.ofReal (igarimaPDF θ x) := by
  by_cases hx : 0 ≤ x
  · rw [PSRNDistributionMixtures.density_one_two _ hθ hx]
    simp only [igarimaWeight, igarimaPDF, ite_eq_left hx]
    congr 1
    field_simp
    ring
  · simp [PSRNDistributionMixtures.density, gammaPDF, gammaPDFReal, igarimaPDF, hx]

/-- Shapes one and three with the Lindley selector identify xgamma's quadratic factor. -/
theorem xgamma_density (θ : ℝ) (hθ : 0 < θ) (x : ℝ) :
    PSRNDistributionMixtures.density (PSRNGammaMixtures.lindleyWeight θ hθ) 1 3 θ x =
      ENNReal.ofReal (xgammaPDF θ x) := by
  by_cases hx : 0 ≤ x
  · rw [PSRNDistributionMixtures.density_one_three _ hθ hx]
    simp only [PSRNGammaMixtures.lindleyWeight, xgammaPDF, ite_eq_left hx]
    congr 1
    field_simp
    ring
  · simp [PSRNDistributionMixtures.density, gammaPDF, gammaPDFReal, xgammaPDF, hx]

/-- Shapes two and three give the weighted exponential-gamma density. -/
theorem weightedExponentialGamma_density (θ : ℝ) (hθ : 0 < θ) (x : ℝ) :
    PSRNDistributionMixtures.density (PSRNGammaMixtures.lindleyWeight θ hθ) 2 3 θ x =
      ENNReal.ofReal (weightedExponentialGammaPDF θ x) := by
  by_cases hx : 0 ≤ x
  · rw [PSRNDistributionMixtures.density_two_three _ hθ hx]
    simp only [PSRNGammaMixtures.lindleyWeight, weightedExponentialGammaPDF,
      ite_eq_left hx]
    congr 1
    field_simp
    ring
  · simp [PSRNDistributionMixtures.density, gammaPDF, gammaPDFReal,
      weightedExponentialGammaPDF, hx]

/-- Mirra's second parameter changes only the quadratic mixture weight. -/
theorem mirra_density (θ α : ℝ) (hθ : 0 < θ) (hα : 0 < α) (x : ℝ) :
    PSRNDistributionMixtures.density (mirraWeight θ α hθ hα) 1 3 θ x =
      ENNReal.ofReal (mirraPDF θ α x) := by
  by_cases hx : 0 ≤ x
  · rw [PSRNDistributionMixtures.density_one_three _ hθ hx]
    simp only [mirraWeight, mirraPDF, ite_eq_left hx]
    congr 1
    field_simp
    ring
  · simp [PSRNDistributionMixtures.density, gammaPDF, gammaPDFReal, mirraPDF, hx]

end

end SampLib.PSRNGammaFamilyDensities
