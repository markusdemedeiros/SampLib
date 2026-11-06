import SampLib.PSRN.Support.LatentRepresentedExponentialWrappers
import SampLib.PSRN.Support.LatentPiAllocation
import SampLib.PSRN.Support.LatentNormalizationModel

/-! # The common exponential world underlying a simplex vector -/

namespace SampLib.PSRNSimplex

noncomputable section

open LatentReal

abbrev rate : ℝ := ((1 : ℤ) : ℝ) / ((1 : ℤ) : ℝ)
abbrev rate_pos : 0 < rate := PSRNRationalRateDecay.rate_pos 1 1 (by decide) (by decide)
abbrev ComponentState := LatentExponential.State rate
abbrev State (n : ℕ) := Fin n → ComponentState
abbrev World (n : ℕ) := Fin n → ℕ × ℝ

def component : Model (ℕ × ℝ) ComponentState := LatentExponential.model rate rate_pos

def componentRepresentation : Representation component :=
  LatentExponential.representation rate rate_pos

def initial (n : ℕ) : State n := PiModel.initial (LatentExponential.initial rate) n

def world (n : ℕ) : Model (World n) (State n) := PiModel.world (fun _ => component)

def original (n : ℕ) (i : Fin n) : Model (World n) (State n) :=
  PiModel.view (fun _ => component) i

theorem original_sameWorld (n : ℕ) (i : Fin n) : (world n).SameWorld (original n i) :=
  PiModel.sameWorld _ i

def originalRepresentation (n : ℕ) (i : Fin n) : Representation (original n i) :=
  PiModel.representation (fun _ => component) (fun _ => componentRepresentation) i

def denominator (n : ℕ) : Model (World n) (State n) :=
  Normalization.denominator (world n) (original n) (original_sameWorld n)

def normalized (n : ℕ) (i : Fin n) : Model (World n) (State n) :=
  Normalization.coordinate (world n) (original n) (original_sameWorld n)
    (originalRepresentation n) i

def normalizedRepresentation (n : ℕ) (i : Fin n) : Representation (normalized n i) :=
  Normalization.representation (world n) (original n) (original_sameWorld n)
    (originalRepresentation n) i

section mathematics

open MeasureTheory ProbabilityTheory

/-- The actual independent constructors have the shape-one gamma proposal law. -/
theorem proposal_law (n : ℕ) :
    vectorLaw (world n) (original n) (initial n) =
      PSRNDirichletLaw.proposal (fun _ => 1) (fun _ => zero_lt_one) := by
  change vectorLaw (PiModel.world (fun _ : Fin n => component))
    (PiModel.view (fun _ => component)) (initial n) = _
  rw [PiModel.vectorLaw_eq_pi]
  change Measure.pi (fun i => component.law (initial n i)) =
    Measure.pi (fun _ => gammaMeasure 1 1)
  congr 1
  funext i
  simp only [initial, PiModel.initial_eq_const]
  exact (LatentExponential.initial_law rate rate_pos).trans
    (congrArg expMeasure (by norm_num [rate]))

/-- One common normalization gives the joint simplex law. -/
theorem normalized_law (n : ℕ) :
    vectorLaw (world n) (normalized n) (initial n) = PSRNDirichletLaw.simplex n :=
  Normalization.law_eq_dirichlet _ _ _ _ _ _ _ (proposal_law n)

end mathematics

end

end SampLib.PSRNSimplex
