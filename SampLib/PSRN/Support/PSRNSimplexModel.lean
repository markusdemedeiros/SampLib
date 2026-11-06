import SampLib.PSRN.Support.LatentRepresentedExponentialWrappers
import SampLib.PSRN.Support.LatentPiAllocation
import SampLib.PSRN.Support.LatentNormalizationModel
import SampLib.PSRN.Syntax.PSRNSimplex

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

namespace SampLib.PSRNSimplex

noncomputable section

open LatentReal MeasureTheory

/-- Strict positivity is established jointly before any coordinate is normalized. -/
theorem initial_nonzero (n : ℕ) (hn : 0 < n) :
    RepresentedReciprocalView.Nonzero (denominator n) (initial n) := by
  have h := PSRNDirichletLaw.ae_total_pos (fun _ : Fin n => (1 : ℝ))
    (fun _ => zero_lt_one) hn
  rw [← proposal_law n] at h
  have hmeas : MeasurableSet {y : Fin n → ℝ | 0 < PSRNDirichletLaw.total y} := by
    unfold PSRNDirichletLaw.total
    apply measurableSet_lt measurable_const
    fun_prop
  have hbefore := (ae_map_iff (measurable_vectorValue (original n)).aemeasurable hmeas).mp h
  change ∀ᵐ x ∂(CoordinateSum.model (world n) (original n) (original_sameWorld n)).posterior
    (initial n), (CoordinateSum.model (world n) (original n) (original_sameWorld n)).value x ≠ 0
  rw [(CoordinateSum.sameWorld (world n) (original n) (original_sameWorld n)).posterior_eq]
  filter_upwards [hbefore] with x hx
  rw [CoordinateSum.value_eq]
  exact hx.ne'

/-- Reading any coordinate preserves positivity of the common sum by absolute continuity. -/
theorem nonzero_of_refines (n : ℕ) (hn : 0 < n) (s : State n)
    (hs : (world n).refines (initial n) s) :
    RepresentedReciprocalView.Nonzero (denominator n) s :=
  RepresentedReciprocalView.nonzero_refines (denominator n)
    ((CoordinateSum.sameWorld (world n) (original n) (original_sameWorld n)).refines_iff _ _
      |>.mpr hs)
    (initial_nonzero n hn)

end

end SampLib.PSRNSimplex

open ProbLang

namespace SampLib.PSRNSimplex

noncomputable section

open LatentReal Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

def originalOwns (n : ℕ) : (Fin n → Val rT) → State n → IProp GF :=
  PiModel.owns (fun _ => ComponentState) (fun _ => PSRNExponential.rationalOwns 1 1)

/-- The actual callback forwards the concrete represented unit-rate exponential law. -/
theorem sampleSpec (E : CoPset) :
    IsRepresentedDistSpec (GF := GF) E pl(&(Program.sampleValue (rT := rT)).fst #())
      component componentRepresentation (LatentExponential.initial rate)
      (PSRNExponential.rationalOwns 1 1) where
  toIsLatentPayloadSpec := by
    refine ⟨fun F hF => ?_⟩
    have hbase : IsRepresentedDistSpec (GF := GF) E
        pl(&Occil.PSRN.newExponential #1 #1 #()) component componentRepresentation
        (LatentExponential.initial rate) (PSRNExponential.rationalOwns 1 1) :=
      PSRNExponential.newExponential_representedDistSpec E 1 1 (by decide) (by decide)
    iintro Hcredit
    rw [Program.sample_fst]
    twp_pure
    rw [Program.exponential_openRec]
    iapply hbase.spec F hF $$ Hcredit
  oracle := (PSRNExponential.newExponential_representedDistSpec E 1 1
    (by decide) (by decide)).oracle

/-- All constructor calls allocate one independent joint family, with exact interval protocols. -/
theorem allocationSpec (E : CoPset) (n : ℕ) :
    IsRepresentedVectorSpec (GF := GF) E
      pl(&Occil.repeatSample &(Program.sampleValue (rT := rT)).fst #int (n : ℤ))
      (world n) (original n) (originalRepresentation n) (initial n) (originalOwns n) :=
  PiModel.repeatSample_vectorSpec E component componentRepresentation
    (LatentExponential.initial rate) (PSRNExponential.rationalOwns 1 1)
    Program.sampleValue (sampleSpec E) n

end

end SampLib.PSRNSimplex
