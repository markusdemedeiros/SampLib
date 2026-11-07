import SampLib.PSRN.Support.Uniform.Vector
import SampLib.PSRN.Support.Events.VectorRejection
import SampLib.Core.BetaStep
import SampLib.Core.Syntax.ClosedExp

/-! # Deferred uniform vectors accepted by a shape predicate

The proposal is the actual repeated uniform constructor. Acceptance conditions the
entire vector and retains all its memoized coordinates in one shared owned world.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.PSRNInsideShape

private instance repeat_closed {rT : Type} : ClosedExp (Occil.repeatSample : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.repeatSample, Exp.fv]

private instance uniform_closed {rT : Type} : ClosedExp (Occil.PSRN.newUniform : Exp rT) where
  lc := by is_lc
  fv := by
    simp [Occil.PSRN.newUniform, Occil.PSRN.fromUniformBag, Occil.PSRN.integerPower,
      Occil.uniformBagPrefix, Occil.uniformBagStep, Occil.newUniformBag, Occil.fairCoin, Exp.fv]

private instance rejection_closed {rT : Type} :
    ClosedExp (Occil.PSRN.newRejection : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.PSRN.newRejection, Exp.fv]

private def proposalBody {rT : Type} (n : ℕ) : Exp rT :=
  pl(&Occil.repeatSample &Occil.PSRN.newUniform #int ((n + 1 : ℕ) : ℤ))

private instance proposal_closed {rT : Type} (n : ℕ) : ClosedExp (proposalBody (rT := rT) n) where
  lc := by is_lc
  fv := by simp [proposalBody, Exp.fv, ClosedExp.fv (e := (Occil.repeatSample : Exp rT)),
    ClosedExp.fv (e := (Occil.PSRN.newUniform : Exp rT))]

private def proposal {rT : Type} (n : ℕ) : Val rT :=
  ⟨.lam (proposalBody n), .lam (by is_lc), by is_lc⟩

noncomputable section

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open LatentReal

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
private theorem proposal_beta (E : CoPset) (n : ℕ) (Φ : Val rT → IProp GF) :
    tglWp E (proposalBody n) Φ ⊢ tglWp E pl(&(proposal (rT := rT) n).fst #()) Φ := by
  have h := twp_beta E [] (proposalBody (rT := rT) n) (Val.unit : Val rT) (by is_lc) Φ
  simpa only [Ectx.fill, List.foldl_nil, Exp.open', ClosedExp.openRec, proposal] using h

private theorem proposalSpec (E : CoPset) (n : ℕ) :
    IsLatentVectorSpec (GF := GF) E pl(&(proposal (rT := rT) n).fst #())
      (UniformVector.world (n + 1)) (fun i => UniformVector.view i)
      (UniformVector.initial (n + 1)) UniformVector.owns where
  sameWorld := UniformVector.view_sameWorld
  coordinate := UniformVector.coordinateSpec E
  payload := {
    spec := fun F hF => by
      iintro Hcredit
      iapply (proposal_beta E n _)
      isimp only [proposalBody]
      iapply (UniformVector.uniformVector_latentSpec E (n + 1)).payload.spec F hF $$ Hcredit }

/-- Positive-dimensional uniform proposals conditioned on a verified latent shape event. -/
theorem newInsideShape_vectorSpec (E : CoPset) (n : ℕ) (A : Set (Fin (n + 1) → ℝ))
    [DecidablePred (· ∈ A)] (hmass : UniformVector.law (UniformVector.initial (n + 1)) A ≠ 0)
    (accept : Val rT)
    (haccept : IsEventSpec (GF := GF) E (UniformVector.world (n + 1))
      (VectorOwns UniformVector.owns) A accept) :
    IsLatentVectorSpec (GF := GF) E
      pl(&Occil.PSRN.newInsideShape #int ((n + 1 : ℕ) : ℤ) &accept.fst #())
      (Conditioning.model (UniformVector.world (n + 1)) (UniformVector.initial (n + 1)) A hmass)
      (fun i => Conditioning.viewModel (UniformVector.world (n + 1)) (UniformVector.view i)
        (UniformVector.view_sameWorld i) (UniformVector.initial (n + 1)) A hmass)
      none (VectorRejection.owns (UniformVector.world (n + 1))
        (UniformVector.initial (n + 1)) A UniformVector.owns) where
  sameWorld i := Conditioning.viewModel_sameWorld (UniformVector.world (n + 1))
    (UniformVector.view i) (UniformVector.view_sameWorld i)
    (UniformVector.initial (n + 1)) A hmass
  coordinate handles i := Conditioning.viewSpec E (UniformVector.world (n + 1))
    (UniformVector.view i) (UniformVector.view_sameWorld i)
    (UniformVector.initial (n + 1)) A hmass (UniformVector.owns handles) (handles i)
    (UniformVector.coordinateSpec E handles i)
  payload := {
    spec := fun F hF => by
      iintro Hcredit
      iterate 5 twp_pure
      isimp only [ClosedExp.openRec, ClosedExp.closeRec]
      let draw : Exp rT := pl(&Occil.PSRN.newRejection &(proposal n).fst &accept.fst #())
      ieval (change _ ⊢ tglWp E draw _)
      iapply (VectorRejection.newRejection_vectorSpec E (UniformVector.world (n + 1))
        (fun i => UniformVector.view i) (UniformVector.initial (n + 1)) UniformVector.owns A
        hmass (proposal n) accept (proposalSpec E n) haccept).payload.spec F hF $$ Hcredit }

end specification

end

end SampLib.PSRNInsideShape
