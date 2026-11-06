import SampLib.LatentVectorSpec
import SampLib.LatentConditionedViews
import SampLib.LatentRejectionKernel

/-! # Rejection retaining an entire deferred vector

The common constructor kernel applies unchanged. Every accepted coordinate remains
a view of the same conditional world; no coordinate ownership is duplicated.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal.VectorRejection

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω] {n : ℕ}
local bi (IProp GF)

/-- All accepted handles retain one conditional physical world. -/
def owns (world : Model Ω S) (initial : S) (A : Set Ω)
    (P : (Fin n → Val rT) → S → IProp GF) (handles : Fin n → Val rT) :
    Option (Conditioning.Accepted world initial A) → IProp GF :=
  Conditioning.worldOwns world initial A (P handles)

omit [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT] in
private theorem retain_vector (world : Model Ω S) (initial : S) (A : Set Ω)
    (P : (Fin n → Val rT) → S → IProp GF) (v : Val rT)
    (q : Option (Conditioning.Accepted world initial A)) :
    Conditioning.owns world initial A (VectorOwns P) v q ⊢
      VectorOwns (owns world initial A P) v q := by
  cases q with
  | none =>
    iintro Hstate
    isimp only [Conditioning.owns] at Hstate
    ihave %hfalse := Hstate
    exact False.elim hfalse
  | some q =>
    isimp only [Conditioning.owns, VectorOwns, owns, Conditioning.worldOwns]
    iintro Hstate
    iexact Hstate

/-- The actual retry algorithm preserves all accepted oracle coordinates jointly. -/
theorem newRejection_vectorSpec (E : CoPset) (world : Model Ω S)
    (views : Fin n → Model Ω S) (initial : S) (P : (Fin n → Val rT) → S → IProp GF)
    (A : Set Ω) [DecidablePred (· ∈ A)] (hmass : world.posterior initial A ≠ 0)
    (proposal accept : Val rT)
    (hproposal : IsLatentVectorSpec E pl(&proposal.fst #()) world views initial P)
    (haccept : IsEventSpec E world (VectorOwns P) A accept) :
    IsLatentVectorSpec E pl(&Occil.PSRN.newRejection &proposal.fst &accept.fst #())
      (Conditioning.model world initial A hmass)
      (fun i => Conditioning.viewModel world (views i) (hproposal.sameWorld i) initial A hmass)
      none (owns world initial A P) where
  sameWorld i := Conditioning.viewModel_sameWorld world (views i)
    (hproposal.sameWorld i) initial A hmass
  coordinate handles i := Conditioning.viewSpec E world (views i) (hproposal.sameWorld i)
    initial A hmass (P handles) (handles i) (hproposal.coordinate handles i)
  payload := {
    spec := fun F hF => by
      have hkernel := LatentRejectionKernel.newRejection_payloadSpec E world initial
        (VectorOwns P) A hmass proposal accept hproposal.payload haccept
      iintro Hcredit
      iapply hkernel.wp F hF _ $$ Hcredit
      iintro %v %q %hq Hstate Hcredit
      iexists q
      iframe Hcredit
      isplitl []
      · ipureintro
        exact hq
      iapply retain_vector world initial A P v q $$ Hstate }

end

end SampLib.LatentReal.VectorRejection
