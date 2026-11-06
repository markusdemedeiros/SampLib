import SampLib.Samplers.MarkovChain
import SampLib.ProofMode.BindFrom

/-! # Finite Markov trajectories

The path contains every state after a transition, excluding the initial state.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.MarkovTrajectory

noncomputable section

open MarkovChain

abbrev law (rows : List Row) := FiniteKernels.trajectory (kernel rows)

private theorem encode_cons {rT : Type _} [ProbLangℝ rT] (j : ℕ) (ys : List ℕ) :
    pl(inr((#int (j : ℤ), {Exp.ofVal (listVal (fun n : ℕ => Val.int n) ys)}))) =
      Exp.ofVal (listVal (fun n : ℕ => Val.int n) (j :: ys) : Val rT) := rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] MarkovTerms.markovStep_openRec MarkovTerms.markovStep_closeRec

theorem twp_markovTrajectory (E : CoPset) (rows : List Row)
    (hsquare : ∀ r ∈ rows, r.val.length = rows.length) (n i : ℕ)
    (hi : i < rows.length) (F : List ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ ys, F ys ∂law rows n i) -∗
      tglWp E pl(&Occil.General.markovTrajectory &(listVal encodeRow rows).fst
        #int (i : ℤ) #int (n : ℤ))
        (fun v : Val rT => iprop(∃ ys : List ℕ,
          ⌜v = listVal (fun k : ℕ => Val.int k) ys⌝ ∗ ↯ (F ys))) := by
  induction n generalizing i F with
  | zero =>
    iintro Hcredit
    twp_pures
    twp_value
    imodintro
    iexists []
    isimp only [law, FiniteKernels.trajectory, MeasureTheory.lintegral_dirac] at Hcredit
    iframe Hcredit
    ipureintro
    rfl
  | succ n ih =>
    iintro Hcredit
    iterate 8 twp_pure
    twp_bind pl(&Occil.General.markovStep &(listVal encodeRow rows).fst #int (i : ℤ))
    isimp only [← FiniteKernels.trajectory_expectation (kernel rows) n i F] at Hcredit
    iapply ((markovStep_distSpec E rows i hi).wp_supported (fun j => j < rows.length)
      (Set.to_countable _).measurableSet (kernel_support rows hsquare i hi)
      (fun j => ∫⁻ ys, F (j :: ys) ∂law rows n j) (measurable_of_countable _) _) $$ Hcredit
    iintro %j %hj Hcredit
    twp_pure
    twp_pure
    rw [Nat.cast_add_one, add_sub_cancel_right]
    have hnext := ih j hj (fun ys => F (j :: ys))
    simp [Occil.General.markovTrajectory, Exp.close, Exp.closeRec] at hnext
    twp_bind_from hnext
    iapply tglWp_wand
    isplitl [Hcredit]
    · exact wand_entails hnext
    iintro %v ⟨%ys, %hv, Hcredit⟩
    subst v
    rw [encode_cons]
    iapply (tglWp_value (v := listVal (fun n : ℕ => Val.int n) (j :: ys)))
    iexists j :: ys
    iframe Hcredit
    ipureintro
    rfl

/-- The normalized finite path law under the given stochastic matrix. -/
theorem markovTrajectory_distSpec (E : CoPset) (rows : List Row)
    (hsquare : ∀ r ∈ rows, r.val.length = rows.length) (n i : ℕ)
    (hi : i < rows.length) :
    IsDistSpec (GF := GF) E pl(&Occil.General.markovTrajectory &(listVal encodeRow rows).fst
      #int (i : ℤ) #int (n : ℤ)) (law rows n i) (listVal (fun k : ℕ => Val.int k)) where
  spec F _ := wand_entails (twp_markovTrajectory E rows hsquare n i hi F)

omit [ProbLangDist.IsUniformInt rT] in
/-- A zero-length trajectory is empty for every matrix and initial value. -/
theorem markovTrajectory_zero_distSpec (E : CoPset) (matrix initial : Val rT) :
    IsDistSpec (GF := GF) E
      pl(&Occil.General.markovTrajectory &matrix.fst &initial.fst #0)
      (MeasureTheory.Measure.dirac ())
      (fun _ : Unit => listVal (fun k : ℕ => Val.int k) []) where
  spec F _ := by
    iintro Hcredit
    iterate 4 twp_pure
    twp_pures
    twp_value
    imodintro
    iexists ()
    isimp only [MeasureTheory.lintegral_dirac] at Hcredit
    iframe Hcredit
    ipureintro
    rfl

end specification

end

end SampLib.MarkovTrajectory
