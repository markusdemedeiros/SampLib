import SampLib.General.Laws.Markov
import SampLib.Core.SupportedSpec
import SampLib.Core.MarkovTerms

/-! # Finite chains with integer-weight transition rows

The target is the finite iterate of the row-normalized transition kernel.
No assumption of stationarity or convergence is needed.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.MarkovChain

noncomputable section

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

def encodeRow (r : Row) : Val rT := listVal (fun n : ℕ => Val.int n) r.val

/-- The object-language row lookup followed by categorical sampling. -/
theorem markovStep_distSpec (E : CoPset) (rows : List Row) (i : ℕ) (hi : i < rows.length) :
    IsDistSpec (GF := GF) E
      pl(&Occil.General.markovStep &(listVal encodeRow rows).fst #int (i : ℤ))
      (kernel rows i) (fun j : ℕ => Val.int j) where
  spec F _ := by
    iintro Hcredit
    twp_pure
    simp only [MarkovTerms.getAt_openRec, MarkovTerms.getAt_closeRec,
      MarkovTerms.weightedChoice_openRec, MarkovTerms.weightedChoice_closeRec]
    twp_pure
    simp only [MarkovTerms.getAt_openRec, MarkovTerms.weightedChoice_openRec]
    twp_bind pl(&Occil.getAt &(listVal encodeRow rows).fst #int (i : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply (twp_getAt E encodeRow rows ⟨i, hi⟩)
    iintro %v %hv
    subst v
    let : NeZero (rows.get ⟨i, hi⟩).val.sum := ⟨(rows.get ⟨i, hi⟩).property.ne'⟩
    isimp only [kernel, row_get rows i hi] at Hcredit
    simp only [Exp.ofVal, encodeRow]
    iapply (WeightedChoice.twp_weightedChoice E (rows.get ⟨i, hi⟩).val F) $$ Hcredit

/-- Execute exactly `n` transitions, retaining the current-state invariant. -/
theorem twp_markovChain (E : CoPset) (rows : List Row)
    (hsquare : ∀ r ∈ rows, r.val.length = rows.length) (n i : ℕ)
    (hi : i < rows.length) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ z, F z ∂law rows n i) -∗
      tglWp E pl(&Occil.General.markovChain &(listVal encodeRow rows).fst
        #int (i : ℤ) #int (n : ℤ))
        (fun v : Val rT => iprop(∃ z : ℕ, ⌜v = Val.int z⌝ ∗ ↯ (F z))) := by
  induction n generalizing i F with
  | zero =>
    iintro Hcredit
    iterate 4
      twp_pure
      simp only [MarkovTerms.markovStep_openRec, MarkovTerms.markovStep_closeRec]
    twp_pures
    twp_value
    imodintro
    iexists i
    isimp only [law, FiniteKernels.iterate, MeasureTheory.lintegral_dirac] at Hcredit
    iframe Hcredit
    itrivial
  | succ n ih =>
    iintro Hcredit
    iterate 4
      twp_pure
      simp only [MarkovTerms.markovStep_openRec, MarkovTerms.markovStep_closeRec]
    iterate 5 twp_pure
    rw [Nat.cast_add_one, add_sub_cancel_right]
    twp_bind pl(&Occil.General.markovStep &(listVal encodeRow rows).fst #int (i : ℤ))
    isimp only [← FiniteKernels.expectation (kernel rows) n i F] at Hcredit
    iapply ((markovStep_distSpec E rows i hi).wp_supported (fun j => j < rows.length)
      (Set.to_countable _).measurableSet (kernel_support rows hsquare i hi)
      (fun j => ∫⁻ z, F z ∂law rows n j) (measurable_of_countable _) _) $$ Hcredit
    iintro %j %hj Hcredit
    have hnext := ih j hj F
    simp [Occil.General.markovChain, Exp.close, Exp.closeRec] at hnext
    exact wand_entails hnext

/-- Finite-step chain law for any square stochastic integer matrix. -/
theorem markovChain_distSpec (E : CoPset) (rows : List Row)
    (hsquare : ∀ r ∈ rows, r.val.length = rows.length) (n i : ℕ)
    (hi : i < rows.length) :
    IsDistSpec (GF := GF) E pl(&Occil.General.markovChain &(listVal encodeRow rows).fst
      #int (i : ℤ) #int (n : ℤ)) (law rows n i) (fun z : ℕ => Val.int z) where
  spec F _ := wand_entails (twp_markovChain E rows hsquare n i hi F)

omit [ProbLangDist.IsUniformInt rT] in
/-- Zero transitions return the initial value without inspecting the matrix. -/
theorem markovChain_zero_distSpec (E : CoPset) (matrix initial : Val rT) :
    IsDistSpec (GF := GF) E
      pl(&Occil.General.markovChain &matrix.fst &initial.fst #0)
      (MeasureTheory.Measure.dirac ()) (fun _ : Unit => initial) where
  spec F _ := by
    iintro Hcredit
    iterate 4
      twp_pure
      simp only [MarkovTerms.markovStep_openRec, MarkovTerms.markovStep_closeRec]
    twp_pures
    iapply (tglWp_value_of_toVal (Val.toVal?_fst initial))
    iexists ()
    isimp only [MeasureTheory.lintegral_dirac] at Hcredit
    iframe Hcredit
    itrivial

end specification

end

end SampLib.MarkovChain
