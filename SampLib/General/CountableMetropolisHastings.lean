import SampLib.General.Laws.CountableMetropolis
import SampLib.General.MetropolisKernel

/-! # Exact rational Metropolis–Hastings transitions

The finite-step law is an iterate of the independently defined Metropolis kernel.
No finite-time convergence to a target distribution is assumed.
-/

open ProbLang
open scoped ENNReal NNReal

namespace SampLib.CountableMetropolisHastings

noncomputable section

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {α : Type _} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
local bi (IProp GF)

/-- Countable-state exact Metropolis–Hastings iteration from any positive-weight state. -/
theorem metropolisHastings_distSpec (E : CoPset) (w : α → ℕ) (p : Proposal α)
    (encode : α → Val rT) (target proposal q : Val rT)
    (htarget : ∀ x, ⊢ tglWp E pl(&target.fst &(encode x).fst)
      (fun v : Val rT => iprop(⌜v = Val.int (w x)⌝)))
    (hq : ∀ x y, ⊢ tglWp E pl(&q.fst &(encode x).fst &(encode y).fst)
      (fun v : Val rT => iprop(⌜v = Val.pair (Val.int (p.numerator x y))
        (Val.int (p.denominator x y))⌝)))
    (hproposal : ∀ x, IsDistSpec (GF := GF) E pl(&proposal.fst &(encode x).fst)
      (p.measure x) encode)
    (n : ℕ) (x : α) (hx : 0 < w x) :
    IsDistSpec (GF := GF) E pl(&Occil.General.metropolisHastings &target.fst &proposal.fst
      &q.fst &(encode x).fst #int (n : ℤ)) (law w p n x) encode :=
  MetropolisRatio.kernel_distSpec E w p.toRatios
    p.measure (proposal_support p) encode target proposal q
    htarget hq hproposal n x hx

omit [ProbLangDist.IsUniformInt rT] in
/-- Zero transitions do not invoke any callback or inspect the initial value. -/
theorem metropolisHastings_zero_distSpec (E : CoPset)
    (target proposal q initial : Val rT) :
    IsDistSpec (GF := GF) E pl(&Occil.General.metropolisHastings &target.fst &proposal.fst
      &q.fst &initial.fst #0) (MeasureTheory.Measure.dirac ()) (fun _ : Unit => initial) :=
  MetropolisRatio.zero_distSpec E target proposal q initial

end specification

end

end SampLib.CountableMetropolisHastings
