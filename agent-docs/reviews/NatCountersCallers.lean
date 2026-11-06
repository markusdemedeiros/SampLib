import SampLib.Discrete.Support.NatCounters

open ProbLang SampLib Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem frame (E : CoPset) (e : Exp rT) (result : Val rT)
    (h : ⊢ tglWp E e (fun v : Val rT => iprop(⌜v = result⌝))) (R : IProp GF) :
    ⊢ R -∗ tglWp E e (fun v : Val rT => iprop(⌜v = result⌝ ∗ R)) := by
  iintro HR
  iapply tglWp_wand
  isplitl []
  · iapply h
  iintro %v %hv
  iframe HR
  ipureintro
  exact hv

example (E : CoPset) (n : ℕ) (R : IProp GF) :
    ⊢ R -∗ tglWp E pl(&Occil.DiscreteExtra.zeroCounters #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = NatCounters.encode (List.replicate n 0)⌝ ∗ R)) :=
  frame _ _ _ (NatCounters.twp_zeroCounters E n) R

example (E : CoPset) (xs : List ℕ) (i : ℕ) (hi : i < xs.length) (R : IProp GF) :
    ⊢ R -∗ tglWp E pl(&Occil.DiscreteExtra.incrementCounter
      &(NatCounters.encode xs).fst #int (i : ℤ))
      (fun v : Val rT => iprop(⌜v = NatCounters.encode (xs.modify i (· + 1))⌝ ∗ R)) :=
  frame _ _ _ (NatCounters.twp_incrementCounter E xs i hi) R

example (E : CoPset) (R : IProp GF) :
    ⊢ R -∗ tglWp E pl(&Occil.DiscreteExtra.adjustCounter
      &(NatCounters.encode [0, 1, 0]).fst #1 #int (-1 : ℤ))
      (fun v : Val rT => iprop(⌜v = NatCounters.encode [0, 0, 0]⌝ ∗ R)) := by
  exact frame _ _ _ (NatCounters.twp_decrementCounter E [0, 1, 0] 1
    (by decide) (by decide)) R

#print axioms NatCounters.twp_zeroCounters
#print axioms NatCounters.twp_incrementCounter
#print axioms NatCounters.twp_decrementCounter
