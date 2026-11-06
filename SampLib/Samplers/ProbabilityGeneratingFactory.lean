import SampLib.Samplers.IterateCoin
import Samplers.Bernoulli.Combinators
import Metrology.Iris.LocalBI

/-!
# Probability-generating coin factory

An independent natural count `N` selects Bernoulli(`p^N`). The mixture therefore
has success probability `E[p^N]`, including `p=0` and `p=1`.
-/

open Set ProbLang
open scoped ENNReal

namespace SampLib.ProbabilityGeneratingFactory

noncomputable section

section mathematics

open MeasureTheory

/-- Mixture of the all-successes laws, with mixing law `ν` on natural counts. -/
def law (ν : Measure ℕ) (p : unitInterval) : Measure Bool :=
  ν.bind (IterateCoin.law p)

instance (ν : Measure ℕ) [IsProbabilityMeasure ν] (p : unitInterval) :
    IsProbabilityMeasure (law ν p) where
  measure_univ := by
    rw [law, Measure.bind_apply MeasurableSet.univ (measurable_of_countable _).aemeasurable]
    simp only [measure_univ, lintegral_const, one_mul]

/-- Conditioning on the count gives exactly the PGF mixture expectation. -/
theorem expectation_preservation (ν : Measure ℕ) (p : unitInterval) (F : Bool → ℝ≥0∞) :
    ∫⁻ n, IterateCoin.credit p n F ∂ν = ∫⁻ b, F b ∂law ν p := by
  rw [law, Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable F).aemeasurable]
  simp only [IterateCoin.law, RealCoin.lintegral_law, IterateCoin.credit]

end mathematics

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

private theorem iterateCoin_openRec {rT : Type _} (k : ℕ) (v : Exp rT) :
    Exp.openRec k v Occil.iterateCoin = Occil.iterateCoin :=
  (Exp.open_lc k v _ (by is_lc)).symm

private theorem iterateCoin_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.iterateCoin : Exp rT) = Occil.iterateCoin :=
  Exp.closeRec_fresh x _ k (by simp [Occil.iterateCoin, Exp.fv])

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- CTE PGF specification for an abstract coin and independent natural count. -/
theorem twp_probabilityGeneratingFactory (E : CoPset) (ν : MeasureTheory.Measure ℕ)
    [MeasureTheory.IsProbabilityMeasure ν] (p : unitInterval) (coin count : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (hcount : IsDistSpec (GF := GF) E pl(&count.fst #()) ν (fun n => Val.int (n : ℤ)))
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ b, F b ∂law ν p) -∗
      tglWp E pl(&Occil.probabilityGeneratingFactory &coin.fst &count.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  twp_pures
  twp_bind pl(&count.fst #())
  isimp only [← expectation_preservation ν p F] at Hcredit
  iapply (hcount.wp (fun n => IterateCoin.credit p n F) (measurable_of_countable _) _)
    $$ Hcredit
  iintro %n Hcredit
  twp_pure
  twp_pure
  twp_pure
  simp only [iterateCoin_openRec, iterateCoin_closeRec]
  twp_bind pl(&Occil.iterateCoin &coin.fst #int (n : ℤ))
  iapply (tglWp_mono fun _ => tglWp_value)
  iapply (IterateCoin.twp_iterateCoin E p coin hcoin n F) $$ Hcredit

/-- Typed Bernoulli mixture specification. -/
theorem probabilityGeneratingFactory_distSpec (E : CoPset) (ν : MeasureTheory.Measure ℕ)
    [MeasureTheory.IsProbabilityMeasure ν] (p : unitInterval) (coin count : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (hcount : IsDistSpec (GF := GF) E pl(&count.fst #()) ν (fun n => Val.int (n : ℤ))) :
    IsDistSpec (GF := GF) E
      pl(&Occil.probabilityGeneratingFactory &coin.fst &count.fst #()) (law ν p) Val.bool where
  spec F _ := wand_entails (twp_probabilityGeneratingFactory E ν p coin count hcoin hcount F)

end specification

end

end SampLib.ProbabilityGeneratingFactory
