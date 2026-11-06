import SampLib.Discrete.CompoundPoisson

/-! # Poisson clusters with Poisson cluster sizes -/

open ProbLang
open scoped ENNReal NNReal

namespace SampLib.NeymanTypeA

noncomputable section

/-- A Poisson number of independent Poisson cluster sizes. -/
abbrev law (rate clusterRate : ℝ≥0) :=
  CompoundPoisson.law rate (ProbabilityTheory.poissonMeasure clusterRate) (fun n => (n : ℤ))

private def callback {rT : Type _} (x y : ℕ) : Val rT :=
  ⟨.lam pl(&Occil.poissonRational #int (x : ℤ) #int (y : ℤ)), .lam (by is_lc), by is_lc⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem callback_distSpec (E : CoPset) (x y : ℕ) (hy : 0 < y) :
    IsDistSpec (GF := GF) E pl(&(callback x y).fst #())
      (ProbabilityTheory.poissonMeasure (PoissonRational.rate x y))
      (fun n : ℕ => Val.int (n : ℤ)) where
  spec F hF := by
    iintro Hcredit
    twp_pure
    simp only [PoissonRational.poissonRational_openRec]
    iapply (PoissonRational.poissonRational_distSpec E x y hy).spec F hF $$ Hcredit

theorem twp_neymanTypeA (E : CoPset) (a b c d : ℕ) (hb : 0 < b) (hd : 0 < d)
    (F : ℤ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ z, F z ∂law (PoissonRational.rate a b) (PoissonRational.rate c d)) -∗
      tglWp E pl(&Occil.DiscreteExtra.neymanTypeA
        #int (a : ℤ) #int (b : ℤ) #int (c : ℤ) #int (d : ℤ))
        (fun v : Val rT => iprop(∃ z : ℤ, ⌜v = Val.int z⌝ ∗ ↯ (F z))) := by
  iintro Hcredit
  iterate 4 twp_pure
  simp only [PoissonRational.poissonRational_openRec,
    PoissonRational.poissonRational_closeRec, CompoundPoisson.compoundPoisson_openRec,
    CompoundPoisson.compoundPoisson_closeRec]
  have h := CompoundPoisson.twp_compoundPoisson (rT := rT) (GF := GF) E a b hb
    (ProbabilityTheory.poissonMeasure (PoissonRational.rate c d))
    (fun n => (n : ℤ)) (callback c d) (callback_distSpec E c d hd) F
  simp only [callback] at h
  iapply h $$ Hcredit

theorem neymanTypeA_distSpec (E : CoPset) (a b c d : ℕ) (hb : 0 < b) (hd : 0 < d) :
    IsDistSpec (GF := GF) E pl(&Occil.DiscreteExtra.neymanTypeA
      #int (a : ℤ) #int (b : ℤ) #int (c : ℤ) #int (d : ℤ))
      (law (PoissonRational.rate a b) (PoissonRational.rate c d)) Val.int where
  spec F _ := wand_entails (twp_neymanTypeA E a b c d hb hd F)

end specification

end

end SampLib.NeymanTypeA
