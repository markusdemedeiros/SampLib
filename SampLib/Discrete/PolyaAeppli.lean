import SampLib.Discrete.CompoundPoisson
import SampLib.Discrete.Geometric

/-! # Poisson clusters with positive geometric cluster sizes -/

open ProbLang
open scoped ENNReal NNReal

namespace SampLib.PolyaAeppli

noncomputable section

def jumpBias (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) : unitInterval :=
  PoissonRational.bias a b (lt_of_lt_of_le ha hab) hab

private theorem jumpBias_pos (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    0 < (jumpBias a b ha hab : ℝ) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  simp only [jumpBias, PoissonRational.bias, RationalCoin.bias, Int.cast_natCast]
  positivity

/-- A Poisson number of independent positive geometric cluster sizes. -/
abbrev law (rate : ℝ≥0) (p : unitInterval) :=
  CompoundPoisson.law rate (Geometric.law p) (fun n => ((n + 1 : ℕ) : ℤ))

private def coin {rT : Type _} (a b : ℕ) : Val rT :=
  ⟨.lam pl(&Occil.rationalCoin #int (a : ℤ) #int (b : ℤ)), .lam (by is_lc), by is_lc⟩

private def jump {rT : Type _} (a b : ℕ) : Val rT :=
  ⟨.lam pl(#1 + &Occil.geometric &(coin a b).fst #()), .lam (by is_lc), by is_lc⟩

private theorem geometric_open {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.geometric = Occil.geometric :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem geometric_close {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.geometric : Exp rT) = Occil.geometric :=
  Exp.closeRec_fresh x _ k (by simp [Occil.geometric, Exp.fv])

private theorem positive_test (a : ℕ) (ha : 0 < a) :
    decide ((a : ℤ) ≤ 0) = false := decide_eq_false (by omega)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem coin_distSpec (E : CoPset) (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    IsDistSpec (GF := GF) E pl(&(coin a b).fst #())
      (RealCoin.law (jumpBias a b ha hab)) Val.bool where
  spec F hF := by
    iintro Hcredit
    isimp only [jumpBias, PoissonRational.bias] at Hcredit
    twp_pure
    simp only [RationalCoin.rationalCoin_openRec]
    iapply (RationalCoin.rationalCoin_distSpec E a b (Int.natCast_nonneg _)
      (Int.natCast_pos.mpr (lt_of_lt_of_le ha hab)) (Int.ofNat_le.mpr hab)).spec F hF
      $$ Hcredit

private theorem jump_distSpec (E : CoPset) (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    IsDistSpec (GF := GF) E pl(&(jump a b).fst #()) (Geometric.law (jumpBias a b ha hab))
      (fun n : ℕ => Val.int ((n + 1 : ℕ) : ℤ)) where
  spec F hF := by
    iintro Hcredit
    twp_pure
    simp only [geometric_open]
    twp_bind pl(&Occil.geometric &(coin a b).fst #())
    iapply ((Geometric.geometric_distSpec E (jumpBias a b ha hab)
      (jumpBias_pos a b ha hab) (coin a b) (coin_distSpec E a b ha hab)).wp F hF _)
      $$ Hcredit
    iintro %n Hcredit
    twp_pures
    rw [add_comm (1 : ℤ), ← Nat.cast_add_one]
    twp_value
    imodintro
    iexists n
    iframe Hcredit
    itrivial

theorem twp_polyaAeppli (E : CoPset) (x y a b : ℕ) (hy : 0 < y)
    (ha : 0 < a) (hab : a ≤ b) (F : ℤ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ z, F z ∂law (PoissonRational.rate x y) (jumpBias a b ha hab)) -∗
      tglWp E pl(&Occil.DiscreteExtra.polyaAeppli
        #int (x : ℤ) #int (y : ℤ) #int (a : ℤ) #int (b : ℤ))
        (fun v : Val rT => iprop(∃ z : ℤ, ⌜v = Val.int z⌝ ∗ ↯ (F z))) := by
  iintro Hcredit
  iterate 5 twp_pure
  rw [positive_test a ha]
  twp_pure
  simp only [CompoundPoisson.compoundPoisson_openRec,
    CompoundPoisson.compoundPoisson_closeRec, geometric_open, geometric_close,
    RationalCoin.rationalCoin_openRec, RationalCoin.rationalCoin_closeRec]
  have h := CompoundPoisson.twp_compoundPoisson (rT := rT) (GF := GF) E x y hy
    (Geometric.law (jumpBias a b ha hab))
    (fun n => ((n + 1 : ℕ) : ℤ)) (jump a b) (jump_distSpec E a b ha hab) F
  simp only [jump, coin] at h
  iapply h $$ Hcredit

theorem polyaAeppli_distSpec (E : CoPset) (x y a b : ℕ) (hy : 0 < y)
    (ha : 0 < a) (hab : a ≤ b) :
    IsDistSpec (GF := GF) E pl(&Occil.DiscreteExtra.polyaAeppli
      #int (x : ℤ) #int (y : ℤ) #int (a : ℤ) #int (b : ℤ))
      (law (PoissonRational.rate x y) (jumpBias a b ha hab)) Val.int where
  spec F _ := wand_entails (twp_polyaAeppli E x y a b hy ha hab F)

end specification

end

end SampLib.PolyaAeppli
