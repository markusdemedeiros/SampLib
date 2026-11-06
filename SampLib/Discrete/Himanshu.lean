import SampLib.Discrete.Geometric
import SampLib.Continuous.IterateCoin
import Samplers.Discrete.Tails

/-! # Independent success-block counts

A block succeeds precisely when all its input flips succeed. The returned count
is therefore geometric with success probability `p^blockSize`.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.Himanshu

noncomputable section

abbrev law (p : unitInterval) (n : ℕ) := Geometric.law (IterateCoin.bias p n)

private def block {rT : Type _} (coin : Val rT) (n : ℕ) : Val rT :=
  ⟨.lam pl(&Occil.iterateCoin &coin.fst #int (n : ℤ)), .lam (by is_lc), by is_lc⟩

private theorem geometric_open {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.geometric = Occil.geometric :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem geometric_close {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.geometric : Exp rT) = Occil.geometric :=
  Exp.closeRec_fresh x _ k (by simp [Occil.geometric, Exp.fv])

private theorem iterate_open {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.iterateCoin = Occil.iterateCoin :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem iterate_close {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.iterateCoin : Exp rT) = Occil.iterateCoin :=
  Exp.closeRec_fresh x _ k (by simp [Occil.iterateCoin, Exp.fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem block_spec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) (n : ℕ) :
    IsDistSpec (GF := GF) E pl(&(block coin n).fst #()) (IterateCoin.law p n) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    simp only [iterate_open]
    iapply ((IterateCoin.iterateCoin_distSpec E p coin hcoin n).spec F hF)
    iexact Hcredit

private theorem positive_test (n : ℕ) (hn : 0 < n) :
    decide ((n : ℤ) ≤ 0) = false := decide_eq_false (by omega)

/-- Each independent block is one trial of the verified geometric sampler. -/
theorem twp_himanshu (E : CoPset) (p : unitInterval) (hp : 0 < (p : ℝ))
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (n : ℕ) (hn : 0 < n) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ k, F k ∂law p n) -∗
      tglWp E pl(&Occil.DiscreteExtra.himanshu &coin.fst #int (n : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k))) := by
  iintro Hcredit
  twp_pures
  rw [positive_test n hn]
  twp_pure
  simp only [geometric_close, geometric_open, iterate_close, iterate_open]
  twp_bind pl(&Occil.geometric &(block coin n).fst #())
  iapply (tglWp_mono fun _ => tglWp_value)
  isimp only [law] at Hcredit
  iapply ((Geometric.geometric_distSpec E (IterateCoin.bias p n) (pow_pos hp n)
    (block coin n) (block_spec E p coin hcoin n)).spec F (measurable_of_countable _))
  iexact Hcredit

/-- Typed law for every positive block size and positive input success probability. -/
theorem himanshu_distSpec (E : CoPset) (p : unitInterval) (hp : 0 < (p : ℝ))
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (n : ℕ) (hn : 0 < n) :
    IsDistSpec (GF := GF) E pl(&Occil.DiscreteExtra.himanshu &coin.fst #int (n : ℤ))
      (law p n) (fun k : ℕ => Val.int (k : ℤ)) where
  spec F _ := wand_entails (twp_himanshu E p hp coin hcoin n hn F)

end specification

end

end SampLib.Himanshu
