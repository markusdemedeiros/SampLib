import SampLib.Samplers.Geometric
import SampLib.Samplers.OneDivOnePlus
import SampLib.CoinComplement
import Samplers.Discrete.Tails

/-! # Two-sided geometric sampling

A geometric magnitude is assigned either its nonnegative position or the
corresponding negative position. The reciprocal selector balances the two tails.
-/

open Set ProbLang
open scoped ENNReal

namespace SampLib.SymmetricGeometric

noncomputable section

section mathematics

open MeasureTheory

/-- Place a geometric count on the selected side of zero. -/
def signed (n : ℕ) (b : Bool) : ℤ := if b then n else -1 - (n : ℤ)

/-- The two-sided law, including its degenerate limit at success probability one. -/
def law (p : unitInterval) : Measure ℤ :=
  ((Geometric.law p).prod (OneDivOnePlus.law (unitInterval.symm p))).map
    (fun z => signed z.1 z.2)

instance (p : unitInterval) : IsProbabilityMeasure (law p) where
  measure_univ := by
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- Each nonnegative atom is a geometric atom times the positive-side mass. -/
theorem law_nonneg (p : unitInterval) (n : ℕ) :
    law p {(n : ℤ)} = Geometric.law p {n} *
      OneDivOnePlus.law (unitInterval.symm p) {true} := by
  have hpre : (fun z : ℕ × Bool => signed z.1 z.2) ⁻¹' {(n : ℤ)} =
      ({n} : Set ℕ) ×ˢ {true} := by
    ext ⟨k, b⟩
    cases b <;> simp [signed]; omega
  rw [law, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    hpre, Measure.prod_prod]

/-- Negative atoms form the other geometric tail, shifted one place below zero. -/
theorem law_neg (p : unitInterval) (n : ℕ) :
    law p {-1 - (n : ℤ)} = Geometric.law p {n} *
      OneDivOnePlus.law (unitInterval.symm p) {false} := by
  have hpre : (fun z : ℕ × Bool => signed z.1 z.2) ⁻¹' {-1 - (n : ℤ)} =
      ({n} : Set ℕ) ×ˢ {false} := by
    ext ⟨k, b⟩
    cases b <;> simp [signed]; omega
  rw [law, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    hpre, Measure.prod_prod]

private theorem side_true (p : unitInterval) :
    OneDivOnePlus.law (unitInterval.symm p) {true} =
      ENNReal.ofReal (1 / (2 - (p : ℝ))) := by
  simp [OneDivOnePlus.law, RealCoin.law, RealCoin.pmf, OneDivOnePlus.bias,
    EvenParity.bias, unitInterval.coe_symm_eq,
    show 1 + (1 - (p : ℝ)) = 2 - (p : ℝ) by ring]

private theorem side_false (p : unitInterval) :
    OneDivOnePlus.law (unitInterval.symm p) {false} =
      ENNReal.ofReal ((1 - (p : ℝ)) / (2 - (p : ℝ))) := by
  have hd : (0 : ℝ) < 2 - (p : ℝ) := by linarith [p.2.2]
  have he : 1 - 1 / (2 - (p : ℝ)) = (1 - (p : ℝ)) / (2 - (p : ℝ)) := by
    field_simp
    ring
  simp [OneDivOnePlus.law, RealCoin.law, RealCoin.pmf, OneDivOnePlus.bias,
    EvenParity.bias, unitInterval.coe_symm_eq,
    show 1 + (1 - (p : ℝ)) = 2 - (p : ℝ) by ring]
  exact congrArg ENNReal.ofReal (by simpa only [one_div] using he)

/-- The nonnegative tail has the standard normalized two-sided geometric mass. -/
theorem nonneg_mass (p : unitInterval) (hp : 0 < (p : ℝ)) (n : ℕ) :
    law p {(n : ℤ)} = ENNReal.ofReal ((1 - (p : ℝ)) ^ n * p / (2 - (p : ℝ))) := by
  have hpne : p ≠ 0 := by intro he; simp [he] at hp
  rw [law_nonneg, ProbabilityTheory.geometricMeasure_singleton hpne, side_true,
    ← ENNReal.ofReal_mul (ProbabilityTheory.geometricMeasure_nonneg p n)]
  congr 1
  ring

/-- The negative tail has exactly the same mass as its reflection about zero. -/
theorem neg_mass (p : unitInterval) (hp : 0 < (p : ℝ)) (n : ℕ) :
    law p {-1 - (n : ℤ)} =
      ENNReal.ofReal ((1 - (p : ℝ)) ^ (n + 1) * p / (2 - (p : ℝ))) := by
  have hpne : p ≠ 0 := by intro he; simp [he] at hp
  rw [law_neg, ProbabilityTheory.geometricMeasure_singleton hpne, side_false,
    ← ENNReal.ofReal_mul (ProbabilityTheory.geometricMeasure_nonneg p n)]
  congr 1
  rw [pow_succ]
  ring

/-- Conditional signed expectation after observing the geometric magnitude. -/
def continuation (p : unitInterval) (F : ℤ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ b, F (signed n b) ∂OneDivOnePlus.law (unitInterval.symm p)

/-- Independent magnitude and side give the signed product expectation. -/
theorem expectation (p : unitInterval) (F : ℤ → ℝ≥0∞) :
    ∫⁻ n, continuation p F n ∂Geometric.law p = ∫⁻ z, F z ∂law p := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    lintegral_prod _ (measurable_of_countable _).aemeasurable]
  rfl

end mathematics

private theorem geometric_open {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.geometric = Occil.geometric :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem geometric_close {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.geometric : Exp rT) = Occil.geometric :=
  Exp.closeRec_fresh x _ k (by simp [Occil.geometric, Exp.fv])

private theorem reciprocal_open {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.oneDivOnePlus = Occil.oneDivOnePlus :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem reciprocal_close {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.oneDivOnePlus : Exp rT) = Occil.oneDivOnePlus :=
  Exp.closeRec_fresh x _ k (by simp [Occil.oneDivOnePlus, Exp.fv, FairCoin.fairCoin_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The signed geometric law from any coin with positive success probability. -/
theorem twp_symmetricGeometric (E : CoPset) (p : unitInterval) (hp : 0 < (p : ℝ))
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : ℤ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ z, F z ∂law p) -∗
      tglWp E pl(&Occil.DiscreteExtra.symmetricGeometric &coin.fst #())
        (fun v : Val rT => iprop(∃ z : ℤ, ⌜v = Val.int z⌝ ∗ ↯ (F z))) := by
  iintro Hcredit
  iterate 2 twp_pure
  simp only [geometric_close, geometric_open, reciprocal_close, reciprocal_open]
  twp_bind pl(&Occil.geometric &coin.fst #())
  isimp only [← expectation p F] at Hcredit
  iapply ((Geometric.geometric_distSpec E p hp coin hcoin).wp (continuation p F)
    (measurable_of_countable _) _) $$ Hcredit
  iintro %n Hcredit
  twp_pure
  twp_bind pl(&Occil.oneDivOnePlus &(CoinComplement.callback coin).fst #())
  isimp only [continuation] at Hcredit
  iapply ((OneDivOnePlus.oneDivOnePlus_distSpec E (unitInterval.symm p)
    (CoinComplement.callback coin)
    (CoinComplement.distSpec E p coin hcoin)).wp (fun b => F (signed n b))
    (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  cases b <;> twp_pures <;> twp_value <;> imodintro
  · iexists (-1 - (n : ℤ))
    isimp only [signed, Bool.false_eq_true, ite_false] at Hcredit
    iframe Hcredit
    itrivial
  · iexists (n : ℤ)
    isimp only [signed, ite_true] at Hcredit
    iframe Hcredit
    itrivial

/-- Typed two-sided geometric specification, including the deterministic endpoint. -/
theorem symmetricGeometric_distSpec (E : CoPset) (p : unitInterval) (hp : 0 < (p : ℝ))
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.DiscreteExtra.symmetricGeometric &coin.fst #())
      (law p) Val.int where
  spec F _ := wand_entails (twp_symmetricGeometric E p hp coin hcoin F)

end specification

end

end SampLib.SymmetricGeometric
