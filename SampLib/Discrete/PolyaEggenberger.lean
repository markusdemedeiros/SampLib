import SampLib.Common.Laws.Urn
import Samplers.Discrete
import Metrology.Iris.LocalBI
import SampLib.Discrete.Laws.PolyaEggenberger
import SampLib.Uniform.RationalCoin

/-! # Pólya–Eggenberger sampling

The CTE proof draws the first color with a rational coin, reinforces that color,
and recurses on the remaining draws.
-/

open Set ProbLang
open scoped ENNReal

namespace SampLib.PolyaEggenberger

noncomputable section

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Reinforced urn counts, allowing both absent colors and zero reinforcement. -/
theorem twp_polyaEggenberger (E : CoPset) (n ones zeros reinforcement : ℕ)
    (h : n = 0 ∨ 0 < ones + zeros) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ k, F k ∂law n ones zeros reinforcement) -∗
      tglWp E pl(&Occil.polyaEggenberger #int (n : ℤ) #int (ones : ℤ)
        #int (zeros : ℤ) #int (reinforcement : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k))) := by
  induction n generalizing ones zeros F with
  | zero =>
    iintro Hcredit
    twp_pures
    twp_value
    imodintro
    iexists 0
    isimp only [law, wordLaw, MeasureTheory.lintegral_map (measurable_of_countable _)
      (measurable_of_countable _), MeasureTheory.lintegral_dirac, List.count_nil] at Hcredit
    iframe Hcredit
    itrivial
  | succ n ih =>
    have ht : 0 < ones + zeros := h.resolve_left (Nat.succ_ne_zero n)
    have ht₁ : 0 < (ones + reinforcement) + zeros := by omega
    have ht₀ : 0 < ones + (zeros + reinforcement) := by omega
    have hcoin : IsDistSpec (GF := GF) E
        pl(&Occil.rationalCoin #int (ones : ℤ) #int ((ones : ℤ) + zeros))
        (RealCoin.law (Urn.bias ones zeros)) Val.bool := by
      simpa only [Urn.bias, dite_eq_left ht, Nat.cast_add] using
        RationalCoin.rationalCoin_distSpec (GF := GF) E ones (ones + zeros)
          (by omega) (by omega) (by omega)
    iintro Hcredit
    iterate 16 twp_pure
    simp only [RationalCoin.rationalCoin_closeRec, RationalCoin.rationalCoin_openRec]
    twp_bind pl(&Occil.rationalCoin #int (ones : ℤ) #int ((ones : ℤ) + zeros))
    isimp only [← expectation n ones zeros reinforcement F] at Hcredit
    iapply (hcoin.wp (continuation n ones zeros reinforcement F)
      (measurable_of_countable _) _) $$ Hcredit
    iintro %b Hcredit
    cases b
    · iterate 3 twp_pure
      rw [Nat.cast_add_one, add_sub_cancel_right, ← Nat.cast_add]
      simp only [Exp.ofVal]
      twp_bind pl(&Occil.polyaEggenberger #int (n : ℤ) #int (ones : ℤ)
        #int ((zeros + reinforcement : ℕ) : ℤ) #int (reinforcement : ℤ))
      iapply tglWp_wand
      isplitl [Hcredit]
      · isimp only [continuation, Bool.false_eq_true, ite_false] at Hcredit
        iapply (ih ones (zeros + reinforcement) (Or.inr ht₀) F) $$ Hcredit
      iintro %v ⟨%k, %hv, Hcredit⟩
      iapply (tglWp_value (v := v))
      iexists k
      iframe Hcredit
      ipureintro
      exact hv
    · iterate 3 twp_pure
      rw [Nat.cast_add_one, add_sub_cancel_right, ← Nat.cast_add]
      simp only [Exp.ofVal]
      twp_bind pl(&Occil.polyaEggenberger #int (n : ℤ) #int ((ones + reinforcement : ℕ) : ℤ)
        #int (zeros : ℤ) #int (reinforcement : ℤ))
      iapply tglWp_wand
      isplitl [Hcredit]
      · isimp only [continuation, ite_true] at Hcredit
        iapply (ih (ones + reinforcement) zeros (Or.inr ht₁) (fun k => F (k + 1))) $$ Hcredit
      iintro %v ⟨%k, %hv, Hcredit⟩
      subst v
      twp_pures
      twp_value
      imodintro
      iexists k + 1
      iframe Hcredit
      ipureintro
      apply Val.ext
      simp [add_comm]

/-- Typed Pólya–Eggenberger law on the entire terminating natural-input domain. -/
theorem polyaEggenberger_distSpec (E : CoPset) (n ones zeros reinforcement : ℕ)
    (h : n = 0 ∨ 0 < ones + zeros) :
    IsDistSpec (GF := GF) E
      pl(&Occil.polyaEggenberger #int (n : ℤ) #int (ones : ℤ)
        #int (zeros : ℤ) #int (reinforcement : ℤ))
      (law n ones zeros reinforcement) (fun k : ℕ => Val.int (k : ℤ)) where
  spec F _ := wand_entails (twp_polyaEggenberger E n ones zeros reinforcement h F)

end specification

end

end SampLib.PolyaEggenberger
