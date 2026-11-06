import SampLib.Uniform.UniformInt
import Samplers.Discrete
import Metrology.Iris.LocalBI

/-! # Sums of fair dice

The law is the convolution of independent uniforms on `1, …, sides`.
-/

open Set ProbLang
open scoped ENNReal

namespace SampLib.Dice

noncomputable section

section mathematics

open MeasureTheory Measure

/-- Sum of `n` independent `sides`-sided dice. -/
def law (sides : ℕ) : ℕ → Measure ℕ
  | 0 => dirac 0
  | n + 1 => ((law sides n).prod (UniformInt.law sides)).map
      (fun z => 1 + z.2 + z.1)

instance (sides n : ℕ) [NeZero sides] : IsProbabilityMeasure (law sides n) := by
  induction n with
  | zero => dsimp [law]; infer_instance
  | succ n ih =>
    let := ih
    constructor
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- Credit remaining for the new die after observing the other dice. -/
def continuation (sides : ℕ) (F : ℕ → ℝ≥0∞) (rest : ℕ) : ℝ≥0∞ :=
  ∫⁻ k, F (1 + k + rest) ∂UniformInt.law sides

/-- Independence identifies the nested expectation with the sum's convolution. -/
theorem expectation (sides n : ℕ) [NeZero sides] (F : ℕ → ℝ≥0∞) :
    ∫⁻ rest, continuation sides F rest ∂law sides n =
      ∫⁻ total, F total ∂law sides (n + 1) := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    lintegral_prod _ (measurable_of_countable _).aemeasurable]
  rfl

end mathematics

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem sides_test (sides : ℕ) [NeZero sides] :
    decide ((sides : ℤ) ≤ 0) = false := by
  simp [NeZero.ne sides]

theorem twp_dice (E : CoPset) (n sides : ℕ) [NeZero sides] (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ total, F total ∂law sides n) -∗
      tglWp E pl(&Occil.dice #int (n : ℤ) #int (sides : ℤ))
        (fun v : Val rT => iprop(∃ total : ℕ,
          ⌜v = Val.int (total : ℤ)⌝ ∗ ↯ (F total))) := by
  induction n generalizing F with
  | zero =>
    iintro Hcredit
    twp_pures
    simp only [Bool.false_or, sides_test]
    twp_pures
    twp_value
    imodintro
    iexists 0
    isimp only [law, MeasureTheory.lintegral_dirac] at Hcredit
    iframe Hcredit
    itrivial
  | succ n ih =>
    iintro Hcredit
    twp_pures
    simp only [Bool.false_or, sides_test]
    iterate 4 twp_pure
    rw [Nat.cast_add_one, add_sub_cancel_right]
    simp only [UniformInt.uniformInt_closeRec, UniformInt.uniformInt_openRec]
    twp_bind pl(&Occil.dice #int (n : ℤ) #int (sides : ℤ))
    iapply tglWp_wand
    isplitl [Hcredit]
    · isimp only [← expectation sides n F] at Hcredit
      iapply ih $$ Hcredit
    iintro %v ⟨%rest, %hv, Hcredit⟩
    subst v
    twp_bind pl(&Occil.uniformInt #int (sides : ℤ))
    isimp only [continuation] at Hcredit
    iapply ((UniformInt.uniformInt_distSpec E sides).wp
      (fun k => F (1 + k + rest)) (measurable_of_countable _) _) $$ Hcredit
    iintro %k Hcredit
    twp_pures
    twp_value
    imodintro
    iexists 1 + k + rest
    iframe Hcredit
    ipureintro
    simp only [Nat.cast_add, Nat.cast_one]

/-- Typed dice-sum specification, including a zero-dice sum. -/
theorem dice_distSpec (E : CoPset) (n sides : ℕ) [NeZero sides] :
    IsDistSpec (GF := GF) E pl(&Occil.dice #int (n : ℤ) #int (sides : ℤ))
      (law sides n) (fun total : ℕ => Val.int (total : ℤ)) where
  spec F _ := wand_entails (twp_dice E n sides F)

end specification

end

end SampLib.Dice
