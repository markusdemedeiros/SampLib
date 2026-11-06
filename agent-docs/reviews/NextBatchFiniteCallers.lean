import SampLib.Discrete.Dice
import SampLib.Discrete.Hypergeometric
import SampLib.Discrete.PolyaEggenberger
import SampLib.Combinatorial.SampleWithoutReplacement
import SampLib.Combinatorial.SampleInOrder
import Metrology.Iris.LocalBI

/-! Independent finite-sampler clients, endpoints, and infinite-credit checks. -/

open Set ProbLang
open scoped ENNReal

namespace NextBatchFiniteAudit

noncomputable section

section mathematics

open MeasureTheory Measure

example (sides : ℕ) : SampLib.Dice.law sides 0 = dirac 0 := rfl

example (n : ℕ) : SampLib.Dice.law 1 n = dirac n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [SampLib.Dice.law, ih, SampLib.UniformInt.law, Measure.uniformOfFinset,
      Measure.dirac_prod_dirac, Measure.map_dirac' (measurable_of_countable _), Nat.add_comm]

example (sides n : ℕ) [NeZero sides] :
    ∫⁻ _total, (∞ : ℝ≥0∞) ∂SampLib.Dice.law sides n = ∞ := by simp

end mathematics

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example (E : CoPset) (n sides : ℕ) [NeZero sides] (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ total, F total ∂Dice.law sides n) ∗ I -∗
      tglWp E pl(&Occil.dice #int (n : ℤ) #int (sides : ℤ))
        (fun v : Val rT => iprop(∃ total : ℕ,
          ⌜v = Val.int (total : ℤ)⌝ ∗ ↯ (F total) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply ((Dice.dice_distSpec E n sides).wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %total Hcredit
  iexists total
  iframe Hcredit HI
  itrivial

#print axioms Dice.twp_dice
#print axioms Dice.dice_distSpec
#print axioms Dice.expectation

end

end NextBatchFiniteAudit

namespace NextBatchSubsetAudit

local instance {α : Type _} : MeasurableSpace (List α) := ⊤

open Set ProbLang
open scoped ENNReal
noncomputable section

section mathematics
open MeasureTheory Measure SampLib

theorem without_zero_law {α : Type _} (xs : List α) :
    SampleWithoutReplacement.law xs 0 = dirac () := by
  apply Measure.ext_of_singleton
  intro t
  rw [SampleWithoutReplacement.law_singleton]
  cases t
  simp only [Nat.descFactorial_zero, Nat.cast_one, inv_one]
  exact (Measure.dirac_apply_of_mem (by rfl)).symm

example {α : Type _} (x : α) :
    Fintype.card (SampleWithoutReplacement.Selection [x, x] 2) = 2 := by
  rw [SampleWithoutReplacement.selection_card]
  norm_num

example {α : Type _} (xs : List α) (k : ℕ) (hk : k ≤ xs.length) :
    letI : Fact (k ≤ xs.length) := ⟨hk⟩
    ∫⁻ _t, (∞ : ℝ≥0∞) ∂SampleWithoutReplacement.law xs k = ∞ := by
  let : Fact (k ≤ xs.length) := ⟨hk⟩
  simp

example {α : Type _} (xs : List α) :
    SampleInOrder.law xs 0 (Nat.zero_le _) = dirac [] := by
  simp [SampleInOrder.law]

example {α : Type _} (xs : List α) :
    SampleInOrder.law xs xs.length le_rfl = dirac xs := by
  simp [SampleInOrder.law, List.sublistsLen_length]

example {α : Type _} (x : α) :
    SampleInOrder.law [x, x] 1 (by simp) = dirac [x] := by
  simp [SampleInOrder.law, List.sublistsLen_succ_cons,
    show (2 : ℝ≥0∞)⁻¹ + 2⁻¹ = 1 by
      rw [← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)],
    smul_add, ← add_smul]

example {α : Type _} (xs : List α) (k : ℕ) (hk : k ≤ xs.length) :
    ∫⁻ _ys, (∞ : ℝ≥0∞) ∂SampleInOrder.law xs k hk = ∞ := by simp

end mathematics

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib
variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF] {α : Type _}
local bi (IProp GF)

example (E : CoPset) (encode : α → Val rT) (xs : List α) (k : ℕ)
    (hk : k ≤ xs.length) (F : SampleWithoutReplacement.Selection xs k → ℝ≥0∞)
    (I : IProp GF) :
    ⊢ ↯ (∫⁻ t, F t ∂SampleWithoutReplacement.law xs k) ∗ I -∗
      tglWp E pl(&Occil.sampleWithoutReplacement &(listVal encode xs).fst #int (k : ℤ))
        (fun v : Val rT => iprop(∃ t : SampleWithoutReplacement.Selection xs k,
          ⌜v = listVal encode (SampleWithoutReplacement.selected xs k t)⌝ ∗ ↯ (F t) ∗ I)) := by
  let : Fact (k ≤ xs.length) := ⟨hk⟩
  iintro ⟨Hcredit, HI⟩
  iapply ((SampleWithoutReplacement.sampleWithoutReplacement_distSpec E encode xs k hk).wp
    F (measurable_of_countable _) _) $$ Hcredit
  iintro %t Hcredit
  iexists t
  iframe Hcredit HI
  itrivial

example (E : CoPset) (encode : α → Val rT) (xs : List α) (k : ℕ)
    (hk : k ≤ xs.length) (F : List α → ℝ≥0∞) (hF : @Measurable _ _ ⊤ _ F)
    (I : IProp GF) :
    ⊢ ↯ (∫⁻ ys, F ys ∂SampleInOrder.law xs k hk) ∗ I -∗
      tglWp E pl(&Occil.sampleInOrder &(listVal encode xs).fst #int (k : ℤ))
        (fun v : Val rT => iprop(∃ ys : List α,
          ⌜v = listVal encode ys⌝ ∗ ↯ (F ys) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply ((SampleInOrder.sampleInOrder_distSpec E encode xs k hk).wp F hF _) $$ Hcredit
  iintro %ys Hcredit
  iexists ys
  iframe Hcredit HI
  itrivial

#print axioms SampleWithoutReplacement.twp_sampleWithoutReplacement
#print axioms SampleWithoutReplacement.sampleWithoutReplacement_distSpec
#print axioms SampleWithoutReplacement.expectation
#print axioms SampleWithoutReplacement.law_singleton
#print axioms SampleInOrder.sampleInOrder_distSpec
#print axioms SampleInOrder.expectation

end
end NextBatchSubsetAudit

namespace NextBatchUrnAudit

open Set ProbLang
open scoped ENNReal
noncomputable section

section mathematics
open MeasureTheory Measure SampLib

example (ones zeros : ℕ) : Hypergeometric.law 0 ones zeros = dirac 0 := by
  refine Measure.ext_of_lintegral _ fun F _hF => ?_
  rw [Hypergeometric.expectation_zero, lintegral_dirac]

example (ones zeros reinforcement : ℕ) :
    PolyaEggenberger.law 0 ones zeros reinforcement = dirac 0 := by
  simp [PolyaEggenberger.law, PolyaEggenberger.wordLaw,
    Measure.map_dirac' (measurable_of_countable _)]

example : PolyaEggenberger.wordLaw 2 1 2 0 {[true, false]} = (2 / 9 : ℝ≥0∞) := by
  have h := PolyaEggenberger.word_mass [true, false] 1 2 0 (Or.inr (by omega))
  simpa [PolyaEggenberger.rising] using h

example : PolyaEggenberger.wordLaw 2 1 1 1 {[true, false]} =
    PolyaEggenberger.wordLaw 2 1 1 1 {[false, true]} := by
  rw [show 2 = [true, false].length by rfl,
    PolyaEggenberger.word_mass [true, false] 1 1 1 (Or.inr (by omega)),
    show [true, false].length = [false, true].length by rfl,
    PolyaEggenberger.word_mass [false, true] 1 1 1 (Or.inr (by omega))]
  norm_num [PolyaEggenberger.rising]

example (n ones zeros : ℕ) [Fact (n ≤ ones + zeros)] :
    ∫⁻ _k, (∞ : ℝ≥0∞) ∂Hypergeometric.law n ones zeros = ∞ := by simp

example (n ones zeros reinforcement : ℕ) :
    ∫⁻ _k, (∞ : ℝ≥0∞) ∂PolyaEggenberger.law n ones zeros reinforcement = ∞ := by simp

end mathematics

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib
variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example (E : CoPset) (n ones zeros : ℕ) [Fact (n ≤ ones + zeros)]
    (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂Hypergeometric.law n ones zeros) ∗ I -∗
      tglWp E pl(&Occil.hypergeometric #int (n : ℤ) #int (ones : ℤ) #int (zeros : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply ((Hypergeometric.hypergeometric_distSpec E n ones zeros).wp F
    (measurable_of_countable _) _) $$ Hcredit
  iintro %k Hcredit
  iexists k
  iframe Hcredit HI
  itrivial

example (E : CoPset) (n ones zeros reinforcement : ℕ) (h : n = 0 ∨ 0 < ones + zeros)
    (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂PolyaEggenberger.law n ones zeros reinforcement) ∗ I -∗
      tglWp E pl(&Occil.polyaEggenberger #int (n : ℤ) #int (ones : ℤ)
        #int (zeros : ℤ) #int (reinforcement : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply ((PolyaEggenberger.polyaEggenberger_distSpec E n ones zeros reinforcement h).wp F
    (measurable_of_countable _) _) $$ Hcredit
  iintro %k Hcredit
  iexists k
  iframe Hcredit HI
  itrivial

local instance : Fact (0 ≤ (0 : ℕ) + 0) := ⟨by omega⟩
local instance : Fact (3 ≤ (0 : ℕ) + 4) := ⟨by omega⟩
local instance : Fact (4 ≤ (2 : ℕ) + 2) := ⟨by omega⟩

example (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.hypergeometric #int (0 : ℤ) #int (0 : ℤ) #int (0 : ℤ))
      (Hypergeometric.law 0 0 0) (fun k : ℕ => Val.int (k : ℤ)) := by
  let : Fact (0 ≤ (0 : ℕ) + 0) := ⟨by omega⟩
  exact Hypergeometric.hypergeometric_distSpec E 0 0 0

example (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.hypergeometric #int (3 : ℤ) #int (0 : ℤ) #int (4 : ℤ))
      (Hypergeometric.law 3 0 4) (fun k : ℕ => Val.int (k : ℤ)) := by
  let : Fact (3 ≤ (0 : ℕ) + 4) := ⟨by omega⟩
  exact Hypergeometric.hypergeometric_distSpec E 3 0 4

example (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.hypergeometric #int (4 : ℤ) #int (2 : ℤ) #int (2 : ℤ))
      (Hypergeometric.law 4 2 2) (fun k : ℕ => Val.int (k : ℤ)) := by
  let : Fact (4 ≤ (2 : ℕ) + 2) := ⟨by omega⟩
  exact Hypergeometric.hypergeometric_distSpec E 4 2 2

example (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.polyaEggenberger #int (0 : ℤ) #int (0 : ℤ)
      #int (0 : ℤ) #int (0 : ℤ)) (PolyaEggenberger.law 0 0 0 0)
      (fun k : ℕ => Val.int (k : ℤ)) :=
  PolyaEggenberger.polyaEggenberger_distSpec E 0 0 0 0 (Or.inl rfl)

example (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.polyaEggenberger #int (3 : ℤ) #int (0 : ℤ)
      #int (2 : ℤ) #int (0 : ℤ)) (PolyaEggenberger.law 3 0 2 0)
      (fun k : ℕ => Val.int (k : ℤ)) :=
  PolyaEggenberger.polyaEggenberger_distSpec E 3 0 2 0 (Or.inr (by omega))

#print axioms Hypergeometric.twp_hypergeometric
#print axioms Hypergeometric.hypergeometric_distSpec
#print axioms Hypergeometric.expectation
#print axioms Hypergeometric.expectation_coin
#print axioms PolyaEggenberger.twp_polyaEggenberger
#print axioms PolyaEggenberger.polyaEggenberger_distSpec
#print axioms PolyaEggenberger.expectation
#print axioms PolyaEggenberger.word_mass
#print axioms Urn.pmf_true
#print axioms Urn.pmf_false

end
end NextBatchUrnAudit
