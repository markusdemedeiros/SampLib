import SampLib.Weighted.Support.FenwickTable
import SampLib.Weighted.Support.FenwickCategory
import SampLib.Weighted.Laws.FenwickSearch
import SampLib.Core.OwnedDistSpec
import SampLib.Weighted.Support.PowerOfTwoCeiling
import Samplers.Weighted.Dynamic

/-! # Categorical draws by Fenwick-tree inversion

Binary lifting locates the cumulative interval of a uniform rank. Each tree read
preserves the table, so the same owned specification supports independent draws.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.FenwickDraw

/-- Uniform cumulative rank has the categorical expectation, including infinite credits. -/
theorem expectation {n : ℕ} (w : Fin n → ℕ) (F : ℕ → ℝ≥0∞) :
    (∑ rank ∈ Finset.range (List.ofFn w).sum,
        F (WeightedChoice.category (List.ofFn w) rank)) / (List.ofFn w).sum =
      ∫⁻ i, F i ∂WeightedChoice.law (List.ofFn w) := by
  rw [WeightedChoice.rank_partition, WeightedChoice.lintegral_law]

private def search {rT : Type} (n : ℕ) (tree : Loc) : Exp rT := pl%
  rec search step index remaining :=
    if step = #0 then index else
      let next := index + step;
      if #int (n : ℤ) < next then search (step / #2) index remaining else
        let mass := !(#loc tree +ₗ next);
        if mass <= remaining then search (step / #2) next (remaining - mass)
        else search (step / #2) index remaining

private theorem zero_test {rT : Type} [BEq rT] (step : ℕ) :
    ((BaseLit.int (step : ℤ) : BaseLit rT) == .int 0) = decide (step = 0) := by
  change ((step : ℤ) == 0) = decide (step = 0)
  simp [beq_eq_decide]

private theorem next_test (n index step : ℕ) :
    decide ((n : ℤ) < (index : ℤ) + step) = decide (n < index + step) := by
  norm_cast

private theorem mass_test (mass remaining : ℕ) :
    decide ((mass : ℤ) ≤ remaining) = decide (mass ≤ remaining) := by simp

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_search (E : CoPset) {n : ℕ} (w : Fin n → ℕ) (tree : Loc)
    (target selected : ℕ) (hq : FenwickMath.Selects w target selected)
    (step index remaining : ℕ)
    (h : FenwickMath.SearchInvariant w target selected step index remaining) :
    Array.owns tree (List.ofFn (FenwickTable.natVal (rT := rT) ∘
        (fun i : Fin (n + 1) => FenwickMath.cell w i.val))) ⊢
      tglWp E pl(&(search n tree) #int (step : ℤ) #int (index : ℤ)
          #int (remaining : ℤ))
        (fun v => iprop(⌜v = Val.int (selected : ℤ)⌝ ∗
          Array.owns tree (List.ofFn (FenwickTable.natVal (rT := rT) ∘
            (fun i : Fin (n + 1) => FenwickMath.cell w i.val))))) := by
  induction step using Nat.strong_induction_on generalizing index remaining with
  | h step IH =>
    by_cases hs : step = 0
    · subst step
      have hi := h.at_zero
      iintro Htree
      twp_pures
      twp_value
      imodintro
      iframe Htree
      ipureintro
      exact congrArg Val.int (congrArg (fun x : ℕ => (x : ℤ)) hi)
    · have hp := Nat.pos_of_ne_zero hs
      have hhalf := FenwickMath.quotient_lt hp
      iintro Htree
      isimp only [search, Exp.close, Exp.closeRec]
      twp_pures
      rw [zero_test, decide_eq_false hs]
      twp_pures
      rw [next_test]
      by_cases hn : n < index + step
      · have hrec := IH (step / 2) hhalf index remaining (h.skip hq hp hn)
        dsimp [search, Exp.close, Exp.closeRec] at hrec
        rw [decide_eq_true hn]
        iterate 2 twp_pure
        simp only [Exp.ofVal]
        iapply hrec $$ Htree
      · let k : Fin (n + 1) :=
          ⟨index + step, Nat.lt_succ_of_le (Nat.le_of_not_gt hn)⟩
        rw [decide_eq_false hn]
        twp_pure
        rw [← Nat.cast_add]
        twp_bind pl(!(#loc tree +ₗ #int ((index + step : ℕ) : ℤ)))
        iapply tglWp_wand
        isplitl [Htree]
        · iapply (Array.twp_load_ofFn E tree
            (FenwickTable.natVal ∘ (fun i : Fin (n + 1) => FenwickMath.cell w i.val)) k)
            $$ Htree
        iintro %v ⟨%hv, Htree⟩
        subst v
        twp_pures
        rw [mass_test]
        by_cases hm : FenwickMath.cell w (index + step) ≤ remaining
        · have hrec := IH (step / 2) hhalf (index + step)
            (remaining - FenwickMath.cell w (index + step)) (h.advance hq hp hm)
          dsimp [search, Exp.close, Exp.closeRec] at hrec
          rw [decide_eq_true hm]
          iterate 3 twp_pure
          rw [← Nat.cast_sub hm]
          simp only [Exp.ofVal, Nat.cast_add]
          iapply hrec $$ Htree
        · have hrec := IH (step / 2) hhalf index remaining
            (h.stay hq hp (Nat.lt_of_not_ge hm))
          dsimp [search, Exp.close, Exp.closeRec] at hrec
          rw [decide_eq_false hm]
          iterate 2 twp_pure
          simp only [Exp.ofVal]
          iapply hrec $$ Htree

/-- Inverting a uniform rank gives the categorical law and retains the entire table. -/
theorem fenwickDraw_ownedDistSpec (E : CoPset) {n : ℕ} (w : Fin n → ℕ)
    [NeZero (List.ofFn w).sum] (total values tree : Loc) :
    IsOwnedDistSpec (rT := rT) (GF := GF) E (FenwickTable.owns w total values tree)
      pl(&Occil.WeightedVariants.fenwickDraw &(FenwickTable.value n total values tree).fst #())
      (WeightedChoice.law (List.ofFn w)) FenwickTable.natVal := by
  have hn : 0 < n := by
    by_contra h
    have hn : n = 0 := by omega
    subst n
    simpa using NeZero.ne (List.ofFn w).sum
  refine ⟨fun F _ => ?_⟩
  isimp only [FenwickTable.owns]
  iintro ⟨⟨Htotal, Hvalues, Htree⟩, Hcredit⟩
  isimp only [Occil.WeightedVariants.fenwickDraw, Exp.close, Exp.closeRec,
    UniformInt.uniformInt_closeRec, PowerOfTwoCeiling.powerOfTwoCeiling_closeRec]
  twp_pures
  isimp only [UniformInt.uniformInt_openRec, UniformInt.uniformInt_closeRec,
    PowerOfTwoCeiling.powerOfTwoCeiling_openRec, PowerOfTwoCeiling.powerOfTwoCeiling_closeRec]
  twp_bind pl(!#loc total)
  iapply twp_load
  iframe Htotal
  iintro Htotal
  twp_bind pl(&Occil.uniformInt #int ((List.ofFn w).sum : ℤ))
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply (UniformInt.twp_uniformInt E (List.ofFn w).sum
      (NeZero.pos _) (fun rank => F (WeightedChoice.category (List.ofFn w) rank)))
    isimp only [← expectation w F] at Hcredit
    iexact Hcredit
  iintro %v ⟨%rank, %hv, %hr, Hcredit⟩
  subst v
  have hq := FenwickCategory.category_selects w rank hr
  have hinit := FenwickMath.SearchInvariant.initial w hq
    ⟨Nat.clog 2 n, rfl⟩ (PowerOfTwoCeiling.le_width n)
  twp_pure
  isimp only [PowerOfTwoCeiling.powerOfTwoCeiling_openRec]
  twp_pure
  twp_bind pl(&Occil.Weighted.powerOfTwoCeiling #int (n : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply PowerOfTwoCeiling.twp_powerOfTwoCeiling E n hn
  iintro %v %hv
  subst v
  twp_bind pl(&(search n tree) #int (PowerOfTwoCeiling.width n : ℤ) #0 #int (rank : ℤ))
  iapply tglWp_wand
  isplitl [Htree]
  · have hsearch := twp_search (GF := GF) E w tree rank _ hq _ 0 rank hinit
    simp only [Nat.cast_zero] at hsearch
    isimp only [PowerOfTwoCeiling.width]
    iapply hsearch $$ Htree
  iintro %v ⟨%hv, Htree⟩
  iapply (tglWp_value (v := v))
  iexists WeightedChoice.category (List.ofFn w) rank
  iframe Htotal Hvalues Htree Hcredit
  itrivial

end specification

end SampLib.FenwickDraw
