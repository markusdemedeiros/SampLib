import SampLib.Distributions.Compositions
import SampLib.Syntax.Compositions

/-! # Uniform positive compositions

Sample increasing interior cuts uniformly, then take their successive gaps.
The cut-to-gap bijection and the resulting uniform law are proved separately.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.PositiveComposition

noncomputable section

local instance : MeasurableSpace (List ℤ) := ⊤

private def differences {rT : Type _} (total : ℤ) : Exp rT := pl%
  rec go prev xs := case! xs
    | inl(u) => inr((#int total - prev, inl(#())))
    | inr(p) => inr((fst(p) - prev, go (fst(p)) (snd(p))))

private theorem valid_test (n total : ℕ) (hn : 0 < n) (ht : n ≤ total) :
    Bool.or (decide ((n : ℤ) ≤ 0)) (decide ((total : ℤ) < n)) = false := by
  simp [Nat.ne_of_gt hn, not_lt.mpr (Int.ofNat_le.mpr ht)]

private theorem total_cast (n total : ℕ) (hn : 0 < n) (ht : n ≤ total) :
    (total : ℤ) = 1 + ((total - 1 : ℕ) : ℤ) := by omega

private theorem count_cast (n : ℕ) (hn : 0 < n) :
    (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) := by omega

private theorem encode_cons {rT : Type _} [ProbLangℝ rT] (x : ℤ) (xs : List ℤ) :
    pl(inr((#int x, {Exp.ofVal (listVal Val.int xs)}))) =
      Exp.ofVal (listVal Val.int (x :: xs) : Val rT) := by simp [Exp.ofVal, listVal]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_differences (E : CoPset) (total prev : ℤ) (cuts : List ℤ) :
    ⊢ tglWp E pl(&(differences (rT := rT) total) #int prev &(listVal Val.int cuts).fst)
      (fun v : Val rT => iprop(⌜v = listVal Val.int (Compositions.gaps total prev cuts)⌝)) := by
  induction cuts generalizing prev with
  | nil =>
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    ipureintro
    exact Val.ext rfl
  | cons x xs IH =>
    simp only [listVal]
    iterate 7 twp_pure
    isimp only [Exp.ofVal]
    twp_bind pl(&(differences (rT := rT) total) #int x &(listVal Val.int xs).fst)
    iapply tglWp_wand
    isplitl []
    · iapply IH x
    iintro %v %hv
    subst v
    twp_pure
    twp_pure
    rw [encode_cons]
    iapply (tglWp_value (v := listVal Val.int
      ((x - prev) :: Compositions.gaps total x xs)))
    ipureintro
    exact Val.ext rfl

variable [ProbLangDist.IsUniformInt rT]

/-- Every ordered positive composition has the same binomial-coefficient mass. -/
theorem positiveComposition_distSpec (E : CoPset) (n total : ℕ)
    (hn : 0 < n) (ht : n ≤ total) :
    IsDistSpec (GF := GF) E pl(&Occil.positiveComposition #int (n : ℤ) #int (total : ℤ))
      (Compositions.law n total hn ht) (listVal Val.int) where
  spec F _ := by
    have hk : n - 1 ≤ (IntegerRange.interval 1 (total - 1)).length := by
      rw [Compositions.interval_length]
      omega
    have hrange := IntegerRange.twp_intRange (rT := rT) (GF := GF) E 1 (total - 1)
    rw [← total_cast n total hn ht] at hrange
    iintro Hcredit
    twp_pures
    rw [valid_test n total hn ht]
    twp_pure
    twp_pure
    simp only [IntegerRange.intRange_openRec, IntegerRange.intRange_closeRec,
      SampleInOrder.sampleInOrder_openRec, SampleInOrder.sampleInOrder_closeRec]
    twp_bind pl(&Occil.intRange #1 #int (total : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply hrange
    iintro %v %hv
    subst v
    rw [count_cast n hn]
    twp_bind pl(&Occil.sampleInOrder
      &(listVal Val.int (IntegerRange.interval 1 (total - 1))).fst
      #int ((n - 1 : ℕ) : ℤ))
    isimp only [← Compositions.expectation n total hn ht F] at Hcredit
    iapply ((SampleInOrder.sampleInOrder_distSpec E Val.int
      (IntegerRange.interval 1 (total - 1)) (n - 1) hk).wp
      (fun cuts => F (Compositions.gaps total 0 cuts)) (measurable_of_countable _) _) $$ Hcredit
    iintro %cuts Hcredit
    twp_pure
    twp_pure
    have hgap := twp_differences (rT := rT) (GF := GF) E total 0 cuts
    simp [differences, Exp.close, Exp.closeRec] at hgap
    iapply tglWp_wand
    isplitl []
    · iapply hgap
    iintro %v %hv
    iexists Compositions.gaps total 0 cuts
    iframe Hcredit
    ipureintro
    exact hv

end specification

end

end SampLib.PositiveComposition
