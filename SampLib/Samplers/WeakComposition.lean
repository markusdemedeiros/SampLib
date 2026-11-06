import SampLib.Samplers.PositiveComposition

/-! # Uniform weak compositions

Subtracting one from each part is the stars-and-bars bijection from positive
compositions of `total+n` to nonnegative compositions of `total`.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.WeakComposition

noncomputable section

local instance : MeasurableSpace (List ℤ) := ⊤

private def subtract {rT : Type _} : Exp rT := pl%
  rec go xs := case! xs
    | inl(u) => inl(#())
    | inr(p) => inr((fst(p) - #1, go (snd(p))))

private theorem encode_cons {rT : Type _} [ProbLangℝ rT] (x : ℤ) (xs : List ℤ) :
    pl(inr((#int x, {Exp.ofVal (listVal Val.int xs)}))) =
      Exp.ofVal (listVal Val.int (x :: xs) : Val rT) := by simp [Exp.ofVal, listVal]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_subtract (E : CoPset) (xs : List ℤ) :
    ⊢ tglWp E pl(&subtract &(listVal Val.int xs).fst)
      (fun v : Val rT => iprop(⌜v = listVal Val.int (Compositions.subtractOne xs)⌝)) := by
  induction xs with
  | nil =>
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    ipureintro
    exact Val.ext rfl
  | cons x xs IH =>
    simp only [listVal]
    iterate 5 twp_pure
    twp_bind pl(&subtract &(listVal Val.int xs).fst)
    iapply tglWp_wand
    isplitl []
    · iapply IH
    iintro %v %hv
    subst v
    twp_pure
    twp_pure
    rw [encode_cons]
    iapply (tglWp_value (v := listVal Val.int ((x - 1) :: Compositions.subtractOne xs)))
    ipureintro
    exact Val.ext rfl

variable [ProbLangDist.IsUniformInt rT]

/-- Uniform nonnegative ordered parts, including the all-zero composition. -/
theorem weakComposition_distSpec (E : CoPset) (n total : ℕ) (hn : 0 < n) :
    IsDistSpec (GF := GF) E pl(&Occil.weakComposition #int (n : ℤ) #int (total : ℤ))
      (Compositions.weakLaw n total hn) (listVal Val.int) where
  spec F _ := by
    have ht : n ≤ total + n := by omega
    iintro Hcredit
    iterate 5 twp_pure
    simp only [PositiveComposition.positiveComposition_openRec,
      PositiveComposition.positiveComposition_closeRec]
    rw [← Nat.cast_add]
    twp_bind pl(&Occil.positiveComposition #int (n : ℤ) #int ((total + n : ℕ) : ℤ))
    isimp only [← Compositions.weak_expectation n total hn F] at Hcredit
    iapply ((PositiveComposition.positiveComposition_distSpec E n (total + n) hn ht).wp
      (fun parts => F (Compositions.subtractOne parts)) (measurable_of_countable _) _) $$ Hcredit
    iintro %parts Hcredit
    twp_pure
    twp_pure
    have hsub := twp_subtract (rT := rT) (GF := GF) E parts
    simp [subtract, Exp.close, Exp.closeRec] at hsub
    iapply tglWp_wand
    isplitl []
    · iapply hsub
    iintro %v %hv
    iexists Compositions.subtractOne parts
    iframe Hcredit
    ipureintro
    exact hv

end specification

end

end SampLib.WeakComposition
