import SampLib.Latent.UniformBag
import SampLib.Latent.Laws.UniformBag

/-! # Reading a finite cached prefix -/

open ProbLang
open scoped ENNReal

namespace SampLib.UniformBag

private theorem readRefines_zero (p : List Bool) : readRefines p 0 p := by
  exact ⟨List.prefix_refl _, by simp⟩

private theorem readRefines_cons {p q r : List Bool} {b : Bool} {n : ℕ}
    (hs : stepRefines p b q) (hr : readRefines q n r) :
    readRefines p (n + 1) (b :: r) := by
  rcases hr with ⟨hprefix, hlen⟩
  rcases hs with ⟨rfl, rfl⟩ | rfl
  · exact ⟨List.nil_prefix, by simp [hlen]⟩
  · exact ⟨List.cons_prefix_cons.mpr ⟨rfl, hprefix⟩, by
      simp only [List.length_cons]
      omega⟩

private theorem accumulate (acc : ℤ) (b : Bool) (q : List Bool) (n : ℕ)
    (hn : n ≤ q.length) :
    (acc * 2 + if b then 1 else 0) * 2 ^ n + rank (q.take n) =
      acc * 2 ^ (n + 1) + rank ((b :: q).take (n + 1)) := by
  simp only [List.take_succ_cons, rank, List.length_take, Nat.min_eq_left hn, pow_succ]
  ring

private theorem readOutcome_cons {p q r : List Bool} {b : Bool} {n : ℕ}
    {acc : ℤ} {v : Val rT} (hs : stepRefines p b q)
    (hr : readRefines q n r ∧
      v = Val.int ((acc * 2 + if b then 1 else 0) * 2 ^ n + rank (r.take n))) :
    readRefines p (n + 1) (b :: r) ∧
      v = Val.int (acc * 2 ^ (n + 1) + rank ((b :: r).take (n + 1))) := by
  exact ⟨readRefines_cons hs hr.1,
    hr.2.trans (congrArg Val.int (accumulate acc b r n
      ((le_max_right _ _).trans_eq hr.1.2.symm)))⟩

private def prefixLoop {rT : Type} : Exp rT := pl%
  rec read node remaining acc :=
    if remaining = #0 then acc else
      let p := &Occil.uniformBagStep node;
      let bit := (if fst(p) then #1 else #0);
      read (snd(p)) (remaining - #1) (acc * #2 + bit)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_prefixLoop (E : CoPset) (n : ℕ) (l : Loc) (p : List Bool)
    (acc : ℤ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    iprop(owns l p ∗ ↯ (DyadicPosterior.credit p F)) ⊢
      tglWp E pl(&prefixLoop #loc l #int (n : ℤ) #int acc)
        (fun v : Val rT => iprop(∃ q : List Bool,
          ⌜readRefines p n q ∧ v = Val.int (acc * 2 ^ n + rank (q.take n))⌝ ∗
          owns l q ∗ ↯ (DyadicPosterior.credit q F))) := by
  induction n generalizing l p acc F with
  | zero =>
    iintro ⟨Hbag, Hcredit⟩
    unfold prefixLoop
    twp_pures
    twp_value
    imodintro
    iexists p
    iframe Hbag Hcredit
    ipureintro
    exact ⟨readRefines_zero p, by simp [rank]⟩
  | succ n IH =>
    iintro ⟨Hbag, Hcredit⟩
    unfold prefixLoop
    iterate 6 twp_pure
    isimp only [uniformBagStep_openRec, uniformBagStep_closeRec]
    twp_bind pl(&Occil.uniformBagStep #loc l)
    iapply tglWp_wand
    isplitl [Hbag Hcredit]
    · iapply twp_uniformBagStep E l p F hF
      iframe Hbag Hcredit
    iintro %v ⟨%b, %tail, %q, %hv, Hl, Htail, Hcredit⟩
    rcases hv with ⟨rfl, hstep⟩
    isimp only [DyadicPosterior.credit_cons b q F hF] at Hcredit
    have hF' := hF.comp (DyadicPosterior.measurable_half b)
    cases b <;> iterate 8 twp_pure
    all_goals
      isimp only [uniformBagStep_openRec]
      rw [Nat.cast_add_one, add_sub_cancel_right]
      twp_bind pl(&prefixLoop #loc tail #int (n : ℤ) #int (acc * 2 + _))
      iapply tglWp_wand
      isplitl [Htail Hcredit]
      · iapply IH tail q _ (fun u => F (DyadicPosterior.half _ u)) hF'
        iframe Htail Hcredit
      iintro %v ⟨%r, %hr, Htail, Hcredit⟩
      iapply (tglWp_value (v := v))
      iexists _ :: r
      isimp only [← DyadicPosterior.credit_cons _ r F hF] at Hcredit
      ihave Hbag : owns l (_ :: r) $$ [Hl Htail]
      · isimp only [owns]
        iexists tail
        iframe Hl Htail
      iframe Hbag Hcredit
      ipureintro
      exact readOutcome_cons hstep hr

/-- Repeated reads preserve the original cache and its posterior continuation credit. -/
theorem twp_uniformBagPrefix (E : CoPset) (l : Loc) (p : List Bool) (n : ℕ)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    iprop(owns l p ∗ ↯ (DyadicPosterior.credit p F)) ⊢
      tglWp E pl(&Occil.uniformBagPrefix #loc l #int (n : ℤ))
        (fun v : Val rT => iprop(∃ q : List Bool,
          ⌜readRefines p n q ∧ v = Val.int (rank (q.take n))⌝ ∗
          owns l q ∗ ↯ (DyadicPosterior.credit q F))) := by
  iintro Hbag
  iterate 5 twp_pure
  isimp only [uniformBagStep_openRec, uniformBagStep_closeRec]
  ieval (change _ ⊢ tglWp E pl(&prefixLoop #loc l #int (n : ℤ) #int (0 : ℤ)) _)
  have hread := twp_prefixLoop (rT := rT) (GF := GF) E n l p 0 F hF
  simp only [zero_mul, zero_add] at hread
  iapply hread $$ Hbag

end specification

end SampLib.UniformBag
