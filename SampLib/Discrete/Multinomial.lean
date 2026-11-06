import SampLib.Discrete.Laws.Multinomial
import SampLib.Discrete.Binomial
import SampLib.Common.WeightedValidation
import SampLib.Core.SupportedSpec
import SampLib.Core.Syntax.ClosedExp
import SampLib.Core.Syntax.ListValues
import Metrology.Iris.LocalBI

/-! # Sequential conditional-binomial multinomial sampling

Conditioning on the first category leaves a smaller multinomial problem. The
canonical count-vector PMF and its disintegration are proved in the mathematical
companion; the program follows that disintegration one category at a time.
-/

open Set ProbLang
open scoped ENNReal

namespace SampLib.Multinomial

noncomputable section

private instance rational_closed {rT : Type _} : ClosedExp (Occil.rationalCoin : Exp rT) where
  lc := by is_lc
  fv := RationalCoin.rationalCoin_fv

private instance binomial_closed {rT : Type _} : ClosedExp (Occil.binomial : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.binomial, Exp.fv]

private instance sum_closed {rT : Type _} : ClosedExp (Occil.sumInts : Exp rT) where
  lc := by is_lc
  fv := WeightedValidation.sumInts_fv

private def headCoin {rT : Type _} [ProbLangℝ rT] (w : ℕ) (ws : List ℕ) : Val rT :=
  ⟨.lam pl(&Occil.rationalCoin
    (fst(&(Val.pair (Val.int (w : ℤ)) (listVal (fun k : ℕ => Val.int (k : ℤ)) ws)).fst))
    #int ((w : ℤ) + ws.sum)), .lam (by is_lc), by is_lc⟩

private theorem total_test (ws : List ℕ) :
    decide ((ws.sum : ℤ) ≤ 0) = decide (ws.sum = 0) :=
  decide_eq_decide.mpr (by omega)

private theorem sub_cast (n k : ℕ) (hk : k ≤ n) :
    (n : ℤ) - k = ((n - k : ℕ) : ℤ) := (Nat.cast_sub hk).symm

private theorem encode_cons {rT : Type _} [ProbLangℝ rT] (n : ℕ) (ns : List ℕ) :
    pl(inr((#int (n : ℤ), {Exp.ofVal (listVal (fun k : ℕ => Val.int (k : ℤ)) ns)}))) =
      Exp.ofVal (listVal (fun k : ℕ => Val.int (k : ℤ)) (n :: ns) : Val rT) := by
  simp [Exp.ofVal, listVal]

private theorem encode_zero {rT : Type _} [ProbLangℝ rT] (ns : List ℕ) :
    pl(inr((#0, {Exp.ofVal (listVal (fun k : ℕ => Val.int (k : ℤ)) ns)}))) =
      Exp.ofVal (listVal (fun k : ℕ => Val.int (k : ℤ)) (0 :: ns) : Val rT) := by
  simpa only [Nat.cast_zero] using encode_cons (rT := rT) 0 ns

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem headCoin_distSpec (E : CoPset) (w : ℕ) (ws : List ℕ)
    (ht : 0 < w + ws.sum) :
    IsDistSpec (GF := GF) E pl(&(headCoin w ws).fst #())
      (RealCoin.law (Urn.bias w ws.sum)) Val.bool where
  spec F hF := by
    have h : IsDistSpec (GF := GF) E
        pl(&Occil.rationalCoin #int (w : ℤ) #int ((w : ℤ) + ws.sum))
        (RealCoin.law (Urn.bias w ws.sum)) Val.bool := by
      simpa only [Urn.bias, dite_eq_left ht] using
        RationalCoin.rationalCoin_distSpec (rT := rT) (GF := GF)
          E w ((w : ℤ) + ws.sum) (by omega) (by omega) (by omega)
    iintro Hcredit
    iterate 2 twp_pure
    simp only [ClosedExp.openRec, Exp.ofVal]
    iapply h.spec F hF $$ Hcredit

/-- One supported binomial count leaves precisely the canonical tail law. -/
theorem twp_multinomial (E : CoPset) (n : ℕ) (ws : List ℕ)
    (hvalid : n = 0 ∨ 0 < ws.sum) (F : List ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ cs, F cs ∂law n ws) -∗
      tglWp E pl(&Occil.multinomial #int (n : ℤ)
        &(listVal (fun k : ℕ => Val.int (k : ℤ)) ws).fst)
        (fun v : Val rT => iprop(∃ cs : List ℕ,
          ⌜v = listVal (fun k : ℕ => Val.int (k : ℤ)) cs⌝ ∗ ↯ (F cs))) := by
  induction ws generalizing n F with
  | nil =>
    have hn : n = 0 := by simpa using hvalid
    subst n
    iintro Hcredit
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    iexists []
    isimp only [law_nil, MeasureTheory.lintegral_dirac] at Hcredit
    iframe Hcredit
    ipureintro
    exact Val.ext rfl
  | cons w ws ih =>
    iintro Hcredit
    simp only [listVal]
    iterate 10 twp_pure
    simp only [ClosedExp.openRec, ClosedExp.closeRec]
    twp_bind pl(&Occil.sumInts
      &(listVal (fun k : ℕ => Val.int (k : ℤ)) (w :: ws)).fst)
    iapply tglWp_wand
    isplitl []
    · iapply WeightedChoice.twp_sumInts E (w :: ws)
    iintro %v %hv
    subst v
    iterate 2 twp_pure
    rw [total_test (w :: ws)]
    by_cases ht : (w :: ws).sum = 0
    · have hn : n = 0 := by simpa [ht] using hvalid
      subst n
      rw [decide_eq_true ht]
      iterate 4 twp_pure
      twp_bind pl(&Occil.multinomial #0
        &(listVal (fun k : ℕ => Val.int (k : ℤ)) ws).fst)
      iapply tglWp_wand
      isplitl [Hcredit]
      · isimp only [← expectation 0 w ws F, Binomial.expectation_zero] at Hcredit
        iapply ih 0 (Or.inl rfl) (fun cs => F (0 :: cs)) $$ Hcredit
      iintro %v ⟨%cs, %hv, Hcredit⟩
      subst v
      rw [encode_zero]
      iapply tglWp_value
      iexists 0 :: cs
      iframe Hcredit
      itrivial
    · have htpos : 0 < w + ws.sum := by simpa using Nat.pos_of_ne_zero ht
      rw [decide_eq_false ht]
      twp_pure
      rw [List.sum_cons, Nat.cast_add]
      simp only [ClosedExp.openRec]
      twp_bind pl(&Occil.binomial &(headCoin w ws).fst #int (n : ℤ))
      isimp only [← expectation n w ws F] at Hcredit
      iapply ((Binomial.binomial_distSpec E (Urn.bias w ws.sum) (headCoin w ws)
        (headCoin_distSpec E w ws htpos) n).wp_supported
        (fun k => k ≤ n ∧ (n - k = 0 ∨ 0 < ws.sum)) ((Set.to_countable _).measurableSet)
        (split_support n w ws hvalid) (fun k => ∫⁻ cs, F (k :: cs) ∂law (n - k) ws)
        (measurable_of_countable _) _) $$ Hcredit
      iintro %k ⟨%hk, %hrest⟩ Hcredit
      iterate 3 twp_pure
      rw [sub_cast n k hk]
      twp_bind pl(&Occil.multinomial #int ((n - k : ℕ) : ℤ)
        &(listVal (fun k : ℕ => Val.int (k : ℤ)) ws).fst)
      iapply tglWp_wand
      isplitl [Hcredit]
      · iapply ih (n - k) hrest (fun cs => F (k :: cs)) $$ Hcredit
      iintro %v ⟨%cs, %hv, Hcredit⟩
      subst v
      rw [encode_cons]
      iapply tglWp_value
      iexists k :: cs
      iframe Hcredit
      itrivial

/-- Typed multinomial law for all feasible nonnegative category weights and trial counts. -/
theorem multinomial_distSpec (E : CoPset) (n : ℕ) (ws : List ℕ)
    (hvalid : n = 0 ∨ 0 < ws.sum) :
    IsDistSpec (GF := GF) E pl(&Occil.multinomial #int (n : ℤ)
      &(listVal (fun k : ℕ => Val.int (k : ℤ)) ws).fst)
      (law n ws) (listVal (fun k : ℕ => Val.int (k : ℤ))) where
  spec F _ := wand_entails (twp_multinomial E n ws hvalid F)

end specification

end

end SampLib.Multinomial
