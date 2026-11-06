import SampLib.Distributions.AffineRatio
import SampLib.AffineRankCoin

/-! # The affine ratio factory

Direct rejection uses disjoint accepted intervals. Otherwise two affine rank
coins feed the verified division factory, with exactly the supplied normalized margin.
-/

open ProbLang
open scoped ENNReal NNReal

namespace SampLib.AffineRatio

noncomputable section

private def directBody {rT : Type _} (pcoin qcoin : Val rT) (c d s : ℕ) : Exp rT :=
  .cond (.binop .lt (.bvar 0) (.lit (.int d))) (.lit (.bool true))
    (.cond (.binop .lt (.bvar 0) (.binop .plus (.lit (.int d)) (.lit (.int s))))
      (.app qcoin.fst (.lit .unit))
      (.cond (.binop .lt (.bvar 0) (.lit (.int c))) (.lit (.bool false))
        (.cond (.app pcoin.fst (.lit .unit)) (.lit (.bool false)) (.app (.bvar 2) (.lit .unit)))))

private def directLoop {rT : Type _} (pcoin qcoin : Val rT) (c d s : ℕ) : Val rT :=
  ⟨.fix (.lam (.app (.lam (directBody pcoin qcoin c d s))
    pl(&Occil.uniformInt (#int (c : ℤ) + #int (s : ℤ))))),
    .fix (by unfold directBody; is_lc), by unfold directBody; is_lc⟩

private def source {rT : Type _} : Val rT :=
  ⟨Occil.FactoryExtra.affineRatio, .lam (by is_lc), by is_lc⟩

private theorem source_fst {rT : Type _} :
    (source (rT := rT)).fst = Occil.FactoryExtra.affineRatio := rfl

private theorem lt_test (k n : ℕ) : decide ((k : ℤ) < n) = decide (k < n) := by
  simp only [Int.ofNat_lt]

private theorem nonpositive_test (n : ℕ) (hn : 0 < n) : decide ((n : ℤ) ≤ 0) = false :=
  decide_eq_false (by exact_mod_cast Nat.not_le.mpr hn)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable [ProbLangDist.IsUniformInt rT]
local bi (IProp GF)

/-- The four rank branches execute the trial partition literally. -/
private theorem twp_direct (E : CoPset) (p q : unitInterval) (c d s : ℕ) (hs : 0 < s)
    (h : d + s ≤ c) (pcoin qcoin : Val rT)
    (hpcoin : IsDistSpec (GF := GF) E pl(&pcoin.fst #()) (RealCoin.law p) Val.bool)
    (hqcoin : IsDistSpec (GF := GF) E pl(&qcoin.fst #()) (RealCoin.law q) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (directBias p q c d s hs h) F) -∗
      tglWp E pl(&(directLoop pcoin qcoin c d s).fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε
    (BernoulliRetry.one_lt_factor (retry p c s hs) (retry_lt_one p c d s hs h)) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  iterate 2 (twp_step; simp [directBody, Exp.open', Exp.openRec,
    ProbLang.openRec_val_fst, UniformInt.uniformInt_openRec])
  twp_pure
  rw [← Int.natCast_add]
  twp_bind pl(&Occil.uniformInt #int ((c + s : ℕ) : ℤ))
  icombine Hcredit Hterm as Hcredit
  ihave Hcredit := ErrorCredit.weaken (direct_expectation p q c d s hs h F ε) $$ Hcredit
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply UniformInt.twp_uniformInt E (c + s) (Nat.add_pos_right c hs)
      (rankCredit p q c d s hs h F ε) $$ Hcredit
  iintro %v ⟨%k, %hv, %hk, Hcredit⟩
  subst v
  twp_step
  simp [Exp.open', Exp.openRec, ProbLang.openRec_val_fst]
  twp_pures
  rw [lt_test]
  by_cases hd : k < d
  · rw [decide_eq_true hd]
    twp_pure
    twp_value
    imodintro
    iexists true
    isimp only [rankCredit, ite_eq_left hd] at Hcredit
    iframe Hcredit
    itrivial
  · rw [decide_eq_false hd]
    twp_pures
    rw [← Int.natCast_add, lt_test]
    by_cases hds : k < d + s
    · rw [decide_eq_true hds]
      twp_pure
      isimp only [rankCredit, ite_eq_right hd, ite_eq_left hds] at Hcredit
      iapply hqcoin.spec F (measurable_of_countable _) $$ Hcredit
    · rw [decide_eq_false hds]
      twp_pures
      rw [lt_test]
      by_cases hc : k < c
      · rw [decide_eq_true hc]
        twp_pure
        twp_value
        imodintro
        iexists false
        isimp only [rankCredit, ite_eq_right hd, ite_eq_right hds, ite_eq_left hc] at Hcredit
        iframe Hcredit
        itrivial
      · rw [decide_eq_false hc]
        twp_pure
        twp_bind pl(&pcoin.fst #())
        isimp only [rankCredit, ite_eq_right hd, ite_eq_right hds, ite_eq_right hc] at Hcredit
        iapply (hpcoin.wp (coinCredit p q c d s hs h F ε) (measurable_of_countable _) _)
          $$ Hcredit
        iintro %b Hcredit
        cases b
        · twp_pure
          isimp only [coinCredit, Bool.false_eq_true, ite_false] at Hcredit
          ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
          twp_bind pl(&(directLoop pcoin qcoin c d s).fst #())
          iapply (tglWp_mono fun _ => tglWp_value)
          iapply IH $$ Hterm Hcredit
        · twp_pure
          twp_value
          imodintro
          iexists false
          isimp only [coinCredit, ite_true] at Hcredit
          iframe Hcredit
          itrivial

/-- Full affine-ratio law: unrestricted direct margins, otherwise the exact normalized gap. -/
theorem affineRatio_distSpec (E : CoPset) (p q : unitInterval) (a b x y : ℕ) (e f : ℤ)
    (hb : 0 < b) (hy : 0 < y) (h : Admissible p q (a * y) (x * b) (b * y) e f)
    (pcoin qcoin : Val rT)
    (hpcoin : IsDistSpec (GF := GF) E pl(&pcoin.fst #()) (RealCoin.law p) Val.bool)
    (hqcoin : IsDistSpec (GF := GF) E pl(&qcoin.fst #()) (RealCoin.law q) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.affineRatio &pcoin.fst &qcoin.fst #int (a : ℤ) #int (b : ℤ)
        #int (x : ℤ) #int (y : ℤ) #int e #int f #())
      (RealCoin.law (bias p q (a * y) (x * b) (b * y) e f (Nat.mul_pos hb hy) h)) Val.bool where
  spec F hF := by
    let c := a * y
    let d := x * b
    let s := b * y
    have hs : 0 < s := Nat.mul_pos hb hy
    iintro Hcredit
    rw [← source_fst (rT := rT)]
    iterate 9 (twp_step; simp [Exp.open', Exp.openRec, Exp.close, Exp.closeRec, Exp.ofVal,
      Var.internal.injEq, ProbLang.openRec_val_fst, Division.division_openRec,
      Division.division_closeRec, UniformInt.uniformInt_openRec, UniformInt.uniformInt_closeRec])
    twp_pures
    simp only [nonpositive_test b hb, nonpositive_test y hy, Bool.or_false]
    iterate 12 (twp_step; simp -failIfUnchanged [Exp.open', Exp.openRec, Exp.ofVal,
      ProbLang.openRec_val_fst, Division.division_openRec, UniformInt.uniformInt_openRec])
    iterate 2 twp_pure
    simp only [← Int.natCast_mul, ← Int.natCast_add, Int.ofNat_le]
    by_cases hd : d + s ≤ c
    · have hr := twp_direct (rT := rT) (GF := GF) E p q c d s hs hd pcoin qcoin hpcoin hqcoin F
      simp only [directLoop, directBody, directBias, bias] at hr
      rw [decide_eq_true hd]
      twp_pure
      twp_step
      simp [Exp.open', Exp.openRec]
      simp only [← Int.natCast_mul]
      isimp only [RealCoin.lintegral_law, bias] at Hcredit
      iapply hr $$ Hcredit
    · have hp := division_parameters p q c d s e f hs h hd
      have hden := AffineRankCoin.distSpec (rT := rT) (GF := GF) E p pcoin hpcoin
        c s (c + d + s) (Nat.add_pos_right _ hs) (interval_bounds c d s).1
      have hnum := AffineRankCoin.distSpec (rT := rT) (GF := GF) E q qcoin hqcoin
        d s (c + d + s) (Nat.add_pos_right _ hs) (interval_bounds c d s).2
      have hr := Division.division_distSpec E (denominatorBias p c d s hs)
        (numeratorBias q c d s hs) e f hp.1 hp.2.1 hp.2.2
        (AffineRankCoin.callback pcoin c s (c + d + s))
        (AffineRankCoin.callback qcoin d s (c + d + s)) hden hnum
      rw [division_bias_eq p q c d s e f hs h hd] at hr
      simp only [AffineRankCoin.callback, AffineRankCoin.body] at hr
      rw [decide_eq_false hd]
      twp_pure
      iapply hr.spec F hF $$ Hcredit

end specification

end

end SampLib.AffineRatio
