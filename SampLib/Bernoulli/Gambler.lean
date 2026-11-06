import SampLib.Bernoulli.Laws.Gambler
import SampLib.Bernoulli.LogisticFactory
import SampLib.Core.SamplerStep
import Samplers.Bernoulli.Linear

/-! # The finite gambler's-ruin factory

The walk's harmonic credit is a normalized geometric tail. Its fixed work
potential pays the extra ambient credit required by amplification induction.
-/

open Set ProbLang
open ENNReal (ofReal)
open scoped ENNReal NNReal

namespace SampLib.Gambler

noncomputable section

private theorem zero_expectation (F : Bool → ℝ≥0∞) :
    (∫⁻ z, F z ∂RealCoin.law 0) = F false := by
  simp [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf]

private def walk {rT : Type _} (coin : Val rT) (N : ℕ) (a b : ℤ) : Val rT :=
  ⟨.fix (.lam (pl% if {Exp.bvar 0} = #0 then #true else
    if #int (N : ℤ) <= {Exp.bvar 0} then #false else
    if &Occil.logisticFactory &coin.fst #int a #int b #()
    then {Exp.bvar 1} ({Exp.bvar 0} - #1)
    else {Exp.bvar 1} ({Exp.bvar 0} + #1))), .fix (by is_lc), by is_lc⟩

private def source {rT : Type _} : Val rT :=
  ⟨Occil.FactoryExtra.gambler, .lam (by is_lc), by is_lc⟩

private theorem source_fst {rT : Type _} :
    (source (rT := rT)).fst = Occil.FactoryExtra.gambler := rfl

theorem logisticFactory_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.logisticFactory = Occil.logisticFactory :=
  (Exp.open_lc k e _ (by is_lc)).symm

theorem logisticFactory_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.logisticFactory : Exp rT) = Occil.logisticFactory :=
  Exp.closeRec_fresh x _ k (by
    simp [Occil.logisticFactory, Exp.fv, RationalCoin.rationalCoin_fv])

private theorem int_pred (i : ℕ) (hi : 0 < i) :
    (i : ℤ) - 1 = ((i - 1 : ℕ) : ℤ) := by omega

private theorem int_beq {rT : Type _} [BEq rT] (i j : ℤ) :
    ((BaseLit.int i : BaseLit rT) == .int j) = (i == j) := rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open FiniteGeometricWalk

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The potential coefficient stays fixed inside `P`; only ambient `δ` doubles. -/
private theorem twp_walk_positive (E : CoPset) (t : ℝ) (ht : 0 ≤ t)
    (N : ℕ) (hN : 0 < N) (coin : Val rT) (a b : ℤ)
    (hstep : IsDistSpec (GF := GF) E
      pl(&Occil.logisticFactory &coin.fst #int a #int b #()) (RealCoin.law (down t ht)) Val.bool)
    (F : Bool → ℝ≥0∞) (δ : ℝ≥0∞) (hδ : 0 < δ) :
    ⊢ ↯ δ -∗ ∀ i : ℕ, ⌜i ≤ N⌝ -∗ ↯ (credit t ht N hN F i + ofReal (work t N i) * δ) -∗
      tglWp E pl(&(walk coin N a b).fst #int (i : ℤ))
        (fun v : Val rT => iprop(∃ z : Bool, ⌜v = Val.bool z⌝ ∗ ↯ (F z))) := by
  iintro Hterm
  iapply ErrorCredit.Induction.simple hδ (by norm_num : (1 : ℝ≥0) < 2) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ %i %hi Hcredit
  iterate 2 (twp_step; simp [Exp.open', Exp.openRec, ProbLang.openRec_val_fst,
    logisticFactory_openRec])
  twp_pure
  rw [int_beq]
  by_cases hi0 : i = 0
  · subst i
    simp only [Int.natCast_zero, beq_self_eq_true]
    twp_pures
    twp_value
    imodintro
    iexists true
    isimp only [credit_zero, work_zero, ENNReal.ofReal_zero, zero_mul, add_zero] at Hcredit
    iframe Hcredit
    itrivial
  · rw [beq_eq_false_iff_ne.mpr (by exact_mod_cast hi0)]
    twp_pure
    twp_pure
    by_cases hitop : i = N
    · subst i
      simp only [le_refl, decide_true]
      twp_pure
      twp_value
      imodintro
      iexists false
      isimp only [credit_top, work_top, ENNReal.ofReal_zero, zero_mul, add_zero] at Hcredit
      iframe Hcredit
      itrivial
    · have hpos : 0 < i := Nat.pos_of_ne_zero hi0
      have hlt : i < N := lt_of_le_of_ne hi hitop
      rw [decide_eq_false (by exact_mod_cast not_le.mpr hlt)]
      twp_pure
      twp_bind pl(&Occil.logisticFactory &coin.fst #int a #int b #())
      icombine Hcredit Hterm as Hcredit
      ihave Hcredit := ErrorCredit.weaken (expectation t ht N i hN hpos hlt F δ) $$ Hcredit
      iapply (hstep.wp (stepCredit t ht N hN F δ i) (measurable_of_countable _) _) $$ Hcredit
      iintro %z Hcredit
      cases z
      · twp_pure
        twp_pure
        rw [← Nat.cast_add_one]
        isimp only [stepCredit, Bool.false_eq_true, ite_false] at Hcredit
        ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
        twp_bind pl(&(walk coin N a b).fst #int ((i + 1 : ℕ) : ℤ))
        iapply (tglWp_mono fun _ => tglWp_value)
        iapply IH $$ Hterm %(i + 1) %(Nat.succ_le_of_lt hlt) Hcredit
      · twp_pure
        twp_pure
        rw [int_pred i hpos]
        isimp only [stepCredit, ite_true] at Hcredit
        ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
        twp_bind pl(&(walk coin N a b).fst #int ((i - 1 : ℕ) : ℤ))
        iapply (tglWp_mono fun _ => tglWp_value)
        iapply IH $$ Hterm %(i - 1) %((Nat.sub_le i 1).trans hi) Hcredit

private theorem twp_walk (E : CoPset) (t : ℝ) (ht : 0 ≤ t)
    (N : ℕ) (hN : 0 < N) (coin : Val rT) (a b : ℤ)
    (hstep : IsDistSpec (GF := GF) E
      pl(&Occil.logisticFactory &coin.fst #int a #int b #()) (RealCoin.law (down t ht)) Val.bool)
    (i : ℕ) (hi : i ≤ N) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (credit t ht N hN F i) -∗
      tglWp E pl(&(walk coin N a b).fst #int (i : ℤ))
        (fun v : Val rT => iprop(∃ z : Bool, ⌜v = Val.bool z⌝ ∗ ↯ (F z))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  let δ := initialSlack t N i ε
  have hδ : 0 < δ := initialSlack_pos t N i ε hε
  ihave Hterm := ErrorCredit.weaken (le_of_eq (initialSlack_budget t N i ε)) $$ Hterm
  ihave ⟨Hwork, Hterm⟩ := ErrorCredit.split $$ Hterm
  icombine Hcredit Hwork as Hcredit
  iapply (twp_walk_positive E t ht N hN coin a b hstep F δ hδ) $$ Hterm %i %hi Hcredit

/-- At heights at most one, the initial state is already at the upper exit. -/
theorem gambler_base_distSpec (E : CoPset) (coin : Val rT) (height a b : ℤ)
    (hheight : height ≤ 1) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.gambler &coin.fst #int height #int a #int b)
      (RealCoin.law 0) Val.bool where
  spec F _ := by
    iintro Hcredit
    rw [← source_fst (rT := rT)]
    iterate 4 (twp_step; simp [Exp.open', Exp.openRec, Exp.close, Exp.closeRec, Exp.ofVal,
      Var.internal.injEq, ProbLang.openRec_val_fst,
      logisticFactory_openRec, logisticFactory_closeRec])
    twp_pures
    rw [decide_eq_true hheight]
    twp_pures
    twp_value
    imodintro
    iexists false
    isimp only [zero_expectation] at Hcredit
    iframe Hcredit
    itrivial

/-- The complete finite walk, including height zero and degenerate input biases. -/
theorem gambler_distSpec [ProbLangDist.IsUniformInt rT]
    (E : CoPset) (p : unitInterval) (height : ℕ) (a b : ℤ)
    (ha : 0 < a) (hb : 0 < b) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.gambler &coin.fst #int (height : ℤ) #int a #int b)
      (RealCoin.law (bias p a b ha hb height)) Val.bool where
  spec F hF := by
    by_cases hheight : height = 0
    · subst height
      simpa only [bias, Nat.zero_max, bias_top, Int.natCast_zero] using
        (gambler_base_distSpec (GF := GF) E coin 0 a b (by norm_num)).spec F hF
    · have hN : 0 < height := Nat.pos_of_ne_zero hheight
      have hs := LogisticFactory.logisticFactory_distSpec (rT := rT) (GF := GF)
        E p a b ha hb coin hcoin
      rw [logistic_bias p a b ha hb] at hs
      have hw := twp_walk E (ratio p a b) (ratio_nonneg p a b ha hb)
        height hN coin a b hs 1 hN F
      simp only [walk, credit] at hw
      iintro Hcredit
      rw [← source_fst (rT := rT)]
      iterate 4 (twp_step; simp [Exp.open', Exp.openRec, Exp.close, Exp.closeRec, Exp.ofVal,
        Var.internal.injEq, ProbLang.openRec_val_fst,
        logisticFactory_openRec, logisticFactory_closeRec])
      twp_step
      simp [Exp.open', Exp.openRec]
      isimp only [RealCoin.lintegral_law, bias,
        max_eq_left (Nat.one_le_iff_ne_zero.mpr hheight)] at Hcredit
      iapply hw $$ Hcredit

end specification

end

end SampLib.Gambler
