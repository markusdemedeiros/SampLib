import SampLib.Bernoulli.Gambler

/-! # High-power logistic factory

Reflecting the finite walk turns its upper-exit probability into a geometric tail.
The same exponential work potential proves termination even when the input bias is zero.
-/

open Set ProbLang
open ENNReal (ofReal)
open scoped ENNReal NNReal

namespace SampLib.HighPowerLogistic

noncomputable section

set_option maxHeartbeats 600000

private def walk {rT : Type _} (coin : Val rT) (N : ℕ) (a b : ℤ) : Val rT :=
  ⟨.fix (.lam (pl% if {Exp.bvar 0} = #0 then #false else
    if #int ((N - 1 : ℕ) : ℤ) < {Exp.bvar 0} then #true else
    if &Occil.logisticFactory &coin.fst #int a #int b #()
    then {Exp.bvar 1} ({Exp.bvar 0} + #1)
    else {Exp.bvar 1} ({Exp.bvar 0} - #1))), .fix (by is_lc), by is_lc⟩

private def source {rT : Type _} : Val rT :=
  ⟨Occil.FactoryExtra.highPowerLogistic, .lam (by is_lc), by is_lc⟩

private theorem source_fst {rT : Type _} :
    (source (rT := rT)).fst = Occil.FactoryExtra.highPowerLogistic := rfl

private theorem int_pred (i : ℕ) (hi : 0 < i) :
    (i : ℤ) - 1 = ((i - 1 : ℕ) : ℤ) := by omega

private theorem int_beq {rT : Type _} [BEq rT] (i j : ℤ) :
    ((BaseLit.int i : BaseLit rT) == .int j) = (i == j) := rfl

private theorem one_expectation (F : Bool → ℝ≥0∞) :
    (∫⁻ z, F z ∂RealCoin.law 1) = F true := by
  simp [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf]

private theorem reflect_succ (N i : ℕ) : N - (i + 1) = N - i - 1 := by omega

private theorem reflect_pred (N i : ℕ) (hi : 0 < i) (hiN : i ≤ N) :
    N - (i - 1) = N - i + 1 := by omega

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open FiniteGeometricWalk
open Gambler (logisticFactory_openRec logisticFactory_closeRec)

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Reflection preserves the fixed work coefficient while ambient slack doubles. -/
private theorem twp_walk_positive (E : CoPset) (t : ℝ) (ht : 0 ≤ t)
    (N : ℕ) (hN : 0 < N) (coin : Val rT) (a b : ℤ)
    (hstep : IsDistSpec (GF := GF) E
      pl(&Occil.logisticFactory &coin.fst #int a #int b #()) (RealCoin.law (down t ht)) Val.bool)
    (F : Bool → ℝ≥0∞) (δ : ℝ≥0∞) (hδ : 0 < δ) :
    ⊢ ↯ δ -∗ ∀ i : ℕ, ⌜i ≤ N⌝ -∗
      ↯ (credit t ht N hN F (N - i) + ofReal (work t N (N - i)) * δ) -∗
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
    iexists false
    isimp only [Nat.sub_zero, credit_top, work_top,
      ENNReal.ofReal_zero, zero_mul, add_zero] at Hcredit
    iframe Hcredit
    itrivial
  · rw [beq_eq_false_iff_ne.mpr (by exact_mod_cast hi0)]
    twp_pure
    twp_pure
    by_cases hitop : i = N
    · subst i
      rw [decide_eq_true (by exact_mod_cast (Nat.sub_lt hN Nat.zero_lt_one))]
      twp_pure
      twp_value
      imodintro
      iexists true
      isimp only [Nat.sub_self, credit_zero, work_zero,
        ENNReal.ofReal_zero, zero_mul, add_zero] at Hcredit
      iframe Hcredit
      itrivial
    · have hpos : 0 < i := Nat.pos_of_ne_zero hi0
      have hlt : i < N := lt_of_le_of_ne hi hitop
      have hjpos : 0 < N - i := Nat.sub_pos_of_lt hlt
      have hjlt : N - i < N := Nat.sub_lt hN hpos
      rw [decide_eq_false (by exact_mod_cast (not_lt.mpr (Nat.le_sub_one_of_lt hlt)))]
      twp_pure
      twp_bind pl(&Occil.logisticFactory &coin.fst #int a #int b #())
      icombine Hcredit Hterm as Hcredit
      ihave Hcredit := ErrorCredit.weaken
        (expectation t ht N (N - i) hN hjpos hjlt F δ) $$ Hcredit
      iapply (hstep.wp (stepCredit t ht N hN F δ (N - i)) (measurable_of_countable _) _)
        $$ Hcredit
      iintro %z Hcredit
      cases z
      · twp_pure
        twp_pure
        rw [int_pred i hpos]
        isimp only [stepCredit, Bool.false_eq_true, ite_false,
          ← reflect_pred N i hpos hi] at Hcredit
        ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
        twp_bind pl(&(walk coin N a b).fst #int ((i - 1 : ℕ) : ℤ))
        iapply (tglWp_mono fun _ => tglWp_value)
        iapply IH $$ Hterm %(i - 1) %((Nat.sub_le i 1).trans hi) Hcredit
      · twp_pure
        twp_pure
        rw [← Nat.cast_add_one]
        isimp only [stepCredit, ite_true, ← reflect_succ N i] at Hcredit
        ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
        twp_bind pl(&(walk coin N a b).fst #int ((i + 1 : ℕ) : ℤ))
        iapply (tglWp_mono fun _ => tglWp_value)
        iapply IH $$ Hterm %(i + 1) %(Nat.succ_le_of_lt hlt) Hcredit

private theorem twp_walk (E : CoPset) (t : ℝ) (ht : 0 ≤ t)
    (N : ℕ) (hN : 0 < N) (coin : Val rT) (a b : ℤ)
    (hstep : IsDistSpec (GF := GF) E
      pl(&Occil.logisticFactory &coin.fst #int a #int b #()) (RealCoin.law (down t ht)) Val.bool)
    (i : ℕ) (hi : i ≤ N) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (credit t ht N hN F (N - i)) -∗
      tglWp E pl(&(walk coin N a b).fst #int (i : ℤ))
        (fun v : Val rT => iprop(∃ z : Bool, ⌜v = Val.bool z⌝ ∗ ↯ (F z))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  let δ := initialSlack t N (N - i) ε
  have hδ : 0 < δ := initialSlack_pos t N (N - i) ε hε
  ihave Hterm := ErrorCredit.weaken (le_of_eq (initialSlack_budget t N (N - i) ε))
    $$ Hterm
  ihave ⟨Hwork, Hterm⟩ := ErrorCredit.split $$ Hterm
  icombine Hcredit Hwork as Hcredit
  iapply (twp_walk_positive E t ht N hN coin a b hstep F δ hδ) $$ Hterm %i %hi Hcredit

/-- Nonpositive powers return true without inspecting the rational parameters or callback. -/
theorem highPowerLogistic_base_distSpec (E : CoPset) (coin : Val rT) (height a b : ℤ)
    (hheight : height ≤ 0) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.highPowerLogistic &coin.fst #int height #int a #int b)
      (RealCoin.law 1) Val.bool where
  spec F _ := by
    iintro Hcredit
    rw [← source_fst (rT := rT)]
    iterate 4 (twp_step; simp [Exp.open', Exp.openRec, Exp.close, Exp.closeRec, Exp.ofVal,
      Var.internal.injEq, ProbLang.openRec_val_fst,
      logisticFactory_openRec, logisticFactory_closeRec])
    twp_pures
    rw [decide_eq_true (lt_of_le_of_lt hheight zero_lt_one)]
    twp_pures
    twp_value
    imodintro
    iexists true
    isimp only [one_expectation] at Hcredit
    iframe Hcredit
    itrivial

/-- The upper-exit probability `t^height / (1 + t + ⋯ + t^height)`. -/
def bias (p : unitInterval) (a b : ℤ) (ha : 0 < a) (hb : 0 < b) (height : ℕ) :
    unitInterval :=
  FiniteGeometricWalk.bias (Gambler.ratio p a b) (Gambler.ratio_nonneg p a b ha hb)
    (height + 1) (Nat.succ_pos _) height

theorem bias_coe (p : unitInterval) (a b : ℤ) (ha : 0 < a) (hb : 0 < b) (height : ℕ) :
    (bias p a b ha hb height : ℝ) =
      Gambler.ratio p a b ^ height /
        FiniteGeometricWalk.total (Gambler.ratio p a b) (height + 1) := by
  simp [bias, FiniteGeometricWalk.bias, tail]

/-- Exact high-power logistic law for all natural powers and input biases. -/
theorem highPowerLogistic_distSpec [ProbLangDist.IsUniformInt rT]
    (E : CoPset) (p : unitInterval) (height : ℕ) (a b : ℤ)
    (ha : 0 < a) (hb : 0 < b) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.highPowerLogistic &coin.fst #int (height : ℤ) #int a #int b)
      (RealCoin.law (bias p a b ha hb height)) Val.bool where
  spec F _ := by
    have hs := LogisticFactory.logisticFactory_distSpec (rT := rT) (GF := GF)
      E p a b ha hb coin hcoin
    rw [Gambler.logistic_bias p a b ha hb] at hs
    have hw := twp_walk E (Gambler.ratio p a b) (Gambler.ratio_nonneg p a b ha hb)
      (height + 1) (Nat.succ_pos _) coin a b hs 1 (Nat.succ_pos _) F
    simp only [walk, credit, Nat.add_sub_cancel] at hw
    iintro Hcredit
    rw [← source_fst (rT := rT)]
    iterate 4 (twp_step; simp [Exp.open', Exp.openRec, Exp.close, Exp.closeRec, Exp.ofVal,
      Var.internal.injEq, ProbLang.openRec_val_fst,
      logisticFactory_openRec, logisticFactory_closeRec])
    twp_step
    simp [Exp.open', Exp.openRec]
    isimp only [RealCoin.lintegral_law, bias] at Hcredit
    iapply hw $$ Hcredit

end specification

end

end SampLib.HighPowerLogistic
