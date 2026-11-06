import SampLib.Constants.Laws.BernoulliMean
import SampLib.Uniform.UniformInt
import Samplers.Constants.Engines

/-! # Bernoulli sampling by rational sign tests

The sign oracle locates one fixed root. A fair bit chooses a half-cell; only the
half containing the root needs another sign test.
-/

open ProbLang Finset
open ENNReal (ofReal)
open scoped ENNReal

namespace SampLib.AlgebraicRoot

noncomputable section

/-- A rational cell known to contain the target probability. -/
structure Cell (p : unitInterval) where
  index : ℕ
  scale : ℕ
  scale_pos : 0 < scale
  lower : (index : ℝ) ≤ (p : ℝ) * scale
  upper : (p : ℝ) * scale ≤ index + 1

namespace Cell

/-- Conditional probability after the preceding uniform bits selected this cell. -/
def probability {p : unitInterval} (c : Cell p) : unitInterval :=
  ⟨(p : ℝ) * c.scale - c.index, sub_nonneg.mpr c.lower, by linarith [c.upper]⟩

def initial (p : unitInterval) : Cell p :=
  ⟨0, 1, by decide, by simpa using p.2.1, by simpa using p.2.2⟩

def left {p : unitInterval} (c : Cell p) (h : (c.probability : ℝ) ≤ (2 : ℝ)⁻¹) : Cell p where
  index := 2 * c.index
  scale := 2 * c.scale
  scale_pos := by have := c.scale_pos; positivity
  lower := by have := c.lower; push_cast; nlinarith
  upper := by dsimp [probability] at h; push_cast; nlinarith

def right {p : unitInterval} (c : Cell p) (h : (2 : ℝ)⁻¹ ≤ (c.probability : ℝ)) : Cell p where
  index := 2 * c.index + 1
  scale := 2 * c.scale
  scale_pos := by have := c.scale_pos; positivity
  lower := by dsimp [probability] at h; push_cast; nlinarith
  upper := by have := c.upper; push_cast; nlinarith

theorem left_probability {p : unitInterval} (c : Cell p)
    (h : (c.probability : ℝ) ≤ (2 : ℝ)⁻¹) :
    ((c.left h).probability : ℝ) = 2 * (c.probability : ℝ) := by
  dsimp [probability, left]
  push_cast
  ring

theorem right_probability {p : unitInterval} (c : Cell p)
    (h : (2 : ℝ)⁻¹ ≤ (c.probability : ℝ)) :
    ((c.right h).probability : ℝ) = 2 * (c.probability : ℝ) - 1 := by
  dsimp [probability, right]
  push_cast
  ring

end Cell

/-- Credits for the two equally likely half-cells. A midpoint root decides at once. -/
def bitCredit {p : unitInterval} (c : Cell p) (F : Bool → ℝ≥0∞)
    (ε : ℝ≥0∞) (bit : ℕ) : ℝ≥0∞ :=
  if (c.probability : ℝ) = (2 : ℝ)⁻¹ then F (decide (bit = 0))
  else if h : (c.probability : ℝ) ≤ (2 : ℝ)⁻¹ then
    if bit = 0 then RealCoin.credit (c.left h).probability F + 2 * ε else F false
  else if bit = 0 then F true
    else RealCoin.credit (c.right (le_of_not_ge h)).probability F + 2 * ε

private theorem left_mean {p : unitInterval} (c : Cell p)
    (h : (c.probability : ℝ) ≤ (2 : ℝ)⁻¹) :
    CoinMean.bias (c.left h).probability 0 = c.probability := by
  apply Subtype.ext
  change (1 - (1 / 2 : ℝ)) * 0 + (1 / 2 : ℝ) * ((c.left h).probability : ℝ) = _
  rw [Cell.left_probability]
  ring

private theorem right_mean {p : unitInterval} (c : Cell p)
    (h : (2 : ℝ)⁻¹ ≤ (c.probability : ℝ)) :
    CoinMean.bias 1 (c.right h).probability = c.probability := by
  apply Subtype.ext
  change (1 - (1 / 2 : ℝ)) * ((c.right h).probability : ℝ) + (1 / 2 : ℝ) * 1 = _
  rw [Cell.right_probability]
  ring

private theorem credit_zero (F : Bool → ℝ≥0∞) : RealCoin.credit 0 F = F false := by
  simp [RealCoin.credit, RealCoin.pmf]

private theorem credit_one (F : Bool → ℝ≥0∞) : RealCoin.credit 1 F = F true := by
  simp [RealCoin.credit, RealCoin.pmf]

private theorem retry_credit (a b ε : ℝ≥0∞) :
    (a + 2 * ε + b) / 2 = (a + b) / 2 + ε := by
  rw [show a + 2 * ε + b = (a + b) + ε * 2 by ring,
    ENNReal.add_div, ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)]

/-- A half-cell is either deterministic or contains the rescaled root.
Their fair mixture has the original bias; the sole retry receives doubled slack. -/
theorem expectation {p : unitInterval} (c : Cell p) (F : Bool → ℝ≥0∞)
    (ε : ℝ≥0∞) :
    (∑ j ∈ range 2, bitCredit c F ε j) / 2 ≤
      RealCoin.credit c.probability F + ε := by
  simp only [sum_range_succ, sum_range_zero, zero_add]
  by_cases heq : (c.probability : ℝ) = (2 : ℝ)⁻¹
  · have hcredit : RealCoin.credit c.probability F = (F true + F false) / 2 := by
      norm_num [RealCoin.credit, RealCoin.pmf, heq, ENNReal.ofReal_inv_of_pos,
        ENNReal.ofReal_div_of_pos, ENNReal.div_eq_inv_mul]
      ring
    simp [bitCredit, heq, ← hcredit]
  · by_cases h : (c.probability : ℝ) ≤ (2 : ℝ)⁻¹
    · have hm := CoinMean.credit_mean (c.left h).probability 0 F
      rw [left_mean, credit_zero] at hm
      simp only [bitCredit, heq, h, dite_true, ite_false, ite_true, Nat.one_ne_zero]
      rw [retry_credit, hm]
    · have hm := CoinMean.credit_mean 1 (c.right (le_of_not_ge h)).probability F
      rw [right_mean, credit_one] at hm
      simp only [bitCredit, heq, h, dite_false, ite_false, ite_true, Nat.one_ne_zero]
      rw [show F true + (RealCoin.credit (c.right (le_of_not_ge h)).probability F + 2 * ε) =
        RealCoin.credit (c.right (le_of_not_ge h)).probability F + 2 * ε + F true by ring,
        retry_credit, add_comm (RealCoin.credit (c.right (le_of_not_ge h)).probability F), hm]

/-- The sign is fixed on each side of the root; `s` is its sign at zero. -/
def side (p : unitInterval) (s : ℤ) (n den : ℕ) : ℤ :=
  if (n : ℝ) < (p : ℝ) * den then s
  else if (p : ℝ) * den < n then -s else 0

private theorem middle_side {p : unitInterval} (c : Cell p) (s : ℤ) :
    side p s (2 * c.index + 1) (2 * c.scale) =
      if (c.probability : ℝ) < (2 : ℝ)⁻¹ then -s
      else if (2 : ℝ)⁻¹ < (c.probability : ℝ) then s else 0 := by
  have hl : ((2 * c.index + 1 : ℕ) : ℝ) < (p : ℝ) * (2 * c.scale : ℕ) ↔
      (2 : ℝ)⁻¹ < (c.probability : ℝ) := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    dsimp [Cell.probability]
    constructor <;> intro h <;> linarith
  have hr : (p : ℝ) * (2 * c.scale : ℕ) < ((2 * c.index + 1 : ℕ) : ℝ) ↔
      (c.probability : ℝ) < (2 : ℝ)⁻¹ := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    dsimp [Cell.probability]
    constructor <;> intro h <;> linarith
  simp only [side, hl, hr]
  by_cases h : (c.probability : ℝ) < (2 : ℝ)⁻¹
  · simp [h, not_lt.mpr (le_of_lt h)]
  · simp [h]

private theorem midpoint_le_den {p : unitInterval} (hp : (p : ℝ) < 1) (c : Cell p) :
    2 * c.index + 1 ≤ 2 * c.scale := by
  have hscale : (0 : ℝ) < c.scale := by exact_mod_cast c.scale_pos
  have hindex : (c.index : ℝ) < c.scale :=
    c.lower.trans_lt (by nlinarith)
  have : c.index < c.scale := by exact_mod_cast hindex
  omega

private theorem middle_eq {p : unitInterval} (c : Cell p) (s : ℤ)
    (h : (c.probability : ℝ) = (2 : ℝ)⁻¹) :
    side p s (2 * c.index + 1) (2 * c.scale) = 0 := by
  simp [middle_side, h]

private theorem middle_lt {p : unitInterval} (c : Cell p) (s : ℤ)
    (h : (c.probability : ℝ) < (2 : ℝ)⁻¹) :
    side p s (2 * c.index + 1) (2 * c.scale) = -s := by
  simp [middle_side, h]

private theorem middle_gt {p : unitInterval} (c : Cell p) (s : ℤ)
    (h : (2 : ℝ)⁻¹ < (c.probability : ℝ)) :
    side p s (2 * c.index + 1) (2 * c.scale) = s := by
  simp [middle_side, h, not_lt.mpr h.le]

private theorem side_zero (p : unitInterval) (hp : 0 < (p : ℝ)) (s : ℤ) :
    side p s 0 1 = s := by simp [side, hp]

private theorem side_one (p : unitInterval) (hp : (p : ℝ) < 1) (s : ℤ) :
    side p s 1 1 = -s := by simp [side, hp, not_lt.mpr p.2.2]

/-- Locally nameless assembly keeps arbitrary oracle values free from capture. -/
private def loop {rT : Type _} (oracle : Val rT) (s : ℤ) : Exp rT :=
  let recur : Exp rT := .app
    (.app (.bvar 5) (.binop .plus (.binop .mult (.lit (.int 2)) (.bvar 4)) (.bvar 2)))
    (.binop .mult (.lit (.int 2)) (.bvar 3))
  let branch : Exp rT :=
    .cond (.binop .eq (.bvar 0) (.lit (.int 0)))
      (.binop .eq (.bvar 2) (.lit (.int 0)))
      (.cond (.binop .eq (.bvar 2) (.lit (.int 1)))
        (.cond (.binop .eq (.bvar 0) (.lit (.int s))) recur (.lit (.bool false)))
        (.cond (.binop .eq (.bvar 0) (.lit (.int s))) (.lit (.bool true)) recur))
  .fix (.lam (.lam (.app (.lam
    (.app (.lam
      (.app (.lam branch) (.app (.app oracle.fst (.bvar 0)) (.bvar 2))))
      (.binop .plus (.binop .mult (.lit (.int 2)) (.bvar 2)) (.lit (.int 1)))))
    (.app Occil.uniformInt (.lit (.int 2))))))

theorem algebraicRoot_lc {rT : Type _} :
    (Occil.Constants.algebraicRoot : Exp rT).IsLocallyClosed := by is_lc

theorem algebraicRoot_fv {rT : Type _} :
    (Occil.Constants.algebraicRoot : Exp rT).fv = ∅ := by
  simp [Occil.Constants.algebraicRoot, Exp.fv, UniformInt.uniformInt_fv]

@[simp] theorem algebraicRoot_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.Constants.algebraicRoot = Occil.Constants.algebraicRoot :=
  (Exp.open_lc k e _ algebraicRoot_lc).symm

@[simp] theorem algebraicRoot_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.Constants.algebraicRoot : Exp rT) = Occil.Constants.algebraicRoot :=
  Exp.closeRec_fresh x _ k (by simp [algebraicRoot_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT] in
private theorem int_beq (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = (a == b) := rfl

private theorem sign_ne_zero (s : ℤ) (h : s = 1 ∨ s = -1) : (s == 0) = false := by
  rcases h with rfl | rfl <;> decide

private theorem neg_sign_ne_zero (s : ℤ) (h : s = 1 ∨ s = -1) : (-s == 0) = false := by
  rcases h with rfl | rfl <;> decide

private theorem neg_sign_ne_self (s : ℤ) (h : s = 1 ∨ s = -1) : (-s == s) = false := by
  rcases h with rfl | rfl <;> decide

omit [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT] in
private theorem guard_false (s : ℤ) (h : s = 1 ∨ s = -1) :
    ((((BaseLit.int s : BaseLit rT) == .int 0) ||
      ((BaseLit.int (-s) : BaseLit rT) == .int 0)) ||
      ((BaseLit.int s : BaseLit rT) == .int (-s))) = false := by
  rcases h with rfl | rfl <;> rfl

private theorem midpoint_cast (n : ℕ) :
    (2 : ℤ) * n + 1 = ((2 * n + 1 : ℕ) : ℤ) := by simp

private theorem bit_cases {bit : ℕ} (h : bit < 2) : bit = 0 ∨ bit = 1 := by omega

private theorem twp_loop (E : CoPset) (p : unitInterval) (hp : (p : ℝ) < 1)
    (s : ℤ) (hs : s = 1 ∨ s = -1) (oracle : Val rT)
    (horacle : ∀ n den : ℕ, n ≤ den → 0 < den →
      ⊢ tglWp E pl(&oracle.fst #int (n : ℤ) #int (den : ℤ))
        (fun v : Val rT => iprop(⌜v = Val.int (side p s n den)⌝)))
    (F : Bool → ℝ≥0∞) (c : Cell p) :
    ⊢ ↯ (RealCoin.credit c.probability F) -∗
      tglWp E pl(&(loop oracle s) #int (c.index : ℤ) #int ((2 * c.scale : ℕ) : ℤ))
        (fun v : Val rT => iprop(∃ a : Bool, ⌜v = Val.bool a⌝ ∗ ↯ (F a))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert %c Hcredit
  iapply ErrorCredit.Induction.simple (k := 2) hε (by norm_num) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ %c Hcredit
  isimp only [ENNReal.coe_ofNat] at IH
  iterate 3 twp_pure
  simp only [UniformInt.uniformInt_openRec]
  twp_bind pl(&Occil.uniformInt #2)
  icombine Hcredit Hterm as Htotal
  ihave Hsample := ErrorCredit.weaken (expectation c F ε) $$ Htotal
  iapply tglWp_wand
  isplitl [Hsample]
  · iapply (UniformInt.twp_uniformInt E 2 (by decide) (bitCredit c F ε)) $$ Hsample
  iintro %v ⟨%bit, %hv, %hbit, Hcredit⟩
  subst v
  twp_pures
  rw [midpoint_cast]
  twp_bind pl(&oracle.fst #int ((2 * c.index + 1 : ℕ) : ℤ)
    #int ((2 * c.scale : ℕ) : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply horacle (2 * c.index + 1) (2 * c.scale) (midpoint_le_den hp c)
      (by have := c.scale_pos; omega)
  iintro %v %hv
  subst v
  rcases lt_trichotomy (c.probability : ℝ) (2 : ℝ)⁻¹ with hlt | heq | hgt
  · rw [middle_lt c s hlt]
    twp_pures
    rw [int_beq, neg_sign_ne_zero s hs]
    twp_pure
    obtain rfl | rfl := bit_cases hbit
    · twp_pures
      rw [int_beq, neg_sign_ne_self s hs]
      iterate 4 twp_pure
      isimp [bitCredit, hlt.ne, hlt.le] at Hcredit
      ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
      ispecialize IH $$ Hterm %(c.left hlt.le) Hcredit
      isimp [loop, Cell.left, Exp.openRec, ProbLang.openRec_val_fst,
        UniformInt.uniformInt_openRec] at IH
      isimp [Exp.ofVal, UniformInt.uniformInt_openRec]
      iapply IH
    · twp_pures
      rw [int_beq, neg_sign_ne_self s hs]
      twp_pures
      twp_value
      imodintro
      iexists false
      isimp [bitCredit, hlt.ne, hlt.le] at Hcredit
      iframe Hcredit
      itrivial
  · rw [middle_eq c s heq]
    obtain rfl | rfl := bit_cases hbit
    · twp_pures
      twp_value
      imodintro
      iexists true
      isimp [bitCredit, heq] at Hcredit
      iframe Hcredit
      itrivial
    · twp_pures
      twp_value
      imodintro
      iexists false
      isimp [bitCredit, heq] at Hcredit
      iframe Hcredit
      itrivial
  · rw [middle_gt c s hgt]
    twp_pures
    rw [int_beq, sign_ne_zero s hs]
    twp_pure
    obtain rfl | rfl := bit_cases hbit
    · twp_pures
      rw [int_beq, beq_self_eq_true]
      twp_pures
      twp_value
      imodintro
      iexists true
      isimp [bitCredit, ne_of_gt hgt, not_le_of_gt hgt] at Hcredit
      iframe Hcredit
      itrivial
    · twp_pures
      rw [int_beq, beq_self_eq_true]
      iterate 4 twp_pure
      isimp [bitCredit, ne_of_gt hgt, not_le_of_gt hgt] at Hcredit
      ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
      ispecialize IH $$ Hterm %(c.right hgt.le) Hcredit
      isimp [loop, Cell.right, Exp.openRec, ProbLang.openRec_val_fst,
        UniformInt.uniformInt_openRec] at IH
      isimp [Exp.ofVal, UniformInt.uniformInt_openRec]
      iapply IH

/-- A rational sign oracle samples its unique root in the open unit interval. -/
theorem twp_algebraicRoot (E : CoPset) (p : unitInterval)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (s : ℤ) (hs : s = 1 ∨ s = -1) (oracle : Val rT)
    (horacle : ∀ n den : ℕ, n ≤ den → 0 < den →
      ⊢ tglWp E pl(&oracle.fst #int (n : ℤ) #int (den : ℤ))
        (fun v : Val rT => iprop(⌜v = Val.int (side p s n den)⌝)))
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit p F) -∗
      tglWp E pl(&Occil.Constants.algebraicRoot &oracle.fst #())
        (fun v : Val rT => iprop(∃ a : Bool, ⌜v = Val.bool a⌝ ∗ ↯ (F a))) := by
  have hloop := twp_loop (rT := rT) (GF := GF) E p hp1 s hs oracle horacle F (Cell.initial p)
  simp [loop, Cell.initial, Cell.probability] at hloop
  iintro Hcredit
  twp_pures
  twp_bind pl(&oracle.fst #0 #1)
  iapply tglWp_wand
  isplitl []
  · iapply horacle 0 1 (by decide) (by decide)
  iintro %v %hv
  subst v
  rw [side_zero p hp0]
  twp_pures
  twp_bind pl(&oracle.fst #1 #1)
  iapply tglWp_wand
  isplitl []
  · iapply horacle 1 1 (by decide) (by decide)
  iintro %v %hv
  subst v
  rw [side_one p hp1]
  twp_pures
  rw [guard_false s hs]
  iterate 2 twp_pure
  simp only [UniformInt.uniformInt_closeRec, UniformInt.uniformInt_openRec]
  iapply hloop $$ Hcredit

/-- Typed Bernoulli law for either orientation of the sign oracle. -/
theorem algebraicRoot_distSpec (E : CoPset) (p : unitInterval)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (s : ℤ) (hs : s = 1 ∨ s = -1) (oracle : Val rT)
    (horacle : ∀ n den : ℕ, n ≤ den → 0 < den →
      ⊢ tglWp E pl(&oracle.fst #int (n : ℤ) #int (den : ℤ))
        (fun v : Val rT => iprop(⌜v = Val.int (side p s n den)⌝))) :
    IsDistSpec (GF := GF) E pl(&Occil.Constants.algebraicRoot &oracle.fst #())
      (RealCoin.law p) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law] using
      wand_entails (twp_algebraicRoot E p hp0 hp1 s hs oracle horacle F)

end specification

end

end SampLib.AlgebraicRoot
