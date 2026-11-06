import SampLib.Constants.Laws.AlgebraicRoot
import SampLib.Uniform.UniformInt
import Samplers.Constants.Engines

/-! # Bernoulli sampling by rational sign tests

The sign oracle locates one fixed root. A fair bit chooses a half-cell; only the
half containing the root needs another sign test.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.AlgebraicRoot

noncomputable section

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
