import SampLib.EntropyPool
import SampLib.Distributions.BitRecycler
import SampLib.CurriedStep

/-! # The bounded-width phase of the entropy recycler

After every fresh bit the width is less than twice the requested bound. Thus
an accepting quotient is one and the physical pool resets to `(0,1)`. Finite
horizon credit follows the actual retained rank; no fixed-rank uniform law is used.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.EntropyPool

noncomputable section

/-- The exact local recursion in `recycledUniform`, with its original argument order. -/
@[pl_fold] def loop {rT : Type} (pool : Loc) (n : ℕ) : Exp rT := pl%
  rec draw value width :=
    if width < #int (n : ℤ) then
      draw (value * #2 + rand(#2, #())) (width * #2)
    else
      let quotient := width / #int (n : ℤ);
      let accepted := quotient * #int (n : ℤ);
      if value < accepted then
        let result := value % #int (n : ℤ);
        #loc pool ← ((value / #int (n : ℤ)), quotient);
        result
      else draw (value - accepted) (width - accepted)

theorem loop_lc {rT : Type} (pool : Loc) (n : ℕ) : (loop pool n : Exp rT).IsLocallyClosed := by
  is_lc

theorem loop_fv {rT : Type} (pool : Loc) (n : ℕ) : (loop pool n : Exp rT).fv = ∅ := by
  simp [loop, Exp.fv]

@[simp] theorem loop_openRec {rT : Type} (pool : Loc) (n k : ℕ) (e : Exp rT) :
    Exp.openRec k e (loop pool n) = loop pool n :=
  (Exp.open_lc k e _ (loop_lc pool n)).symm

@[simp] theorem loop_closeRec {rT : Type} (pool : Loc) (n k : ℕ) (x : Var) :
    Exp.closeRec k x (loop pool n : Exp rT) = loop pool n :=
  Exp.closeRec_fresh x _ k (by simp [loop_fv])

namespace Program

def body {rT : Type} (pool : Loc) (n : ℕ) : Exp rT :=
  match (loop pool n : Exp rT) with
  | .fix (.lam (.lam body)) => body
  | _ => .fail

/-- The source after its three binders have received self, value and width. -/
def step {rT : Type} (pool : Loc) (n value width : ℕ) : Exp rT := pl(
  if #int (width : ℤ) < #int (n : ℤ) then
    &(loop pool n) (#int (value : ℤ) * #2 + rand(#2, #())) (#int (width : ℤ) * #2)
  else
    let quotient := #int (width : ℤ) / #int (n : ℤ);
    let accepted := quotient * #int (n : ℤ);
    if #int (value : ℤ) < accepted then
      let result := #int (value : ℤ) % #int (n : ℤ);
      #loc pool ← ((#int (value : ℤ) / #int (n : ℤ)), quotient);
      result
    else &(loop pool n) (#int (value : ℤ) - accepted) (#int (width : ℤ) - accepted))

private theorem body_lcb {rT : Type} (pool : Loc) (n : ℕ) :
    Exp.lcb 3 (body (rT := rT) pool n) = true := by lcb_decide

theorem opened {rT : Type} (pool : Loc) (n value width : ℕ) :
    CurriedStep.opened [Val.int value, Val.int width]
      (Exp.openRec 2 (loop pool n) (body pool n)) = (step pool n value width : Exp rT) := by
  simp [CurriedStep.opened, body, step, loop, Exp.openRec,
    Exp.close, Exp.closeRec, Var.internal.injEq]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem twp_open (E : CoPset) (pool : Loc) (n value width : ℕ)
    (Φ : Val rT → IProp GF) :
    tglWp E (step pool n value width) Φ ⊢
      tglWp E pl(&(loop pool n) #int (value : ℤ) #int (width : ℤ)) Φ := by
  have h := CurriedStep.twp_fix_apply (rT := rT) (GF := GF) E [] (Val.int value)
    [Val.int width] (body pool n) (body_lcb pool n) Φ
  change tglWp E (CurriedStep.opened [Val.int value, Val.int width]
      (Exp.openRec 2 (loop pool n) (body pool n))) Φ ⊢
    tglWp E pl(&(loop pool n) #int (value : ℤ) #int (width : ℤ)) Φ at h
  rwa [opened] at h

end specification

end Program

private theorem narrow_true (n width : ℕ) (h : width < n) :
    decide ((width : ℤ) < n) = true := decide_eq_true (by exact_mod_cast h)

private theorem narrow_false (n width : ℕ) (h : n ≤ width) :
    decide ((width : ℤ) < n) = false := decide_eq_false (by exact_mod_cast not_lt.mpr h)

private theorem quotient_one (n width : ℕ) (hlo : n ≤ width) (hhi : width < 2 * n) :
    (width : ℤ) / n = 1 := by
  have h : width / n = 1 := Nat.div_eq_of_lt_le (by simpa) (by simpa)
  rw [← Int.natCast_ediv, h]
  rfl

private theorem division_zero (n value : ℕ) (h : value < n) : (value : ℤ) / n = 0 := by
  rw [← Int.natCast_ediv, Nat.div_eq_of_lt h]
  rfl

private theorem remainder_small (n value : ℕ) (h : value < n) : (value : ℤ) % n = value := by
  rw [← Int.natCast_emod, Nat.mod_eq_of_lt h]

private theorem sub_cast (a b : ℕ) (h : b ≤ a) :
    (a : ℤ) - b = ((a - b : ℕ) : ℤ) := (Nat.cast_sub h).symm

private theorem double_cast (w : ℕ) : (w : ℤ) * 2 = ((w * 2 : ℕ) : ℤ) := by norm_cast

private theorem prefix_cast (v : ℕ) (b : ℤ) (hb : 0 ≤ b) :
    (v : ℤ) * 2 + b = ((v * 2 + b.toNat : ℕ) : ℤ) := by
  simp [Nat.cast_add, Nat.cast_mul, Int.toNat_of_nonneg hb]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Every fresh-bit acceptance restores the exact singleton pool. -/
def loopPost (pool : Loc) (n : ℕ) (F : ℕ → ℝ≥0∞) (result : Val rT) : IProp GF :=
  iprop(∃ r : ℕ, ⌜result = Val.int (r : ℤ) ∧ r < n⌝ ∗
    appHeapFrag pool (poolVal (rT := rT) 0 1) ∗ ↯ (F r))

private theorem twp_wide (E : CoPset) (pool : Loc) (stored : Val rT)
    (n T width value : ℕ) (_hn : 0 < n) (hwide : n ≤ width)
    (hwidth : width < 2 * n) (hvalue : value < width) (F : ℕ → ℝ≥0∞)
    (hrec : ∀ w v, w < n → v < w →
      iprop(appHeapFrag pool stored ∗ ↯ (BitRecycler.credit .lower n F T w v)) ⊢
        tglWp E pl(&(loop pool n) #int (v : ℤ) #int (w : ℤ)) (loopPost pool n F)) :
    iprop(appHeapFrag pool stored ∗
      ↯ (BitRecycler.kernel .lower n F (BitRecycler.credit .lower n F T) width value)) ⊢
      tglWp E pl(&(loop pool n) #int (value : ℤ) #int (width : ℤ)) (loopPost pool n F) := by
  iintro ⟨Hpool, Hcredit⟩
  iapply Program.twp_open E pool n value width _
  unfold Program.step
  twp_pure
  rw [narrow_false n width hwide]
  twp_pures
  rw [quotient_one n width hwide hwidth, one_mul]
  isimp only [BitRecycler.kernel, ite_eq_left hwide] at Hcredit
  by_cases haccept : value < n
  · rw [decide_eq_true (by exact_mod_cast haccept : (value : ℤ) < n)]
    twp_pures
    rw [division_zero n value haccept, remainder_small n value haccept]
    twp_bind (Exp.store pl(#loc pool) (Exp.ofVal (poolVal (rT := rT) 0 1)))
    iapply (twp_store (v := poolVal (rT := rT) 0 1))
    iframe Hpool
    iintro Hpool
    twp_pures
    twp_value
    imodintro
    isimp only [loopPost]
    iexists value
    isimp only [ite_eq_left haccept] at Hcredit
    iframe Hpool Hcredit
    ipureintro
    exact ⟨rfl, haccept⟩
  · rw [decide_eq_false (by exact_mod_cast haccept : ¬(value : ℤ) < n)]
    iterate 3 twp_pure
    rw [sub_cast value n (Nat.le_of_not_gt haccept), sub_cast width n hwide]
    isimp only [loop_openRec, loop_closeRec, Exp.ofVal]
    isimp only [ite_eq_right haccept] at Hcredit
    iapply hrec (width - n) (value - n) (by omega)
      (BitRecycler.lower_recycle_lt n width value (Nat.le_of_not_gt haccept) hvalue)
    iframe Hpool Hcredit

/-- Follow the actual fresh bits with a finite cutoff and an arbitrary stored heap value. -/
theorem twp_loop_horizon (E : CoPset) (pool : Loc) (stored : Val rT)
    (n T width value : ℕ) (hn : 0 < n) (hwidth : width < n) (hvalue : value < width)
    (F : ℕ → ℝ≥0∞) :
    iprop(appHeapFrag pool stored ∗ ↯ (BitRecycler.credit .lower n F T width value)) ⊢
      tglWp E pl(&(loop pool n) #int (value : ℤ) #int (width : ℤ)) (loopPost pool n F) := by
  induction T generalizing width value with
  | zero =>
    iintro ⟨Hpool, Hcredit⟩
    isimp only [BitRecycler.credit_zero] at Hcredit
    iexfalso
    iapply ErrorCredit.contradict le_rfl $$ Hcredit
  | succ T ih =>
    iintro ⟨Hpool, Hcredit⟩
    iapply Program.twp_open E pool n value width _
    unfold Program.step
    twp_pure
    rw [narrow_true n width hwidth]
    iterate 2 twp_pure
    twp_bind pl(rand(#2, #()))
    iapply (twp_rand_exp (ε₂ := BitRecycler.bitCredit .lower n T F width value)
      (by decide) (BitRecycler.expectation .lower n T F width value).le) $$ Hcredit
    iintro %b ⟨%hb, Hcredit⟩
    have hbNat : b.toNat < 2 := by omega
    have hexpanded := BitRecycler.expanded_lt width value b.toNat hvalue hbNat
    iterate 2 twp_pure
    isimp only [Exp.ofVal]
    rw [prefix_cast value b hb.1, double_cast width]
    by_cases hwide : n ≤ width * 2
    · isimp only [BitRecycler.bitCredit] at Hcredit
      iapply twp_wide E pool stored n T (width * 2) (value * 2 + b.toNat) hn hwide
        (by omega) hexpanded F ih
      iframe Hpool Hcredit
    · isimp only [BitRecycler.bitCredit, BitRecycler.kernel, ite_eq_right hwide] at Hcredit
      iapply ih (width * 2) (value * 2 + b.toNat) (Nat.lt_of_not_ge hwide) hexpanded
      iframe Hpool Hcredit

end specification

end

end SampLib.EntropyPool
