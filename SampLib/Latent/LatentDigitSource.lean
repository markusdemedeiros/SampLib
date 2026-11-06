import SampLib.Core.BetaStep
import SampLib.Latent.Syntax.PSRNDigits

/-! # Cached deterministic transport for conditional digit readers -/

open ProbLang Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

namespace SampLib.LatentDigits.Syntax

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]
local bi (IProp GF)

/-- Return the exact interval oracle after the root allocation's final beta step. -/
theorem twp_allocated_oracle (E : CoPset) (nextBit : Val rT) (root : Loc)
    (Φ : Val rT → IProp GF) :
    tglWp E (oracleVal nextBit root).fst Φ ⊢
      tglWp E (.app (.lam (rootBody nextBit)) (.lit (.loc root))) Φ := by
  rw [← allocated_oracle]
  exact twp_beta E [] (rootBody nextBit) (.loc root) (rootBinderVal nextBit).lc Φ

private theorem unfold_read (E : CoPset) (K : Ectx rT) (nextBit : Val rT) (node : Loc)
    (Φ : Val rT → IProp GF) :
    tglWp E (K.fill (.app (unfoldedVal nextBit).fst (.lit (.loc node)))) Φ ⊢
      tglWp E (K.fill (.app (readVal nextBit).fst (.lit (.loc node)))) Φ := by
  have : PureExec ((.lit (.loc node) : Exp rT).isValue ∧ (readVal nextBit).fst.IsLocallyClosed) 1
      (.app (readVal nextBit).fst (.lit (.loc node)))
      (.app (unfoldedVal nextBit).fst (.lit (.loc node))) :=
    pureExec_app_fix (body := .lam (.lam (.lam (.lam (loopTemplate nextBit)))))
      (v := (.lit (.loc node) : Exp rT))
  exact twp_pure_step_ctx K _ ⟨⟨(Val.loc node : Val rT).snd⟩, (readVal nextBit).lc⟩

private theorem node_beta (E : CoPset) (K : Ectx rT) (nextBit : Val rT) (node : Loc)
    (Φ : Val rT → IProp GF) :
    tglWp E (K.fill (nodeVal nextBit node).fst) Φ ⊢
      tglWp E (K.fill (.app (unfoldedVal nextBit).fst (.lit (.loc node)))) Φ :=
  twp_beta E K (.lam (.lam (.lam (selfBody nextBit)))) (.loc node) (unfoldedVal nextBit).lc Φ

private theorem remaining_beta (E : CoPset) (K : Ectx rT) (nextBit : Val rT)
    (node : Loc) (remaining : ℤ) (Φ : Val rT → IProp GF) :
    tglWp E (K.fill (remainingVal nextBit node remaining).fst) Φ ⊢
      tglWp E (K.fill (.app (nodeVal nextBit node).fst (.lit (.int remaining)))) Φ :=
  twp_beta E K (.lam (.lam (nodeBody nextBit node))) (.int remaining) (nodeVal nextBit node).lc Φ

private theorem numerator_beta (E : CoPset) (K : Ectx rT) (nextBit : Val rT)
    (node : Loc) (remaining numerator : ℤ) (Φ : Val rT → IProp GF) :
    tglWp E (K.fill (numeratorVal nextBit node remaining numerator).fst) Φ ⊢
      tglWp E (K.fill (.app (remainingVal nextBit node remaining).fst (.lit (.int numerator)))) Φ :=
  twp_beta E K (.lam (remainingBody nextBit node remaining)) (.int numerator)
    (remainingVal nextBit node remaining).lc Φ

private theorem denominator_beta (E : CoPset) (nextBit : Val rT)
    (node : Loc) (remaining numerator denominator : ℤ) (Φ : Val rT → IProp GF) :
    tglWp E (Exp.open' (numeratorBody nextBit node remaining numerator)
      (.lit (.int denominator))) Φ ⊢
      tglWp E (.app (numeratorVal nextBit node remaining numerator).fst
        (.lit (.int denominator))) Φ :=
  twp_beta E [] (numeratorBody nextBit node remaining numerator) (.int denominator)
    (numeratorVal nextBit node remaining numerator).lc Φ

/-- Fix unfolding and four beta steps expose exactly the source's numeric branch body. -/
theorem twp_read_apply (E : CoPset) (nextBit : Val rT) (node : Loc)
    (remaining numerator denominator : ℤ) (Φ : Val rT → IProp GF) :
    tglWp E (openedReadCode nextBit node remaining numerator denominator) Φ ⊢
      tglWp E pl(&(readVal nextBit).fst #loc node #int remaining #int numerator #int denominator)
        Φ := by
  iintro Hbody
  have hfix := unfold_read E
    [.appL (.int remaining), .appL (.int numerator), .appL (.int denominator)] nextBit node Φ
  simp only [Ectx.fill, Function.flip_def, EctxItem.fillItem, List.foldl_cons,
    List.foldl_nil, Exp.ofVal] at hfix
  iapply hfix
  have hnode := node_beta E
    [.appL (.int remaining), .appL (.int numerator), .appL (.int denominator)] nextBit node Φ
  simp only [Ectx.fill, Function.flip_def, EctxItem.fillItem, List.foldl_cons,
    List.foldl_nil, Exp.ofVal] at hnode
  iapply hnode
  have hremaining := remaining_beta E [.appL (.int numerator), .appL (.int denominator)]
    nextBit node remaining Φ
  simp only [Ectx.fill, Function.flip_def, EctxItem.fillItem, List.foldl_cons,
    List.foldl_nil, Exp.ofVal] at hremaining
  iapply hremaining
  have hnumerator := numerator_beta E [.appL (.int denominator)] nextBit node remaining numerator Φ
  simp only [Ectx.fill, Function.flip_def, EctxItem.fillItem, List.foldl_cons,
    List.foldl_nil, Exp.ofVal] at hnumerator
  iapply hnumerator
  iapply denominator_beta E nextBit node remaining numerator denominator Φ
  simp only [Exp.open', numeratorBody, remainingBody, nodeBody, selfBody, read_apply]
  iexact Hbody

private theorem oracle_beta (E : CoPset) (nextBit : Val rT) (root : Loc) (n : ℕ)
    (Φ : Val rT → IProp GF) :
    tglWp E (Exp.open' (oracleBody nextBit root) (.lit (.int (n : ℤ)))) Φ ⊢
      tglWp E pl(&(oracleVal nextBit root).fst #int (n : ℤ)) Φ :=
  twp_beta E [] (oracleBody nextBit root) (.int n) (oracleVal nextBit root).lc Φ

/-- A nonnegative observation enters the cached reader without unfolding its fixpoint. -/
theorem twp_oracle_apply (E : CoPset) (nextBit : Val rT) (root : Loc) (n : ℕ)
    (Φ : Val rT → IProp GF) :
    tglWp E pl(&(readVal nextBit).fst #loc root #int (n : ℤ) #0 #1) Φ ⊢
      tglWp E pl(&(oracleVal nextBit root).fst #int (n : ℤ)) Φ := by
  iintro Hread
  iapply oracle_beta E nextBit root n Φ
  rw [oracle_open]
  twp_pure
  twp_pure
  simp only [bind]
  have hcall := twp_beta E [] (readCallBody root n) (readVal nextBit) (by is_lc) Φ
  simp only [Ectx.fill_nil] at hcall
  iapply hcall
  simp only [readCallBody, Exp.open', Exp.openRec, ite_true]
  iexact Hread

end SampLib.LatentDigits.Syntax
