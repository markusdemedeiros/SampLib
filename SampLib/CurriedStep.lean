import SampLib.BetaStep
import Metrology.Iris.LocalBI

/-! # Checked beta reduction of a curried source

Keep the named body opaque while applying its argument list. Opening equations
and local-closure certificates are proved once, outside sampler symbolic execution.
-/

open ProbLang

namespace SampLib.CurriedStep

def lambdas {rT : Type} : ℕ → Exp rT → Exp rT
  | 0, body => body
  | n + 1, body => .lam (lambdas n body)

def context {rT : Type} (args : List (Val rT)) : Ectx rT := args.map EctxItem.appL

def application {rT : Type} (args : List (Val rT)) (fn : Exp rT) : Exp rT :=
  (context args).fill fn

def opened {rT : Type} : List (Val rT) → Exp rT → Exp rT
  | [], body => body
  | v :: vs, body => opened vs (Exp.openRec vs.length v.fst body)

theorem lcb_lambdas {rT : Type} (n k : ℕ) (body : Exp rT) :
    Exp.lcb k (lambdas n body) = Exp.lcb (k + n) body := by
  induction n generalizing k with
  | zero => simp [lambdas]
  | succ n ih =>
    simpa [lambdas, Exp.lcb, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1)

theorem openRec_lambdas {rT : Type} (n k : ℕ) (v body : Exp rT) :
    Exp.openRec k v (lambdas n body) = lambdas n (Exp.openRec (k + n) v body) := by
  induction n generalizing k with
  | zero => simp [lambdas]
  | succ n ih =>
    simpa [lambdas, Exp.openRec, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      congrArg Exp.lam (ih (k + 1))

theorem lambdas_lc {rT : Type} (n : ℕ) (body : Exp rT) (hc : Exp.lcb n body = true) :
    (lambdas n body).IsLocallyClosed := by
  apply Exp.lcb_imp_lc
  simpa only [lcb_lambdas, Nat.zero_add] using hc

section specification

open Iris Iris.BI TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]
local bi (IProp GF)

/-- Execute all curried applications using only the checked single-beta rule. -/
theorem twp_apply (E : CoPset) (K : Ectx rT) (args : List (Val rT)) (body : Exp rT)
    (hc : Exp.lcb args.length body = true) (Φ : Val rT → IProp GF) :
    tglWp E (K.fill (opened args body)) Φ ⊢
      tglWp E (K.fill (application args (lambdas args.length body))) Φ := by
  induction args generalizing body with
  | nil => exact BI.BIBase.Entails.refl _
  | cons v vs ih =>
    have hnext : Exp.lcb vs.length (Exp.openRec vs.length v.fst body) = true :=
      Exp.lcb_openRec (Exp.lcb_ofVal vs.length v) hc
    have hclosed : (Exp.lam (lambdas vs.length body)).IsLocallyClosed :=
      lambdas_lc (vs.length + 1) body hc
    apply BI.BIBase.Entails.trans (ih (Exp.openRec vs.length v.fst body) hnext)
    simpa only [opened, application, context, List.map_cons, List.length_cons,
      lambdas, Ectx.fill_append, Exp.open', openRec_lambdas, Nat.zero_add,
      Ectx.fill, List.foldl_cons, List.foldl_append, EctxItem.fillItem, Exp.ofVal, flip] using
      twp_beta E (context vs ++ K) (lambdas vs.length body) v hclosed Φ

/-- Unfold a named recursive function, then apply its curried arguments. -/
theorem twp_fix_apply (E : CoPset) (K : Ectx rT) (v : Val rT) (vs : List (Val rT))
    (body : Exp rT) (hc : Exp.lcb (vs.length + 2) body = true)
    (Φ : Val rT → IProp GF) :
    let fn := Exp.fix (lambdas (vs.length + 1) body)
    tglWp E (K.fill (opened (v :: vs) (Exp.openRec (vs.length + 1) fn body))) Φ ⊢
      tglWp E (K.fill (application (v :: vs) fn)) Φ := by
  let fn := Exp.fix (lambdas (vs.length + 1) body)
  have hfn : fn.IsLocallyClosed := by
    apply Exp.lcb_imp_lc
    change Exp.lcb 1 (lambdas (vs.length + 1) body) = true
    rw [lcb_lambdas]
    have hlength : 1 + (vs.length + 1) = vs.length + 2 := by omega
    rwa [hlength]
  let self : Val rT := ⟨fn, .fix hfn, hfn⟩
  have hbody : Exp.lcb (vs.length + 1) (Exp.openRec (vs.length + 1) fn body) = true :=
    Exp.lcb_openRec (Exp.lcb_ofVal (vs.length + 1) self) hc
  apply BI.BIBase.Entails.trans (twp_apply E K (v :: vs) _ hbody Φ)
  have hfix : tglWp E ((context vs ++ K).fill
      (.app (Exp.open' (lambdas (vs.length + 1) body) fn) v.fst)) Φ ⊢
      tglWp E ((context vs ++ K).fill (.app fn v.fst)) Φ :=
    twp_pure_step_ctx (context vs ++ K) (v.fst.isValue ∧ fn.IsLocallyClosed)
      ⟨⟨v.snd⟩, hfn⟩
  simpa only [opened, application, context, List.map_cons, List.length_cons,
    Ectx.fill_append, Exp.open', openRec_lambdas, Nat.zero_add,
    Ectx.fill, List.foldl_cons, List.foldl_append, EctxItem.fillItem, Exp.ofVal, flip] using hfix

end specification

end SampLib.CurriedStep
