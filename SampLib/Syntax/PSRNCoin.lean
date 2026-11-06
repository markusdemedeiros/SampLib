import SampLib.Syntax.PSRNLess

/-! # Opening the fresh-uniform conditional coin -/

open ProbLang

namespace SampLib.LatentReal.Coin.Program

private def body {rT : Type} (source : Exp rT) : Exp rT :=
  .app (.app Occil.PSRN.less (.app Occil.PSRN.newUniform (.lit .unit))) source

def sourceCode {rT : Type} : Exp rT := .lam (.lam (body (.bvar 1)))

theorem source_eq {rT : Type} : (Occil.PSRN.coin : Exp rT) = sourceCode := by
  kernel_rfl

theorem source_lc {rT : Type} : (sourceCode : Exp rT).IsLocallyClosed := by
  rw [← source_eq]
  is_lc

private theorem uniform_openRec {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.PSRN.newUniform = Occil.PSRN.newUniform :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem value_lc {rT : Type} (source : Val rT) :
    (Exp.lam (body source.fst)).IsLocallyClosed := by
  apply Exp.lcb_imp_lc
  have hs (k : ℕ) : Exp.lcb k source.fst = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb source.lc) (Nat.zero_le k)
  have hl (k : ℕ) : Exp.lcb k (Occil.PSRN.less : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb Less.Program.source_lc) (Nat.zero_le k)
  have hu (k : ℕ) : Exp.lcb k (Occil.PSRN.newUniform : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb (by is_lc)) (Nat.zero_le k)
  simp [body, Exp.lcb, hs, hl, hu]

/-- The actual unit callback, retaining its original source handle. -/
def value {rT : Type} (source : Val rT) : Val rT :=
  ⟨.lam (body source.fst), .lam (value_lc source), value_lc source⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]
local bi (IProp GF)

/-- Open the source and unit arguments before allocating the fresh comparison uniform. -/
theorem twp_open (E : CoPset) (source : Val rT) (Φ : Val rT → IProp GF) :
    tglWp E pl(&Occil.PSRN.less (&Occil.PSRN.newUniform #()) &source.fst) Φ ⊢
      tglWp E pl(&Occil.PSRN.coin &source.fst #()) Φ := by
  iintro H
  rw [source_eq]
  ieval (change _ ⊢ tglWp E (Ectx.fill [.appL (.unit : Val rT)]
    (.app (.lam (.lam (body (.bvar 1)))) source.fst)) Φ)
  iapply (twp_beta E [.appL (.unit : Val rT)] (.lam (body (.bvar 1))) source source_lc Φ)
  simp only [Exp.open', body, Exp.openRec, Less.Program.less_openRec, uniform_openRec,
    ↓reduceIte]
  twp_pure
  isimp only [Less.Program.less_openRec, uniform_openRec]
  iexact H

/-- The returned callback performs the same comparison after its unit argument. -/
theorem twp_open_value (E : CoPset) (source : Val rT) (Φ : Val rT → IProp GF) :
    tglWp E pl(&Occil.PSRN.less (&Occil.PSRN.newUniform #()) &source.fst) Φ ⊢
      tglWp E pl(&(value source).fst #()) Φ := by
  iintro H
  unfold value
  twp_pure
  isimp only [body, Exp.open', Exp.openRec, Less.Program.less_openRec, uniform_openRec,
    (Exp.open_lc 0 (.lit .unit) source.fst source.lc).symm]
  iexact H

end specification

end SampLib.LatentReal.Coin.Program
