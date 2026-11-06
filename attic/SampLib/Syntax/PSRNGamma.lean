import SampLib.PSRN.Syntax.PSRNGammaInteger

/-! # Literal continuations of the fractional gamma constructor -/

open ProbLang

namespace SampLib.PSRNGamma.Program

open scoped SampLib.PSRNGammaInteger.Program

scoped instance beta_closed {rT : Type} : ClosedExp (Occil.PSRN.newBeta : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

scoped instance multiply_closed {rT : Type} : ClosedExp (Occil.PSRN.multiply : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

scoped instance rational_closed {rT : Type} : ClosedExp (Occil.PSRN.rational : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

open scoped SampLib.PSRNGamma.Program

def bind {rT : Type} (e body : Exp rT) : Exp rT := .app (.lam body) e

def beta {rT : Type} (r d : ℤ) : Exp rT :=
  pl(&Occil.PSRN.newBeta #r #d #int (d - r) #d #())

def exponential {rT : Type} (a b : ℤ) : Exp rT :=
  pl(&Occil.PSRN.newExponential #a #b #())

def afterExponential {rT : Type} (integer beta : Val rT) : Exp rT :=
  .app (.app Occil.PSRN.add integer.fst)
    (.app (.app Occil.PSRN.multiply beta.fst) (.bvar 0))

def afterBeta {rT : Type} (a b : ℤ) (integer : Val rT) : Exp rT :=
  bind (exponential a b)
    (.app (.app Occil.PSRN.add integer.fst)
      (.app (.app Occil.PSRN.multiply (.bvar 1)) (.bvar 0)))

def afterInteger {rT : Type} (r d a b : ℤ) : Exp rT :=
  bind (beta r d)
    (bind (exponential a b)
      (.app (.app Occil.PSRN.add (.bvar 2))
        (.app (.app Occil.PSRN.multiply (.bvar 1)) (.bvar 0))))

/-- The source branch after testing its nonzero fractional remainder. -/
def fractional {rT : Type} (integer : Exp rT) (r d a b : ℤ) : Exp rT :=
  bind integer (afterInteger r d a b)

theorem afterInteger_lc {rT : Type} (r d a b : ℤ) :
    (Exp.lam (afterInteger (rT := rT) r d a b)).IsLocallyClosed := by
  have hbeta (n : ℕ) : Exp.lcb n (Occil.PSRN.newBeta : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb (beta_closed (rT := rT)).lc) (Nat.zero_le _)
  have hexp (n : ℕ) : Exp.lcb n (Occil.PSRN.newExponential : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb (PSRNGammaInteger.Program.exponential_closed (rT := rT)).lc)
      (Nat.zero_le _)
  have hadd (n : ℕ) : Exp.lcb n (Occil.PSRN.add : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb (PSRNGammaInteger.Program.add_closed (rT := rT)).lc)
      (Nat.zero_le _)
  have hmul (n : ℕ) : Exp.lcb n (Occil.PSRN.multiply : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb (multiply_closed (rT := rT)).lc) (Nat.zero_le _)
  apply Exp.lcb_imp_lc
  simp [afterInteger, bind, beta, exponential, Exp.lcb, hbeta, hexp, hadd, hmul]

theorem opened_afterInteger {rT : Type} (r d a b : ℤ) (integer : Val rT) :
    Exp.open' (afterInteger r d a b) integer.fst =
      bind (beta r d) (afterBeta a b integer) := by
  simp [afterInteger, afterBeta, bind, beta, exponential, Exp.open', Exp.openRec,
    ClosedExp.openRec]

theorem opened_afterBeta {rT : Type} (a b : ℤ) (integer beta : Val rT) :
    Exp.open' (afterBeta a b integer) beta.fst =
      bind (exponential a b) (afterExponential integer beta) := by
  simp [afterBeta, afterExponential, bind, exponential, Exp.open', Exp.openRec,
    ClosedExp.openRec, ProbLang.openRec_val_fst]

theorem opened_afterExponential {rT : Type} (integer beta exponential : Val rT) :
    Exp.open' (afterExponential integer beta) exponential.fst =
      pl(&Occil.PSRN.add &integer.fst
        (&Occil.PSRN.multiply &beta.fst &exponential.fst)) := by
  simp [afterExponential, Exp.open', Exp.openRec, ClosedExp.openRec,
    ProbLang.openRec_val_fst]

theorem afterBeta_lc {rT : Type} (a b : ℤ) (integer : Val rT) :
    (Exp.lam (afterBeta a b integer)).IsLocallyClosed := by
  have hi (n : ℕ) : Exp.lcb n integer.fst = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb integer.lc) (Nat.zero_le _)
  have hexp (n : ℕ) : Exp.lcb n (Occil.PSRN.newExponential : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb (PSRNGammaInteger.Program.exponential_closed (rT := rT)).lc)
      (Nat.zero_le _)
  have hadd (n : ℕ) : Exp.lcb n (Occil.PSRN.add : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb (PSRNGammaInteger.Program.add_closed (rT := rT)).lc)
      (Nat.zero_le _)
  have hmul (n : ℕ) : Exp.lcb n (Occil.PSRN.multiply : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb (multiply_closed (rT := rT)).lc) (Nat.zero_le _)
  apply Exp.lcb_imp_lc
  simp [afterBeta, bind, exponential, Exp.lcb, hi, hexp, hadd, hmul]

theorem afterExponential_lc {rT : Type} (integer beta : Val rT) :
    (Exp.lam (afterExponential integer beta)).IsLocallyClosed := by
  have hi (n : ℕ) : Exp.lcb n integer.fst = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb integer.lc) (Nat.zero_le _)
  have hb (n : ℕ) : Exp.lcb n beta.fst = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb beta.lc) (Nat.zero_le _)
  have hadd (n : ℕ) : Exp.lcb n (Occil.PSRN.add : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb (PSRNGammaInteger.Program.add_closed (rT := rT)).lc)
      (Nat.zero_le _)
  have hmul (n : ℕ) : Exp.lcb n (Occil.PSRN.multiply : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb (multiply_closed (rT := rT)).lc) (Nat.zero_le _)
  apply Exp.lcb_imp_lc
  simp [afterExponential, Exp.lcb, hi, hb, hadd, hmul]

end SampLib.PSRNGamma.Program
