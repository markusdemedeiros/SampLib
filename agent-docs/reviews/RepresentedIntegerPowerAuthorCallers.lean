import SampLib.LatentRepresentedIntegerPower

open ProbLang
open scoped ENNReal

namespace RepresentedIntegerPowerAuthorCallers

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib SampLib.LatentReal

private theorem observed_unique {Ω S : Type} [MeasurableSpace Ω] (D : Model Ω S)
    (R : Representation D) (s : S) (n : ℕ) (I J : RationalInterval)
    (hI : R.Observed s n I) (hJ : R.Observed s n J) : I = J := by
  obtain ⟨x, hx, hy⟩ := (hI.and hJ).exists
  exact hx.trans hy.symm

private def twice {rT : Type} (handle : Val rT) (precision : ℕ) : Exp rT :=
  let call := Exp.app handle.fst (.lit (.int (precision : ℤ)))
  .app (.lam (.app (.lam (.pair (.bvar 1) (.bvar 0))) call)) call

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

example (E : CoPset) (D : Model Ω S) (source : Val rT) (P : S → IProp GF)
    (s : S) (n : ℕ) (G : Ω → ℝ≥0∞) (H : IProp GF) :
    iprop(P s ∗ ↯ (∫⁻ x, G x ∂D.posterior s) ∗ H) ⊢
      tglWp E pl(&Occil.PSRN.integerPowerReal &source.fst #int (n : ℤ))
        (fun v => iprop(ViewOwns (IntegerPower.value source n) P v s ∗
          ↯ (∫⁻ x, G x ∂(IntegerPower.model D n).posterior s) ∗ H)) := by
  iintro ⟨Hstate, Hcredit, Hframe⟩
  iapply tglWp_wand
  isplitl [Hstate Hcredit]
  · iapply IntegerPower.twp_integerPowerReal_credit E D source P s n
    iframe Hstate Hcredit
  iintro %v ⟨Hstate, Hcredit⟩
  iframe Hstate Hcredit Hframe

example (E : CoPset) (D : Model Ω S) (R : Representation D) (P : S → IProp GF)
    (source : Val rT) (hsource : IsRepresentedViewSpec E D R P source) (n : ℕ)
    (s : S) (precision : ℕ) (G : Ω → ℝ≥0∞) (hG : Measurable G) (H : IProp GF) :
    iprop(P s ∗ ↯ (∫⁻ x, G x ∂(IntegerPower.model D n).posterior s) ∗ H) ⊢
      tglWp E pl(&(IntegerPower.value source n).fst #int (precision : ℤ))
        (fun result => iprop(∃ (t : S) (I : RationalInterval),
          ⌜result = intervalVal I ∧ D.refines s t ∧
            (IntegerPower.model D n).Encloses t precision I ∧
            (IntegerPower.representation D R n).Observed t precision I⌝ ∗
          P t ∗ ↯ (∫⁻ x, G x ∂D.posterior t) ∗ H)) := by
  iintro ⟨Hstate, Hcredit, Hframe⟩
  iapply (IntegerPower.oracleSpec E D R P source hsource n).wp s precision G hG _ $$
    Hstate Hcredit
  iintro %t %I %hI Hstate Hcredit
  isimp only [(IntegerPower.sameWorld D n).posterior_eq t] at Hcredit
  iexists t, I
  iframe Hstate Hcredit Hframe
  ipureintro
  exact ⟨rfl, ((IntegerPower.sameWorld D n).refines_iff s t).mp hI.1, hI.2⟩

example (E : CoPset) (D : Model Ω S) (R : Representation D) (P : S → IProp GF)
    (source : Val rT) (hsource : IsRepresentedViewSpec E D R P source) (n : ℕ)
    (s : S) (precision : ℕ) (G : Ω → ℝ≥0∞) (hG : Measurable G) (H : IProp GF) :
    iprop(P s ∗ ↯ (∫⁻ x, G x ∂(IntegerPower.model D n).posterior s) ∗ H) ⊢
      tglWp E (twice (IntegerPower.value source n) precision)
        (fun result => iprop(∃ (u : S) (I J : RationalInterval),
          ⌜result = Val.pair (intervalVal I) (intervalVal J) ∧
            (IntegerPower.model D n).refines s u ∧ I = J⌝ ∗
          P u ∗ ↯ (∫⁻ x, G x ∂(IntegerPower.model D n).posterior u) ∗ H)) := by
  have horacle := IntegerPower.oracleSpec E D R P source hsource n
  iintro ⟨Hstate, Hcredit, Hframe⟩
  unfold twice
  twp_bind pl(&(IntegerPower.value source n).fst #int (precision : ℤ))
  iapply horacle.wp s precision G hG _ $$ Hstate Hcredit
  iintro %t %I %hI Hstate Hcredit
  twp_pure
  twp_bind pl(&(IntegerPower.value source n).fst #int (precision : ℤ))
  iapply horacle.wp t precision G hG _ $$ Hstate Hcredit
  iintro %u %J %hJ Hstate Hcredit
  twp_pure
  ieval (change _ ⊢ tglWp E (Exp.ofVal
    (Val.pair (intervalVal I : Val rT) (intervalVal J))) _)
  iapply tglWp_value
  iexists u, I, J
  iframe Hstate Hcredit Hframe
  ipureintro
  exact ⟨rfl, (IntegerPower.model D n).refines_trans hI.1 hJ.1,
    observed_unique _ _ u precision I J
      ((IntegerPower.representation D R n).observed_refines hJ.1 hI.2.2) hJ.2.2⟩

example (E : CoPset) (source : Val rT) (P : S → IProp GF) (s : S) :
    P s ⊢ tglWp E pl(&Occil.PSRN.integerPowerReal &source.fst #0)
      (fun v => ViewOwns (LatentRational.value 1 1) P v s) := by
  simpa only [IntegerPower.value_zero, Nat.cast_zero] using
    IntegerPower.twp_integerPowerReal E source P s 0

example (E : CoPset) (source : Val rT) (P : S → IProp GF) (s : S) :
    P s ⊢ tglWp E pl(&Occil.PSRN.integerPowerReal &source.fst #1)
      (fun v => ViewOwns source P v s) := by
  simpa only [IntegerPower.value_one, Nat.cast_one] using
    IntegerPower.twp_integerPowerReal E source P s 1

example : (IntegerPower.model (LatentRational.model 0 1) 0).value () = 1 := by
  rw [IntegerPower.value_eq]
  simp

example : (IntegerPower.model (LatentRational.model (-2) 1) 2).value () = 4 := by
  rw [IntegerPower.value_eq]
  norm_num [LatentRational.model]

example : (IntegerPower.model (LatentRational.model (-2) 1) 3).value () = -8 := by
  rw [IntegerPower.value_eq]
  norm_num [LatentRational.model]

example (D : Model Ω S) (hD : D.MeasurableError) (n : ℕ) :
    (IntegerPower.model D n).MeasurableError := IntegerPower.measurableError D hD n

example (E : CoPset) (D : Model Ω S) (source : Val rT) (P : S → IProp GF) (s : S) (n : ℕ) :
    iprop(P s ∗ ↯ (∞ : ℝ≥0∞)) ⊢
      tglWp E pl(&Occil.PSRN.integerPowerReal &source.fst #int (n : ℤ))
        (fun v => iprop(ViewOwns (IntegerPower.value source n) P v s ∗ ↯ (∞ : ℝ≥0∞))) := by
  have h := IntegerPower.twp_integerPowerReal_credit E D source P s n (fun _ => ∞)
  simpa only [MeasureTheory.lintegral_const, MeasureTheory.measure_univ, mul_one] using h

end

end RepresentedIntegerPowerAuthorCallers

#print axioms SampLib.LatentReal.IntegerPower.Program.source_eq
#print axioms SampLib.LatentReal.IntegerPower.value_eq
#print axioms SampLib.LatentReal.IntegerPower.measurableError
#print axioms SampLib.LatentReal.IntegerPower.oracleSpec
#print axioms SampLib.LatentReal.IntegerPower.twp_integerPowerReal
#print axioms SampLib.LatentReal.IntegerPower.twp_integerPowerReal_credit
