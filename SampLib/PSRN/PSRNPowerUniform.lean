import SampLib.PSRN.Support.Uniform.PowerOracle

/-! # Rational powers of one shared deferred uniform

`newPowerUniform a b` allocates one uniform `u` and returns a lazy oracle for
`u ^ (a / b)`, for every integer `a` and positive `b`. The actual source builds
`u ^ |a|` by repeated squaring, takes a bisection root unless `b = 1`, and takes a
reciprocal when `a < 0`. A zero exponent returns the constant unit oracle.

The uniform is positive almost surely under every posterior. This gives the root's
comparison domain and the reciprocal's nonzero denominator after all later reads.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.PSRNPowerUniform

noncomputable section

open LatentReal

namespace Program

private instance uniform_closed {rT : Type} : ClosedExp (Occil.PSRN.newUniform : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

private instance powerRational_closed {rT : Type} :
    ClosedExp (Occil.PSRN.powerRational : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

private instance rational_closed {rT : Type} : ClosedExp (Occil.PSRN.rational : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

private instance root_closed {rT : Type} : ClosedExp (Occil.PSRN.root : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

private instance reciprocal_closed {rT : Type} : ClosedExp (Occil.PSRN.reciprocal : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

private instance power_closed {rT : Type} : ClosedExp (Occil.PSRN.integerPowerReal : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

end Program

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem newPowerUniform_representedDistSpec (E : CoPset) (a : ℤ) (b : ℕ) (hb : 0 < b) :
    IsRepresentedDistSpec (GF := GF) E pl(&Occil.PSRN.newPowerUniform #a #int (b : ℤ) #())
      (model a b) (representation a b) [] (owns a b) where
  oracle := representedOracleSpec E a b hb
  spec F hF := by
    iintro Hcredit
    iterate 3 twp_pure
    simp only [ClosedExp.openRec, ClosedExp.closeRec]
    twp_pure
    rw [decide_eq_false (by omega)]
    twp_pure
    twp_bind pl(&Occil.PSRN.newUniform #())
    isimp only [(sameWorld a b).posterior_eq] at Hcredit
    iapply ((LatentUniform.newUniform_representedDistSpec E).toIsLatentPayloadSpec.wp F hF _)
      $$ Hcredit
    iintro %source %p %hp Hstate Hcredit
    twp_pure
    simp only [ClosedExp.openRec]
    iterate 3 twp_pure
    simp only [ClosedExp.openRec, ClosedExp.closeRec]
    twp_pure
    rw [decide_eq_false (by omega)]
    twp_pure
    twp_pure
    rw [Program.int_beq]
    rcases lt_trichotomy a 0 with ha | rfl | ha
    · -- Negative exponent: the reciprocal of the positive branch.
      obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat ha.le
      have hn : 0 < n := by omega
      rw [beq_eq_false_iff_ne.mpr ha.ne]
      twp_pure
      twp_pure
      rw [decide_eq_true ha]
      twp_pure
      twp_pure
      rw [neg_neg]
      twp_bind pl(&Occil.PSRN.root (&Occil.PSRN.integerPowerReal &source.fst #int (n : ℤ))
        #int (b : ℤ))
      iapply tglWp_wand
      isplitl [Hstate]
      · iapply twp_rooted E n b hn hb source p $$ Hstate
      iintro %root Hstate
      simp only [Exp.ofVal]
      iapply tglWp_wand
      isplitl [Hstate Hcredit]
      · iapply RepresentedReciprocal.twp_reciprocal E (rooted n b).1 (rooted n b).2
          (rootedOwns n b) root p (rooted_nonzero n b hb p) F
        isimp only [(rooted_sameWorld n b).posterior_eq]
        iframe Hstate Hcredit
      iintro %v ⟨Hstate, Hcredit⟩
      iexists p
      rw [owns_neg b ha, Int.natAbs_neg, Int.natAbs_natCast]
      isimp only [(sameWorld _ b).posterior_eq]
      isimp only [(RepresentedReciprocal.sameWorld (rooted n b).1 (rooted n b).2).posterior_eq,
        (rooted_sameWorld n b).posterior_eq] at Hcredit
      iframe Hstate Hcredit
      ipureintro
      exact ((sameWorld _ b).refines_iff _ _).mpr hp
    · -- Zero exponent: the constant unit oracle; the allocated cache is not needed.
      rw [show ((0 : ℤ) == 0) = true from rfl]
      twp_pure
      twp_pures
      ieval (change _ ⊢ tglWp E (Exp.ofVal (LatentRational.value 1 1)) _)
      iapply tglWp_value
      iexists p
      rw [owns_zero b]
      isimp only [(sameWorld 0 b).posterior_eq, ViewOwns]
      iframe Hcredit
      iclear Hstate
      ipureintro
      exact ⟨((sameWorld 0 b).refines_iff _ _).mpr hp, trivial, trivial⟩
    · -- Positive exponent.
      obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ha.le
      have hn : 0 < n := by omega
      rw [beq_eq_false_iff_ne.mpr ha.ne']
      twp_pure
      twp_pure
      twp_pure
      iapply tglWp_wand
      isplitl [Hstate]
      · iapply twp_rooted E n b hn hb source p $$ Hstate
      iintro %v Hstate
      iexists p
      rw [owns_pos b ha, Int.natAbs_natCast]
      isimp only [(sameWorld _ b).posterior_eq]
      iframe Hstate Hcredit
      ipureintro
      exact ((sameWorld _ b).refines_iff _ _).mpr hp

/-- Standard latent-law interface, including arbitrary future shared observations. -/
theorem newPowerUniform_latentDistSpec (E : CoPset) (a : ℤ) (b : ℕ) (hb : 0 < b) :
    IsLatentDistSpec (GF := GF) E pl(&Occil.PSRN.newPowerUniform #a #int (b : ℤ) #())
      (model a b) [] (owns a b) :=
  (newPowerUniform_representedDistSpec E a b hb).forget

end specification

end

end SampLib.PSRNPowerUniform
