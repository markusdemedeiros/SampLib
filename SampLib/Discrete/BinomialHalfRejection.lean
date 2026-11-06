import SampLib.Discrete.Support.BinomialHalfRejectionCore
import SampLib.Discrete.Support.BinomialHalfOpening
import SampLib.Discrete.Laws.BinomialHalfBranches

/-! # Bringmann's half-binomial sampler, including small and odd inputs -/

open ProbLang
open scoped ENNReal NNReal

namespace SampLib.BinomialHalfRejection

noncomputable section

open BinomialHalfEnvelope
open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
attribute [local pl_step_simp]
  BinomialHalfOpening.source_openRec
  BinomialHalfRejectionSyntax.bits_openRec BinomialHalfRejectionSyntax.bits_closeRec
  BinomialHalfRejectionSyntax.sqrt_openRec BinomialHalfRejectionSyntax.sqrt_closeRec
  BinomialHalfRejectionSyntax.geometric_openRec BinomialHalfRejectionSyntax.geometric_closeRec
  BinomialHalfRejectionSyntax.choose_openRec BinomialHalfRejectionSyntax.choose_closeRec
  BinomialHalfRejectionSyntax.power_openRec BinomialHalfRejectionSyntax.power_closeRec
  UniformInt.uniformInt_openRec UniformInt.uniformInt_closeRec
  FairCoin.fairCoin_openRec FairCoin.fairCoin_closeRec
  RationalCoin.rationalCoin_openRec RationalCoin.rationalCoin_closeRec

local bi (IProp GF)

/-- Full natural input domain, including the small and odd recursive branches. -/
theorem twp_binomialHalfRejection (E : CoPset) (n : ℕ) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ k, F k ∂law n) -∗
      tglWp E pl(&Occil.DiscreteExtra.binomialHalfRejection #int (n : ℤ))
        (fun v : Val rT => iprop(∃ (k : ℕ), ⌜v = Val.int k⌝ ∗ ↯ (F k))) := by
  induction n using Nat.strong_induction_on generalizing F with
  | h n IH =>
    iintro Hcredit
    iapply BinomialHalfOpening.twp_open E n
    iterate 3 twp_pure
    by_cases hsmall : n < 4
    · rw [decide_eq_true (by exact_mod_cast hsmall : (n : ℤ) < 4)]
      twp_pure
      iapply (BinomialHalfBits.binomialHalfBits_distSpec E n).spec F
        (measurable_of_countable _) $$ Hcredit
    · rw [decide_eq_false (by exact_mod_cast hsmall : ¬(n : ℤ) < 4)]
      iterate 3 twp_pure
      by_cases hodd : n % 2 = 1
      · rw [show (n : ℤ) % 2 = 1 by exact_mod_cast hodd]
        twp_pure
        twp_bind pl(&Occil.uniformInt #2)
        isimp only [← BinomialHalfBranches.odd_expectation_pred n (by omega) F] at Hcredit
        iapply (UniformInt.uniformInt_distSpec E 2).wp
          (fun bit => ∫⁻ k, F (k + bit) ∂law (n - 1)) (measurable_of_countable _) _ $$ Hcredit
        iintro %bit Hcredit
        twp_pure
        rw [show (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) by omega]
        twp_bind pl(&Occil.DiscreteExtra.binomialHalfRejection #int (n - 1 : ℕ))
        iapply tglWp_wand
        isplitl [Hcredit]
        · iapply IH (n - 1) (by omega) (fun k => F (k + bit)) $$ Hcredit
        iintro %v ⟨%k, %hv, Hcredit⟩
        subst v
        twp_pures
        twp_value
        imodintro
        iexists (k + bit)
        iframe Hcredit
        ipureintro
        apply Val.ext
        simp [Nat.cast_add]
      · have hmod : n % 2 = 0 := by omega
        rw [show (n : ℤ) % 2 = 0 by exact_mod_cast hmod]
        twp_pure
        twp_bind pl(&Occil.DiscreteExtra.integerSqrt #int (n : ℤ))
        iapply tglWp_wand
        isplitl []
        · iapply IntegerSqrt.twp_integerSqrt E n
        iintro %v %hv
        subst v
        iterate 3 twp_pure
        have heven : Even n := Nat.even_iff.mpr hmod
        iapply loop_sqrt_align E n
          (fun v : Val rT => iprop(∃ (k : ℕ), ⌜v = Val.int k⌝ ∗ ↯ (F k)))
        iapply twp_loop E n heven F $$ Hcredit

/-- Bringmann rejection returns the canonical half-binomial law for every natural size. -/
theorem binomialHalfRejection_distSpec (E : CoPset) (n : ℕ) :
    IsDistSpec (GF := GF) E pl(&Occil.DiscreteExtra.binomialHalfRejection #int (n : ℤ))
      (law n) (fun k => Val.int (k : ℤ)) where
  spec F _ := wand_entails (twp_binomialHalfRejection E n F)

end

end SampLib.BinomialHalfRejection
