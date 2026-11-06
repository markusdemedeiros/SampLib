import SampLib.Samplers.ReciprocalAffine
import SampLib.Samplers.CoinConditional
import SampLib.Samplers.RationalCoin
import SampLib.Samplers.IterateCoin
import SampLib.FactorySyntax

/-! # The inverse quadratic Bernoulli factory -/

open Set ProbLang
open scoped ENNReal

namespace SampLib.InverseQuadratic

noncomputable section

/-- The reciprocal quadratic probability. -/
def bias (p : unitInterval) (m : ℕ) : unitInterval :=
  ⟨1 / (1 + ((m : ℝ) + p) ^ 2), by positivity,
    (div_le_one (by positivity : (0 : ℝ) < 1 + ((m : ℝ) + p) ^ 2)).mpr
      (le_add_of_nonneg_right (sq_nonneg _))⟩

private abbrev selectorBias (m : ℕ) : unitInterval :=
  RationalCoin.bias ((2 * m : ℕ) : ℤ) ((2 * m + 1 : ℕ) : ℤ)
    (by omega) (by omega) (by omega)

private abbrev mixedBias (p : unitInterval) (m : ℕ) : unitInterval :=
  CoinConditional.bias p (IterateCoin.bias p 2) (selectorBias m)

private theorem mixedBias_coe (p : unitInterval) (m : ℕ) :
    (mixedBias p m : ℝ) = (2 * m * (p : ℝ) + (p : ℝ) ^ 2) / (2 * m + 1) := by
  simp only [mixedBias, CoinConditional.bias, Set.Icc.coe_convexComb,
    IterateCoin.bias, selectorBias, RationalCoin.bias, Int.cast_add, Int.cast_mul,
    Int.cast_ofNat, Int.cast_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  field_simp
  ring

/-- The rational mixture turns `c+p` into the polynomial `1+(m+p)^2`. -/
theorem reciprocal_bias (p : unitInterval) (m : ℕ) :
    ReciprocalAffine.bias (mixedBias p m) ((m * m + 1) * (2 * m + 1))
      (1 * (2 * m + 1)) ((2 * m + 1) * (2 * m + 1))
      (by positivity) (Nat.mul_le_mul_right _ (by omega)) = bias p m := by
  apply Subtype.ext
  have hden :
      (((m * m + 1) * (2 * m + 1) : ℕ) : ℝ) +
        (((2 * m + 1) * (2 * m + 1) : ℕ) : ℝ) * (mixedBias p m : ℝ) =
      (2 * (m : ℝ) + 1) * (1 + ((m : ℝ) + p) ^ 2) := by
    rw [mixedBias_coe]
    push_cast
    field_simp
    ring
  change ((1 * (2 * m + 1) : ℕ) : ℝ) / _ = 1 / (1 + ((m : ℝ) + p) ^ 2)
  rw [hden]
  push_cast
  field_simp

private theorem valid_parameters (m : ℕ) :
    0 < m * m + 1 ∧ 0 < 2 * m + 1 ∧
      1 * (2 * m + 1) ≤ (m * m + 1) * (2 * m + 1) :=
  ⟨Nat.succ_pos _, Nat.succ_pos _, Nat.mul_le_mul_right _ (by omega)⟩

private def mixed {rT : Type _} (coin : Val rT) (m : ℕ) : Val rT :=
  ⟨.lam pl(if &Occil.rationalCoin (#2 * #int (m : ℤ))
      (#2 * #int (m : ℤ) + #1) then &coin.fst #()
      else &Occil.iterateCoin &coin.fst #2), .lam (by is_lc), by is_lc⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem mixed_distSpec (E : CoPset) (p : unitInterval) (m : ℕ) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&(mixed coin m).fst #()) (RealCoin.law (mixedBias p m))
      Val.bool where
  spec F _ := by
    have hselect := RationalCoin.rationalCoin_distSpec (rT := rT) (GF := GF)
      E ((2 * m : ℕ) : ℤ) ((2 * m + 1 : ℕ) : ℤ) (Int.natCast_nonneg _)
        (Int.natCast_pos.mpr (Nat.succ_pos _)) (Int.ofNat_le.mpr (Nat.le_succ _))
    iintro Hcredit
    iterate 4 (twp_step; simp -failIfUnchanged [Exp.open', Exp.openRec, Exp.ofVal,
      ProbLang.openRec_val_fst, RationalCoin.rationalCoin_openRec,
      FactorySyntax.iterateCoin_openRec])
    twp_bind pl(&Occil.rationalCoin #int ((2 * m : ℕ) : ℤ)
      #int ((2 * m + 1 : ℕ) : ℤ))
    isimp only [← CoinConditional.expectation_preservation p (IterateCoin.bias p 2)
      (selectorBias m) F] at Hcredit
    iapply (hselect.wp
      (CoinConditional.firstCredit p (IterateCoin.bias p 2) F) (measurable_of_countable _) _)
      $$ Hcredit
    iintro %b Hcredit
    cases b
    · twp_pure
      isimp only [CoinConditional.firstCredit, Bool.false_eq_true, ite_false] at Hcredit
      iapply (IterateCoin.iterateCoin_distSpec E p coin hcoin 2).spec F
        (measurable_of_countable _) $$ Hcredit
    · twp_pure
      isimp only [CoinConditional.firstCredit, ite_true] at Hcredit
      iapply hcoin.spec F (measurable_of_countable _) $$ Hcredit

/-- The quadratic factory is total for every nonnegative integer shift and input bias. -/
theorem twp_inverseQuadratic (E : CoPset) (p : unitInterval) (m : ℕ) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law (bias p m)) -∗
      tglWp E pl(&Occil.FactoryExtra.inverseQuadratic &coin.fst #int (m : ℤ) #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  obtain ⟨ha, hb, hd⟩ := valid_parameters m
  have hrec := ReciprocalAffine.reciprocalAffine_distSpec (rT := rT) (GF := GF)
    E (mixedBias p m) (m * m + 1) (2 * m + 1) 1 (2 * m + 1) ha hb hb hd
      (mixed coin m) (mixed_distSpec E p m coin hcoin)
  simp only [reciprocal_bias] at hrec
  iintro Hcredit
  iterate 12 (twp_step; simp -failIfUnchanged [Exp.open', Exp.openRec, Exp.close,
    Exp.closeRec, Exp.ofVal, Var.internal.injEq, ProbLang.openRec_val_fst,
    ReciprocalAffine.reciprocalAffine_openRec, ReciprocalAffine.reciprocalAffine_closeRec,
    RationalCoin.rationalCoin_openRec, RationalCoin.rationalCoin_closeRec,
    FactorySyntax.iterateCoin_openRec, FactorySyntax.iterateCoin_closeRec])
  simp only [← Int.natCast_mul]
  twp_bind pl(&Occil.FactoryExtra.reciprocalAffine &(mixed coin m).fst
    #int ((m * m + 1 : ℕ) : ℤ) #int ((2 * m + 1 : ℕ) : ℤ)
    #1 #int ((2 * m + 1 : ℕ) : ℤ) #())
  iapply (tglWp_mono fun _ => tglWp_value)
  iapply hrec.spec F (measurable_of_countable _) $$ Hcredit

/-- Typed Bernoulli law with bias `1/(1+(m+p)^2)`. -/
theorem inverseQuadratic_distSpec (E : CoPset) (p : unitInterval) (m : ℕ) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.inverseQuadratic &coin.fst #int (m : ℤ) #())
      (RealCoin.law (bias p m)) Val.bool where
  spec F _ := wand_entails (twp_inverseQuadratic E p m coin hcoin F)

end specification

end

end SampLib.InverseQuadratic
