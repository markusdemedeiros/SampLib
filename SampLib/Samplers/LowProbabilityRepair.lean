import SampLib.Distributions.LowProbabilityRepair
import SampLib.Syntax.LowProbabilityRepair

/-! # CTE verification of the proposed low-probability margin repair

Both selectors compose with the verified linear factory on its complete
admissible domain. `LinearLowProbability` transports this proof to the canonical term.
-/

open ProbLang
open scoped ENNReal SampLib.LowProbabilityRepair.Syntax

namespace SampLib.LowProbabilityRepair

noncomputable section

private def source {rT : Type _} : Val rT :=
  ⟨algorithm, .lam (by is_lc), by is_lc⟩

private theorem source_fst {rT : Type _} : (source (rT := rT)).fst = algorithm := rfl

private theorem int_beq {rT : Type _} [BEq rT] (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = (a == b) := rfl

private theorem valid_test {p : unitInterval} (σ : Parameters p) :
    Bool.or (Bool.or (Bool.or (decide (σ.a < 0)) (decide (σ.b ≤ 0)))
      (decide (σ.m < 0))) (decide (σ.n ≤ 2 * σ.m)) = false := by
  obtain ⟨ha, hb, hm, hmn, _⟩ := σ.admissible
  simp [not_lt.mpr ha, not_le.mpr hb, not_lt.mpr hm, not_le.mpr hmn]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

private theorem twp_open (E : CoPset) (p : unitInterval) (σ : Parameters p)
    (coin : Val rT) (Φ : Val rT → IProp GF) :
    tglWp E (Syntax.body coin σ.a σ.b σ.m σ.n) Φ ⊢
      tglWp E pl(&algorithm &coin.fst #int σ.a #int σ.b #int σ.m #int σ.n #()) Φ := by
  iintro Hbody
  rw [← source_fst (rT := rT)]
  iterate 6 twp_pure
  isimp only [Syntax.body, ClosedExp.openRec, ClosedExp.closeRec, Exp.ofVal] at Hbody
  iexact Hbody

variable [ProbLangDist.IsUniformInt rT]

private theorem logistic_spec (E : CoPset) (p : unitInterval) (σ : Parameters p)
    (ha : σ.b < σ.a) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.logisticFactory &coin.fst #int (σ.a * σ.n)
        #int (σ.b * (σ.n - 2 * σ.m)) #())
      (RealCoin.law (σ.logisticBias ha)) Val.bool :=
  LogisticFactory.logisticFactory_distSpec E p (σ.a * σ.n) (σ.b * (σ.n - 2 * σ.m))
    (mul_pos (σ.admissible.2.1.trans ha) σ.n_pos)
    (mul_pos σ.admissible.2.1 σ.betaDen_pos) coin hcoin

private theorem selector_spec (E : CoPset) (p : unitInterval) (σ : Parameters p) :
    IsDistSpec (GF := GF) E
      pl(&Occil.rationalCoin #int (σ.n - 2 * σ.m) #int σ.n)
      (RealCoin.law σ.selectorBias) Val.bool :=
  RationalCoin.rationalCoin_distSpec E (σ.n - 2 * σ.m) σ.n
    σ.betaDen_pos.le σ.n_pos σ.betaDen_le

private theorem inner_spec (E : CoPset) (p : unitInterval) (σ : Parameters p)
    (hm : 0 < σ.m) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.linear &coin.fst #int (σ.a * σ.n)
        #int (σ.b * 2 * σ.m) #1 #2 #())
      (RealCoin.law (σ.innerBias hm)) Val.bool :=
  LinearFactory.linear_distSpec E p (σ.a * σ.n) (σ.b * 2 * σ.m) 1 2
    (LowProbabilityMargin.repaired_inner_admissible _ _ _ _ _ σ.admissible hm) coin hcoin

theorem twp_lowProbabilityRepair (E : CoPset) (p : unitInterval) (σ : Parameters p)
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ z, F z ∂RealCoin.law σ.bias) -∗
      tglWp E pl(&algorithm &coin.fst #int σ.a #int σ.b #int σ.m #int σ.n #())
        (fun v : Val rT => iprop(∃ z : Bool, ⌜v = Val.bool z⌝ ∗ ↯ (F z))) := by
  iintro Hcredit
  iapply twp_open E p σ coin
  unfold Syntax.body
  twp_pures
  rw [valid_test σ]
  twp_pure
  twp_pure
  by_cases hab : σ.a ≤ σ.b
  · rw [decide_eq_true hab]
    twp_pure
    twp_bind pl(&Occil.rationalCoin #int σ.a #int σ.b)
    isimp only [← σ.contracting_expectation hab F] at Hcredit
    iapply ((RationalCoin.rationalCoin_distSpec E σ.a σ.b σ.admissible.1
      σ.admissible.2.1 hab).wp (LinearFactory.contractingCredit p F)
        (measurable_of_countable _) _) $$ Hcredit
    iintro %z Hcredit
    cases z
    · twp_pure
      twp_value
      imodintro
      iexists false
      isimp only [LinearFactory.contractingCredit, Bool.false_eq_true, ite_false] at Hcredit
      iframe Hcredit
      itrivial
    · twp_pure
      isimp only [LinearFactory.contractingCredit, ite_true] at Hcredit
      iapply hcoin.spec F (measurable_of_countable _) $$ Hcredit
  · have hba : σ.b < σ.a := lt_of_not_ge hab
    rw [decide_eq_false hab]
    twp_pure
    twp_pure
    rw [int_beq]
    by_cases hm : σ.m = 0
    · simp only [hm, beq_self_eq_true]
      twp_pure
      twp_value
      imodintro
      iexists false
      isimp only [σ.zero_expectation hm F] at Hcredit
      iframe Hcredit
      itrivial
    · have hmpos := σ.m_pos hm
      rw [beq_eq_false_iff_ne.mpr hm]
      twp_pure
      twp_pure
      iterate 4 twp_pure
      twp_bind pl(&Occil.logisticFactory &coin.fst #int (σ.a * σ.n)
        #int (σ.b * (σ.n - 2 * σ.m)) #())
      isimp only [← expectation σ hba hmpos F] at Hcredit
      iapply ((logistic_spec E p σ hba coin hcoin).wp (firstCredit σ hmpos F)
        (measurable_of_countable _) _) $$ Hcredit
      iintro %z Hcredit
      cases z
      · twp_pure
        twp_value
        imodintro
        iexists false
        isimp only [firstCredit, Bool.false_eq_true, ite_false] at Hcredit
        iframe Hcredit
        itrivial
      · twp_pure
        twp_bind pl(&Occil.rationalCoin #int (σ.n - 2 * σ.m) #int σ.n)
        isimp only [firstCredit, ite_true] at Hcredit
        iapply ((selector_spec E p σ).wp (selectorCredit σ hmpos F)
          (measurable_of_countable _) _) $$ Hcredit
        iintro %z Hcredit
        cases z
        · twp_pure
          isimp only [selectorCredit, Bool.false_eq_true, ite_false] at Hcredit
          iterate 3 twp_pure
          simp only [Exp.ofVal]
          iapply (inner_spec E p σ hmpos coin hcoin).spec F (measurable_of_countable _) $$ Hcredit
        · twp_pure
          twp_value
          imodintro
          iexists true
          isimp only [selectorCredit, ite_true] at Hcredit
          iframe Hcredit
          itrivial

/-- Full advertised domain of the corrected wrapper, including zero and contracting cases. -/
theorem lowProbabilityRepair_distSpec (E : CoPset) (p : unitInterval) (σ : Parameters p)
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&algorithm &coin.fst #int σ.a #int σ.b #int σ.m #int σ.n #())
      (RealCoin.law σ.bias) Val.bool where
  spec F _ := wand_entails (twp_lowProbabilityRepair E p σ coin hcoin F)

end specification

end

end SampLib.LowProbabilityRepair
