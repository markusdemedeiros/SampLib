import SampLib.Bernoulli.VonNeumann
import Samplers.Uniform
import Metrology.Iris.LocalBI

/-! # A fair coin from a uniform integer bit -/

open Set ProbLang Finset
open scoped ENNReal

namespace SampLib.FairCoin

noncomputable section

/-- The primitive bit's arithmetic mean equals the fair Bernoulli expectation. -/
theorem expectation (F : Bool → ℝ≥0∞) :
    (∑ n ∈ range 2, F (decide (n = 1))) / 2 =
      ∫⁻ b, F b ∂RealCoin.law VonNeumann.fairBias := by
  rw [RealCoin.lintegral_law]
  norm_num [RealCoin.credit, RealCoin.pmf, VonNeumann.fairBias, sum_range_succ,
    ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.div_eq_inv_mul,
    mul_add, add_comm]

/-- Closedness rewrites keep the named primitive visible under sampler binders. -/
theorem fairCoin_lc {rT : Type _} : (Occil.fairCoin : Exp rT).IsLocallyClosed := by is_lc

theorem fairCoin_fv {rT : Type _} : (Occil.fairCoin : Exp rT).fv = ∅ := by
  simp [Occil.fairCoin, Exp.fv]

@[simp] theorem fairCoin_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.fairCoin = Occil.fairCoin :=
  (Exp.open_lc k e _ fairCoin_lc).symm

@[simp] theorem fairCoin_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.fairCoin : Exp rT) = Occil.fairCoin :=
  Exp.closeRec_fresh x _ k (by simp [fairCoin_fv])

private theorem toNat_eq_one (k : ℤ) : k.toNat = 1 ↔ k = 1 := by omega

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- CTE specification for the uniform integer bit. -/
theorem twp_fairCoin (E : CoPset) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law VonNeumann.fairBias) -∗
      tglWp E pl(&Occil.fairCoin #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  twp_pures
  twp_bind pl(rand(#2, #()))
  iapply (twp_rand_exp (ε₂ := fun n => F (decide (n = 1))) (by norm_num) ?_) $$ Hcredit
  · simpa using (expectation F).le
  iintro %k ⟨%hk, Hcredit⟩
  twp_pures
  twp_value
  imodintro
  iexists (decide (k = 1))
  isimp only [toNat_eq_one] at Hcredit
  iframe Hcredit
  ipureintro
  apply Val.ext
  simp [beq_eq_decide]

/-- Typed fair Bernoulli specification. -/
theorem fairCoin_distSpec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.fairCoin #())
      (RealCoin.law VonNeumann.fairBias) Val.bool where
  spec F _ := wand_entails (twp_fairCoin E F)

end specification

end

end SampLib.FairCoin
