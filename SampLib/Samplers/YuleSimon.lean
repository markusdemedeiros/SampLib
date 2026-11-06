import SampLib.Samplers.BetaNegativeBinomial
import SampLib.BetaNegativeBinomialSyntax

/-! # Positive Yule–Simon variates with rational shape -/

open ProbLang
open scoped ENNReal

namespace SampLib.YuleSimon

noncomputable section

open MeasureTheory (Measure IsProbabilityMeasure lintegral_map)

private def parameters (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    BetaNegativeBinomial.Parameters := ⟨a, b, 1, 1, ha, hb, by decide, by decide⟩

/-- One plus a beta-geometric count with shapes `a/b` and one. -/
def law (a b : ℕ) (ha : 0 < a) (hb : 0 < b) : Measure ℕ :=
  (BetaNegativeBinomial.law (parameters a b ha hb) 1).map Nat.succ

instance (a b : ℕ) (ha : 0 < a) (hb : 0 < b) : IsProbabilityMeasure (law a b ha hb) := by
  dsimp [law]
  infer_instance

/-- The canonical rising-product mass, at positive integer `n+1`. -/
theorem mass (a b n : ℕ) (ha : 0 < a) (hb : 0 < b) :
    law a b ha hb {n + 1} = InverseUrn.positiveMass 0 a b b n := by
  rw [law, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have hpre : Nat.succ ⁻¹' ({n + 1} : Set ℕ) = {n} := by ext; simp
  rw [hpre]
  simpa only [parameters, BetaNegativeBinomial.marked, BetaNegativeBinomial.unmarked,
    BetaNegativeBinomial.reinforcement, Nat.mul_one, Nat.one_mul] using
    BetaNegativeBinomial.mass (parameters a b ha hb) 0 n

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem yuleSimon_distSpec (E : CoPset) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    IsDistSpec (GF := GF) E
      pl(&Occil.DiscreteExtra.yuleSimon #int (a : ℤ) #int (b : ℤ))
      (law a b ha hb) (fun k : ℕ => Val.int (k : ℤ)) where
  spec F hF := by
    iintro Hcredit
    isimp only [law, lintegral_map hF (measurable_of_countable _), Nat.succ_eq_add_one]
      at Hcredit
    iterate 2 twp_pure
    simp only [BetaNegativeBinomial.betaNegativeBinomial_openRec,
      BetaNegativeBinomial.betaNegativeBinomial_closeRec]
    twp_bind pl(&Occil.DiscreteExtra.betaNegativeBinomial #1 #int (a : ℤ) #int (b : ℤ) #1 #1)
    have h := BetaNegativeBinomial.betaNegativeBinomial_distSpec (rT := rT) (GF := GF)
      E (parameters a b ha hb) 1
    simp only [parameters, Nat.cast_one] at h
    isimp only [parameters] at Hcredit
    iapply (h.wp (fun k => F (k + 1)) (measurable_of_countable _) _) $$ Hcredit
    iintro %k Hcredit
    twp_pures
    twp_value
    imodintro
    iexists (k + 1)
    iframe Hcredit
    ipureintro
    apply Val.ext
    simp [add_comm]

end specification

end

end SampLib.YuleSimon
