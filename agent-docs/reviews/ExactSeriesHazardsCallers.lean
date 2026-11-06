import SampLib.Samplers.PowerSeriesHazards

open ProbLang
open scoped ENNReal

namespace ExactSeriesHazardsCallers

open SampLib SampLib.PowerSeriesHazards

noncomputable section

/-- The first hazard is zero; every later hazard is one. -/
def a (n : ℕ) : Coefficient := ⟨if n = 0 then 0 else 1, 1, by decide, by split_ifs <;> omega⟩

def hazard {rT : Type _} : Val rT :=
  ⟨pl(fun n, if n = #0 then (#0, #1) else (#1, #1)), .lam (by is_lc), by is_lc⟩

private theorem absorbs (p : unitInterval) :
    Filter.Tendsto (AbsorbingChain.survival (fun n => continuation p (a n).bias) 0)
      Filter.atTop (nhds 0) := by
  have hz (depth : ℕ) :
      AbsorbingChain.survival (fun n => continuation p (a n).bias) 0 (depth + 2) = 0 := by
    rw [show depth + 2 = (depth + 1) + 1 by omega, AbsorbingChain.survival_succ,
      AbsorbingChain.survival_succ]
    simp [continuation, a, Coefficient.bias, RationalCoin.bias]
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop 2] with depth hd
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hd
  simpa [Nat.add_comm] using hz k

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
private theorem hazard_spec (E : CoPset) (n : ℕ) :
    ⊢ tglWp E pl(&(hazard (rT := rT)).fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = (a n).encode⌝)) := by
  cases n with
  | zero =>
    twp_pures
    twp_value
    imodintro
    ipureintro
    simp [a, Coefficient.encode]
  | succ n =>
    twp_pures
    twp_value
    imodintro
    ipureintro
    simp [a, Coefficient.encode]

/-- The public spec preserves a completely unrelated linear caller resource. -/
example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (R : IProp GF) :
    iprop(↯ (∫⁻ b, F b ∂outputLaw p a (absorbs p)) ∗ R) ⊢
      tglWp E pl(&Occil.FactoryExtra.powerSeriesHazards &coin.fst &(hazard (rT := rT)).fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  iapply ((powerSeriesHazards_distSpec E p a coin hazard hcoin (hazard_spec E) (absorbs p)).wp
    F (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HR
  itrivial

#print axioms SampLib.PowerSeriesHazards.powerSeriesHazards_distSpec
#print axioms SampLib.PowerSeriesHazards.success_probability
#print axioms SampLib.PowerSeriesHazards.absorbs_of_coefficient_sum

end specification

end

end ExactSeriesHazardsCallers
