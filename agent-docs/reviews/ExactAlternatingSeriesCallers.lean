import SampLib.Bernoulli.AlternatingSeries

open ProbLang
open scoped ENNReal

namespace ExactAlternatingSeriesCallers

open SampLib SampLib.AlternatingSeries SampLib.FactoryFractions

noncomputable section

/-- Unreduced coefficients for the finite series `2/3-p/3`. -/
def raw : ℕ → Fraction
  | 0 => ⟨4, 6, by decide⟩
  | 1 => ⟨2, 6, by decide⟩
  | _ + 2 => ⟨0, 2, by decide⟩

def parameters : Parameters where
  coefficient n := (raw n).value
  nonnegative n := by
    rcases n with _ | n
    · norm_num [raw, Fraction.value]
    · rcases n with _ | n <;> norm_num [raw, Fraction.value]
  decreasing := by
    apply antitone_nat_of_succ_le
    intro n
    rcases n with _ | n
    · norm_num [raw, Fraction.value]
    · rcases n with _ | n <;> norm_num [raw, Fraction.value]
  initial := by norm_num [raw, Fraction.value]
  vanishes := by
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    simp [raw, Fraction.value, Nat.add_comm]

def callback {rT : Type} : Val rT :=
  ⟨pl(fun n, if n = #0 then (#4, #6) else if n = #1 then (#2, #6) else (#0, #2)),
    .lam (by is_lc), by is_lc⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
private theorem callback_spec (E : CoPset) (n : ℕ) :
    ⊢ tglWp E pl(&(callback (rT := rT)).fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = (raw n).encode⌝)) := by
  rcases n with _ | n
  · twp_pures
    twp_value
    imodintro
    ipureintro
    rfl
  · rcases n with _ | n
    · twp_pures
      twp_value
      imodintro
      ipureintro
      rfl
    · twp_pures
      twp_value
      imodintro
      ipureintro
      simp [raw, Fraction.encode]

/-- Arbitrary caller resources survive the complete owned-uniform algorithm. -/
example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (R : IProp GF) :
    iprop(↯ (RealCoin.credit (meanBias parameters p) F) ∗ R) ⊢
      tglWp E pl(&Occil.FactoryExtra.alternatingSeries &coin.fst &(callback (rT := rT)).fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  isimp only [← RealCoin.lintegral_law] at Hcredit
  iapply ((alternatingSeries_distSpec E parameters raw (fun _ => rfl) p coin callback
    hcoin (callback_spec E)).wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HR
  itrivial

#print axioms SampLib.AlternatingSeries.alternatingSeries_distSpec
#print axioms SampLib.AlternatingSeries.weighted_partialSum_tendsto
#print axioms SampLib.AlternatingSeries.Program.source_eq

end specification

end

end ExactAlternatingSeriesCallers
