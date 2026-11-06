import SampLib.PSRN.PSRNPowerCoin

/-! Exact-source calls cover the zero exponent, fractional zero bias, and infinite credits. -/

open ProbLang
open scoped ENNReal

namespace SampLib.PSRNPowerCoin.ProducerCallers

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The arbitrary continuation and resource frame use the actual source head. -/
theorem framed (E : CoPset) (p : unitInterval) (a b : ℕ) (hb : 0 < b)
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (R : IProp GF) :
    iprop(↯ (∫⁻ bit, F bit ∂RealCoin.law (RationalPower.bias p a b hb)) ∗ R) ⊢
      tglWp E pl(&Occil.PSRN.powerCoin &coin.fst #int (a : ℤ) #int (b : ℤ) #())
        (fun result : Val rT => iprop(∃ bit : Bool,
          ⌜result = Val.bool bit⌝ ∗ ↯ (F bit) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  iapply (powerCoin_distSpec E p a b hb coin hcoin).wp F (measurable_of_countable _) _ $$ Hcredit
  iintro %bit Hcredit
  iexists bit
  iframe Hcredit HR
  itrivial

private def falseCoin : Val rT := ⟨pl(fun u, #false), .lam (by is_lc), by is_lc⟩

omit [ProbLangDist.IsUniformInt rT] in
private theorem falseCoin_spec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&(falseCoin : Val rT).fst #())
      (RealCoin.law 0) Val.bool where
  spec F _ := by
    iintro Hcredit
    isimp only [RealCoin.lintegral_law] at Hcredit
    isimp [RealCoin.credit, RealCoin.pmf] at Hcredit
    unfold falseCoin
    twp_pures
    twp_value
    imodintro
    iexists false
    iframe Hcredit
    itrivial

/-- Zero input and zero exponent still return the unit bias. -/
example (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.PSRN.powerCoin &(falseCoin : Val rT).fst #0 #7 #())
      (RealCoin.law (RationalPower.bias 0 0 7 (by norm_num))) Val.bool :=
  powerCoin_distSpec E 0 0 7 (by norm_num) falseCoin (falseCoin_spec E)

/-- The fractional zero-input endpoint uses the verified infinite-mean hazard loop. -/
example (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.PSRN.powerCoin &(falseCoin : Val rT).fst #1 #2 #())
      (RealCoin.law (RationalPower.bias 0 1 2 (by norm_num))) Val.bool :=
  powerCoin_distSpec E 0 1 2 (by norm_num) falseCoin (falseCoin_spec E)

example :
    (∫⁻ bit, (if bit then 0 else ∞ : ℝ≥0∞)
      ∂RealCoin.law (RationalPower.bias 0 0 7 (by norm_num))) = 0 := by
  simp [RealCoin.lintegral_law, RationalPower.bias, RealCoin.credit, RealCoin.pmf]

example :
    (∫⁻ bit, (if bit then ∞ else 0 : ℝ≥0∞)
      ∂RealCoin.law (RationalPower.bias 0 1 2 (by norm_num))) = 0 := by
  norm_num [RealCoin.lintegral_law, RationalPower.bias, RealCoin.credit, RealCoin.pmf]

#print axioms framed
#print axioms twp_powerCoin
#print axioms powerCoin_distSpec
#print axioms expectation

end

end SampLib.PSRNPowerCoin.ProducerCallers
