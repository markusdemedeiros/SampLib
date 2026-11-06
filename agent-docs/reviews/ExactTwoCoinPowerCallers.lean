import SampLib.Samplers.TwoCoinPower

open ProbLang Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open scoped ENNReal

namespace SampLib.ExactTwoCoinPowerCallers

noncomputable section

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Both unknown input callbacks remain abstract, with an unrelated caller resource framed. -/
theorem framed (E : CoPset) (p q : unitInterval) (hstop : 0 < (p : ℝ) ∨ 0 < (q : ℝ))
    (base exponent : Val rT)
    (hbase : IsDistSpec (GF := GF) E pl(&base.fst #()) (RealCoin.law p) Val.bool)
    (hexponent : IsDistSpec (GF := GF) E pl(&exponent.fst #()) (RealCoin.law q) Val.bool)
    (F : Bool → ℝ≥0∞) (P : IProp GF) :
    iprop(P ∗ ↯ (∫⁻ bit, F bit ∂RealCoin.law (TwoCoinPower.bias p q))) ⊢
      tglWp E pl(&Occil.FactoryExtra.twoCoinPower &base.fst &exponent.fst #())
        (fun v : Val rT => iprop(∃ bit : Bool, ⌜v = Val.bool bit⌝ ∗ P ∗ ↯ (F bit))) := by
  iintro ⟨HP, Hcredit⟩
  iapply ((TwoCoinPower.twoCoinPower_distSpec E p q hstop base exponent hbase hexponent).wp
    F (measurable_of_countable _) _) $$ Hcredit
  iintro %bit Hcredit
  iexists bit
  iframe HP Hcredit
  itrivial

/-- Zero base bias is admitted for every positive unknown exponent bias. -/
example (E : CoPset) (q : unitInterval) (hq : 0 < (q : ℝ)) (base exponent : Val rT)
    (hbase : IsDistSpec (GF := GF) E pl(&base.fst #()) (RealCoin.law 0) Val.bool)
    (hexponent : IsDistSpec (GF := GF) E pl(&exponent.fst #()) (RealCoin.law q) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.twoCoinPower &base.fst &exponent.fst #())
      (RealCoin.law (TwoCoinPower.bias 0 q)) Val.bool :=
  TwoCoinPower.twoCoinPower_distSpec E 0 q (Or.inr hq) base exponent hbase hexponent

/-- Zero exponent bias is admitted for every positive unknown base bias. -/
example (E : CoPset) (p : unitInterval) (hp : 0 < (p : ℝ)) (base exponent : Val rT)
    (hbase : IsDistSpec (GF := GF) E pl(&base.fst #()) (RealCoin.law p) Val.bool)
    (hexponent : IsDistSpec (GF := GF) E pl(&exponent.fst #()) (RealCoin.law 0) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.twoCoinPower &base.fst &exponent.fst #())
      (RealCoin.law (TwoCoinPower.bias p 0)) Val.bool :=
  TwoCoinPower.twoCoinPower_distSpec E p 0 (Or.inl hp) base exponent hbase hexponent

#print axioms TwoCoinPower.twoCoinPower_distSpec
#print axioms framed

end

end SampLib.ExactTwoCoinPowerCallers
