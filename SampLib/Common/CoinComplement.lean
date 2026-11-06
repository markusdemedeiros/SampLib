import SampLib.Bernoulli.Complement

/-! # Negating a supplied coin callback -/

open ProbLang
open scoped ENNReal

namespace SampLib.CoinComplement

noncomputable section

/-- A callback that negates one fresh call to the supplied coin. -/
def callback {rT : Type _} (coin : Val rT) : Val rT :=
  ⟨.lam pl(~(&coin.fst #())), .lam (by is_lc), by is_lc⟩

private theorem bool_not (b : Bool) : Bool.rec true false b = !b := by
  cases b <;> rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Negation preserves a fresh callback's conditional Bernoulli specification. -/
theorem distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&(callback coin).fst #())
      (RealCoin.law (unitInterval.symm p)) Val.bool where
  spec F _ := by
    iintro Hcredit
    twp_pure
    twp_bind pl(&coin.fst #())
    isimp only [← Complement.expectation_preservation p F] at Hcredit
    iapply (hcoin.wp (fun b => F (!b)) (measurable_of_countable _) _) $$ Hcredit
    iintro %b Hcredit
    twp_pures
    twp_value
    imodintro
    iexists !b
    iframe Hcredit
    ipureintro
    simp only [Val.ext_iff, bool_not]

end specification

end

end SampLib.CoinComplement
