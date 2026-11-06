import SampLib.Samplers.RationalPower

open ProbLang Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open scoped ENNReal

namespace SampLib.ExactRationalPowerCallers

noncomputable section

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem framed_factory (E : CoPset) (p : unitInterval) (a b : ℕ) (hb : 0 < b)
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (P : IProp GF) :
    iprop(P ∗ ↯ (∫⁻ bit, F bit ∂RealCoin.law (RationalPower.bias p a b hb))) ⊢
      tglWp E pl(&Occil.FactoryExtra.rationalPower &coin.fst #int (a : ℤ) #int (b : ℤ) #())
        (fun v : Val rT => iprop(∃ bit : Bool, ⌜v = Val.bool bit⌝ ∗ P ∗ ↯ (F bit))) := by
  iintro ⟨HP, Hcredit⟩
  iapply ((RationalPower.rationalPower_distSpec E p a b hb coin hcoin).wp
    F (measurable_of_countable _) _) $$ Hcredit
  iintro %bit Hcredit
  iexists bit
  iframe HP Hcredit
  itrivial

theorem framed_discrete (E : CoPset) (p : unitInterval) (a b : ℕ) (hb : 0 < b)
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (P : IProp GF) :
    iprop(P ∗ ↯ (∫⁻ bit, F bit ∂RealCoin.law (RationalPower.bias p a b hb))) ⊢
      tglWp E pl(&Occil.DiscreteExtra.rationalPowerCoin &coin.fst #int (a : ℤ) #int (b : ℤ) #())
        (fun v : Val rT => iprop(∃ bit : Bool, ⌜v = Val.bool bit⌝ ∗ P ∗ ↯ (F bit))) := by
  iintro ⟨HP, Hcredit⟩
  iapply ((RationalPower.rationalPowerCoin_distSpec E p a b hb coin hcoin).wp
    F (measurable_of_countable _) _) $$ Hcredit
  iintro %bit Hcredit
  iexists bit
  iframe HP Hcredit
  itrivial

/-- A zero exponent is the sure-success law, even when the input bias is zero. -/
example (E : CoPset) (p : unitInterval) (b : ℕ) (hb : 0 < b) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.rationalPower &coin.fst #0 #int (b : ℤ) #())
      (RealCoin.law 1) Val.bool := by
  have h := RationalPower.rationalPower_distSpec E p 0 b hb coin hcoin
  have hbias : RationalPower.bias p 0 b hb = 1 := by
    apply Subtype.ext
    simp [RationalPower.bias]
  simpa only [hbias, Nat.cast_zero] using h

/-- A nontrivial fractional remainder is covered at zero input bias. -/
example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 0) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.DiscreteExtra.rationalPowerCoin &coin.fst #7 #3 #())
      (RealCoin.law (RationalPower.bias 0 7 3 (by decide))) Val.bool :=
  RationalPower.rationalPowerCoin_distSpec E 0 7 3 (by decide) coin hcoin

#print axioms RationalPower.rationalPower_distSpec
#print axioms RationalPower.rationalPowerCoin_distSpec
#print axioms framed_factory
#print axioms framed_discrete

end

end SampLib.ExactRationalPowerCallers
