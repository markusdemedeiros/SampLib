import SampLib.Samplers.ThreePointPiecewise

open ProbLang
open scoped ENNReal

namespace ExactMinimumFactoriesCallers

open SampLib SampLib.MinimumComplement

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (R : IProp GF) :
    iprop(↯ (RealCoin.credit (bias p) F) ∗ R) ⊢
      tglWp E pl(&Occil.FactoryExtra.minimumComplement &coin.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  isimp only [← RealCoin.lintegral_law] at Hcredit
  iapply ((minimumComplement_distSpec E p coin hcoin).wp F
    (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HR
  itrivial

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (R : IProp GF) :
    iprop(↯ (RealCoin.credit (halfBias p) F) ∗ R) ⊢
      tglWp E pl(&Occil.FactoryExtra.minimumHalf &coin.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  isimp only [← RealCoin.lintegral_law] at Hcredit
  iapply ((minimumHalf_distSpec E p coin hcoin).wp F
    (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HR
  itrivial

example (E : CoPset) (p μ ν : unitInterval) (coin mu nu : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (hmu : IsDistSpec (GF := GF) E pl(&mu.fst #()) (RealCoin.law μ) Val.bool)
    (hnu : IsDistSpec (GF := GF) E pl(&nu.fst #()) (RealCoin.law ν) Val.bool)
    (mode : Fin 6) (F : Bool → ℝ≥0∞) (R : IProp GF) :
    iprop(↯ (RealCoin.credit (piecewiseBias p μ ν mode) F) ∗ R) ⊢
      tglWp E pl(&Occil.FactoryExtra.threePointPiecewise &coin.fst &mu.fst &nu.fst
        #int (mode.val : ℤ) #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  isimp only [← RealCoin.lintegral_law] at Hcredit
  iapply ((threePointPiecewise_distSpec E p μ ν coin mu nu hcoin hmu hnu mode).wp F
    (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HR
  itrivial

private def zeroCoin : Val rT := ⟨pl(fun u, #false), .lam (by is_lc), by is_lc⟩

omit [ProbLangDist.IsUniformInt rT] in
private theorem zeroCoin_spec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&zeroCoin.fst #()) (RealCoin.law 0) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    iapply (CoinExpression.false_spec (rT := rT) (GF := GF) E).spec F hF $$ Hcredit

example (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.minimumComplement &zeroCoin.fst #())
      (RealCoin.law 0) Val.bool := by
  have h := minimumComplement_distSpec (GF := GF) E 0 (zeroCoin (rT := rT))
    (zeroCoin_spec (rT := rT) (GF := GF) E)
  have hzero : bias 0 = 0 := by apply Subtype.ext; norm_num [bias]
  simpa only [hzero] using h

example : bias 0 = 0 := by apply Subtype.ext; norm_num [bias]
example : bias 1 = 0 := by apply Subtype.ext; norm_num [bias]
example : bias VonNeumann.fairBias = VonNeumann.fairBias := by
  apply Subtype.ext
  norm_num [bias, VonNeumann.fairBias]
example : halfBias 1 = VonNeumann.fairBias := by
  apply Subtype.ext
  norm_num [halfBias, VonNeumann.fairBias]

example : RealCoin.credit (bias 0) (fun b => if b then ⊤ else 0) = 0 := by
  norm_num [bias, RealCoin.credit, RealCoin.pmf]
example : RealCoin.credit (bias 1) (fun b => if b then ⊤ else 0) = 0 := by
  norm_num [bias, RealCoin.credit, RealCoin.pmf]

#print axioms SampLib.MinimumComplement.minimumComplement_distSpec
#print axioms SampLib.MinimumComplement.minimumHalf_distSpec
#print axioms SampLib.MinimumComplement.threePointPiecewise_distSpec
#print axioms SampLib.MinimumComplement.twp_index
#print axioms SampLib.MinimumComplement.Program.source_eq

end

end ExactMinimumFactoriesCallers
