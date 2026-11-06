import SampLib.Bernoulli.Complement
import SampLib.Bernoulli.CoinProduct
import SampLib.Bernoulli.CoinDisjunction
import SampLib.Bernoulli.CoinConditional
import SampLib.Bernoulli.EvenParity
import SampLib.Bernoulli.CoinMean
import SampLib.Bernoulli.OnePlusHalf
import SampLib.Bernoulli.ComplementHalf
import SampLib.Bernoulli.OneDivOnePlus
import SampLib.Bernoulli.OneMinusOverOnePlus
import SampLib.Bernoulli.BernoulliRace
import SampLib.Continuous.GeometricFailures
import Metrology.Iris.LocalBI

open Set ProbLang
open scoped ENNReal

namespace ReviewCoins
noncomputable section

-- Boundary laws are genuine deterministic/selector endpoints, without limiting credits.
example (q : unitInterval) : SampLib.CoinProduct.law 0 q = SampLib.RealCoin.law 0 := by
  simp [SampLib.CoinProduct.law]
example (q : unitInterval) : SampLib.CoinProduct.law 1 q = SampLib.RealCoin.law q := by
  simp [SampLib.CoinProduct.law]
example (q : unitInterval) : SampLib.CoinDisjunction.law 0 q = SampLib.RealCoin.law q := by
  simp [SampLib.CoinDisjunction.law, SampLib.CoinDisjunction.bias]
example (q : unitInterval) : SampLib.CoinDisjunction.law 1 q = SampLib.RealCoin.law 1 := by
  simp [SampLib.CoinDisjunction.law, SampLib.CoinDisjunction.bias]
example (p q : unitInterval) :
    SampLib.CoinConditional.law p q 0 = SampLib.RealCoin.law q := by
  simp [SampLib.CoinConditional.law, SampLib.CoinConditional.bias]
example (p q : unitInterval) :
    SampLib.CoinConditional.law p q 1 = SampLib.RealCoin.law p := by
  simp [SampLib.CoinConditional.law, SampLib.CoinConditional.bias]
example : SampLib.Complement.law 0 = SampLib.RealCoin.law 1 := by
  simp [SampLib.Complement.law]
example : SampLib.Complement.law 1 = SampLib.RealCoin.law 0 := by
  simp [SampLib.Complement.law]
example : SampLib.EvenParity.law 0 = SampLib.RealCoin.law 1 := by
  change SampLib.RealCoin.law (SampLib.EvenParity.bias 0) = SampLib.RealCoin.law 1
  apply congrArg SampLib.RealCoin.law
  apply Subtype.ext
  norm_num [SampLib.EvenParity.bias]

example : (∫⁻ b, (if b then ∞ else 0 : ℝ≥0∞) ∂SampLib.CoinProduct.law 0 1) = 0 := by
  simp [SampLib.CoinProduct.law, SampLib.RealCoin.lintegral_law,
    SampLib.RealCoin.credit, SampLib.RealCoin.pmf]
example : (∫⁻ b, (if b then ∞ else 0 : ℝ≥0∞) ∂SampLib.Complement.law 0) = ∞ := by
  simp [SampLib.Complement.law, SampLib.RealCoin.lintegral_law,
    SampLib.RealCoin.credit, SampLib.RealCoin.pmf]

example : (SampLib.OnePlusHalf.bias 0 : ℝ) = 1 / 2 := by
  norm_num [SampLib.OnePlusHalf.bias]
example : (SampLib.OnePlusHalf.bias 1 : ℝ) = 1 := by
  norm_num [SampLib.OnePlusHalf.bias]
example : (SampLib.ComplementHalf.bias 0 : ℝ) = 1 / 2 := by
  norm_num [SampLib.ComplementHalf.bias_coe]
example : (SampLib.ComplementHalf.bias 1 : ℝ) = 0 := by
  norm_num [SampLib.ComplementHalf.bias_coe]
example : (∫⁻ b, (if b then 0 else ∞ : ℝ≥0∞)
    ∂SampLib.RealCoin.law (SampLib.OnePlusHalf.bias 1)) = 0 := by
  norm_num [SampLib.RealCoin.lintegral_law, SampLib.RealCoin.credit,
    SampLib.RealCoin.pmf, SampLib.OnePlusHalf.bias]
example : (∫⁻ b, (if b then ∞ else 0 : ℝ≥0∞)
    ∂SampLib.RealCoin.law (SampLib.ComplementHalf.bias 1)) = 0 := by
  norm_num [SampLib.RealCoin.lintegral_law, SampLib.RealCoin.credit,
    SampLib.RealCoin.pmf, SampLib.ComplementHalf.bias_coe]

example : (SampLib.OneDivOnePlus.bias 0 : ℝ) = 1 := by
  norm_num [SampLib.OneDivOnePlus.bias, SampLib.EvenParity.bias]
example : (SampLib.OneDivOnePlus.bias 1 : ℝ) = 1 / 2 := by
  norm_num [SampLib.OneDivOnePlus.bias, SampLib.EvenParity.bias]
example : (SampLib.OneMinusOverOnePlus.bias 0 : ℝ) = 1 := by
  norm_num [SampLib.OneMinusOverOnePlus.bias]
example : (SampLib.OneMinusOverOnePlus.bias 1 : ℝ) = 0 := by
  norm_num [SampLib.OneMinusOverOnePlus.bias]
example : (∫⁻ b, (if b then 0 else ∞ : ℝ≥0∞) ∂SampLib.OneDivOnePlus.law 0) = 0 := by
  norm_num [SampLib.OneDivOnePlus.law, SampLib.OneDivOnePlus.bias,
    SampLib.EvenParity.bias, SampLib.RealCoin.lintegral_law,
    SampLib.RealCoin.credit, SampLib.RealCoin.pmf]
example : (∫⁻ b, (if b then ∞ else 0 : ℝ≥0∞)
    ∂SampLib.RealCoin.law (SampLib.OneMinusOverOnePlus.bias 1)) = 0 := by
  norm_num [SampLib.OneMinusOverOnePlus.bias, SampLib.RealCoin.lintegral_law,
    SampLib.RealCoin.credit, SampLib.RealCoin.pmf]

example (q : unitInterval) : (SampLib.BernoulliRace.bias 0 q : ℝ) = 0 := by
  simp [SampLib.BernoulliRace.bias]
example (p : unitInterval) (hp : 0 < (p : ℝ)) :
    (SampLib.BernoulliRace.bias p 0 : ℝ) = 1 := by
  simp [SampLib.BernoulliRace.bias, hp.ne']
example : (SampLib.BernoulliRace.bias 1 1 : ℝ) = 1 / 2 := by
  norm_num [SampLib.BernoulliRace.bias]
theorem geometric_zero : SampLib.GeometricFailures.law 0 = MeasureTheory.Measure.dirac 0 := by
  suffices h : ProbabilityTheory.geometricMeasure 1 = MeasureTheory.Measure.dirac 0 by
    simpa [SampLib.GeometricFailures.law, SampLib.GeometricFailures.stopBias] using h
  apply MeasureTheory.Measure.ext_of_singleton
  intro n
  rw [ProbabilityTheory.geometricMeasure_singleton (p := 1) (by norm_num)]
  cases n <;> simp
example : (∫⁻ n, (if n = 0 then 0 else ∞ : ℝ≥0∞)
    ∂SampLib.GeometricFailures.law 0) = 0 := by
  rw [geometric_zero]
  simp
example : (∫⁻ b, (if b then ∞ else 0 : ℝ≥0∞) ∂SampLib.BernoulliRace.law 0 1) = 0 := by
  norm_num [SampLib.BernoulliRace.law, SampLib.BernoulliRace.bias,
    SampLib.RealCoin.lintegral_law, SampLib.RealCoin.credit, SampLib.RealCoin.pmf]

#print axioms SampLib.Complement.complement_distSpec
#print axioms SampLib.CoinProduct.coinProduct_distSpec
#print axioms SampLib.CoinDisjunction.coinDisjunction_distSpec
#print axioms SampLib.CoinConditional.coinConditional_distSpec
#print axioms SampLib.EvenParity.evenParity_distSpec
#print axioms SampLib.CoinMean.coinMean_distSpec
#print axioms SampLib.OnePlusHalf.onePlusHalf_distSpec
#print axioms SampLib.ComplementHalf.complementHalf_distSpec
#print axioms SampLib.OneDivOnePlus.oneDivOnePlus_distSpec
#print axioms SampLib.OneMinusOverOnePlus.oneMinusOverOnePlus_distSpec
#print axioms SampLib.BernoulliRace.bernoulliRace_distSpec
#print axioms SampLib.GeometricFailures.geometricFailures_distSpec
#print axioms ProbabilityTheory.lintegral_geometricMeasure_succ

example (p q : unitInterval) :
    (SampLib.CoinMean.bias p q : ℝ) = ((p : ℝ) + (q : ℝ)) / 2 := by
  simp [SampLib.CoinMean.bias, SampLib.CoinConditional.bias, SampLib.VonNeumann.fairBias]
  ring

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS SampLib
variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

-- Each accepted spec can preserve an arbitrary linear caller resource.
theorem frame {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    {E : CoPset} {e : Exp rT} {encode : α → Val rT}
    (h : IsDistSpec (GF := GF) E e μ encode) (F : α → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂μ) ∗ I -∗ tglWp E e
      (fun v : Val rT => iprop(∃ b : α, ⌜v = encode b⌝ ∗ ↯ (F b) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply (h.wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HI
  itrivial

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂Complement.law p) ∗ I -∗
      tglWp E pl(&Occil.complement &coin.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) :=
  frame (Complement.complement_distSpec E p coin hcoin) F I

example (E : CoPset) (p : unitInterval) (coin : Val rT) (hp : (p : ℝ) < 1)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂EvenParity.law p) ∗ I -∗
      tglWp E pl(&Occil.evenParity &coin.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) :=
  frame (EvenParity.evenParity_distSpec E p coin hp hcoin) F I
example (E : CoPset) (p q : unitInterval) (left right : Val rT)
    (hl : IsDistSpec (GF := GF) E pl(&left.fst #()) (RealCoin.law p) Val.bool)
    (hr : IsDistSpec (GF := GF) E pl(&right.fst #()) (RealCoin.law q) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂CoinProduct.law p q) ∗ I -∗
      tglWp E pl(&Occil.coinProduct &left.fst &right.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) :=
  frame (CoinProduct.coinProduct_distSpec E p q left right hl hr) F I

example (E : CoPset) (p q : unitInterval) (left right : Val rT)
    (hl : IsDistSpec (GF := GF) E pl(&left.fst #()) (RealCoin.law p) Val.bool)
    (hr : IsDistSpec (GF := GF) E pl(&right.fst #()) (RealCoin.law q) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂CoinDisjunction.law p q) ∗ I -∗
      tglWp E pl(&Occil.coinDisjunction &left.fst &right.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) :=
  frame (CoinDisjunction.coinDisjunction_distSpec E p q left right hl hr) F I

example (E : CoPset) (p q r : unitInterval) (left right select : Val rT)
    (hl : IsDistSpec (GF := GF) E pl(&left.fst #()) (RealCoin.law p) Val.bool)
    (hr : IsDistSpec (GF := GF) E pl(&right.fst #()) (RealCoin.law q) Val.bool)
    (hs : IsDistSpec (GF := GF) E pl(&select.fst #()) (RealCoin.law r) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂CoinConditional.law p q r) ∗ I -∗
      tglWp E pl(&Occil.coinConditional &left.fst &right.fst &select.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) :=
  frame (CoinConditional.coinConditional_distSpec E p q r left right select hl hr hs) F I

example [ProbLangDist.IsUniformInt rT] (E : CoPset) (p q : unitInterval) (left right : Val rT)
    (hl : IsDistSpec (GF := GF) E pl(&left.fst #()) (RealCoin.law p) Val.bool)
    (hr : IsDistSpec (GF := GF) E pl(&right.fst #()) (RealCoin.law q) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂CoinMean.law p q) ∗ I -∗
      tglWp E pl(&Occil.coinMean &left.fst &right.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) :=
  frame (CoinMean.coinMean_distSpec E p q left right hl hr) F I

example [ProbLangDist.IsUniformInt rT] (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hc : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law (OnePlusHalf.bias p)) ∗ I -∗
      tglWp E pl(&Occil.FactoryExtra.onePlusHalf &coin.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) :=
  frame (OnePlusHalf.onePlusHalf_distSpec E p coin hc) F I

example [ProbLangDist.IsUniformInt rT] (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hc : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law (ComplementHalf.bias p)) ∗ I -∗
      tglWp E pl(&Occil.FactoryExtra.complementHalf &coin.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) :=
  frame (ComplementHalf.complementHalf_distSpec E p coin hc) F I

example [ProbLangDist.IsUniformInt rT] (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hc : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂OneDivOnePlus.law p) ∗ I -∗
      tglWp E pl(&Occil.oneDivOnePlus &coin.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) :=
  frame (OneDivOnePlus.oneDivOnePlus_distSpec E p coin hc) F I

example [ProbLangDist.IsUniformInt rT] (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hc : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law (OneMinusOverOnePlus.bias p)) ∗ I -∗
      tglWp E pl(&Occil.FactoryExtra.oneMinusOverOnePlus &coin.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) :=
  frame (OneMinusOverOnePlus.oneMinusOverOnePlus_distSpec E p coin hc) F I

example [ProbLangDist.IsUniformInt rT] (E : CoPset) (p q : unitInterval)
    (hsum : 0 < (p : ℝ) + q) (left right : Val rT)
    (hl : IsDistSpec (GF := GF) E pl(&left.fst #()) (RealCoin.law p) Val.bool)
    (hr : IsDistSpec (GF := GF) E pl(&right.fst #()) (RealCoin.law q) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂BernoulliRace.law p q) ∗ I -∗
      tglWp E pl(&Occil.bernoulliRace &left.fst &right.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) :=
  frame (BernoulliRace.bernoulliRace_distSpec E p q hsum left right hl hr) F I

example (E : CoPset) (p : unitInterval) (hp : (p : ℝ) < 1) (coin : Val rT)
    (hc : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (offset : ℤ) (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ n, F n ∂GeometricFailures.law p) ∗ I -∗
      tglWp E pl(&Occil.geometricFailures &coin.fst #offset)
        (fun v : Val rT => iprop(∃ n : ℕ,
          ⌜v = Val.int (offset + n)⌝ ∗ ↯ (F n) ∗ I)) :=
  frame (GeometricFailures.geometricFailures_distSpec E p hp coin hc offset) F I

-- Concrete compositions with the already verified integer fair coin.
example [ProbLangDist.IsUniformInt rT] (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.complement &Occil.fairCoin #())
      (Complement.law VonNeumann.fairBias) Val.bool :=
  Complement.complement_distSpec E VonNeumann.fairBias
    ⟨Occil.fairCoin, .lam (by is_lc), by is_lc⟩ (FairCoin.fairCoin_distSpec E)

example [ProbLangDist.IsUniformInt rT] (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.oneDivOnePlus &Occil.fairCoin #())
      (OneDivOnePlus.law VonNeumann.fairBias) Val.bool :=
  OneDivOnePlus.oneDivOnePlus_distSpec E VonNeumann.fairBias
    ⟨Occil.fairCoin, .lam (by is_lc), by is_lc⟩ (FairCoin.fairCoin_distSpec E)

example [ProbLangDist.IsUniformInt rT] (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.geometricFailures &Occil.fairCoin #(-7))
      (GeometricFailures.law VonNeumann.fairBias) (fun n : ℕ => Val.int (-7 + n)) :=
  GeometricFailures.geometricFailures_distSpec E VonNeumann.fairBias
    (by norm_num [VonNeumann.fairBias])
    ⟨Occil.fairCoin, .lam (by is_lc), by is_lc⟩ (FairCoin.fairCoin_distSpec E) (-7)

end
end ReviewCoins
