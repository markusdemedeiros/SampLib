import SampLib.Samplers.IterateCoin
import Metrology.Iris.LocalBI
import SampLib.Samplers.UniformInt
import SampLib.Samplers.FairCoin
import SampLib.Samplers.BoundedGeometric
import SampLib.Samplers.Binomial
import SampLib.Samplers.RandomWalk
import SampLib.Samplers.Geometric
import SampLib.Samplers.NegativeBinomial
import SampLib.Samplers.RndInt
import SampLib.Samplers.RndIntRange
import SampLib.Samplers.RndIntExcRange
import SampLib.Samplers.RationalCoin
import SampLib.Samplers.VonNeumann

/-!
# Independent discrete-sampler caller checks

Reviewed clients preserve arbitrary Iris resources and exercise parameter
boundaries. Compile with `lake env lean agent-docs/reviews/DiscreteCallers.lean`.
Axiom checks cover each core, public specification, and expectation argument.
-/

namespace IterateAudit
open Set ProbLang
open scoped ENNReal
noncomputable section
open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS SampLib
variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (n : ℕ) (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (IterateCoin.credit p n F) ∗ I -∗
      tglWp E pl(&Occil.iterateCoin &coin.fst #int (n : ℤ))
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  have hspec := IterateCoin.iterateCoin_distSpec E p coin hcoin n
  isimp only [IterateCoin.credit, ← RealCoin.lintegral_law] at Hcredit
  iapply (hspec.wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HI
  itrivial

example (n : ℕ) : IterateCoin.bias 0 (n + 1) = 0 := by
  apply Subtype.ext
  simp [IterateCoin.bias]

example (n : ℕ) : IterateCoin.bias 1 n = 1 := by
  apply Subtype.ext
  simp [IterateCoin.bias]

example (p : unitInterval) : IterateCoin.bias p 0 = 1 := by
  apply Subtype.ext
  simp [IterateCoin.bias]

#print axioms IterateCoin.twp_iterateCoin
#print axioms IterateCoin.iterateCoin_distSpec
#print axioms IterateCoin.expectation

end

end IterateAudit

namespace UniformFairAudit
open Set ProbLang
open scoped ENNReal
noncomputable section

open MeasureTheory in
example : SampLib.UniformInt.law 1 = Measure.dirac 0 := by
  simp [SampLib.UniformInt.law, Measure.uniformOfFinset]

abbrev fairValue {rT : Type _} : Val rT :=
  ⟨Occil.fairCoin, .lam (by is_lc), by is_lc⟩

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS SampLib
variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example (E : CoPset) (n : ℕ) [NeZero n] (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂UniformInt.law n) ∗ I -∗
      tglWp E pl(&Occil.uniformInt #int (n : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply ((UniformInt.uniformInt_distSpec E n).wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %k Hcredit
  iexists k
  iframe Hcredit HI
  itrivial

example (E : CoPset) (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law VonNeumann.fairBias) ∗ I -∗
      tglWp E pl(&Occil.fairCoin #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply ((FairCoin.fairCoin_distSpec E).wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HI
  itrivial

example (E : CoPset) (n : ℕ) :
    IsDistSpec (GF := GF) E pl(&Occil.iterateCoin &(fairValue (rT := rT)).fst #int (n : ℤ))
      (IterateCoin.law VonNeumann.fairBias n) Val.bool :=
  IterateCoin.iterateCoin_distSpec E VonNeumann.fairBias fairValue
    (FairCoin.fairCoin_distSpec E) n

#print axioms UniformInt.uniformInt_distSpec
#print axioms UniformInt.twp_uniformInt
#print axioms UniformInt.lintegral_law
#print axioms FairCoin.twp_fairCoin
#print axioms FairCoin.fairCoin_distSpec
#print axioms FairCoin.expectation

end

end UniformFairAudit

namespace BoundedAudit
open Set ProbLang
open scoped ENNReal
noncomputable section

open MeasureTheory in
example (n : ℕ) : SampLib.BoundedGeometric.law 0 n = Measure.dirac n := by
  induction n with
  | zero => rfl
  | succ n IH => simp [SampLib.BoundedGeometric.law, SampLib.RealCoin.pmf, IH]

open MeasureTheory in
example (n : ℕ) : SampLib.BoundedGeometric.law 1 (n + 1) = Measure.dirac 0 := by
  simp [SampLib.BoundedGeometric.law, SampLib.RealCoin.pmf]

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS SampLib
variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (n : ℕ) (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂BoundedGeometric.law p n) ∗ I -∗
      tglWp E pl(&Occil.boundedGeometric &coin.fst #int (n : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply ((BoundedGeometric.boundedGeometric_distSpec E p coin hcoin n).wp F
    (measurable_of_countable _) _) $$ Hcredit
  iintro %k Hcredit
  iexists k
  iframe Hcredit HI
  itrivial

#print axioms BoundedGeometric.twp_boundedGeometric
#print axioms BoundedGeometric.boundedGeometric_distSpec
#print axioms BoundedGeometric.expectation

end

end BoundedAudit

namespace BinomialAudit
open Set ProbLang
open scoped ENNReal
noncomputable section

open MeasureTheory in
example (n : ℕ) : SampLib.Binomial.law 0 n = Measure.dirac 0 := by
  induction n with
  | zero => rfl
  | succ n IH => simp [SampLib.Binomial.law, SampLib.RealCoin.pmf, IH]

open MeasureTheory in
example (n : ℕ) : SampLib.Binomial.law 1 n = Measure.dirac n := by
  induction n with
  | zero => rfl
  | succ n IH => simp [SampLib.Binomial.law, SampLib.RealCoin.pmf, IH]

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS SampLib
variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (n : ℕ) (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂Binomial.law p n) ∗ I -∗
      tglWp E pl(&Occil.binomial &coin.fst #int (n : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply ((Binomial.binomial_distSpec E p coin hcoin n).wp F
    (measurable_of_countable _) _) $$ Hcredit
  iintro %k Hcredit
  iexists k
  iframe Hcredit HI
  itrivial

#print axioms Binomial.twp_binomial
#print axioms Binomial.binomial_distSpec
#print axioms Binomial.expectation

end

end BinomialAudit

namespace RandomWalkAudit
open Set ProbLang
open scoped ENNReal
noncomputable section

open MeasureTheory in
example : SampLib.RandomWalk.law 0 = Measure.dirac 0 := rfl

open MeasureTheory in
example : SampLib.RandomWalk.law 1 {1} = ENNReal.ofReal (1 / 2 : ℝ) := by
  norm_num [SampLib.RandomWalk.law, SampLib.RealCoin.pmf, SampLib.VonNeumann.fairBias,
    Measure.map_apply (measurable_of_countable _)]

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS SampLib
variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example (E : CoPset) (n : ℕ) (F : ℤ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ z, F z ∂RandomWalk.law n) ∗ I -∗
      tglWp E pl(&Occil.randomWalk #int (n : ℤ))
        (fun v : Val rT => iprop(∃ z : ℤ, ⌜v = Val.int z⌝ ∗ ↯ (F z) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply ((RandomWalk.randomWalk_distSpec E n).wp F
    (measurable_of_countable _) _) $$ Hcredit
  iintro %z Hcredit
  iexists z
  iframe Hcredit HI
  itrivial

#print axioms RandomWalk.twp_randomWalk
#print axioms RandomWalk.randomWalk_distSpec
#print axioms RandomWalk.expectation

end

end RandomWalkAudit

namespace GeometricAudit
open Set ProbLang
open scoped ENNReal
noncomputable section

example : SampLib.Geometric.law 1 {0} = 1 := by
  rw [ProbabilityTheory.geometricMeasure_singleton (by norm_num)]
  norm_num

example (n : ℕ) : SampLib.Geometric.law 1 {n + 1} = 0 := by
  rw [ProbabilityTheory.geometricMeasure_singleton (by norm_num)]
  simp

abbrev fairValue {rT : Type _} : Val rT :=
  ⟨Occil.fairCoin, .lam (by is_lc), by is_lc⟩

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS SampLib
variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example (E : CoPset) (p : unitInterval) (hp : 0 < (p : ℝ)) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (Geometric.credit p F) ∗ I -∗
      tglWp E pl(&Occil.geometric &coin.fst #())
        (fun v : Val rT => iprop(∃ n : ℕ, ⌜v = Val.int (n : ℤ)⌝ ∗ ↯ (F n) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  isimp only [Geometric.credit] at Hcredit
  iapply ((Geometric.geometric_distSpec E p hp coin hcoin).wp F
    (measurable_of_countable _) _) $$ Hcredit
  iintro %n Hcredit
  iexists n
  iframe Hcredit HI
  itrivial

example [ProbLangDist.IsUniformInt rT] (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.geometric &(fairValue (rT := rT)).fst #())
      (Geometric.law VonNeumann.fairBias) (fun n : ℕ => Val.int (n : ℤ)) :=
  Geometric.geometric_distSpec E VonNeumann.fairBias (by norm_num [VonNeumann.fairBias])
    fairValue (FairCoin.fairCoin_distSpec E)

#print axioms Geometric.twp_geometric
#print axioms Geometric.geometric_distSpec
#print axioms Geometric.lintegral_coinCredit

end

end GeometricAudit

namespace NegativeBinomialAudit
open Set ProbLang
open scoped ENNReal
noncomputable section

open MeasureTheory in
private theorem geometric_one : SampLib.Geometric.law 1 = Measure.dirac 0 := by
  apply Measure.ext_of_singleton
  intro n
  rw [ProbabilityTheory.geometricMeasure_singleton (by norm_num)]
  cases n <;> simp

open MeasureTheory in
example (p : unitInterval) : SampLib.NegativeBinomial.law p 0 = Measure.dirac 0 := rfl

open MeasureTheory in
example (r : ℕ) : SampLib.NegativeBinomial.law 1 r = Measure.dirac 0 := by
  induction r with
  | zero => rfl
  | succ r IH => simp [SampLib.NegativeBinomial.law, IH, geometric_one, Measure.dirac_prod_dirac,
      Measure.map_dirac' (measurable_of_countable _)]

abbrev fairValue {rT : Type _} : Val rT :=
  ⟨Occil.fairCoin, .lam (by is_lc), by is_lc⟩

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS SampLib
variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (r : ℕ) (hp : r = 0 ∨ 0 < (p : ℝ)) (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (NegativeBinomial.credit p r F) ∗ I -∗
      tglWp E pl(&Occil.negativeBinomial &coin.fst #int (r : ℤ))
        (fun v : Val rT => iprop(∃ n : ℕ, ⌜v = Val.int (n : ℤ)⌝ ∗ ↯ (F n) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  isimp only [NegativeBinomial.credit] at Hcredit
  iapply ((NegativeBinomial.negativeBinomial_distSpec E p coin hcoin r hp).wp F
    (measurable_of_countable _) _) $$ Hcredit
  iintro %n Hcredit
  iexists n
  iframe Hcredit HI
  itrivial

example [ProbLangDist.IsUniformInt rT] (E : CoPset) (r : ℕ) :
    IsDistSpec (GF := GF) E
      pl(&Occil.negativeBinomial &(fairValue (rT := rT)).fst #int (r : ℤ))
      (NegativeBinomial.law VonNeumann.fairBias r) (fun n : ℕ => Val.int (n : ℤ)) :=
  NegativeBinomial.negativeBinomial_distSpec E VonNeumann.fairBias fairValue
    (FairCoin.fairCoin_distSpec E) r (Or.inr (by norm_num [VonNeumann.fairBias]))

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 0) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.negativeBinomial &coin.fst #int (0 : ℤ))
      (NegativeBinomial.law 0 0) (fun n : ℕ => Val.int (n : ℤ)) :=
  NegativeBinomial.negativeBinomial_distSpec E 0 coin hcoin 0 (Or.inl rfl)

#print axioms NegativeBinomial.twp_negativeBinomial
#print axioms NegativeBinomial.negativeBinomial_distSpec
#print axioms NegativeBinomial.credit_succ
#print axioms ProbabilityTheory.lintegral_geometricMeasure_succ

end

end NegativeBinomialAudit

namespace RangesAudit
open Set ProbLang
open scoped ENNReal
noncomputable section

open MeasureTheory in
example : SampLib.RndInt.law 0 = Measure.dirac 0 := by
  simp [SampLib.RndInt.law, SampLib.UniformInt.law, Measure.uniformOfFinset]

open MeasureTheory in
example (z : ℤ) : SampLib.RndIntRange.law z z = Measure.dirac z := by
  simp [SampLib.RndIntRange.law, SampLib.RndInt.law, SampLib.UniformInt.law,
    Measure.uniformOfFinset, Measure.map_dirac' (measurable_of_countable _)]

open MeasureTheory in
example : SampLib.RndIntExcRange.law (-7) (-6) (by norm_num) = Measure.dirac (-7) := by
  norm_num [SampLib.RndIntExcRange.law, SampLib.UniformInt.law,
    Measure.uniformOfFinset, Measure.map_dirac' (measurable_of_countable _)]

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS SampLib
variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example (E : CoPset) (hi : ℕ) (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂RndInt.law hi) ∗ I -∗ tglWp E pl(&Occil.rndInt #int (hi : ℤ))
      (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply ((RndInt.rndInt_distSpec E hi).wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %k Hcredit
  iexists k
  iframe Hcredit HI
  itrivial

example (E : CoPset) (lo hi : ℤ) (h : lo ≤ hi) (F : ℤ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ z, F z ∂RndIntRange.law lo hi) ∗ I -∗ tglWp E pl(&Occil.rndIntRange #lo #hi)
      (fun v : Val rT => iprop(∃ z : ℤ, ⌜v = Val.int z⌝ ∗ ↯ (F z) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply ((RndIntRange.rndIntRange_distSpec E lo hi h).wp F (measurable_of_countable _) _)
    $$ Hcredit
  iintro %z Hcredit
  iexists z
  iframe Hcredit HI
  itrivial

example (E : CoPset) (lo hi : ℤ) (h : lo < hi) (F : ℤ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ z, F z ∂RndIntExcRange.law lo hi h) ∗ I -∗
      tglWp E pl(&Occil.rndIntExcRange #lo #hi)
        (fun v : Val rT => iprop(∃ z : ℤ, ⌜v = Val.int z⌝ ∗ ↯ (F z) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply ((RndIntExcRange.rndIntExcRange_distSpec E lo hi h).wp F
    (measurable_of_countable _) _) $$ Hcredit
  iintro %z Hcredit
  iexists z
  iframe Hcredit HI
  itrivial

#print axioms RndInt.twp_rndInt
#print axioms RndInt.rndInt_distSpec
#print axioms RndInt.expectation
#print axioms RndIntRange.twp_rndIntRange
#print axioms RndIntRange.rndIntRange_distSpec
#print axioms RndIntRange.expectation
#print axioms RndIntExcRange.twp_rndIntExcRange
#print axioms RndIntExcRange.rndIntExcRange_distSpec
#print axioms RndIntExcRange.expectation

end

end RangesAudit

namespace RationalAudit
open Set ProbLang
open scoped ENNReal
noncomputable section

example (b : ℤ) (hb : 0 < b) : SampLib.RationalCoin.bias 0 b (by omega) hb hb.le = 0 := by
  apply Subtype.ext
  simp [SampLib.RationalCoin.bias]

example (b : ℤ) (hb : 0 < b) : SampLib.RationalCoin.bias b b hb.le hb le_rfl = 1 := by
  apply Subtype.ext
  simp [SampLib.RationalCoin.bias, show (b : ℝ) ≠ 0 by exact_mod_cast hb.ne']

abbrev rationalValue {rT : Type _} (a b : ℤ) : Val rT :=
  ⟨pl(fun u, &Occil.rationalCoin #int a #int b), .lam (by is_lc), by is_lc⟩

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS SampLib
variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example (E : CoPset) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) (hab : a ≤ b)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂RealCoin.law (RationalCoin.bias a b ha hb hab)) ∗ I -∗
      tglWp E pl(&Occil.rationalCoin #int a #int b)
        (fun v : Val rT => iprop(∃ x : Bool, ⌜v = Val.bool x⌝ ∗ ↯ (F x) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply ((RationalCoin.rationalCoin_distSpec E a b ha hb hab).wp F
    (measurable_of_countable _) _) $$ Hcredit
  iintro %x Hcredit
  iexists x
  iframe Hcredit HI
  itrivial

theorem inputSpec (E : CoPset) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) (hab : a ≤ b) :
    IsDistSpec (GF := GF) E pl(&(rationalValue (rT := rT) a b).fst #())
      (RealCoin.law (RationalCoin.bias a b ha hb hab)) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    simp only [RationalCoin.rationalCoin_closeRec, RationalCoin.rationalCoin_openRec]
    iapply (RationalCoin.rationalCoin_distSpec E a b ha hb hab).spec F hF $$ Hcredit

example (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.vonNeumann &(rationalValue (rT := rT) 1 4).fst #())
      VonNeumann.law Val.bool :=
  VonNeumann.vonNeumann_distSpec E (RationalCoin.bias 1 4 (by norm_num) (by norm_num)
    (by norm_num)) (rationalValue 1 4)
    (by norm_num [RationalCoin.bias]) (by norm_num [RationalCoin.bias])
    (inputSpec E 1 4 (by norm_num) (by norm_num) (by norm_num))

#print axioms RationalCoin.twp_rationalCoin
#print axioms RationalCoin.rationalCoin_distSpec
#print axioms RationalCoin.expectation

end

end RationalAudit
