import SampLib.Bernoulli.Syntax.MinimumComplement
import SampLib.Bernoulli.Support.MinimumComplementBinomial
import SampLib.Bernoulli.Laws.MinimumFactories
import Samplers.Bernoulli.Series

/-! # The Catalan-mixture minimum-complement factory

The fair first-passage walk preserves the harmonic credit. At absorption, the
padded binomial stage realizes that credit exactly.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.MinimumComplement

noncomputable section

theorem minimumComplement_lc {rT : Type} :
    (Occil.FactoryExtra.minimumComplement : Exp rT).IsLocallyClosed := by is_lc

theorem minimumComplement_fv {rT : Type} :
    (Occil.FactoryExtra.minimumComplement : Exp rT).fv = ∅ := by
  simp [Occil.FactoryExtra.minimumComplement, Exp.fv, FairCoin.fairCoin_fv,
    FactoryChoose.choose_fv, Occil.FactoryExtra.intPower, Occil.binomial,
    RationalCoin.rationalCoin_fv]

@[simp] theorem minimumComplement_openRec {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.FactoryExtra.minimumComplement =
      Occil.FactoryExtra.minimumComplement :=
  (Exp.open_lc k e _ minimumComplement_lc).symm

@[simp] theorem minimumComplement_closeRec {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.FactoryExtra.minimumComplement : Exp rT) =
      Occil.FactoryExtra.minimumComplement :=
  Exp.closeRec_fresh x _ k (by simp [minimumComplement_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem twp_minimumComplement (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (bias p) F) -∗
      tglWp E pl(&Occil.FactoryExtra.minimumComplement &coin.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iapply Program.twp_open E coin
  twp_bind pl(&walk #0 #0)
  isimp only [← initial_bias] at Hcredit
  iapply twp_index E p F _ ?_ $$ Hcredit
  intro m hm
  iintro Hcredit
  twp_value
  imodintro
  ieval (
    change _ ⊢ tglWp E
      (.app (.lam (Program.initialBody coin)) (Val.int (m : ℤ)).fst) _)
  iapply Program.twp_finish E coin m
  iapply twp_binomialBody E p coin hcoin m F $$ Hcredit

/-- The existing source samples `Bernoulli(min(p,1-p))` for every input bias. -/
theorem minimumComplement_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.minimumComplement &coin.fst #())
      (RealCoin.law (bias p)) Val.bool where
  spec F _ := by
    rw [RealCoin.lintegral_law]
    exact wand_entails (twp_minimumComplement E p coin hcoin F)

end specification

end

end SampLib.MinimumComplement
