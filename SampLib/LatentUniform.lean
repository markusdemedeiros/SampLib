import SampLib.Distributions.LatentReal.Uniform
import SampLib.PSRNIntegerPower
import SampLib.LatentSpec
import Samplers.PSRN.Core

/-! # A uniform real whose digits remain deferred

Construction allocates a memoized stream. Observations refine its posterior and
return rational enclosures of the same latent uniform, retaining ownership for
later reads through any alias of the returned closure.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentUniform

private instance prefix_closed {rT : Type} :
    ClosedExp (Occil.uniformBagPrefix : Exp rT) where
  lc := by is_lc
  fv := by
    simp [Occil.uniformBagPrefix, Occil.uniformBagStep, Occil.newUniformBag,
      Occil.fairCoin, Exp.fv]

private instance fromBag_closed {rT : Type} :
    ClosedExp (Occil.PSRN.fromUniformBag : Exp rT) where
  lc := by is_lc
  fv := by
    simp [Occil.PSRN.fromUniformBag, Occil.PSRN.integerPower, Occil.uniformBagPrefix,
      Occil.uniformBagStep, Occil.newUniformBag, Occil.fairCoin, Exp.fv]

/-- The actual interval-oracle closure returned for a uniform bag. -/
def value {rT : Type} (l : Loc) : Val rT :=
  ⟨pl(fun bits,
    if bits < #0 then fail else
      let numerator := &Occil.uniformBagPrefix #loc l bits;
      let denominator := &Occil.PSRN.integerPower #2 bits;
      (numerator, (numerator + #1, denominator))), .lam (by is_lc), by is_lc⟩

/-- Finite observation format: lower numerator, upper numerator, denominator. -/
def intervalValue {rT : Type} (a b d : ℤ) : Val rT :=
  .pair (.int a) (.pair (.int b) (.int d))

noncomputable section

/-- Posterior model for the original unit uniform, including all previously cached bits. -/
def model : LatentReal.Model ℝ (List Bool) where
  posterior := DyadicPosterior.law
  probability := fun _ => inferInstance
  value := id
  measurable_value := measurable_id
  refines := List.IsPrefix
  refines_refl := List.prefix_refl
  refines_trans := List.IsPrefix.trans
  absolutelyContinuous := DyadicPosterior.law_refines
  error n _ := (2 ^ n : ℝ)⁻¹
  error_tendsto _ := Filter.Eventually.of_forall fun _ =>
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))

/-- The finite rational interval exposed at a requested precision. -/
def interval (q : List Bool) (n : ℕ) : LatentReal.RationalInterval where
  lower := UniformBag.rank (q.take n)
  upper := UniformBag.rank (q.take n) + 1
  denominator := 2 ^ n
  denominator_pos := pow_pos (by norm_num) _
  lower_le_upper := by omega

/-- Finite observation intervals shrink at the requested binary rate. -/
theorem interval_encloses {p q : List Bool} {n : ℕ}
    (hread : UniformBag.readRefines p n q) : model.Encloses q n (interval q n) := by
  filter_upwards [ae_read_interval hread] with u hu
  refine ⟨?_, ?_⟩
  · simpa [LatentReal.RationalInterval.Contains, LatentReal.RationalInterval.lowerReal,
      LatentReal.RationalInterval.upperReal, interval, model] using hu
  · change ((UniformBag.rank (q.take n) + 1 : ℤ) : ℝ) / (2 ^ n : ℤ) -
      (UniformBag.rank (q.take n) : ℝ) / (2 ^ n : ℤ) ≤ (2 ^ n : ℝ)⁻¹
    push_cast
    rw [add_div, add_sub_cancel_left, one_div]

@[simp] theorem model_initial_law : model.law [] = DyadicPosterior.unitLaw := by
  simp [LatentReal.Model.law, model]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Both the closure and its cached state are tied to the same physical root. -/
def owns (v : Val rT) (p : List Bool) : IProp GF := iprop(
  ∃ l : Loc, ⌜v = value l⌝ ∗ UniformBag.owns l p)

/-- Allocation defers the draw: all future continuation credit remains posterior credit. -/
theorem twp_newUniform (E : CoPset) (F : ℝ → ℝ≥0∞) :
    iprop(↯ (DyadicPosterior.credit [] F)) ⊢
      tglWp E pl(&Occil.PSRN.newUniform #())
        (fun v : Val rT => iprop(owns v [] ∗ ↯ (DyadicPosterior.credit [] F))) := by
  iintro Hcredit
  iterate 2 twp_pure
  twp_bind pl(alloc(inl(#())))
  ieval (change _ ⊢ tglWp E (.alloc (.ofVal (Val.inl (Val.unit : Val rT)))) _)
  iapply (twp_alloc (v := Val.inl (Val.unit : Val rT)))
  iintro %l Hbag
  twp_pure
  isimp only [ClosedExp.openRec, ClosedExp.closeRec]
  twp_pure
  isimp only [ClosedExp.openRec, ClosedExp.closeRec]
  twp_value
  imodintro
  iframe Hcredit
  isimp only [owns]
  iexists l
  isimp only [UniformBag.owns, UniformBag.emptyVal]
  iframe Hbag
  ipureintro
  apply Val.ext
  simp only [value]
  rfl

/-- A finite observation refines the owned stream without changing its latent draw. -/
theorem twp_observe (E : CoPset) (v : Val rT) (p : List Bool) (n : ℕ)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    iprop(owns v p ∗ ↯ (DyadicPosterior.credit p F)) ⊢
      tglWp E pl(&v.fst #int (n : ℤ))
        (fun result : Val rT => iprop(∃ q : List Bool,
          ⌜UniformBag.readRefines p n q ∧
            result = LatentReal.intervalVal (interval q n)⌝ ∗
          owns v q ∗ ↯ (DyadicPosterior.credit q F))) := by
  iintro ⟨Hstate, Hcredit⟩
  isimp only [owns] at Hstate
  ihave ⟨%l, %hv, Hbag⟩ := Hstate
  subst v
  unfold value
  iterate 3 twp_pure
  isimp only [ClosedExp.openRec, ClosedExp.closeRec]
  twp_bind pl(&Occil.uniformBagPrefix #loc l #int (n : ℤ))
  iapply tglWp_wand
  isplitl [Hbag Hcredit]
  · iapply UniformBag.twp_uniformBagPrefix E l p n F hF
    iframe Hbag Hcredit
  iintro %result ⟨%q, %hq, Hbag, Hcredit⟩
  rcases hq with ⟨hrefines, rfl⟩
  twp_pure
  isimp only [ClosedExp.openRec, ClosedExp.closeRec]
  twp_bind pl(&Occil.PSRN.integerPower #2 #int (n : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply PSRNIntegerPower.twp_integerPower E 2 n
  iintro %result %hresult
  subst result
  twp_pures
  twp_value
  imodintro
  iexists q
  iframe Hcredit
  isplitl []
  · ipureintro
    exact ⟨hrefines, rfl⟩
  isimp only [owns]
  iexists l
  iframe Hbag
  ipureintro
  rfl

/-- Reusable observation protocol for aliases of a memoized uniform oracle. -/
theorem oracleSpec (E : CoPset) :
    LatentReal.IsOracleSpec (GF := GF) E model owns where
  observe v p n F hF := by
    iintro Hstate
    have hread := twp_observe (rT := rT) (GF := GF) E v p n F hF
    unfold DyadicPosterior.credit at hread
    isimp only [model] at Hstate
    iapply tglWp_wand
    isplitl [Hstate]
    · iapply hread $$ Hstate
    iintro %result ⟨%q, %hq, Hstate, Hcredit⟩
    rcases hq with ⟨hrefines, rfl⟩
    iexists q, interval q n
    rw [show model.posterior q = DyadicPosterior.law q from rfl]
    iframe Hstate Hcredit
    ipureintro
    exact ⟨rfl, hrefines.1, interval_encloses hrefines⟩

/-- The actual constructor represents one unit uniform through all future observations. -/
theorem newUniform_latentDistSpec (E : CoPset) :
    LatentReal.IsLatentDistSpec (GF := GF) E pl(&Occil.PSRN.newUniform #())
      model [] owns where
  oracle := oracleSpec E
  spec F _ := by
    have hnew := twp_newUniform (rT := rT) (GF := GF) E F
    unfold DyadicPosterior.credit at hnew
    iintro Hcredit
    isimp only [model] at Hcredit
    iapply tglWp_wand
    isplitl [Hcredit]
    · iapply hnew $$ Hcredit
    iintro %v ⟨Hstate, Hcredit⟩
    iexists []
    rw [show model.posterior [] = DyadicPosterior.law [] from rfl]
    iframe Hstate Hcredit
    ipureintro
    exact List.prefix_refl _

end specification

end

end SampLib.LatentUniform
