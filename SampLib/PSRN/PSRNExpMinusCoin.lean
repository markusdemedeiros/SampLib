import SampLib.PSRN.Laws.ExpMinusCoinKernel
import SampLib.PSRN.Syntax.PSRNExpMinusCoin
import SampLib.PSRN.Support.LatentExactFloor
import SampLib.PSRN.Support.PSRNCoin
import SampLib.PSRN.Support.LatentRationalSubtract
import SampLib.PSRN.Support.LatentCoinExponential

/-! # Conditional negative-exponential trials from an owned PSRN

The floor certificate splits the latent real into integer and fractional parts.
Every subsequent call retains the original handle and arbitrary joint credit.
-/

open ProbLang
open scoped ENNReal SampLib.LatentReal.ExpMinusCoin.Program

namespace SampLib.LatentReal.ExpMinusCoin

noncomputable section

private theorem fractional_credit {Ω S : Type} [MeasurableSpace Ω] (D : Model Ω S) (t : S) (z : ℤ)
    (G : Bool → Ω → ℝ≥0∞) :
    LatentCoin.credit (D.subtractRational z 1) t (CoinExponential.bias (fractionBias D z)) G =
      ∫⁻ x, LatentCoin.kernel (CoinExponential.bias (fractionBias D z)) G x ∂D.posterior t := rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec ProbLang.openRec_val_fst

private theorem twp_open (E : CoPset) (source : Val ℝ) (Φ : Val ℝ → IProp GF) :
    tglWp E (Program.body source) Φ ⊢
      tglWp E pl(&Occil.PSRN.expMinusCoin &source.fst #()) Φ := by
  have hc : Exp.lcb [source, Val.unit].length (Program.sourceBody : Exp ℝ) = true :=
    Program.sourceBody_lcb
  have h := CurriedStep.twp_apply E [] [source, Val.unit] Program.sourceBody hc Φ
  rw [Program.opened_source] at h
  simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, ← Program.source_eq,
    CurriedStep.application, CurriedStep.context, List.map_cons, List.map_nil,
    Ectx.fill, List.foldl_cons, List.foldl_nil, EctxItem.fillItem, Exp.ofVal, flip] using h

private theorem twp_afterWhole (E : CoPset) (source : Val ℝ) (z : ℤ)
    (Φ : Val ℝ → IProp GF) :
    tglWp E (.cond pl(#int z < #0) .fail (Program.fractionBody source z)) Φ ⊢
      tglWp E (.app (.lam (Program.afterWhole source)) (Val.int z).fst) Φ := by
  have h := twp_beta E [] (Program.afterWhole source) (Val.int z) (by is_lc) Φ
  rw [Program.opened_afterWhole] at h
  simpa only [Ectx.fill, List.foldl_nil] using h

private theorem twp_afterFraction (E : CoPset) (fraction : Val ℝ) (z : ℤ)
    (Φ : Val ℝ → IProp GF) :
    tglWp E pl(if &Occil.expMinusRational #int z #1 #() then
      &Occil.expMinusFactory &(Program.fractionCoin fraction).fst #() else #false) Φ ⊢
      tglWp E (.app (.lam (Program.afterFraction z)) fraction.fst) Φ := by
  have h := twp_beta E [] (Program.afterFraction z) fraction (by is_lc) Φ
  simpa only [Ectx.fill, List.foldl_nil, Program.opened_afterFraction] using h

variable [ProbLangDist.IsUniformInt ℝ]

private theorem fractionCoin_spec (E : CoPset) (D : Model Ω S) (hD : D.MeasurableError)
    (owns : Val ℝ → S → IProp GF) (horacle : IsOracleSpec E D owns) :
    IsLatentCoinSpec E D owns (fun x => LatentBernoulli.bias (D.value x))
      Program.fractionCoin where
  measurable_bias := LatentBernoulli.measurable_bias.comp D.measurable_value
  spec source s G hG := by
    iintro H
    twp_pure
    iapply (Coin.coin_programSpec E D hD owns horacle).spec source s G hG $$ H

variable [ProbLangDist.IsUniformReal ℝ]

private theorem fractional_spec (E : CoPset) (D : Model Ω S) (hD : D.MeasurableError)
    (owns : Val ℝ → S → IProp GF) (horacle : IsOracleSpec E D owns)
    (source : Val ℝ) (z : ℤ) :
    IsLatentCoinProgramSpec E (D.subtractRational z 1)
      (ViewOwns (subtractRationalVal source z 1) (owns source))
      (CoinExponential.bias (fractionBias D z))
      (fun fraction => pl(&Occil.expMinusFactory &(Program.fractionCoin fraction).fst #())) := by
  have h := CoinExponential.exponential_programSpec E (D.subtractRational z 1)
    (ViewOwns (subtractRationalVal source z 1) (owns source))
    (fun x => LatentBernoulli.bias ((D.subtractRational z 1).value x)) Program.fractionCoin
    (fractionCoin_spec E (D.subtractRational z 1) (hD.subtractRational z 1) _
      (subtractRational_viewSpec E D (owns source) source (horacle.viewSpec E D owns source)
        z 1 (by norm_num)))
  have hφ : (fun x => LatentBernoulli.bias ((D.subtractRational z 1).value x)) =
      fractionBias D z := by
    funext x
    simp [fractionBias]
  rw [hφ] at h
  exact h

omit [ProbLangDist.IsUniformReal ℝ] in
private theorem whole_spec (E : CoPset) (z : ℤ) (hz : 0 ≤ z) :
    IsDistSpec (GF := GF) E pl(&Occil.expMinusRational #int z #1 #())
      (RealCoin.law (valueBias z)) Val.bool := by
  rw [whole_bias z hz]
  exact ExpMinusRational.expMinusRational_distSpec E z 1 hz (by norm_num)

omit [ProbLangDist ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
  [ProbLangDist.IsUniformReal ℝ] [ProbLangDist.IsUniformInt ℝ] in
private theorem fraction_post (D : Model Ω S) (owns : Val ℝ → S → IProp GF)
    (source fraction result : Val ℝ) (z : ℤ) (s t : S) (hst : D.refines s t)
    (G : Bool → Ω → ℝ≥0∞) :
    LatentCoin.post (D.subtractRational z 1)
      (ViewOwns (subtractRationalVal source z 1) (owns source)) fraction t G result ⊢
      LatentCoin.post D owns source s G result := by
  iintro Hpost
  isimp only [LatentCoin.post] at Hpost
  icases Hpost with ⟨%b, %u, %hu, Hstate, Hcredit⟩
  isimp only [ViewOwns] at Hstate
  icases Hstate with ⟨_, Hstate⟩
  rcases hu with ⟨rfl, htu⟩
  iapply LatentCoin.post_return D owns source s u b G (D.refines_trans hst htu)
  isimp only [show (D.subtractRational z 1).posterior u = D.posterior u from rfl] at Hcredit
  iframe Hstate Hcredit

omit [ProbLangDist.IsUniformReal ℝ] [ProbLangDist.IsUniformInt ℝ] in
private theorem twp_floor (E : CoPset) (D : Model Ω S) (hD : D.MeasurableError)
    (owns : Val ℝ → S → IProp GF) (horacle : IsOracleSpec E D owns)
    (source : Val ℝ) (s : S)
    (hresolve : Floor.AvoidsGrid D 1 s ∨ ∀ᵐ x ∂D.posterior s, D.error 1 x = 0)
    (H : ℤ → Ω → ℝ≥0∞) (hH : ∀ z, Measurable (H z)) :
    iprop(owns source s ∗ ↯ (∫⁻ x, Floor.outputCredit D 1 H x ∂D.posterior s)) ⊢
      tglWp E pl(&Occil.PSRN.floorScaled &source.fst #1)
        (Floor.post D 1 (owns source) s H) := by
  rcases hresolve with hgrid | hzero
  · exact Floor.twp_floorScaled E D hD owns horacle source 1 (by norm_num) s hgrid H hH
  · exact Floor.twp_floorScaled_exact E D owns horacle source 1 (by norm_num) s hzero H hH

/-- The floor resolves by grid avoidance or exact enclosure; all output credits stay joint. -/
theorem twp_expMinusCoin (E : CoPset) (D : Model Ω S) (hD : D.MeasurableError)
    (owns : Val ℝ → S → IProp GF) (horacle : IsOracleSpec E D owns)
    (source : Val ℝ) (s : S) (hadmissible : Admissible D s)
    (G : Bool → Ω → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) :
    iprop(owns source s ∗ ↯ (LatentCoin.credit D s (bias D) G)) ⊢
      tglWp E pl(&Occil.PSRN.expMinusCoin &source.fst #()) (LatentCoin.post D owns source s G) := by
  iintro ⟨Hstate, Hcredit⟩
  iapply twp_open E source
  unfold Program.body
  twp_bind pl(&Occil.PSRN.floorScaled &source.fst #1)
  isimp only [← expectation D s hadmissible.1 G] at Hcredit
  iapply tglWp_wand
  isplitl [Hstate Hcredit]
  · iapply twp_floor E D hD owns horacle source s hadmissible.2
      (floorCredit D G) (measurable_floorCredit D G hG)
    iframe Hstate Hcredit
  iintro %whole Hpost
  isimp only [Floor.post] at Hpost
  icases Hpost with ⟨%z, %t, %ht, Hstate, Hcredit⟩
  rcases ht with ⟨rfl, hst, hfloor⟩
  have hz : 0 ≤ z := whole_nonneg ((D.absolutelyContinuous hst).ae_le hadmissible.1) hfloor
  simp only [Exp.ofVal]
  iapply twp_afterWhole E source z
  twp_pure
  rw [decide_eq_false (not_lt.mpr hz)]
  twp_pure
  unfold Program.fractionBody
  twp_bind pl(&Occil.PSRN.subtract &source.fst (&Occil.PSRN.rational #int z #1))
  iapply tglWp_wand
  isplitl [Hstate]
  · iapply twp_subtractRational E source z 1 (by norm_num) (owns source) t $$ Hstate
  iintro %fraction Hstate
  simp only [Exp.ofVal]
  iapply twp_afterFraction E fraction z
  twp_bind pl(&Occil.expMinusRational #int z #1 #())
  isimp only [whole_expectation D t z G hG] at Hcredit
  iapply ((whole_spec E z hz).wp (fun b => ∫⁻ x, afterWhole D z G b x ∂D.posterior t)
    (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  cases b
  · isimp only [afterWhole, Bool.false_eq_true, ite_false] at Hcredit
    twp_pure
    twp_value
    imodintro
    isimp only [ViewOwns] at Hstate
    icases Hstate with ⟨_, Hstate⟩
    iapply LatentCoin.post_return D owns source s t false G hst
    iframe Hstate Hcredit
  · isimp only [afterWhole, ite_true, ← fractional_credit D t z G] at Hcredit
    twp_pure
    iapply tglWp_wand
    isplitl [Hstate Hcredit]
    · iapply (fractional_spec E D hD owns horacle source z).spec fraction t G hG
      iframe Hstate Hcredit
    iintro %result Hpost
    iapply fraction_post D owns source fraction result z s t hst G $$ Hpost

/-- Ownership includes the sufficient termination domain and retains it after every call. -/
def domainOwns (D : Model Ω S) (owns : Val ℝ → S → IProp GF)
    (source : Val ℝ) (s : S) : IProp GF := iprop(⌜Admissible D s⌝ ∗ owns source s)

omit [ProbLangDist ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
  [ProbLangDist.IsUniformReal ℝ] [ProbLangDist.IsUniformInt ℝ] in
private theorem domain_post (D : Model Ω S) (owns : Val ℝ → S → IProp GF)
    (source result : Val ℝ) (s : S) (hs : Admissible D s) (G : Bool → Ω → ℝ≥0∞) :
    LatentCoin.post D owns source s G result ⊢
      LatentCoin.post D (domainOwns D owns) source s G result := by
  iintro Hpost
  isimp only [LatentCoin.post] at Hpost
  icases Hpost with ⟨%b, %t, %ht, Hstate, Hcredit⟩
  isimp only [LatentCoin.post, domainOwns]
  iexists b, t
  iframe Hstate Hcredit
  ipureintro
  exact ⟨ht, hs.refines ht.2⟩

/-- A reusable conditional law on owned nonnegative sources whose floor read terminates. -/
theorem expMinusCoin_programSpec (E : CoPset) (D : Model Ω S) (hD : D.MeasurableError)
    (owns : Val ℝ → S → IProp GF) (horacle : IsOracleSpec E D owns) :
    IsLatentCoinProgramSpec E D (domainOwns D owns) (bias D)
      (fun source => pl(&Occil.PSRN.expMinusCoin &source.fst #())) where
  measurable_bias := measurable_bias D
  spec source s G hG := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [domainOwns] at Hstate
    icases Hstate with ⟨%hs, Hstate⟩
    iapply tglWp_wand
    isplitl [Hstate Hcredit]
    · iapply twp_expMinusCoin E D hD owns horacle source s hs G hG
      iframe Hstate Hcredit
    iintro %result Hpost
    iapply domain_post D owns source result s hs G $$ Hpost

/-- The same joint law is available through a unit callback. -/
theorem expMinusCoin_coinSpec (E : CoPset) (D : Model Ω S) (hD : D.MeasurableError)
    (owns : Val ℝ → S → IProp GF) (horacle : IsOracleSpec E D owns) :
    IsLatentCoinSpec E D (domainOwns D owns) (bias D) Program.callback where
  measurable_bias := measurable_bias D
  spec source s G hG := by
    iintro H
    twp_pure
    iapply (expMinusCoin_programSpec E D hD owns horacle).spec source s G hG $$ H

end specification

end

end SampLib.LatentReal.ExpMinusCoin
