import SampLib.Bernoulli.Laws.LatentPower

/-! # A power factory retaining an owned shared exponent oracle

A positive base bias gives a uniform termination factor. The exponent callback
retains its posterior on every call; no unconditional independence is assumed.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentPower

noncomputable section

open TwoCoinPower.Program

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private def property (E : CoPset) (p : unitInterval) (φ : ℝ → unitInterval)
    (base exponent : Val rT) (l : Loc) : IProp GF := iprop(
  ∀ (n : ℕ) (q : List Bool) (G : Bool → ℝ → ℝ≥0∞), ⌜∀ b, Measurable (G b)⌝ -∗
    UniformBag.owns l q -∗ ↯ (DyadicPosterior.credit q (credit p φ G n)) -∗
      tglWp E pl(&(loop base exponent) #int ((n : ℤ) + 1)) (UniformBag.coinPost l q G))

private theorem gate_spec (E : CoPset) (n : ℕ) :
    IsDistSpec (GF := GF) E pl(&Occil.rationalCoin #1 #int ((n : ℤ) + 1))
      (RealCoin.law (FractionalPower.hazardBias 1 n)) Val.bool := by
  have hb : RationalCoin.bias 1 ((n : ℤ) + 1) (by positivity) (by positivity) (by omega) =
      FractionalPower.hazardBias 1 n := by
    apply Subtype.ext
    simp [RationalCoin.bias, FractionalPower.hazardBias]
  simpa only [hb] using RationalCoin.rationalCoin_distSpec (GF := GF) E 1 ((n : ℤ) + 1)
    (by positivity) (by positivity) (by omega)

private theorem twp_property (E : CoPset) (p : unitInterval) (hp : 0 < (p : ℝ))
    (φ : ℝ → unitInterval) (base exponent : Val rT) (l : Loc)
    (hbase : IsDistSpec (GF := GF) E pl(&base.fst #()) (RealCoin.law p) Val.bool)
    (hexponent : UniformBag.IsCoinSpec (GF := GF) E l pl(&exponent.fst #()) φ)
    (ε : ℝ≥0∞) (hε : 0 < ε) : iprop(↯ ε) ⊢ property E p φ base exponent l := by
  iintro Hterm
  iapply ErrorCredit.Induction.simple (k := Geometric.terminationFactor p) hε
    (terminationFactor_gt_one p hp) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩
  isimp only [property]
  iintro %n %q %G %hG Hbag Hcredit
  twp_pures
  isimp only [RationalCoin.rationalCoin_openRec, RationalCoin.rationalCoin_closeRec]
  twp_bind pl(&base.fst #())
  icombine Hcredit Hterm as Htotal
  isimp only [← expectation p hexponent.measurable_bias q hG n ε] at Htotal
  iapply (hbase.wp (baseBudget p φ q G n ε) (measurable_of_countable _) _) $$ Htotal
  iintro %bit Hcredit
  cases bit
  · isimp only [baseBudget, Bool.false_eq_true, ite_false, input_false] at Hcredit
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    twp_pure
    twp_bind pl(&exponent.fst #())
    iapply (hexponent.wp q (exponentKernel p φ G n)
      (measurable_exponentKernel p hexponent.measurable_bias hG n) _) $$ Hbag Hcredit
    iintro %select %q' %hprefix Hbag Hcredit
    cases select
    · isimp only [exponent_false] at Hcredit
      twp_pure
      twp_pure
      rw [← Nat.cast_add_one]
      ieval (
        change _ ⊢ tglWp E pl(&(loop base exponent) #int (((n + 1 : ℕ) : ℤ) + 1))
          (UniformBag.coinPost l q G))
      iapply tglWp_wand
      isplitl [IH Hterm Hbag Hcredit]
      · ihave Hnext := IH $$ Hterm
        isimp only [property] at Hnext
        iapply Hnext $$ %(n + 1) %q' %G %hG Hbag Hcredit
      iintro %v Hpost
      iapply UniformBag.coinPost_weaken l q q' G v hprefix $$ Hpost
    · twp_pure
      twp_bind pl(&Occil.rationalCoin #1 #int ((n : ℤ) + 1))
      isimp only [← gate_expectation p hexponent.measurable_bias q' hG n] at Hcredit
      iapply ((gate_spec E n).wp (fun b => DyadicPosterior.credit q' (gateKernel p φ G n b))
        (measurable_of_countable _) _) $$ Hcredit
      iintro %gate Hcredit
      cases gate
      · isimp only [gate_false] at Hcredit
        twp_pure
        twp_pure
        rw [← Nat.cast_add_one]
        ieval (
          change _ ⊢ tglWp E pl(&(loop base exponent) #int (((n + 1 : ℕ) : ℤ) + 1))
            (UniformBag.coinPost l q G))
        iapply tglWp_wand
        isplitl [IH Hterm Hbag Hcredit]
        · ihave Hnext := IH $$ Hterm
          isimp only [property] at Hnext
          iapply Hnext $$ %(n + 1) %q' %G %hG Hbag Hcredit
        iintro %v Hpost
        iapply UniformBag.coinPost_weaken l q q' G v hprefix $$ Hpost
      · isimp only [gate_true] at Hcredit
        twp_pures
        twp_value
        imodintro
        iapply UniformBag.coinPost_return l q q' false G hprefix
        iframe Hbag Hcredit
  · isimp only [baseBudget, ite_true, input_true] at Hcredit
    ihave ⟨Hcredit, _⟩ := ErrorCredit.split $$ Hcredit
    twp_pures
    twp_value
    imodintro
    iapply UniformBag.coinPost_return l q q true G (List.prefix_refl _)
    iframe Hbag Hcredit

/-- The repeated exponent calls retain the same owned latent probability. -/
theorem twp_loop (E : CoPset) (p : unitInterval) (hp : 0 < (p : ℝ))
    (φ : ℝ → unitInterval) (base exponent : Val rT) (l : Loc)
    (hbase : IsDistSpec (GF := GF) E pl(&base.fst #()) (RealCoin.law p) Val.bool)
    (hexponent : UniformBag.IsCoinSpec (GF := GF) E l pl(&exponent.fst #()) φ)
    (q : List Bool) (G : Bool → ℝ → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) :
    iprop(UniformBag.owns l q ∗ ↯ (DyadicPosterior.credit q (credit p φ G 0))) ⊢
      tglWp E pl(&(loop base exponent) #1) (UniformBag.coinPost l q G) := by
  iintro ⟨Hbag, Hcredit⟩
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  ihave Hnext := twp_property E p hp φ base exponent l hbase hexponent ε hε $$ Hterm
  isimp only [property] at Hnext
  ihave Hloop := Hnext $$ %0 %q %G %hG Hbag Hcredit
  isimp only [Nat.cast_zero, zero_add] at Hloop
  iexact Hloop

/-- Conditional power law, compositional with further observations of the same bag. -/
theorem twoCoinPower_coinSpec (E : CoPset) (p : unitInterval) (hp : 0 < (p : ℝ))
    (φ : ℝ → unitInterval) (base exponent : Val rT) (l : Loc)
    (hbase : IsDistSpec (GF := GF) E pl(&base.fst #()) (RealCoin.law p) Val.bool)
    (hexponent : UniformBag.IsCoinSpec (GF := GF) E l pl(&exponent.fst #()) φ) :
    UniformBag.IsCoinSpec (GF := GF) E l
      pl(&Occil.FactoryExtra.twoCoinPower &base.fst &exponent.fst #())
      (fun u => FractionalPower.powerBias p (φ u)) where
  measurable_bias := measurable_powerBias p hexponent.measurable_bias
  spec q G hG := by
    iintro ⟨Hbag, Hcredit⟩
    rw [← source_fst (rT := rT)]
    iterate 4 twp_pure
    isimp only [RationalCoin.rationalCoin_openRec]
    ieval (change _ ⊢ tglWp E pl(&(loop base exponent) #1) _)
    isimp only [← credit_zero p hp φ q G] at Hcredit
    iapply twp_loop E p hp φ base exponent l hbase hexponent q G hG
    iframe Hbag Hcredit

end specification

end

end SampLib.LatentPower
