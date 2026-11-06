import SampLib.Bernoulli.Laws.VonNeumann
import SampLib.Uniform.RealCoin
import Samplers.Bernoulli.Basic
import Metrology.Iris.LocalBI

/-!
# Von Neumann's fair-coin extractor

Equal input flips retry; unequal flips return the first result. The CTE proof composes
an abstract coin specification and closes recursion by error amplification.
-/

open Set ProbLang
open scoped ENNReal

namespace SampLib.VonNeumann

open RealCoin (lintegral_law)

noncomputable section

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

private theorem bool_beq {rT : Type _} [BEq rT] (a b : Bool) :
    ((BaseLit.bool a : BaseLit rT) == .bool b) = (a == b) := rfl

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- CTE specification from an abstract input-coin spec, for `0 < p < 1`. -/
theorem twp_vonNeumann (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (credit F) -∗ tglWp E pl(&Occil.vonNeumann &coin.fst #())
      (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε (one_lt_terminationFactor p hp0 hp1) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  twp_pures
  twp_bind pl(&coin.fst #())
  icombine Hcredit Hterm as Hcredit
  isimp only [← lintegral_firstCredit p F ε] at Hcredit
  iapply (hcoin.wp (firstCredit p F ε) (measurable_of_countable _) _) $$ Hcredit
  iintro %a Hcredit
  twp_pures
  twp_bind pl(&coin.fst #())
  isimp only [firstCredit] at Hcredit
  iapply (hcoin.wp (pairCredit p F ε a) (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  twp_pures
  rw [bool_beq]
  by_cases hab : a = b
  · rw [beq_iff_eq.mpr hab]
    twp_pure
    isimp only [pairCredit, ite_eq_left hab] at Hcredit
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    twp_bind pl(&Occil.vonNeumann &coin.fst #())
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply IH $$ Hterm Hcredit
  · rw [beq_eq_false_iff_ne.mpr hab]
    twp_pures
    twp_value
    imodintro
    iexists a
    isimp only [pairCredit, ite_eq_right hab] at Hcredit
    iframe Hcredit
    itrivial

/-- Typed distribution specification for the fair output. -/
theorem vonNeumann_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.vonNeumann &coin.fst #()) law Val.bool where
  spec F _ := by
    simpa only [lintegral_law, credit] using
      wand_entails (twp_vonNeumann E p coin hp0 hp1 hcoin F)

end specification

end

end SampLib.VonNeumann
