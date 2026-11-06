import SampLib.Distributions.LatentReal.RepresentedReciprocal
import SampLib.Syntax.RepresentedReciprocal
import SampLib.LatentMeasuredError

/-! # The actual reciprocal observer over one represented latent world

The first separating interval determines both the inverse's representation and
its actual error width. A measurable finite selector supplies termination credit;
no uniform bound on a coarse inverse interval is required.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal.RepresentedReciprocal

noncomputable section

open ReciprocalSelection

variable {Ω S : Type} [MeasurableSpace Ω]

def model (D : Model Ω S) (R : Representation D) : Model Ω S :=
  { D with
    value := fun ω => 1 / D.value ω
    measurable_value := measurable_const.div D.measurable_value
    error := fun n ω => (interval R.interval n ω).width
    error_tendsto := fun s => (R.approximates s).mono fun ω hω =>
      (approximates R.interval ω hω).2 }

def representation (D : Model Ω S) (R : Representation D) : Representation (model D R) where
  interval := interval R.interval
  measurable_lower n := (measurable_fields R.interval R.measurable_lower
    R.measurable_upper R.measurable_denominator n).1
  measurable_upper n := (measurable_fields R.interval R.measurable_lower
    R.measurable_upper R.measurable_denominator n).2.1
  measurable_denominator n := (measurable_fields R.interval R.measurable_lower
    R.measurable_upper R.measurable_denominator n).2.2
  approximates s := (R.approximates s).mono fun ω hω => approximates R.interval ω hω

theorem sameWorld (D : Model Ω S) (R : Representation D) : D.SameWorld (model D R) :=
  ⟨fun _ => rfl, fun _ _ => Iff.rfl⟩

theorem measurableError (D : Model Ω S) (R : Representation D) :
    (model D R).MeasurableError :=
  measurable_width R.interval R.measurable_lower R.measurable_upper R.measurable_denominator

private theorem no_zero_endpoints (D : Model Ω S) {s : S} {n : ℕ} (I : RationalInterval)
    (hI : D.Encloses s n I) (hne : ∀ᵐ ω ∂D.posterior s, D.value ω ≠ 0) :
    ¬ (I.lower = 0 ∧ I.upper = 0) := by
  obtain ⟨ω, hω, hne⟩ := (hI.and hne).exists
  exact not_zero_endpoints I hω.1 hne

private theorem observed_return (D : Model Ω S) (R : Representation D)
    {s : S} {start current : ℕ} (hstart : start ≤ current) (I : RationalInterval)
    (hbound : ∀ᵐ ω ∂D.posterior s, current ≤ precision R.interval start ω)
    (hobs : R.Observed s current I) (hsep : separated I) :
    (representation D R).Observed s start (I.reciprocal hsep) := by
  change ∀ᵐ ω ∂D.posterior s,
    I.reciprocal hsep = interval R.interval start ω
  filter_upwards [hbound, hobs] with ω hb ho
  have hmin := precision_min R.interval start ω hstart (ho ▸ hsep)
  have heq := le_antisymm hmin hb
  have hi : I = R.interval (precision R.interval start ω) ω := by
    rw [heq]
    exact ho
  cases hi
  simp only [interval, dite_eq_left hsep]

private theorem output_encloses (D : Model Ω S) (R : Representation D)
    {s : S} {n : ℕ} {I : RationalInterval} (hobs : (representation D R).Observed s n I) :
    (model D R).Encloses s n I := by
  filter_upwards [hobs, (representation D R).approximates s] with ω ho ha
  rw [ho]
  exact ⟨ha.1 n, le_rfl⟩

private theorem next_bound (D : Model Ω S) (R : Representation D)
    {s : S} {start current : ℕ} (I : RationalInterval)
    (hbound : ∀ᵐ ω ∂D.posterior s, current ≤ precision R.interval start ω)
    (hobs : R.Observed s current I) (hnot : ¬ separated I)
    (hne : ∀ᵐ ω ∂D.posterior s, D.value ω ≠ 0) :
    ∀ᵐ ω ∂D.posterior s, current + 1 ≤ precision R.interval start ω := by
  filter_upwards [hbound, hobs, R.approximates s, hne] with ω hb ho ha hn
  exact next_le_precision R.interval start current ω hb (ho ▸ hnot)
    (precision_separated_of_approximates R.interval start ω ha hn)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

def post (D : Model Ω S) (R : Representation D) (owns : Val rT → S → IProp GF)
    (source : Val rT) (initial : S) (n : ℕ) (F : Ω → ℝ≥0∞) (result : Val rT) : IProp GF :=
  iprop(∃ (t : S) (I : RationalInterval),
    ⌜result = intervalVal I ∧ D.refines initial t ∧
      (model D R).Encloses t n I ∧ (representation D R).Observed t n I⌝ ∗
    owns source t ∗ ↯ (∫⁻ ω, F ω ∂D.posterior t))

private theorem twp_round (E : CoPset) (D : Model Ω S) (R : Representation D)
    (O : Val rT → S → IProp GF) (horacle : IsRepresentedOracleSpec E D R O)
    (source : Val rT) (initial s : S) (hs : D.refines initial s)
    (hne : ∀ᵐ ω ∂D.posterior initial, D.value ω ≠ 0)
    (start N current : ℕ) (hstart : start ≤ current)
    (hbound : ∀ᵐ ω ∂D.posterior s, current ≤ precision R.interval start ω)
    (F : Ω → ℝ≥0∞) (hF : Measurable F)
    (hcontinue : ∀ t, D.refines s t →
      (∀ᵐ ω ∂D.posterior t, current + 1 ≤ precision R.interval start ω) →
      iprop(O source t ∗ ↯ (∫⁻ ω, horizonCredit R.interval start N F ω ∂D.posterior t)) ⊢
        tglWp E pl(&(Program.loop source) #int ((current + 1 : ℕ) : ℤ))
          (post D R O source initial start F)) :
    iprop(O source s ∗ ↯ (∫⁻ ω, horizonCredit R.interval start N F ω ∂D.posterior s)) ⊢
      tglWp E pl(&(Program.loop source) #int (current : ℤ))
        (post D R O source initial start F) := by
  iintro ⟨Hstate, Hcredit⟩
  iterate 2 twp_pure
  twp_bind pl(&source.fst #int (current : ℤ))
  iapply horacle.wp source s current (horizonCredit R.interval start N F)
    (measurable_horizonCredit R.interval R.measurable_lower R.measurable_upper start N F hF)
    _ $$ Hstate Hcredit
  iintro %t %I %hI Hstate Hcredit
  have hst := D.refines_trans hs hI.1
  have hne_t := (D.absolutelyContinuous hst).ae_le hne
  have hb_t := (D.absolutelyContinuous hI.1).ae_le hbound
  have hzero := no_zero_endpoints D I hI.2.1 hne_t
  iterate 12 twp_pure
  rw [Program.zero_guard_false (rT := rT) I hzero]
  twp_pure
  iterate 3 twp_pure
  by_cases hsep : separated I
  · rw [Program.straddle_false I hsep]
    twp_pures
    twp_value
    imodintro
    have hobs := observed_return D R hstart I hb_t hI.2.2 hsep
    ihave Hcredit := ErrorCredit.weaken
      (output_credit_le (D.posterior t) R.interval start N F) $$ Hcredit
    isimp only [post]
    iexists t, I.reciprocal hsep
    iframe Hstate Hcredit
    ipureintro
    exact ⟨rfl, hst, output_encloses D R hobs, hobs⟩
  · rw [Program.straddle_true I hsep]
    iterate 2 twp_pure
    rw [← Nat.cast_add_one]
    twp_bind pl(&(Program.loop source) #int ((current + 1 : ℕ) : ℤ))
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply hcontinue t hI.1 (next_bound D R I hb_t hI.2.2 hsep hne_t)
    iframe Hstate Hcredit

private theorem twp_until (E : CoPset) (D : Model Ω S) (R : Representation D)
    (O : Val rT → S → IProp GF) (horacle : IsRepresentedOracleSpec E D R O)
    (source : Val rT) (initial s : S) (hs : D.refines initial s)
    (hne : ∀ᵐ ω ∂D.posterior initial, D.value ω ≠ 0)
    (start N current : ℕ) (hcurrent : current ≤ N) (hstart : start ≤ current)
    (hbound : ∀ᵐ ω ∂D.posterior s, current ≤ precision R.interval start ω)
    (F : Ω → ℝ≥0∞) (hF : Measurable F) :
    iprop(O source s ∗ ↯ (∫⁻ ω, horizonCredit R.interval start N F ω ∂D.posterior s)) ⊢
      tglWp E pl(&(Program.loop source) #int (current : ℤ))
        (post D R O source initial start F) := by
  have hall : ∀ current ≤ N, ∀ s, D.refines initial s → start ≤ current →
      (∀ᵐ ω ∂D.posterior s, current ≤ precision R.interval start ω) →
      iprop(O source s ∗ ↯ (∫⁻ ω, horizonCredit R.interval start N F ω ∂D.posterior s)) ⊢
        tglWp E pl(&(Program.loop source) #int (current : ℤ))
          (post D R O source initial start F) := by
    intro current hcurrent
    apply Nat.decreasingInduction (motive := fun current _ => ∀ s,
      D.refines initial s → start ≤ current →
      (∀ᵐ ω ∂D.posterior s, current ≤ precision R.interval start ω) →
      iprop(O source s ∗ ↯ (∫⁻ ω, horizonCredit R.interval start N F ω ∂D.posterior s)) ⊢
        tglWp E pl(&(Program.loop source) #int (current : ℤ))
          (post D R O source initial start F)) ?_ ?_ hcurrent
    · intro current hcurrent IH s hs hstart hbound
      iapply twp_round E D R O horacle source initial s hs hne start N current hstart hbound
        F hF (fun t hst hb => IH t (D.refines_trans hs hst)
          (hstart.trans (Nat.le_succ _)) hb)
    · intro s hs hstart hbound
      iapply twp_round E D R O horacle source initial s hs hne start N N hstart hbound F hF ?_
      intro t hst hb
      iintro ⟨Hstate, Hcredit⟩
      iexfalso
      iapply ErrorCredit.contradict
        (unresolved_credit (D.posterior t) R.interval start N F
          (hb.mono fun _ h => Nat.lt_of_lt_of_le (Nat.lt_succ_self N) h)) $$ Hcredit
  exact hall current hcurrent s hs hstart hbound

/-- Reading the actual reciprocal returns the first separating represented interval. -/
theorem twp_observe (E : CoPset) (D : Model Ω S) (R : Representation D)
    (O : Val rT → S → IProp GF) (horacle : IsRepresentedOracleSpec E D R O)
    (source : Val rT) (s : S) (hne : ∀ᵐ ω ∂D.posterior s, D.value ω ≠ 0)
    (n : ℕ) (F : Ω → ℝ≥0∞) (hF : Measurable F) :
    iprop(O source s ∗ ↯ (∫⁻ ω, F ω ∂D.posterior s)) ⊢
      tglWp E pl(&(Program.value source).fst #int (n : ℤ)) (post D R O source s n F) := by
  iintro ⟨Hstate, Hcredit⟩
  iapply Program.twp_open E source n _
  iapply twp_err_pos solve_not_value
  iintro %δ %hδ Hterm
  obtain ⟨N, hN, hcost⟩ := exists_credit_horizon (D.posterior s) R.interval
    R.measurable_lower R.measurable_upper n F hF hδ
  icombine Hcredit Hterm as Htotal
  ihave Hcredit := ErrorCredit.weaken hcost $$ Htotal
  iapply twp_until E D R O horacle source s s (D.refines_refl s) hne n N n hN le_rfl
    (Filter.Eventually.of_forall (precision_ge R.interval n)) F hF
  iframe Hstate Hcredit

/-- One physical source and state-local nonzero metadata back every reciprocal alias. -/
def owns (D : Model Ω S) (O : Val rT → S → IProp GF) (v : Val rT) (s : S) : IProp GF :=
  iprop(∃ source : Val rT,
    ⌜v = Program.value source ∧ ∀ᵐ ω ∂D.posterior s, D.value ω ≠ 0⌝ ∗ O source s)

/-- Constructing the actual closure retains the whole original world and its credit. -/
theorem twp_reciprocal (E : CoPset) (D : Model Ω S) (R : Representation D)
    (O : Val rT → S → IProp GF) (source : Val rT) (s : S)
    (hne : ∀ᵐ ω ∂D.posterior s, D.value ω ≠ 0) (F : Ω → ℝ≥0∞) :
    iprop(O source s ∗ ↯ (∫⁻ ω, F ω ∂D.posterior s)) ⊢
      tglWp E pl(&Occil.PSRN.reciprocal &source.fst)
        (fun result : Val rT => iprop(owns D O result s ∗
          ↯ (∫⁻ ω, F ω ∂(model D R).posterior s))) := by
  iintro ⟨Hstate, Hcredit⟩
  iapply Program.twp_constructor E source _
  isplitl [Hstate]
  · isimp only [owns]
    iexists source
    iframe Hstate
    ipureintro
    exact ⟨rfl, hne⟩
  isimp only [model]
  iframe Hcredit

/-- The source protocol certifies the actual adaptive reciprocal observer, without independence. -/
theorem oracleSpec (E : CoPset) (D : Model Ω S) (R : Representation D)
    (O : Val rT → S → IProp GF) (horacle : IsRepresentedOracleSpec E D R O) :
    IsRepresentedOracleSpec E (model D R) (representation D R) (owns D O) where
  observe v s n F hF := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [owns] at Hstate
    icases Hstate with ⟨%source, %hv, Hstate⟩
    rcases hv with ⟨rfl, hne⟩
    isimp only [model] at Hcredit
    iapply tglWp_wand
    isplitl [Hstate Hcredit]
    · iapply twp_observe E D R O horacle source s hne n F hF
      iframe Hstate Hcredit
    iintro %result Hpost
    isimp only [post] at Hpost
    icases Hpost with ⟨%t, %I, %hI, Hstate, Hcredit⟩
    iexists t, I
    isplit
    · ipureintro
      exact hI
    isplitl [Hstate]
    · isimp only [owns]
      iexists source
      iframe Hstate
      ipureintro
      exact ⟨rfl, (D.absolutelyContinuous hI.2.1).ae_le hne⟩
    isimp only [model]
    iframe Hcredit

end specification

end

end SampLib.LatentReal.RepresentedReciprocal
