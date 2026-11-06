import SampLib.Latent.LatentDigits
import SampLib.PSRN.Support.LatentRepresentedSpec

/-! # Exact interval representations of conditional digit streams

The latent world fixes every finite prefix, even for dependent or atomic digits.
Unlike floor-based canonical digits, this representation retains both binary
expansions of a dyadic endpoint, including the all-ones stream representing one.
-/

open ProbLang
open scoped ENNReal Topology

namespace SampLib.LatentDigits

noncomputable section

section mathematics

open MeasureTheory

variable {Ω : Type}

/-- The first `n` digits of the actual stream in one latent world. -/
def streamPrefix (digits : Ω → ℕ → Bool) (n : ℕ) (x : Ω) : List Bool :=
  List.ofFn (fun i : Fin n => digits x i)

@[simp] theorem streamPrefix_length (digits : Ω → ℕ → Bool) (n : ℕ) (x : Ω) :
    (streamPrefix digits n x).length = n := List.length_ofFn

@[simp] theorem take_streamPrefix (digits : Ω → ℕ → Bool) (n : ℕ) (x : Ω) :
    (streamPrefix digits n x).take n = streamPrefix digits n x :=
  List.take_of_length_le (by simp)

theorem prefix_mem (digits : Ω → ℕ → Bool) (n : ℕ) (x : Ω) :
    x ∈ DigitPosterior.cylinder digits (streamPrefix digits n x) := by
  induction n generalizing digits with
  | zero => simp [streamPrefix]
  | succ n ih =>
    rw [streamPrefix, List.ofFn_succ]
    exact ⟨rfl, ih (fun x n => digits x (n + 1))⟩

/-- A cylinder identifies its complete finite prefix pointwise. -/
theorem prefix_eq {digits : Ω → ℕ → Bool} {p : List Bool} {x : Ω}
    (hx : x ∈ DigitPosterior.cylinder digits p) : streamPrefix digits p.length x = p := by
  induction p generalizing digits with
  | nil => simp [streamPrefix]
  | cons b p ih =>
    rw [streamPrefix, List.ofFn_succ]
    exact congrArg₂ List.cons hx.1 (ih hx.2)

/-- The actual closed dyadic interval of the stream, retaining endpoint atoms. -/
def representedInterval (digits : Ω → ℕ → Bool) (n : ℕ) (x : Ω) :
    LatentReal.RationalInterval := LatentUniform.interval (streamPrefix digits n x) n

theorem representedInterval_width (digits : Ω → ℕ → Bool) (n : ℕ) (x : Ω) :
    (representedInterval digits n x).width = (2 ^ n : ℝ)⁻¹ := by
  simp only [representedInterval, LatentUniform.interval, LatentReal.RationalInterval.width,
    LatentReal.RationalInterval.lowerReal, LatentReal.RationalInterval.upperReal,
    Int.cast_add, Int.cast_one, Int.cast_pow, Int.cast_ofNat]
  rw [add_div, add_sub_cancel_left, one_div]

variable [MeasurableSpace Ω]

theorem measurable_rank_prefix (digits : Ω → ℕ → Bool)
    (hd : ∀ n, Measurable (fun x => digits x n)) (n : ℕ) :
    Measurable (fun x => UniformBag.rank (streamPrefix digits n x)) := by
  exact (measurable_of_countable (fun f : Fin n → Bool => UniformBag.rank (List.ofFn f))).comp
    (Measurable.of_eval fun i : Fin n => hd i)

variable (μ : Measure Ω) [IsProbabilityMeasure μ] (digits : Ω → ℕ → Bool)
  (hd : ∀ n, Measurable (fun x => digits x n))

/-- Each observable interval is a measurable function of the same whole latent world. -/
def representation : LatentReal.Representation (model μ digits hd) where
  interval := representedInterval digits
  measurable_lower n := by
    simpa only [representedInterval, LatentUniform.interval, take_streamPrefix] using
      measurable_rank_prefix digits hd n
  measurable_upper n := by
    simpa only [representedInterval, LatentUniform.interval, take_streamPrefix] using
      (measurable_rank_prefix digits hd n).add_const 1
  measurable_denominator _ := measurable_const
  approximates _ := Filter.Eventually.of_forall fun x => ⟨fun n => by
    have h := DigitPosterior.value_mem_interval digits (streamPrefix digits n x)
      (prefix_mem digits n x)
    simpa [LatentReal.RationalInterval.Contains, LatentReal.RationalInterval.lowerReal,
      LatentReal.RationalInterval.upperReal, representedInterval, LatentUniform.interval,
      take_streamPrefix, streamPrefix_length, model] using h, by
    simp only [representedInterval_width]
    exact tendsto_inv_atTop_zero.comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))⟩

/-- Cached longer prefixes identify every shorter returned interval as well. -/
theorem interval_observed {p q : State μ digits} {n : ℕ}
    (hread : UniformBag.readRefines p.val n q.val) :
    (representation μ digits hd).Observed q n (LatentUniform.interval q.val n) := by
  have hn : n ≤ q.val.length := by rw [hread.2]; exact le_max_right _ _
  filter_upwards [DigitPosterior.ae_mem μ hd q.val] with x hx
  have hprefix := prefix_eq (DigitPosterior.cylinder_mono (List.take_prefix n q.val) hx)
  simp only [List.length_take, Nat.min_eq_left hn] at hprefix
  change LatentUniform.interval q.val n = representedInterval digits n x
  simp only [representedInterval, hprefix, LatentUniform.interval, List.take_take, min_self]

end mathematics

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open MeasureTheory (Measure IsProbabilityMeasure)

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- Strengthen the original observer using its exact returned streamPrefix. -/
theorem representedOracleSpec (E : CoPset) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (digits : Ω → ℕ → Bool) (hd : ∀ n, Measurable (fun x => digits x n))
    (nextBit : Val rT) (hnext : IsNextDigitSpec (GF := GF) E μ digits hd nextBit) :
    LatentReal.IsRepresentedOracleSpec (GF := GF) E (model μ digits hd)
      (representation μ digits hd) (owns μ digits nextBit) where
  observe v p n F _ := by
    iintro Hstate
    isimp only [model] at Hstate
    iapply tglWp_wand
    isplitl [Hstate]
    · iapply twp_observe E μ digits hd nextBit hnext v p n F $$ Hstate
    iintro %result ⟨%q, %hq, Hstate, Hcredit⟩
    rcases hq with ⟨hread, rfl⟩
    iexists q, LatentUniform.interval q.val n
    rw [show (model μ digits hd).posterior q = DigitPosterior.law μ digits q.val from rfl]
    iframe Hstate Hcredit
    ipureintro
    exact ⟨rfl, hread.1, interval_encloses μ digits hd hread,
      interval_observed μ digits hd hread⟩

/-- The unchanged constructor retains its exact representation through every future read. -/
theorem newByDigits_representedDistSpec (E : CoPset) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (digits : Ω → ℕ → Bool) (hd : ∀ n, Measurable (fun x => digits x n))
    (nextBit : Val rT) (hnext : IsNextDigitSpec (GF := GF) E μ digits hd nextBit) :
    LatentReal.IsRepresentedDistSpec (GF := GF) E pl(&Occil.PSRN.newByDigits &nextBit.fst #())
      (model μ digits hd) (representation μ digits hd) (initial μ digits)
      (owns μ digits nextBit) where
  spec := (newByDigits_latentDistSpec E μ digits hd nextBit hnext).spec
  oracle := representedOracleSpec E μ digits hd nextBit hnext

end specification

end

end SampLib.LatentDigits
