import SampLib.PSRN.Support.LatentGammaIntegerModel
import SampLib.PSRN.Support.LatentRational
import SampLib.Distributions.GammaErlang

/-! # The integer part of a rational-shape gamma draw

Zero is an exact rational oracle. Positive integers use the verified recursive
integer-gamma model, with one independent exponential world for every summand.
-/

open MeasureTheory ProbabilityTheory

namespace SampLib.LatentGammaIntegerPart

noncomputable section

open LatentReal

abbrev World (Ω : Type) : ℕ → Type
  | 0 => Unit
  | n + 1 => LatentGammaInteger.World Ω n

instance worldMeasurableSpace (Ω : Type) [MeasurableSpace Ω] :
    (n : ℕ) → MeasurableSpace (World Ω n)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | n + 1 => LatentGammaInteger.worldMeasurableSpace Ω n

abbrev State (S : Type) : ℕ → Type
  | 0 => Unit
  | n + 1 => LatentGammaInteger.State S n

variable {Ω S : Type} [MeasurableSpace Ω]

def model (D : Model Ω S) : (n : ℕ) → Model (World Ω n) (State S n)
  | 0 => LatentRational.model 0 1
  | n + 1 => LatentGammaInteger.model D n

def initial (i : S) : (n : ℕ) → State S n
  | 0 => ()
  | n + 1 => LatentGammaInteger.initial i n

/-- The source's zero branch is Dirac zero, rather than a zero-shape gamma call. -/
theorem model_law (D : Model Ω S) (i : S) (rate : ℝ) (hrate : 0 < rate)
    (hD : D.law i = expMeasure rate) (n : ℕ) :
    (model D n).law (initial i n) = GammaErlang.law rate n := by
  cases n with
  | zero => simp [model, initial, GammaErlang.law]
  | succ n =>
    rw [model, initial, LatentGammaInteger.model_law D i rate hrate hD]
    rfl

end

end SampLib.LatentGammaIntegerPart
