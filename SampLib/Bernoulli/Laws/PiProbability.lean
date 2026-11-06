import SampLib.Bernoulli.Laws.PiBoundsState
import SampLib.Bernoulli.Laws.RealEnclosureTransforms

/-! # Probability enclosures obtained from the concrete Machin bounds -/

namespace SampLib.PiProbability

noncomputable section

/-- The full signed-offset probability domain of `piAffine`. -/
def affineBias (offset : ℤ) (divisor : ℕ) (hd : 0 < divisor)
    (hlo : 0 ≤ Real.pi - offset) (hhi : Real.pi - offset ≤ divisor) : unitInterval :=
  ⟨(Real.pi - offset) / divisor,
    div_nonneg hlo (by positivity),
    (div_le_one (by exact_mod_cast hd)).mpr hhi⟩

def affineInterval (offset : ℤ) (divisor : ℕ) (hd : 0 < divisor)
    (hlo : 0 ≤ Real.pi - offset) (hhi : Real.pi - offset ≤ divisor) (n : ℕ) :
    FromBounds.Interval (affineBias offset divisor hd hlo hhi) :=
  ((PiBounds.interval n).affine offset divisor hd).toProbability _ rfl

theorem affine_tight (offset : ℤ) (divisor : ℕ) (hd : 0 < divisor)
    (hlo : 0 ≤ Real.pi - offset) (hhi : Real.pi - offset ≤ divisor) :
    FromBounds.Tight (affineInterval offset divisor hd hlo hhi) :=
  (PiBounds.interval_tight.affine offset divisor hd).toProbability _ rfl

end

end SampLib.PiProbability
