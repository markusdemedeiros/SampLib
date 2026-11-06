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

theorem affine_encode {rT : Type} (offset : ℤ) (divisor : ℕ) (hd : 0 < divisor)
    (hlo : 0 ≤ Real.pi - offset) (hhi : Real.pi - offset ≤ divisor) (n : ℕ) :
    FromBounds.encodeInterval (rT := rT) (affineInterval offset divisor hd hlo hhi n) =
      RealEnclosure.encodeTriple
        ((PiBounds.piRaw n).1 - offset * (PiBounds.piRaw n).2.2,
          ((PiBounds.piRaw n).2.1 - offset * (PiBounds.piRaw n).2.2,
            (divisor : ℤ) * (PiBounds.piRaw n).2.2)) := by
  simp [affineInterval, FromBounds.encodeInterval, RealEnclosure.encodeTriple,
    RealEnclosure.Interval.toProbability,
    RealEnclosure.Interval.affine, PiBounds.interval,
    Int.toNat_of_nonneg (PiBounds.piRaw_den_pos n).le]

end

end SampLib.PiProbability
