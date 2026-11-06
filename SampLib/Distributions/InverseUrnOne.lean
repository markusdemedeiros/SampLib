import SampLib.Distributions.InverseUrnMass

/-! # One marked draw is exactly the first-marked waiting law -/

namespace SampLib.InverseUrn

noncomputable section

/-- The first-success component identifies the one-success inverse urn. -/
theorem law_one (a b c : ℕ) (ha : 0 < a) : law 1 a b c ha = UrnWaiting.law a b c := by
  simp [law]

end

end SampLib.InverseUrn
