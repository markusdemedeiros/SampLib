import SampLib.Uniform.RationalCoin
import SampLib.PSRN.Laws.PSRNGammaFamilyDensities

/-! # Exact rational selectors for the named gamma-mixture families -/

namespace SampLib.PSRNGammaFamilies

noncomputable section

/-- The common positive rational rate. -/
def rate (n d : ℤ) : ℝ := (n : ℝ) / d

theorem rate_pos (n d : ℤ) (hn : 0 < n) (hd : 0 < d) : 0 < rate n d :=
  div_pos (by exact_mod_cast hn) (by exact_mod_cast hd)

def garimaBias (n d : ℤ) (hn : 0 < n) (hd : 0 < d) :=
  RationalCoin.bias (n + d) (n + 2 * d) (by omega) (by omega) (by omega)

def igarimaBias (n d : ℤ) (hn : 0 < n) (hd : 0 < d) :=
  RationalCoin.bias (n + 2 * d) (n + 3 * d) (by omega) (by omega) (by omega)

def baseBias (n d : ℤ) (hn : 0 < n) (hd : 0 < d) :=
  RationalCoin.bias n (n + d) hn.le (by omega) (by omega)

def mirraBias (n d an ad : ℤ) (hn : 0 < n) (hd : 0 < d)
    (han : 0 < an) (had : 0 < ad) :=
  RationalCoin.bias (n * n * ad) (an * d * d + n * n * ad) (by positivity)
    (by positivity) (le_add_of_nonneg_left (by positivity))

theorem garimaBias_eq (n d : ℤ) (hn : 0 < n) (hd : 0 < d) :
    garimaBias n d hn hd =
      PSRNGammaFamilyDensities.garimaWeight (rate n d) (rate_pos n d hn hd) := by
  apply Subtype.ext
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  dsimp [garimaBias, RationalCoin.bias, PSRNGammaFamilyDensities.garimaWeight, rate]
  push_cast
  field_simp

theorem igarimaBias_eq (n d : ℤ) (hn : 0 < n) (hd : 0 < d) :
    igarimaBias n d hn hd =
      PSRNGammaFamilyDensities.igarimaWeight (rate n d) (rate_pos n d hn hd) := by
  apply Subtype.ext
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  dsimp [igarimaBias, RationalCoin.bias, PSRNGammaFamilyDensities.igarimaWeight, rate]
  push_cast
  field_simp

theorem baseBias_eq (n d : ℤ) (hn : 0 < n) (hd : 0 < d) :
    baseBias n d hn hd = PSRNGammaMixtures.lindleyWeight (rate n d) (rate_pos n d hn hd) := by
  apply Subtype.ext
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  dsimp [baseBias, RationalCoin.bias, PSRNGammaMixtures.lindleyWeight, rate]
  push_cast
  field_simp

theorem mirraBias_eq (n d an ad : ℤ) (hn : 0 < n) (hd : 0 < d)
    (han : 0 < an) (had : 0 < ad) :
    mirraBias n d an ad hn hd han had =
      PSRNGammaFamilyDensities.mirraWeight (rate n d) ((an : ℝ) / ad)
        (rate_pos n d hn hd) (div_pos (by exact_mod_cast han) (by exact_mod_cast had)) := by
  apply Subtype.ext
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have han' : (0 : ℝ) < an := by exact_mod_cast han
  have had' : (0 : ℝ) < ad := by exact_mod_cast had
  dsimp [mirraBias, RationalCoin.bias, PSRNGammaFamilyDensities.mirraWeight, rate]
  push_cast
  field_simp

end

end SampLib.PSRNGammaFamilies
