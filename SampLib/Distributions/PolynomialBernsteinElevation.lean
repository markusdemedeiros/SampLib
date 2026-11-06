module

public import SampLib.Distributions.PolynomialBernstein
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! # Eventual admissibility of elevated Bernstein coefficients

Normalize each falling-product factor by the degree. As the degree grows, these
continuous functions converge to the coordinate function on `[0,1]`. Their finite
products therefore recover monomials uniformly. The compact-open neighborhood of
functions valued in `(0,1)` supplies the uniform probability margin.
-/

open Finset Filter Set
open scoped BigOperators unitInterval Topology

namespace SampLib.PolynomialBernstein

noncomputable section

/-- The coordinate on the compact unit interval. -/
def coordinate : C(I, ℝ) := ⟨fun x => (x : ℝ), continuous_subtype_val⟩

@[simp] theorem coordinate_apply (x : I) : coordinate x = (x : ℝ) := rfl

/-- One normalized falling-factorial factor. -/
def factor (n i : ℕ) : C(I, ℝ) :=
  (1 - (i : ℝ) / n)⁻¹ • (coordinate - ContinuousMap.const I ((i : ℝ) / n))

@[simp] theorem factor_apply (n i : ℕ) (x : I) :
    factor n i x = ((x : ℝ) - (i : ℝ) / n) / (1 - (i : ℝ) / n) := by
  simp [factor, coordinate, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- A normalized falling product representing `choose(k,j)/choose(n,j)` at grid points. -/
def basisCoefficient (n j : ℕ) : C(I, ℝ) := ∏ i ∈ range j, factor n i

private theorem tendsto_div_nat (i : ℕ) :
    Tendsto (fun n : ℕ => (i : ℝ) / n) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

private theorem tendsto_const_div_nat (i : ℕ) :
    Tendsto (fun n : ℕ => ContinuousMap.const I ((i : ℝ) / n)) atTop (𝓝 (0 : C(I, ℝ))) := by
  simpa [Function.comp_def] using
    ((ContinuousMap.continuous_const' (X := I) (Y := ℝ)).tendsto 0).comp (tendsto_div_nat i)

private theorem tendsto_factor (i : ℕ) :
    Tendsto (fun n => factor n i) atTop (𝓝 coordinate) := by
  have hd : Tendsto (fun n : ℕ => 1 - (i : ℝ) / n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_div_nat i)
  have hn : Tendsto (fun n : ℕ => coordinate - ContinuousMap.const I ((i : ℝ) / n))
      atTop (𝓝 coordinate) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_nat i)
  simpa [factor] using (hd.inv₀ one_ne_zero).smul hn

theorem tendsto_basisCoefficient (j : ℕ) :
    Tendsto (fun n => basisCoefficient n j) atTop (𝓝 (coordinate ^ j)) := by
  simpa [basisCoefficient] using tendsto_finsetProd (range j) (fun i _ => tendsto_factor i)

private theorem factor_at_grid (n i : ℕ) (k : Fin (n + 1)) (hn : 0 < n) :
    factor n i (bernstein.z k) = ((k : ℝ) - i) / ((n : ℝ) - i) := by
  rw [factor_apply]
  change (((k : ℝ) / n) - (i : ℝ) / n) / (1 - (i : ℝ) / n) = _
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [← sub_div, show 1 - (i : ℝ) / n = ((n : ℝ) - i) / n by
    rw [sub_div, div_self hn']]
  exact div_div_div_cancel_right₀ hn' _ _

/-- The normalized product gives the exact source ratio, including `k < j`. -/
theorem basisCoefficient_at_grid (n j : ℕ) (k : Fin (n + 1)) (hn : 0 < n) :
    basisCoefficient n j (bernstein.z k) =
      (Nat.choose (k : ℕ) j : ℝ) / (Nat.choose n j : ℝ) := by
  calc
    _ = ∏ i ∈ range j, ((k : ℝ) - i) / ((n : ℝ) - i) := by
      rw [basisCoefficient, ContinuousMap.prod_apply]
      apply prod_congr rfl
      intro i _
      exact factor_at_grid n i k hn
    _ = (descPochhammer ℝ j).eval (k : ℝ) / (descPochhammer ℝ j).eval (n : ℝ) := by
      rw [prod_div_distrib, ← descPochhammer_eval_eq_prod_range,
        ← descPochhammer_eval_eq_prod_range]
    _ = _ := by
      rw [Nat.cast_choose_eq_descPochhammer_div, Nat.cast_choose_eq_descPochhammer_div,
        div_div_div_cancel_right₀ (by positivity : (j.factorial : ℝ) ≠ 0)]

/-- The continuous input polynomial on the unit interval. -/
def valueMap (a : ℕ → ℝ) (d : ℕ) : C(I, ℝ) := ∑ j ∈ range (d + 1), a j • coordinate ^ j

@[simp] theorem valueMap_apply (a : ℕ → ℝ) (d : ℕ) (x : I) : valueMap a d x = value a d x := by
  simp [valueMap, value, smul_eq_mul]

/-- The continuous function whose rational grid values are the elevated coefficients. -/
def coefficientMap (a : ℕ → ℝ) (d n : ℕ) : C(I, ℝ) :=
  ∑ j ∈ range (d + 1), a j • basisCoefficient n j

theorem coefficientMap_at_grid (a : ℕ → ℝ) (d n : ℕ) (k : Fin (n + 1)) (hn : 0 < n) :
    coefficientMap a d n (bernstein.z k) = coefficient a d n k := by
  simp [coefficientMap, coefficient, basisCoefficient_at_grid n _ k hn, smul_eq_mul]

/-- Degree elevation converges to the input polynomial uniformly on the compact interval. -/
theorem tendsto_coefficientMap (a : ℕ → ℝ) (d : ℕ) :
    Tendsto (coefficientMap a d) atTop (𝓝 (valueMap a d)) := by
  change Tendsto (fun n => ∑ j ∈ range (d + 1), a j • basisCoefficient n j) atTop
    (𝓝 (∑ j ∈ range (d + 1), a j • coordinate ^ j))
  exact tendsto_finsetSum (range (d + 1))
    (fun j _ => tendsto_const_nhds.smul (tendsto_basisCoefficient j))

/-- A polynomial strictly between zero and one eventually has admissible coefficients. -/
theorem eventually_admissible_strict (a : ℕ → ℝ) (d : ℕ)
    (h : ∀ x : I, value a d x ∈ Ioo (0 : ℝ) 1) :
    ∀ᶠ n in atTop, ∀ k ≤ n, coefficient a d n k ∈ Ioo (0 : ℝ) 1 := by
  have hmaps : ∀ᶠ n in atTop, MapsTo (coefficientMap a d n) univ (Ioo (0 : ℝ) 1) :=
    (tendsto_coefficientMap a d).eventually
      (ContinuousMap.eventually_mapsTo isCompact_univ isOpen_Ioo
        (fun x _ => by simpa using h x))
  filter_upwards [hmaps, eventually_ge_atTop 1] with n hn hnpos
  intro k hk
  have hkn := hn (x := bernstein.z ⟨k, Nat.lt_succ_iff.mpr hk⟩) (mem_univ _)
  simpa only [coefficientMap_at_grid a d n _ (by omega : 0 < n)] using hkn

/-- The source's increasing-degree search reaches a finite successful degree. -/
theorem exists_admissible_degree (a : ℕ → ℝ) (d : ℕ)
    (h : ∀ x : I, value a d x ∈ Ioo (0 : ℝ) 1) :
    ∃ n, d ≤ n ∧ ∀ k ≤ n, coefficient a d n k ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨n, hn, hcoeff⟩ := ((eventually_ge_atTop d).and (eventually_admissible_strict a d h)).exists
  exact ⟨n, hn, fun k hk => ⟨(hcoeff k hk).1.le, (hcoeff k hk).2.le⟩⟩

end

end SampLib.PolynomialBernstein
