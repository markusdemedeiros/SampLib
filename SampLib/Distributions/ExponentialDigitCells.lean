import SampLib.Distributions.ExponentialDigits
import SampLib.Distributions.LatentReal.DigitValue

/-! # Canonical binary cells for the fractional exponential law

Canonical binary digits represent every point of `[0,1)`. Finite prefix events
agree with their half-open dyadic cells up to endpoint null sets, so the interval
calculation applies directly to the memoized digit posterior.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SampLib.ExponentialDigits

noncomputable section

/-- Canonical binary digits, with the terminating expansion at dyadic rationals. -/
def digits (x : ℝ) (n : ℕ) : Bool := decide (⌊x * 2 ^ (n + 1)⌋₊ % 2 = 1)

theorem measurable_digits (n : ℕ) : Measurable (fun x => digits x n) := by
  exact (measurable_of_countable (fun k : ℕ => decide (k % 2 = 1))).comp
    (Nat.measurable_floor.comp (by fun_prop : Measurable (fun x : ℝ => x * 2 ^ (n + 1))))

private theorem binary_digits (x : ℝ) (n : ℕ) :
    DigitPosterior.binary (digits x n) = Real.digits x 2 n := by
  apply Fin.ext
  have hbound := Nat.mod_lt ⌊x * 2 ^ (n + 1)⌋₊ (by decide : 0 < 2)
  unfold DigitPosterior.binary digits Real.digits
  simp only [Fin.val_ofNat]
  split_ifs <;> simp_all

/-- Canonical digits retain the original fractional real, including dyadic endpoints. -/
theorem value_digits {x : ℝ} (hx : x ∈ Ico 0 1) : DigitPosterior.value (digits x) = x := by
  unfold DigitPosterior.value
  simp_rw [binary_digits]
  exact Real.ofDigits_digits (by decide : 1 < 2) hx

theorem rank_bounds (p : List Bool) :
    0 ≤ UniformBag.rank p ∧ UniformBag.rank p < (2 : ℤ) ^ p.length := by
  induction p with
  | nil => simp [UniformBag.rank]
  | cons b p IH =>
    cases b <;> simp only [UniformBag.rank, Bool.false_eq_true, ite_false, ite_true,
      zero_mul, one_mul, zero_add, List.length_cons, pow_succ] <;> omega

private theorem rank_injective (p q : List Bool) (hlen : p.length = q.length)
    (hrank : UniformBag.rank p = UniformBag.rank q) : p = q := by
  induction p generalizing q with
  | nil => simpa using hlen.symm
  | cons b p IH =>
    cases q with
    | nil => simp at hlen
    | cons c q =>
      have hlen' : p.length = q.length := by simpa using hlen
      have hp := rank_bounds p
      have hq := rank_bounds q
      rw [← hlen'] at hq
      simp only [UniformBag.rank, ← hlen'] at hrank
      cases b <;> cases c <;> simp only [Bool.false_eq_true, ite_false, ite_true,
        zero_mul, one_mul, zero_add] at hrank
      · exact congrArg (List.cons false) (IH q hlen' hrank)
      · omega
      · omega
      · exact congrArg (List.cons true) (IH q hlen' (by omega))

private theorem prefix_mem {Ω : Type} (d : Ω → ℕ → Bool) (x : Ω) (n : ℕ) :
    x ∈ DigitPosterior.cylinder d (List.ofFn (fun i : Fin n => d x i)) := by
  induction n generalizing d with
  | zero => simp
  | succ n IH =>
    rw [List.ofFn_succ]
    exact ⟨rfl, IH (fun x n => d x (n + 1))⟩

/-- A strict interior point identifies its prefix independently of binary endpoint ambiguity. -/
private theorem cylinder_of_interior {Ω : Type} (d : Ω → ℕ → Bool) (x : Ω) (p : List Bool)
    (hlo : (UniformBag.rank p : ℝ) / 2 ^ p.length < DigitPosterior.value (d x))
    (hhi : DigitPosterior.value (d x) < ((UniformBag.rank p : ℝ) + 1) / 2 ^ p.length) :
    x ∈ DigitPosterior.cylinder d p := by
  let q := List.ofFn (fun i : Fin p.length => d x i)
  have hq : x ∈ DigitPosterior.cylinder d q := prefix_mem d x p.length
  have hbounds := DigitPosterior.value_mem_interval d q hq
  have hlen : q.length = p.length := List.length_ofFn
  rw [hlen] at hbounds
  have hD : (0 : ℝ) < 2 ^ p.length := by positivity
  have hqlo := (div_le_iff₀ hD).mp hbounds.1
  have hqhi := (le_div_iff₀ hD).mp hbounds.2
  have hplo := (div_lt_iff₀ hD).mp hlo
  have hphi := (lt_div_iff₀ hD).mp hhi
  have hrank : UniformBag.rank q = UniformBag.rank p := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h : UniformBag.rank q + 1 ≤ UniformBag.rank p := by omega
      have h' : (UniformBag.rank q : ℝ) + 1 ≤ UniformBag.rank p := by exact_mod_cast h
      linarith
    · have h : UniformBag.rank p + 1 ≤ UniformBag.rank q := by omega
      have h' : (UniformBag.rank p : ℝ) + 1 ≤ UniformBag.rank q := by exact_mod_cast h
      linarith
  rwa [rank_injective q p hlen hrank] at hq

theorem fraction_support (rate : ℝ) :
    ∀ᵐ x ∂fraction rate, x ∈ Ico (0 : ℝ) 1 := by
  have hAC : fraction rate ≪ volume.restrict (Ico (0 : ℝ) 1) := by
    unfold fraction
    rw [restrict_withDensity measurableSet_Ico]
    exact (withDensity_absolutelyContinuous _ _).smul_left _
  exact hAC.ae_le (ae_restrict_mem measurableSet_Ico)

/-- A canonical prefix event is its dyadic cell, modulo two endpoint null sets. -/
theorem cylinder_ae_cell (rate : ℝ) (p : List Bool) :
    DigitPosterior.cylinder digits p =ᵐ[fraction rate]
      Ico ((UniformBag.rank p : ℝ) / 2 ^ p.length)
        (((UniformBag.rank p : ℝ) + 1) / 2 ^ p.length) := by
  filter_upwards [fraction_support rate,
    (fraction rate).ae_ne ((UniformBag.rank p : ℝ) / 2 ^ p.length),
    (fraction rate).ae_ne (((UniformBag.rank p : ℝ) + 1) / 2 ^ p.length)] with x hx hlo hhi
  apply propext
  constructor
  · intro hc
    have hbounds := DigitPosterior.value_mem_interval digits p hc
    rw [value_digits hx] at hbounds
    exact ⟨hbounds.1, lt_of_le_of_ne hbounds.2 hhi⟩
  · intro hcell
    apply cylinder_of_interior digits x p
    · rw [value_digits hx]
      exact lt_of_le_of_ne hcell.1 (Ne.symm hlo)
    · rw [value_digits hx]
      exact hcell.2

end

end SampLib.ExponentialDigits
