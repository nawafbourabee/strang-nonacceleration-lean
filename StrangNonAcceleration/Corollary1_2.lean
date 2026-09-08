/-
The constants in the proof of Corollary 1.2(i) of

  N. Bou-Rabee, Provable non-acceleration of standard Strang splittings of kinetic
  Langevin dynamics, arXiv:2608.25279.

The elementary inequalities `log((1+x)/(1-x)) <= 3x`, `log(1/q_kappa) <= 3 C_star/kappa`, and the
choice of the integer `n_star` in the proof of Corollary 1.2(i). Everything else in
Corollary 1.2 (the constants `c_1`, `c_2`, `c` and part (ii)) is not formalized.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic

open Real

namespace OBABO

/-- `log((1+x)/(1-x)) ≤ 3x` for `0 ≤ x ≤ 1/2`. -/
theorem log_ratio_le (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    Real.log ((1 + x) / (1 - x)) ≤ 3 * x := by
  have h1 : 0 < 1 - x := by linarith
  rw [Real.log_div (by linarith) h1.ne']
  have ha : Real.log (1 + x) ≤ x := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + x); linarith
  have hb : -Real.log (1 - x) ≤ x / (1 - x) := by
    have := Real.log_le_sub_one_of_pos (inv_pos.mpr h1)
    rw [Real.log_inv] at this
    have : (1 - x)⁻¹ - 1 = x / (1 - x) := by field_simp; ring
    linarith
  have hc : x / (1 - x) ≤ 2 * x := by rw [div_le_iff₀ h1]; nlinarith
  linarith

/-- `log(1/q_κ) ≤ 3 C⋆/κ` for `κ ≥ 2 C⋆ > 0`, where `q_κ = (1 - C⋆/κ)/(1 + C⋆/κ)`. -/
theorem log_inv_q_le (C κ : ℝ) (hC : 0 < C) (hκ : 2 * C ≤ κ) :
    Real.log (1 / ((1 - C / κ) / (1 + C / κ))) ≤ 3 * C / κ := by
  have hκ0 : 0 < κ := by linarith
  have hx0 : 0 ≤ C / κ := by positivity
  have hx : C / κ ≤ 1 / 2 := by rw [div_le_iff₀ hκ0]; linarith
  rw [one_div_div]
  have := log_ratio_le (C / κ) hx0 hx
  calc Real.log ((1 + C / κ) / (1 - C / κ)) ≤ 3 * (C / κ) := this
    _ = 3 * C / κ := by ring

/-- The time `n_* = ⌊log(c/(4ε)) / log(1/q)⌋` satisfies `c q^{n_*}/2 ≥ 2ε`
(for `0 < q < 1`, `ε > 0`, `c ≥ 4ε`). -/
theorem nstar_property (q c ε : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (hε : 0 < ε) (hc : 4 * ε ≤ c) :
    2 * ε ≤ c * q ^ ⌊Real.log (c / (4 * ε)) / Real.log (1 / q)⌋₊ / 2 := by
  set L := Real.log (c / (4 * ε)) with hL
  set M := Real.log (1 / q) with hM
  have hc0 : 0 < c := by linarith
  have hL0 : 0 ≤ L := by
    rw [hL]; apply Real.log_nonneg; rw [le_div_iff₀ (by positivity)]; linarith
  have hM0 : 0 < M := by
    rw [hM]; apply Real.log_pos; rw [lt_div_iff₀ hq0]; linarith
  set n := ⌊L / M⌋₊ with hn
  have hfloor : (n : ℝ) ≤ L / M := Nat.floor_le (div_nonneg hL0 hM0.le)
  have hnM : (n : ℝ) * M ≤ L := by rwa [le_div_iff₀ hM0] at hfloor
  have hqn : 4 * ε / c ≤ q ^ n := by
    rw [← Real.log_le_log_iff (by positivity) (pow_pos hq0 n), Real.log_pow]
    have h1 : Real.log (4 * ε / c) = -L := by
      rw [hL, ← Real.log_inv, inv_div]
    have h2 : Real.log q = -M := by
      rw [hM, one_div, Real.log_inv, neg_neg]
    rw [h1, h2]; linarith
  have : 4 * ε ≤ c * q ^ n := by rw [div_le_iff₀ hc0] at hqn; linarith
  linarith

/-- Lower bound on `n_*`: `n_* ≥ (κ/(3C⋆)) log(c/(4ε)) - 1` when `log(1/q) ≤ 3C⋆/κ`
and `log(c/(4ε)) ≥ 0`. -/
theorem nstar_lower (C κ q c ε : ℝ) (hC : 0 < C) (hκ : 0 < κ) (hq : 0 < Real.log (1 / q))
    (hqκ : Real.log (1 / q) ≤ 3 * C / κ) (hL : 0 ≤ Real.log (c / (4 * ε))) :
    κ / (3 * C) * Real.log (c / (4 * ε)) - 1 ≤ ⌊Real.log (c / (4 * ε)) / Real.log (1 / q)⌋₊ := by
  set L := Real.log (c / (4 * ε))
  set M := Real.log (1 / q)
  have h1 : L / M < ⌊L / M⌋₊ + 1 := Nat.lt_floor_add_one _
  have h2 : L / (3 * C / κ) ≤ L / M := div_le_div_of_nonneg_left hL hq hqκ
  have h3 : L / (3 * C / κ) = κ / (3 * C) * L := by field_simp
  linarith

end OBABO
