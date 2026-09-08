/-
The deterministic and numerical content of Proposition 4.7 of

  N. Bou-Rabee, Provable non-acceleration of standard Strang splittings of kinetic
  Langevin dynamics, arXiv:2608.25279.

The origin tube, the disjointness of the tubes, the identities (4.26), (4.27), and the
constants in (4.28). The Gaussian tail bound and the union bound are not formalized.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import StrangNonAcceleration.Lemma4_6

open Real

namespace OBABO
namespace Cycle

/-- The same for the origin (used in the proof of Proposition 4.7): the perturbed recurrence
started at `(0, 0)` stays within `1/20` of `0`. -/
theorem lemma_4_6_origin (g : ℝ → ℝ) (hg : GradOK g) (x ε : ℕ → ℝ)
    (hx0 : x 0 = 0) (hx1 : x 1 = 0)
    (hxrec : ∀ k, x (k + 2) = 13 / 9 * x (k + 1) - 4 / 9 * x k - 1 / 9 * g (x (k + 1)) + ε (k + 2))
    (hε : ∀ k, |ε k| ≤ 1 / 180) :
    ∀ k, |x k| ≤ 1 / 20 := by
  have := lemma_4_6 g hg (fun _ => 0) x ε (fun _ => Or.inr (Or.inr (Or.inr rfl)))
    (fun k => by simp [hg.left 0 (by norm_num [δ₀])]) hx0 hx1 hxrec hε
  simpa using this

/-- The tubes are disjoint: `min{|a|, |b|, |c|} > 1/10`, so a point within `1/20` of a cycle
point and a point within `1/20` of the origin differ. -/
theorem tubes_disjoint (y y' z : ℝ) (hz : z = a ∨ z = b ∨ z = c)
    (hy : |y - z| ≤ 1 / 20) (hy' : |y'| ≤ 1 / 20) : y ≠ y' := by
  obtain ⟨h1, h2⟩ := abs_le.mp hy
  obtain ⟨h3, h4⟩ := abs_le.mp hy'
  rcases hz with hz | hz | hz <;> subst hz <;> norm_num [a, b, c] at h1 h2 ⊢ <;>
    intro h <;> linarith

/-- (4.26): `h⋆^2 (1 - β⋆^2) = 10/81`. -/
theorem eq_4_26 : hstar ^ 2 * (1 - βstar ^ 2) = 10 / 81 := by
  rw [hstar_sq]; unfold βstar; norm_num

/-- (4.27): the initial velocity `√β⋆ (R(a - c)/h⋆ - (h⋆/2) R (25a - 24)) = 360√26 R/637`. -/
theorem eq_4_27 (R : ℝ) :
    √βstar * (R * (a - c) / hstar - hstar / 2 * (R * (25 * a - 24))) = 360 * √26 / 637 * R := by
  rw [sqrt_βstar]
  unfold hstar a c
  have h26 : √26 ^ 2 = 26 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < √26 := by positivity
  field_simp
  rw [h26]; ring

/-- The Gaussian-tail exponent: `(R/180)^2 / (2 · 10/81) = R^2/8000`. -/
theorem tail_exponent (R : ℝ) : (R / 180) ^ 2 / (2 * (10 / 81)) = R ^ 2 / 8000 := by ring

/-- At `N_R = ⌊e^{R^2/8000}/16⌋`, the right-hand side of (4.28) is at least `3/4`. -/
theorem rhs_4_28 (R : ℝ) (n : ℕ) (hn : n ≤ ⌊Real.exp (R ^ 2 / 8000) / 16⌋₊) :
    3 / 4 ≤ 1 - 4 * n * Real.exp (-(R ^ 2 / 8000)) := by
  have hE : 0 < Real.exp (R ^ 2 / 8000) := Real.exp_pos _
  have h1 : (n : ℝ) ≤ Real.exp (R ^ 2 / 8000) / 16 := by
    calc (n : ℝ) ≤ (⌊Real.exp (R ^ 2 / 8000) / 16⌋₊ : ℝ) := by exact_mod_cast hn
      _ ≤ Real.exp (R ^ 2 / 8000) / 16 := Nat.floor_le (by positivity)
  rw [Real.exp_neg]
  have h2 : (n : ℝ) * (Real.exp (R ^ 2 / 8000))⁻¹ ≤ 1 / 16 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hE]; linarith
  linarith

/-- The window `0 ≤ n ≤ N_R` contains a positive time once `R ≥ √(8000 log 16) ≈ 148.9`:
numerically `148.9 < √(8000 log 16) < 149`. -/
theorem window_threshold : (148.9 : ℝ) < √(8000 * Real.log 16) ∧ √(8000 * Real.log 16) < 149 := by
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  have hlo := Real.log_two_gt_d9
  have hhi := Real.log_two_lt_d9
  constructor
  · rw [Real.lt_sqrt (by norm_num), h16]; nlinarith
  · rw [Real.sqrt_lt' (by norm_num), h16]; nlinarith

end Cycle
end OBABO
