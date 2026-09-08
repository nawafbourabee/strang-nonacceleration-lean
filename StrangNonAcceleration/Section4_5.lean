/-
The constants of Section 4.5 of

  N. Bou-Rabee, Provable non-acceleration of standard Strang splittings of kinetic
  Langevin dynamics, arXiv:2608.25279.

The cycle points `a, b, c` and the width `δ₀` of the piecewise quadratic potential, the
gradient identities (4.23) as the predicate `GradOK`, the Hessian bounds, and the tuning
`h⋆, β⋆, γ⋆` with its identities.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic

open Real

namespace OBABO
namespace Cycle

/-- The cycle points of Section 4.5 (Lessard, Recht and Packard). -/
noncomputable def a : ℝ := 2592 / 1225
noncomputable def b : ℝ := 792 / 1225
noncomputable def c : ℝ := -2208 / 1225
noncomputable def δ₀ : ℝ := 1 / 100

/-- The two affine pieces of (4.23) that Lemma 4.6 uses: `U'(x) = 25x` for `x ≤ 1 - δ₀` and
`U'(x) = 25x - 24` for `x ≥ 2 + δ₀`.  (The middle piece is not used.) -/
structure GradOK (g : ℝ → ℝ) : Prop where
  left : ∀ x, x ≤ 1 - δ₀ → g x = 25 * x
  right : ∀ x, 2 + δ₀ ≤ x → g x = 25 * x - 24

/-- `U'(a) = 25a - 24`, `U'(b) = 25b`, `U'(c) = 25c`. -/
theorem grad_values (g : ℝ → ℝ) (hg : GradOK g) :
    g a = 25 * a - 24 ∧ g b = 25 * b ∧ g c = 25 * c :=
  ⟨hg.right a (by norm_num [a, δ₀]), hg.left b (by norm_num [b, δ₀]),
    hg.left c (by norm_num [c, δ₀])⟩

/-- `1 ≤ U'' ≤ 25` for `U'' = 25 - 24 χ((x-1)/δ₀) + 24 χ((x-2)/δ₀)` with `χ` nondecreasing and
`[0,1]`-valued: the two arguments satisfy `(x-2)/δ₀ ≤ (x-1)/δ₀`. -/
theorem hessian_bounds (χ : ℝ → ℝ) (hmono : Monotone χ) (h0 : ∀ t, 0 ≤ χ t)
    (h1 : ∀ t, χ t ≤ 1) (x : ℝ) :
    1 ≤ 25 - 24 * χ ((x - 1) / δ₀) + 24 * χ ((x - 2) / δ₀) ∧
      25 - 24 * χ ((x - 1) / δ₀) + 24 * χ ((x - 2) / δ₀) ≤ 25 := by
  have hle : (x - 2) / δ₀ ≤ (x - 1) / δ₀ := by
    unfold δ₀; rw [div_le_div_iff_of_pos_right (by norm_num)]; linarith
  have := hmono hle
  have := h0 ((x - 2) / δ₀)
  have := h1 ((x - 1) / δ₀)
  constructor <;> linarith

/-- The tuning (1.15): `h⋆ = 2/√26`, `β⋆ = 4/9`, `γ⋆ = -(1/h⋆) log(4/9)`. -/
noncomputable def hstar : ℝ := 2 / √26
noncomputable def βstar : ℝ := 4 / 9
noncomputable def γstar : ℝ := -(1 / hstar) * Real.log (4 / 9)

theorem hstar_sq : hstar ^ 2 = 4 / 26 := by
  unfold hstar
  rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num

/-- `β⋆ = e^{-γ⋆ h⋆}`. -/
theorem βstar_eq_exp : Real.exp (-(γstar * hstar)) = βstar := by
  unfold γstar βstar
  have h : hstar ≠ 0 := by unfold hstar; positivity
  have : -(-(1 / hstar) * Real.log (4 / 9) * hstar) = Real.log (4 / 9) := by field_simp
  rw [this, Real.exp_log (by norm_num)]

/-- The heavy-ball parameters at (1.15): `s = h⋆^2 (1 + β⋆)/2 = 1/9`, `√β⋆ = 2/3`. -/
theorem s_star : hstar ^ 2 * (1 + βstar) / 2 = 1 / 9 := by
  rw [hstar_sq]; unfold βstar; norm_num

theorem sqrt_βstar : √βstar = 2 / 3 := by
  unfold βstar
  rw [show (4 : ℝ) / 9 = (2 / 3) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- `h⋆ < 2/5` (used for the invariant-law assertion, Theorem 4.5 with `λ_* = 25`). -/
theorem hstar_lt : hstar < 2 / 5 := by
  unfold hstar
  rw [div_lt_div_iff_of_pos_left (by norm_num) (by positivity) (by norm_num)]
  rw [Real.lt_sqrt (by norm_num)]; norm_num

end Cycle
end OBABO
