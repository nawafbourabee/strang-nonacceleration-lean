/-
Lemma 3.2 of

  N. Bou-Rabee, Provable non-acceleration of standard Strang splittings of kinetic
  Langevin dynamics, arXiv:2608.25279.

The case `m = 3` and the elementary steps (3.15) to (3.18) of the case `m >= 4`. The parts of
the proof that invoke [22, Lemma B.2, Lemma B.7] are not formalized.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic

open Real

namespace OBABO

theorem sqrt5_bounds : (2.236 : ℝ) < √5 ∧ √5 < 2.2361 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- Lemma 3.2, case `m = 3`: `u^2 - 3u + 1 > 0` for `u < (3 - √5)/2`
(the smaller root of the quadratic). -/
theorem lemma_3_2_m3 (u : ℝ) (hu : u < (3 - √5) / 2) : 0 < u ^ 2 - 3 * u + 1 := by
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < √5 := by positivity
  have h1 : 0 < (3 - √5) / 2 - u := by linarith
  have h2 : 0 < (3 + √5) / 2 - u := by linarith
  nlinarith [mul_pos h1 h2]

/-- The hypothesis chain of Lemma 3.2 for `m = 3`: `u < ((3-√5)/4)^2` implies
`u < (3-√5)/2`, hence `u^2 - 3u + 1 > 0`. -/
theorem lemma_3_2_m3' (u : ℝ) (hu : u < ((3 - √5) / 4) ^ 2) :
    0 < u ^ 2 - 3 * u + 1 := by
  apply lemma_3_2_m3
  obtain ⟨h1, h2⟩ := sqrt5_bounds
  have : ((3 - √5) / 4) ^ 2 < (3 - √5) / 2 := by nlinarith
  linarith

/-- The polynomial identity in the proof of Lemma 3.2 (`c = cos θ_{m+1}`, `d = cos θ_m`). -/
theorem lemma_3_2_identity (β u c d : ℝ) :
    (1 + β * u) ^ 2 * (c - d) + (1 - β * u) ^ 2 * (c + d)
      = 2 * (1 + β ^ 2 * u ^ 2) * c - 4 * β * u * d := by ring

/-- The elementary bound `1/(1+t) ≤ 1 - t + t^2` for `t ≥ 0` used in the proof of Lemma 3.2. -/
theorem one_div_one_add_le (t : ℝ) (ht : 0 ≤ t) : 1 / (1 + t) ≤ 1 - t + t ^ 2 := by
  rw [div_le_iff₀ (by linarith)]
  nlinarith [pow_nonneg ht 3]

/-- `cos(2π/5) = (√5 - 1)/4`, hence `1/cos θ_5 + 2 = 3 + √5 = √C_GTD`
(the value appearing at the end of the proof of Lemma 3.2). -/
theorem cos_two_pi_div_five : Real.cos (2 * π / 5) = (√5 - 1) / 4 := by
  have h : 2 * π / 5 = 2 * (π / 5) := by ring
  rw [h, Real.cos_two_mul, Real.cos_pi_div_five]
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith

theorem inv_cos_two_pi_div_five_add_two : 1 / Real.cos (2 * π / 5) + 2 = 3 + √5 := by
  rw [cos_two_pi_div_five]
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < √5 - 1 := by have := sqrt5_bounds.1; linarith
  field_simp
  nlinarith

end OBABO
