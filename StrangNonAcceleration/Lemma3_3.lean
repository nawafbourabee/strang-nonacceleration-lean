/-
Lemma 3.3 of

  N. Bou-Rabee, Provable non-acceleration of standard Strang splittings of kinetic
  Langevin dynamics, arXiv:2608.25279.

The smallness of `u = 1/kappa`, the algebra and numerics of Step 1 (namespace `OBABO`), Step 2
and Step 3 for `m-bar = 3` (namespace `OBABO.Section3`), and the direct proof of
`s_+(beta, 3) >= 2(1+beta)/kappa`. The level-set bound (3.20) and the steps that invoke
[22, Corollary 2.3, Lemmas 2.4, B.8, B.9] are not formalized; where needed they enter as
hypotheses.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import StrangNonAcceleration.Theorem3_1
import StrangNonAcceleration.Lemma3_2

open Real

namespace OBABO

theorem C_GTD_gt_27 : (27 : ℝ) < (3 + √5) ^ 2 := by
  have := sqrt5_bounds.1; nlinarith

/-- The smallness of `u = 1/κ` used at the start of the proof of Lemma 3.3:
`u ≤ 1/(2 C⋆)` with `C⋆ > (3+√5)^2` gives `u < ((3-√5)/4)^2` and `u < 1/16`. -/
theorem u_small (C u : ℝ) (hC : (3 + √5) ^ 2 < C) (hu0 : 0 < u) (hu : u ≤ 1 / (2 * C)) :
    u < ((3 - √5) / 4) ^ 2 ∧ u < 1 / 16 := by
  obtain ⟨h1, h2⟩ := sqrt5_bounds
  have hC' : (27.4 : ℝ) < C := by nlinarith
  have hu' : u < 1 / 54 := by
    calc u ≤ 1 / (2 * C) := hu
      _ < 1 / 54 := by
        rw [div_lt_div_iff_of_pos_left (by norm_num) (by linarith) (by norm_num)]; linarith
  constructor
  · have : (0.19 : ℝ) < (3 - √5) / 4 := by linarith
    nlinarith
  · linarith

/-- Monotonicity of `t ↦ (1 - t)/(1 + t)`: used for `q_κ < g` (Step 1) and for
`q_κ < (1 - (50/3)u)/(1 + (50/3)u)` (Step 2) in the proof of Lemma 3.3. -/
theorem frac_anti (x y : ℝ) (hy : -1 < y) (hxy : y < x) :
    (1 - x) / (1 + x) < (1 - y) / (1 + y) := by
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- The exact identity `(g - q_κ)/(1 - g q_κ) = (C⋆ - 1)/(C⋆ + 1)` of Step 1, where
`g = (1-u)/(1+u)` and `q_κ = (1 - C⋆ u)/(1 + C⋆ u)`. -/
theorem frac_identity (C u : ℝ) (hu : 0 < u) (hC : 0 < C) (hCu : C * u < 1) :
    let g := (1 - u) / (1 + u)
    let q := (1 - C * u) / (1 + C * u)
    (g - q) / (1 - g * q) = (C - 1) / (C + 1) := by
  intro g q
  have hCu0 : 0 < C * u := mul_pos hC hu
  have h1 : (1 + u) ≠ 0 := by positivity
  have h2 : (1 + C * u) ≠ 0 := by positivity
  have h3 : (C + 1) ≠ 0 := by positivity
  have hgq : 1 - g * q ≠ 0 := by
    have : g * q < 1 := by
      have hg : g < 1 := by
        rw [div_lt_one (by linarith)]; linarith
      have hq : q < 1 := by
        rw [div_lt_one (by linarith)]; nlinarith
      have hq0 : 0 ≤ q := by
        apply div_nonneg <;> linarith
      nlinarith [mul_nonneg hq0 (sub_nonneg.2 hg.le)]
    linarith
  rw [div_eq_div_iff hgq h3]
  simp only [g, q]
  field_simp
  ring

/-- The level-set function `ell(t) = t(g - t)/(1 - g t)` of Step 1. -/
noncomputable def ell (g t : ℝ) : ℝ := t * (g - t) / (1 - g * t)

/-- `ell(q_κ) = q_κ (C⋆ - 1)/(C⋆ + 1)`. -/
theorem ell_q (C u : ℝ) (hu : 0 < u) (hC : 0 < C) (hCu : C * u < 1) :
    ell ((1 - u) / (1 + u)) ((1 - C * u) / (1 + C * u))
      = (1 - C * u) / (1 + C * u) * ((C - 1) / (C + 1)) := by
  have := frac_identity C u hu hC hCu
  simp only at this
  unfold ell
  rw [mul_div_assoc, this]

/-- Step 1 numerics: if `C⋆ u ≤ 1/2` and `C⋆ > 27` then `q_κ ≥ 1/3`,
`(C⋆-1)/(C⋆+1) > 13/14`, hence `ell(q_κ) > 13/42 > 1/5`. -/
theorem step1_numerics (C u : ℝ) (hu : 0 < u) (hC : 27 < C) (hCu : C * u ≤ 1 / 2) :
    1 / 3 ≤ (1 - C * u) / (1 + C * u) ∧ 13 / 14 < (C - 1) / (C + 1) ∧
      13 / 42 < ell ((1 - u) / (1 + u)) ((1 - C * u) / (1 + C * u)) := by
  have hq : 1 / 3 ≤ (1 - C * u) / (1 + C * u) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hr : 13 / 14 < (C - 1) / (C + 1) := by
    rw [lt_div_iff₀ (by linarith)]; linarith
  refine ⟨hq, hr, ?_⟩
  rw [ell_q C u hu (by linarith) (by linarith)]
  calc (13 : ℝ) / 42 = 1 / 3 * (13 / 14) := by norm_num
    _ < (1 - C * u) / (1 + C * u) * ((C - 1) / (C + 1)) := by
      apply mul_lt_mul' hq hr (by norm_num) (by linarith)

/-- Strict decrease of `ell` on `[ρ_*, g]`, where `ρ_* = (1-√u)/(1+√u)` and `g = (1-u)/(1+u)`
(the paper argues via `ell'(t) = (g - 2t + g t^2)/(1 - g t)^2`, whose numerator has the roots
`ρ_*` and `1/ρ_*`; here the same fact is proved by direct algebra). -/
theorem ell_strictAnti (u t₁ t₂ : ℝ) (hu0 : 0 < u) (hu1 : u < 1)
    (h1 : (1 - √u) / (1 + √u) ≤ t₁) (h12 : t₁ < t₂) (h2 : t₂ < (1 - u) / (1 + u)) :
    ell ((1 - u) / (1 + u)) t₂ < ell ((1 - u) / (1 + u)) t₁ := by
  set v := √u with hv
  have hv0 : 0 < v := Real.sqrt_pos.mpr hu0
  have hv2 : v ^ 2 = u := Real.sq_sqrt hu0.le
  have hv1 : v < 1 := by nlinarith
  set g := (1 - u) / (1 + u) with hg
  set r := (1 - v) / (1 + v) with hr
  have hg0 : 0 < g := by rw [hg]; apply div_pos <;> linarith
  have hg1 : g < 1 := by rw [hg, div_lt_one (by linarith)]; linarith
  have hr0 : 0 < r := by rw [hr]; apply div_pos <;> linarith
  have hrg : r < g := by
    rw [hr, hg, div_lt_div_iff₀ (by linarith) (by linarith)]
    rw [← hv2]; nlinarith
  -- φ(r, r) = 0
  have hφrr : g - 2 * r + g * r ^ 2 = 0 := by
    rw [hg, hr, ← hv2]
    field_simp
    ring
  have ht1 : 0 < t₁ := lt_of_lt_of_le hr0 h1
  have hgt1 : g * t₁ < 1 := by nlinarith
  have hgt2 : g * t₂ < 1 := by nlinarith
  have hgr : g * r < 1 := by nlinarith
  -- φ(t₁, t₂) < 0
  have hφ : g - t₁ - t₂ + g * t₁ * t₂ < 0 := by
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_pos.2 hgt2).le,
      mul_pos (sub_pos.2 (lt_of_le_of_lt h1 h12)) (sub_pos.2 hgr)]
  unfold ell
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_pos (sub_pos.2 h12) (neg_pos.2 hφ)]

/-- `cos θ_3 = cos(2π/3) = -1/2`. -/
theorem cos_two_pi_div_three : Real.cos (2 * π / 3) = -1 / 2 := by
  have h : 2 * π / 3 = π - π / 3 := by ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]; norm_num

/-- `P_m` as a monic quadratic in `s`: `P_m = s^2 - 2 A_m s + B_m'` with
`A_m = β - cos θ_m + u(1 - β cos θ_m)` and `B_m' = 2u(1 - cos θ_m)(1 + β^2 - 2β cos θ_m)`,
`u = κ⁻¹` (the notation of Lemma 3.2). -/
theorem Pcyc_eq (s β κ c : ℝ) :
    Pcyc s β κ c = s ^ 2 - 2 * (β - c + κ⁻¹ * (1 - β * c)) * s
      + 2 * κ⁻¹ * (1 - c) * (1 + β ^ 2 - 2 * β * c) := rfl

/-- If a monic quadratic `s^2 - 2 A s + B` is nonpositive at `s₀`, then its discriminant is
nonnegative and `s₀ ≤ A + √(A^2 - B)` (the larger root). -/
theorem le_larger_root (A B s₀ : ℝ) (h : s₀ ^ 2 - 2 * A * s₀ + B ≤ 0) :
    B ≤ A ^ 2 ∧ s₀ ≤ A + √(A ^ 2 - B) := by
  have hsq : (s₀ - A) ^ 2 ≤ A ^ 2 - B := by nlinarith
  refine ⟨by nlinarith [sq_nonneg (s₀ - A)], ?_⟩
  have := Real.le_sqrt_of_sq_le hsq
  linarith

/-- Value of `P_3` at the numerical-stability edge `s = 2(1+β)u`:
`P_3(2(1+β)u, β; 1/u) = u (2β(1+β)u - β^2 - 3β + 1)`. -/
theorem P3_at_edge (β u : ℝ) :
    Pcyc (2 * (1 + β) * u) β u⁻¹ (-1 / 2) = u * (2 * β * (1 + β) * u - β ^ 2 - 3 * β + 1) := by
  unfold Pcyc
  rw [inv_inv]
  ring

/-- For `β ≥ 13/42` and `0 < u ≤ 1/54`, the value above is nonpositive. -/
theorem P3_at_edge_nonpos (β u : ℝ) (hβ : 13 / 42 ≤ β) (hu0 : 0 < u)
    (hu : u ≤ 1 / 54) :
    Pcyc (2 * (1 + β) * u) β u⁻¹ (-1 / 2) ≤ 0 := by
  rw [P3_at_edge β u]
  apply mul_nonpos_of_nonneg_of_nonpos hu0.le
  nlinarith [mul_nonneg (sub_nonneg.2 hβ) (sub_nonneg.2 hu),
    mul_nonneg (sub_nonneg.2 hu) (mul_nonneg (by linarith : (0:ℝ) ≤ β)
    (by linarith : (0:ℝ) ≤ 1 + β))]

/-- Step 3 of Lemma 3.3, case `m̄ = 3`: `s₊(β, 3) ≥ 2(1+β)/κ`, with `s₊ = A_3 + √(A_3^2 - B_3')`,
valid for `β ≥ 13/42` and `κ ≥ 54`.
The paper's argument is: for `cos θ₃ = -1/2` the roots of `P₃(·, β; κ)` are real by (3.24)
(`β ≥ β₋(3)`) and sum to `2β + 1 + u(2 + β) > 1`, so `s₊ > 1/2 > 4u ≥ 2(1+β)u` when
`u = 1/κ < 1/16` and `β < 1`; that argument is formalized as
`OBABO.Section3.lemma33_step3_m3`. The proof below is different: it shows `P₃ ≤ 0` at the
stability edge `s = 2(1+β)u` (`P3_at_edge_nonpos`), so the edge lies below the larger root
(`le_larger_root`), which also yields the real-roots condition `B_3' ≤ A_3^2` instead of
assuming it. -/
theorem s_plus_3_ge (β κ : ℝ) (hβ : 13 / 42 ≤ β) (hκ : 54 ≤ κ) :
    let c := Real.cos (2 * π / 3)
    let A := β - c + κ⁻¹ * (1 - β * c)
    let B := 2 * κ⁻¹ * (1 - c) * (1 + β ^ 2 - 2 * β * c)
    B ≤ A ^ 2 ∧ 2 * (1 + β) / κ ≤ A + √(A ^ 2 - B) := by
  intro c A B
  have hκ0 : 0 < κ := by linarith
  have hu0 : 0 < κ⁻¹ := inv_pos.mpr hκ0
  have hu : κ⁻¹ ≤ 1 / 54 := by rw [inv_le_comm₀ hκ0 (by norm_num)]; simpa using hκ
  have hc : c = -1 / 2 := cos_two_pi_div_three
  have hP := P3_at_edge_nonpos β κ⁻¹ hβ hu0 hu
  rw [inv_inv, Pcyc_eq] at hP
  have h2 : 2 * (1 + β) / κ = 2 * (1 + β) * κ⁻¹ := by ring
  rw [h2]
  apply le_larger_root
  simp only [A, B, hc]
  linarith

end OBABO

namespace OBABO.Section3

section Lemma33

/-- **Step 2 of Lemma 3.3.** Let `0 < u < 1/16`, `0 < ρ < (1 - (50/3)u)/(1 + (50/3)u)`, and
`β ≤ ρ²` (the level-set consequence (3.20); the paper also assumes `β ≥ 0`, which is not
needed). Then `(1 - ρ)(ρ - β)/ρ > (50/3) u (1 - β)`.
Proof as in the paper: the function `b ↦ (1-ρ)(ρ-b)/ρ - (50/3)u(1-b)` on `[0, ρ²]` has
derivative `(50/3)u - (1-ρ)/ρ < 0`, since `ρ < (1-(50/3)u)/(1+(50/3)u) < 1/(1+(50/3)u)`,
and its value at `b = ρ²` equals
`(1-ρ)(1+(50/3)u)((1-(50/3)u)/(1+(50/3)u) - ρ) > 0`. -/
theorem lemma33_step2 (u ρ β : ℝ) (hu0 : 0 < u) (hu : u < 1 / 16) (hρ0 : 0 < ρ)
    (hρ : ρ < (1 - 50 / 3 * u) / (1 + 50 / 3 * u)) (hβ : β ≤ ρ ^ 2) :
    50 / 3 * u * (1 - β) < (1 - ρ) * (ρ - β) / ρ := by
  have hden : 0 < 1 + 50 / 3 * u := by positivity
  have hρ' : ρ * (1 + 50 / 3 * u) < 1 - 50 / 3 * u := by rwa [lt_div_iff₀ hden] at hρ
  -- the slope `(1-ρ)/ρ - (50/3)u` is positive (multiplied by `ρ`)
  have hslope : 0 < (1 - ρ) - 50 / 3 * u * ρ := by nlinarith
  have h1 : 0 < 1 - ρ := by nlinarith
  -- the value at `b = ρ²` (multiplied by `ρ`) is positive
  have h2 : 0 < (1 - ρ) - 50 / 3 * u * (1 + ρ) := by nlinarith
  have hval : 0 < (1 - ρ) * (ρ - ρ ^ 2) - 50 / 3 * u * ρ * (1 - ρ ^ 2) := by
    have e : (1 - ρ) * (ρ - ρ ^ 2) - 50 / 3 * u * ρ * (1 - ρ ^ 2)
        = ρ * (1 - ρ) * ((1 - ρ) - 50 / 3 * u * (1 + ρ)) := by ring
    rw [e]; positivity
  -- `ρ f(β) = ρ f(ρ²) + (ρ² - β) (slope · ρ)`
  have hid : (1 - ρ) * (ρ - β) - 50 / 3 * u * ρ * (1 - β)
      = ((1 - ρ) * (ρ - ρ ^ 2) - 50 / 3 * u * ρ * (1 - ρ ^ 2))
        + (ρ ^ 2 - β) * ((1 - ρ) - 50 / 3 * u * ρ) := by ring
  have hprod : 0 ≤ (ρ ^ 2 - β) * ((1 - ρ) - 50 / 3 * u * ρ) :=
    mul_nonneg (sub_nonneg.2 hβ) hslope.le
  have key : 0 < (1 - ρ) * (ρ - β) - 50 / 3 * u * ρ * (1 - β) := by rw [hid]; linarith
  rw [lt_div_iff₀ hρ0]
  linarith

/-- **(3.21).** Combined with the level-set consequence `s ≥ (1-ρ)(1-β/ρ)` of
[22, Lemma 2.4], which enters as the hypothesis `hs`, Step 2 gives the strict lower bound
`s > (50/3) u (1 - β)`. -/
theorem lemma33_step2_s_lower (u ρ β s : ℝ) (hu0 : 0 < u) (hu : u < 1 / 16) (hρ0 : 0 < ρ)
    (hρ : ρ < (1 - 50 / 3 * u) / (1 + 50 / 3 * u)) (hβ : β ≤ ρ ^ 2)
    (hs : (1 - ρ) * (1 - β / ρ) ≤ s) :
    50 / 3 * u * (1 - β) < s := by
  have e : (1 - ρ) * (1 - β / ρ) = (1 - ρ) * (ρ - β) / ρ := by
    field_simp
  have := lemma33_step2 u ρ β hu0 hu hρ0 hρ hβ
  linarith

/-- **Step 3 of Lemma 3.3, the case `m̄ = 3`, by the argument of the paper.** For
`cos θ₃ = -1/2` the roots of `P₃(·, β; κ)` sum to `2A₃ = 2β + 1 + u(2 + β) > 1`, so the larger
root `s₊(β, 3) = A₃ + √(A₃² - B₃')` satisfies `s₊ > 1/2 > 4u ≥ 2(1+β)u = 2(1+β)/κ` when
`u = 1/κ < 1/16` and `0 ≤ β ≤ 1`. The expression `A₃ + √(A₃² - B₃')` is the larger root
`s₊(β, 3)` when the roots are real, that is `β ≥ β₋(3)`, which is (3.24) in the paper; the
inequalities below hold for the expression without that hypothesis, since `√` is
nonnegative. (The theorem `s_plus_3_ge` in this file proves the non-strict bound by a
different route, from `P₃ ≤ 0` at the stability edge.) -/
theorem lemma33_step3_m3 (β κ : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hκ : 16 < κ) :
    2 * (1 + β) / κ < 1 / 2 ∧
    1 / 2 < (β - Real.cos (2 * π / 3) + κ⁻¹ * (1 - β * Real.cos (2 * π / 3)))
      + √((β - Real.cos (2 * π / 3) + κ⁻¹ * (1 - β * Real.cos (2 * π / 3))) ^ 2
          - 2 * κ⁻¹ * (1 - Real.cos (2 * π / 3))
            * (1 + β ^ 2 - 2 * β * Real.cos (2 * π / 3))) := by
  have hc : Real.cos (2 * π / 3) = -1 / 2 := OBABO.cos_two_pi_div_three
  have hκ0 : 0 < κ := by linarith
  have hu0 : 0 < κ⁻¹ := inv_pos.mpr hκ0
  have hu : κ⁻¹ < 1 / 16 := by
    rw [inv_lt_comm₀ hκ0 (by norm_num)]; simpa using hκ
  constructor
  · -- `2(1+β)/κ = 2(1+β)u ≤ 4u < 1/4 < 1/2`
    rw [div_lt_iff₀ hκ0]
    have : 2 * (1 + β) * κ⁻¹ < 1 / 2 := by nlinarith
    have e : 2 * (1 + β) = 2 * (1 + β) * κ⁻¹ * κ := by field_simp
    rw [e]; nlinarith
  · -- `s₊ ≥ A₃ = β + 1/2 + u(1 + β/2) > 1/2`
    rw [hc]
    have hA : 1 / 2 < β - (-1 / 2) + κ⁻¹ * (1 - β * (-1 / 2)) := by nlinarith
    have hsq : 0 ≤ √((β - (-1 / 2) + κ⁻¹ * (1 - β * (-1 / 2))) ^ 2
        - 2 * κ⁻¹ * (1 - (-1 / 2)) * (1 + β ^ 2 - 2 * β * (-1 / 2))) := Real.sqrt_nonneg _
    linarith

end Lemma33

end OBABO.Section3
