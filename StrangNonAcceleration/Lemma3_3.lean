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
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import StrangNonAcceleration.Section1
import StrangNonAcceleration.Corollary1_3

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

namespace OBABO

/-! ## Lemma 3.3 in full

The proof of Lemma 3.3 uses three facts from [22] besides Lemma 3.2 and the level-set bounds
of `Section1.lean`: Lemma B.7 (`one_sub_cos_ratio_le`), Lemma B.8 (`exists_m0`, in the form
with `m₀ ≥ 3` that the paper derives from `β > 1/5`), Lemma B.9 (`βMinus_le_of_ratio`), and
the computation leading to [22, equation (29)] (`sMinus_le_bound`). All are proved here from
the definitions of `Lemma3_2.lean`. -/

/-- [22, Lemma B.7]: `1 - cos θ_K ≤ (3/2)(1 - cos θ_{K+1})` for `K ≥ 2`. -/
theorem one_sub_cos_ratio_le (K : ℕ) (hK : 2 ≤ K) :
    1 - cos (θm K) ≤ 3 / 2 * (1 - cos (θm (K + 1))) := by
  have h5 := sqrt5_bounds
  rcases Nat.lt_or_ge K 5 with hlt | hge
  · interval_cases K
    · -- K = 2: cos θ_2 = -1, cos θ_3 = -1/2
      have h2 : θm 2 = π := by unfold θm; push_cast; ring
      have h3 : θm 3 = 2 * π / 3 := by unfold θm; norm_num
      rw [h2, h3, Real.cos_pi, cos_two_pi_div_three]; norm_num
    · -- K = 3: cos θ_3 = -1/2, cos θ_4 = 0
      have h3 : θm 3 = 2 * π / 3 := by unfold θm; norm_num
      have h4 : θm 4 = π / 2 := by unfold θm; ring
      rw [h3, h4, cos_two_pi_div_three, Real.cos_pi_div_two]; norm_num
    · -- K = 4: cos θ_4 = 0, cos θ_5 = (√5 - 1)/4
      have h4 : θm 4 = π / 2 := by unfold θm; ring
      have h5' : θm 5 = 2 * π / 5 := by unfold θm; norm_num
      rw [h4, h5', Real.cos_pi_div_two, cos_two_pi_div_five]
      nlinarith
  · have h := one_sub_cos_ratio K (by omega)
    have hK' : (5 : ℝ) ≤ K := by exact_mod_cast hge
    have hfrac : ((K + 1 : ℝ) / K) ^ 2 ≤ 3 / 2 := by
      have : (K + 1 : ℝ) / K ≤ 6 / 5 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
      have h0 : (0 : ℝ) ≤ (K + 1 : ℝ) / K := by positivity
      nlinarith
    have hc1 := cos_θm_lt_one (K + 1) (by omega)
    have h0 : 0 ≤ 1 - cos (θm (K + 1)) := by linarith
    calc 1 - cos (θm K) ≤ ((K + 1 : ℝ) / K) ^ 2 * (1 - cos (θm (K + 1))) := h
      _ ≤ 3 / 2 * (1 - cos (θm (K + 1))) := mul_le_mul_of_nonneg_right hfrac h0

/-- `cos θ_m` is nondecreasing in `m ≥ 2`. -/
theorem cos_θm_mono (m n : ℕ) (hm : 2 ≤ m) (hmn : m ≤ n) : cos (θm m) ≤ cos (θm n) := by
  apply Real.cos_le_cos_of_nonneg_of_le_pi (θm_pos n (by omega)).le
  · unfold θm
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    rw [div_le_iff₀ (by positivity)]; nlinarith [Real.pi_pos]
  · unfold θm
    have hm' : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    exact div_le_div_of_nonneg_left (by positivity) hm' this

/-- [22, Lemma B.8], with `m₀ ≥ 3` (the paper obtains `m₀ ≥ 3` from `β > 1/5`; `β ≥ 1/10`
suffices): for `1/10 ≤ β < 1` there is `m₀ ≥ 3` with
`(2/3)(1 - β) ≤ β - cos θ_{m₀} ≤ (3/2)(1 - β)`. -/
theorem exists_m0 (β : ℝ) (hβ0 : 1 / 10 ≤ β) (hβ1 : β < 1) :
    ∃ m₀ : ℕ, 3 ≤ m₀ ∧ 2 / 3 * (1 - β) ≤ β - cos (θm m₀) ∧
      β - cos (θm m₀) ≤ 3 / 2 * (1 - β) := by
  set t := β - 2 / 3 * (1 - β) with ht
  have ht1 : t < 1 := by linarith
  -- the predicate `3 ≤ k ∧ t < cos θ_{k+1}` holds for large `k` since `cos x ≥ 1 - x²/2`
  have hex : ∃ k : ℕ, 3 ≤ k ∧ t < cos (θm (k + 1)) := by
    set N : ℕ := ⌈2 * π ^ 2 / (1 - t)⌉₊ + 4 with hN
    refine ⟨N - 1, by omega, ?_⟩
    have hN1 : N - 1 + 1 = N := by omega
    rw [hN1]
    have hNge : 2 * π ^ 2 / (1 - t) < N := by
      have := Nat.le_ceil (2 * π ^ 2 / (1 - t))
      have : (⌈2 * π ^ 2 / (1 - t)⌉₊ : ℝ) + 4 = (N : ℝ) := by rw [hN]; push_cast; ring
      linarith
    have hNpos : (1 : ℝ) ≤ N := by
      have : (4 : ℕ) ≤ N := by omega
      exact_mod_cast (by omega : 1 ≤ N)
    have hsq : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have hθ : θm N ^ 2 / 2 = 2 * π ^ 2 / (N : ℝ) ^ 2 := by
      unfold θm; field_simp
    have hb := Real.one_sub_sq_div_two_le_cos (x := θm N)
    rw [hθ] at hb
    have : 2 * π ^ 2 / (N : ℝ) ^ 2 < 1 - t := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ (by linarith)] at hNge
      nlinarith [Real.pi_pos]
    linarith
  classical
  let K := Nat.find hex
  have hK : 3 ≤ K ∧ t < cos (θm (K + 1)) := Nat.find_spec hex
  have hmin : ∀ k, k < K → ¬(3 ≤ k ∧ t < cos (θm (k + 1))) := fun k hk => Nat.find_min hex hk
  refine ⟨K, hK.1, ?_, ?_⟩
  · -- lower bound: `cos θ_K ≤ t`
    have hcK : cos (θm K) ≤ t := by
      rcases Nat.eq_or_lt_of_le hK.1 with h3 | h3
      · rw [← h3]
        have : θm 3 = 2 * π / 3 := by unfold θm; norm_num
        rw [this, cos_two_pi_div_three]; linarith
      · have := hmin (K - 1) (by omega)
        push Not at this
        have h := this (by omega)
        have e : K - 1 + 1 = K := by omega
        rw [e] at h; exact h
    linarith
  · -- upper bound from Lemma B.7 and `t < cos θ_{K+1}`
    have h7 := one_sub_cos_ratio_le K (by omega)
    have : 1 - cos (θm (K + 1)) < 1 - t := by linarith [hK.2]
    nlinarith

/-- If the quadratic `a β² + b β + e` (with `a > 0`) is nonnegative at `β₁` and `β₁` lies to
the right of its vertex, then `β₁` is at least its larger root. -/
theorem βMinus_le_of (κ β₁ : ℝ) (m : ℕ) (hu : κ⁻¹ < 1 / 2)
    (hD : 0 ≤ Disc β₁ κ (cos (θm m)))
    (hV : 0 ≤ 2 * discA κ⁻¹ (cos (θm m)) * β₁ + discB κ⁻¹ (cos (θm m))) :
    βMinus κ m ≤ β₁ := by
  set u := κ⁻¹
  set c := cos (θm m)
  have ha := discA_pos u c hu
  set a := discA u c
  set b := discB u c
  set e := discC u c
  rw [Disc_eq] at hD
  unfold βMinus
  rw [div_le_iff₀ (by linarith)]
  have h2 := four_mul_quadratic a b e β₁
  have h3 : b ^ 2 - 4 * a * e ≤ (2 * a * β₁ + b) ^ 2 := by nlinarith
  have h4 : √(b ^ 2 - 4 * a * e) ≤ 2 * a * β₁ + b := by
    calc √(b ^ 2 - 4 * a * e) ≤ √((2 * a * β₁ + b) ^ 2) := Real.sqrt_le_sqrt h3
      _ = 2 * a * β₁ + b := Real.sqrt_sq hV
  linarith

/-- [22, Lemma B.9] in the form used by the paper: for `u = κ⁻¹ ≤ 1/16` and
`β ≤ 1` with `β - cos θ_m ≥ (2/3)(1 - β)`, one has `β ≥ β_-(m; κ)` (the hypothesis `m ≥ 2` of
[22] is not needed). -/
theorem βMinus_le_of_ratio (β κ : ℝ) (m : ℕ) (hκ0 : 0 < κ⁻¹) (hκ : κ⁻¹ ≤ 1 / 16)
    (hβ1 : β ≤ 1) (hratio : 2 / 3 * (1 - β) ≤ β - cos (θm m)) :
    βMinus κ m ≤ β := by
  set u := κ⁻¹ with hu
  set c := cos (θm m) with hc
  have hc1 : c ≤ 1 := Real.cos_le_one _
  have hc0 : -1 ≤ c := Real.neg_one_le_cos _
  -- `β ≥ β₁ := 1 - (3/5)(1 - c)`
  set β₁ := 1 - 3 / 5 * (1 - c) with hβ₁
  have hββ₁ : β₁ ≤ β := by linarith
  refine le_trans (βMinus_le_of κ β₁ m (by linarith) ?_ ?_) hββ₁
  · -- `Disc β₁ = (1 - c)² [4(1 - 16u)(1 - u) + 3u(1 - c)(10 - u(13 + 3c))]/25 ≥ 0`
    unfold Disc Acoef
    rw [← hu, ← hc]
    have key : (β₁ - c + u * (1 - β₁ * c)) ^ 2 - 2 * u * (1 - c) * (1 + β₁ ^ 2 - 2 * β₁ * c)
        = (1 - c) ^ 2 * (4 * (1 - 16 * u) * (1 - u) + 3 * u * (1 - c) * (10 - u * (13 + 3 * c))) / 25 := by
      rw [hβ₁]; ring
    rw [key]
    apply div_nonneg _ (by norm_num)
    apply mul_nonneg (sq_nonneg _)
    have h1 : 0 ≤ 4 * (1 - 16 * u) * (1 - u) := by
      apply mul_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ 3 * u * (1 - c) * (10 - u * (13 + 3 * c)) := by
      apply mul_nonneg (by positivity)
      nlinarith
    linarith
  · -- `2 a β₁ + b = (2/5)(1 - c)(2 + u + 5cu - 5cu² - 3c²u²) ≥ 0`
    unfold discA discB
    rw [← hu, ← hc]
    have key : 2 * (1 - 2 * u + c ^ 2 * u ^ 2) * β₁ +
        (-2 * c + 2 * u + 4 * c * u - 2 * c ^ 2 * u - 2 * c * u ^ 2)
        = 2 / 5 * (1 - c) * (2 + u + 5 * c * u - 5 * c * u ^ 2 - 3 * c ^ 2 * u ^ 2) := by
      rw [hβ₁]; ring
    rw [key]
    apply mul_nonneg (by linarith)
    have hu2 : u ^ 2 ≤ u / 16 := by nlinarith
    nlinarith [sq_nonneg c, mul_nonneg hκ0.le (sq_nonneg c)]

/-- The computation leading to [22, equation (29)]: if `(2/3)(1 - β) ≤ β - c ≤ (3/2)(1 - β)`,
`0 < β < 1`, and the roots are real, then
`A - √(A² - E) ≤ E/(β - c) ≤ (50/3) u (1 - β)`, where `A = A_m`, `E = 2u(1 - c)(1 + β² - 2βc)`
and `u = κ⁻¹`. -/
theorem sMinus_le_bound (β κ c : ℝ) (hκ0 : 0 < κ⁻¹) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hlo : 2 / 3 * (1 - β) ≤ β - c) (hhi : β - c ≤ 3 / 2 * (1 - β))
    (hD : 0 ≤ Disc β κ c) :
    Acoef β κ c - √(Disc β κ c) ≤ 50 / 3 * κ⁻¹ * (1 - β) := by
  set u := κ⁻¹ with hu
  set d := β - c with hd
  have hd0 : 0 < d := by linarith
  have hc1 : c < 1 := by linarith
  have hA : d ≤ Acoef β κ c := by
    unfold Acoef; rw [← hu]
    have : 0 ≤ 1 - β * c := by nlinarith
    nlinarith
  have hApos : 0 < Acoef β κ c := lt_of_lt_of_le hd0 hA
  set A := Acoef β κ c with hAdef
  set E := 2 * u * (1 - c) * (1 + β ^ 2 - 2 * β * c) with hE
  have hE0 : 0 ≤ E := by
    rw [hE]
    apply mul_nonneg (mul_nonneg (by positivity) (by linarith))
    nlinarith
  have hDisc : Disc β κ c = A ^ 2 - E := by unfold Disc; rw [← hu]
  rw [hDisc] at hD ⊢
  -- `A - √(A² - E) ≤ E/A`
  have h1 : A - E / A ≤ √(A ^ 2 - E) := by
    have hsq : (A - E / A) ^ 2 ≤ A ^ 2 - E := by
      have : (A - E / A) ^ 2 = A ^ 2 - 2 * E + (E / A) ^ 2 := by field_simp; ring
      rw [this]
      have : (E / A) ^ 2 ≤ E := by
        rw [div_pow, div_le_iff₀ (by positivity)]
        nlinarith
      linarith
    exact le_trans (le_abs_self _) (Real.abs_le_sqrt hsq)
  have h2 : A - √(A ^ 2 - E) ≤ E / A := by linarith
  -- `E/A ≤ E/d ≤ (50/3) u (1 - β)`
  have h3 : E / A ≤ E / d := div_le_div_of_nonneg_left hE0 hd0 hA
  have h4 : E / d ≤ 50 / 3 * u * (1 - β) := by
    rw [div_le_iff₀ hd0, hE]
    have hcd : c = β - d := by rw [hd]; ring
    rw [hcd]
    set w := 1 - β with hw
    have hw0 : 0 < w := by linarith
    have hβw : β = 1 - w := by rw [hw]; ring
    -- `2(w + d)(w(1 + β) + 2βd) ≤ 4(w + d)² ≤ (50/3) w d`
    have e1 : 2 * u * (1 - (β - d)) * (1 + β ^ 2 - 2 * β * (β - d))
        = u * (2 * (w + d) * (w * (1 + β) + 2 * β * d)) := by rw [hβw]; ring
    rw [e1]
    have h5 : 2 * (w + d) * (w * (1 + β) + 2 * β * d) ≤ 4 * (w + d) ^ 2 := by
      have : w * (1 + β) + 2 * β * d ≤ 2 * (w + d) := by nlinarith
      nlinarith
    have h6 : 4 * (w + d) ^ 2 ≤ 50 / 3 * w * d := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ 3 * d - 2 * w) (by linarith : 0 ≤ 3 * w - 2 * d)]
    calc u * (2 * (w + d) * (w * (1 + β) + 2 * β * d)) ≤ u * (50 / 3 * w * d) := by
          apply mul_le_mul_of_nonneg_left _ hκ0.le; linarith
      _ = 50 / 3 * u * w * d := by ring
  linarith

/-- **Lemma 3.3** (existence of a period with `P_m(s, β; κ) < 0`). Let `C⋆ > C_GTD = (3 + √5)²`,
`κ ≥ 2 C⋆`, and let `(s, β) ∈ (0, ∞) × (0, 1)` satisfy the numerical stability condition
(2.10), `s < 2(1 + β)/κ`, with `ρ_q(s, β; κ) < q_κ = (1 - C⋆/κ)/(1 + C⋆/κ)`. Then there is an
integer `m ≥ 3` with `P_m(s, β; κ) < 0`. -/
theorem lemma_3_3 (Cs κ s β : ℝ) (hC : (3 + √5) ^ 2 < Cs) (hκ : 2 * Cs ≤ κ)
    (hs : 0 < s) (hβ0 : 0 < β) (hβ1 : β < 1) (hstab : s < 2 * (1 + β) / κ)
    (hρ : ρq s β κ < q Cs κ) :
    ∃ m : ℕ, 3 ≤ m ∧ Pcyc s β κ (cos (θm m)) < 0 := by
  have h5 := sqrt5_bounds
  have hC27 : 27 < Cs := lt_trans C_GTD_gt_27 hC
  have hκ0 : 0 < κ := by linarith
  have hκ1 : 1 < κ := by linarith
  have hκ54 : 54 ≤ κ := by linarith
  set u := κ⁻¹ with hu
  have hu0 : 0 < u := inv_pos.2 hκ0
  have huC : u ≤ 1 / (2 * Cs) := by
    rw [hu, inv_le_comm₀ hκ0 (by positivity)]; simpa using hκ
  obtain ⟨hu1, hu16⟩ := u_small Cs u hC hu0 huC
  have hu54 : u ≤ 1 / 54 := by rw [hu, inv_le_comm₀ hκ0 (by norm_num)]; simpa using hκ54
  have hCu : Cs * u ≤ 1 / 2 := by
    calc Cs * u ≤ Cs * (1 / (2 * Cs)) := mul_le_mul_of_nonneg_left huC (by linarith)
      _ = 1 / 2 := by field_simp
  have hCu1 : Cs * u < 1 := by linarith
  -- `q_κ = (1 - C⋆ u)/(1 + C⋆ u)`, `g = (1 - u)/(1 + u)`, `ρ = ρ_q(s, β; κ)`
  have hq : q Cs κ = (1 - Cs * u) / (1 + Cs * u) := by
    unfold q; rw [show Cs / κ = Cs * u by rw [hu, div_eq_mul_inv]]
  set g := (1 - u) / (1 + u) with hg
  set ρ := ρq s β κ with hρdef
  have hqg : q Cs κ < g := by
    rw [hq, hg]; exact frac_anti (Cs * u) u (by linarith) (by nlinarith)
  have hg1 : g < 1 := by rw [hg, div_lt_one (by linarith)]; linarith
  have hρ1 : ρ < 1 := by linarith
  obtain ⟨hρ0, hβρ, hslow, -⟩ := ρq_facts s β κ hβ0 hs.le hκ1.le
  -- Step 1: `β > 13/42`
  have hell := ell_ρq_le s β κ hβ0 hβ1 hs.le hκ1 hρ1
  simp only at hell
  have hstar := rho_star_le_ρq s β κ hβ0 hβ1 hs.le hκ1 hρ1
  have hellq : ell g (q Cs κ) < ell g ρ := by
    rw [hg]
    exact ell_strictAnti u ρ (q Cs κ) hu0 (by linarith) hstar hρ (by rw [← hg]; exact hqg)
  have hnum := step1_numerics Cs u hu0 hC27 hCu
  rw [← hq] at hnum
  have hβ13 : 13 / 42 < β := by
    have : ell g ρ ≤ β := by unfold ell; rw [hg]; exact hell
    linarith [hnum.2.2]
  -- Step 2: `s > (50/3) u (1 - β)` and `s > s_-(β, m₀)` for the `m₀` of [22, Lemma B.8]
  have hρ50 : ρ < (1 - 50 / 3 * u) / (1 + 50 / 3 * u) := by
    calc ρ < q Cs κ := hρ
      _ = (1 - Cs * u) / (1 + Cs * u) := hq
      _ < (1 - 50 / 3 * u) / (1 + 50 / 3 * u) :=
        frac_anti (Cs * u) (50 / 3 * u) (by linarith) (by nlinarith)
  have hs50 : 50 / 3 * u * (1 - β) < s :=
    Section3.lemma33_step2_s_lower u ρ β s hu0 hu16 hρ0 hρ50 hβρ hslow
  obtain ⟨m₀, hm₀3, hlo, hhi⟩ := exists_m0 β (by linarith) hβ1
  -- Step 3: every `3 ≤ m ≤ m₀` has `β ≥ β_-(m; κ)`
  have hadm : ∀ m, 3 ≤ m → m ≤ m₀ → βMinus κ m ≤ β := by
    intro m hm3 hmm₀
    apply βMinus_le_of_ratio β κ m hu0 hu16.le hβ1.le
    have := cos_θm_mono m m₀ (by omega) hmm₀
    linarith
  have hDisc : ∀ m, 3 ≤ m → m ≤ m₀ → 0 ≤ Disc β κ (cos (θm m)) := fun m hm3 hmm₀ =>
    Disc_nonneg_of_βMinus_le β κ m (by linarith) (hadm m hm3 hmm₀)
  have hm₀s : sMinus β κ m₀ < s := by
    unfold sMinus
    have := sMinus_le_bound β κ (cos (θm m₀)) hu0 hβ0 hβ1 hlo hhi (hDisc m₀ hm₀3 le_rfl)
    rw [← hu] at this
    linarith
  -- the minimal period `m̄` with `s > s_-(β, m̄)`
  have hex : ∃ m : ℕ, 3 ≤ m ∧ m ≤ m₀ ∧ sMinus β κ m < s := ⟨m₀, hm₀3, le_rfl, hm₀s⟩
  classical
  set mb := Nat.find hex with hmb
  have hQ : 3 ≤ mb ∧ mb ≤ m₀ ∧ sMinus β κ mb < s := Nat.find_spec hex
  have hmin : ∀ m, m < mb → ¬(3 ≤ m ∧ m ≤ m₀ ∧ sMinus β κ m < s) :=
    fun m hm => Nat.find_min hex hm
  have hupper : s < sPlus β κ mb := by
    rcases Nat.eq_or_lt_of_le hQ.1 with h3 | h4
    · -- `m̄ = 3`: `s < 2(1+β)/κ < 1/2 < s_+(β, 3)`
      rw [← h3]
      have hθ3 : θm 3 = 2 * π / 3 := by unfold θm; norm_num
      have h := Section3.lemma33_step3_m3 β κ hβ0.le hβ1.le (by linarith)
      simp only [sPlus, Acoef, Disc]
      rw [hθ3]
      linarith [h.1, h.2]
    · -- `m̄ ≥ 4`: otherwise Lemma 3.2 contradicts the minimality of `m̄`
      by_contra hcon
      push Not at hcon
      have h32 := lemma_3_2 (mb - 1) (by omega) β κ hκ0 hu1 hβ0 hβ1
        (by rw [show mb - 1 + 1 = mb by omega]; exact hadm mb hQ.1 hQ.2.1)
      rw [show mb - 1 + 1 = mb by omega] at h32
      exact hmin (mb - 1) (by omega) ⟨by omega, by omega, lt_of_lt_of_le h32 hcon⟩
  refine ⟨mb, hQ.1, ?_⟩
  rw [Pcyc_eq_mul_roots s β κ mb (hDisc mb hQ.1 hQ.2.1)]
  apply mul_neg_of_pos_of_neg
  · linarith [hQ.2.2]
  · linarith

end OBABO
