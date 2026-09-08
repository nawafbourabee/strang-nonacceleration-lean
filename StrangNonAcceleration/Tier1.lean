/-
Tier-1 formalization for arXiv:2608.25279v1
("Non-acceleration of Strang Langevin splittings").

This file formalizes the finite, algebraic and numerical lemmas of the paper
that are used on the way to Corollary 1.3.  The statements are self-contained:
no measure theory, no Markov chains.  Each section names the item of the paper
it corresponds to.  Items that depend on the cited literature ([22], [30], [6])
or on probabilistic arguments are NOT formalized here; see the SM note.

Sections:
  A. Lemma 2.2 (Schur stability of the two-step position matrix).
  B. Theorem 3.1, identity (3.11) and the half-angle formula (3.9).
  C. Lemma 3.2 (m = 3 case) and the algebra of Lemma 3.3 (Steps 1 and 3).
  D. The constants in the proof of Corollary 1.2(i).
  E. Lemma 4.6 and the numerical constants of Section 4.5 / Proposition 4.7.
  F. The constants in the proof of Theorem 5.1.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic

open Real

namespace OBABO

/-! ## A. Lemma 2.2: Schur stability -/

/-- Schur criterion for the real quadratic `z^2 - t z + β` with `0 < β < 1`:
all complex roots have modulus `< 1` iff `|t| < 1 + β`.  This is the algebraic
content of the criterion `|tr M| < 1 + det M < 2` used in the proof of Lemma 2.2,
for the matrices `A_λ(s, β)` (trace `t = 1 + β - sλ`, determinant `β`). -/
theorem schur_quadratic (t β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∀ z : ℂ, z ^ 2 - (t : ℂ) * z + (β : ℂ) = 0 → ‖z‖ < 1) ↔ |t| < 1 + β := by
  constructor
  · intro h
    by_contra hcon
    rw [not_lt] at hcon
    -- a real root of modulus at least one exists
    have hΔ : 0 ≤ t ^ 2 - 4 * β := by
      have : (1 + β) ^ 2 ≤ t ^ 2 := by
        have := sq_abs t
        nlinarith [abs_nonneg t]
      nlinarith
    rcases le_abs'.mp hcon with ht | ht
    · -- t ≤ -(1+β): the root (t - √Δ)/2 is ≤ -1
      set z : ℝ := (t - √(t ^ 2 - 4 * β)) / 2 with hz
      have hroot : z ^ 2 - t * z + β = 0 := by
        rw [hz]; have := Real.sq_sqrt hΔ; nlinarith
      have hz1 : z ≤ -1 := by
        have hs := Real.sqrt_nonneg (t ^ 2 - 4 * β)
        have hsq := Real.sq_sqrt hΔ
        rw [hz]
        by_cases ht2 : t + 2 ≤ 0
        · linarith
        · push Not at ht2
          have : t + 2 ≤ √(t ^ 2 - 4 * β) := by
            apply Real.le_sqrt_of_sq_le
            nlinarith
          linarith
      have := h z (by
        have : ((z : ℂ)) ^ 2 - (t : ℂ) * (z : ℂ) + (β : ℂ) = ((z ^ 2 - t * z + β : ℝ) : ℂ) := by
          push_cast; ring
        rw [this, hroot]; simp)
      rw [Complex.norm_real, Real.norm_eq_abs] at this
      have : |z| ≥ 1 := by rw [abs_of_neg (by linarith)]; linarith
      linarith
    · -- t ≥ 1+β: the root (t + √Δ)/2 is ≥ 1
      set z : ℝ := (t + √(t ^ 2 - 4 * β)) / 2 with hz
      have hroot : z ^ 2 - t * z + β = 0 := by
        rw [hz]; have := Real.sq_sqrt hΔ; nlinarith
      have hz1 : 1 ≤ z := by
        have hs := Real.sqrt_nonneg (t ^ 2 - 4 * β)
        have hsq := Real.sq_sqrt hΔ
        rw [hz]
        by_cases ht2 : 2 - t ≤ 0
        · linarith
        · push Not at ht2
          have : 2 - t ≤ √(t ^ 2 - 4 * β) := by
            apply Real.le_sqrt_of_sq_le
            nlinarith
          linarith
      have := h z (by
        have : ((z : ℂ)) ^ 2 - (t : ℂ) * (z : ℂ) + (β : ℂ) = ((z ^ 2 - t * z + β : ℝ) : ℂ) := by
          push_cast; ring
        rw [this, hroot]; simp)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at this
      linarith
  · intro ht z hz
    have hre := congrArg Complex.re hz
    have him := congrArg Complex.im hz
    simp [sq] at hre him
    have hnorm : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
      rw [Complex.sq_norm, Complex.normSq_apply]
    have habs := abs_lt.mp ht
    have hlt : ‖z‖ ^ 2 < 1 := by
      rw [hnorm]
      by_cases hy : z.im = 0
      · -- real root
        rw [hy] at hre ⊢
        simp only [mul_zero, add_zero]
        set x := z.re with hx
        by_contra hcon
        push Not at hcon
        have hx1 : 1 ≤ x ∨ x ≤ -1 := by
          by_contra h'
          push Not at h'
          nlinarith
        rcases hx1 with hx1 | hx1
        · nlinarith [mul_nonneg (sub_nonneg.2 hx1) (sub_nonneg.2 (le_of_lt (lt_of_lt_of_le hβ1 hx1)))]
        · nlinarith [mul_nonneg (sub_nonneg.2 (show 1 ≤ -x by linarith))
            (sub_nonneg.2 (show β ≤ -x by linarith))]
      · -- complex conjugate pair: modulus squared equals β
        have hx : z.re = t / 2 := by
          have : z.im * (2 * z.re - t) = 0 := by linarith
          rcases mul_eq_zero.mp this with h | h
          · exact absurd h hy
          · linarith
        have : z.re * z.re + z.im * z.im = β := by
          rw [hx] at hre ⊢; nlinarith
        linarith
    have h0 := norm_nonneg z
    nlinarith

/-- Uniformity over the curvature interval: for `s > 0` and `κ ≥ 1`,
`|1 + β - sλ| < 1 + β` for every `λ ∈ [1, κ]` iff `s < 2(1+β)/κ`. -/
theorem uniform_trace_condition (s β κ : ℝ) (hs : 0 < s) (hκ : 1 ≤ κ) :
    (∀ l : ℝ, 1 ≤ l → l ≤ κ → |1 + β - s * l| < 1 + β) ↔ s < 2 * (1 + β) / κ := by
  constructor
  · intro h
    have := abs_lt.mp (h κ hκ le_rfl)
    rw [lt_div_iff₀ (by linarith)]
    linarith
  · intro h l hl1 hlκ
    rw [lt_div_iff₀ (by linarith)] at h
    rw [abs_lt]
    constructor
    · nlinarith
    · nlinarith

/-- Lemma 2.2, combined form: all `A_λ(s,β)`, `λ ∈ [1,κ]`, are Schur stable iff
`0 < s < 2(1+β)/κ`. -/
theorem lemma_2_2 (s β κ : ℝ) (hs : 0 < s) (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 1 ≤ κ) :
    (∀ l : ℝ, 1 ≤ l → l ≤ κ →
        ∀ z : ℂ, z ^ 2 - ((1 + β - s * l : ℝ) : ℂ) * z + (β : ℂ) = 0 → ‖z‖ < 1)
      ↔ s < 2 * (1 + β) / κ := by
  rw [← uniform_trace_condition s β κ hs hκ]
  constructor
  · intro h l hl1 hlκ
    exact (schur_quadratic _ β hβ0 hβ1).mp (h l hl1 hlκ)
  · intro h l hl1 hlκ
    exact (schur_quadratic _ β hβ0 hβ1).mpr (h l hl1 hlκ)

/-- With `s = h^2(1+β)/2` and `h > 0`, the condition `s < 2(1+β)/κ` is `h < 2/√κ`. -/
theorem step_size_form (h β κ : ℝ) (hh : 0 < h) (hβ0 : 0 < β) (hκ : 0 < κ) :
    h ^ 2 * (1 + β) / 2 < 2 * (1 + β) / κ ↔ h < 2 / √κ := by
  have hsκ : 0 < √κ := Real.sqrt_pos.mpr hκ
  have h1 : h ^ 2 * (1 + β) / 2 < 2 * (1 + β) / κ ↔ h ^ 2 * κ < 4 := by
    rw [div_lt_div_iff₀ (by norm_num) hκ]
    constructor <;> intro h' <;> nlinarith
  rw [h1, lt_div_iff₀ hsκ]
  constructor
  · intro h'
    nlinarith [Real.sq_sqrt hκ.le, Real.sqrt_nonneg κ]
  · intro h'
    have hsq := Real.sq_sqrt hκ.le
    have hp : 0 < h * √κ := mul_pos hh hsκ
    have h2 : (h * √κ) * (h * √κ) < 2 * 2 := mul_lt_mul'' h' h' hp.le hp.le
    have h3 : (h * √κ) * (h * √κ) = h ^ 2 * κ := by
      calc (h * √κ) * (h * √κ) = h ^ 2 * √κ ^ 2 := by ring
        _ = h ^ 2 * κ := by rw [hsq]
    linarith

/-- Second assertion of Lemma 2.2 (algebraic part): if `sκ ≥ 2(1+β)`, the characteristic
polynomial at `λ = κ` has a real root `z₋ ≤ -1`. -/
theorem real_root_le_neg_one (s β κ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hsκ : 2 * (1 + β) ≤ s * κ) :
    ∃ z : ℝ, z ≤ -1 ∧ z ^ 2 - (1 + β - s * κ) * z + β = 0 := by
  set t := 1 + β - s * κ with ht
  have ht' : t ≤ -(1 + β) := by rw [ht]; linarith
  have hΔ : 0 ≤ t ^ 2 - 4 * β := by nlinarith
  refine ⟨(t - √(t ^ 2 - 4 * β)) / 2, ?_, ?_⟩
  · have hs := Real.sqrt_nonneg (t ^ 2 - 4 * β)
    by_cases ht2 : t + 2 ≤ 0
    · linarith
    · push Not at ht2
      have : t + 2 ≤ √(t ^ 2 - 4 * β) := by
        apply Real.le_sqrt_of_sq_le
        nlinarith
      linarith
  · have := Real.sq_sqrt hΔ; nlinarith

/-! ## B. Theorem 3.1: the cycling quadratic and identity (3.11) -/

/-- The roots-of-unity cycling quadratic `P_m(s, β; κ)` of the paper, written with
`c = cos θ_m` as a free parameter. -/
noncomputable def Pcyc (s β κ c : ℝ) : ℝ :=
  s ^ 2 - 2 * (β - c + κ⁻¹ * (1 - β * c)) * s + 2 * κ⁻¹ * (1 - c) * (1 + β ^ 2 - 2 * β * c)

/-- The scalar `I_{0,1} = c_1` from the proof of Theorem 3.1, before the half-angle
substitution: `(1 - cos θ)(a^2 + b^2 - a) - b sin θ`, with
`a = ((1+β-s) - (1+β) cos θ)/((κ-1)s)` and `b = -(1-β) sin θ/((κ-1)s)`. -/
noncomputable def I01 (s β κ θ : ℝ) : ℝ :=
  let a := ((1 + β - s) - (1 + β) * Real.cos θ) / ((κ - 1) * s)
  let b := -(1 - β) * Real.sin θ / ((κ - 1) * s)
  (1 - Real.cos θ) * (a ^ 2 + b ^ 2 - a) - b * Real.sin θ

/-- Polynomial core of identity (3.11), with `A = (κ-1)s a`, `B = (κ-1)s b`. -/
theorem identity_3_11_poly (s β κ c S : ℝ) (hS : S ^ 2 + c ^ 2 = 1) (hκ : κ ≠ 0) :
    κ * (1 - c) * Pcyc s β κ c =
      (1 - c) * (((1 + β - s) - (1 + β) * c) ^ 2 + (-(1 - β) * S) ^ 2)
        - (1 - c) * (κ - 1) * s * ((1 + β - s) - (1 + β) * c)
        - (κ - 1) * s * (-(1 - β) * S) * S := by
  unfold Pcyc
  field_simp
  linear_combination ((β - 1) * (β * c - β - c + κ * s - s + 1)) * hS

/-- Identity (3.11): `P_m(s, β; κ) = (κ-1)^2 s^2 / (κ (1 - cos θ_m)) · I_{0,1}`. -/
theorem identity_3_11 (s β κ θ : ℝ) (hs : s ≠ 0) (hκ0 : κ ≠ 0) (hκ1 : κ ≠ 1)
    (hc : Real.cos θ ≠ 1) :
    Pcyc s β κ (Real.cos θ) = (κ - 1) ^ 2 * s ^ 2 / (κ * (1 - Real.cos θ)) * I01 s β κ θ := by
  have hκ1' : κ - 1 ≠ 0 := sub_ne_zero.mpr hκ1
  have hc' : 1 - Real.cos θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  have hden : κ * (1 - Real.cos θ) ≠ 0 := mul_ne_zero hκ0 hc'
  have key := identity_3_11_poly s β κ (Real.cos θ) (Real.sin θ)
    (Real.sin_sq_add_cos_sq θ) hκ0
  have hI : (κ - 1) ^ 2 * s ^ 2 * I01 s β κ θ =
      (1 - Real.cos θ) * (((1 + β - s) - (1 + β) * Real.cos θ) ^ 2
          + (-(1 - β) * Real.sin θ) ^ 2)
        - (1 - Real.cos θ) * (κ - 1) * s * ((1 + β - s) - (1 + β) * Real.cos θ)
        - (κ - 1) * s * (-(1 - β) * Real.sin θ) * Real.sin θ := by
    unfold I01
    field_simp
  rw [div_mul_eq_mul_div, eq_div_iff hden]
  linear_combination key - hI

/-- Half-angle identity used for (3.9): `sin x = (1 - cos x) cot(x/2)` when `sin(x/2) ≠ 0`. -/
theorem sin_eq_one_sub_cos_mul_cot (x : ℝ) (h : Real.sin (x / 2) ≠ 0) :
    Real.sin x = (1 - Real.cos x) * (Real.cos (x / 2) / Real.sin (x / 2)) := by
  have h1 : Real.sin x = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  have h2 : Real.cos x = 2 * Real.cos (x / 2) ^ 2 - 1 := by
    rw [← Real.cos_two_mul]; ring_nf
  rw [h1, h2]
  field_simp
  linear_combination (2 * Real.cos (x / 2)) * Real.sin_sq_add_cos_sq (x / 2)

/-- For `m ≥ 3`, `θ_m = 2π/m ∈ (0, π)`, hence `sin θ_m > 0` and `b < 0` in the proof of
Theorem 3.1 (given `0 < β < 1`, `s > 0`, `κ > 1`). -/
theorem b_neg (m : ℕ) (hm : 3 ≤ m) (s β κ : ℝ) (hs : 0 < s) (hβ1 : β < 1) (hκ : 1 < κ) :
    -(1 - β) * Real.sin (2 * π / m) / ((κ - 1) * s) < 0 := by
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hpos : 0 < Real.sin (2 * π / m) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · rw [div_lt_iff₀ (by linarith)]
      nlinarith [Real.pi_pos]
  have : 0 < (κ - 1) * s := mul_pos (by linarith) hs
  apply div_neg_of_neg_of_pos _ this
  nlinarith

/-! ## C. Lemma 3.2 (case m = 3) and the algebra of Lemma 3.3 -/

theorem sqrt5_bounds : (2.236 : ℝ) < √5 ∧ √5 < 2.2361 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- `C_GTD = (3 + √5)^2 > 27`. -/
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

/-! ## D. Constants in the proof of Corollary 1.2(i) -/

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

/-! ## E. Lemma 4.6 and the constants of Section 4.5 -/

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

/-- The three substitutions in the proof of Lemma 4.6. -/
theorem cycle_steps (g : ℝ → ℝ) (hg : GradOK g) :
    13 / 9 * a - 4 / 9 * c - 1 / 9 * g a = b ∧
    13 / 9 * b - 4 / 9 * a - 1 / 9 * g b = c ∧
    13 / 9 * c - 4 / 9 * b - 1 / 9 * g c = a := by
  obtain ⟨ha, hb, hc⟩ := grad_values g hg
  rw [ha, hb, hc]
  norm_num [a, b, c]

/-- The period-three sequence, indexed so that `p 0 = p_{-1} = c`, `p 1 = p_0 = a`,
`p 2 = p_1 = b` (index shift by one relative to the paper). -/
noncomputable def p (k : ℕ) : ℝ := if k % 3 = 0 then c else if k % 3 = 1 then a else b

theorem p_values (k : ℕ) : p k = a ∨ p k = b ∨ p k = c ∨ p k = 0 := by
  unfold p
  split_ifs <;> simp

/-- `(p_k)` is an exact orbit of the noise-free recurrence
`x_{k+1} = (13/9) x_k - (4/9) x_{k-1} - (1/9) U'(x_k)`. -/
theorem p_exact (g : ℝ → ℝ) (hg : GradOK g) (k : ℕ) :
    p (k + 2) = 13 / 9 * p (k + 1) - 4 / 9 * p k - 1 / 9 * g (p (k + 1)) := by
  obtain ⟨s1, s2, s3⟩ := cycle_steps g hg
  have h : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases h with h | h | h
  · have h1 : (k + 1) % 3 = 1 := by omega
    have h2 : (k + 2) % 3 = 2 := by omega
    simp only [p, h, h1, h2]; norm_num; linarith
  · have h1 : (k + 1) % 3 = 2 := by omega
    have h2 : (k + 2) % 3 = 0 := by omega
    simp only [p, h, h1, h2]; norm_num; linarith
  · have h1 : (k + 1) % 3 = 0 := by omega
    have h2 : (k + 2) % 3 = 1 := by omega
    simp only [p, h, h1, h2]; norm_num; linarith

/-- The `1/20`-neighbourhoods of `a`, `b`, `c` and `0` lie in the affine regions of (4.23):
there `U'(y) - U'(z) = 25 (y - z)`. -/
theorem grad_diff (g : ℝ → ℝ) (hg : GradOK g) (y z : ℝ)
    (hz : z = a ∨ z = b ∨ z = c ∨ z = 0) (hyz : |y - z| ≤ 1 / 20) :
    g y - g z = 25 * (y - z) := by
  obtain ⟨hy1, hy2⟩ := abs_le.mp hyz
  rcases hz with hz | hz | hz | hz <;> subst hz
  · rw [hg.right a (by norm_num [a, δ₀]), hg.right y (by norm_num [a, δ₀] at hy1 ⊢; linarith)]
    ring
  · rw [hg.left b (by norm_num [b, δ₀]), hg.left y (by norm_num [b, δ₀] at hy2 ⊢; linarith)]
    ring
  · rw [hg.left c (by norm_num [c, δ₀]), hg.left y (by norm_num [c, δ₀] at hy2 ⊢; linarith)]
    ring
  · rw [hg.left 0 (by norm_num [δ₀]), hg.left y (by norm_num [δ₀] at hy2 ⊢; linarith)]
    ring

/-- One step of the error recursion (4.24) with the two-stage bound: with
`f_k = e_{k+1} + (2/3) e_k` one has `f_{k+1} = -(2/3) f_k + ε_{k+2}`, so `|f| ≤ 3m` and
`|e| ≤ 9m` propagate. -/
theorem error_step (e0 e1 e2 ε m : ℝ) (hε : |ε| ≤ m) (hF : |e1 + 2 / 3 * e0| ≤ 3 * m)
    (h1 : |e1| ≤ 9 * m) (hrec : e2 = -4 / 3 * e1 - 4 / 9 * e0 + ε) :
    |e2 + 2 / 3 * e1| ≤ 3 * m ∧ |e2| ≤ 9 * m := by
  have hf : e2 + 2 / 3 * e1 = -2 / 3 * (e1 + 2 / 3 * e0) + ε := by rw [hrec]; ring
  obtain ⟨a1, a2⟩ := abs_le.mp hε
  obtain ⟨b1, b2⟩ := abs_le.mp hF
  obtain ⟨c1, c2⟩ := abs_le.mp h1
  constructor
  · rw [hf, abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith

/-- Bound (4.25): if `e_0 = e_1 = 0` and `e_{k+2} = -(4/3) e_{k+1} - (4/9) e_k + ε_{k+2}` with
`|ε_j| ≤ m`, then `|e_k| ≤ 9m` for every `k`.  (The paper sums the closed form
`e_k = Σ (k-j+1)(-2/3)^{k-j} ε_j`; here the same bound follows from the two-stage recursion.) -/
theorem bound_4_25 (e ε : ℕ → ℝ) (m : ℝ) (h0 : e 0 = 0) (h1 : e 1 = 0)
    (hrec : ∀ k, e (k + 2) = -4 / 3 * e (k + 1) - 4 / 9 * e k + ε (k + 2))
    (hε : ∀ k, |ε k| ≤ m) : ∀ k, |e k| ≤ 9 * m := by
  have hm : 0 ≤ m := le_trans (abs_nonneg _) (hε 0)
  have key : ∀ k, |e k| ≤ 9 * m ∧ |e (k + 1)| ≤ 9 * m ∧ |e (k + 1) + 2 / 3 * e k| ≤ 3 * m := by
    intro k
    induction k with
    | zero => simp [h0, h1]; positivity
    | succ k ih =>
      obtain ⟨_, ih1, ih2⟩ := ih
      obtain ⟨s1, s2⟩ := error_step (e k) (e (k + 1)) (e (k + 2)) (ε (k + 2)) m (hε _) ih2 ih1
        (hrec k)
      exact ⟨ih1, s2, s1⟩
  intro k; exact (key k).1

/-- Lemma 4.6 with the bootstrap: if `P` is an exact orbit of the noise-free recurrence with
values in `{a, b, c, 0}`, `x` follows the perturbed recurrence from the same two initial
values, and every perturbation is at most `1/180`, then `|x_k - P_k| ≤ 1/20` for every `k`
(so `x_k` and `P_k` stay in the same affine region at every step). -/
theorem lemma_4_6 (g : ℝ → ℝ) (hg : GradOK g) (P x ε : ℕ → ℝ)
    (hP : ∀ k, P k = a ∨ P k = b ∨ P k = c ∨ P k = 0)
    (hPrec : ∀ k, P (k + 2) = 13 / 9 * P (k + 1) - 4 / 9 * P k - 1 / 9 * g (P (k + 1)))
    (hx0 : x 0 = P 0) (hx1 : x 1 = P 1)
    (hxrec : ∀ k, x (k + 2) = 13 / 9 * x (k + 1) - 4 / 9 * x k - 1 / 9 * g (x (k + 1)) + ε (k + 2))
    (hε : ∀ k, |ε k| ≤ 1 / 180) :
    ∀ k, |x k - P k| ≤ 1 / 20 := by
  have key : ∀ k, |x k - P k| ≤ 9 * (1 / 180) ∧ |x (k + 1) - P (k + 1)| ≤ 9 * (1 / 180) ∧
      |(x (k + 1) - P (k + 1)) + 2 / 3 * (x k - P k)| ≤ 3 * (1 / 180) := by
    intro k
    induction k with
    | zero => simp [hx0, hx1]
    | succ k ih =>
      obtain ⟨_, ih1, ih2⟩ := ih
      have hrec : x (k + 2) - P (k + 2) =
          -4 / 3 * (x (k + 1) - P (k + 1)) - 4 / 9 * (x k - P k) + ε (k + 2) := by
        have hd := grad_diff g hg (x (k + 1)) (P (k + 1)) (hP (k + 1)) (by norm_num at ih1; exact ih1)
        rw [hxrec k, hPrec k]
        linarith
      obtain ⟨s1, s2⟩ := error_step (x k - P k) (x (k + 1) - P (k + 1)) (x (k + 2) - P (k + 2))
        (ε (k + 2)) (1 / 180) (hε _) ih2 ih1 hrec
      exact ⟨ih1, s2, s1⟩
  intro k
  have := (key k).1
  norm_num at this ⊢
  exact this

/-- Lemma 4.6 for the cycle: the perturbed recurrence started at `(p_{-1}, p_0) = (c, a)`
stays within `1/20` of the cycle. -/
theorem lemma_4_6_cycle (g : ℝ → ℝ) (hg : GradOK g) (x ε : ℕ → ℝ)
    (hx0 : x 0 = c) (hx1 : x 1 = a)
    (hxrec : ∀ k, x (k + 2) = 13 / 9 * x (k + 1) - 4 / 9 * x k - 1 / 9 * g (x (k + 1)) + ε (k + 2))
    (hε : ∀ k, |ε k| ≤ 1 / 180) :
    ∀ k, |x k - p k| ≤ 1 / 20 :=
  lemma_4_6 g hg p x ε p_values (p_exact g hg) (by simpa [p] using hx0) (by simpa [p] using hx1)
    hxrec hε

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

/-! ## F. Constants in the proof of Theorem 5.1 -/

namespace Diffusive

/-- `e^{-1}`. -/
noncomputable def e1 : ℝ := Real.exp (-1)

theorem e1_bounds : (0.3678 : ℝ) < e1 ∧ e1 < 0.36788 := by
  unfold e1
  rw [Real.exp_neg]
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.exp_one_lt_d9
  constructor
  · rw [lt_inv_comm₀ (by norm_num) (Real.exp_pos 1)]
    calc Real.exp 1 < 2.7182818286 := h2
      _ ≤ (0.3678 : ℝ)⁻¹ := by norm_num
  · rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
    calc (0.36788 : ℝ)⁻¹ ≤ 2.7182818283 := by norm_num
      _ < Real.exp 1 := h1

theorem e1_lt_half : e1 < 1 / 2 := by have := e1_bounds.2; linarith

theorem one_sub_e1_pos : 0 < 1 - e1 := by have := e1_bounds.2; linarith

/-- The tuning: `h_κ = 1/(4√κ)`, `γ_κ = 4√κ`. -/
noncomputable def h (κ : ℝ) : ℝ := 1 / (4 * √κ)
noncomputable def γ (κ : ℝ) : ℝ := 4 * √κ

theorem γ_mul_h (κ : ℝ) (hκ : 0 < κ) : γ κ * h κ = 1 := by
  unfold γ h
  have : √κ ≠ 0 := (Real.sqrt_pos.mpr hκ).ne'
  field_simp

/-- `β = e^{-γ_κ h_κ} = e^{-1}`. -/
theorem β_eq (κ : ℝ) (hκ : 0 < κ) : Real.exp (-(γ κ * h κ)) = e1 := by
  rw [γ_mul_h κ hκ]; rfl

/-- The step-size condition `h < (1 - e^{-γh})/(2√κ)` of [30, Theorem 5.2] holds since
`1/4 < (1 - e^{-1})/2`. -/
theorem step_condition (κ : ℝ) (hκ : 0 < κ) : h κ < (1 - e1) / (2 * √κ) := by
  unfold h
  have hs : 0 < √κ := Real.sqrt_pos.mpr hκ
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have := e1_lt_half
  nlinarith

/-- `b^2 < a/4` for `a = κ⁻¹`, `b = h_κ/(1 - e^{-1})`: the weighted norm is a norm. -/
theorem b_sq_lt (κ : ℝ) (hκ : 0 < κ) : (h κ / (1 - e1)) ^ 2 < κ⁻¹ / 4 := by
  unfold h
  have hs : 0 < √κ := Real.sqrt_pos.mpr hκ
  have hsq : √κ ^ 2 = κ := Real.sq_sqrt hκ.le
  have he := e1_lt_half
  have he0 := one_sub_e1_pos
  have key : (1 / (4 * √κ) / (1 - e1)) ^ 2 = 1 / (16 * κ * (1 - e1) ^ 2) := by
    rw [div_pow, div_pow, mul_pow, hsq]; field_simp; ring
  rw [key, inv_eq_one_div, div_div]
  apply one_div_lt_one_div_of_lt (by positivity)
  nlinarith [mul_pos (by linarith : 0 < 1 - e1 - 1 / 2) (by linarith : 0 < 1 - e1 + 1 / 2)]

/-- `c(h_κ) = h_κ^2/(4(1 - e^{-1})) = 1/(64 (1 - e^{-1}) κ)`. -/
noncomputable def cH (κ : ℝ) : ℝ := 1 / (64 * (1 - e1) * κ)

theorem cH_eq (κ : ℝ) (hκ : 0 < κ) : h κ ^ 2 / (4 * (1 - e1)) = cH κ := by
  unfold h cH
  have hsq : √κ ^ 2 = κ := Real.sq_sqrt hκ.le
  have he0 := one_sub_e1_pos
  rw [div_pow, mul_pow, hsq]
  field_simp
  norm_num

/-- `max{a, a⁻¹} = κ` for `a = κ⁻¹`, `κ ≥ 1`. -/
theorem max_a (κ : ℝ) (hκ : 1 ≤ κ) : max κ⁻¹ κ = κ := by
  apply max_eq_right
  rw [inv_le_comm₀ (by linarith) (by linarith)]
  calc κ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hκ
    _ ≤ κ := hκ

/-- `3 · 49/(1 - c) · κ · (1 - c)^n = 147 κ (1 - c)^{n-1}` for `n ≥ 1`, `c < 1`. -/
theorem wasserstein_const (κ c : ℝ) (hc : c < 1) (n : ℕ) (hn : 1 ≤ n) :
    3 * (49 / (1 - c)) * κ * (1 - c) ^ n = 147 * κ * (1 - c) ^ (n - 1) := by
  have h1 : 1 - c ≠ 0 := by linarith
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel, pow_succ]
  field_simp
  ring

/-- Constant `c_* = (2 √(2(1 - e^{-1})))⁻¹`. -/
noncomputable def cstar : ℝ := 1 / (2 * √(2 * (1 - e1)))

/-- The closed-form `R_24` of the paper. -/
noncomputable def R24 (κ : ℝ) : ℝ :=
  (5 / (12 * √6) + 10 / √6 + 2 * √3 * cstar) * √κ + √6 + 12 * √3 / 25 * cstar

/-- The regularization constant `R_r` of [6, Theorem 3.2 and Corollary 3.3] as displayed in the
proof of Theorem 5.1 (friction `γ`, step `h`, condition number `κ`, `r` steps). -/
noncomputable def Rr (γ h κ : ℝ) (r : ℕ) : ℝ :=
  (√γ)⁻¹ * (5 / ((r * h) * √(r * h)) + (12 + 5 * γ) / √(r * h)
    + κ * √(γ * h) / √(1 - Real.exp (-(γ * h))) * (1 + r * h / (1 + r * γ * h)) * √(r * h))

/-- Evaluation of `R_r` at the tuning with `r = 24`, written with `κ = T^4` (`T = κ^{1/4} > 0`). -/
theorem R24_eq_aux (T : ℝ) (hT : 0 < T) :
    Rr (γ (T ^ 4)) (h (T ^ 4)) (T ^ 4) 24 = R24 (T ^ 4) := by
  have hS : √(T ^ 4) = T ^ 2 := by
    rw [show T ^ 4 = (T ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hγ : γ (T ^ 4) = 4 * T ^ 2 := by unfold γ; rw [hS]
  have hh : h (T ^ 4) = 1 / (4 * T ^ 2) := by unfold h; rw [hS]
  have hγh : γ (T ^ 4) * h (T ^ 4) = 1 := γ_mul_h _ (by positivity)
  have hsγ : √(γ (T ^ 4)) = 2 * T := by
    rw [hγ, show 4 * T ^ 2 = (2 * T) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hrh : ((24 : ℕ) : ℝ) * h (T ^ 4) = 6 / T ^ 2 := by
    rw [hh]; push_cast; field_simp; ring
  have hsrh : √(6 / T ^ 2) = √6 / T := by
    rw [Real.sqrt_div (by norm_num), Real.sqrt_sq hT.le]
  have h2 : √(2 * (1 - e1)) = √2 * √(1 - e1) := Real.sqrt_mul (by norm_num) _
  have h6 : √6 = √2 * √3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.sqrt_mul (by norm_num)]
  have hs2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hv : 0 < √(1 - e1) := Real.sqrt_pos.mpr one_sub_e1_pos
  have hs2p : 0 < √2 := by positivity
  have hs3p : 0 < √3 := by positivity
  have he : Real.exp (-1) = e1 := rfl
  unfold Rr R24 cstar
  rw [hrh, hsrh, hsγ, hγh, Real.sqrt_one, he, h2, h6, hS, hγ, hh]
  push_cast
  field_simp
  rw [hs2, hs3]
  ring

/-- `R_24 = (5/(12√6) + 10/√6 + 2√3 c_*)√κ + √6 + (12√3/25) c_*` at the tuning, for every `κ > 0`. -/
theorem R24_eq (κ : ℝ) (hκ : 0 < κ) : Rr (γ κ) (h κ) κ 24 = R24 κ := by
  have hT : 0 < √(√κ) := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hκ)
  have hκ' : κ = √(√κ) ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg κ),
      Real.sq_sqrt hκ.le]
  rw [hκ']
  exact R24_eq_aux _ hT

theorem sqrt6_bounds : (2.449 : ℝ) < √6 ∧ √6 < 2.4495 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem sqrt3_bounds : (1.732 : ℝ) < √3 ∧ √3 < 1.7321 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem cstar_bounds : 0 < cstar ∧ cstar ≤ 0.44475 := by
  have he := e1_bounds.2
  have hw : (1.1243 : ℝ) ≤ √(2 * (1 - e1)) := by
    apply Real.le_sqrt_of_sq_le; nlinarith
  have hw0 : 0 < √(2 * (1 - e1)) := by linarith
  unfold cstar
  constructor
  · positivity
  · rw [div_le_iff₀ (by positivity)]; nlinarith

/-- `R_24 ≤ 8.62 √κ` for `κ ≥ 1`. -/
theorem R24_le (κ : ℝ) (hκ : 1 ≤ κ) : R24 κ ≤ 8.62 * √κ := by
  obtain ⟨h6a, h6b⟩ := sqrt6_bounds
  obtain ⟨h3a, h3b⟩ := sqrt3_bounds
  obtain ⟨hc0, hc1⟩ := cstar_bounds
  have hs : 1 ≤ √κ := by rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have t1 : 5 / (12 * √6) ≤ 0.17014 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  have t2 : 10 / √6 ≤ 4.0834 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  have t34 : √3 * cstar ≤ 1.7321 * 0.44475 := mul_le_mul h3b.le hc1 hc0.le (by norm_num)
  have t3 : 2 * √3 * cstar ≤ 1.5408 := by linarith
  have t5 : 12 * √3 / 25 * cstar ≤ 0.3698 := by linarith
  have hA : 5 / (12 * √6) + 10 / √6 + 2 * √3 * cstar ≤ 5.7944 := by linarith
  have hB : √6 + 12 * √3 / 25 * cstar ≤ 2.8193 := by linarith
  have hA0 : 0 ≤ 5 / (12 * √6) + 10 / √6 + 2 * √3 * cstar := by positivity
  unfold R24
  calc (5 / (12 * √6) + 10 / √6 + 2 * √3 * cstar) * √κ + √6 + 12 * √3 / 25 * cstar
      ≤ 5.7944 * √κ + 2.8193 * √κ := by
        have := mul_le_mul_of_nonneg_right hA (by linarith : (0:ℝ) ≤ √κ)
        nlinarith
    _ ≤ 8.62 * √κ := by linarith

/-- The mixing-time constant `c = 1/(128(1 - e^{-1}))` of Theorem 5.1. -/
noncomputable def cDiff : ℝ := 1 / (128 * (1 - e1))

theorem cDiff_pos : 0 < cDiff := by unfold cDiff; have := one_sub_e1_pos; positivity

theorem cDiff_lt : cDiff < 0.01237 := by
  unfold cDiff
  have := e1_bounds.2
  rw [div_lt_iff₀ (by have := one_sub_e1_pos; positivity)]; nlinarith

/-- `√147 < 12.1245`. -/
theorem sqrt147_lt : √147 < 12.1245 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- `e^{25/(128(1 - e^{-1}))} < 1.3634` (via the Taylor bound `Real.exp_bound'` with `n = 3`). -/
theorem exp_const_lt : Real.exp (25 / (128 * (1 - e1))) < 1.3634 := by
  set x := 25 / (128 * (1 - e1)) with hx
  have he := e1_bounds.2
  have he0 := one_sub_e1_pos
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hx1 : x ≤ 0.30904 := by
    rw [hx, div_le_iff₀ (by positivity)]; nlinarith
  have hb := Real.exp_bound' hx0 (by linarith) (by norm_num : 0 < 3)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
  norm_num at hb
  have hx2 : x ^ 2 ≤ 0.30904 ^ 2 := pow_le_pow_left₀ hx0 hx1 2
  have hx3 : x ^ 3 ≤ 0.30904 ^ 3 := pow_le_pow_left₀ hx0 hx1 3
  calc Real.exp x ≤ _ := hb
    _ < 1.3634 := by norm_num at hx2 hx3 ⊢; linarith

/-- The final constant: `√147 · 8.62 · e^{25/(128(1 - e^{-1}))} ≤ 143`. -/
theorem final_constant : √147 * 8.62 * Real.exp (25 / (128 * (1 - e1))) ≤ 143 := by
  have h1 := sqrt147_lt
  have h2 := exp_const_lt
  have h0 : 0 ≤ √147 := Real.sqrt_nonneg _
  have h3 : 0 < Real.exp (25 / (128 * (1 - e1))) := Real.exp_pos _
  nlinarith

/-- `(1 - t)^{(n-25)/2} ≤ e^{25t/2} e^{-tn/2}` for `0 ≤ t ≤ 1` and `n ≥ 25`. -/
theorem pow_bound (t : ℝ) (ht1 : t ≤ 1) (n : ℕ) (hn : 25 ≤ n) :
    (1 - t) ^ (((n : ℝ) - 25) / 2) ≤ Real.exp (25 * t / 2) * Real.exp (-(t * n / 2)) := by
  have hn' : (25 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 1 - t ≤ Real.exp (-t) := by have := Real.add_one_le_exp (-t); linarith
  calc (1 - t) ^ (((n : ℝ) - 25) / 2) ≤ Real.exp (-t) ^ (((n : ℝ) - 25) / 2) :=
        Real.rpow_le_rpow (by linarith) h1 (by linarith)
    _ = Real.exp (-t * (((n : ℝ) - 25) / 2)) := (Real.exp_mul _ _).symm
    _ = Real.exp (25 * t / 2) * Real.exp (-(t * n / 2)) := by
        rw [← Real.exp_add]; ring_nf

/-- `c(h_κ) ≤ 1/(64(1 - e^{-1}))` for `κ > 1`, and `c(h_κ) n/2 = c n/κ`. -/
theorem cH_le (κ : ℝ) (hκ : 1 < κ) : cH κ ≤ 1 / (64 * (1 - e1)) := by
  unfold cH
  have := one_sub_e1_pos
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  nlinarith

theorem cH_pos (κ : ℝ) (hκ : 0 < κ) : 0 < cH κ := by
  unfold cH; have := one_sub_e1_pos; positivity

theorem cH_lt_one (κ : ℝ) (hκ : 1 < κ) : cH κ < 1 := by
  have := cH_le κ hκ
  have he := e1_bounds.2
  have : 1 / (64 * (1 - e1)) < 1 := by
    rw [div_lt_one (by have := one_sub_e1_pos; positivity)]; linarith
  linarith

theorem cH_mul_eq (κ : ℝ) (hκ : 0 < κ) (n : ℝ) : cH κ * n / 2 = cDiff * n / κ := by
  unfold cH cDiff
  have := one_sub_e1_pos
  field_simp
  ring

/-- For `n ≤ 24` the bound is trivial: `143 e^{-24c} > 1`. -/
theorem small_n : 1 < 143 * Real.exp (-(24 * cDiff)) := by
  have h1 := cDiff_lt
  have h2 := cDiff_pos
  have := Real.add_one_le_exp (-(24 * cDiff))
  nlinarith

/-- The square-root step: `W_2^2 ≤ K (1 - c)^m W^2` gives `W_2 ≤ √K (1 - c)^{m/2} W`. -/
theorem sqrt_step (y K c W : ℝ) (m : ℕ) (hK : 0 ≤ K) (hc : 0 ≤ 1 - c)
    (hW : 0 ≤ W) (h : y ^ 2 ≤ K * (1 - c) ^ m * W ^ 2) :
    y ≤ √K * (1 - c) ^ ((m : ℝ) / 2) * W := by
  have hpow : (1 - c) ^ ((m : ℝ) / 2) = √((1 - c) ^ m) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hc]; ring_nf
  rw [hpow]
  have : √K * √((1 - c) ^ m) * W = √(K * (1 - c) ^ m * W ^ 2) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hK, Real.sqrt_sq hW]
  rw [this]
  exact Real.le_sqrt_of_sq_le h

/-- Assembly of the proof of Theorem 5.1 from the two cited estimates.  Notation: for a fixed
target, initial state `z` and invariant law `π`, `TV n = ‖δ_z Q^n - π‖_TV`,
`W1 n = W_1(δ_z Q^n, π)`, `W2 n = W_2(δ_z Q^n, π)`, `W = W_2(δ_z, π)`.  Hypotheses:
`hcontr` is the squared contraction estimate obtained from [30, Theorem 5.2 and Proposition 2.4],
`hreg` is the regularization estimate (5.1) of [6] with `r = 24` applied to `ν = δ_z Q^{n}`,
`ν̃ = π`.  Conclusion: the bound of Theorem 5.1 with `C = 143`, `c = 1/(128(1 - e^{-1}))`. -/
theorem theorem_5_1_assembly (κ : ℝ) (hκ : 1 < κ) (W : ℝ) (hW : 0 ≤ W)
    (TV W1 W2 : ℕ → ℝ) (hTV1 : ∀ n, TV n ≤ 1) (hW2nn : ∀ n, 0 ≤ W2 n)
    (hcontr : ∀ n, 1 ≤ n →
      W2 n ^ 2 ≤ 3 * (49 / (1 - cH κ)) * max κ⁻¹ κ * (1 - cH κ) ^ n * W ^ 2)
    (hW12 : ∀ n, W1 n ≤ W2 n)
    (hreg : ∀ n, TV (n + 24) ≤ Rr (γ κ) (h κ) κ 24 * W1 n) :
    ∀ n : ℕ, TV n ≤ 143 * κ * (1 + W) * Real.exp (-(cDiff * n) / κ) := by
  intro n
  have hκ0 : 0 < κ := by linarith
  have hc0 := cH_pos κ hκ0
  have hc1 := cH_lt_one κ hκ
  have hcd := cDiff_pos
  by_cases hn : n ≤ 24
  · -- trivial range
    have hn' : (n : ℝ) ≤ 24 := by exact_mod_cast hn
    have h1 : -(24 * cDiff) ≤ -(cDiff * n) / κ := by
      rw [neg_div, neg_le_neg_iff, div_le_iff₀ hκ0]
      nlinarith
    have h2 := Real.exp_le_exp.mpr h1
    have h3 := small_n
    calc TV n ≤ 1 := hTV1 n
      _ ≤ 143 * Real.exp (-(24 * cDiff)) := h3.le
      _ ≤ 143 * Real.exp (-(cDiff * n) / κ) := by nlinarith
      _ ≤ 143 * κ * (1 + W) * Real.exp (-(cDiff * n) / κ) := by
        have hk : 1 ≤ κ * (1 + W) := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hk
          (by positivity : (0:ℝ) ≤ 143 * Real.exp (-(cDiff * n) / κ))]
  · push Not at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 24 := ⟨n - 24, by omega⟩
    have hm : 1 ≤ m := by omega
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    set N : ℝ := ((m + 24 : ℕ) : ℝ) with hN
    -- Wasserstein contraction after m steps
    have hW2 : W2 m ≤ √(147 * κ) * (1 - cH κ) ^ (((m - 1 : ℕ) : ℝ) / 2) * W := by
      apply sqrt_step _ _ _ _ _ (by positivity) (by linarith) hW
      have hc := hcontr m hm
      rw [max_a κ hκ.le, wasserstein_const κ (cH κ) hc1 m hm] at hc
      exact hc
    have hexp : ((m - 1 : ℕ) : ℝ) / 2 = (N - 25) / 2 := by
      rw [hN, Nat.cast_sub hm]; push_cast; ring
    rw [hexp] at hW2
    have hR := R24_le κ hκ.le
    have hRr : Rr (γ κ) (h κ) κ 24 = R24 κ := R24_eq κ hκ0
    have hRpos : 0 ≤ R24 κ := by
      unfold R24; have := cstar_bounds.1; positivity
    have hpow : (1 - cH κ) ^ ((N - 25) / 2) ≤
        Real.exp (25 * cH κ / 2) * Real.exp (-(cH κ * N / 2)) :=
      pow_bound (cH κ) hc1.le (m + 24) (by omega)
    have hsqrt : √(147 * κ) = √147 * √κ := Real.sqrt_mul (by norm_num) κ
    have hsκ : √κ * √κ = κ := Real.mul_self_sqrt hκ0.le
    have hsκ0 : 0 ≤ √κ := Real.sqrt_nonneg κ
    have hE : Real.exp (25 * cH κ / 2) ≤ Real.exp (25 / (128 * (1 - e1))) := by
      rw [Real.exp_le_exp]
      have := cH_le κ hκ
      have := one_sub_e1_pos
      calc 25 * cH κ / 2 ≤ 25 * (1 / (64 * (1 - e1))) / 2 := by gcongr
        _ = 25 / (128 * (1 - e1)) := by field_simp; ring
    have hfin := final_constant
    have hcn : Real.exp (-(cH κ * N / 2)) = Real.exp (-(cDiff * N) / κ) := by
      rw [cH_mul_eq κ hκ0, neg_div]
    have hE2pos : 0 < Real.exp (-(cH κ * N / 2)) := Real.exp_pos _
    calc TV (m + 24) ≤ Rr (γ κ) (h κ) κ 24 * W1 m := hreg m
      _ ≤ R24 κ * W2 m := by rw [hRr]; exact mul_le_mul_of_nonneg_left (hW12 m) hRpos
      _ ≤ (8.62 * √κ) * (√147 * √κ * (1 - cH κ) ^ ((N - 25) / 2) * W) := by
        rw [hsqrt] at hW2
        exact mul_le_mul hR hW2 (hW2nn m) (by positivity)
      _ = 8.62 * √147 * κ * (1 - cH κ) ^ ((N - 25) / 2) * W := by
        have : (8.62 * √κ) * (√147 * √κ * (1 - cH κ) ^ ((N - 25) / 2) * W)
            = 8.62 * √147 * (√κ * √κ) * (1 - cH κ) ^ ((N - 25) / 2) * W := by ring
        rw [this, hsκ]
      _ ≤ 8.62 * √147 * κ * (Real.exp (25 * cH κ / 2) * Real.exp (-(cH κ * N / 2))) * W := by
        have h0 : 0 ≤ 8.62 * √147 * κ := by positivity
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow h0) hW
      _ ≤ 8.62 * √147 * κ * (Real.exp (25 / (128 * (1 - e1))) *
            Real.exp (-(cDiff * N) / κ)) * W := by
        rw [← hcn]
        have h0 : 0 ≤ 8.62 * √147 * κ := by positivity
        apply mul_le_mul_of_nonneg_right _ hW
        apply mul_le_mul_of_nonneg_left _ h0
        exact mul_le_mul_of_nonneg_right hE hE2pos.le
      _ ≤ 143 * κ * (1 + W) * Real.exp (-(cDiff * N) / κ) := by
        have hkey : 8.62 * √147 * Real.exp (25 / (128 * (1 - e1))) ≤ 143 := by linarith
        have hW1 : W ≤ 1 + W := by linarith
        have h0 : 0 ≤ κ * Real.exp (-(cDiff * N) / κ) := by positivity
        calc 8.62 * √147 * κ * (Real.exp (25 / (128 * (1 - e1))) *
              Real.exp (-(cDiff * N) / κ)) * W
            = (8.62 * √147 * Real.exp (25 / (128 * (1 - e1)))) *
                (κ * Real.exp (-(cDiff * N) / κ)) * W := by ring
          _ ≤ 143 * (κ * Real.exp (-(cDiff * N) / κ)) * (1 + W) := by
              apply mul_le_mul (mul_le_mul_of_nonneg_right hkey h0) hW1 hW (by positivity)
          _ = 143 * κ * (1 + W) * Real.exp (-(cDiff * N) / κ) := by ring

end Diffusive

end OBABO
