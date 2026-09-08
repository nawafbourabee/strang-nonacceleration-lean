/-
Theorem 3.1(ii), the attracting neighborhood of the roots-of-unity cycle of

  N. Bou-Rabee, Provable non-acceleration of standard Strang splittings of kinetic
  Langevin dynamics, arXiv:2608.25279.

The plane is modelled by `ℂ` with its real inner product `⟪w, z⟫_ℝ = Re(z * conj w)`.
Rotation by `θ_m = 2π/m` is multiplication by `ζ = exp(θ_m i)`, the cycle points are
`x°_j = ζ^j`, and the matrix `M = a Id + b J` of (3.4) is multiplication by `μ = a + b i`
(the matrix `J` is multiplication by `i`). Everything in the proof of Theorem 3.1(ii)
is therefore complex arithmetic plus the variational characterization of the metric
projection onto a convex set (`norm_eq_iInf_iff_real_inner_le_zero` in Mathlib).

Contents.
* The cycling quadratic `P_m(s, β; κ)`, the scalar `I_{0,1}`, identity (3.11), the
  half-angle formula behind (3.9), and `b < 0` for `m ≥ 3` (namespace `OBABO`).
* Part A: the scalars `I_{0,j}` (3.9), their closed form, and the monotonicity (3.10).
* Part B: the radius `r_max` (3.13) and the projection inequalities on the balls
  `B(x°_t, r_max)`; the conclusion that `M x°_t` is the unique nearest point of
  `C = conv{M x°_j}` to every point of the ball; the local identity (3.8) for the
  gradient field `x ↦ x + (κ - 1) proj_C(x)` of (3.5).
* Part C: `P_m(s, β; κ) < 0` gives `I_{0,1} < 0`, hence all `I_{0,j} < 0`, hence
  `r_max > 0`, which is Theorem 3.1(ii) in the form used in the paper.

Part (i) of Theorem 3.1 (the representation of ψ, imported from [22]) is not formalized;
the gradient field of ψ enters only through its formula `x + (κ - 1) proj_C(x)`.
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic

open Real

namespace OBABO

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

end OBABO

open Complex Real
open scoped InnerProductSpace ComplexConjugate

namespace OBABO.Section3

/-! ## A. The scalars `I_{0,j}` and the monotonicity (3.10) -/

/-- The rotation `R_m` as the unit complex number `ζ = exp(θ i)`. -/
noncomputable def ζ (θ : ℝ) : ℂ := Complex.exp (θ * I)

/-- The cycle points `x°_j = R_m^j x°_0 = ζ^j`, with `x°_0 = 1`. -/
noncomputable def xc (θ : ℝ) (j : ℕ) : ℂ := ζ θ ^ j

/-- The matrix `M = a Id + b J` of (3.4), as the complex number `μ = a + b i`. -/
noncomputable def μ (a b : ℝ) : ℂ := (a : ℂ) + (b : ℂ) * I

/-- `I_{0,j} = ⟪x°_0 - M x°_0, M x°_j - M x°_0⟫` from the proof of Theorem 3.1. -/
noncomputable def I0 (a b θ : ℝ) (j : ℕ) : ℝ :=
  ⟪(1 : ℂ) - μ a b, μ a b * (xc θ j - 1)⟫_ℝ

lemma xc_eq_exp (θ : ℝ) (j : ℕ) : xc θ j = Complex.exp (((j * θ : ℝ) : ℂ) * I) := by
  unfold xc ζ
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast; ring

lemma xc_re (θ : ℝ) (j : ℕ) : (xc θ j).re = Real.cos (j * θ) := by
  rw [xc_eq_exp, Complex.exp_ofReal_mul_I_re]

lemma xc_im (θ : ℝ) (j : ℕ) : (xc θ j).im = Real.sin (j * θ) := by
  rw [xc_eq_exp, Complex.exp_ofReal_mul_I_im]

lemma norm_xc (θ : ℝ) (j : ℕ) : ‖xc θ j‖ = 1 := by
  rw [xc_eq_exp, Complex.norm_exp_ofReal_mul_I]

/-- The closed form (3.9) before the half-angle substitution:
`I_{0,j} = (1 - cos(jθ))(a² + b² - a) - b sin(jθ)`. -/
theorem I0_eq (a b θ : ℝ) (j : ℕ) :
    I0 a b θ j = (1 - Real.cos (j * θ)) * (a ^ 2 + b ^ 2 - a) - b * Real.sin (j * θ) := by
  unfold I0
  rw [Complex.inner]
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.conj_re, Complex.conj_im, xc_re, xc_im, μ, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- The half-angle form of (3.9): with `φ = jθ/2`,
`I_{0,j} = 2 sin φ · ((a² + b² - a) sin φ - b cos φ)`. -/
theorem I0_eq_half (a b θ : ℝ) (j : ℕ) :
    I0 a b θ j = 2 * Real.sin (j * θ / 2) *
      ((a ^ 2 + b ^ 2 - a) * Real.sin (j * θ / 2) - b * Real.cos (j * θ / 2)) := by
  rw [I0_eq]
  have h1 : Real.cos (j * θ) = 2 * Real.cos (j * θ / 2) ^ 2 - 1 := by
    rw [← Real.cos_two_mul]; ring_nf
  have h2 : Real.sin (j * θ) = 2 * Real.sin (j * θ / 2) * Real.cos (j * θ / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  have h3 := Real.sin_sq_add_cos_sq (j * θ / 2)
  rw [h1, h2]
  linear_combination (-2 * (a ^ 2 + b ^ 2 - a)) * h3

/-- Monotonicity (3.10) in the form used in the paper: if `b < 0`, `0 < φ₁ ≤ φ < π`, then
`g(φ) := K sin φ - b cos φ` satisfies `g(φ₁) < 0 → g(φ) < 0`. This is the statement that
`K - b cot φ` is strictly decreasing on `(0, π)` (with `-b > 0`). -/
theorem g_neg_of_g_neg (K b φ₁ φ : ℝ) (hb : b < 0) (h0 : 0 < φ₁) (h1 : φ₁ ≤ φ) (hπ : φ < π)
    (hg : K * Real.sin φ₁ - b * Real.cos φ₁ < 0) :
    K * Real.sin φ - b * Real.cos φ < 0 := by
  have hs1 : 0 < Real.sin φ₁ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith)
  have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi (by linarith) hπ
  have hd : 0 ≤ Real.sin (φ - φ₁) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi <;> linarith
  have key : (K * Real.sin φ - b * Real.cos φ) * Real.sin φ₁
      = (K * Real.sin φ₁ - b * Real.cos φ₁) * Real.sin φ + b * Real.sin (φ - φ₁) := by
    rw [Real.sin_sub]; ring
  have hneg : (K * Real.sin φ - b * Real.cos φ) * Real.sin φ₁ < 0 := by
    rw [key]
    have h4 := mul_nonpos_of_nonpos_of_nonneg hb.le hd
    have h5 := mul_neg_of_neg_of_pos hg hs
    linarith
  exact neg_of_mul_neg_left hneg hs1.le

/-- (3.10): for `θ = 2π/m`, `m ≥ 3`, `b < 0`: `I_{0,1} < 0` implies `I_{0,j} < 0` for
`1 ≤ j ≤ m - 1`. -/
theorem I0_neg_of_I0_one_neg (m : ℕ) (hm : 3 ≤ m) (a b : ℝ) (hb : b < 0)
    (h1 : I0 a b (2 * π / m) 1 < 0) :
    ∀ j : ℕ, 1 ≤ j → j ≤ m - 1 → I0 a b (2 * π / m) j < 0 := by
  intro j hj1 hjm
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hj1' : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  have hjm' : (j : ℝ) ≤ m - 1 := by
    have h' : ((j : ℕ) : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by exact_mod_cast hjm
    rwa [Nat.cast_sub (by omega), Nat.cast_one] at h'
  have hθpos : 0 < 2 * π / m := by positivity
  rw [I0_eq_half] at h1 ⊢
  simp only [Nat.cast_one, one_mul] at h1
  have hφ₁pos : 0 < 2 * π / m / 2 := by positivity
  have hφ₁π : 2 * π / m / 2 < π := by
    rw [div_div]
    exact (div_lt_iff₀ (by positivity)).2 (by nlinarith [Real.pi_pos])
  have hφ₁φ : 2 * π / m / 2 ≤ j * (2 * π / m) / 2 := by
    have := mul_le_mul_of_nonneg_right hj1' hθpos.le
    linarith
  have hφπ : j * (2 * π / m) / 2 < π := by
    have hjm2 : (j : ℝ) / m < 1 := by rw [div_lt_one hmpos]; linarith
    have e : (j : ℝ) * (2 * π / m) / 2 = π * (j / m) := by ring
    rw [e]
    nlinarith [Real.pi_pos]
  have hs1 : 0 < Real.sin (2 * π / m / 2) := Real.sin_pos_of_pos_of_lt_pi hφ₁pos hφ₁π
  have hg1 : (a ^ 2 + b ^ 2 - a) * Real.sin (2 * π / m / 2) - b * Real.cos (2 * π / m / 2) < 0 := by
    by_contra hcon
    push Not at hcon
    have := mul_nonneg (by linarith [hs1] : (0 : ℝ) ≤ 2 * Real.sin (2 * π / m / 2)) hcon
    linarith
  have hg := g_neg_of_g_neg (a ^ 2 + b ^ 2 - a) b _ _ hb hφ₁pos hφ₁φ hφπ hg1
  have hs : 0 < Real.sin (j * (2 * π / m) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) hφπ
  exact mul_neg_of_pos_of_neg (by linarith [hs]) hg

/-! ## B. The radius `r_max` and the projection inequalities on the balls -/

/-- `ζ^m = 1` for `θ = 2π/m`. -/
lemma ζ_pow_m (m : ℕ) (hm : 0 < m) : ζ (2 * π / m) ^ m = 1 := by
  unfold ζ
  rw [← Complex.exp_nat_mul]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have e : (m : ℂ) * (((2 * π / m : ℝ) : ℂ) * I) = 2 * π * I := by
    push_cast; field_simp
  rw [e, Complex.exp_two_pi_mul_I]

/-- `ζ^n` depends only on `n mod m`. -/
lemma ζ_pow_mod (m : ℕ) (hm : 0 < m) (n : ℕ) :
    ζ (2 * π / m) ^ n = ζ (2 * π / m) ^ (n % m) := by
  conv_lhs => rw [← Nat.mod_add_div n m]
  rw [pow_add, pow_mul, ζ_pow_m m hm, one_pow, mul_one]

/-- For `1 ≤ j ≤ m - 1`, `ζ^j ≠ 1`: the cycle points are distinct from `x°_0`. -/
lemma xc_ne_one (m : ℕ) (hm : 3 ≤ m) (j : ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ m - 1) :
    xc (2 * π / m) j ≠ 1 := by
  rw [xc_eq_exp]
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hn' : ((j * (2 * π / m) : ℝ) : ℂ) * I = ((n * (2 * π) : ℝ) : ℂ) * I := by
    push_cast at hn ⊢; linear_combination hn
  have hn'' := mul_right_cancel₀ Complex.I_ne_zero hn'
  have hreal : (j : ℝ) * (2 * π / m) = n * (2 * π) := Complex.ofReal_injective hn''
  have hm0 : (m : ℝ) ≠ 0 := hmpos.ne'
  have h2 : (j : ℝ) * (2 * π) = (n * m) * (2 * π) := by
    have e : (j : ℝ) * (2 * π / m) * m = j * (2 * π) := by field_simp
    linear_combination (m : ℝ) * hreal - e
  have h3 : (j : ℝ) = n * m := mul_right_cancel₀ (by positivity) h2
  have hj1' : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  have hjm' : (j : ℝ) ≤ m - 1 := by
    have h' : ((j : ℕ) : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by exact_mod_cast hjm
    rwa [Nat.cast_sub (by omega), Nat.cast_one] at h'
  rcases le_or_gt n 0 with hn0 | hn0
  · have : (n : ℝ) * m ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hn0) hmpos.le
    linarith
  · have h1 : (1 : ℤ) ≤ n := hn0
    have h1' : (1 : ℝ) ≤ n := by exact_mod_cast h1
    nlinarith

/-- The factorization `x°_j = x°_t · x°_d` with `d = (j + m - t) mod m`. -/
lemma xc_factor (m : ℕ) (hm : 0 < m) (j t : ℕ) (hj : j < m) (ht : t < m) :
    xc (2 * π / m) j = xc (2 * π / m) t * xc (2 * π / m) ((j + m - t) % m) := by
  unfold xc
  rw [← pow_add, ζ_pow_mod m hm (t + (j + m - t) % m), ζ_pow_mod m hm j]
  congr 1
  have e : t + (j + m - t) = j + m := by omega
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, e, Nat.add_mod_right, Nat.mod_eq_of_lt hj]

/-- For `j ≠ t` in `[0, m)`, the index `d = (j + m - t) mod m` lies in `[1, m - 1]`. -/
lemma index_range (m : ℕ) (j t : ℕ) (hj : j < m) (ht : t < m) (hjt : j ≠ t) :
    1 ≤ (j + m - t) % m ∧ (j + m - t) % m ≤ m - 1 := by
  have hm : 0 < m := by omega
  refine ⟨?_, by have := Nat.mod_lt (j + m - t) hm; omega⟩
  by_contra h0
  have h0' : (j + m - t) % m = 0 := by omega
  obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero h0'
  rcases q with _ | _ | q
  · rw [Nat.mul_zero] at hq; omega
  · rw [Nat.mul_one] at hq; omega
  · have e : m * (q + 1 + 1) = m * q + 2 * m := by ring
    rw [e] at hq
    generalize hp : m * q = p at hq
    omega

/-- The radius `r_max` of (3.13): the minimum over `1 ≤ j ≤ m - 1` of
`-I_{0,j} / |M(x°_j - x°_0)|`. -/
lemma Icc_nonempty (m : ℕ) (hm : 3 ≤ m) : (Finset.Icc 1 (m - 1)).Nonempty :=
  ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩

noncomputable def rmax (m : ℕ) (hm : 3 ≤ m) (a b : ℝ) : ℝ :=
  (Finset.Icc 1 (m - 1)).inf' (Icc_nonempty m hm)
    (fun j => -I0 a b (2 * π / m) j / ‖μ a b * (xc (2 * π / m) j - 1)‖)

lemma norm_μ_pos (a b : ℝ) (hb : b < 0) : 0 < ‖μ a b‖ := by
  rw [norm_pos_iff]
  intro h
  have him := congrArg Complex.im h
  simp [μ] at him
  linarith

/-- `r_max > 0` when every `I_{0,j}` is negative. -/
theorem rmax_pos (m : ℕ) (hm : 3 ≤ m) (a b : ℝ) (hb : b < 0)
    (hI : ∀ j : ℕ, 1 ≤ j → j ≤ m - 1 → I0 a b (2 * π / m) j < 0) :
    0 < rmax m hm a b := by
  unfold rmax
  rw [Finset.lt_inf'_iff]
  intro j hj
  rw [Finset.mem_Icc] at hj
  apply div_pos
  · linarith [hI j hj.1 hj.2]
  · rw [norm_mul]
    apply mul_pos (norm_μ_pos a b hb)
    rw [norm_pos_iff, sub_ne_zero]
    exact xc_ne_one m hm j hj.1 hj.2

lemma rmax_le (m : ℕ) (hm : 3 ≤ m) (a b : ℝ) (j : ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ m - 1) :
    rmax m hm a b ≤ -I0 a b (2 * π / m) j / ‖μ a b * (xc (2 * π / m) j - 1)‖ := by
  unfold rmax
  exact Finset.inf'_le _ (Finset.mem_Icc.mpr ⟨hj1, hjm⟩)

/-- Rotation invariance: `⟪ζ^t w, ζ^t z⟫ = ⟪w, z⟫`. -/
lemma inner_xc_mul (θ : ℝ) (t : ℕ) (w z : ℂ) :
    ⟪xc θ t * w, xc θ t * z⟫_ℝ = ⟪w, z⟫_ℝ := by
  rw [Complex.inner, Complex.inner, map_mul]
  have h : xc θ t * z * (conj (xc θ t) * conj w) = (xc θ t * conj (xc θ t)) * (z * conj w) := by
    ring
  rw [h, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_xc]
  simp

/-- The projection inequalities (3.12) on the ball: for `‖u‖ ≤ r_max` and every `j`,
`⟪x°_t + u - M x°_t, M x°_j - M x°_t⟫ ≤ 0`. -/
theorem projection_inequality (m : ℕ) (hm : 3 ≤ m) (a b : ℝ) (hb : b < 0)
    (hI : ∀ j : ℕ, 1 ≤ j → j ≤ m - 1 → I0 a b (2 * π / m) j < 0)
    (t : ℕ) (ht : t < m) (u : ℂ) (hu : ‖u‖ ≤ rmax m hm a b) (j : ℕ) (hj : j < m) :
    ⟪xc (2 * π / m) t + u - μ a b * xc (2 * π / m) t,
      μ a b * xc (2 * π / m) j - μ a b * xc (2 * π / m) t⟫_ℝ ≤ 0 := by
  by_cases hjt : j = t
  · subst hjt; simp
  · obtain ⟨hd1, hdm⟩ := index_range m j t hj ht hjt
    have hfac : xc (2 * π / m) j = xc (2 * π / m) t * xc (2 * π / m) ((j + m - t) % m) :=
      xc_factor m (by omega) j t hj ht
    have e3 : μ a b * xc (2 * π / m) j - μ a b * xc (2 * π / m) t
        = xc (2 * π / m) t * (μ a b * (xc (2 * π / m) ((j + m - t) % m) - 1)) := by
      rw [hfac]; ring
    have hsplit : ⟪xc (2 * π / m) t + u - μ a b * xc (2 * π / m) t,
        μ a b * xc (2 * π / m) j - μ a b * xc (2 * π / m) t⟫_ℝ
        = I0 a b (2 * π / m) ((j + m - t) % m)
          + ⟪u, μ a b * xc (2 * π / m) j - μ a b * xc (2 * π / m) t⟫_ℝ := by
      have e1 : xc (2 * π / m) t + u - μ a b * xc (2 * π / m) t
          = (xc (2 * π / m) t - μ a b * xc (2 * π / m) t) + u := by ring
      rw [e1, inner_add_left]
      congr 1
      have e2 : xc (2 * π / m) t - μ a b * xc (2 * π / m) t
          = xc (2 * π / m) t * (1 - μ a b) := by ring
      rw [e2, e3, inner_xc_mul]
      rfl
    have hnorm : ‖μ a b * xc (2 * π / m) j - μ a b * xc (2 * π / m) t‖
        = ‖μ a b * (xc (2 * π / m) ((j + m - t) % m) - 1)‖ := by
      rw [e3, norm_mul, norm_xc, one_mul]
    have hpos : 0 < ‖μ a b * (xc (2 * π / m) ((j + m - t) % m) - 1)‖ := by
      rw [norm_mul]
      apply mul_pos (norm_μ_pos a b hb)
      rw [norm_pos_iff, sub_ne_zero]
      exact xc_ne_one m hm _ hd1 hdm
    have hI0 := hI _ hd1 hdm
    have hr := rmax_le m hm a b _ hd1 hdm
    have hcs : ⟪u, μ a b * xc (2 * π / m) j - μ a b * xc (2 * π / m) t⟫_ℝ
        ≤ ‖u‖ * ‖μ a b * (xc (2 * π / m) ((j + m - t) % m) - 1)‖ := by
      rw [← hnorm]; exact real_inner_le_norm _ _
    rw [hsplit]
    have hu' : ‖u‖ * ‖μ a b * (xc (2 * π / m) ((j + m - t) % m) - 1)‖
        ≤ -I0 a b (2 * π / m) ((j + m - t) % m) := by
      calc ‖u‖ * ‖μ a b * (xc (2 * π / m) ((j + m - t) % m) - 1)‖
          ≤ rmax m hm a b * ‖μ a b * (xc (2 * π / m) ((j + m - t) % m) - 1)‖ :=
            mul_le_mul_of_nonneg_right hu (norm_nonneg _)
        _ ≤ (-I0 a b (2 * π / m) ((j + m - t) % m)
              / ‖μ a b * (xc (2 * π / m) ((j + m - t) % m) - 1)‖)
              * ‖μ a b * (xc (2 * π / m) ((j + m - t) % m) - 1)‖ :=
            mul_le_mul_of_nonneg_right hr (norm_nonneg _)
        _ = -I0 a b (2 * π / m) ((j + m - t) % m) := div_mul_cancel₀ _ hpos.ne'
    linarith

/-- The convex set `C = conv{M x°_j : 0 ≤ j < m}` of (3.4). -/
noncomputable def Cset (m : ℕ) (a b : ℝ) : Set ℂ :=
  convexHull ℝ (Set.range (fun j : Fin m => μ a b * xc (2 * π / m) j))

lemma mul_xc_mem_Cset (m : ℕ) (a b : ℝ) (t : ℕ) (ht : t < m) :
    μ a b * xc (2 * π / m) t ∈ Cset m a b :=
  subset_convexHull ℝ _ ⟨⟨t, ht⟩, rfl⟩

lemma convex_Cset (m : ℕ) (a b : ℝ) : Convex ℝ (Cset m a b) := convex_convexHull ℝ _

/-- The half-space `{y : ⟪x - c, y - c⟫ ≤ 0}` is convex. -/
lemma convex_halfspace_inner (x c : ℂ) : Convex ℝ {y : ℂ | ⟪x - c, y - c⟫_ℝ ≤ 0} := by
  have hlin : IsLinearMap ℝ (fun y : ℂ => ⟪x - c, y⟫_ℝ) :=
    ⟨fun y z => inner_add_right _ _ _, fun r y => inner_smul_right _ _ _⟩
  have e : {y : ℂ | ⟪x - c, y - c⟫_ℝ ≤ 0} = {y : ℂ | ⟪x - c, y⟫_ℝ ≤ ⟪x - c, c⟫_ℝ} := by
    ext y
    simp only [Set.mem_ofPred_eq, inner_sub_right]
    constructor <;> intro h <;> linarith
  rw [e]
  exact convex_halfSpace_le hlin _

/-- Theorem 3.1(ii), projection form: for `‖u‖ ≤ r_max`, the variational inequality
`⟪x°_t + u - M x°_t, y - M x°_t⟫ ≤ 0` holds for every `y ∈ C`. -/
theorem variational_inequality (m : ℕ) (hm : 3 ≤ m) (a b : ℝ) (hb : b < 0)
    (hI : ∀ j : ℕ, 1 ≤ j → j ≤ m - 1 → I0 a b (2 * π / m) j < 0)
    (t : ℕ) (ht : t < m) (u : ℂ) (hu : ‖u‖ ≤ rmax m hm a b) :
    ∀ y ∈ Cset m a b,
      ⟪xc (2 * π / m) t + u - μ a b * xc (2 * π / m) t,
        y - μ a b * xc (2 * π / m) t⟫_ℝ ≤ 0 := by
  intro y hy
  have hsub : Set.range (fun j : Fin m => μ a b * xc (2 * π / m) j) ⊆
      {y : ℂ | ⟪xc (2 * π / m) t + u - μ a b * xc (2 * π / m) t,
        y - μ a b * xc (2 * π / m) t⟫_ℝ ≤ 0} := by
    rintro _ ⟨j, rfl⟩
    exact projection_inequality m hm a b hb hI t ht u hu (j : ℕ) j.isLt
  exact convexHull_min hsub (convex_halfspace_inner _ _) hy

/-- `M x°_t` is a nearest point of `C` to `x°_t + u` whenever `‖u‖ ≤ r_max`
(`proj_C(x°_t + u) = M x°_t`). -/
theorem nearest_point (m : ℕ) (hm : 3 ≤ m) (a b : ℝ) (hb : b < 0)
    (hI : ∀ j : ℕ, 1 ≤ j → j ≤ m - 1 → I0 a b (2 * π / m) j < 0)
    (t : ℕ) (ht : t < m) (u : ℂ) (hu : ‖u‖ ≤ rmax m hm a b) :
    ‖(xc (2 * π / m) t + u) - μ a b * xc (2 * π / m) t‖
      = iInf (fun w : Cset m a b => ‖(xc (2 * π / m) t + u) - w‖) := by
  rw [norm_eq_iInf_iff_real_inner_le_zero (convex_Cset m a b) (mul_xc_mem_Cset m a b t ht)]
  exact variational_inequality m hm a b hb hI t ht u hu

/-- Uniqueness of the nearest point of a convex set, from the variational
characterization. -/
theorem nearest_unique {K : Set ℂ} (hK : Convex ℝ K) {x v v' : ℂ} (hv : v ∈ K) (hv' : v' ∈ K)
    (h : ‖x - v‖ = iInf (fun w : K => ‖x - w‖)) (h' : ‖x - v'‖ = iInf (fun w : K => ‖x - w‖)) : v = v' := by
  rw [norm_eq_iInf_iff_real_inner_le_zero hK hv] at h
  rw [norm_eq_iInf_iff_real_inner_le_zero hK hv'] at h'
  have h1 := h v' hv'
  have h2 := h' v hv
  have hsum : ⟪v' - v, v' - v⟫_ℝ ≤ 0 := by
    have e : v' - v = (x - v) - (x - v') := by ring
    have e2 : v - v' = -(v' - v) := by ring
    calc ⟪v' - v, v' - v⟫_ℝ = ⟪x - v, v' - v⟫_ℝ - ⟪x - v', v' - v⟫_ℝ := by
          rw [e, inner_sub_left]
      _ = ⟪x - v, v' - v⟫_ℝ + ⟪x - v', v - v'⟫_ℝ := by
          rw [e2, inner_neg_right]; ring
      _ ≤ 0 := by linarith
  have h0 : ‖v' - v‖ ^ 2 ≤ 0 := by rw [← real_inner_self_eq_norm_sq]; exact hsum
  have hz : ‖v' - v‖ = 0 := by nlinarith [norm_nonneg (v' - v)]
  rw [norm_eq_zero, sub_eq_zero] at hz
  exact hz.symm

/-- A metric projection onto `K`: a map `p` with `p x ∈ K` and `p x` nearest to `x`. -/
def IsMetricProj (K : Set ℂ) (p : ℂ → ℂ) : Prop :=
  ∀ x, p x ∈ K ∧ ‖x - p x‖ = iInf (fun w : K => ‖x - w‖)

/-- The metric projection onto `C` is constant, equal to `M x°_t`, on `B(x°_t, r_max)`. -/
theorem proj_const (m : ℕ) (hm : 3 ≤ m) (a b : ℝ) (hb : b < 0)
    (hI : ∀ j : ℕ, 1 ≤ j → j ≤ m - 1 → I0 a b (2 * π / m) j < 0)
    (p : ℂ → ℂ) (hp : IsMetricProj (Cset m a b) p)
    (t : ℕ) (ht : t < m) (u : ℂ) (hu : ‖u‖ ≤ rmax m hm a b) :
    p (xc (2 * π / m) t + u) = μ a b * xc (2 * π / m) t := by
  obtain ⟨hmem, hmin⟩ := hp (xc (2 * π / m) t + u)
  exact nearest_unique (convex_Cset m a b) hmem (mul_xc_mem_Cset m a b t ht) hmin
    (nearest_point m hm a b hb hI t ht u hu)

/-- The gradient field of the potential ψ of (3.5): `∇ψ(x) = x + (κ - 1) proj_C(x)`. -/
noncomputable def gradPsi (κ : ℝ) (p : ℂ → ℂ) (x : ℂ) : ℂ := x + ((κ - 1 : ℝ) : ℂ) * p x

/-- **Theorem 3.1(ii), identity (3.8)**: `∇ψ(x°_t + u) = ∇ψ(x°_t) + u` for `‖u‖ ≤ r_max`. -/
theorem theorem_3_1_ii (m : ℕ) (hm : 3 ≤ m) (a b κ : ℝ) (hb : b < 0)
    (hI : ∀ j : ℕ, 1 ≤ j → j ≤ m - 1 → I0 a b (2 * π / m) j < 0)
    (p : ℂ → ℂ) (hp : IsMetricProj (Cset m a b) p)
    (t : ℕ) (ht : t < m) (u : ℂ) (hu : ‖u‖ ≤ rmax m hm a b) :
    gradPsi κ p (xc (2 * π / m) t + u) = gradPsi κ p (xc (2 * π / m) t) + u := by
  have hp0 : p (xc (2 * π / m) t) = μ a b * xc (2 * π / m) t := by
    have := proj_const m hm a b hb hI p hp t ht 0
      (by rw [norm_zero]; exact (rmax_pos m hm a b hb hI).le)
    simpa using this
  unfold gradPsi
  rw [proj_const m hm a b hb hI p hp t ht u hu, hp0]
  ring

/-! ## C. Link with the cycling quadratic: `P_m(s, β; κ) < 0 ⇒ r_max > 0` -/

/-- The coefficient `a` of `M = a Id + b J` in the proof of Theorem 3.1. -/
noncomputable def aCoef (s β κ θ : ℝ) : ℝ :=
  ((1 + β - s) - (1 + β) * Real.cos θ) / ((κ - 1) * s)

/-- The coefficient `b` of `M = a Id + b J` in the proof of Theorem 3.1. -/
noncomputable def bCoef (s β κ θ : ℝ) : ℝ := -(1 - β) * Real.sin θ / ((κ - 1) * s)

/-- `I_{0,1}` in this file equals the scalar `I01` defined above (namespace `OBABO`). -/
lemma I0_one_eq_I01 (s β κ θ : ℝ) :
    I0 (aCoef s β κ θ) (bCoef s β κ θ) θ 1 = OBABO.I01 s β κ θ := by
  rw [I0_eq]
  unfold OBABO.I01 aCoef bCoef
  simp only [Nat.cast_one, one_mul]

/-- `P_m(s, β; κ) < 0` implies `I_{0,1} < 0` (identity (3.11) with positive prefactor). -/
theorem I0_one_neg_of_Pcyc_neg (m : ℕ) (hm : 3 ≤ m) (s β κ : ℝ) (hs : 0 < s) (hκ : 1 < κ)
    (hP : OBABO.Pcyc s β κ (Real.cos (2 * π / m)) < 0) :
    I0 (aCoef s β κ (2 * π / m)) (bCoef s β κ (2 * π / m)) (2 * π / m) 1 < 0 := by
  rw [I0_one_eq_I01]
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hc : Real.cos (2 * π / m) ≠ 1 := by
    intro h
    have hpos : 0 < 2 * π / m := by positivity
    have hlt : 2 * π / m < 2 * π :=
      (div_lt_iff₀ (by linarith)).2 (by nlinarith [Real.pi_pos])
    rw [Real.cos_eq_one_iff_of_lt_of_lt (by linarith) hlt] at h
    linarith
  have h311 := OBABO.identity_3_11 s β κ (2 * π / m) hs.ne' (by linarith) (by linarith) hc
  rw [h311] at hP
  have hpre : 0 < (κ - 1) ^ 2 * s ^ 2 / (κ * (1 - Real.cos (2 * π / m))) := by
    apply div_pos
    · positivity
    · apply mul_pos (by linarith)
      rcases (Real.cos_le_one (2 * π / m)).lt_or_eq with h | h
      · linarith
      · exact absurd h hc
  exact neg_of_mul_neg_right hP hpre.le

/-- **Theorem 3.1(ii) in the form used in the paper.** If `P_m(s, β; κ) < 0` (with
`m ≥ 3`, `s > 0`, `β < 1`, `κ > 1`), then `r_max > 0` and the metric projection onto
`C` is constant on every ball `B(x°_t, r_max)`, so that (3.8) holds there. -/
theorem theorem_3_1_ii_of_Pcyc (m : ℕ) (hm : 3 ≤ m) (s β κ : ℝ) (hs : 0 < s)
    (hβ1 : β < 1) (hκ : 1 < κ)
    (hP : OBABO.Pcyc s β κ (Real.cos (2 * π / m)) < 0)
    (p : ℂ → ℂ)
    (hp : IsMetricProj (Cset m (aCoef s β κ (2 * π / m)) (bCoef s β κ (2 * π / m))) p) :
    0 < rmax m hm (aCoef s β κ (2 * π / m)) (bCoef s β κ (2 * π / m)) ∧
    ∀ (t : ℕ), t < m → ∀ (u : ℂ),
      ‖u‖ ≤ rmax m hm (aCoef s β κ (2 * π / m)) (bCoef s β κ (2 * π / m)) →
      gradPsi κ p (xc (2 * π / m) t + u) = gradPsi κ p (xc (2 * π / m) t) + u := by
  have hb : bCoef s β κ (2 * π / m) < 0 := OBABO.b_neg m hm s β κ hs hβ1 hκ
  have hI1 := I0_one_neg_of_Pcyc_neg m hm s β κ hs hκ hP
  have hI := I0_neg_of_I0_one_neg m hm _ _ hb hI1
  exact ⟨rmax_pos m hm _ _ hb hI,
    fun t ht u hu => theorem_3_1_ii m hm _ _ κ hb hI p hp t ht u hu⟩

/-! ## D. The metric projection onto `C` exists -/

/-- `C` is nonempty (it contains `M x°_0`). -/
lemma Cset_nonempty (m : ℕ) (hm : 1 ≤ m) (a b : ℝ) : (Cset m a b).Nonempty :=
  ⟨_, mul_xc_mem_Cset m a b 0 (by omega)⟩

/-- `C` is compact (the convex hull of finitely many points), hence complete. -/
lemma isCompact_Cset (m : ℕ) (a b : ℝ) : IsCompact (Cset m a b) :=
  (Set.finite_range _).isCompact_convexHull (𝕜 := ℝ)

/-- The metric projection onto `C` exists: for every `x` there is a nearest point of `C`. -/
theorem exists_isMetricProj (m : ℕ) (hm : 1 ≤ m) (a b : ℝ) :
    ∃ p : ℂ → ℂ, IsMetricProj (Cset m a b) p := by
  have h := exists_norm_eq_iInf_of_complete_convex (Cset_nonempty m hm a b)
    (isCompact_Cset m a b).isClosed.isComplete (convex_Cset m a b)
  choose p hp using h
  exact ⟨p, fun x => ⟨(hp x).1, (hp x).2⟩⟩

/-- A fixed choice of the metric projection onto `C`. -/
noncomputable def projC (m : ℕ) (hm : 1 ≤ m) (a b : ℝ) : ℂ → ℂ :=
  Classical.choose (exists_isMetricProj m hm a b)

theorem isMetricProj_projC (m : ℕ) (hm : 1 ≤ m) (a b : ℝ) :
    IsMetricProj (Cset m a b) (projC m hm a b) :=
  Classical.choose_spec (exists_isMetricProj m hm a b)

/-- **Theorem 3.1(ii)** for the metric projection `projC` itself (no hypothesis on `p`). -/
theorem theorem_3_1_ii_projC (m : ℕ) (hm : 3 ≤ m) (s β κ : ℝ) (hs : 0 < s)
    (hβ1 : β < 1) (hκ : 1 < κ)
    (hP : OBABO.Pcyc s β κ (Real.cos (2 * π / m)) < 0) :
    0 < rmax m hm (aCoef s β κ (2 * π / m)) (bCoef s β κ (2 * π / m)) ∧
    ∀ (t : ℕ), t < m → ∀ (u : ℂ),
      ‖u‖ ≤ rmax m hm (aCoef s β κ (2 * π / m)) (bCoef s β κ (2 * π / m)) →
      gradPsi κ (projC m (by omega) (aCoef s β κ (2 * π / m)) (bCoef s β κ (2 * π / m)))
          (xc (2 * π / m) t + u)
        = gradPsi κ (projC m (by omega) (aCoef s β κ (2 * π / m)) (bCoef s β κ (2 * π / m)))
          (xc (2 * π / m) t) + u :=
  theorem_3_1_ii_of_Pcyc m hm s β κ hs hβ1 hκ hP _ (isMetricProj_projC m (by omega) _ _)

end OBABO.Section3
