/-
Lean formalization of the attracting neighborhood of the roots-of-unity cycle:
Theorem 3.1(ii) of

  N. Bou-Rabee, Provable non-acceleration of standard Strang splittings of kinetic
  Langevin dynamics, arXiv:2608.25279,

together with the deterministic invariant-tube argument behind Lemma 4.4(i)
(the "adapted norm and invariant ball").

The plane is modelled by `ℂ` with its real inner product `⟪w, z⟫_ℝ = Re(z * conj w)`.
Rotation by `θ_m = 2π/m` is multiplication by `ζ = exp(θ_m i)`, the cycle points are
`x°_j = ζ^j`, and the matrix `M = a Id + b J` of (3.4) is multiplication by `μ = a + b i`
(the matrix `J` is multiplication by `i`). Everything in the proof of Theorem 3.1(ii)
is therefore complex arithmetic plus the variational characterization of the metric
projection onto a convex set (`norm_eq_iInf_iff_real_inner_le_zero` in Mathlib).

Contents.
* Part A: the scalars `I_{0,j}` (3.9), their closed form, and the monotonicity (3.10).
* Part B: the radius `r_max` (3.13) and the projection inequalities on the balls
  `B(x°_t, r_max)`; the conclusion that `M x°_t` is the unique nearest point of
  `C = conv{M x°_j}` to every point of the ball; the local identity (3.8) for the
  gradient field `x ↦ x + (κ - 1) proj_C(x)` of (3.5).
* Part C: the link with Tier 1: `P_m(s, β; κ) < 0` gives `I_{0,1} < 0`, hence all
  `I_{0,j} < 0`, hence `r_max > 0`, which is Theorem 3.1(ii) in the form used in the paper.
* Part D: the deterministic invariant tube of Lemma 4.4(i): if the error recursion is
  linear inside the tube and the noise is small, the errors never leave the tube; and the
  derivation of the error recursion from (4.5), (4.6), (4.10).

Part (i) of Theorem 3.1 (the representation of ψ, imported from [22]) is not formalized;
the gradient field of ψ enters only through its formula `x + (κ - 1) proj_C(x)`.
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import StrangNonAcceleration.Tier1

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

/-- `I_{0,1}` in this file equals the scalar `I01` of Tier 1. -/
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

/-! ### Geometric decay from the spectral radius (Gelfand's formula)

Assumption 2 asks for `ρ(A_{m-1} ⋯ A_0) < 1`, and the paper deduces from Gelfand's formula
constants `C ≥ 1` and `q ∈ (0, 1)` with `‖M^n‖ ≤ C q^n`. This is the "adapted norm" step:
the norm `‖x‖_* = sup_n q^{-n} ‖M^n x‖` is equivalent to `‖·‖` and contracts `M` by the
factor `q`. We prove the geometric bound for any element of a complex Banach algebra, which
covers complex matrices with any operator norm, hence real matrices after complexification. -/

section Gelfand

open Filter Topology
open scoped ENNReal NNReal

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- If `spectralRadius ℂ a < 1`, then `‖a ^ n‖ ≤ C q ^ n` for some `C ≥ 1`, `q ∈ (0, 1)`. -/
theorem geometric_decay_of_spectralRadius_lt_one (a : A) (hρ : spectralRadius ℂ a < 1) :
    ∃ C q : ℝ, 0 < q ∧ q < 1 ∧ 1 ≤ C ∧ ∀ n : ℕ, ‖a ^ n‖ ≤ C * q ^ n := by
  obtain ⟨q, hq1, hq2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hρ
  have hq0 : (0 : ℝ) < q := by
    have : (0 : ℝ≥0∞) < q := lt_of_le_of_lt (by positivity) hq1
    exact_mod_cast this
  have hq1' : (q : ℝ) < 1 := by exact_mod_cast hq2
  have htend := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius a
  have hev : ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (‖a ^ n‖ ^ (1 / (n : ℝ))) < q :=
    htend.eventually_lt_const hq1
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  -- for n ≥ N + 1: ‖a^n‖ ≤ q^n
  have htail : ∀ n : ℕ, N + 1 ≤ n → ‖a ^ n‖ ≤ (q : ℝ) ^ n := by
    intro n hn
    have h1 := hN n (by omega)
    rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff hq0] at h1
    have hn0 : n ≠ 0 := by omega
    have hx : 0 ≤ ‖a ^ n‖ := norm_nonneg _
    have e : ‖a ^ n‖ = (‖a ^ n‖ ^ (1 / (n : ℝ))) ^ n := by
      rw [one_div, Real.rpow_inv_natCast_pow hx hn0]
    rw [e]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hx _) h1.le n
  -- the constant absorbing the first N + 1 terms
  set C := 1 + ∑ k ∈ Finset.range (N + 1), ‖a ^ k‖ / (q : ℝ) ^ k with hC
  have hC1 : 1 ≤ C := by
    rw [hC]
    have : 0 ≤ ∑ k ∈ Finset.range (N + 1), ‖a ^ k‖ / (q : ℝ) ^ k :=
      Finset.sum_nonneg fun k _ => div_nonneg (norm_nonneg _) (pow_nonneg hq0.le _)
    linarith
  refine ⟨C, q, hq0, hq1', hC1, fun n => ?_⟩
  rcases Nat.lt_or_ge n (N + 1) with hlt | hge
  · have hmem : n ∈ Finset.range (N + 1) := Finset.mem_range.mpr hlt
    have hterm : ‖a ^ n‖ / (q : ℝ) ^ n ≤ ∑ k ∈ Finset.range (N + 1), ‖a ^ k‖ / (q : ℝ) ^ k :=
      Finset.single_le_sum (f := fun k => ‖a ^ k‖ / (q : ℝ) ^ k)
        (fun k _ => div_nonneg (norm_nonneg _) (pow_nonneg hq0.le _)) hmem
    have hqn : 0 < (q : ℝ) ^ n := pow_pos hq0 n
    calc ‖a ^ n‖ = (‖a ^ n‖ / (q : ℝ) ^ n) * (q : ℝ) ^ n := (div_mul_cancel₀ _ hqn.ne').symm
      _ ≤ C * (q : ℝ) ^ n := by
          apply mul_le_mul_of_nonneg_right _ hqn.le
          rw [hC]; linarith
  · calc ‖a ^ n‖ ≤ (q : ℝ) ^ n := htail n hge
      _ ≤ C * (q : ℝ) ^ n := by
          have := pow_pos hq0 n
          nlinarith

end Gelfand

/-! ## D. The invariant tube of Lemma 4.4(i) -/

section Tube

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Products `Ψ(k, l) = A_{k-1} ⋯ A_l` of the error maps, defined recursively
(`Ψ(l, l) = Id`). -/
noncomputable def Ψ (A : ℕ → E →L[ℝ] E) : ℕ → ℕ → E →L[ℝ] E
  | 0, _ => ContinuousLinearMap.id ℝ E
  | k + 1, l => if l ≤ k then A k ∘L Ψ A k l else ContinuousLinearMap.id ℝ E

lemma Ψ_succ (A : ℕ → E →L[ℝ] E) (k l : ℕ) (h : l ≤ k) :
    Ψ A (k + 1) l = A k ∘L Ψ A k l := by
  simp [Ψ, h]

lemma Ψ_self (A : ℕ → E →L[ℝ] E) (k : ℕ) : Ψ A k k = ContinuousLinearMap.id ℝ E := by
  cases k with
  | zero => rfl
  | succ k => simp [Ψ]

/-- Duhamel formula: if the recursion `Err (i+1) = A i (Err i) + N (i+1)` holds for all
`i < k`, then `Err k = Ψ(k,0) Err 0 + ∑_{i=1}^{k} Ψ(k,i) N i`. -/
theorem duhamel (A : ℕ → E →L[ℝ] E) (Err N : ℕ → E) (k : ℕ)
    (hrec : ∀ i < k, Err (i + 1) = A i (Err i) + N (i + 1)) :
    Err k = Ψ A k 0 (Err 0) + ∑ i ∈ Finset.Icc 1 k, Ψ A k i (N i) := by
  induction k with
  | zero => simp [Ψ]
  | succ k ih =>
    have ih' := ih (fun i hi => hrec i (by omega))
    rw [hrec k (by omega), ih', map_add, map_sum, Finset.sum_Icc_succ_top (by omega),
      Ψ_succ A k 0 (by omega), ContinuousLinearMap.comp_apply]
    have hcongr : ∀ i ∈ Finset.Icc 1 k, A k (Ψ A k i (N i)) = Ψ A (k + 1) i (N i) := by
      intro i hi
      rw [Finset.mem_Icc] at hi
      rw [Ψ_succ A k i hi.2, ContinuousLinearMap.comp_apply]
    rw [Finset.sum_congr rfl hcongr, Ψ_self]
    simp only [ContinuousLinearMap.id_apply]
    abel

/-- **The invariant tube (Lemma 4.4(i), deterministic core).** Suppose the error recursion
`Err (i+1) = A i (Err i) + N (i+1)` holds whenever `‖Err i‖ ≤ ρ` (the local linear identity
(4.6) is available inside the tube), that `‖Ψ(k,0)‖ ≤ C` with `C ≥ 1` and
`∑_{i=1}^k ‖Ψ(k,i)‖ ‖N i‖ ≤ G₀ δ' R` for `k ≤ n`, that `‖Err 0‖ ≤ ε₀ R`, and that
`C ε₀ R + G₀ δ' R ≤ ρ` (this is (4.12) with `ρ = aR/2`). Then `‖Err k‖ ≤ ρ` for all
`k ≤ n`. -/
theorem invariant_tube (A : ℕ → E →L[ℝ] E) (Err N : ℕ → E) (n : ℕ) (ρ C ε₀ G₀ δ' R : ℝ)
    (hrec : ∀ i < n, ‖Err i‖ ≤ ρ → Err (i + 1) = A i (Err i) + N (i + 1))
    (hC1 : 1 ≤ C) (hC : ∀ k ≤ n, ‖Ψ A k 0‖ ≤ C)
    (hG : ∀ k ≤ n, ∑ i ∈ Finset.Icc 1 k, ‖Ψ A k i‖ * ‖N i‖ ≤ G₀ * δ' * R)
    (h0 : ‖Err 0‖ ≤ ε₀ * R)
    (hcond : C * (ε₀ * R) + G₀ * δ' * R ≤ ρ) :
    ∀ k ≤ n, ‖Err k‖ ≤ ρ := by
  have hG0 : 0 ≤ G₀ * δ' * R := by
    have := hG 0 (by omega); simpa using this
  have hε : 0 ≤ ε₀ * R := (norm_nonneg _).trans h0
  have key : ∀ k ≤ n, ∀ i ≤ k, ‖Err i‖ ≤ ρ := by
    intro k
    induction k with
    | zero =>
      intro _ i hi
      have hi0 : i = 0 := by omega
      subst hi0
      calc ‖Err 0‖ ≤ ε₀ * R := h0
        _ ≤ C * (ε₀ * R) + G₀ * δ' * R := by nlinarith
        _ ≤ ρ := hcond
    | succ k ih =>
      intro hk i hi
      have ih' := ih (by omega)
      rcases Nat.lt_or_ge i (k + 1) with hlt | hge
      · exact ih' i (by omega)
      · have hik : i = k + 1 := by omega
        subst hik
        have hrec' : ∀ j < k + 1, Err (j + 1) = A j (Err j) + N (j + 1) :=
          fun j hj => hrec j (by omega) (ih' j (by omega))
        rw [duhamel A Err N (k + 1) hrec']
        have hCk := hC (k + 1) hk
        have hGk := hG (k + 1) hk
        calc ‖Ψ A (k + 1) 0 (Err 0) + ∑ i ∈ Finset.Icc 1 (k + 1), Ψ A (k + 1) i (N i)‖
            ≤ ‖Ψ A (k + 1) 0 (Err 0)‖ + ‖∑ i ∈ Finset.Icc 1 (k + 1), Ψ A (k + 1) i (N i)‖ :=
              norm_add_le _ _
          _ ≤ ‖Ψ A (k + 1) 0‖ * ‖Err 0‖
                + ∑ i ∈ Finset.Icc 1 (k + 1), ‖Ψ A (k + 1) i‖ * ‖N i‖ :=
              add_le_add (ContinuousLinearMap.le_opNorm _ _)
                ((norm_sum_le _ _).trans
                  (Finset.sum_le_sum fun i _ => ContinuousLinearMap.le_opNorm _ _))
          _ ≤ C * (ε₀ * R) + G₀ * δ' * R :=
              add_le_add
                (mul_le_mul hCk h0 (norm_nonneg _) ((norm_nonneg _).trans hCk)) hGk
          _ ≤ ρ := hcond
  exact fun k hk => key k hk k le_rfl

end Tube

/-! ### The error recursion of Lemma 4.4 from (4.5), (4.6), (4.10) -/

section ErrorRecursion

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Derivation of the error recursion in the proof of Lemma 4.4. Let `Y` be the noisy
heavy-ball sequence (4.10) with noise `ζ`, let `x` be the cycle (4.5), dilated by `R`
(so `R • x` solves the noiseless recursion with the dilated gradient `gU`), and suppose the
dilated local identity (4.6), `gU (R x k + u) = gU (R x k) + H k u`, holds at the current
error `u = Y k - R x k`. Then the next error is an affine function of the two previous
errors plus the noise: this is `E_{i+1} = A_{j+i} E_i + B ζ_{i+1}`. Indices are shifted by
one: `Y (k + 1)` is the paper's `Y_k` and `x (k + 1)` the paper's `x°_{j+k}`. -/
theorem error_recursion (β s : ℝ) (Y x : ℕ → E) (gU : E → E) (ζ : ℕ → E)
    (H : ℕ → E →ₗ[ℝ] E) (R : ℝ) (k : ℕ)
    (h410 : Y (k + 2) = (1 + β) • Y (k + 1) - β • Y k - s • gU (Y (k + 1)) + ζ (k + 1))
    (h45 : R • x (k + 2) = (1 + β) • (R • x (k + 1)) - β • (R • x k) - s • gU (R • x (k + 1)))
    (h46 : gU (Y (k + 1)) = gU (R • x (k + 1)) + H (k + 1) (Y (k + 1) - R • x (k + 1))) :
    Y (k + 2) - R • x (k + 2)
      = (1 + β) • (Y (k + 1) - R • x (k + 1)) - s • H (k + 1) (Y (k + 1) - R • x (k + 1))
        - β • (Y k - R • x k) + ζ (k + 1) := by
  rw [h410, h45, h46]
  simp only [smul_add, smul_sub]
  abel

end ErrorRecursion

/-! ## E. Lemma 3.3, Steps 2 and 3 (the parts not depending on [22]) -/

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
nonnegative. (The theorem `s_plus_3_ge` of Tier 1 proves the non-strict bound by a
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
