/-
The constants and the assembly of Theorem 5.1 of

  N. Bou-Rabee, Provable non-acceleration of standard Strang splittings of kinetic
  Langevin dynamics, arXiv:2608.25279.

The tuning `h = 1/(4 sqrt(kappa))`, `gamma = 4 sqrt(kappa)`, the constants `c_H`, `c_*`, `R_24`, the
numerical bounds (`147 kappa`, `8.62 sqrt(kappa)`, `143`, the exponent `c`), the case `n <= 24`, and the
assembly of the total variation bound (5.1). The contraction estimate of [30] and the
regularization estimate of [6] enter as hypotheses.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic

open Real

namespace OBABO
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
