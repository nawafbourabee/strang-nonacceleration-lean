/-
Lemma 3.2 of

  N. Bou-Rabee, Provable non-acceleration of standard Strang splittings of kinetic
  Langevin dynamics, arXiv:2608.25279.

Lemma 3.2 in full: the thresholds `s_±(β, m; κ)` and `β_-(m; κ)` of [22, Notation B.1] are
defined from the cycling quadratic, the two facts the paper imports from [22] (Lemma B.2 and
the elementary bound from the proof of Lemma B.6 via Lemma B.7) are proved here, and the
overlap inequality (3.14) is proved for every `m ≥ 3` following the paper's argument, with
the case `m = 3` and the elementary steps (3.15) to (3.18) of the case `m ≥ 4` as separate
lemmas.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import StrangNonAcceleration.Theorem3_1

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

/-! ## Lemma 3.2 in full

The thresholds `s_±(β, m; κ)` of the paper are the roots of `s ↦ P_m(s, β; κ)`, written as
`A_m ± B_m` in (3.15) with `A_m = β - cos θ_m + u(1 - β cos θ_m)` and
`B_m² = A_m² - 2u(1 - cos θ_m)(1 + β² - 2β cos θ_m)`, `u = κ⁻¹`. The threshold `β_-(m; κ)`
of [22, Notation B.1] is the larger root of `β ↦ B_m²` (a quadratic in `β` with positive
leading coefficient for `u < 1/2`), so that `B_m² ≥ 0` for `β ≥ β_-(m; κ)`.

The two facts imported from [22] in the paper's proof are proved here:
`βMinus_ge` is the lower bound `β_-(m+1; κ) ≥ cos θ_{m+1} (1 + √u ξ_{m+1})` of [22, Lemma B.2],
and `xi_bound` is the bound `ξ_{m+1} + 2(1 - cos θ_m)/ξ_{m+1} ≤ 3 + √5` for `m ≥ 4` that the
paper takes from the proof of [22, Lemma B.6] via [22, Lemma B.7]. -/

/-- `θ_m = 2π/m`. -/
noncomputable def θm (m : ℕ) : ℝ := 2 * π / m

/-- `A_m` of (3.15), as a function of `c = cos θ_m`, with `u = κ⁻¹`. -/
noncomputable def Acoef (β κ c : ℝ) : ℝ := β - c + κ⁻¹ * (1 - β * c)

/-- `B_m²` of (3.15): the discriminant of `s ↦ P_m(s, β; κ)` (divided by 4). -/
noncomputable def Disc (β κ c : ℝ) : ℝ :=
  Acoef β κ c ^ 2 - 2 * κ⁻¹ * (1 - c) * (1 + β ^ 2 - 2 * β * c)

/-- `s_-(β, m; κ) = A_m - B_m`. -/
noncomputable def sMinus (β κ : ℝ) (m : ℕ) : ℝ :=
  Acoef β κ (cos (θm m)) - √(Disc β κ (cos (θm m)))

/-- `s_+(β, m; κ) = A_m + B_m`. -/
noncomputable def sPlus (β κ : ℝ) (m : ℕ) : ℝ :=
  Acoef β κ (cos (θm m)) + √(Disc β κ (cos (θm m)))

/-- `P_m(s, β; κ) = (s - s_-)(s - s_+)` when the roots are real. -/
theorem Pcyc_eq_mul_roots (s β κ : ℝ) (m : ℕ) (h : 0 ≤ Disc β κ (cos (θm m))) :
    Pcyc s β κ (cos (θm m)) = (s - sMinus β κ m) * (s - sPlus β κ m) := by
  have hS := Real.sq_sqrt h
  unfold sMinus sPlus Pcyc
  unfold Disc Acoef at hS ⊢
  linear_combination hS

/-- The coefficients of `β ↦ B_m²` as a quadratic `a β² + b β + e`. -/
noncomputable def discA (u c : ℝ) : ℝ := 1 - 2 * u + c ^ 2 * u ^ 2
noncomputable def discB (u c : ℝ) : ℝ :=
  -2 * c + 2 * u + 4 * c * u - 2 * c ^ 2 * u - 2 * c * u ^ 2
noncomputable def discC (u c : ℝ) : ℝ := c ^ 2 - 2 * u + u ^ 2

theorem Disc_eq (β κ c : ℝ) :
    Disc β κ c = discA κ⁻¹ c * β ^ 2 + discB κ⁻¹ c * β + discC κ⁻¹ c := by
  unfold Disc Acoef discA discB discC; ring

/-- `β_-(m; κ)`: the larger root of `β ↦ B_m²` ([22, Notation B.1]). -/
noncomputable def βMinus (κ : ℝ) (m : ℕ) : ℝ :=
  (-discB κ⁻¹ (cos (θm m)) +
      √(discB κ⁻¹ (cos (θm m)) ^ 2 - 4 * discA κ⁻¹ (cos (θm m)) * discC κ⁻¹ (cos (θm m)))) /
    (2 * discA κ⁻¹ (cos (θm m)))

theorem discA_pos (u c : ℝ) (hu : u < 1 / 2) : 0 < discA u c := by
  unfold discA; nlinarith [sq_nonneg (c * u)]

/-- `4a(aβ² + bβ + e) = (2aβ + b)² - (b² - 4ae)`. -/
theorem four_mul_quadratic (a b e β : ℝ) :
    4 * a * (a * β ^ 2 + b * β + e) = (2 * a * β + b) ^ 2 - (b ^ 2 - 4 * a * e) := by ring

/-- `B_m² ≥ 0` for `β ≥ β_-(m; κ)` (the roots `s_±` are real). -/
theorem Disc_nonneg_of_βMinus_le (β κ : ℝ) (m : ℕ) (hu : κ⁻¹ < 1 / 2)
    (hβ : βMinus κ m ≤ β) : 0 ≤ Disc β κ (cos (θm m)) := by
  set u := κ⁻¹
  set c := cos (θm m)
  have ha := discA_pos u c hu
  set a := discA u c
  set b := discB u c
  set e := discC u c
  rw [Disc_eq]
  unfold βMinus at hβ
  rw [div_le_iff₀ (by linarith)] at hβ
  have hs : 0 ≤ √(b ^ 2 - 4 * a * e) := Real.sqrt_nonneg _
  have h1 : b ^ 2 - 4 * a * e ≤ (2 * a * β + b) ^ 2 := by
    rcases le_or_gt 0 (b ^ 2 - 4 * a * e) with h | h
    · have := Real.sq_sqrt h
      nlinarith [sq_nonneg (2 * a * β + b - √(b ^ 2 - 4 * a * e))]
    · nlinarith [sq_nonneg (2 * a * β + b)]
  have h2 := four_mul_quadratic a b e β
  nlinarith

/-- If `B_m²(β₀) ≤ 0` then `β₀ ≤ β_-(m; κ)`. -/
theorem le_βMinus_of_Disc_nonpos (β₀ κ : ℝ) (m : ℕ) (hu : κ⁻¹ < 1 / 2)
    (h : Disc β₀ κ (cos (θm m)) ≤ 0) : β₀ ≤ βMinus κ m := by
  set u := κ⁻¹
  set c := cos (θm m)
  have ha := discA_pos u c hu
  set a := discA u c
  set b := discB u c
  set e := discC u c
  rw [Disc_eq] at h
  unfold βMinus
  rw [le_div_iff₀ (by linarith)]
  have h2 := four_mul_quadratic a b e β₀
  have h3 : (2 * a * β₀ + b) ^ 2 ≤ b ^ 2 - 4 * a * e := by nlinarith
  have h4 := Real.abs_le_sqrt h3
  have h5 := le_abs_self (2 * a * β₀ + b)
  linarith

/-- The discriminant at `β₀ = c + r(1 - c)`, `u = r²`, is nonpositive for `0 < c ≤ 1` and
`0 < r ≤ 1/5` (the computation behind [22, Lemma B.2]). -/
theorem Disc_at_β0_nonpos (κ c r : ℝ) (hκ : κ⁻¹ = r ^ 2) (hr0 : 0 < r) (hr : r ≤ 1 / 5)
    (hc0 : 0 < c) (hc1 : c ≤ 1) :
    Disc (c + r * (1 - c)) κ c ≤ 0 := by
  unfold Disc Acoef
  rw [hκ]
  have hr2 : r ^ 2 ≤ 1 / 25 := by nlinarith
  have hr3 : r ^ 3 ≤ 1 / 125 := by nlinarith [pow_nonneg hr0.le 2]
  have hr4 : r ^ 4 ≤ 1 / 625 := by nlinarith [pow_nonneg hr0.le 3, pow_nonneg hr0.le 2]
  have hc2 : c ^ 2 ≤ c := by nlinarith
  have key : (1 - c) ^ 2 * r ^ 2 *
      (-(1 + 2 * c) + 2 * r * (1 + c) + r ^ 2 * (c ^ 2 + 2 * c - 1)
        - 2 * c * r ^ 3 * (c + 1) + c ^ 2 * r ^ 4) =
      (c + r * (1 - c) - c + r ^ 2 * (1 - (c + r * (1 - c)) * c)) ^ 2 -
        2 * r ^ 2 * (1 - c) * (1 + (c + r * (1 - c)) ^ 2 - 2 * (c + r * (1 - c)) * c) := by
    ring
  rw [← key]
  apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
  have h1 : 2 * r * (1 + c) ≤ 2 / 5 * (1 + c) := by nlinarith
  have h2 : r ^ 2 * (c ^ 2 + 2 * c - 1) ≤ r ^ 2 * (c ^ 2 + 2 * c) := by nlinarith [sq_nonneg r]
  have h3 : r ^ 2 * (c ^ 2 + 2 * c) ≤ 1 / 25 * (c ^ 2 + 2 * c) := by nlinarith
  have h4 : 0 ≤ 2 * c * r ^ 3 * (c + 1) := by positivity
  have h5 : c ^ 2 * r ^ 4 ≤ 1 / 625 * c ^ 2 := by nlinarith
  nlinarith

/-- `0 < θ_m ≤ 2π/3` for `m ≥ 3`. -/
theorem θm_pos (m : ℕ) (hm : 1 ≤ m) : 0 < θm m := by
  unfold θm
  have : (1 : ℝ) ≤ m := by exact_mod_cast hm
  positivity

theorem θm_le (m : ℕ) (hm : 3 ≤ m) : θm m ≤ 2 * π / 3 := by
  unfold θm
  have : (3 : ℝ) ≤ m := by exact_mod_cast hm
  exact div_le_div_of_nonneg_left (by positivity) (by norm_num) this

theorem θm_succ_lt (m : ℕ) (hm : 1 ≤ m) : θm (m + 1) < θm m := by
  unfold θm
  have : (1 : ℝ) ≤ m := by exact_mod_cast hm
  push_cast
  exact div_lt_div_of_pos_left (by positivity) (by linarith) (by linarith)

/-- `cos θ_m < cos θ_{m+1}` for `m ≥ 3`. -/
theorem cos_θm_lt (m : ℕ) (hm : 3 ≤ m) : cos (θm m) < cos (θm (m + 1)) := by
  apply Real.cos_lt_cos_of_nonneg_of_le_pi (θm_pos (m + 1) (Nat.le_add_left 1 m)).le
  · linarith [θm_le m hm, Real.pi_pos]
  · exact θm_succ_lt m (by omega)

theorem cos_θm_lt_one (m : ℕ) (hm : 2 ≤ m) : cos (θm m) < 1 := by
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ)) (y := θm m) ?_ (θm_pos m (by omega))
  · simpa using h
  · unfold θm
    have : (2 : ℝ) ≤ m := by exact_mod_cast (by omega : 2 ≤ m)
    rw [div_le_iff₀ (by positivity)]; nlinarith [Real.pi_pos]

/-- `cos θ_{m+1} > 0` for `m ≥ 4` (`θ_{m+1} ≤ 2π/5 < π/2`). -/
theorem cos_θm_succ_pos (m : ℕ) (hm : 4 ≤ m) : 0 < cos (θm (m + 1)) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · linarith [θm_pos (m + 1) (by omega), Real.pi_pos]
  · unfold θm
    have : (5 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast (by omega : 5 ≤ m + 1)
    rw [div_lt_iff₀ (by positivity)]; nlinarith [Real.pi_pos]

/-- `cos θ_{m+1} ≥ 1/2` for `m ≥ 5` (`θ_{m+1} ≤ π/3`). -/
theorem cos_θm_succ_ge_half (m : ℕ) (hm : 5 ≤ m) : 1 / 2 ≤ cos (θm (m + 1)) := by
  rw [← Real.cos_pi_div_three]
  apply Real.cos_le_cos_of_nonneg_of_le_pi (θm_pos (m + 1) (by omega)).le
  · linarith [Real.pi_pos]
  · unfold θm
    have : (6 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast (by omega : 6 ≤ m + 1)
    rw [div_le_iff₀ (by positivity)]; nlinarith [Real.pi_pos]

/-- `1 - cos θ_m = 2 sin²(π/m)`. -/
theorem one_sub_cos_θm (m : ℕ) : 1 - cos (θm m) = 2 * sin (π / m) ^ 2 := by
  have h : θm m = 2 * (π / m) := by unfold θm; ring
  rw [h, Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq (π / m)]

/-- Concavity of `sin` on `[0, π]`: `sin(π/(m+1)) ≥ (m/(m+1)) sin(π/m)` for `m ≥ 1`. -/
theorem sin_succ_ge (m : ℕ) (hm : 1 ≤ m) :
    (m : ℝ) / (m + 1) * sin (π / m) ≤ sin (π / (m + 1)) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hx : (0 : ℝ) ∈ Set.Icc 0 π := ⟨le_rfl, Real.pi_pos.le⟩
  have hy : π / m ∈ Set.Icc 0 π := by
    constructor
    · positivity
    · exact div_le_self Real.pi_pos.le hm'
  have ha : (0 : ℝ) ≤ 1 / (m + 1) := by positivity
  have hb : (0 : ℝ) ≤ m / (m + 1) := by positivity
  have hab : (1 : ℝ) / (m + 1) + m / (m + 1) = 1 := by field_simp; ring
  have := strictConcaveOn_sin_Icc.concaveOn.2 hx hy ha hb hab
  simp only [smul_eq_mul, mul_zero, Real.sin_zero, zero_add] at this
  have heq : (m : ℝ) / (m + 1) * (π / m) = π / (m + 1) := by field_simp
  rw [heq] at this
  exact this

/-- `1 - cos θ_m ≤ ((m+1)/m)² (1 - cos θ_{m+1})` for `m ≥ 1`. -/
theorem one_sub_cos_ratio (m : ℕ) (hm : 1 ≤ m) :
    1 - cos (θm m) ≤ ((m + 1 : ℝ) / m) ^ 2 * (1 - cos (θm (m + 1))) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [one_sub_cos_θm, one_sub_cos_θm]
  push_cast
  have h := sin_succ_ge m hm
  have hs : 0 ≤ sin (π / m) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
    exact div_le_self Real.pi_pos.le hm'
  have h2 : ((m : ℝ) / (m + 1) * sin (π / m)) ^ 2 ≤ sin (π / (m + 1)) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity) h
  have hpos : (0 : ℝ) < m + 1 := by positivity
  have hm0 : (0 : ℝ) < m := by linarith
  have key : ((m + 1 : ℝ) / m) ^ 2 * ((m : ℝ) / (m + 1) * sin (π / m)) ^ 2 = sin (π / m) ^ 2 := by
    field_simp
  nlinarith [mul_le_mul_of_nonneg_left h2 (le_of_lt (pow_pos (div_pos hpos hm0) 2))]

/-- [22, Lemma B.2] in the form used by the paper: `β_-(m+1; κ) ≥ cos θ_{m+1} (1 + √u ξ_{m+1})`
with `ξ_{m+1} = 1/cos θ_{m+1} - 1`, that is `β_-(m+1; κ) ≥ c + √u (1 - c)`, for `m ≥ 4` and
`√u ≤ 1/5`. -/
theorem βMinus_ge (m : ℕ) (hm : 4 ≤ m) (κ r : ℝ) (hκ : κ⁻¹ = r ^ 2) (hr0 : 0 < r)
    (hr : r ≤ 1 / 5) :
    cos (θm (m + 1)) + r * (1 - cos (θm (m + 1))) ≤ βMinus κ (m + 1) := by
  have hc0 := cos_θm_succ_pos m hm
  have hc1 := cos_θm_lt_one (m + 1) (by omega)
  apply le_βMinus_of_Disc_nonpos _ _ _ (by rw [hκ]; nlinarith)
  exact Disc_at_β0_nonpos κ _ r hκ hr0 hr hc0 hc1.le

/-- `ξ_5 = 1/cos θ_5 - 1 = √5`. -/
theorem xi_five : (1 - cos (θm 5)) / cos (θm 5) = √5 := by
  have h : θm 5 = 2 * π / 5 := by unfold θm; norm_num
  rw [h, cos_two_pi_div_five]
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < √5 - 1 := by have := sqrt5_bounds.1; linarith
  field_simp
  nlinarith

/-- The bound `ξ_{m+1} + 2(1 - cos θ_m)/ξ_{m+1} ≤ 3 + √5` for `m ≥ 4`, with
`ξ_{m+1} = 1/cos θ_{m+1} - 1` (the elementary bound in the proof of [22, Lemma B.6]). -/
theorem xi_bound (m : ℕ) (hm : 4 ≤ m) :
    (1 - cos (θm (m + 1))) / cos (θm (m + 1)) +
      2 * (1 - cos (θm m)) / ((1 - cos (θm (m + 1))) / cos (θm (m + 1))) ≤ 3 + √5 := by
  have hc0 := cos_θm_succ_pos m hm
  have hc1 := cos_θm_lt_one (m + 1) (by omega)
  set c := cos (θm (m + 1)) with hc
  have hxi : 0 < (1 - c) / c := by positivity
  have h5 := sqrt5_bounds
  rcases Nat.eq_or_lt_of_le hm with h4 | h5'
  · -- m = 4: ξ_5 = √5 and cos θ_4 = 0
    subst h4
    have hc5 : (1 - c) / c = √5 := xi_five
    have hd : cos (θm 4) = 0 := by
      have : θm 4 = π / 2 := by unfold θm; ring
      rw [this, Real.cos_pi_div_two]
    rw [hc5, hd]
    have h5' : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have hpos : 0 < √5 := by positivity
    have : 2 * (1 - 0) / √5 ≤ 3 := by rw [div_le_iff₀ hpos]; nlinarith
    linarith
  · -- m ≥ 5: ξ ≤ 1 and (1 - cos θ_m) ≤ (36/25)(1 - cos θ_{m+1})
    have hhalf := cos_θm_succ_ge_half m h5'
    have hxi1 : (1 - c) / c ≤ 1 := by rw [div_le_one hc0]; linarith
    have hratio := one_sub_cos_ratio m (by omega)
    have hm5 : (5 : ℝ) ≤ m := by exact_mod_cast h5'
    have hfrac : ((m + 1 : ℝ) / m) ^ 2 ≤ 36 / 25 := by
      have : (m + 1 : ℝ) / m ≤ 6 / 5 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
      have h0 : (0 : ℝ) ≤ (m + 1 : ℝ) / m := by positivity
      nlinarith
    have hd : 1 - cos (θm m) ≤ 36 / 25 * (1 - c) := by
      have h0 : 0 ≤ 1 - c := by linarith
      nlinarith
    have hterm : 2 * (1 - cos (θm m)) / ((1 - c) / c) ≤ 72 / 25 := by
      rw [div_le_iff₀ hxi]
      have : 2 * (1 - cos (θm m)) ≤ 72 / 25 * (1 - c) := by linarith
      calc 2 * (1 - cos (θm m)) ≤ 72 / 25 * (1 - c) := this
        _ = 72 / 25 * ((1 - c) / c) * c := by field_simp
        _ ≤ 72 / 25 * ((1 - c) / c) := by nlinarith
    linarith

/-- (3.17) in the cleared form `2(1 + β²u²) c - 4βu d < 2β(1 - u)²`, case `m = 3`
(`c = cos θ_4 = 0`, `d = cos θ_3 = -1/2`). -/
theorem key_m3 (β u : ℝ) (hβ0 : 0 < β) (hu : u < ((3 - √5) / 4) ^ 2) :
    2 * (1 + β ^ 2 * u ^ 2) * 0 - 4 * β * u * (-1 / 2) < 2 * β * (1 - u) ^ 2 := by
  have := lemma_3_2_m3' u hu
  nlinarith

/-- The map `t ↦ t + 1/t` is antitone on `(0, 1]`: for `0 < s ≤ t ≤ 1`, `t + 1/t ≤ s + 1/s`. -/
theorem add_inv_antitone (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) (ht : t ≤ 1) :
    t + 1 / t ≤ s + 1 / s := by
  have ht0 : 0 < t := by linarith
  have key : (s + 1 / s) - (t + 1 / t) = (t - s) * (1 - s * t) / (s * t) := by
    field_simp; ring
  rw [← sub_nonneg, key]
  apply div_nonneg _ (by positivity)
  apply mul_nonneg (by linarith)
  nlinarith [mul_le_mul hst ht ht0.le ht0.le]

/-- (3.17) in the cleared form, case `m ≥ 4`. -/
theorem key_ge4 (m : ℕ) (hm : 4 ≤ m) (β κ : ℝ) (hκ0 : 0 < κ)
    (hκ : κ⁻¹ < ((3 - √5) / 4) ^ 2) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : βMinus κ (m + 1) ≤ β) :
    2 * (1 + β ^ 2 * κ⁻¹ ^ 2) * cos (θm (m + 1)) - 4 * β * κ⁻¹ * cos (θm m)
      < 2 * β * (1 - κ⁻¹) ^ 2 := by
  have hu0 : 0 < κ⁻¹ := inv_pos.2 hκ0
  set u := κ⁻¹ with hu_def
  set r := √u with hr_def
  have h5 := sqrt5_bounds
  have hr0 : 0 < r := Real.sqrt_pos.2 hu0
  have hur : u = r ^ 2 := (Real.sq_sqrt hu0.le).symm
  have hr : r < (3 - √5) / 4 := by
    rw [hr_def, Real.sqrt_lt' (by nlinarith)]; exact hκ
  have hr5 : r ≤ 1 / 5 := by nlinarith
  have hu' : u < 1 / 2 := by nlinarith
  have hc0 := cos_θm_succ_pos m hm
  have hc1 := cos_θm_lt_one (m + 1) (by omega)
  have hcd := cos_θm_lt m (by omega)
  set c := cos (θm (m + 1)) with hc
  set d := cos (θm m) with hd
  -- β₀ = c + r(1 - c) = c (1 + r ξ), and β ≥ β₀ by [22, Lemma B.2]
  set β₀ := c + r * (1 - c) with hβ₀
  have hβ₀pos : 0 < β₀ := by positivity
  have hβ₀le : β₀ ≤ 1 := by nlinarith
  have hβ₀β : β₀ ≤ β := le_trans (βMinus_ge m hm κ r hur hr0 hr5) hβ
  -- the inequality at β₀: c/β₀ + c β₀ u² < (1 - u)² + 2ud
  set ξ := (1 - c) / c with hξ
  have hξpos : 0 < ξ := by positivity
  have hβ₀ξ : β₀ = c * (1 + r * ξ) := by rw [hξ, hβ₀]; field_simp
  have hB7 := xi_bound m hm
  rw [← hξ] at hB7
  have h1r : 3 + √5 < 1 / r := by
    rw [lt_div_iff₀ hr0]
    have : (3 + √5) * ((3 - √5) / 4) = 1 := by nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)]
    nlinarith
  have h18 : ξ + 2 * (1 - d) / ξ < 1 / r := lt_of_le_of_lt hB7 h1r
  have h18' : r * ξ ^ 2 + 2 * r * (1 - d) < ξ := by
    have := (lt_div_iff₀ hr0).1 h18
    have h2 : 2 * (1 - d) / ξ * ξ = 2 * (1 - d) := by field_simp
    nlinarith
  have hA : c / β₀ ≤ 1 - r * ξ + r ^ 2 * ξ ^ 2 := by
    have : c / β₀ = 1 / (1 + r * ξ) := by rw [hβ₀ξ]; field_simp
    rw [this]
    have h1 := one_div_one_add_le (r * ξ) (by positivity)
    have h2 : (r * ξ) ^ 2 = r ^ 2 * ξ ^ 2 := by ring
    linarith
  have hB : c * β₀ * u ^ 2 ≤ u ^ 2 := by
    have h1 : c * β₀ ≤ 1 := mul_le_one₀ hc1.le hβ₀pos.le hβ₀le
    calc c * β₀ * u ^ 2 ≤ 1 * u ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg u)
      _ = u ^ 2 := one_mul _
  have hC : r ^ 2 * ξ ^ 2 + 2 * r ^ 2 * (1 - d) < r * ξ := by
    have h1 := mul_lt_mul_of_pos_left h18' hr0
    calc r ^ 2 * ξ ^ 2 + 2 * r ^ 2 * (1 - d) = r * (r * ξ ^ 2 + 2 * r * (1 - d)) := by ring
      _ < r * ξ := h1
  have hat_β₀ : c / β₀ + c * β₀ * u ^ 2 < (1 - u) ^ 2 + 2 * u * d := by
    have : (1 - u) ^ 2 + 2 * u * d = 1 - 2 * r ^ 2 * (1 - d) + u ^ 2 := by rw [hur]; ring
    rw [this]
    have hr2 : r ^ 2 = u := hur.symm
    rw [← hr2] at hB ⊢
    linarith
  -- monotonicity in β: t ↦ t + 1/t is antitone on (0, 1]
  have hβu1 : β * u ≤ 1 := by
    calc β * u ≤ 1 * 1 := mul_le_mul hβ1.le (by linarith) hu0.le zero_le_one
      _ = 1 := one_mul 1
  have hmono : β * u + 1 / (β * u) ≤ β₀ * u + 1 / (β₀ * u) :=
    add_inv_antitone (β₀ * u) (β * u) (by positivity)
      (mul_le_mul_of_nonneg_right hβ₀β hu0.le) hβu1
  -- assemble: divide the target by 2βu > 0
  have hβu : 0 < β * u := by positivity
  have htarget : c * (β * u + 1 / (β * u)) < (1 - u) ^ 2 / u + 2 * d := by
    have e1 : c * (β₀ * u + 1 / (β₀ * u)) = (c / β₀ + c * β₀ * u ^ 2) / u := by
      field_simp; ring
    have e2 : (1 - u) ^ 2 / u + 2 * d = ((1 - u) ^ 2 + 2 * u * d) / u := by
      field_simp
    have : c * (β * u + 1 / (β * u)) ≤ c * (β₀ * u + 1 / (β₀ * u)) :=
      mul_le_mul_of_nonneg_left hmono hc0.le
    rw [e1] at this
    rw [e2]
    calc c * (β * u + 1 / (β * u)) ≤ (c / β₀ + c * β₀ * u ^ 2) / u := this
      _ < ((1 - u) ^ 2 + 2 * u * d) / u := by
        exact div_lt_div_of_pos_right hat_β₀ hu0
  have e3 : 2 * (1 + β ^ 2 * u ^ 2) * c - 4 * β * u * d
      = 2 * β * u * (c * (β * u + 1 / (β * u)) - 2 * d) := by
    field_simp; ring
  have e4 : 2 * β * (1 - u) ^ 2 = 2 * β * u * ((1 - u) ^ 2 / u) := by
    field_simp
  rw [e3, e4]
  apply mul_lt_mul_of_pos_left _ (by positivity)
  linarith

/-- **Lemma 3.2** (overlap of consecutive intervals). For `κ⁻¹ < ((3 - √5)/4)²`, every
`m ≥ 3` and every `β ∈ (0, 1)` with `β ≥ β_-(m+1; κ)`,
`s_-(β, m; κ) < s_+(β, m+1; κ)`, inequality (3.14). -/
theorem lemma_3_2 (m : ℕ) (hm : 3 ≤ m) (β κ : ℝ) (hκ0 : 0 < κ)
    (hκ : κ⁻¹ < ((3 - √5) / 4) ^ 2) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : βMinus κ (m + 1) ≤ β) :
    sMinus β κ m < sPlus β κ (m + 1) := by
  have hu0 : 0 < κ⁻¹ := inv_pos.2 hκ0
  set u := κ⁻¹ with hu_def
  have h5 := sqrt5_bounds
  have hu' : u < 1 / 2 := by nlinarith
  have hcd := cos_θm_lt m hm
  set c := cos (θm (m + 1)) with hc
  set d := cos (θm m) with hd
  -- (3.17) in cleared form
  have key17 : 2 * (1 + β ^ 2 * u ^ 2) * c - 4 * β * u * d < 2 * β * (1 - u) ^ 2 := by
    rcases Nat.eq_or_lt_of_le hm with h3 | h4
    · subst h3
      have hc0 : c = 0 := by
        have : θm 4 = π / 2 := by unfold θm; ring
        rw [hc, this, Real.cos_pi_div_two]
      have hd0 : d = -1 / 2 := by
        have h1 : θm 3 = π - π / 3 := by unfold θm; ring
        rw [hd, h1, Real.cos_pi_sub, Real.cos_pi_div_three]; norm_num
      rw [hc0, hd0]
      exact key_m3 β u hβ0 hκ
    · exact key_ge4 m (by omega) β κ hκ0 hκ hβ0 hβ1 hβ
  -- (3.16): (A_m - A_{m+1})² < B_m² - B_{m+1}²
  have hAdiff : Acoef β κ d - Acoef β κ c = (1 + β * u) * (c - d) := by
    unfold Acoef; ring
  have hDdiff : Disc β κ d - Disc β κ c
      = (2 * β * (1 - u) ^ 2 - (1 - β * u) ^ 2 * (c + d)) * (c - d) := by
    unfold Disc Acoef; ring
  have h16 : (Acoef β κ d - Acoef β κ c) ^ 2 < Disc β κ d - Disc β κ c := by
    rw [hAdiff, hDdiff]
    have hpos : 0 < c - d := by linarith
    have : (1 + β * u) ^ 2 * (c - d) + (1 - β * u) ^ 2 * (c + d) < 2 * β * (1 - u) ^ 2 := by
      nlinarith [key17]
    nlinarith [mul_lt_mul_of_pos_right this hpos]
  have hDc : 0 ≤ Disc β κ c := Disc_nonneg_of_βMinus_le β κ (m + 1) hu' hβ
  have hDd : (Acoef β κ d - Acoef β κ c) ^ 2 < Disc β κ d := by linarith
  have habs : |Acoef β κ d - Acoef β κ c| < √(Disc β κ d) := by
    rw [Real.lt_sqrt (abs_nonneg _), sq_abs]; exact hDd
  have hsq : 0 ≤ √(Disc β κ c) := Real.sqrt_nonneg _
  unfold sMinus sPlus
  rw [← hc, ← hd]
  have := (abs_lt.1 habs).2
  linarith

end OBABO
