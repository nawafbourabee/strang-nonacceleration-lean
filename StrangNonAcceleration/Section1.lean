/-
The worst-case spectral radius `ρ_q(s, β; κ)` of (1.10) of

  N. Bou-Rabee, Provable non-acceleration of standard Strang splittings of kinetic
  Langevin dynamics, arXiv:2608.25279.

For `λ ∈ [1, κ]` the companion matrix `A_λ(s, β)` of (1.10) has characteristic polynomial
`z² - (1 + β - sλ) z + β`. Its spectral radius is the explicit function `rootRad (1 + β - sλ) β`
of the trace (`spectralRadius_Amat`), and `ρ_q(s, β; κ)` is the supremum of these values over
`λ ∈ [1, κ]` (`ρq`). Since the trace is affine in `λ` and the spectral radius is nondecreasing in
the modulus of the trace, the supremum is attained at `λ = 1` or `λ = κ`, and `ρ_q ≤ r` for
`r ≥ √β` is equivalent to `|1 + β - s| ≤ r + β/r` and `|1 + β - sκ| ≤ r + β/r`
(`ρq_le_iff`). This is the description of the sublevel sets of `ρ_q` in [22, Lemma 2.4] in
the form used by the paper: for `ρ = ρ_q(s, β; κ)` one has `β ≤ ρ²`, `s ≥ (1 - ρ)(1 - β/ρ)`
and `s ≤ (1 + ρ)(1 + β/ρ)/κ`, hence `ℓ(ρ) ≤ β` (the bound (3.20)) and `ρ ≥ ρ⋆(κ)`
([22, Corollary 2.3]).
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import StrangNonAcceleration.Lemma2_2

open Real

namespace OBABO

/-! ## The spectral radius of a real companion matrix `[[T, -β], [1, 0]]` -/

/-- The spectral radius of the companion matrix of `z² - T z + β` for `β ≥ 0`:
`√β` if the roots are complex, `(|T| + √(T² - 4β))/2` if they are real. Written as a
maximum so that no case distinction is needed (`√(T² - 4β) = 0` when `T² < 4β`). -/
noncomputable def rootRad (T β : ℝ) : ℝ := max (√β) ((|T| + √(T ^ 2 - 4 * β)) / 2)

theorem sqrt_le_rootRad (T β : ℝ) : √β ≤ rootRad T β := le_max_left _ _

/-- Every complex root of `z² - T z + β` (`β ≥ 0`) has modulus at most `rootRad T β`. -/
theorem norm_root_le (T β : ℝ) (_hβ : 0 ≤ β) (z : ℂ)
    (hz : z ^ 2 - (T : ℂ) * z + (β : ℂ) = 0) : ‖z‖ ≤ rootRad T β := by
  set x := z.re with hx
  set y := z.im with hy
  have hre : x ^ 2 - y ^ 2 - T * x + β = 0 := by
    have := congrArg Complex.re hz
    simp [sq, Complex.mul_re] at this
    linarith
  have him : y * (2 * x - T) = 0 := by
    have := congrArg Complex.im hz
    simp [sq, Complex.mul_im] at this
    linarith
  have hnorm : ‖z‖ = √(x ^ 2 + y ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]; congr 1; ring
  rcases mul_eq_zero.1 him with hy0 | hx0
  · -- real root: `x² - T x + β = 0`, so `|x| ≤ (|T| + √(T² - 4β))/2`
    rw [hy0] at hre hnorm
    have hD : 0 ≤ T ^ 2 - 4 * β := by nlinarith [sq_nonneg (2 * x - T)]
    have hsq : (2 * x - T) ^ 2 = T ^ 2 - 4 * β := by nlinarith
    have habs : |2 * x - T| = √(T ^ 2 - 4 * β) := by
      rw [← hsq, Real.sqrt_sq_eq_abs]
    have h1 : |x| ≤ (|T| + √(T ^ 2 - 4 * β)) / 2 := by
      rw [← habs]
      have := abs_add_le (2 * x - T) T
      have e : 2 * x - T + T = 2 * x := by ring
      rw [e, abs_mul, abs_two] at this
      linarith
    rw [hnorm]
    simp only [zero_pow two_ne_zero, add_zero, Real.sqrt_sq_eq_abs]
    exact le_trans h1 (le_max_right _ _)
  · -- complex root: `x = T/2` and `x² + y² = β`
    have hx2 : x = T / 2 := by linarith
    have hmod : x ^ 2 + y ^ 2 = β := by rw [hx2] at hre ⊢; nlinarith
    rw [hnorm, hmod]
    exact le_max_left _ _

/-- Some complex root of `z² - T z + β` (`β ≥ 0`) has modulus exactly `rootRad T β`. -/
theorem exists_root_norm_eq (T β : ℝ) (_hβ : 0 ≤ β) :
    ∃ z : ℂ, z ^ 2 - (T : ℂ) * z + (β : ℂ) = 0 ∧ ‖z‖ = rootRad T β := by
  rcases lt_or_ge (T ^ 2) (4 * β) with hlt | hge
  · -- complex roots: `z = T/2 + i √(β - T²/4)`
    have hD : √(T ^ 2 - 4 * β) = 0 := Real.sqrt_eq_zero'.2 (by linarith)
    have hmax : rootRad T β = √β := by
      unfold rootRad; rw [hD, add_zero]
      apply max_eq_left
      have : |T| < 2 * √β := by
        rw [← Real.sqrt_sq_eq_abs]
        calc √(T ^ 2) < √(4 * β) := Real.sqrt_lt_sqrt (sq_nonneg T) hlt
          _ = 2 * √β := by
            rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      linarith
    refine ⟨⟨T / 2, √(β - T ^ 2 / 4)⟩, ?_, ?_⟩
    · have hs : √(β - T * T / 4) * √(β - T * T / 4) = β - T * T / 4 :=
        Real.mul_self_sqrt (by nlinarith)
      apply Complex.ext <;> simp [sq, Complex.mul_re, Complex.mul_im] <;> nlinarith [hs]
    · rw [hmax, Complex.norm_def, Complex.normSq_apply]
      simp only
      have hs : √(β - T ^ 2 / 4) * √(β - T ^ 2 / 4) = β - T ^ 2 / 4 :=
        Real.mul_self_sqrt (by linarith)
      congr 1; rw [hs]; ring
  · -- real roots `(T ± √(T² - 4β))/2`; the one with the larger modulus
    have hs : √(T ^ 2 - 4 * β) ^ 2 = T ^ 2 - 4 * β := Real.sq_sqrt (by linarith)
    have hmax : rootRad T β = (|T| + √(T ^ 2 - 4 * β)) / 2 := by
      unfold rootRad
      apply max_eq_right
      have h1 : √β ≤ |T| / 2 := by
        rw [← Real.sqrt_sq_eq_abs]
        have : √β = √(4 * β) / 2 := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
          ring
        rw [this]
        exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hge) (by norm_num)
      linarith [Real.sqrt_nonneg (T ^ 2 - 4 * β)]
    rcases le_or_gt 0 T with hT | hT
    · refine ⟨((T + √(T ^ 2 - 4 * β)) / 2 : ℝ), ?_, ?_⟩
      · have : ((T + √(T ^ 2 - 4 * β)) / 2) ^ 2 - T * ((T + √(T ^ 2 - 4 * β)) / 2) + β = 0 := by
          nlinarith [hs]
        exact_mod_cast this
      · rw [hmax, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hT,
          abs_of_nonneg (by positivity)]
    · refine ⟨((T - √(T ^ 2 - 4 * β)) / 2 : ℝ), ?_, ?_⟩
      · have : ((T - √(T ^ 2 - 4 * β)) / 2) ^ 2 - T * ((T - √(T ^ 2 - 4 * β)) / 2) + β = 0 := by
          nlinarith [hs]
        exact_mod_cast this
      · rw [hmax, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hT,
          abs_of_nonpos (by linarith [Real.sqrt_nonneg (T ^ 2 - 4 * β)])]
        ring

/-- The spectral radius (Mathlib's `spectralRadius`, in `ℝ≥0∞`) of the complexified companion
matrix `A_λ(s, β)` of (1.10) equals `rootRad (1 + β - sλ) β`. -/
theorem spectralRadius_Amat (s β l : ℝ) (hβ : 0 ≤ β) :
    spectralRadius ℂ ((Section2.Amat s β l).map (algebraMap ℝ ℂ))
      = ENNReal.ofReal (rootRad (1 + β - s * l) β) := by
  apply le_antisymm
  · apply iSup₂_le
    intro z hz
    rw [Section2.mem_spectrum_Amat] at hz
    have := norm_root_le (1 + β - s * l) β hβ z hz
    rw [← enorm_eq_nnnorm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal this
  · obtain ⟨z, hz, hzn⟩ := exists_root_norm_eq (1 + β - s * l) β hβ
    have hmem : z ∈ spectrum ℂ ((Section2.Amat s β l).map (algebraMap ℝ ℂ)) :=
      (Section2.mem_spectrum_Amat s β l z).2 hz
    have h1 : ENNReal.ofReal (rootRad (1 + β - s * l) β) = (‖z‖₊ : ENNReal) := by
      rw [← hzn, ← enorm_eq_nnnorm, ofReal_norm]
    rw [h1]
    exact le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ ((Section2.Amat s β l).map (algebraMap ℝ ℂ))) =>
      (‖k‖₊ : ENNReal)) z hmem

/-- `rootRad T β ≤ r` for `r ≥ √β > 0` iff `|T| ≤ r + β/r`. -/
theorem rootRad_le_iff (T β r : ℝ) (hβ : 0 ≤ β) (hr0 : 0 < r) (hr : √β ≤ r) :
    rootRad T β ≤ r ↔ |T| ≤ r + β / r := by
  have hβr : β ≤ r ^ 2 := by
    have := Real.sq_sqrt hβ
    nlinarith [Real.sqrt_nonneg β]
  have hRr : r + β / r = (r ^ 2 + β) / r := by field_simp
  unfold rootRad
  rw [max_le_iff]
  constructor
  · rintro ⟨-, h⟩
    rcases lt_or_ge (T ^ 2) (4 * β) with hlt | hge
    · -- `|T| < 2√β ≤ r + β/r`
      have h1 : |T| ^ 2 < 4 * β := by rwa [sq_abs]
      rw [hRr, le_div_iff₀ hr0]
      nlinarith [sq_nonneg (r - |T| / 2), abs_nonneg T]
    · have hs : √(T ^ 2 - 4 * β) ^ 2 = T ^ 2 - 4 * β := Real.sq_sqrt (by linarith)
      have hs0 := Real.sqrt_nonneg (T ^ 2 - 4 * β)
      have h2 : √(T ^ 2 - 4 * β) ≤ 2 * r - |T| := by linarith
      have h3 : (2 * r - |T|) ^ 2 ≥ T ^ 2 - 4 * β := by nlinarith
      rw [hRr, le_div_iff₀ hr0]
      nlinarith [sq_abs T]
  · intro h
    refine ⟨hr, ?_⟩
    rw [hRr, le_div_iff₀ hr0] at h
    rcases lt_or_ge (T ^ 2) (4 * β) with hlt | hge
    · have hD : √(T ^ 2 - 4 * β) = 0 := Real.sqrt_eq_zero'.2 (by linarith)
      rw [hD, add_zero]
      have : |T| ^ 2 < 4 * β := by rwa [sq_abs]
      have h4 : |T| < 2 * √β := by
        have := Real.sqrt_lt_sqrt (sq_nonneg |T|) this
        rw [Real.sqrt_sq (abs_nonneg T), Real.sqrt_mul (by norm_num),
          show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at this
        exact this
      linarith
    · have hs : √(T ^ 2 - 4 * β) ^ 2 = T ^ 2 - 4 * β := Real.sq_sqrt (by linarith)
      have h5 : √(T ^ 2 - 4 * β) ≤ 2 * r - |T| := by
        apply Real.sqrt_le_iff.2
        refine ⟨?_, ?_⟩
        · nlinarith [abs_nonneg T]
        · nlinarith [sq_abs T, abs_nonneg T]
      linarith

/-! ## The worst-case spectral radius `ρ_q(s, β; κ)` -/

/-- `ρ_q(s, β; κ) = sup_{λ ∈ [1, κ]} ρ(A_λ(s, β))`, (1.10). -/
noncomputable def ρq (s β κ : ℝ) : ℝ :=
  sSup ((fun l => rootRad (1 + β - s * l) β) '' Set.Icc 1 κ)

theorem rootRad_le_bound (T β : ℝ) (hβ : 0 ≤ β) : rootRad T β ≤ |T| + √β := by
  unfold rootRad
  apply max_le (by linarith [abs_nonneg T])
  have : √(T ^ 2 - 4 * β) ≤ |T| := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith)
  linarith [Real.sqrt_nonneg β]

theorem ρq_bddAbove (s β κ : ℝ) (hβ : 0 ≤ β) (hs : 0 ≤ s) (hκ : 1 ≤ κ) :
    BddAbove ((fun l => rootRad (1 + β - s * l) β) '' Set.Icc 1 κ) := by
  refine ⟨1 + β + s * κ + √β, ?_⟩
  rintro _ ⟨l, ⟨hl1, hlκ⟩, rfl⟩
  refine le_trans (rootRad_le_bound _ _ hβ) ?_
  have : |1 + β - s * l| ≤ 1 + β + s * κ := by
    rw [abs_le]; constructor <;> nlinarith
  linarith

/-- `√β ≤ ρ_q(s, β; κ)` (the product of the two roots of `A_λ` is `β`). -/
theorem sqrt_le_ρq (s β κ : ℝ) (hβ : 0 ≤ β) (hs : 0 ≤ s) (hκ : 1 ≤ κ) :
    √β ≤ ρq s β κ := by
  refine le_trans (sqrt_le_rootRad (1 + β - s * 1) β) ?_
  exact le_csSup (ρq_bddAbove s β κ hβ hs hκ) ⟨1, ⟨le_rfl, hκ⟩, rfl⟩

/-- The sublevel sets of `ρ_q` ([22, Lemma 2.4] in the form used here): for `r ≥ √β > 0`,
`ρ_q(s, β; κ) ≤ r` iff `|1 + β - s| ≤ r + β/r` and `|1 + β - sκ| ≤ r + β/r`. -/
theorem ρq_le_iff (s β κ r : ℝ) (hβ : 0 ≤ β) (hs : 0 ≤ s) (hκ : 1 ≤ κ) (hr0 : 0 < r)
    (hr : √β ≤ r) :
    ρq s β κ ≤ r ↔ |1 + β - s| ≤ r + β / r ∧ |1 + β - s * κ| ≤ r + β / r := by
  constructor
  · intro h
    have h1 : rootRad (1 + β - s * 1) β ≤ r :=
      le_trans (le_csSup (ρq_bddAbove s β κ hβ hs hκ) ⟨1, ⟨le_rfl, hκ⟩, rfl⟩) h
    have h2 : rootRad (1 + β - s * κ) β ≤ r :=
      le_trans (le_csSup (ρq_bddAbove s β κ hβ hs hκ) ⟨κ, ⟨hκ, le_rfl⟩, rfl⟩) h
    rw [rootRad_le_iff _ _ _ hβ hr0 hr] at h1 h2
    rw [mul_one] at h1
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine csSup_le ⟨rootRad (1 + β - s * 1) β, ⟨1, ⟨le_rfl, hκ⟩, rfl⟩⟩ ?_
    rintro _ ⟨l, ⟨hl1, hlκ⟩, rfl⟩
    rw [rootRad_le_iff _ _ _ hβ hr0 hr]
    -- `1 + β - s l` lies between `1 + β - s κ` and `1 + β - s`
    rw [abs_le] at h1 h2 ⊢
    constructor <;> nlinarith

/-- For `ρ = ρ_q(s, β; κ)`: `β ≤ ρ²`, `s ≥ (1 - ρ)(1 - β/ρ)` and `s ≤ (1 + ρ)(1 + β/ρ)/κ`. -/
theorem ρq_facts (s β κ : ℝ) (hβ : 0 < β) (hs : 0 ≤ s) (hκ : 1 ≤ κ) :
    let ρ := ρq s β κ
    0 < ρ ∧ β ≤ ρ ^ 2 ∧ (1 - ρ) * (1 - β / ρ) ≤ s ∧ s * κ ≤ (1 + ρ) * (1 + β / ρ) := by
  intro ρ
  have hsq := sqrt_le_ρq s β κ hβ.le hs hκ
  have hρ0 : 0 < ρ := lt_of_lt_of_le (Real.sqrt_pos.2 hβ) hsq
  have hβρ : β ≤ ρ ^ 2 := by
    have := Real.sq_sqrt hβ.le
    nlinarith [Real.sqrt_nonneg β]
  obtain ⟨h1, h2⟩ := (ρq_le_iff s β κ ρ hβ.le hs hκ hρ0 hsq).1 le_rfl
  refine ⟨hρ0, hβρ, ?_, ?_⟩
  · have := (abs_le.1 h1).2
    have e : (1 - ρ) * (1 - β / ρ) = 1 + β - (ρ + β / ρ) := by field_simp; ring
    linarith
  · have := (abs_le.1 h2).1
    have e : (1 + ρ) * (1 + β / ρ) = 1 + β + (ρ + β / ρ) := by field_simp; ring
    linarith

/-- The level-set bound (3.20): `ℓ(ρ) ≤ β` for `ρ = ρ_q(s, β; κ)`, with
`ℓ(t) = t(g - t)/(1 - g t)`, `g = (1 - u)/(1 + u)`, `u = κ⁻¹`. -/
theorem ell_ρq_le (s β κ : ℝ) (hβ : 0 < β) (hβ1 : β < 1) (hs : 0 ≤ s) (hκ : 1 < κ)
    (hρ1 : ρq s β κ < 1) :
    let u := κ⁻¹
    let ρ := ρq s β κ
    ρ * ((1 - u) / (1 + u) - ρ) / (1 - (1 - u) / (1 + u) * ρ) ≤ β := by
  intro u ρ
  obtain ⟨hρ0, hβρ, hlow, hup⟩ := ρq_facts s β κ hβ hs hκ.le
  have hu0 : 0 < u := inv_pos.2 (by linarith)
  have hu1 : u < 1 := inv_lt_one_of_one_lt₀ hκ
  have hκu : κ = u⁻¹ := (inv_inv κ).symm
  -- `(1 - ρ)(1 - β/ρ) ≤ s ≤ (1 + ρ)(1 + β/ρ) u`
  have hchain : (1 - ρ) * (1 - β / ρ) ≤ (1 + ρ) * (1 + β / ρ) * u := by
    have : s * κ * u = s := by rw [hκu]; field_simp
    calc (1 - ρ) * (1 - β / ρ) ≤ s := hlow
      _ = s * κ * u := this.symm
      _ ≤ (1 + ρ) * (1 + β / ρ) * u := mul_le_mul_of_nonneg_right hup hu0.le
  have hden : 0 < 1 - (1 - u) / (1 + u) * ρ := by
    have : (1 - u) / (1 + u) < 1 := by rw [div_lt_one (by linarith)]; linarith
    nlinarith
  have hρne : ρ ≠ 0 := ne_of_gt hρ0
  rw [div_le_iff₀ hden]
  have e1 : (1 - ρ) * (1 - β / ρ) = ((1 - ρ) * (ρ - β)) / ρ := by field_simp
  have e2 : (1 + ρ) * (1 + β / ρ) * u = ((1 + ρ) * (ρ + β) * u) / ρ := by field_simp
  rw [e1, e2, div_le_div_iff_of_pos_right hρ0] at hchain
  have hg : (1 - u) / (1 + u) * ρ = (1 - u) * ρ / (1 + u) := by ring
  have key : ρ * ((1 - u) / (1 + u) - ρ) ≤ β * (1 - (1 - u) / (1 + u) * ρ) := by
    have hpos : 0 < 1 + u := by linarith
    rw [show ρ * ((1 - u) / (1 + u) - ρ) = (ρ * ((1 - u) - (1 + u) * ρ)) / (1 + u) by
      field_simp]
    rw [show β * (1 - (1 - u) / (1 + u) * ρ) = (β * ((1 + u) - (1 - u) * ρ)) / (1 + u) by
      field_simp]
    apply div_le_div_of_nonneg_right _ hpos.le
    nlinarith
  exact key

/-- [22, Corollary 2.3]: `ρ_q(s, β; κ) ≥ ρ⋆(κ) = (1 - √u)/(1 + √u)`, `u = κ⁻¹`. -/
theorem rho_star_le_ρq (s β κ : ℝ) (hβ : 0 < β) (hβ1 : β < 1) (hs : 0 ≤ s) (hκ : 1 < κ)
    (hρ1 : ρq s β κ < 1) :
    (1 - √κ⁻¹) / (1 + √κ⁻¹) ≤ ρq s β κ := by
  have hell := ell_ρq_le s β κ hβ hβ1 hs hκ hρ1
  obtain ⟨hρ0, hβρ, -, -⟩ := ρq_facts s β κ hβ hs hκ.le
  simp only at hell
  set ρ := ρq s β κ
  set u := κ⁻¹ with hu
  have hu0 : 0 < u := inv_pos.2 (by linarith)
  have hu1 : u < 1 := inv_lt_one_of_one_lt₀ hκ
  set v := √u with hv
  have hv0 : 0 < v := Real.sqrt_pos.2 hu0
  have hv1 : v < 1 := by rw [hv, Real.sqrt_lt' (by norm_num)]; linarith
  have hvu : v ^ 2 = u := Real.sq_sqrt hu0.le
  -- `ℓ(ρ) ≤ β ≤ ρ²` gives `g ρ² - 2ρ + g ≤ 0`
  have hden : 0 < 1 - (1 - u) / (1 + u) * ρ := by
    have : (1 - u) / (1 + u) < 1 := by rw [div_lt_one (by linarith)]; linarith
    nlinarith
  have h1 : ρ * ((1 - u) / (1 + u) - ρ) ≤ ρ ^ 2 * (1 - (1 - u) / (1 + u) * ρ) := by
    rw [div_le_iff₀ hden] at hell
    nlinarith
  have h2 : (1 - u) * ρ ^ 2 - 2 * (1 + u) * ρ + (1 - u) ≤ 0 := by
    have hpos : 0 < 1 + u := by linarith
    have : ρ * ((1 - u) - (1 + u) * ρ) ≤ ρ ^ 2 * ((1 + u) - (1 - u) * ρ) := by
      have e1 : ρ * ((1 - u) / (1 + u) - ρ) = ρ * ((1 - u) - (1 + u) * ρ) / (1 + u) := by
        field_simp
      have e2 : ρ ^ 2 * (1 - (1 - u) / (1 + u) * ρ) = ρ ^ 2 * ((1 + u) - (1 - u) * ρ) / (1 + u) := by
        field_simp
      rw [e1, e2, div_le_div_iff_of_pos_right hpos] at h1
      exact h1
    nlinarith
  -- factor: `(1 - v²)ρ² - 2(1 + v²)ρ + (1 - v²) = ((1+v)ρ - (1-v))((1-v)ρ - (1+v))`
  have hfac : (1 - u) * ρ ^ 2 - 2 * (1 + u) * ρ + (1 - u)
      = ((1 + v) * ρ - (1 - v)) * ((1 - v) * ρ - (1 + v)) := by rw [← hvu]; ring
  have hneg : (1 - v) * ρ - (1 + v) < 0 := by nlinarith
  have hfirst : 0 ≤ (1 + v) * ρ - (1 - v) := by
    by_contra hcon
    push Not at hcon
    have := mul_pos_of_neg_of_neg hcon hneg
    linarith
  rw [div_le_iff₀ (by linarith)]
  linarith

end OBABO
