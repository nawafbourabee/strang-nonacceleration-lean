/-
Proposition 3.4 (smooth attracting cycle with stable linearization) of

  N. Bou-Rabee, Provable non-acceleration of standard Strang splittings of kinetic
  Langevin dynamics, arXiv:2608.25279.

The paper mollifies the piecewise quadratic potential `ψ` of Theorem 3.1 with a centered
smooth probability density `ϱ_ε` supported in `B(0, ε)`, `ε < r_max/4`, and shows that
`U = ϱ_ε * ψ` is `C^∞`, `1`-strongly convex with `κ`-Lipschitz gradient (so `U ∈ U_κ²`), has the
same cycle (3.25), the locally affine gradient (3.26) with `r₀ = r_max/2`, the bounded remainder
(3.27), Hessian `Id` on the balls `B(x°_j, r₀)`, and the Jacobian (3.28) of the heavy-ball
update at the cycle states, whose `m`-th power has spectral radius `ρ(A_1(s, β))^m ≤ ρ_q^m < 1`.

Part A (namespace `Mollify`) is the general mollification argument on a finite-dimensional real
inner product space with a Haar measure: the mollified vector field `ϱ ⋆ g` inherits strong
monotonicity, Lipschitz bounds, local affine structure and bounded remainders from `g`, it is
smooth, and it is the gradient of `ϱ ⋆ ψ` when `g` is the gradient of `ψ`; Hessian bounds follow
from monotonicity and Lipschitz continuity by the limiting argument of the paper.

Part B assembles Proposition 3.4 in the plane `ℂ` of Theorem3_1.lean. The representation of
`ψ` (Theorem 3.1(i), imported from [22, Theorem 3.5]) enters as hypotheses: `ψ` has gradient
`∇ψ(x) = x + (κ - 1) proj_C(x)`, which is `1`-strongly monotone and `κ`-Lipschitz.
-/
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Analysis.Complex.Polynomial.Basic
import StrangNonAcceleration.Theorem3_1
import StrangNonAcceleration.Section1

open MeasureTheory Real Filter Topology
open scoped InnerProductSpace Convolution

namespace OBABO.Section3

/-! ## Part A. Mollification of a vector field -/

namespace Mollify

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Hessian bounds from monotonicity and Lipschitz continuity, by the limiting argument of the
paper: if `G` is differentiable at `x`, `1`-strongly monotone and `κ`-Lipschitz, then
`⟪DG(x) v, v⟫ ≥ ‖v‖²` and `‖DG(x) v‖ ≤ κ ‖v‖`. -/
theorem hessian_bounds_of_mono_lip (G : E → E) (κ : ℝ) (x : E) (D : E →L[ℝ] E)
    (hD : HasFDerivAt G D x)
    (hmono : ∀ x y, ‖x - y‖ ^ 2 ≤ ⟪G x - G y, x - y⟫_ℝ)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ κ * ‖x - y‖) (v : E) :
    ‖v‖ ^ 2 ≤ ⟪D v, v⟫_ℝ ∧ ‖D v‖ ≤ κ * ‖v‖ := by
  have hc : Tendsto (fun n : ℕ => ‖((n : ℝ) + 1)‖) atTop atTop := by
    have : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    exact this.congr (fun n => (Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1)).symm)
  have hlim := hD.lim v (c := fun n : ℕ => (n : ℝ) + 1) hc
  set q : ℕ → E := fun n => ((n : ℝ) + 1) • (G (x + ((n : ℝ) + 1)⁻¹ • v) - G x) with hq
  constructor
  · -- `⟪q n, v⟫ ≥ ‖v‖²` for every `n`
    have h1 : ∀ n : ℕ, ‖v‖ ^ 2 ≤ ⟪q n, v⟫_ℝ := by
      intro n
      have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have := hmono (x + ((n : ℝ) + 1)⁻¹ • v) x
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hn),
        real_inner_smul_right] at this
      simp only [q, real_inner_smul_left]
      have h2 : (((n : ℝ) + 1)⁻¹) ^ 2 * ‖v‖ ^ 2 ≤
          ((n : ℝ) + 1)⁻¹ * ⟪G (x + ((n : ℝ) + 1)⁻¹ • v) - G x, v⟫_ℝ := by
        rw [mul_pow] at this; exact this
      have h3 := mul_le_mul_of_nonneg_left h2 (le_of_lt (pow_pos hn 2))
      have e1 : ((n : ℝ) + 1) ^ 2 * ((((n : ℝ) + 1)⁻¹) ^ 2 * ‖v‖ ^ 2) = ‖v‖ ^ 2 := by
        field_simp
      have e2 : ((n : ℝ) + 1) ^ 2 * (((n : ℝ) + 1)⁻¹ * ⟪G (x + ((n : ℝ) + 1)⁻¹ • v) - G x, v⟫_ℝ)
          = ((n : ℝ) + 1) * ⟪G (x + ((n : ℝ) + 1)⁻¹ • v) - G x, v⟫_ℝ := by
        field_simp
      rw [e1, e2] at h3
      exact h3
    have hcont : Tendsto (fun n => ⟪q n, v⟫_ℝ) atTop (𝓝 ⟪D v, v⟫_ℝ) :=
      hlim.inner (tendsto_const_nhds (x := v))
    exact ge_of_tendsto hcont (Eventually.of_forall h1)
  · have h1 : ∀ n : ℕ, ‖q n‖ ≤ κ * ‖v‖ := by
      intro n
      have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have := hlip (x + ((n : ℝ) + 1)⁻¹ • v) x
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hn)] at this
      simp only [q, norm_smul, Real.norm_eq_abs, abs_of_pos hn]
      calc ((n : ℝ) + 1) * ‖G (x + ((n : ℝ) + 1)⁻¹ • v) - G x‖
          ≤ ((n : ℝ) + 1) * (κ * (((n : ℝ) + 1)⁻¹ * ‖v‖)) := mul_le_mul_of_nonneg_left this hn.le
        _ = κ * ‖v‖ := by field_simp
    exact le_of_tendsto hlim.norm (Eventually.of_forall h1)

/-- On the open ball where `G` is affine with slope `Id`, its derivative is `Id`. -/
theorem hasFDerivAt_id_of_affine (G : E → E) (c : E) (r₀ : ℝ)
    (haff : ∀ u : E, ‖u‖ ≤ r₀ → G (c + u) = G c + u) (x : E) (hx : x ∈ Metric.ball c r₀) :
    HasFDerivAt G (ContinuousLinearMap.id ℝ E) x := by
  have h : HasFDerivAt (fun y => G c + (y - c)) (ContinuousLinearMap.id ℝ E) x := by
    simpa using ((hasFDerivAt_id x).sub_const c).const_add (G c)
  apply h.congr_of_eventuallyEq
  filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
  rw [Metric.mem_ball, dist_eq_norm] at hy
  have := haff (y - c) hy.le
  rw [add_sub_cancel] at this
  exact this

end Calculus

section Mollifier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]
variable (φ : ContDiffBump (0 : E))

/-- The mollified vector field `ϱ ⋆ g` with `ϱ = φ.normed μ`. -/
noncomputable def moll (g : E → E) : E → E := φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem moll_apply (g : E → E) (x : E) :
    moll μ φ g x = ∫ t, φ.normed μ t • g (x - t) ∂μ := by
  unfold moll; rw [convolution_def]; simp only [ContinuousLinearMap.lsmul_apply]

theorem integrable_normed_smul (g : E → E) (hg : Continuous g) (x : E) :
    Integrable (fun t => φ.normed μ t • g (x - t)) μ := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact φ.continuous_normed.smul (hg.comp (continuous_const.sub continuous_id))
  · exact φ.hasCompactSupport_normed.smul_right

theorem integrable_normed_mul (h : E → ℝ) (hh : Continuous h) :
    Integrable (fun t => φ.normed μ t * h t) μ := by
  apply Continuous.integrable_of_hasCompactSupport (φ.continuous_normed.mul hh)
  exact φ.hasCompactSupport_normed.mul_right

omit [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
/-- `∫ ϱ(t) • t = 0`: the mollifier is centered. -/
theorem integral_normed_smul_self [μ.IsNegInvariant] : ∫ t, φ.normed μ t • t ∂μ = 0 := by
  have h := integral_neg_eq_self (fun t => φ.normed μ t • t) μ
  simp only [φ.normed_neg, smul_neg] at h
  rw [integral_neg] at h
  set I := ∫ t, φ.normed μ t • t ∂μ
  have h2 : I + I = 0 := by nth_rewrite 1 [← h]; exact neg_add_cancel I
  rw [← two_smul ℝ] at h2
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

/-- The mollified field of a `1`-strongly monotone field is `1`-strongly monotone. -/
theorem moll_strongMono (g : E → E) (hg : Continuous g)
    (hmono : ∀ x y, ‖x - y‖ ^ 2 ≤ ⟪g x - g y, x - y⟫_ℝ) (x y : E) :
    ‖x - y‖ ^ 2 ≤ ⟪moll μ φ g x - moll μ φ g y, x - y⟫_ℝ := by
  rw [moll_apply, moll_apply, ← integral_sub (integrable_normed_smul μ φ g hg x)
    (integrable_normed_smul μ φ g hg y)]
  have hint : Integrable (fun t => φ.normed μ t • g (x - t) - φ.normed μ t • g (y - t)) μ :=
    (integrable_normed_smul μ φ g hg x).sub (integrable_normed_smul μ φ g hg y)
  rw [real_inner_comm, ← integral_inner hint]
  have h1 : ∀ t, ⟪x - y, φ.normed μ t • g (x - t) - φ.normed μ t • g (y - t)⟫_ℝ
      = φ.normed μ t * ⟪g (x - t) - g (y - t), x - y⟫_ℝ := by
    intro t; rw [← smul_sub, real_inner_smul_right, real_inner_comm]
  simp_rw [h1]
  have h2 : ∀ t, φ.normed μ t * ‖x - y‖ ^ 2 ≤ φ.normed μ t * ⟪g (x - t) - g (y - t), x - y⟫_ℝ := by
    intro t
    apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed t)
    have := hmono (x - t) (y - t)
    rwa [sub_sub_sub_cancel_right] at this
  calc ‖x - y‖ ^ 2 = ∫ t, φ.normed μ t * ‖x - y‖ ^ 2 ∂μ := by
        rw [integral_mul_const, φ.integral_normed, one_mul]
    _ ≤ ∫ t, φ.normed μ t * ⟪g (x - t) - g (y - t), x - y⟫_ℝ ∂μ := by
        apply integral_mono (integrable_normed_mul μ φ _ continuous_const) _ h2
        exact integrable_normed_mul μ φ _
          (((hg.comp (continuous_const.sub continuous_id)).sub
            (hg.comp (continuous_const.sub continuous_id))).inner continuous_const)

/-- The mollified field of a `κ`-Lipschitz field is `κ`-Lipschitz. -/
theorem moll_lipschitz (g : E → E) (hg : Continuous g) (κ : ℝ)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ κ * ‖x - y‖) (x y : E) :
    ‖moll μ φ g x - moll μ φ g y‖ ≤ κ * ‖x - y‖ := by
  rw [moll_apply, moll_apply, ← integral_sub (integrable_normed_smul μ φ g hg x)
    (integrable_normed_smul μ φ g hg y)]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  have h1 : ∀ t, ‖φ.normed μ t • g (x - t) - φ.normed μ t • g (y - t)‖
      = φ.normed μ t * ‖g (x - t) - g (y - t)‖ := by
    intro t; rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed t)]
  simp_rw [h1]
  have h2 : ∀ t, φ.normed μ t * ‖g (x - t) - g (y - t)‖ ≤ φ.normed μ t * (κ * ‖x - y‖) := by
    intro t
    apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed t)
    have := hlip (x - t) (y - t)
    rwa [sub_sub_sub_cancel_right] at this
  calc ∫ t, φ.normed μ t * ‖g (x - t) - g (y - t)‖ ∂μ
      ≤ ∫ t, φ.normed μ t * (κ * ‖x - y‖) ∂μ := by
        apply integral_mono _ (integrable_normed_mul μ φ _ continuous_const) h2
        exact integrable_normed_mul μ φ _
          ((hg.comp (continuous_const.sub continuous_id)).sub
            (hg.comp (continuous_const.sub continuous_id))).norm
    _ = κ * ‖x - y‖ := by rw [integral_mul_const, φ.integral_normed, one_mul]

/-- If `g` is affine on `closedBall c r` and `ϱ` is supported in `B(0, r/2)`, then `ϱ ⋆ g` is
affine with the same slope on `closedBall c (r/2)`, and `(ϱ ⋆ g)(c) = g(c)`. -/
theorem moll_local_affine [μ.IsNegInvariant] (g : E → E) (c : E) (r : ℝ) (hφ : φ.rOut ≤ r / 2)
    (haff : ∀ u : E, ‖u‖ ≤ r → g (c + u) = g c + u) :
    ∀ u : E, ‖u‖ ≤ r / 2 → moll μ φ g (c + u) = g c + u := by
  intro u hu
  rw [moll_apply]
  have h1 : ∀ t, φ.normed μ t • g (c + u - t) = φ.normed μ t • (g c + u - t) := by
    intro t
    by_cases ht : φ.normed μ t = 0
    · simp [ht]
    · have hmem : t ∈ Function.support (φ.normed μ) := ht
      rw [φ.support_normed_eq, Metric.mem_ball, dist_zero_right] at hmem
      have : ‖u - t‖ ≤ r := by
        calc ‖u - t‖ ≤ ‖u‖ + ‖t‖ := norm_sub_le _ _
          _ ≤ r / 2 + r / 2 := by linarith
          _ = r := by ring
      rw [show c + u - t = c + (u - t) by abel, haff (u - t) this]
      congr 1; abel
  simp_rw [h1]
  have h2 : ∀ t, φ.normed μ t • (g c + u - t) = φ.normed μ t • (g c + u) - φ.normed μ t • t := by
    intro t; rw [← smul_sub]
  simp_rw [h2]
  rw [integral_sub, φ.integral_normed_smul, integral_normed_smul_self, sub_zero]
  · exact (φ.integrable_normed.smul_const _)
  · exact (integrable_normed_smul μ φ id continuous_id 0).neg.congr
      (Eventually.of_forall fun t => by simp)

/-- A bounded remainder `‖g x - x‖ ≤ b` passes to the mollified field. -/
theorem moll_remainder [μ.IsNegInvariant] (g : E → E) (hg : Continuous g) (b : ℝ)
    (hb : ∀ x, ‖g x - x‖ ≤ b) (x : E) : ‖moll μ φ g x - x‖ ≤ b := by
  rw [moll_apply]
  have hx : x = ∫ t, φ.normed μ t • (x - t) ∂μ := by
    have h : ∀ t, φ.normed μ t • (x - t) = φ.normed μ t • x - φ.normed μ t • t := by
      intro t; rw [smul_sub]
    simp_rw [h]
    rw [integral_sub (φ.integrable_normed.smul_const _), φ.integral_normed_smul,
      integral_normed_smul_self, sub_zero]
    exact (integrable_normed_smul μ φ id continuous_id 0).neg.congr
      (Eventually.of_forall fun t => by simp)
  have hint2 : Integrable (fun t => φ.normed μ t • (x - t)) μ :=
    (integrable_normed_smul μ φ id continuous_id x).congr (Eventually.of_forall fun t => by simp)
  have e : (∫ t, φ.normed μ t • g (x - t) ∂μ) - x
      = ∫ t, (φ.normed μ t • g (x - t) - φ.normed μ t • (x - t)) ∂μ := by
    rw [integral_sub (integrable_normed_smul μ φ g hg x) hint2, ← hx]
  rw [e]
  · refine le_trans (norm_integral_le_integral_norm _) ?_
    have h1 : ∀ t, ‖φ.normed μ t • g (x - t) - φ.normed μ t • (x - t)‖
        = φ.normed μ t * ‖g (x - t) - (x - t)‖ := by
      intro t; rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed t)]
    simp_rw [h1]
    calc ∫ t, φ.normed μ t * ‖g (x - t) - (x - t)‖ ∂μ ≤ ∫ t, φ.normed μ t * b ∂μ := by
          apply integral_mono _ (integrable_normed_mul μ φ _ continuous_const)
          · intro t; exact mul_le_mul_of_nonneg_left (hb _) (φ.nonneg_normed t)
          · exact integrable_normed_mul μ φ _
              ((hg.comp (continuous_const.sub continuous_id)).sub
                (continuous_const.sub continuous_id)).norm
      _ = b := by rw [integral_mul_const, φ.integral_normed, one_mul]

/-- The mollified field is `C^∞`. -/
theorem moll_contDiff [μ.IsNegInvariant] (g : E → E) (hg : Continuous g) :
    ContDiff ℝ (⊤ : ℕ∞) (moll μ φ g) := by
  unfold moll
  exact φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
    hg.locallyIntegrable

/-- The mollified potential `ϱ ⋆ ψ` has gradient `ϱ ⋆ ∇ψ` (differentiation under the integral,
using the Lipschitz bound on `∇ψ` for domination). -/
theorem hasGradientAt_moll (ψ : E → ℝ) (g : E → E) (κ : ℝ) (hκ : 0 ≤ κ)
    (hψ : ∀ x, HasGradientAt ψ (g x) x) (hlip : ∀ x y, ‖g x - g y‖ ≤ κ * ‖x - y‖) (x₀ : E) :
    HasGradientAt (φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] ψ) (moll μ φ g x₀) x₀ := by
  have hg : Continuous g := by
    apply LipschitzWith.continuous (K := ⟨κ, hκ⟩)
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    exact hlip x y
  have hψc : Continuous ψ := by
    apply continuous_iff_continuousAt.2
    intro x; exact (hψ x).differentiableAt.continuousAt
  rw [hasGradientAt_iff_hasFDerivAt]
  -- the convolution as a parametric integral
  have hconv : (φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] ψ)
      = fun x => ∫ t, φ.normed μ t • ψ (x - t) ∂μ := by
    funext x; rw [convolution_def]; simp only [ContinuousLinearMap.lsmul_apply]
  rw [hconv]
  set F' : E → E → E →L[ℝ] ℝ := fun x t => φ.normed μ t • (InnerProductSpace.toDual ℝ E (g (x - t)))
  have key : HasFDerivAt (fun x => ∫ t, φ.normed μ t • ψ (x - t) ∂μ) (∫ t, F' x₀ t ∂μ) x₀ := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Metric.ball x₀ 1)
      (bound := fun t => φ.normed μ t * (‖g (x₀ - t)‖ + κ)) (Metric.ball_mem_nhds x₀ one_pos)
    · exact Eventually.of_forall fun x =>
        (φ.continuous_normed.smul (hψc.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
    · apply Continuous.integrable_of_hasCompactSupport
      · exact φ.continuous_normed.smul (hψc.comp (continuous_const.sub continuous_id))
      · exact φ.hasCompactSupport_normed.smul_right
    · apply Continuous.aestronglyMeasurable
      exact φ.continuous_normed.smul
        ((InnerProductSpace.toDual ℝ E).continuous.comp (hg.comp (continuous_const.sub continuous_id)))
    · refine Eventually.of_forall fun t x hx => ?_
      simp only [F']
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed t),
        LinearIsometryEquiv.norm_map]
      apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed t)
      have h1 := hlip (x - t) (x₀ - t)
      rw [sub_sub_sub_cancel_right] at h1
      have h2 : ‖x - x₀‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hx
      calc ‖g (x - t)‖ ≤ ‖g (x₀ - t)‖ + ‖g (x - t) - g (x₀ - t)‖ := by
            have := norm_le_norm_add_norm_sub' (g (x - t)) (g (x₀ - t))
            linarith [norm_sub_rev (g (x - t)) (g (x₀ - t))]
        _ ≤ ‖g (x₀ - t)‖ + κ * ‖x - x₀‖ := by linarith
        _ ≤ ‖g (x₀ - t)‖ + κ := by nlinarith
    · exact integrable_normed_mul μ φ _
        ((hg.comp (continuous_const.sub continuous_id)).norm.add continuous_const)
    · refine Eventually.of_forall fun t x _ => ?_
      simp only [F']
      have h := ((hψ (x - t)).hasFDerivAt).comp x ((hasFDerivAt_id x).sub_const t)
      rw [ContinuousLinearMap.comp_id] at h
      exact h.const_smul (φ.normed μ t)
  -- identify the integral of `F'` with `toDual (moll g x₀)`
  have hint : Integrable (fun t => φ.normed μ t • g (x₀ - t)) μ := integrable_normed_smul μ φ g hg x₀
  have e : ∫ t, F' x₀ t ∂μ = InnerProductSpace.toDual ℝ E (moll μ φ g x₀) := by
    rw [moll_apply]
    have := ((InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.toContinuousLinearMap).integral_comp_comm hint
    simp only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv] at this
    rw [← this]
    congr 1; funext t
    simp only [F', map_smul]
  rw [e] at key
  exact key

end Mollifier

end Mollify

/-! ## Part B. Proposition 3.4 in the plane -/

open Complex in
/-- The cycle equation (3.2) for the gradient field `x ↦ x + (κ - 1) M x` at the cycle points:
an algebraic identity in `ℂ` between `ζ = exp(θ i)` and `μ = a + b i` with `a, b` of (3.6). -/
theorem cycle_equation_aux (s β κ θ : ℝ) (hs : s ≠ 0) (hκ : κ - 1 ≠ 0) :
    ζ θ ^ 2 = ((1 + β - s : ℝ) : ℂ) * ζ θ - (β : ℂ)
      - ((s * (κ - 1) : ℝ) : ℂ) * (μ (aCoef s β κ θ) (bCoef s β κ θ) * ζ θ) := by
  have hre : (ζ θ).re = Real.cos θ := by unfold ζ; exact Complex.exp_ofReal_mul_I_re θ
  have him : (ζ θ).im = Real.sin θ := by unfold ζ; exact Complex.exp_ofReal_mul_I_im θ
  have hcs := Real.cos_sq_add_sin_sq θ
  have hκs : (κ - 1) * s ≠ 0 := mul_ne_zero hκ hs
  have hμa : (κ - 1) * s * aCoef s β κ θ = (1 + β - s) - (1 + β) * Real.cos θ := by
    unfold aCoef; field_simp
  have hμb : (κ - 1) * s * bCoef s β κ θ = -(1 - β) * Real.sin θ := by
    unfold bCoef; field_simp
  apply Complex.ext
  · simp only [sq, Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, μ, hre, him]
    linear_combination Real.cos θ * hμa - Real.sin θ * hμb - β * hcs
  · simp only [sq, Complex.mul_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, μ, hre, him]
    linear_combination Real.sin θ * hμa + Real.cos θ * hμb

/-- The cycle equation (3.25) for `G` with `G(x°_t) = x°_t + (κ - 1) μ x°_t`:
`x°_{t+2} = (1 + β) x°_{t+1} - β x°_t - s G(x°_{t+1})`. -/
theorem cycle_equation (s β κ θ : ℝ) (hs : s ≠ 0) (hκ : κ - 1 ≠ 0) (t : ℕ) :
    xc θ (t + 2) = (1 + β) • xc θ (t + 1) - β • xc θ t
      - s • (xc θ (t + 1) + ((κ - 1 : ℝ) : ℂ) * (μ (aCoef s β κ θ) (bCoef s β κ θ) * xc θ (t + 1))) := by
  have h := cycle_equation_aux s β κ θ hs hκ
  unfold xc
  simp only [Complex.real_smul]
  rw [show ζ θ ^ (t + 2) = ζ θ ^ t * ζ θ ^ 2 by ring, h]
  simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_one]
  ring

/-- Every point of `C` has norm at most `‖μ‖` (the vertices `μ x°_j` do, and the closed ball is
convex), so the remainder `∇ψ(x) - x = (κ - 1) proj_C(x)` is bounded by `(κ - 1) ‖μ‖`. -/
theorem norm_gradPsi_sub_le (m : ℕ) (a b κ : ℝ) (hκ : 1 ≤ κ) (p : ℂ → ℂ)
    (hp : IsMetricProj (Cset m a b) p) (x : ℂ) :
    ‖gradPsi κ p x - x‖ ≤ (κ - 1) * ‖μ a b‖ := by
  have hmem : p x ∈ Cset m a b := (hp x).1
  have hsub : Cset m a b ⊆ Metric.closedBall (0 : ℂ) ‖μ a b‖ := by
    apply convexHull_min _ (convex_closedBall 0 _)
    rintro _ ⟨j, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, norm_mul, norm_xc, mul_one]
  have hle : ‖p x‖ ≤ ‖μ a b‖ := by
    have := hsub hmem
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  unfold gradPsi
  rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith)]
  exact mul_le_mul_of_nonneg_left hle (by linarith)

/-- The heavy-ball update `(x, y) ↦ ((1 + β) x - β y - s G(x), x)`. -/
noncomputable def hbUpdate (s β : ℝ) (G : ℂ → ℂ) (z : ℂ × ℂ) : ℂ × ℂ :=
  ((1 + β) • z.1 - β • z.2 - s • G z.1, z.1)

/-- The linear map `𝖠₁ : (v, w) ↦ ((1 + β - s) v - β w, v)` of (3.28). -/
noncomputable def hbLin (s β : ℝ) : (ℂ × ℂ) →L[ℝ] (ℂ × ℂ) :=
  ((1 + β - s) • ContinuousLinearMap.fst ℝ ℂ ℂ - β • ContinuousLinearMap.snd ℝ ℂ ℂ).prod
    (ContinuousLinearMap.fst ℝ ℂ ℂ)

theorem hbLin_apply (s β : ℝ) (v w : ℂ) :
    hbLin s β (v, w) = ((1 + β - s) • v - β • w, v) := by
  simp [hbLin]

/-- The Jacobian (3.28) of the heavy-ball update at a point where `DG = Id`. -/
theorem hasFDerivAt_hbUpdate (s β : ℝ) (G : ℂ → ℂ) (z : ℂ × ℂ)
    (hG : HasFDerivAt G (ContinuousLinearMap.id ℝ ℂ) z.1) :
    HasFDerivAt (hbUpdate s β G) (hbLin s β) z := by
  have h1 : HasFDerivAt (fun z : ℂ × ℂ => (1 + β) • z.1 - β • z.2 - s • G z.1)
      ((1 + β) • ContinuousLinearMap.fst ℝ ℂ ℂ - β • ContinuousLinearMap.snd ℝ ℂ ℂ
        - s • (ContinuousLinearMap.id ℝ ℂ).comp (ContinuousLinearMap.fst ℝ ℂ ℂ)) z := by
    have hf := hasFDerivAt_fst (𝕜 := ℝ) (p := z) (E := ℂ) (F := ℂ)
    have hs := hasFDerivAt_snd (𝕜 := ℝ) (p := z) (E := ℂ) (F := ℂ)
    have hGz := hG.comp z hf
    exact ((hf.const_smul (1 + β)).sub (hs.const_smul β)).sub (hGz.const_smul s)
  have h2 := h1.prodMk (hasFDerivAt_fst (𝕜 := ℝ) (p := z) (E := ℂ) (F := ℂ))
  have e : ((1 + β) • ContinuousLinearMap.fst ℝ ℂ ℂ - β • ContinuousLinearMap.snd ℝ ℂ ℂ
        - s • (ContinuousLinearMap.id ℝ ℂ).comp (ContinuousLinearMap.fst ℝ ℂ ℂ)).prod
      (ContinuousLinearMap.fst ℝ ℂ ℂ) = hbLin s β := by
    ext ⟨v, w⟩ <;> simp [hbLin, sub_smul]
  rw [e] at h2
  exact h2

/-- The `n`-step update at a cycle state has Jacobian `𝖠₁^n` (chain rule along the cycle). -/
theorem hasFDerivAt_hbUpdate_iterate (s β : ℝ) (G : ℂ → ℂ) (z : ℕ → ℂ × ℂ)
    (hz : ∀ t, hbUpdate s β G (z t) = z (t + 1))
    (hG : ∀ t, HasFDerivAt G (ContinuousLinearMap.id ℝ ℂ) (z t).1) (t n : ℕ) :
    HasFDerivAt (hbUpdate s β G)^[n] (hbLin s β ^ n) (z t) := by
  induction n generalizing t with
  | zero => rw [Function.iterate_zero, pow_zero]; exact hasFDerivAt_id (z t)
  | succ n ih =>
    have hiter : ∀ k, (hbUpdate s β G)^[k] (z t) = z (t + k) := by
      intro k; induction k with
      | zero => simp
      | succ k ihk => rw [Function.iterate_succ_apply', ihk, hz]; rfl
    rw [Function.iterate_succ, pow_succ, ContinuousLinearMap.mul_def]
    have h1 := hasFDerivAt_hbUpdate s β G (z t) (hG t)
    have h2 := ih (t + 1)
    have h3 : HasFDerivAt (hbUpdate s β G)^[n] (hbLin s β ^ n) (hbUpdate s β G (z t)) := by
      rw [hz t]; exact h2
    exact h3.comp (z t) h1

/-- The spectral radius of `A_1(s, β)^m` is `ρ(A_1(s, β))^m`, and it is `< 1` when
`ρ_q(s, β; κ) < 1` (since `ρ(A_1) ≤ ρ_q`). -/
theorem spectralRadius_Amat_pow (s β κ : ℝ) (hβ : 0 ≤ β) (hs : 0 ≤ s) (hκ : 1 ≤ κ)
    (hρ : OBABO.ρq s β κ < 1) (m : ℕ) (hm : 0 < m) :
    spectralRadius ℂ (((OBABO.Section2.Amat s β 1).map (algebraMap ℝ ℂ)) ^ m)
        = ENNReal.ofReal (OBABO.rootRad (1 + β - s * 1) β ^ m) ∧
      spectralRadius ℂ (((OBABO.Section2.Amat s β 1).map (algebraMap ℝ ℂ)) ^ m) < 1 := by
  set A := (OBABO.Section2.Amat s β 1).map (algebraMap ℝ ℂ)
  set r := OBABO.rootRad (1 + β - s * 1) β
  have hr0 : 0 ≤ r := le_trans (Real.sqrt_nonneg β) (OBABO.sqrt_le_rootRad _ _)
  have hspec : spectrum ℂ (A ^ m) = (fun z => z ^ m) '' spectrum ℂ A :=
    spectrum.map_pow_of_pos A hm
  have heq : spectralRadius ℂ (A ^ m) = ENNReal.ofReal (r ^ m) := by
    apply le_antisymm
    · apply iSup₂_le
      intro z hz
      rw [hspec] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      rw [OBABO.Section2.mem_spectrum_Amat] at hw
      have := OBABO.norm_root_le (1 + β - s * 1) β hβ w hw
      rw [← enorm_eq_nnnorm, ← ofReal_norm, norm_pow]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) this m)
    · obtain ⟨w, hw, hwn⟩ := OBABO.exists_root_norm_eq (1 + β - s * 1) β hβ
      have hmem : w ^ m ∈ spectrum ℂ (A ^ m) := by
        rw [hspec]; exact ⟨w, (OBABO.Section2.mem_spectrum_Amat s β 1 w).2 hw, rfl⟩
      have h1 : ENNReal.ofReal (r ^ m) = (‖w ^ m‖₊ : ENNReal) := by
        rw [← enorm_eq_nnnorm, ← ofReal_norm, norm_pow, hwn]
      rw [h1]
      exact le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ (A ^ m)) => (‖k‖₊ : ENNReal)) (w ^ m) hmem
  refine ⟨heq, ?_⟩
  rw [heq]
  have hrρ : r ≤ OBABO.ρq s β κ :=
    le_csSup (OBABO.ρq_bddAbove s β κ hβ hs hκ) ⟨1, ⟨le_rfl, hκ⟩, rfl⟩
  have hr1 : r < 1 := lt_of_le_of_lt hrρ hρ
  have : r ^ m < 1 := pow_lt_one₀ hr0 hr1 hm.ne'
  exact ENNReal.ofReal_lt_one.2 this

/-- **Proposition 3.4** (smooth attracting cycle with stable linearization), with the
representation of `ψ` from Theorem 3.1(i) ([22, Theorem 3.5]) as hypotheses. Let `m ≥ 3` satisfy
`P_m(s, β; κ) < 0`, let `p` be the metric projection onto `C`, and let `ψ : ℂ → ℝ` have gradient
`∇ψ(x) = x + (κ - 1) p(x)` which is `1`-strongly monotone and `κ`-Lipschitz. Then there are
`U : ℂ → ℝ` and `G = ∇U`, both `C^∞`, `r₀ > 0` and `b⋆`, such that `G` is `1`-strongly monotone
and `κ`-Lipschitz (so `U ∈ U_κ²`: the Hessian `DG(x)` satisfies `⟪DG(x) v, v⟫ ≥ ‖v‖²` and
`‖DG(x) v‖ ≤ κ ‖v‖`), the cycle equation (3.25) holds, `G` is affine with slope `Id` on the balls
`B(x°_t, r₀)` (3.26), `‖G(x) - x‖ ≤ b⋆` (3.27), and `DG = Id` on each ball `B(x°_t, r₀)`. -/
theorem proposition_3_4 (m : ℕ) (hm : 3 ≤ m) (s β κ : ℝ) (hs : 0 < s) (hβ1 : β < 1)
    (hκ : 1 < κ) (hP : OBABO.Pcyc s β κ (Real.cos (2 * π / m)) < 0)
    (p : ℂ → ℂ)
    (hp : IsMetricProj (Cset m (aCoef s β κ (2 * π / m)) (bCoef s β κ (2 * π / m))) p)
    (ψ : ℂ → ℝ) (hψ : ∀ x, HasGradientAt ψ (gradPsi κ p x) x)
    (hmono : ∀ x y, ‖x - y‖ ^ 2 ≤ ⟪gradPsi κ p x - gradPsi κ p y, x - y⟫_ℝ)
    (hlip : ∀ x y, ‖gradPsi κ p x - gradPsi κ p y‖ ≤ κ * ‖x - y‖) :
    ∃ (U : ℂ → ℝ) (G : ℂ → ℂ) (r₀ b : ℝ), 0 < r₀ ∧
      ContDiff ℝ (⊤ : ℕ∞) U ∧ (∀ x, HasGradientAt U (G x) x) ∧ ContDiff ℝ (⊤ : ℕ∞) G ∧
      (∀ x y, ‖x - y‖ ^ 2 ≤ ⟪G x - G y, x - y⟫_ℝ) ∧
      (∀ x y, ‖G x - G y‖ ≤ κ * ‖x - y‖) ∧
      (∀ x v, ‖v‖ ^ 2 ≤ ⟪fderiv ℝ G x v, v⟫_ℝ ∧ ‖fderiv ℝ G x v‖ ≤ κ * ‖v‖) ∧
      (∀ t : ℕ, xc (2 * π / m) (t + 2) = (1 + β) • xc (2 * π / m) (t + 1)
        - β • xc (2 * π / m) t - s • G (xc (2 * π / m) (t + 1))) ∧
      (∀ (t : ℕ) (u : ℂ), ‖u‖ ≤ r₀ → G (xc (2 * π / m) t + u) = G (xc (2 * π / m) t) + u) ∧
      (∀ x, ‖G x - x‖ ≤ b) ∧
      (∀ (t : ℕ), ∀ x ∈ Metric.ball (xc (2 * π / m) t) r₀,
        fderiv ℝ G x = ContinuousLinearMap.id ℝ ℂ) := by
  set θ := 2 * π / m with hθ
  set a := aCoef s β κ θ
  set b := bCoef s β κ θ
  set g := gradPsi κ p with hg
  obtain ⟨hr, hloc⟩ := theorem_3_1_ii_of_Pcyc m hm s β κ hs hβ1 hκ hP p hp
  set r := rmax m hm a b with hrdef
  have hm0 : 0 < m := by omega
  -- the local identity (3.8) at every cycle point (periodicity of `x°`)
  have hloc' : ∀ (t : ℕ) (u : ℂ), ‖u‖ ≤ r → g (xc θ t + u) = g (xc θ t) + u := by
    intro t u hu
    have hper : xc θ t = xc θ (t % m) := by
      unfold xc; rw [hθ]; exact ζ_pow_mod m hm0 t
    rw [hper]
    exact hloc (t % m) (Nat.mod_lt t hm0) u hu
  -- `g(x°_t) = x°_t + (κ - 1) μ x°_t`
  have hb : b < 0 := OBABO.b_neg m hm s β κ hs hβ1 hκ
  have hI := I0_neg_of_I0_one_neg m hm a b hb (I0_one_neg_of_Pcyc_neg m hm s β κ hs hκ hP)
  have hgc : ∀ t : ℕ, g (xc θ t) = xc θ t + ((κ - 1 : ℝ) : ℂ) * (μ a b * xc θ t) := by
    intro t
    have hper : xc θ t = xc θ (t % m) := by
      unfold xc; rw [hθ]; exact ζ_pow_mod m hm0 t
    rw [hper, hg]; unfold gradPsi
    have := proj_const m hm a b hb hI p hp (t % m) (Nat.mod_lt t hm0) 0 (by rw [norm_zero]; exact hr.le)
    rw [add_zero] at this
    rw [this]
  -- the mollifier: support radius `ε = r/4`
  have hg_cont : Continuous g := by
    apply LipschitzWith.continuous (K := ⟨κ, by linarith⟩)
    apply LipschitzWith.of_dist_le_mul
    intro x y; rw [dist_eq_norm, dist_eq_norm]; exact hlip x y
  let φ : ContDiffBump (0 : ℂ) := ⟨r / 8, r / 4, by linarith, by linarith⟩
  have hφ : φ.rOut ≤ r / 2 := by show r / 4 ≤ r / 2; linarith
  set G := Mollify.moll volume φ g with hG
  set U := φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ with hU
  have hGmono := fun x y => Mollify.moll_strongMono volume φ g hg_cont hmono x y
  have hGlip := fun x y => Mollify.moll_lipschitz volume φ g hg_cont κ hlip x y
  have hGsmooth := Mollify.moll_contDiff volume φ g hg_cont
  have hGgrad := fun x => Mollify.hasGradientAt_moll volume φ ψ g κ (by linarith) hψ hlip x
  have hGaff : ∀ (t : ℕ) (u : ℂ), ‖u‖ ≤ r / 2 → G (xc θ t + u) = G (xc θ t) + u := by
    intro t u hu
    have h1 := Mollify.moll_local_affine volume φ g (xc θ t) r hφ (hloc' t) u hu
    have h0 := Mollify.moll_local_affine volume φ g (xc θ t) r hφ (hloc' t) 0 (by rw [norm_zero]; linarith)
    rw [add_zero, add_zero] at h0
    rw [← hG] at h1 h0
    rw [h1, h0]
  have hGc : ∀ t : ℕ, G (xc θ t) = g (xc θ t) := by
    intro t
    have h0 := Mollify.moll_local_affine volume φ g (xc θ t) r hφ (hloc' t) 0 (by rw [norm_zero]; linarith)
    rw [add_zero, add_zero] at h0
    exact h0
  refine ⟨U, G, r / 2, (κ - 1) * ‖μ a b‖, by linarith, ?_, hGgrad, hGsmooth, hGmono, hGlip,
    ?_, ?_, hGaff, ?_, ?_⟩
  · -- `U` is `C^∞`
    rw [hU]
    apply φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
    have hψc : Continuous ψ := continuous_iff_continuousAt.2 fun x =>
      (hψ x).differentiableAt.continuousAt
    exact hψc.locallyIntegrable
  · -- Hessian bounds
    intro x v
    have hD : HasFDerivAt G (fderiv ℝ G x) x :=
      (hGsmooth.differentiable (by simp)).differentiableAt.hasFDerivAt
    exact Mollify.hessian_bounds_of_mono_lip G κ x _ hD hGmono hGlip v
  · -- the cycle equation (3.25)
    intro t
    rw [hGc (t + 1), hgc (t + 1)]
    exact cycle_equation s β κ θ hs.ne' (by linarith) t
  · -- the bounded remainder (3.27)
    intro x
    exact Mollify.moll_remainder volume φ g hg_cont _ (norm_gradPsi_sub_le m a b κ hκ.le p hp) x
  · -- `DG = Id` on the balls
    intro t x hx
    exact (Mollify.hasFDerivAt_id_of_affine G (xc θ t) (r / 2) (hGaff t) x hx).fderiv

end OBABO.Section3
