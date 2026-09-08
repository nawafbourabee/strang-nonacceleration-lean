/-
Lemma 2.2 of

  N. Bou-Rabee, Provable non-acceleration of standard Strang splittings of kinetic
  Langevin dynamics, arXiv:2608.25279.

  A. The Schur stability criterion for the two-step position matrix `A_lambda(s, beta)` of
     (1.10): `0 < s < 2(1+beta)/kappa`, its form `h < 2/sqrt(kappa)` via (2.10), and the real
     root `z_- <= -1` beyond the stability edge.
  B. The quadratic case: the phase-space matrix (2.7) and the noise matrix `N` of the proof
     of Lemma 2.2 are read off the OBABO step; trace, determinant, characteristic polynomial
     (2.8); the two-step position matrix of (1.10); equality of the complex spectra (2.9).
  C. Lemma 2.2 on the actual matrices; the linear-algebra steps of its second assertion
     (real root `z_- <= -1`, left eigenvector, `det N = h sigma^2 > 0`, `N^T w != 0`, the scalar
     recursion `Y_{k+1} = z_- Y_k + eta_{k+1}`), and the analytic contradiction that closes
     the characteristic-function argument.

Not formalized: the passage from an invariant law to the functional equation of its
characteristic function in the second assertion.
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import StrangNonAcceleration.Proposition2_1

open Real Matrix

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

namespace Section2

/-! ## B. The quadratic case: matrices (2.7), N, (1.10), (2.8), (2.9) -/

/-- The phase-space matrix `M_λ` of (2.7). -/
noncomputable def Mmat (h r β l : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 - h ^ 2 * l / 2, h * r; -h * r * l * (1 - h ^ 2 * l / 4), β * (1 - h ^ 2 * l / 2)]

/-- The noise matrix `N` of the proof of Lemma 2.2. -/
noncomputable def Nmat (h r σ l : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![h * σ, 0; r * σ * (1 - h ^ 2 * l / 2), σ]

/-- The companion matrix `A_λ(s, β)` of (1.10). -/
noncomputable def Amat (s β l : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1 + β - s * l, -β; 1, 0]

/-- One OBABO step on the quadratic potential `λ x^2/2` (one coordinate) is the affine map
`(x, v) ↦ M_λ (x, v) + N (ξ1, ξ2)` with `β = r^2`: this is (2.7) together with the matrix `N`
of the proof of Lemma 2.2. -/
theorem step_quadratic (h r σ l x v ξ1 ξ2 : ℝ) :
    ![(step (E := ℝ) (fun y => l * y) h r σ x v ξ1 ξ2).1,
      (step (E := ℝ) (fun y => l * y) h r σ x v ξ1 ξ2).2]
      = Mmat h r (r ^ 2) l *ᵥ ![x, v] + Nmat h r σ l *ᵥ ![ξ1, ξ2] := by
  ext i
  fin_cases i <;> simp [step, Mmat, Nmat] <;> ring

theorem trace_Mmat (h r β l : ℝ) :
    (Mmat h r β l).trace = 1 + β - (h ^ 2 * (1 + β) / 2) * l := by
  simp [Mmat, Matrix.trace_fin_two]; ring

theorem det_Mmat (h r β l : ℝ) (hβ : β = r ^ 2) : (Mmat h r β l).det = β := by
  simp [Mmat, Matrix.det_fin_two]; rw [hβ]; ring

theorem trace_Amat (s β l : ℝ) : (Amat s β l).trace = 1 + β - s * l := by
  simp [Amat, Matrix.trace_fin_two]

theorem det_Amat (s β l : ℝ) : (Amat s β l).det = β := by
  simp [Amat, Matrix.det_fin_two]

open Polynomial in
/-- The characteristic polynomial (2.8) of `M_λ`, with `s = h^2(1+β)/2`. -/
theorem charpoly_Mmat (h r β l : ℝ) (hβ : β = r ^ 2) :
    (Mmat h r β l).charpoly = X ^ 2 - C (1 + β - (h ^ 2 * (1 + β) / 2) * l) * X + C β := by
  rw [Matrix.charpoly_fin_two, trace_Mmat, det_Mmat h r β l hβ]

open Polynomial in
/-- The characteristic polynomial (2.8) of `A_λ(s, β)`. -/
theorem charpoly_Amat (s β l : ℝ) :
    (Amat s β l).charpoly = X ^ 2 - C (1 + β - s * l) * X + C β := by
  rw [Matrix.charpoly_fin_two, trace_Amat, det_Amat]

/-- Both matrices have the same characteristic polynomial. -/
theorem charpoly_eq (h r β l : ℝ) (hβ : β = r ^ 2) :
    (Mmat h r β l).charpoly = (Amat (h ^ 2 * (1 + β) / 2) β l).charpoly := by
  rw [charpoly_Mmat h r β l hβ, charpoly_Amat]

/-- The complex spectrum of `A_λ(s, β)` is the root set of `z^2 - (1 + β - sλ) z + β`. -/
theorem mem_spectrum_Amat (s β l : ℝ) (z : ℂ) :
    z ∈ spectrum ℂ ((Amat s β l).map (algebraMap ℝ ℂ)) ↔
      z ^ 2 - ((1 + β - s * l : ℝ) : ℂ) * z + (β : ℂ) = 0 := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_map, charpoly_Amat]
  simp [Polynomial.IsRoot.def]

/-- (2.9): the complex spectra of `M_λ` and `A_λ(s, β)` coincide (in particular the spectral
radii do). -/
theorem spectrum_Mmat_eq (h r β l : ℝ) (hβ : β = r ^ 2) :
    spectrum ℂ ((Mmat h r β l).map (algebraMap ℝ ℂ)) =
      spectrum ℂ ((Amat (h ^ 2 * (1 + β) / 2) β l).map (algebraMap ℝ ℂ)) := by
  ext z
  simp only [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_map, charpoly_eq h r β l hβ]

/-- The noise-free position recursion (2.2) on `λ x^2/2` is the two-step linear recursion with
matrix `A_λ(s, β)`: `(X_{k+1}, X_k) = A_λ (X_k, X_{k-1})`. -/
theorem position_recursion_quadratic (h r σ l : ℝ) (X V : ℕ → ℝ)
    (hc : IsChain (E := ℝ) (fun y => l * y) h r σ (fun _ => 0) (fun _ => 0) X V) (k : ℕ) :
    ![X (k + 2), X (k + 1)] = Amat (h ^ 2 * (1 + r ^ 2) / 2) (r ^ 2) l *ᵥ ![X (k + 1), X k] := by
  have := prop_2_1 hc k
  simp only [ζ, add_zero, smul_eq_mul] at this
  ext i
  fin_cases i
  · simp [Amat, this]; ring
  · simp [Amat]

/-! ## C. Lemma 2.2 on the matrices, and the second assertion -/

/-- Lemma 2.2 for the position matrices: all `A_λ(s, β)`, `λ ∈ [1, κ]`, are Schur stable
(every complex eigenvalue has modulus `< 1`) iff `s < 2(1+β)/κ`. -/
theorem lemma_2_2_Amat (s β κ : ℝ) (hs : 0 < s) (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 1 ≤ κ) :
    (∀ l : ℝ, 1 ≤ l → l ≤ κ →
        ∀ z ∈ spectrum ℂ ((Amat s β l).map (algebraMap ℝ ℂ)), ‖z‖ < 1)
      ↔ s < 2 * (1 + β) / κ := by
  rw [← OBABO.lemma_2_2 s β κ hs hβ0 hβ1 hκ]
  simp only [mem_spectrum_Amat]

/-- Lemma 2.2 for OBABO: with `β = r^2`, `0 < r < 1`, `h > 0`, all phase-space matrices `M_λ`,
`λ ∈ [1, κ]`, are Schur stable iff `h < 2/√κ`. -/
theorem lemma_2_2_OBABO (h r κ : ℝ) (hh : 0 < h) (hr0 : 0 < r) (hr1 : r < 1) (hκ : 1 ≤ κ) :
    (∀ l : ℝ, 1 ≤ l → l ≤ κ →
        ∀ z ∈ spectrum ℂ ((Mmat h r (r ^ 2) l).map (algebraMap ℝ ℂ)), ‖z‖ < 1)
      ↔ h < 2 / √κ := by
  have hβ0 : 0 < r ^ 2 := by positivity
  have hβ1 : r ^ 2 < 1 := by nlinarith
  have hs : 0 < h ^ 2 * (1 + r ^ 2) / 2 := by positivity
  simp only [spectrum_Mmat_eq h r (r ^ 2) _ rfl]
  rw [lemma_2_2_Amat _ _ κ hs hβ0 hβ1 hκ, step_size_form h (r ^ 2) κ hh hβ0 (by linarith)]

/-- Second assertion of Lemma 2.2, first step: if `h ≥ 2/√κ` (equivalently `sκ ≥ 2(1+β)`),
`M_κ` has a real eigenvalue `z_- ≤ -1`. -/
theorem real_eigenvalue_Mmat (h r β κ : ℝ) (hβ : β = r ^ 2) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hsκ : 2 * (1 + β) ≤ (h ^ 2 * (1 + β) / 2) * κ) :
    ∃ z : ℝ, z ≤ -1 ∧ z ∈ spectrum ℝ (Mmat h r β κ) := by
  obtain ⟨z, hz, hroot⟩ := OBABO.real_root_le_neg_one (h ^ 2 * (1 + β) / 2) β κ hβ0 hβ1 hsκ
  refine ⟨z, hz, ?_⟩
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, charpoly_Mmat h r β κ hβ]
  simp [Polynomial.IsRoot.def, hroot]

/-- A real eigenvalue has a nonzero left eigenvector: `w ᵥ* M = z • w`. -/
theorem exists_left_eigenvector (M : Matrix (Fin 2) (Fin 2) ℝ) (z : ℝ) (hz : z ∈ spectrum ℝ M) :
    ∃ w : Fin 2 → ℝ, w ≠ 0 ∧ w ᵥ* M = z • w := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot.def, Matrix.eval_charpoly] at hz
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hz
  refine ⟨w, hw0, ?_⟩
  rw [Matrix.vecMul_sub, sub_eq_zero, Matrix.scalar_apply, Matrix.vecMul_diagonal_const] at hw
  rw [← hw]
  ext i; simp [mul_comm]

/-- `det N = h σ^2`. -/
theorem det_Nmat (h r σ l : ℝ) : (Nmat h r σ l).det = h * σ ^ 2 := by
  simp [Nmat, Matrix.det_fin_two]; ring

/-- `N^T w ≠ 0` for `w ≠ 0` when `h > 0`, `σ > 0`; hence `ω^2 = |N^T w|^2 > 0`. -/
theorem Nmat_transpose_mulVec_ne_zero (h r σ l : ℝ) (hh : 0 < h) (hσ : 0 < σ)
    (w : Fin 2 → ℝ) (hw : w ≠ 0) : (Nmat h r σ l)ᵀ *ᵥ w ≠ 0 := by
  intro hcon
  have hdet : (Nmat h r σ l)ᵀ.det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨w, hw, hcon⟩
  rw [Matrix.det_transpose, det_Nmat] at hdet
  have : 0 < h * σ ^ 2 := by positivity
  linarith

/-- The scalar recursion `Y_{k+1} = z_- Y_k + η_{k+1}` for `Y_k = ⟨w, Z_k⟩`, with
`η_{k+1} = ⟨w, N ξ_{k+1}⟩ = ⟨N^T w, ξ_{k+1}⟩`, from `Z_{k+1} = M Z_k + N ξ_{k+1}`. -/
theorem scalar_recursion (M N : Matrix (Fin 2) (Fin 2) ℝ) (w : Fin 2 → ℝ) (z : ℝ)
    (hw : w ᵥ* M = z • w) (Zk Zk1 ξ : Fin 2 → ℝ) (hZ : Zk1 = M *ᵥ Zk + N *ᵥ ξ) :
    dotProduct w Zk1 = z * (dotProduct w Zk) + dotProduct (Nᵀ *ᵥ w) ξ := by
  rw [hZ, dotProduct_add, Matrix.dotProduct_mulVec, hw, smul_dotProduct, smul_eq_mul,
    Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

/-- `∑_{j<n} z^{2j} ≥ n` when `z^2 ≥ 1`. -/
theorem sum_sq_pow_ge (z : ℝ) (hz : 1 ≤ z ^ 2) (n : ℕ) :
    (n : ℝ) ≤ ∑ j ∈ Finset.range n, (z ^ 2) ^ j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    have := one_le_pow₀ (M₀ := ℝ) hz (n := n)
    linarith

/-- The analytic core of the "no invariant law" argument: a function `φ : ℝ → ℂ` with
`|φ| ≤ 1`, `φ(0) = 1`, continuous at `0`, cannot satisfy `φ(t) = φ(z t) e^{-ω^2 t^2/2}` for all
`t` when `z^2 ≥ 1` and `ω > 0`.  (For the paper: `φ` is the characteristic function of the
invariant law of `Y_k`, and the functional equation expresses stationarity of
`Y_{k+1} = z_- Y_k + η_{k+1}` with `η_{k+1} ~ N(0, ω^2)` independent of `Y_k`.) -/
theorem charfun_contradiction (φ : ℝ → ℂ) (z ω : ℝ) (hz : 1 ≤ z ^ 2) (hω : 0 < ω)
    (hbound : ∀ t, ‖φ t‖ ≤ 1)
    (hfe : ∀ t, φ t = φ (z * t) * Real.exp (-(ω ^ 2 * t ^ 2 / 2)))
    (hcont : ContinuousAt φ 0) (h0 : φ 0 = 1) : False := by
  -- iterate the functional equation
  have key : ∀ n : ℕ, ∀ t, ‖φ t‖ ≤ Real.exp (-(n * (ω ^ 2 * t ^ 2 / 2))) := by
    intro n
    induction n with
    | zero => intro t; simpa using hbound t
    | succ n ih =>
      intro t
      rw [hfe t, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      have h1 := ih (z * t)
      have h2 : Real.exp (-(n * (ω ^ 2 * (z * t) ^ 2 / 2))) ≤
          Real.exp (-(n * (ω ^ 2 * t ^ 2 / 2))) := by
        rw [Real.exp_le_exp]
        have : t ^ 2 ≤ (z * t) ^ 2 := by rw [mul_pow]; nlinarith [sq_nonneg t]
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith [mul_nonneg hn (sq_nonneg ω)]
      calc ‖φ (z * t)‖ * Real.exp (-(ω ^ 2 * t ^ 2 / 2))
          ≤ Real.exp (-(n * (ω ^ 2 * t ^ 2 / 2))) * Real.exp (-(ω ^ 2 * t ^ 2 / 2)) :=
            mul_le_mul_of_nonneg_right (h1.trans h2) (Real.exp_pos _).le
        _ = Real.exp (-((n + 1 : ℕ) * (ω ^ 2 * t ^ 2 / 2))) := by
            rw [← Real.exp_add]; push_cast; ring_nf
  -- hence φ vanishes away from 0
  have hzero : ∀ t, t ≠ 0 → φ t = 0 := by
    intro t ht
    by_contra hne
    have hpos : 0 < ‖φ t‖ := norm_pos_iff.mpr hne
    have hc : 0 < ω ^ 2 * t ^ 2 / 2 := by positivity
    -- choose n with 1/(1 + n c) < ‖φ t‖
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / (‖φ t‖ * (ω ^ 2 * t ^ 2 / 2)))
    have h1 := key n t
    have h2 : Real.exp (-(n * (ω ^ 2 * t ^ 2 / 2))) ≤ 1 / (1 + n * (ω ^ 2 * t ^ 2 / 2)) := by
      rw [Real.exp_neg, inv_eq_one_div]
      apply one_div_le_one_div_of_le (by positivity)
      have := Real.add_one_le_exp (n * (ω ^ 2 * t ^ 2 / 2))
      linarith
    have h3 : 1 / (1 + n * (ω ^ 2 * t ^ 2 / 2)) < ‖φ t‖ := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ (by positivity)] at hn
      nlinarith
    linarith
  -- contradiction with continuity at 0
  have hseq : Filter.Tendsto (fun n : ℕ => φ (1 / ((n : ℝ) + 1))) Filter.atTop (nhds (φ 0)) :=
    hcont.tendsto.comp tendsto_one_div_add_atTop_nhds_zero_nat
  have hconst : (fun n : ℕ => φ (1 / ((n : ℝ) + 1))) = fun _ => 0 := by
    funext n; exact hzero _ (by positivity)
  rw [hconst, h0] at hseq
  have := tendsto_nhds_unique hseq tendsto_const_nhds
  simp at this

end Section2
end OBABO
