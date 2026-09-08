/-
Section 2 of arXiv:2608.25279v1 ("OBABO position as an exact noisy heavy-ball method"):
the deterministic content.

  A. Proposition 2.1 as a pathwise identity: for any real vector space, any gradient map,
     and any noise sequences, the OBABO positions satisfy the two-step recursion (2.2)
     with the noise term (2.3), including the first step through the auxiliary
     position X_{-1} of (2.1); the covariance scalars (2.4).
  B. The quadratic case: the phase-space matrix (2.7) and the noise matrix N of the
     proof of Lemma 2.2 are read off the OBABO step; trace, determinant, characteristic
     polynomial (2.8); the two-step position matrix A_λ(s,β) of (1.10); equality of
     the complex spectra (2.9).
  C. Lemma 2.2 on the actual matrices; the linear-algebra steps of its second assertion
     (real root z_- ≤ -1, left eigenvector, det N = hσ² > 0, N^T w ≠ 0, the scalar
     recursion Y_{k+1} = z_- Y_k + η_{k+1}), and the analytic contradiction that closes
     the characteristic-function argument.

Not formalized: the probabilistic statements of Proposition 2.1 (independence and
Gaussianity of the ζ_k, covariance as an expectation) and the invariant-law and
characteristic-function steps of the second assertion of Lemma 2.2.
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import StrangNonAcceleration.Tier1

open Real Matrix

namespace OBABO
namespace Section2

/-! ## A. Proposition 2.1: the pathwise heavy-ball identity -/

section pathwise

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- One OBABO step (1.4)-(1.6) with gradient map `g`, parameters `h, r, σ`, state `(x, v)`
and noise inputs `ξ1, ξ2`; returns `(x⁺, v⁺)`. -/
noncomputable def step (g : E → E) (h r σ : ℝ) (x v ξ1 ξ2 : E) : E × E :=
  let va := r • v + σ • ξ1
  let vb := va - (h / 2) • g x
  let x' := x + h • vb
  let vc := vb - (h / 2) • g x'
  (x', r • vc + σ • ξ2)

/-- The OBABO chain: `(X (k+1), V (k+1))` is obtained from `(X k, V k)` with the noises
`ξ1 (k+1), ξ2 (k+1)`; the value `ξ2 0` is the auxiliary variable of Proposition 2.1. -/
def IsChain (g : E → E) (h r σ : ℝ) (ξ1 ξ2 X V : ℕ → E) : Prop :=
  ∀ k, (X (k + 1), V (k + 1)) = step g h r σ (X k) (V k) (ξ1 (k + 1)) (ξ2 (k + 1))

/-- The noise term (2.3): `ζ_{k+1} = hσ (r ξ2_k + ξ1_{k+1})` (here `ζ k` is `ζ_{k+1}`). -/
def ζ (h r σ : ℝ) (ξ1 ξ2 : ℕ → E) (k : ℕ) : E := (h * σ) • (r • ξ2 k + ξ1 (k + 1))

/-- Equation (2.5): `X_{k+1} - X_k = h (r V_k + σ ξ1_{k+1} - (h/2) ∇U(X_k))`. -/
theorem eq_2_5 {g : E → E} {h r σ : ℝ} {ξ1 ξ2 X V : ℕ → E}
    (hc : IsChain g h r σ ξ1 ξ2 X V) (k : ℕ) :
    X (k + 1) - X k = h • (r • V k + σ • ξ1 (k + 1) - (h / 2) • g (X k)) := by
  have := congrArg Prod.fst (hc k)
  simp only [step] at this
  rw [this]; abel

/-- Equation (2.6), multiplied by `h`: `h V_k = r ((X_k - X_{k-1}) - (h^2/2) ∇U(X_k)) + hσ ξ2_k`. -/
theorem eq_2_6 {g : E → E} {h r σ : ℝ} {ξ1 ξ2 X V : ℕ → E}
    (hc : IsChain g h r σ ξ1 ξ2 X V) (k : ℕ) :
    h • V (k + 1) = r • ((X (k + 1) - X k) - (h ^ 2 / 2) • g (X (k + 1))) + (h * σ) • ξ2 (k + 1) := by
  have h1 := congrArg Prod.fst (hc k)
  have h2 := congrArg Prod.snd (hc k)
  simp only [step] at h1 h2
  rw [h2, h1]
  module

/-- Proposition 2.1 for `k ≥ 1`: the recursion (2.2), `X_{k+1} = X_k + β(X_k - X_{k-1}) - s∇U(X_k) + ζ_{k+1}`,
with `β = r^2` and `s = h^2(1+β)/2`, holds pathwise for every noise sequence. -/
theorem prop_2_1 {g : E → E} {h r σ : ℝ} {ξ1 ξ2 X V : ℕ → E}
    (hc : IsChain g h r σ ξ1 ξ2 X V) (k : ℕ) :
    X (k + 2) = X (k + 1) + (r ^ 2) • (X (k + 1) - X k)
      - (h ^ 2 * (1 + r ^ 2) / 2) • g (X (k + 1)) + ζ h r σ ξ1 ξ2 (k + 1) := by
  have h5 := eq_2_5 hc (k + 1)
  have h6 := eq_2_6 hc k
  have hV : h • (r • V (k + 1)) = r • (h • V (k + 1)) := smul_comm _ _ _
  have : X (k + 2) = X (k + 1) + (X (k + 1 + 1) - X (k + 1)) := by abel
  rw [this, h5, smul_sub, smul_add, hV, h6]
  unfold ζ
  module

/-- Proposition 2.1, first step, through the auxiliary position `X_{-1}` of (2.1)
(written `Xm1`): if `V_0 = r ((X_0 - X_{-1})/h - (h/2)∇U(X_0)) + σ ξ2_0`, then (2.2) holds at `k = 0`. -/
theorem prop_2_1_first {g : E → E} {h r σ : ℝ} (hh : h ≠ 0) {ξ1 ξ2 X V : ℕ → E}
    (hc : IsChain g h r σ ξ1 ξ2 X V) (Xm1 : E)
    (h21 : V 0 = r • ((1 / h) • (X 0 - Xm1) - (h / 2) • g (X 0)) + σ • ξ2 0) :
    X 1 = X 0 + (r ^ 2) • (X 0 - Xm1) - (h ^ 2 * (1 + r ^ 2) / 2) • g (X 0) + ζ h r σ ξ1 ξ2 0 := by
  have h5 := eq_2_5 hc 0
  have : X 1 = X 0 + (X (0 + 1) - X 0) := by abel
  rw [this, h5, h21]
  unfold ζ
  have e : h * (r * (r * (1 / h))) = r ^ 2 := by field_simp
  simp only [smul_sub, smul_add, smul_smul]
  rw [e]
  module

/-- The covariance scalars (2.4): `h^2 σ^2 (1 + r^2) = h^2 (1 - β^2)` and `h^2 σ^2 = h^2 (1-β)`
with `β = r^2`, `σ^2 = 1 - β`. -/
theorem covariance_scalars (h r σ : ℝ) (hσ : σ ^ 2 = 1 - r ^ 2) :
    h ^ 2 * σ ^ 2 * (1 + r ^ 2) = h ^ 2 * (1 - (r ^ 2) ^ 2) ∧ h ^ 2 * σ ^ 2 = h ^ 2 * (1 - r ^ 2) := by
  constructor
  · rw [hσ]; ring
  · rw [hσ]


end pathwise

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
