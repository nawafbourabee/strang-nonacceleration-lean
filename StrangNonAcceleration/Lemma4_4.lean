/-
The deterministic core of Lemma 4.4(i) of

  N. Bou-Rabee, Provable non-acceleration of standard Strang splittings of kinetic
  Langevin dynamics, arXiv:2608.25279.

* Geometric decay from the spectral radius (Gelfand's formula): the constants `(C, q)` with
  `‖M^n‖ ≤ C q^n` after Assumption 2.
* The invariant tube of Lemma 4.4(i): if the error recursion is linear inside the tube and
  the noise is small, the errors never leave the tube.
* The derivation of the error recursion from (4.5), (4.6), (4.10).

Parts (ii) and (iii) of Lemma 4.4 (total variation separation, union bound) and the
passage from the full-cycle product to the partial products in (4.8) are not formalized.
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic

open Complex Real
open scoped InnerProductSpace ComplexConjugate

namespace OBABO.Section3

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

end OBABO.Section3
