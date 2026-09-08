/-
Lemma 4.6 of

  N. Bou-Rabee, Provable non-acceleration of standard Strang splittings of kinetic
  Langevin dynamics, arXiv:2608.25279.

The exact three-cycle of the noise-free recurrence, the bounds (4.24) and (4.25), and the
bootstrap to the tube of radius `1/20`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import StrangNonAcceleration.Section4_5

open Real

namespace OBABO
namespace Cycle

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

end Cycle
end OBABO
