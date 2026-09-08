/-
Proposition 2.1 of

  N. Bou-Rabee, Provable non-acceleration of standard Strang splittings of kinetic
  Langevin dynamics, arXiv:2608.25279.

Proposition 2.1 as a pathwise identity: for any real vector space, any gradient map, and any
noise sequences, the OBABO positions satisfy the two-step recursion (2.2) with the noise term
(2.3), including the first step through the auxiliary position `X_{-1}` of (2.1); the
covariance scalars (2.4).

Not formalized: the probabilistic statements of Proposition 2.1 (independence and
Gaussianity of the `zeta_k`, the covariance as an expectation).
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

open Real Matrix

namespace OBABO
namespace Section2

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

end Section2
end OBABO
