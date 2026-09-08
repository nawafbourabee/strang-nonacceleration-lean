/-
Proposition 6.2 (noisy heavy-ball representation of BAOAB) of

  N. Bou-Rabee, Provable non-acceleration of standard Strang splittings of kinetic
  Langevin dynamics, arXiv:2608.25279.

The BAOAB step (6.3) to (6.5) with momentum `β = e^{-γh}` and noise scale `ς = (1 - β²)^{1/2}`,
as a pathwise map on any real vector space; the one-step position identity (6.10); the velocity
in terms of the position pair (6.11); the heavy-ball recursion (6.7) with the noise (6.8),
`ζ̃_{k+1} = (h/2) ς (ξ_k + ξ_{k+1})`, for every `k ≥ 1` and, through the auxiliary position
`X_{-1}` of (6.6), for `k = 0`; and the covariance scalars (6.9).

Not formalized: that the `ξ_k` are Gaussian and independent, hence that `(ζ̃_k)` is a centered
stationary `1`-dependent Gaussian sequence (the covariances (6.9) are recorded as identities
between the scalar coefficients).
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp

namespace OBABO
namespace Section6

section BAOAB

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- One BAOAB step (6.3) to (6.5) with gradient map `g`, step size `h`, momentum `β`, noise scale
`ς`, state `(x, v)` and noise input `ξ`; returns `(x⁺, v⁺)`. -/
noncomputable def stepBAOAB (g : E → E) (h β ς : ℝ) (x v ξ : E) : E × E :=
  let va := v - (h / 2) • g x
  let xb := x + (h / 2) • va
  let vc := β • va + ς • ξ
  let x' := xb + (h / 2) • vc
  (x', vc - (h / 2) • g x')

/-- The BAOAB chain: `(X (k+1), V (k+1))` is obtained from `(X k, V k)` with the noise `ξ (k+1)`;
the value `ξ 0` is the auxiliary variable `ξ_0` of Proposition 6.2. -/
def IsChainBAOAB (g : E → E) (h β ς : ℝ) (ξ X V : ℕ → E) : Prop :=
  ∀ k, (X (k + 1), V (k + 1)) = stepBAOAB g h β ς (X k) (V k) (ξ (k + 1))

/-- The noise term (6.8): `ζ̃_{k+1} = (h/2) ς (ξ_k + ξ_{k+1})` (here `ζB k` is `ζ̃_{k+1}`). -/
noncomputable def ζB (h ς : ℝ) (ξ : ℕ → E) (k : ℕ) : E := (h / 2 * ς) • (ξ k + ξ (k + 1))

/-- The one-step position identity (6.10):
`X_{k+1} = X_k + (h/2)(1+β)(V_k - (h/2)∇U(X_k)) + (h/2) ς ξ_{k+1}`. -/
theorem eq_6_10 {g : E → E} {h β ς : ℝ} {ξ X V : ℕ → E}
    (hc : IsChainBAOAB g h β ς ξ X V) (k : ℕ) :
    X (k + 1) = X k + (h / 2 * (1 + β)) • (V k - (h / 2) • g (X k)) + (h / 2 * ς) • ξ (k + 1) := by
  have := congrArg Prod.fst (hc k)
  simp only [stepBAOAB] at this
  rw [this]; module

/-- The velocity from the position pair, (6.11) multiplied by `(1+β) h`:
`(1+β) h V_{k+1} = 2β (X_{k+1} - X_k) + h ς ξ_{k+1} - (h²/2)(1+β) ∇U(X_{k+1})`. -/
theorem eq_6_11 {g : E → E} {h β ς : ℝ} {ξ X V : ℕ → E}
    (hc : IsChainBAOAB g h β ς ξ X V) (k : ℕ) :
    ((1 + β) * h) • V (k + 1) = (2 * β) • (X (k + 1) - X k) + (h * ς) • ξ (k + 1)
      - (h ^ 2 / 2 * (1 + β)) • g (X (k + 1)) := by
  have h1 := congrArg Prod.fst (hc k)
  have h2 := congrArg Prod.snd (hc k)
  simp only [stepBAOAB] at h1 h2
  rw [h2, h1]
  module

/-- **Proposition 6.2**, the recursion (6.7) for `k ≥ 1`:
`X_{k+1} = X_k + β(X_k - X_{k-1}) - s∇U(X_k) + ζ̃_{k+1}`, `s = h²(1+β)/2`, pathwise. -/
theorem prop_6_2 {g : E → E} {h β ς : ℝ} {ξ X V : ℕ → E}
    (hc : IsChainBAOAB g h β ς ξ X V) (k : ℕ) :
    X (k + 2) = X (k + 1) + β • (X (k + 1) - X k)
      - (h ^ 2 * (1 + β) / 2) • g (X (k + 1)) + ζB h ς ξ (k + 1) := by
  have e1 := congrArg Prod.fst (hc k)
  have e2 := congrArg Prod.snd (hc k)
  have e3 := congrArg Prod.fst (hc (k + 1))
  simp only [stepBAOAB] at e1 e2 e3
  rw [show k + 1 + 1 = k + 2 from rfl] at e3
  unfold ζB
  rw [e3, e2, e1]
  module

/-- **Proposition 6.2**, first step: if `V_0` satisfies (6.6) with the auxiliary position
`X_{-1}` (written `Xm1`), then (6.7) holds at `k = 0`. -/
theorem prop_6_2_first {g : E → E} {h β ς : ℝ} (hh : h ≠ 0) (hβ : 1 + β ≠ 0) {ξ X V : ℕ → E}
    (hc : IsChainBAOAB g h β ς ξ X V) (Xm1 : E)
    (h66 : V 0 = (2 * β / ((1 + β) * h)) • (X 0 - Xm1) + (ς / (1 + β)) • ξ 0 - (h / 2) • g (X 0)) :
    X 1 = X 0 + β • (X 0 - Xm1) - (h ^ 2 * (1 + β) / 2) • g (X 0) + ζB h ς ξ 0 := by
  have e := eq_6_10 hc 0
  rw [e, h66]
  unfold ζB
  have c1 : h / 2 * (1 + β) * (2 * β / ((1 + β) * h)) = β := by field_simp
  have c2 : h / 2 * (1 + β) * (ς / (1 + β)) = h / 2 * ς := by field_simp
  simp only [smul_sub, smul_add, smul_smul]
  rw [c1, c2]
  module

/-- The covariance scalars (6.9): with `ς² = 1 - β²`, the noise `ζ̃_{k+1} = (h/2)ς(ξ_k + ξ_{k+1})`
of two independent standard Gaussian inputs has covariance `2 (h ς/2)² = h²(1 - β²)/2`, the
cross covariance of consecutive terms is `(h ς/2)² = h²(1 - β²)/4`, and the first term
`(h/2) ς ξ_1` (case `ξ_0 = 0`) has covariance `h²(1 - β²)/4`. -/
theorem covariance_scalars_BAOAB (h β ς : ℝ) (hς : ς ^ 2 = 1 - β ^ 2) :
    2 * (h / 2 * ς) ^ 2 = h ^ 2 * (1 - β ^ 2) / 2 ∧ (h / 2 * ς) ^ 2 = h ^ 2 * (1 - β ^ 2) / 4 := by
  constructor <;> · rw [mul_pow, hς]; ring

end BAOAB

end Section6
end OBABO
