/-
Proposition 6.5 (noisy heavy-ball representations of the remaining Strang splittings) of

  N. Bou-Rabee, Provable non-acceleration of standard Strang splittings of kinetic
  Langevin dynamics, arXiv:2608.25279.

The steps of ABOBA, AOBOA, BOAOB and OABAO as pathwise maps on any real vector space, with
`β = e^{-γh}`, `r = e^{-γh/2}` (so `β = r²`), `σ = (1 - β)^{1/2}` and `ς = (1 - β²)^{1/2}`, and
the four heavy-ball representations (6.13), (6.14), (6.16) (with the first step through the
auxiliary position (6.15)) and (6.17), together with the identities `Y_{m+1} - Y_m = h V_m` for
the force-evaluation points of ABOBA and AOBOA and the covariance scalars.

Not formalized: that the driving variables are Gaussian and independent, hence the
distributional statements about the noise sequences.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp

namespace OBABO
namespace Section6

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ## (i) ABOBA -/

/-- One ABOBA step: `A_{h/2} B_{h/2} O_h B_{h/2} A_{h/2}`, with both half kicks at the
force-evaluation point `y = x + (h/2) v`. -/
noncomputable def stepABOBA (g : E → E) (h β ς : ℝ) (x v ξ : E) : E × E :=
  let y := x + (h / 2) • v
  let v' := β • (v - (h / 2) • g y) + ς • ξ - (h / 2) • g y
  (y + (h / 2) • v', v')

def IsChainABOBA (g : E → E) (h β ς : ℝ) (ξ X V : ℕ → E) : Prop :=
  ∀ m, (X (m + 1), V (m + 1)) = stepABOBA g h β ς (X m) (V m) (ξ (m + 1))

/-- ABOBA: the force-evaluation points `Y_{m+1} = X_m + (h/2) V_m`, `Y_0 = X_0 - (h/2) V_0`,
satisfy `Y_{m+1} - Y_m = h V_m`. -/
theorem ABOBA_Y_diff {g : E → E} {h β ς : ℝ} {ξ X V : ℕ → E}
    (hc : IsChainABOBA g h β ς ξ X V) (Y : ℕ → E) (hY0 : Y 0 = X 0 - (h / 2) • V 0)
    (hY : ∀ m, Y (m + 1) = X m + (h / 2) • V m) (m : ℕ) :
    Y (m + 1) - Y m = h • V m := by
  cases m with
  | zero => rw [hY, hY0]; module
  | succ m =>
    have e1 := congrArg Prod.fst (hc m)
    simp only [stepABOBA] at e1
    rw [hY, hY, e1]
    have e2 := congrArg Prod.snd (hc m)
    simp only [stepABOBA] at e2
    rw [e2]; module

/-- **Proposition 6.5(i)**, the recursion (6.13) for the ABOBA force-evaluation points:
`Y_{m+1} = Y_m + β(Y_m - Y_{m-1}) - s∇U(Y_m) + hς ξ_m`, `s = h²(1+β)/2`, for `m ≥ 1`. -/
theorem prop_6_5_i {g : E → E} {h β ς : ℝ} {ξ X V : ℕ → E}
    (hc : IsChainABOBA g h β ς ξ X V) (Y : ℕ → E) (hY0 : Y 0 = X 0 - (h / 2) • V 0)
    (hY : ∀ m, Y (m + 1) = X m + (h / 2) • V m) (m : ℕ) :
    Y (m + 2) = Y (m + 1) + β • (Y (m + 1) - Y m) - (h ^ 2 * (1 + β) / 2) • g (Y (m + 1))
      + (h * ς) • ξ (m + 1) := by
  have d1 := ABOBA_Y_diff hc Y hY0 hY (m + 1)
  have d0 := ABOBA_Y_diff hc Y hY0 hY m
  have e2 := congrArg Prod.snd (hc m)
  simp only [stepABOBA] at e2
  rw [← hY m] at e2
  rw [show m + 2 = m + 1 + 1 from rfl, show Y (m + 1 + 1) = Y (m + 1) + (Y (m + 1 + 1) - Y (m + 1)) by module,
    d1, e2, show β • (Y (m + 1) - Y m) = β • (h • V m) by rw [d0]]
  module

/-- ABOBA noise covariance scalar: `(hς)² = h²(1 - β²)`. -/
theorem covariance_scalar_ABOBA (h β ς : ℝ) (hς : ς ^ 2 = 1 - β ^ 2) :
    (h * ς) ^ 2 = h ^ 2 * (1 - β ^ 2) := by rw [mul_pow, hς]

/-! ## (ii) AOBOA -/

/-- One AOBOA step: `A_{h/2} O_{h/2} B_h O_{h/2} A_{h/2}`, with the half-step factor `r`
(`β = r²`) and the two noise inputs `ξ1, ξ2` of the two `O` half steps. -/
noncomputable def stepAOBOA (g : E → E) (h r σ : ℝ) (x v ξ1 ξ2 : E) : E × E :=
  let y := x + (h / 2) • v
  let v1 := r • v + σ • ξ1
  let v2 := v1 - h • g y
  let v' := r • v2 + σ • ξ2
  (y + (h / 2) • v', v')

def IsChainAOBOA (g : E → E) (h r σ : ℝ) (ξ1 ξ2 X V : ℕ → E) : Prop :=
  ∀ m, (X (m + 1), V (m + 1)) = stepAOBOA g h r σ (X m) (V m) (ξ1 (m + 1)) (ξ2 (m + 1))

/-- AOBOA: `Y_{m+1} - Y_m = h V_m` for the force-evaluation points. -/
theorem AOBOA_Y_diff {g : E → E} {h r σ : ℝ} {ξ1 ξ2 X V : ℕ → E}
    (hc : IsChainAOBOA g h r σ ξ1 ξ2 X V) (Y : ℕ → E) (hY0 : Y 0 = X 0 - (h / 2) • V 0)
    (hY : ∀ m, Y (m + 1) = X m + (h / 2) • V m) (m : ℕ) :
    Y (m + 1) - Y m = h • V m := by
  cases m with
  | zero => rw [hY, hY0]; module
  | succ m =>
    have e1 := congrArg Prod.fst (hc m)
    have e2 := congrArg Prod.snd (hc m)
    simp only [stepAOBOA] at e1 e2
    rw [hY, hY, e1, e2]; module

/-- **Proposition 6.5(ii)**, the recursion (6.14) for the AOBOA force-evaluation points:
`Y_{m+1} = Y_m + β(Y_m - Y_{m-1}) - s∇U(Y_m) + hσ(r ξ¹_m + ξ²_m)`, `β = r²`, `s = √β h² = r h²`. -/
theorem prop_6_5_ii {g : E → E} {h r σ : ℝ} {ξ1 ξ2 X V : ℕ → E}
    (hc : IsChainAOBOA g h r σ ξ1 ξ2 X V) (Y : ℕ → E) (hY0 : Y 0 = X 0 - (h / 2) • V 0)
    (hY : ∀ m, Y (m + 1) = X m + (h / 2) • V m) (m : ℕ) :
    Y (m + 2) = Y (m + 1) + (r ^ 2) • (Y (m + 1) - Y m) - (r * h ^ 2) • g (Y (m + 1))
      + (h * σ) • (r • ξ1 (m + 1) + ξ2 (m + 1)) := by
  have d1 := AOBOA_Y_diff hc Y hY0 hY (m + 1)
  have d0 := AOBOA_Y_diff hc Y hY0 hY m
  have e2 := congrArg Prod.snd (hc m)
  simp only [stepAOBOA] at e2
  rw [← hY m] at e2
  rw [show m + 2 = m + 1 + 1 from rfl, show Y (m + 1 + 1) = Y (m + 1) + (Y (m + 1 + 1) - Y (m + 1)) by module,
    d1, e2, show (r ^ 2) • (Y (m + 1) - Y m) = (r ^ 2) • (h • V m) by rw [d0]]
  module

/-- AOBOA noise covariance scalar: `(hσ)²(r² + 1) = h²(1 - β²)` with `σ² = 1 - r²`, `β = r²`. -/
theorem covariance_scalar_AOBOA (h r σ : ℝ) (hσ : σ ^ 2 = 1 - r ^ 2) :
    (h * σ) ^ 2 * (r ^ 2 + 1) = h ^ 2 * (1 - (r ^ 2) ^ 2) := by rw [mul_pow, hσ]; ring

/-! ## (iii) BOAOB -/

/-- One BOAOB step: `B_{h/2} O_{h/2} A_h O_{h/2} B_{h/2}`. -/
noncomputable def stepBOAOB (g : E → E) (h r σ : ℝ) (x v ξ1 ξ2 : E) : E × E :=
  let v1 := v - (h / 2) • g x
  let vb := r • v1 + σ • ξ1
  let x' := x + h • vb
  let v2 := r • vb + σ • ξ2
  (x', v2 - (h / 2) • g x')

def IsChainBOAOB (g : E → E) (h r σ : ℝ) (ξ1 ξ2 X V : ℕ → E) : Prop :=
  ∀ k, (X (k + 1), V (k + 1)) = stepBOAOB g h r σ (X k) (V k) (ξ1 (k + 1)) (ξ2 (k + 1))

/-- **Proposition 6.5(iii)**, the recursion (6.16) for `k ≥ 1`:
`X_{k+1} = X_k + β(X_k - X_{k-1}) - s∇U(X_k) + hσ(r ξ²_k + ξ¹_{k+1})`, `β = r²`, `s = r h²`. -/
theorem prop_6_5_iii {g : E → E} {h r σ : ℝ} {ξ1 ξ2 X V : ℕ → E}
    (hc : IsChainBOAOB g h r σ ξ1 ξ2 X V) (k : ℕ) :
    X (k + 2) = X (k + 1) + (r ^ 2) • (X (k + 1) - X k) - (r * h ^ 2) • g (X (k + 1))
      + (h * σ) • (r • ξ2 (k + 1) + ξ1 (k + 2)) := by
  have e1 := congrArg Prod.fst (hc k)
  have e2 := congrArg Prod.snd (hc k)
  have e3 := congrArg Prod.fst (hc (k + 1))
  simp only [stepBOAOB] at e1 e2 e3
  rw [show k + 1 + 1 = k + 2 from rfl] at e3
  rw [e3, e2, e1]
  module

/-- **Proposition 6.5(iii)**, first step: if `V_0` satisfies (6.15) with the auxiliary position
`X_{-1}` (written `Xm1`), then (6.16) holds at `k = 0`. -/
theorem prop_6_5_iii_first {g : E → E} {h r σ : ℝ} (hh : h ≠ 0) {ξ1 ξ2 X V : ℕ → E}
    (hc : IsChainBOAOB g h r σ ξ1 ξ2 X V) (Xm1 : E)
    (h615 : V 0 = (r / h) • (X 0 - Xm1) + σ • ξ2 0 - (h / 2) • g (X 0)) :
    X 1 = X 0 + (r ^ 2) • (X 0 - Xm1) - (r * h ^ 2) • g (X 0)
      + (h * σ) • (r • ξ2 0 + ξ1 1) := by
  have e1 := congrArg Prod.fst (hc 0)
  simp only [stepBOAOB] at e1
  rw [e1, h615]
  have c1 : h * (r * (r / h)) = r ^ 2 := by field_simp
  simp only [smul_sub, smul_add, smul_smul]
  rw [c1]
  module

/-- BOAOB noise covariance scalars: `(hσ)²(r² + 1) = h²(1 - β²)` and `(hσ)² = h²(1 - β)`. -/
theorem covariance_scalars_BOAOB (h r σ : ℝ) (hσ : σ ^ 2 = 1 - r ^ 2) :
    (h * σ) ^ 2 * (r ^ 2 + 1) = h ^ 2 * (1 - (r ^ 2) ^ 2) ∧ (h * σ) ^ 2 = h ^ 2 * (1 - r ^ 2) := by
  constructor
  · rw [mul_pow, hσ]; ring
  · rw [mul_pow, hσ]

/-! ## (iv) OABAO -/

/-- One OABAO step: `O_{h/2} A_{h/2} B_h A_{h/2} O_{h/2}`. -/
noncomputable def stepOABAO (g : E → E) (h r σ : ℝ) (x v ξ1 ξ2 : E) : E × E :=
  let va := r • v + σ • ξ1
  let y := x + (h / 2) • va
  let vc := va - h • g y
  (y + (h / 2) • vc, r • vc + σ • ξ2)

def IsChainOABAO (g : E → E) (h r σ : ℝ) (ξ1 ξ2 X V : ℕ → E) : Prop :=
  ∀ m, (X (m + 1), V (m + 1)) = stepOABAO g h r σ (X m) (V m) (ξ1 (m + 1)) (ξ2 (m + 1))

/-- The combined noise `χ_{m+1} = r ξ²_m + ξ¹_{m+1}` of Proposition 6.5(iv) (here `χ k` is
`χ_{k+1}`). -/
def χ (r : ℝ) (ξ1 ξ2 : ℕ → E) (k : ℕ) : E := r • ξ2 k + ξ1 (k + 1)

/-- **Proposition 6.5(iv)**, the recursion (6.17) for the OABAO force-evaluation points
`Y_{m+1} = X_m + (h/2)(r V_m + σ ξ¹_{m+1})`: for `m ≥ 2`,
`Y_{m+1} = Y_m + β(Y_m - Y_{m-1}) - s∇U(Y_m) + (h/2)σ(χ_m + χ_{m+1})`, `β = r²`, `s = h²(1+β)/2`. -/
theorem prop_6_5_iv {g : E → E} {h r σ : ℝ} {ξ1 ξ2 X V : ℕ → E}
    (hc : IsChainOABAO g h r σ ξ1 ξ2 X V) (Y : ℕ → E)
    (hY : ∀ m, Y (m + 1) = X m + (h / 2) • (r • V m + σ • ξ1 (m + 1))) (m : ℕ) :
    Y (m + 3) = Y (m + 2) + (r ^ 2) • (Y (m + 2) - Y (m + 1))
      - (h ^ 2 * (1 + r ^ 2) / 2) • g (Y (m + 2))
      + (h / 2 * σ) • (χ r ξ1 ξ2 (m + 1) + χ r ξ1 ξ2 (m + 2)) := by
  -- step `m+1` from `(X m, V m)` and step `m+2` from `(X (m+1), V (m+1))`
  have e1 := congrArg Prod.fst (hc m)
  have e2 := congrArg Prod.snd (hc m)
  have e3 := congrArg Prod.fst (hc (m + 1))
  have e4 := congrArg Prod.snd (hc (m + 1))
  simp only [stepOABAO] at e1 e2 e3 e4
  rw [show m + 1 + 1 = m + 2 from rfl] at e3 e4
  have y1 := hY m
  have y2 := hY (m + 1)
  have y3 := hY (m + 2)
  rw [show m + 1 + 1 = m + 2 from rfl] at y2
  rw [show m + 2 + 1 = m + 3 from rfl] at y3
  unfold χ
  rw [y3, y2, y1, e3, e4, e1, e2]
  module

/-- OABAO noise covariance scalars: `σ²(r² + 1) = 1 - β²` (the covariance scalar of `σχ_m`),
so that the noise `(h/2)σ(χ_m + χ_{m+1})` of two such independent terms has the covariance
scalars (6.9): `2 (h/2)² σ²(r² + 1) = h²(1 - β²)/2` and, for the cross term of consecutive
noises, `(h/2)² σ²(r² + 1) = h²(1 - β²)/4`. -/
theorem covariance_scalars_OABAO (h r σ : ℝ) (hσ : σ ^ 2 = 1 - r ^ 2) :
    σ ^ 2 * (r ^ 2 + 1) = 1 - (r ^ 2) ^ 2 ∧
      2 * ((h / 2) ^ 2 * (σ ^ 2 * (r ^ 2 + 1))) = h ^ 2 * (1 - (r ^ 2) ^ 2) / 2 ∧
      (h / 2) ^ 2 * (σ ^ 2 * (r ^ 2 + 1)) = h ^ 2 * (1 - (r ^ 2) ^ 2) / 4 := by
  refine ⟨?_, ?_, ?_⟩ <;> · rw [hσ]; ring

end Section6
end OBABO
