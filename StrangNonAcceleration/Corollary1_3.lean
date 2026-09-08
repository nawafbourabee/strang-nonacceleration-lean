/-
Supplementary material for

  N. Bou-Rabee, "Provable non-acceleration of standard Strang splittings of
  kinetic Langevin dynamics", arXiv:2608.25279.

Lean 4 / Mathlib formalization of the proof of Corollary 1.3.

Scope.  The corollary is deduced in the paper from Theorem 5.1 (part (i)) and
from Theorem 1.1 together with the triangle inequality for total variation
(part (ii)).  What is formalized here is exactly that deduction.  The analytic
content of the two cited theorems (Markov kernels, total variation and
Wasserstein distances, invariant laws) is not formalized; it enters through
real-valued functions and hypotheses that record precisely the properties the
proof in Section 5 of the paper uses.  The correspondence is spelled out in the
docstrings and in the README.

Conventions.  Total variation distances, Wasserstein distances and mixing times
are represented by real-valued functions of the iteration number.  `tmix TV ε`
is the least `n` with `TV n ≤ ε`.  Real powers `x ^ y` with `y : ℝ` are
Mathlib's `Real.rpow`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Lattice.Nat

open Real Filter Topology

namespace OBABO

/-! ## Elementary numerical facts -/

/-- `0.36 < e⁻¹ < 1`. -/
lemma exp_neg_one_bounds : (0.36 : ℝ) < exp (-1) ∧ exp (-1) < 1 := by
  constructor
  · rw [exp_neg]
    have h1 : exp 1 < 2.7182818286 := exp_one_lt_d9
    have h2 : (1 : ℝ) / 2.7182818286 < (exp 1)⁻¹ := by
      rw [← one_div]
      exact one_div_lt_one_div_of_lt (exp_pos 1) h1
    linarith [show (0.36 : ℝ) < 1 / 2.7182818286 by norm_num]
  · rw [exp_neg, inv_lt_one_iff₀]
    right
    exact one_lt_exp_iff.2 one_pos

/-- The threshold `C_GTD = (3 + √5)²` exceeds `27`. -/
lemma C_GTD_gt : (27 : ℝ) < (3 + √5) ^ 2 := by
  have h : (2.2 : ℝ) < √5 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  nlinarith [Real.sqrt_nonneg 5]

/-! ## Part (i): the mixing time bound of Corollary 1.3(i)

Theorem 5.1 of the paper gives, for the tuning `h = 1/(4√κ)`, `γ = 4√κ`, and
every `U ∈ U^d_κ`, `z`, `n ≥ 0`,

  `‖δ_z Q^n − π‖_TV ≤ C κ (1 + W₂(δ_z, π)) exp(−c n / κ)`,
  `C = 143`,  `c = 1 / (128 (1 − e⁻¹))`.

Part (i) of Corollary 1.3 solves this bound for the mixing time.  Below, `TV n`
stands for `‖δ_z Q^n − π‖_TV` and `W` for `W₂(δ_z, π)`. -/

/-- The constant `c` of Theorem 5.1. -/
noncomputable def cDiff : ℝ := 1 / (128 * (1 - exp (-1)))

lemma cDiff_pos : 0 < cDiff := by
  unfold cDiff
  have := exp_neg_one_bounds.2
  positivity

/-- `1/c + 1 < 83`, as used in the proof of Corollary 1.3(i). -/
lemma one_div_cDiff_add_one_lt : 1 / cDiff + 1 < 83 := by
  unfold cDiff
  have := exp_neg_one_bounds.1
  have hpos : 0 < 1 - exp (-1) := by linarith [exp_neg_one_bounds.2]
  rw [one_div_one_div]
  nlinarith

/-- The mixing time `t_mix(z, ε; Q, π)`: the least `n` with `‖δ_z Q^n − π‖_TV ≤ ε`,
for a given distance profile `TV : ℕ → ℝ`.  The paper uses the convention
`inf ∅ = ∞`, while `sInf ∅ = 0` in `ℕ`; the theorem below asserts that the set
is nonempty, so the two conventions agree there. -/
noncomputable def tmix (TV : ℕ → ℝ) (ε : ℝ) : ℕ := sInf {n : ℕ | TV n ≤ ε}

/-- **Corollary 1.3(i).**  If `TV n ≤ 143 κ (1 + W) exp(−c n/κ)` for all `n`
(the conclusion of Theorem 5.1), then for every `ε ∈ (0,1)`,

  `t_mix ≤ C₁ κ log (C₁ κ (1 + W) / ε)`,   `C₁ = 143`. -/
theorem corollary_1_3_i (κ W : ℝ) (hκ : 1 < κ) (hW : 0 ≤ W) (TV : ℕ → ℝ)
    (hTV : ∀ n : ℕ, TV n ≤ 143 * κ * (1 + W) * exp (-(cDiff * n) / κ))
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    {n : ℕ | TV n ≤ ε}.Nonempty ∧
      (tmix TV ε : ℝ) ≤ 143 * κ * log (143 * κ * (1 + W) / ε) := by
  have hc := cDiff_pos
  have hκ0 : 0 < κ := by linarith
  have hA : (143 : ℝ) < 143 * κ * (1 + W) / ε := by
    rw [lt_div_iff₀ hε0]
    have : (143 : ℝ) * ε < 143 * κ := by nlinarith
    nlinarith
  set L := log (143 * κ * (1 + W) / ε) with hL
  have hL1 : 1 ≤ L := by
    rw [hL, le_log_iff_exp_le (by positivity)]
    have := exp_one_lt_d9
    linarith
  have hL0 : 0 ≤ L := by linarith
  set x := κ / cDiff * L with hx
  have hx0 : 0 ≤ x := by positivity
  -- the candidate time `n₀ = ⌈x⌉₊` satisfies the accuracy requirement
  have hmem : ⌈x⌉₊ ∈ {n : ℕ | TV n ≤ ε} := by
    show TV ⌈x⌉₊ ≤ ε
    have hceil : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
    have hexp : exp (-(cDiff * (⌈x⌉₊ : ℝ)) / κ) ≤ exp (-L) := by
      rw [exp_le_exp]
      have : L ≤ cDiff * (⌈x⌉₊ : ℝ) / κ := by
        rw [le_div_iff₀ hκ0]
        calc L * κ = cDiff * x := by rw [hx]; field_simp
          _ ≤ cDiff * (⌈x⌉₊ : ℝ) := by gcongr
      rw [neg_div]
      linarith
    calc TV ⌈x⌉₊ ≤ 143 * κ * (1 + W) * exp (-(cDiff * ⌈x⌉₊) / κ) := hTV _
      _ ≤ 143 * κ * (1 + W) * exp (-L) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = ε := by
        rw [exp_neg, hL, exp_log (by positivity)]
        field_simp
  have h1 : (tmix TV ε : ℝ) ≤ (⌈x⌉₊ : ℝ) := by
    exact_mod_cast Nat.sInf_le hmem
  have h2 : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  -- `x + 1 ≤ (1/c + 1) κ L ≤ 143 κ L`, using `κ L ≥ 1`
  have hκL : 1 ≤ κ * L := by nlinarith
  have h3 : x + 1 ≤ (1 / cDiff + 1) * (κ * L) := by
    rw [hx]
    have : κ / cDiff * L = 1 / cDiff * (κ * L) := by field_simp
    rw [this]
    nlinarith
  have h4 : (1 / cDiff + 1) * (κ * L) ≤ 143 * (κ * L) := by
    have := one_div_cDiff_add_one_lt
    nlinarith
  refine ⟨⟨⌈x⌉₊, hmem⟩, ?_⟩
  calc (tmix TV ε : ℝ) ≤ (⌈x⌉₊ : ℝ) := h1
    _ ≤ x + 1 := h2.le
    _ ≤ (1 / cDiff + 1) * (κ * L) := h3
    _ ≤ 143 * (κ * L) := h4
    _ = 143 * κ * L := by ring

/-! ## Part (ii): sharpness of the diffusive scale

The objects of Theorem 1.1 are abstracted into the structure `TuningData`.
For a fixed numerically stable fixed-parameter tuning rule `t`, evaluated on
the normalized two-dimensional class `U^2_κ`:

* `Adm κ U`             : `U ∈ U^2_κ`;
* `HasInv κ U`          : the kernel `Q^U_{h_κ,γ_κ}` has a unique invariant law `π`;
* `TV κ U z n`          : `‖δ_z (Q^U_{h_κ,γ_κ})^n − π‖_TV`;
* `TVpair κ U z z' n`   : `‖δ_z (Q^U_{h_κ,γ_κ})^n − δ_{z'} (Q^U_{h_κ,γ_κ})^n‖_TV`;
* `W2 κ U z`            : `W₂(δ_z, π)`.

The three recorded properties are nonnegativity of total variation and
Wasserstein distances and the triangle inequality through the invariant law,
which is the only property of total variation used in Section 5. -/

structure TuningData where
  Target : Type
  State : Type
  Adm : ℝ → Target → Prop
  HasInv : ℝ → Target → Prop
  TV : ℝ → Target → State → ℕ → ℝ
  TVpair : ℝ → Target → State → State → ℕ → ℝ
  W2 : ℝ → Target → State → ℝ
  TVpair_nonneg : ∀ κ U z z' n, 0 ≤ TVpair κ U z z' n
  W2_nonneg : ∀ κ U z, 0 ≤ W2 κ U z
  TVpair_le : ∀ κ U z z' n, HasInv κ U → TVpair κ U z z' n ≤ TV κ U z n + TV κ U z' n

/-- `C_GTD = (3 + √5)²`. -/
noncomputable def C_GTD : ℝ := (3 + √5) ^ 2

/-- The threshold `q_κ = (1 − C⋆/κ)/(1 + C⋆/κ)` of (1.9). -/
noncomputable def q (Cs κ : ℝ) : ℝ := (1 - Cs / κ) / (1 + Cs / κ)

/-- Case (Q) of Theorem 1.1 at condition number `κ`: a Gaussian target `U = U_λ`
in `U^2_κ` with an invariant law, and two initial states whose asymptotic
total variation contraction factor `ρ` satisfies `ρ ≥ q_κ`, i.e. (1.11). -/
def CaseQ (D : TuningData) (Cs κ : ℝ) : Prop :=
  ∃ U z z' ρ, D.Adm κ U ∧ D.HasInv κ U ∧ q Cs κ ≤ ρ ∧
    Tendsto (fun n : ℕ => D.TVpair κ U z z' n ^ (1 / (n : ℝ))) atTop (nhds ρ)

/-- Case (C) of Theorem 1.1 at condition number `κ`: constants `c₀, C₀ > 0` and,
for every `R ≥ 1`, a target (the dilation `U_R`) in `U^2_κ` with a unique
invariant law and an initial state `z_R` satisfying (1.12) and (1.13). -/
def CaseC (D : TuningData) (κ : ℝ) : Prop :=
  ∃ c₀ C₀ : ℝ, 0 < c₀ ∧ 0 < C₀ ∧ ∀ R : ℝ, 1 ≤ R → ∃ U z, D.Adm κ U ∧ D.HasInv κ U ∧
    D.W2 κ U z ≤ C₀ * (1 + R) ∧
    ∀ n : ℕ, n ≤ ⌊exp (c₀ * R ^ 2) / 16⌋₊ → 3 / 8 ≤ D.TV κ U z n

/-- Inequality (5.2): `q_κ > exp(−c/τ(κ))` when `κ > C⋆²`, `C⋆ > 27`, and
`c κ / τ(κ) ≥ 5 C⋆`.  Stated with `t = c/τ(κ)` and `x = C⋆/κ`. -/
lemma exp_neg_lt_q (Cs κ t : ℝ) (hCs : 27 < Cs) (hκ : Cs ^ 2 < κ) (ht : 5 * (Cs / κ) ≤ t) :
    exp (-t) < q Cs κ := by
  have hCs0 : 0 < Cs := by linarith
  have hκ0 : 0 < κ := by nlinarith
  set x := Cs / κ with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x < 1 / 27 := by
    rw [hx, div_lt_div_iff₀ hκ0 (by norm_num)]
    nlinarith
  have hq : q Cs κ = (1 - x) / (1 + x) := rfl
  have hden : 0 < 1 + x := by linarith
  rw [hq, lt_div_iff₀ hden]
  by_cases h1 : 1 ≤ t
  · -- `exp(−t) ≤ e⁻¹ < 13/14 ≤ q_κ`
    have he : exp (-t) ≤ exp (-1) := by rw [exp_le_exp]; linarith
    have hhalf : exp (-1) < 1 / 2 := by
      rw [exp_neg, inv_lt_comm₀ (exp_pos 1) (by norm_num)]
      have := exp_one_gt_two
      norm_num
      linarith
    have hq' : (13 : ℝ) / 14 * (1 + x) ≤ 1 - x := by nlinarith
    have h1' : exp (-t) * (1 + x) ≤ exp (-1) * (1 + x) :=
      mul_le_mul_of_nonneg_right he hden.le
    have h2' : exp (-1) * (1 + x) < 1 / 2 * (1 + x) := mul_lt_mul_of_pos_right hhalf hden
    linarith
  · -- `1 − exp(−t) ≥ t/(1+t) ≥ t/2 > 2x ≥ 1 − q_κ`
    push Not at h1
    have ht0 : 0 < t := by nlinarith
    have hexp : exp (-t) ≤ 1 / (1 + t) := by
      rw [exp_neg, inv_eq_one_div]
      apply one_div_le_one_div_of_le (by linarith)
      linarith [add_one_le_exp t]
    have h2 : 1 / (1 + t) ≤ 1 - t / 2 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have h3 : exp (-t) ≤ 1 - t / 2 := hexp.trans h2
    nlinarith

/-- `K ^ (1/n) → 1` as `n → ∞`, for `K > 0`. -/
lemma tendsto_rpow_one_div_natCast (K : ℝ) (hK : 0 < K) :
    Tendsto (fun n : ℕ => K ^ (1 / (n : ℝ))) atTop (nhds 1) := by
  have h : ∀ n : ℕ, K ^ (1 / (n : ℝ)) = exp (log K / n) := by
    intro n
    rw [rpow_def_of_pos hK]
    congr 1
    ring
  simp_rw [h]
  have hcont : Tendsto exp (nhds 0) (nhds 1) := by
    simpa using Real.continuous_exp.tendsto 0
  exact hcont.comp (tendsto_const_div_atTop_nhds_zero_nat (log K))

/-- **Corollary 1.3(ii).**  Let `t` be a numerically stable fixed-parameter OBABO
tuning rule (abstracted as `D`), for which the dichotomy of Theorem 1.1 holds
at every `κ ≥ 2C⋆` (hypothesis `dich`).  Let `C, c > 0`, `b ≥ 0`, `a` real
(the paper assumes `a ≥ 0`; the sign of `a` is not used), let
`τ(κ) = o(κ)`, and `κ₀ > 1`.  Then there are `κ ≥ κ₀`, `U ∈ U^2_κ` with an
invariant law, `z`, and `n` for which (1.14) holds:

  `‖δ_z (Q^U_{h_κ,γ_κ})^n − π‖_TV > C κ^a (1 + W₂(δ_z,π))^b exp(−c n/τ(κ))`. -/
theorem corollary_1_3_ii (D : TuningData) (Cs : ℝ) (hCs : C_GTD < Cs)
    (dich : ∀ κ : ℝ, 2 * Cs ≤ κ → CaseQ D Cs κ ∨ CaseC D κ)
    (C c a b : ℝ) (hC : 0 < C) (hc : 0 < c) (hb : 0 ≤ b)
    (τ : ℝ → ℝ) (hτ : ∀ κ, 1 < κ → 0 < τ κ)
    (hτo : Tendsto (fun κ => τ κ / κ) atTop (nhds 0))
    (κ₀ : ℝ) (hκ₀ : 1 < κ₀) :
    ∃ κ, κ₀ ≤ κ ∧ ∃ U z, D.Adm κ U ∧ D.HasInv κ U ∧ ∃ n : ℕ,
      C * κ ^ a * (1 + D.W2 κ U z) ^ b * exp (-(c * n) / τ κ) < D.TV κ U z n := by
  by_contra hcon
  push Not at hcon
  -- `hcon : ∀ κ ≥ κ₀, ∀ U z, Adm → HasInv → ∀ n, TV ≤ C κ^a (1+W2)^b exp(−c n/τ)`
  have hCs27 : 27 < Cs := lt_trans C_GTD_gt hCs
  have hCs0 : 0 < Cs := by linarith
  -- choose `κ₁` with `τ(κ)/κ < c/(5C⋆)` for `κ ≥ κ₁`
  have hev : ∀ᶠ κ in atTop, τ κ / κ < c / (5 * Cs) :=
    (tendsto_order.1 hτo).2 _ (by positivity)
  obtain ⟨κ₁, hκ₁⟩ := Filter.eventually_atTop.1 hev
  -- the condition number used in the argument
  set κ := max (max κ₀ κ₁) (max (Cs ^ 2 + 1) (2 * Cs)) with hκdef
  have hκ0' : κ₀ ≤ κ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hκ1' : κ₁ ≤ κ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hκsq : Cs ^ 2 < κ := by
    have : Cs ^ 2 + 1 ≤ κ := le_trans (le_max_left _ _) (le_max_right _ _)
    linarith
  have hκ2 : 2 * Cs ≤ κ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hκ1 : 1 < κ := by linarith
  have hκpos : 0 < κ := by linarith
  have hτκ : 0 < τ κ := hτ κ hκ1
  -- (5.2): `exp(−c/τ(κ)) < q_κ`
  have hratio : τ κ / κ < c / (5 * Cs) := hκ₁ κ hκ1'
  have ht : 5 * (Cs / κ) ≤ c / τ κ := by
    rw [div_lt_div_iff₀ hκpos (by positivity)] at hratio
    rw [← mul_div_assoc, div_le_div_iff₀ hκpos hτκ]
    nlinarith
  have h52 : exp (-(c / τ κ)) < q Cs κ := exp_neg_lt_q Cs κ _ hCs27 hκsq ht
  -- the assumed bound at `κ`
  have hb' : ∀ U z, D.Adm κ U → D.HasInv κ U → ∀ n : ℕ,
      D.TV κ U z n ≤ C * κ ^ a * (1 + D.W2 κ U z) ^ b * exp (-(c * n) / τ κ) :=
    fun U z hU hI n => hcon κ hκ0' U z hU hI n
  rcases dich κ hκ2 with ⟨U, z, z', ρ, hU, hI, hρ, hlim⟩ | ⟨c₀, C₀, hc₀, hC₀, hfam⟩
  · -- Case (Q): the assumed bound forces `ρ ≤ exp(−c/τ(κ)) < q_κ ≤ ρ`.
    set Kz := C * κ ^ a * (1 + D.W2 κ U z) ^ b with hKz
    set Kz' := C * κ ^ a * (1 + D.W2 κ U z') ^ b with hKz'
    have hKzpos : 0 < Kz := by
      have := D.W2_nonneg κ U z
      positivity
    have hKz'pos : 0 < Kz' := by
      have := D.W2_nonneg κ U z'
      positivity
    set K := Kz + Kz' with hK
    have hKpos : 0 < K := by positivity
    -- `TVpair n ≤ K exp(−c n/τ)` by the triangle inequality
    have hpair : ∀ n : ℕ, D.TVpair κ U z z' n ≤ K * exp (-(c * n) / τ κ) := by
      intro n
      calc D.TVpair κ U z z' n ≤ D.TV κ U z n + D.TV κ U z' n := D.TVpair_le κ U z z' n hI
        _ ≤ Kz * exp (-(c * n) / τ κ) + Kz' * exp (-(c * n) / τ κ) :=
            add_le_add (hb' U z hU hI n) (hb' U z' hU hI n)
        _ = K * exp (-(c * n) / τ κ) := by rw [hK]; ring
    -- `n`-th roots, for `n ≥ 1`
    have hroot : ∀ n : ℕ, 1 ≤ n →
        D.TVpair κ U z z' n ^ (1 / (n : ℝ)) ≤ K ^ (1 / (n : ℝ)) * exp (-(c / τ κ)) := by
      intro n hn
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
      have hnn : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
      calc D.TVpair κ U z z' n ^ (1 / (n : ℝ))
          ≤ (K * exp (-(c * n) / τ κ)) ^ (1 / (n : ℝ)) :=
            rpow_le_rpow (D.TVpair_nonneg κ U z z' n) (hpair n) hnn
        _ = K ^ (1 / (n : ℝ)) * (exp (-(c * n) / τ κ)) ^ (1 / (n : ℝ)) :=
            mul_rpow hKpos.le (exp_pos _).le
        _ = K ^ (1 / (n : ℝ)) * exp (-(c / τ κ)) := by
            rw [← exp_mul]
            congr 2
            field_simp
    -- pass to the limit
    have hlimR : Tendsto (fun n : ℕ => K ^ (1 / (n : ℝ)) * exp (-(c / τ κ))) atTop
        (nhds (1 * exp (-(c / τ κ)))) :=
      (tendsto_rpow_one_div_natCast K hKpos).mul_const _
    have hle : ρ ≤ 1 * exp (-(c / τ κ)) :=
      le_of_tendsto_of_tendsto hlim hlimR (Filter.eventually_atTop.2 ⟨1, hroot⟩)
    linarith
  · -- Case (C): the assumed bound at `z_R`, `n = ⌊exp(c₀R²)/16⌋₊` tends to zero as `R → ∞`.
    set μ := c * c₀ / (16 * τ κ) with hμ
    have hμpos : 0 < μ := by positivity
    set K₂ := C * κ ^ a * (1 + 2 * C₀) ^ b * exp (c / τ κ) with hK₂
    have hK₂pos : 0 < K₂ := by positivity
    have hlim := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero b μ hμpos
    have hev2 : ∀ᶠ R in atTop, (R : ℝ) ^ b * exp (-μ * R) < 3 / 8 / K₂ :=
      (tendsto_order.1 hlim).2 _ (by positivity)
    obtain ⟨R, hR1, hRsmall⟩ := ((eventually_ge_atTop (1 : ℝ)).and hev2).exists
    obtain ⟨U, z, hU, hI, hW, hTV⟩ := hfam R hR1
    set N := ⌊exp (c₀ * R ^ 2) / 16⌋₊ with hN
    have h38 : 3 / 8 ≤ D.TV κ U z N := hTV N le_rfl
    have hbd := hb' U z hU hI N
    -- bound the Wasserstein factor
    have hWfac : (1 + D.W2 κ U z) ^ b ≤ (1 + 2 * C₀) ^ b * R ^ b := by
      rw [← mul_rpow (by positivity) (by linarith)]
      apply rpow_le_rpow (by linarith [D.W2_nonneg κ U z]) _ hb
      nlinarith
    -- bound the exponential factor: `N > exp(c₀R²)/16 − 1` and `exp(c₀R²) ≥ c₀ R`
    have hNlow : exp (c₀ * R ^ 2) / 16 - 1 < (N : ℝ) := by
      have := Nat.lt_floor_add_one (exp (c₀ * R ^ 2) / 16)
      rw [hN]; linarith
    have hexpR : c₀ * R ≤ exp (c₀ * R ^ 2) := by
      have h1 : c₀ * R ≤ c₀ * R ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hc₀.le
        nlinarith [mul_nonneg (sub_nonneg.2 hR1) (by linarith : (0 : ℝ) ≤ R)]
      have h2 := add_one_le_exp (c₀ * R ^ 2)
      linarith
    have hexpfac : exp (-(c * N) / τ κ) ≤ exp (c / τ κ) * exp (-μ * R) := by
      rw [← exp_add, exp_le_exp]
      have : -(c * (N : ℝ)) / τ κ = -(c / τ κ) * N := by field_simp
      rw [this, hμ]
      have h1 : c / τ κ * (exp (c₀ * R ^ 2) / 16 - 1) ≤ c / τ κ * N :=
        mul_le_mul_of_nonneg_left hNlow.le (by positivity)
      have h2 : c * c₀ / (16 * τ κ) * R ≤ c / τ κ * (exp (c₀ * R ^ 2) / 16) := by
        have : c * c₀ / (16 * τ κ) * R = c / τ κ * (c₀ * R / 16) := by field_simp
        rw [this]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      nlinarith
    -- combine
    have hfinal : D.TV κ U z N ≤ K₂ * (R ^ b * exp (-μ * R)) := by
      calc D.TV κ U z N ≤ C * κ ^ a * (1 + D.W2 κ U z) ^ b * exp (-(c * N) / τ κ) := hbd
        _ ≤ C * κ ^ a * ((1 + 2 * C₀) ^ b * R ^ b) * (exp (c / τ κ) * exp (-μ * R)) := by
            gcongr
        _ = K₂ * (R ^ b * exp (-μ * R)) := by rw [hK₂]; ring
    have : K₂ * (R ^ b * exp (-μ * R)) < 3 / 8 := by
      have := hRsmall
      rw [lt_div_iff₀ hK₂pos] at this
      linarith
    linarith

end OBABO
