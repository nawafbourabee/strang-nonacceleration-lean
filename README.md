# strang-nonacceleration-lean

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22662612.svg)](https://doi.org/10.5281/zenodo.22662612)

Lean 4 companion to

**Provable Non-Acceleration of Standard Strang Splittings of Kinetic Langevin Dynamics**
Nawaf Bou-Rabee, arXiv:2608.25279.

## Scope

The algebraic identities, the numerical constants, the Schur stability criterion of Lemma 2.2, the cycle geometry of Theorem 3.1(ii), and the deterministic attraction estimates underlying Lemmas 4.4 and 4.6 and Theorem 5.1 are verified in Lean 4 with Mathlib. The probabilistic arguments of Section 4 and the three imported results, [22, Theorem 3.5], [30, Theorem 5.2] and [6, Corollary 3.3], are not formalized and enter as hypotheses. The main theorems of the paper are not themselves formalized.

Reference numbers are those of the current paper source (`obabo_non_acceleration.tex`, September 8, 2026), taken from its `.aux` file. Citation numbers: [22] Goujaud, Taylor and Dieuleveut; [30] Leimkuhler, Paulin and Whalley; [6] Bou-Rabee, Cox and Schieven.

## Files

| File | Content |
|---|---|
| `StrangNonAcceleration/Corollary13.lean` | Deduction of Corollary 1.3 from Theorems 1.1 and 5.1 (both as hypotheses) |
| `StrangNonAcceleration/Tier1.lean` | Finite, algebraic and numerical lemmas of Sections 2 to 5, Lemma 4.6, the constants of Section 4.5 and of Theorem 5.1 |
| `StrangNonAcceleration/Section2.lean` | Deterministic content of Section 2: Proposition 2.1 pathwise, the matrices (2.7) to (2.9), Lemma 2.2 |
| `StrangNonAcceleration/Section3.lean` | Theorem 3.1(ii) (the attracting neighborhood of the cycle), Lemma 3.3 Steps 2 and 3, geometric decay from the spectral radius, the invariant tube of Lemma 4.4(i) |
| `StrangNonAcceleration/Axioms.lean` | `#print axioms` for the 100 statements listed in the table below |
| `numerics/lemma33_grid_check.py` | Numerical sanity check of Lemma 3.3 at isolated grid points, and one exact symbolic instance (see below) |

## Build

```
lake exe cache get
lake build
lake env lean StrangNonAcceleration/Axioms.lean
```

Pinned versions: Lean `leanprover/lean4:v4.34.0-rc2` (file `lean-toolchain`); Mathlib commit `85e3a25e006c35636f0e53b0e9296caca2685bc0` (file `lake-manifest.json`, the commit against which the development was built on September 8, 2026). The build produces no warnings and no `sorry`. The GitHub Actions workflow in `.github/workflows/build.yml` runs `lake build` on every push and fails if any file contains `sorry`.

Every statement in the table below reports only the three standard axioms of Lean's foundations. One representative line per file, as printed by `lake env lean StrangNonAcceleration/Axioms.lean`:

```
'OBABO.corollary_1_3_i' depends on axioms: [propext, Classical.choice, Quot.sound]
'OBABO.Diffusive.theorem_5_1_assembly' depends on axioms: [propext, Classical.choice, Quot.sound]
'OBABO.Section2.lemma_2_2_OBABO' depends on axioms: [propext, Classical.choice, Quot.sound]
'OBABO.Section3.theorem_3_1_ii_of_Pcyc' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Numerical checks (not verification)

`numerics/lemma33_grid_check.py` (output in `numerics/lemma33_grid_check_out.txt`, runtime about seven minutes) has two parts.

Part 1 is an exact symbolic evaluation, in the field Q(sqrt 2) with sympy, of one instance of the roots-of-unity construction: m = 8, kappa = 1000, C_star = 28, beta = 881/1000, s = 1879/500000. At this instance it checks numerical stability, rho_q < q_kappa, P_8(s, beta; kappa) < 0, the negativity of I_{0,j} for j = 1, ..., 7 from the definition and from (3.9), identity (3.11), the cycle equation at every cycle point, r_max as an exact algebraic number, the projection identity at 400 exact rational sample points inside the balls, and the spectral radius condition of Assumption 2. This is an example, not coverage of the parameter domain.

Part 2 evaluates every inequality in the proof of Lemma 3.3, including the ones imported from [22], at isolated grid points: kappa in {10^3, 3 x 10^3, 10^4, 10^5, 10^6}, 50 values of beta and 50 values of s per kappa, keeping the points inside the hypothesis region of the lemma, which gives 2,901 points in total. Interval arithmetic (mpmath, 40 digits) is used only to make each pointwise evaluation rigorous. The grid points are isolated; they do not form boxes covering the parameter domain, so this part is a numerical sanity check and not a verification of Lemma 3.3. Steps 2 and 3 of Lemma 3.3 are formalized in `Section3.lean` (`lemma33_step2`, `lemma33_step2_s_lower`, `lemma33_step3_m3`); the steps that invoke [22] are not.

## Correspondence table

Status values: "formalized" means proved in Lean from Mathlib alone; "conditional on" lists the hypotheses of the Lean statement that record results not proved in Lean; "not formalized" marks material of the paper with no Lean counterpart. Definitions are marked "definition". Names are given without the namespace prefix `OBABO.`; the namespaces are `OBABO` (Corollary13.lean, Tier1.lean), `OBABO.Cycle` and `OBABO.Diffusive` (Tier1.lean), `OBABO.Section2`, `OBABO.Section3`.

| Lean name | File | Paper statement | Status |
|---|---|---|---|
| `TuningData` (fields `Adm`, `HasInv`, `TV`, `TVpair`, `W2`, `TV_nonneg`, `W2_nonneg`, `TVpair_le`) | Corollary13.lean | abstract data of Theorem 1.1: class U_kappa^2, invariant law, TV distances, W2, with the triangle inequality for TV through pi (`TVpair_le`) assumed as a property of the data | definition (the fields are hypotheses on the abstract data) |
| `C_GTD`, `q`, `CaseQ`, `CaseC`, `tmix`, `cDiff` | Corollary13.lean | C_GTD, q_kappa of (1.11), cases (Q) and (C) of Theorem 1.1, mixing time, constant c of Theorem 5.1 | definition |
| `exp_neg_lt_q` | Corollary13.lean | inequality (5.2) | formalized |
| `corollary_1_3_i` | Corollary13.lean | Corollary 1.3(i) | conditional on `hTV` (the TV bound of Theorem 5.1) |
| `corollary_1_3_ii` | Corollary13.lean | Corollary 1.3(ii), bound (1.14) | conditional on `dich` (Theorem 1.1 for the tuning rule) and `hτo` (tau(kappa) = o(kappa)) |
| `schur_quadratic`, `uniform_trace_condition` | Tier1.lean | Schur stability criterion in Lemma 2.2 | formalized |
| `lemma_2_2` | Tier1.lean | Lemma 2.2, criterion 0 < s < 2(1+beta)/kappa | formalized |
| `step_size_form` | Tier1.lean | Lemma 2.2, form h < 2/sqrt(kappa) via (2.10) | formalized |
| `real_root_le_neg_one` | Tier1.lean | Lemma 2.2, real root z_- <= -1 | formalized |
| `Pcyc`, `I01` | Tier1.lean | P_m(s, beta; kappa) and I_{0,1} | definition |
| `identity_3_11_poly`, `identity_3_11` | Tier1.lean | identity (3.11) | formalized |
| `sin_eq_one_sub_cos_mul_cot` | Tier1.lean | half-angle identity used for (3.9) | formalized |
| `b_neg` | Tier1.lean | b < 0 for m >= 3 (proof of Theorem 3.1) | formalized |
| `sqrt5_bounds`, `C_GTD_gt_27`, `u_small` | Tier1.lean | Lemma 3.3, smallness of u = 1/kappa | formalized |
| `lemma_3_2_m3`, `lemma_3_2_m3'` | Tier1.lean | Lemma 3.2, case m = 3 | formalized |
| `lemma_3_2_identity`, `one_div_one_add_le`, `cos_two_pi_div_five`, `inv_cos_two_pi_div_five_add_two` | Tier1.lean | Lemma 3.2, m >= 4, elementary steps (3.15) to (3.18) | formalized |
| (none) | Tier1.lean | Lemma 3.2, m >= 4, the parts invoking [22, Lemma B.2, Lemma B.7] | not formalized |
| `frac_anti`, `frac_identity`, `ell`, `ell_q`, `step1_numerics`, `ell_strictAnti` | Tier1.lean | Lemma 3.3, Step 1, algebra and numerics | formalized |
| (none) | Tier1.lean | Lemma 3.3, Step 1, the level-set bound (3.20) from [22, Corollary 2.3, Lemma 2.4] | not formalized |
| `lemma33_step2` | Section3.lean | Lemma 3.3, Step 2, the inequality (1-rho)(rho-beta)/rho > (50/3)u(1-beta) | formalized |
| `lemma33_step2_s_lower` | Section3.lean | Lemma 3.3, Step 2, inequality (3.21) | conditional on `hs` (s >= (1-rho)(1-beta/rho), from [22, Lemma 2.4]) |
| (none) | Section3.lean | Lemma 3.3, Step 2, the parts invoking [22, Lemma B.8] and Step 3 for m-bar >= 4 invoking [22, Lemma B.9] and Lemma 3.2 | not formalized |
| `cos_two_pi_div_three`, `Pcyc_eq`, `le_larger_root`, `P3_at_edge`, `P3_at_edge_nonpos` | Tier1.lean | Lemma 3.3, Step 3, case m-bar = 3, auxiliary facts | formalized |
| `s_plus_3_ge` | Tier1.lean | Lemma 3.3, Step 3, s_+(beta, 3) >= 2(1+beta)/kappa (direct proof from P_3 <= 0 at the stability edge) | formalized |
| `lemma33_step3_m3` | Section3.lean | Lemma 3.3, Step 3, case m-bar = 3, by the paper's argument (roots sum to 2 beta + 1 + u(2 + beta) > 1); real roots (3.24) not needed for the inequality | formalized |
| `ζ`, `xc`, `μ`, `I0`, `rmax`, `Cset`, `IsMetricProj`, `gradPsi`, `aCoef`, `bCoef` | Section3.lean | cycle points, M of (3.4), I_{0,j}, r_max of (3.13), C, metric projection, gradient field of (3.5), coefficients a and b | definition |
| `I0_eq`, `I0_eq_half` | Section3.lean | closed form (3.9) of I_{0,j} | formalized |
| `g_neg_of_g_neg`, `I0_neg_of_I0_one_neg` | Section3.lean | monotonicity (3.10) | formalized |
| `xc_ne_one`, `ζ_pow_m`, `ζ_pow_mod`, `xc_factor`, `index_range`, `inner_xc_mul` | Section3.lean | proof of Theorem 3.1(ii): distinct cycle points, I_{t,j} = I_{0,j-t} | formalized |
| `rmax_pos`, `rmax_le` | Section3.lean | r_max > 0 in (3.13) | formalized |
| `projection_inequality` | Section3.lean | projection inequalities (3.12) at the vertices | formalized |
| `variational_inequality`, `convex_halfspace_inner` | Section3.lean | projection inequalities (3.12) on all of C | formalized |
| `nearest_point`, `nearest_unique`, `proj_const` | Section3.lean | proj_C(x_t + u) = M x_t for |u| <= r_max | formalized |
| `theorem_3_1_ii` | Section3.lean | Theorem 3.1(ii), identity (3.8) | conditional on `hp` (p is a metric projection onto C; the representation (3.5) of psi is Theorem 3.1(i)) |
| `I0_one_eq_I01`, `I0_one_neg_of_Pcyc_neg` | Section3.lean | P_m < 0 implies I_{0,1} < 0 via (3.11) | formalized |
| `theorem_3_1_ii_of_Pcyc` | Section3.lean | Theorem 3.1(ii) from P_m(s, beta; kappa) < 0 | conditional on `hp` (as above) |
| (none) | | Theorem 3.1(i), the representation (3.5) of psi, [22, Theorem 3.5, Section B.1] | not formalized |
| (none) | | Proposition 3.4 (mollification, (3.25) to (3.28)) | not formalized |
| `log_ratio_le`, `log_inv_q_le` | Tier1.lean | Corollary 1.2(i), log(1/q_kappa) <= 3 C_star/kappa | formalized |
| `nstar_property`, `nstar_lower` | Tier1.lean | Corollary 1.2(i), the integer n_star | formalized |
| (none) | | Corollary 1.2(i), constants c_1, c_2, c; Corollary 1.2(ii) | not formalized |
| `Cycle.a`, `Cycle.b`, `Cycle.c`, `Cycle.δ₀`, `Cycle.GradOK`, `Cycle.p`, `Cycle.hstar`, `Cycle.βstar`, `Cycle.γstar` | Tier1.lean | Section 4.5: the cycle points, the gradient identities (4.23), the tuning h_star, beta_star, gamma_star | definition |
| `Cycle.cycle_steps`, `Cycle.p_values`, `Cycle.p_exact` | Tier1.lean | Lemma 4.6, the exact three-cycle | formalized |
| `Cycle.grad_diff`, `Cycle.error_step`, `Cycle.bound_4_25` | Tier1.lean | Lemma 4.6, (4.24) and (4.25) | formalized |
| `Cycle.lemma_4_6`, `Cycle.lemma_4_6_cycle` | Tier1.lean | Lemma 4.6, bootstrap to the tube of radius 1/20 | formalized |
| `Cycle.lemma_4_6_origin`, `Cycle.tubes_disjoint` | Tier1.lean | Proposition 4.7, origin tube and disjointness | formalized |
| `Cycle.hessian_bounds` | Tier1.lean | (4.23), Hessian bounds of the pieces | conditional on `GradOK` (the gradient identities of the piecewise potential (4.23)) |
| `Cycle.hstar_sq`, `Cycle.βstar_eq_exp`, `Cycle.s_star`, `Cycle.sqrt_βstar`, `Cycle.hstar_lt` | Tier1.lean | Section 4.5, tuning identities | formalized |
| `Cycle.eq_4_26`, `Cycle.eq_4_27`, `Cycle.tail_exponent`, `Cycle.rhs_4_28`, `Cycle.window_threshold` | Tier1.lean | (4.26), (4.27), the constants in (4.28) | formalized |
| (none) | | Proposition 4.7, Gaussian tail bound and union bound | not formalized |
| `Section3.Ψ`, `Section3.duhamel` | Section3.lean | proof of Lemma 4.4, products Psi_j(k, l) and the Duhamel formula | formalized |
| `Section3.error_recursion` | Section3.lean | proof of Lemma 4.4, error recursion from (4.5), (4.6), (4.10) | formalized |
| `Section3.invariant_tube` | Section3.lean | Lemma 4.4(i), deterministic core (the tube of radius aR/2 under (4.12)) | conditional on `hC`, `hG` (the bounds on the partial products, (4.8)) |
| `Section3.geometric_decay_of_spectralRadius_lt_one` | Section3.lean | after Assumption 2: constants (C, q) with the norm of the n-th power at most C q^n, from Gelfand's formula | formalized |
| (none) | | the passage from the full-cycle product to the partial products Psi_j(k, l) in (4.8) | not formalized |
| (none) | | Lemma 4.4(ii), (iii) (total variation separation, union bound) | not formalized |
| (none) | | Lemma 4.1, Proposition 4.2, Corollary 4.3 | not formalized |
| (none) | | Theorem 4.5 (existence and uniqueness of the invariant law, metastability, (4.13) to (4.22)) | not formalized |
| `Diffusive.e1`, `Diffusive.h`, `Diffusive.γ`, `Diffusive.cH`, `Diffusive.cstar`, `Diffusive.R24`, `Diffusive.Rr`, `Diffusive.cDiff` | Tier1.lean | Theorem 5.1, the tuning and the constants | definition |
| `Diffusive.e1_bounds`, `Diffusive.γ_mul_h`, `Diffusive.β_eq`, `Diffusive.step_condition`, `Diffusive.b_sq_lt`, `Diffusive.cH_eq`, `Diffusive.cH_le`, `Diffusive.cH_lt_one` | Tier1.lean | Theorem 5.1, tuning identities and the step condition of [30] | formalized |
| `Diffusive.max_a`, `Diffusive.wasserstein_const`, `Diffusive.sqrt_step` | Tier1.lean | Theorem 5.1, the constant 147 kappa | formalized |
| `Diffusive.R24_eq`, `Diffusive.R24_le` | Tier1.lean | Theorem 5.1, closed form of R_24 and R_24 <= 8.62 sqrt(kappa) | formalized |
| `Diffusive.cstar_bounds`, `Diffusive.cDiff_pos`, `Diffusive.cDiff_lt`, `Diffusive.exp_const_lt`, `Diffusive.final_constant`, `Diffusive.pow_bound` | Tier1.lean | Theorem 5.1, the constant 143 and the exponent c | formalized |
| `Diffusive.small_n` | Tier1.lean | Theorem 5.1, the case n <= 24 | formalized |
| `Diffusive.theorem_5_1_assembly` | Tier1.lean | Theorem 5.1, assembly of the TV bound (5.1) | conditional on `hcontr` ([30, Theorem 5.2, Proposition 2.4]) and `hreg` ([6, Theorem 3.2, Corollary 3.3]) |
| (none) | | the contraction estimate of [30] and the regularization estimate of [6] in Theorem 5.1 | not formalized |
| `Section2.step`, `Section2.IsChain`, `Section2.ζ`, `Section2.Mmat`, `Section2.Nmat`, `Section2.Amat` | Section2.lean | the OBABO step (1.4) to (1.6), the noise (2.3), the matrices (2.7) and (1.10) | definition |
| `Section2.eq_2_5`, `Section2.eq_2_6` | Section2.lean | (2.5), (2.6) | formalized |
| `Section2.prop_2_1`, `Section2.prop_2_1_first` | Section2.lean | Proposition 2.1, (2.2) and (2.3), as a pathwise identity | formalized |
| `Section2.covariance_scalars` | Section2.lean | (2.4) and the cold-start covariance, scalar form | formalized |
| (none) | | Proposition 2.1, the noise zeta_k is Gaussian and independent | not formalized |
| `Section2.step_quadratic`, `Section2.trace_Mmat`, `Section2.det_Mmat`, `Section2.trace_Amat`, `Section2.det_Amat` | Section2.lean | (2.7), trace and determinant of M_lambda and of (1.10) | formalized |
| `Section2.charpoly_Mmat`, `Section2.charpoly_Amat`, `Section2.charpoly_eq` | Section2.lean | (2.8) | formalized |
| `Section2.mem_spectrum_Amat`, `Section2.spectrum_Mmat_eq` | Section2.lean | (2.9) | formalized |
| `Section2.position_recursion_quadratic` | Section2.lean | noise-free (2.2) as the matrix A_lambda | formalized |
| `Section2.lemma_2_2_Amat`, `Section2.lemma_2_2_OBABO` | Section2.lean | Lemma 2.2, first assertion | formalized |
| `Section2.real_eigenvalue_Mmat`, `Section2.exists_left_eigenvector` | Section2.lean | Lemma 2.2, second assertion, real eigenvalue z_- and left eigenvector | formalized |
| `Section2.det_Nmat`, `Section2.Nmat_transpose_mulVec_ne_zero`, `Section2.scalar_recursion` | Section2.lean | Lemma 2.2, second assertion, det N and the scalar recursion | formalized |
| `Section2.sum_sq_pow_ge`, `Section2.charfun_contradiction` | Section2.lean | Lemma 2.2, second assertion, the characteristic-function contradiction (analytic form) | formalized |
| (none) | | Lemma 2.2, second assertion, from an invariant law to the functional equation of its characteristic function | not formalized |
| (none) | | Section 6 (Lemma 6.1, Proposition 6.2, Theorem 6.3, Corollary 6.4, Proposition 6.5, Theorem 6.6, Corollary 6.7) | not formalized |
| (none) | | Section 7 | not formalized |
| (none) | | Appendix A (Proposition A.1 and (A.1) to (A.11)) | not formalized |
| (none) | | Appendix B (Proposition B.1, (B.1), (B.2)) | not formalized |
| (none) | | Theorem 1.1, Corollary 1.2(ii), Corollary 1.5 | not formalized |

## Archive and citation

Tagged releases of this repository are archived on Zenodo. The concept DOI [10.5281/zenodo.22662612](https://doi.org/10.5281/zenodo.22662612) always resolves to the latest archived version; each archived version also carries its own version DOI, listed on the Zenodo record.

Suggested citation: N. Bou-Rabee, strang-nonacceleration-lean: Lean 4 companion to "Provable Non-Acceleration of Standard Strang Splittings of Kinetic Langevin Dynamics", Zenodo, 2026, doi:10.5281/zenodo.22662612.

## License

Apache License 2.0, see `LICENSE`.
