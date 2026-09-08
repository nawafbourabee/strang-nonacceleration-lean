# strang-nonacceleration-lean

Lean 4 companion to

**Provable Non-Acceleration of Standard Strang Splittings of Kinetic Langevin Dynamics**
Nawaf Bou-Rabee, arXiv:2608.25279.

## Scope

Formalized in Lean 4 with Mathlib (163 statements, no `sorry`, only the standard axioms): the worst-case spectral radius rho_q of (1.10) and its sublevel sets; two steps of Corollary 1.2(i) and the deduction of Corollary 1.3; the heavy-ball representation of Proposition 2.1 as a pathwise identity; Lemma 2.2, the Schur criterion and the matrix identities (2.7) to (2.9); Theorem 3.1(ii), the cycle geometry; Lemmas 3.2 and 3.3 in full; Proposition 3.4, the mollification; the deterministic parts of Section 4, namely Lemma 4.4(i), the cycle data of Section 4.5, Lemma 4.6 and the estimates (4.26) to (4.28) of Proposition 4.7; the tuning, the constants and the assembly of Theorem 5.1; and the heavy-ball representations of Propositions 6.2 and 6.5 as pathwise identities. Three imported results enter as hypotheses of the Lean statements instead of being proved: the representation (3.5) of the potential from [GTD, Theorem 3.5], the contraction estimate of [LPW, Theorem 5.2] and the regularization estimate of [BCS, Corollary 3.3].

Not formalized: the probabilistic arguments, that is, the Gaussian and independence statements in Propositions 2.1, 6.2 and 6.5, the invariant-law step in Lemma 2.2, Lemma 4.1, Proposition 4.2, Corollary 4.3, Lemma 4.4(ii) and (iii), Theorem 4.5, the tail and union bounds of Proposition 4.7, and Lemma 6.1; the deductions of Theorem 1.1 and Corollaries 1.2 and 1.5 from the results of Sections 4 and 5, and the constants of Corollary 1.2; the bound (4.8) on the partial products in Lemma 4.4, which enters as a hypothesis; Theorems 6.3 and 6.6 and Corollaries 6.4 and 6.7; Section 7 and Appendices A and B.

Statement and equation numbers follow the paper source dated September 8, 2026 (`obabo_non_acceleration.tex`, numbering taken from its `.aux` file). References are cited by author tags rather than by the numbers of the paper's bibliography: [GTD] Goujaud, Taylor and Dieuleveut (2025), [LPW] Leimkuhler, Paulin and Whalley (2024), [BCS] Bou-Rabee, Cox and Schieven (2026).

## Files

Each Lean file is named after the statement of the paper it covers (a dot in a statement number becomes an underscore, since Lean module names cannot contain dots).

| File | Content |
|---|---|
| `StrangNonAcceleration/Section1.lean` | The worst-case spectral radius rho_q(s, beta; kappa) of (1.10): the spectral radius of A_lambda in closed form, rho_q as the supremum over lambda in [1, kappa], the description of its sublevel sets ([GTD, Lemma 2.4] as used), the level-set bound (3.20) and [GTD, Corollary 2.3] |
| `StrangNonAcceleration/Corollary1_2.lean` | Two steps of the proof of Corollary 1.2(i): the logarithmic inequalities and the integer n_star (the corollary itself is not formalized) |
| `StrangNonAcceleration/Corollary1_3.lean` | Deduction of Corollary 1.3 from Theorems 1.1 and 5.1 (both as hypotheses); the constants (1.11) |
| `StrangNonAcceleration/Proposition2_1.lean` | Proposition 2.1 as a pathwise identity, the noise (2.3), the covariance scalars (2.4) |
| `StrangNonAcceleration/Lemma2_2.lean` | Lemma 2.2: the Schur stability criterion, the matrices (2.7) to (2.9), the second assertion |
| `StrangNonAcceleration/Theorem3_1.lean` | Theorem 3.1(ii): the cycling quadratic, identity (3.11), the attracting neighborhood of the cycle |
| `StrangNonAcceleration/Lemma3_2.lean` | Lemma 3.2 in full: the thresholds s_+, s_-, beta_- of [GTD, Notation B.1], the two bounds imported from [GTD] (Lemma B.2, and the bound from the proof of Lemma B.6 via Lemma B.7), and the overlap inequality (3.14) for every m >= 3 |
| `StrangNonAcceleration/Lemma3_3.lean` | Lemma 3.3 in full: the three facts imported from [GTD] (Lemmas B.7, B.8, B.9) and the bound of [GTD, equation (29)], the three steps of the proof, and the existence of a period m >= 3 with P_m(s, beta; kappa) < 0 |
| `StrangNonAcceleration/Proposition3_4.lean` | Proposition 3.4: mollification of the potential of Theorem 3.1 (strong monotonicity, Lipschitz and Hessian bounds, the cycle equation (3.25), the locally affine gradient (3.26), the bounded remainder (3.27)), the Jacobian (3.28) along the cycle, and the spectral radius bound rho(A_1)^m <= rho_q^m < 1 |
| `StrangNonAcceleration/Lemma4_4.lean` | Deterministic core of Lemma 4.4(i): geometric decay from the spectral radius, the invariant tube, the error recursion (parts (ii) and (iii) are not formalized) |
| `StrangNonAcceleration/Section4_5.lean` | Section 4.5: the cycle points, the gradient identities (4.23), the Hessian bounds, the tuning |
| `StrangNonAcceleration/Lemma4_6.lean` | Lemma 4.6: the exact three-cycle, (4.24), (4.25), the bootstrap to the tube |
| `StrangNonAcceleration/Proposition4_7.lean` | Deterministic steps of the proof of Proposition 4.7: origin tube, disjointness, (4.26), (4.27), the constants in (4.28) (the Gaussian tail bound and the union bound are not formalized) |
| `StrangNonAcceleration/Theorem5_1.lean` | Theorem 5.1: the tuning, the constants, the case n <= 24, and the assembly of (5.1) conditional on the two imported estimates |
| `StrangNonAcceleration/Proposition6_2.lean` | Proposition 6.2 as a pathwise identity: the BAOAB step (6.3) to (6.5), the identities (6.10) and (6.11), the recursion (6.7) with the noise (6.8) for every k >= 1 and, through the auxiliary position of (6.6), for k = 0, and the covariance scalars (6.9) |
| `StrangNonAcceleration/Proposition6_5.lean` | Proposition 6.5 as pathwise identities: the steps of ABOBA, AOBOA, BOAOB and OABAO, the identities Y_{m+1} - Y_m = h V_m of parts (i) and (ii), the four recursions (6.13), (6.14), (6.16) (with the first step through (6.15)) and (6.17), and the covariance scalars |
| `StrangNonAcceleration/Axioms.lean` | `#print axioms` for the 163 statements listed in the table below |

## Build

```
lake exe cache get
lake build
lake env lean StrangNonAcceleration/Axioms.lean
```

Pinned versions: Lean `leanprover/lean4:v4.34.0-rc2` (file `lean-toolchain`); Mathlib commit `85e3a25e006c35636f0e53b0e9296caca2685bc0` (file `lake-manifest.json`, the commit against which the development was built on September 8, 2026). The build produces no warnings and no `sorry`. The GitHub Actions workflow in `.github/workflows/build.yml` runs `lake build` on every push and fails if any file contains `sorry`.

Every statement in the tables below reports only the three standard axioms of Lean's foundations. All 163 lines printed by `lake env lean StrangNonAcceleration/Axioms.lean` have the form of the first and the last:

```
'OBABO.norm_root_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'OBABO.Section6.covariance_scalars_OABAO' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Correspondence with the paper

Status: "formalized" means proved in Lean from Mathlib alone; "conditional on" names the hypotheses of the Lean statement that stand for results not proved in Lean. Lean names omit the prefix `OBABO.`; the namespaces `Section2`, `Section3`, `Section3.Mollify`, `Cycle`, `Diffusive` and `Section6` are written where they apply.

### Summary by paper statement

| Paper statement | Lean statement | File | Status |
|---|---|---|---|
| rho_q(s, beta; kappa) of (1.10), with [GTD, Lemma 2.4 and Corollary 2.3] as used | `ρq`, `ρq_le_iff`, `ρq_facts`, `rho_star_le_ρq` | Section1.lean | formalized |
| Corollary 1.2(i) | `log_inv_q_le`, `nstar_property` | Corollary1_2.lean | two steps of the proof formalized; the constants c_1, c_2, c and part (ii) not formalized |
| Corollary 1.3 | `corollary_1_3_i`, `corollary_1_3_ii` | Corollary1_3.lean | conditional on Theorem 1.1 and Theorem 5.1 |
| Proposition 2.1 | `Section2.prop_2_1`, `Section2.prop_2_1_first` | Proposition2_1.lean | formalized as a pathwise identity; the Gaussian and independence statements not formalized |
| Lemma 2.2 | `lemma_2_2`, `Section2.lemma_2_2_OBABO`, `Section2.charfun_contradiction` | Lemma2_2.lean | first assertion formalized; second assertion formalized except the passage from an invariant law to the characteristic-function equation |
| Theorem 3.1(ii) | `Section3.theorem_3_1_ii_projC` | Theorem3_1.lean | formalized (Theorem 3.1(i) is imported from [GTD] and enters Proposition 3.4 as a hypothesis) |
| Lemma 3.2 | `lemma_3_2` | Lemma3_2.lean | formalized |
| Lemma 3.3 | `lemma_3_3` | Lemma3_3.lean | formalized |
| Proposition 3.4 | `Section3.proposition_3_4_projC` | Proposition3_4.lean | conditional on the representation (3.5) of the potential from [GTD, Theorem 3.5] |
| Lemma 4.4(i) | `Section3.invariant_tube` | Lemma4_4.lean | conditional on the partial-product bound (4.8); parts (ii) and (iii) not formalized |
| Lemma 4.6 | `Cycle.lemma_4_6`, `Cycle.lemma_4_6_cycle` | Lemma4_6.lean | formalized |
| Proposition 4.7 | `Cycle.tubes_disjoint`, `Cycle.eq_4_26`, `Cycle.eq_4_27`, `Cycle.rhs_4_28` | Proposition4_7.lean | the deterministic estimates formalized; the tail and union bounds not formalized |
| Theorem 5.1 | `Diffusive.theorem_5_1_assembly` | Theorem5_1.lean | conditional on [LPW, Theorem 5.2] and [BCS, Corollary 3.3] |
| Proposition 6.2 | `Section6.prop_6_2`, `Section6.prop_6_2_first` | Proposition6_2.lean | formalized as a pathwise identity; the distributional statements not formalized |
| Proposition 6.5 | `Section6.prop_6_5_i`, `Section6.prop_6_5_ii`, `Section6.prop_6_5_iii`, `Section6.prop_6_5_iv` | Proposition6_5.lean | formalized as pathwise identities; the distributional statements not formalized |

Theorem 1.1, Corollary 1.5, Lemma 4.1, Proposition 4.2, Corollary 4.3, Theorem 4.5, Lemma 6.1, Theorems 6.3 and 6.6, Corollaries 6.4 and 6.7, Section 7 and the appendices have no Lean counterpart.

### Full table

Every Lean declaration of the development, in the order of the files.

| Lean name | File | Paper statement | Status |
|---|---|---|---|
| `rootRad`, `ρq` | Section1.lean | the spectral radius of the companion matrix of z^2 - T z + beta in closed form; rho_q(s, beta; kappa) of (1.10) as the supremum over lambda in [1, kappa] | definition |
| `norm_root_le`, `exists_root_norm_eq`, `spectralRadius_Amat` | Section1.lean | the closed form equals Mathlib's `spectralRadius` of the complexified A_lambda(s, beta) | formalized |
| `rootRad_le_iff`, `sqrt_le_ρq`, `ρq_le_iff`, `ρq_facts` | Section1.lean | the sublevel sets of rho_q ([GTD, Lemma 2.4] as used): rho_q <= r iff the traces at lambda = 1 and lambda = kappa are at most r + beta/r; hence beta <= rho^2, s >= (1 - rho)(1 - beta/rho), s kappa <= (1 + rho)(1 + beta/rho) for rho = rho_q | formalized |
| `ell_ρq_le` | Section1.lean | the level-set bound (3.20), l(rho) <= beta | formalized |
| `rho_star_le_ρq` | Section1.lean | [GTD, Corollary 2.3]: rho_q >= rho_star(kappa) = (1 - sqrt u)/(1 + sqrt u) | formalized |
| `log_ratio_le`, `log_inv_q_le` | Corollary1_2.lean | Corollary 1.2(i), log(1/q_kappa) <= 3 C_star/kappa | formalized |
| `nstar_property`, `nstar_lower` | Corollary1_2.lean | Corollary 1.2(i), the integer n_star | formalized |
| `TuningData` (fields `Adm`, `HasInv`, `TV`, `TVpair`, `W2`, `TV_nonneg`, `W2_nonneg`, `TVpair_le`) | Corollary1_3.lean | abstract data of Theorem 1.1: class U_kappa^2, invariant law, TV distances, W2, with the triangle inequality for TV through pi (`TVpair_le`) assumed as a property of the data | definition (the fields are hypotheses on the abstract data) |
| `C_GTD`, `q`, `CaseQ`, `CaseC`, `tmix`, `cDiff` | Corollary1_3.lean | C_GTD, q_kappa of (1.11), cases (Q) and (C) of Theorem 1.1, mixing time, constant c of Theorem 5.1 | definition |
| `exp_neg_lt_q` | Corollary1_3.lean | inequality (5.2) | formalized |
| `corollary_1_3_i` | Corollary1_3.lean | Corollary 1.3(i) | conditional on `hTV` (the TV bound of Theorem 5.1) |
| `corollary_1_3_ii` | Corollary1_3.lean | Corollary 1.3(ii), bound (1.14) | conditional on `dich` (Theorem 1.1 for the tuning rule) and `hτo` (tau(kappa) = o(kappa)) |
| `Section2.step`, `Section2.IsChain`, `Section2.ζ` | Proposition2_1.lean | the OBABO step (1.4) to (1.6), the chain, the noise (2.3) | definition |
| `Section2.eq_2_5`, `Section2.eq_2_6` | Proposition2_1.lean | (2.5), (2.6) | formalized |
| `Section2.prop_2_1`, `Section2.prop_2_1_first` | Proposition2_1.lean | Proposition 2.1, (2.2) and (2.3), as a pathwise identity | formalized |
| `Section2.covariance_scalars` | Proposition2_1.lean | (2.4) and the cold-start covariance, scalar form | formalized |
| `schur_quadratic`, `uniform_trace_condition` | Lemma2_2.lean | Schur stability criterion in Lemma 2.2 | formalized |
| `lemma_2_2` | Lemma2_2.lean | Lemma 2.2, criterion 0 < s < 2(1+beta)/kappa | formalized |
| `step_size_form` | Lemma2_2.lean | Lemma 2.2, form h < 2/sqrt(kappa) via (2.10) | formalized |
| `real_root_le_neg_one` | Lemma2_2.lean | Lemma 2.2, real root z_- <= -1 | formalized |
| `Section2.Mmat`, `Section2.Nmat`, `Section2.Amat` | Lemma2_2.lean | the matrices (2.7), N and (1.10) | definition |
| `Section2.step_quadratic`, `Section2.trace_Mmat`, `Section2.det_Mmat`, `Section2.trace_Amat`, `Section2.det_Amat` | Lemma2_2.lean | (2.7), trace and determinant of M_lambda and of (1.10) | formalized |
| `Section2.charpoly_Mmat`, `Section2.charpoly_Amat`, `Section2.charpoly_eq` | Lemma2_2.lean | (2.8) | formalized |
| `Section2.mem_spectrum_Amat`, `Section2.spectrum_Mmat_eq` | Lemma2_2.lean | (2.9) | formalized |
| `Section2.position_recursion_quadratic` | Lemma2_2.lean | noise-free (2.2) as the matrix A_lambda | formalized |
| `Section2.lemma_2_2_Amat`, `Section2.lemma_2_2_OBABO` | Lemma2_2.lean | Lemma 2.2, first assertion | formalized |
| `Section2.real_eigenvalue_Mmat`, `Section2.exists_left_eigenvector` | Lemma2_2.lean | Lemma 2.2, second assertion, real eigenvalue z_- and left eigenvector | formalized |
| `Section2.det_Nmat`, `Section2.Nmat_transpose_mulVec_ne_zero`, `Section2.scalar_recursion` | Lemma2_2.lean | Lemma 2.2, second assertion, det N and the scalar recursion | formalized |
| `Section2.sum_sq_pow_ge`, `Section2.charfun_contradiction` | Lemma2_2.lean | Lemma 2.2, second assertion, the characteristic-function contradiction (analytic form) | formalized |
| `Pcyc`, `I01` | Theorem3_1.lean | P_m(s, beta; kappa) and I_{0,1} | definition |
| `identity_3_11_poly`, `identity_3_11` | Theorem3_1.lean | identity (3.11) | formalized |
| `sin_eq_one_sub_cos_mul_cot` | Theorem3_1.lean | half-angle identity used for (3.9) | formalized |
| `b_neg` | Theorem3_1.lean | b < 0 for m >= 3 (proof of Theorem 3.1) | formalized |
| `Section3.ζ`, `Section3.xc`, `Section3.μ`, `Section3.I0`, `Section3.rmax`, `Section3.Cset`, `Section3.IsMetricProj`, `Section3.gradPsi`, `Section3.aCoef`, `Section3.bCoef` | Theorem3_1.lean | cycle points, M of (3.4), I_{0,j}, r_max of (3.13), C, metric projection, gradient field of (3.5), coefficients a and b | definition |
| `Section3.I0_eq`, `Section3.I0_eq_half` | Theorem3_1.lean | closed form (3.9) of I_{0,j} | formalized |
| `Section3.g_neg_of_g_neg`, `Section3.I0_neg_of_I0_one_neg` | Theorem3_1.lean | monotonicity (3.10) | formalized |
| `Section3.xc_ne_one`, `Section3.ζ_pow_m`, `Section3.ζ_pow_mod`, `Section3.xc_factor`, `Section3.index_range`, `Section3.inner_xc_mul` | Theorem3_1.lean | proof of Theorem 3.1(ii): distinct cycle points, I_{t,j} = I_{0,j-t} | formalized |
| `Section3.rmax_pos`, `Section3.rmax_le` | Theorem3_1.lean | r_max > 0 in (3.13) | formalized |
| `Section3.projection_inequality` | Theorem3_1.lean | projection inequalities (3.12) at the vertices | formalized |
| `Section3.variational_inequality`, `Section3.convex_halfspace_inner` | Theorem3_1.lean | projection inequalities (3.12) on all of C | formalized |
| `Section3.nearest_point`, `Section3.nearest_unique`, `Section3.proj_const` | Theorem3_1.lean | proj_C(x_t + u) = M x_t for | u | <= r_max | formalized |
| `Section3.theorem_3_1_ii` | Theorem3_1.lean | Theorem 3.1(ii), identity (3.8) | conditional on `hp` (p is a metric projection onto C; the representation (3.5) of psi is Theorem 3.1(i)) |
| `Section3.I0_one_eq_I01`, `Section3.I0_one_neg_of_Pcyc_neg` | Theorem3_1.lean | P_m < 0 implies I_{0,1} < 0 via (3.11) | formalized |
| `Section3.theorem_3_1_ii_of_Pcyc` | Theorem3_1.lean | Theorem 3.1(ii) from P_m(s, beta; kappa) < 0 | conditional on `hp` (as above) |
| `Section3.Cset_nonempty`, `Section3.isCompact_Cset`, `Section3.exists_isMetricProj`, `Section3.projC`, `Section3.isMetricProj_projC` | Theorem3_1.lean | C is nonempty and compact; the metric projection onto C exists (`projC` is a fixed choice) | formalized |
| `Section3.theorem_3_1_ii_projC` | Theorem3_1.lean | Theorem 3.1(ii) for the metric projection `projC` of C: r_max > 0 and (3.8) | formalized |
| `sqrt5_bounds` | Lemma3_2.lean | bounds on sqrt 5 (used in Lemmas 3.2 and 3.3) | formalized |
| `θm`, `Acoef`, `Disc`, `sMinus`, `sPlus`, `βMinus` | Lemma3_2.lean | theta_m = 2 pi/m; A_m and B_m^2 of (3.15); the thresholds s_-(beta, m; kappa), s_+(beta, m; kappa) and beta_-(m; kappa) of [GTD, Notation B.1] (beta_- as the larger root of beta -> B_m^2) | definition |
| `Pcyc_eq_mul_roots` | Lemma3_2.lean | P_m(s, beta; kappa) = (s - s_-)(s - s_+) when the roots are real | formalized |
| `Disc_nonneg_of_βMinus_le`, `le_βMinus_of_Disc_nonpos` | Lemma3_2.lean | the roots are real for beta >= beta_-(m; kappa); B_m^2(beta_0) <= 0 implies beta_0 <= beta_-(m; kappa) | formalized |
| `Disc_at_β0_nonpos`, `βMinus_ge` | Lemma3_2.lean | [GTD, Lemma B.2] as used in the proof: beta_-(m+1; kappa) >= cos theta_{m+1} (1 + sqrt u xi_{m+1}) for m >= 4 | formalized |
| `cos_θm_lt`, `sin_succ_ge`, `one_sub_cos_ratio`, `xi_bound` | Lemma3_2.lean | cos theta_m < cos theta_{m+1}; concavity of sin; (1 - cos theta_m) <= ((m+1)/m)^2 (1 - cos theta_{m+1}); the bound xi_{m+1} + 2(1 - cos theta_m)/xi_{m+1} <= 3 + sqrt 5 for m >= 4 (the elementary bound from the proof of [GTD, Lemma B.6] via [GTD, Lemma B.7]) | formalized |
| `lemma_3_2_m3`, `lemma_3_2_m3'`, `key_m3` | Lemma3_2.lean | (3.17) in the case m = 3: u^2 - 3u + 1 > 0 | formalized |
| `lemma_3_2_identity`, `one_div_one_add_le`, `cos_two_pi_div_five`, `inv_cos_two_pi_div_five_add_two`, `add_inv_antitone`, `key_ge4` | Lemma3_2.lean | (3.17) in the case m >= 4, through the elementary steps (3.15) to (3.18) | formalized |
| `lemma_3_2` | Lemma3_2.lean | Lemma 3.2, inequality (3.14): s_-(beta, m; kappa) < s_+(beta, m+1; kappa) for m >= 3, beta in (0, 1), beta >= beta_-(m+1; kappa), kappa^{-1} < ((3 - sqrt 5)/4)^2 | formalized |
| `C_GTD_gt_27`, `u_small` | Lemma3_3.lean | Lemma 3.3, smallness of u = 1/kappa | formalized |
| `frac_anti`, `frac_identity`, `ell`, `ell_q`, `step1_numerics`, `ell_strictAnti` | Lemma3_3.lean | Lemma 3.3, Step 1, algebra and numerics | formalized |
| `Section3.lemma33_step2` | Lemma3_3.lean | Lemma 3.3, Step 2, the inequality (1-rho)(rho-beta)/rho > (50/3)u(1-beta) | formalized |
| `Section3.lemma33_step2_s_lower` | Lemma3_3.lean | Lemma 3.3, Step 2, inequality (3.21) | conditional on `hs` (s >= (1-rho)(1-beta/rho), from [GTD, Lemma 2.4]) |
| `cos_two_pi_div_three`, `Pcyc_eq`, `le_larger_root`, `P3_at_edge`, `P3_at_edge_nonpos` | Lemma3_3.lean | Lemma 3.3, Step 3, case m-bar = 3, auxiliary facts | formalized |
| `s_plus_3_ge` | Lemma3_3.lean | Lemma 3.3, Step 3, s_+(beta, 3) >= 2(1+beta)/kappa (direct proof from P_3 <= 0 at the stability edge) | formalized |
| `Section3.lemma33_step3_m3` | Lemma3_3.lean | Lemma 3.3, Step 3, case m-bar = 3, by the paper's argument (roots sum to 2 beta + 1 + u(2 + beta) > 1); real roots (3.24) not needed for the inequality | formalized |
| `one_sub_cos_ratio_le`, `cos_θm_mono` | Lemma3_3.lean | [GTD, Lemma B.7]: 1 - cos theta_K <= (3/2)(1 - cos theta_{K+1}) for K >= 2; monotonicity of cos theta_m | formalized |
| `exists_m0` | Lemma3_3.lean | [GTD, Lemma B.8] with m_0 >= 3: a period with (2/3)(1 - beta) <= beta - cos theta_{m_0} <= (3/2)(1 - beta) | formalized |
| `βMinus_le_of`, `βMinus_le_of_ratio` | Lemma3_3.lean | [GTD, Lemma B.9] as used: beta >= beta_-(m; kappa) when beta - cos theta_m >= (2/3)(1 - beta) and u <= 1/16 | formalized |
| `sMinus_le_bound` | Lemma3_3.lean | the bound of [GTD, equation (29)]: s_-(beta, m_0) <= (50/3) u (1 - beta) | formalized |
| `lemma_3_3` | Lemma3_3.lean | Lemma 3.3: for C_star > C_GTD, kappa >= 2 C_star, numerically stable (s, beta) with rho_q(s, beta; kappa) < q_kappa, there is m >= 3 with P_m(s, beta; kappa) < 0 | formalized |
| `Section3.Mollify.moll`, `Section3.hbUpdate`, `Section3.hbLin` | Proposition3_4.lean | the mollified vector field rho_eps * g; the heavy-ball update (x, y) -> ((1+beta)x - beta y - s G(x), x); the linear map A_1 of (3.28) | definition |
| `Section3.Mollify.integral_normed_smul_self`, `Section3.Mollify.moll_strongMono`, `Section3.Mollify.moll_lipschitz`, `Section3.Mollify.moll_local_affine`, `Section3.Mollify.moll_remainder`, `Section3.Mollify.moll_contDiff`, `Section3.Mollify.hasGradientAt_moll` | Proposition3_4.lean | proof of Proposition 3.4: the mollifier is centered; rho_eps * g inherits 1-strong monotonicity, the kappa-Lipschitz bound, the locally affine structure and the bounded remainder; it is C^infinity and is the gradient of rho_eps * psi | formalized |
| `Section3.Mollify.hessian_bounds_of_mono_lip`, `Section3.Mollify.hasFDerivAt_id_of_affine` | Proposition3_4.lean | proof of Proposition 3.4: Hessian eigenvalue bounds [1, kappa] from monotonicity and Lipschitz continuity by the limiting argument; DU = Id on the balls B(x_j, r_0) | formalized |
| `Section3.cycle_equation`, `Section3.norm_gradPsi_sub_le` | Proposition3_4.lean | the cycle equation (3.2) for the gradient field x + (kappa - 1) M x at the cycle points; the bound b_star = (kappa - 1) max_{y in C} abs(y) | formalized |
| `Section3.proposition_3_4`, `Section3.proposition_3_4_projC` | Proposition3_4.lean | Proposition 3.4: U in U_kappa^2 (C^infinity, gradient G 1-strongly monotone and kappa-Lipschitz, Hessian bounds), (3.25), (3.26) with r_0 = r_max/2, (3.27), DG = Id near the cycle | conditional on the representation of psi from Theorem 3.1(i) only (gradient x + (kappa - 1) proj_C(x), 1-strongly monotone, kappa-Lipschitz); `proposition_3_4` takes any metric projection p as a further hypothesis, `proposition_3_4_projC` uses `projC` |
| `Section3.hasFDerivAt_hbUpdate`, `Section3.hasFDerivAt_hbUpdate_iterate` | Proposition3_4.lean | the Jacobian (3.28) of the heavy-ball update at the cycle states and A_1^m for the m-step update (chain rule along the cycle) | formalized |
| `Section3.spectralRadius_Amat_pow` | Proposition3_4.lean | rho(A_1(s, beta)^m) = rho(A_1(s, beta))^m <= rho_q(s, beta; kappa)^m < 1 | formalized |
| `Section3.Ψ`, `Section3.duhamel` | Lemma4_4.lean | proof of Lemma 4.4, products Psi_j(k, l) and the Duhamel formula | formalized |
| `Section3.error_recursion` | Lemma4_4.lean | proof of Lemma 4.4, error recursion from (4.5), (4.6), (4.10) | formalized |
| `Section3.invariant_tube` | Lemma4_4.lean | Lemma 4.4(i), deterministic core (the tube of radius aR/2 under (4.12)) | conditional on `hC`, `hG` (the bounds on the partial products, (4.8)) |
| `Section3.geometric_decay_of_spectralRadius_lt_one` | Lemma4_4.lean | after Assumption 2: constants (C, q) with the norm of the n-th power at most C q^n, from Gelfand's formula | formalized |
| `Cycle.a`, `Cycle.b`, `Cycle.c`, `Cycle.δ₀`, `Cycle.GradOK`, `Cycle.hstar`, `Cycle.βstar`, `Cycle.γstar` | Section4_5.lean | Section 4.5: the cycle points, the width delta_0, the gradient identities (4.23), the tuning h_star, beta_star, gamma_star | definition |
| `Cycle.hessian_bounds` | Section4_5.lean | (4.23), Hessian bounds of the pieces | conditional on `GradOK` (the gradient identities of the piecewise potential (4.23)) |
| `Cycle.hstar_sq`, `Cycle.βstar_eq_exp`, `Cycle.s_star`, `Cycle.sqrt_βstar`, `Cycle.hstar_lt` | Section4_5.lean | Section 4.5, tuning identities | formalized |
| `Cycle.p` | Lemma4_6.lean | Lemma 4.6, the period-three sequence | definition |
| `Cycle.cycle_steps`, `Cycle.p_values`, `Cycle.p_exact` | Lemma4_6.lean | Lemma 4.6, the exact three-cycle | formalized |
| `Cycle.grad_diff`, `Cycle.error_step`, `Cycle.bound_4_25` | Lemma4_6.lean | Lemma 4.6, (4.24) and (4.25) | formalized |
| `Cycle.lemma_4_6`, `Cycle.lemma_4_6_cycle` | Lemma4_6.lean | Lemma 4.6, bootstrap to the tube of radius 1/20 | formalized |
| `Cycle.lemma_4_6_origin`, `Cycle.tubes_disjoint` | Proposition4_7.lean | Proposition 4.7, origin tube and disjointness | formalized |
| `Cycle.eq_4_26`, `Cycle.eq_4_27`, `Cycle.tail_exponent`, `Cycle.rhs_4_28`, `Cycle.window_threshold` | Proposition4_7.lean | (4.26), (4.27), the constants in (4.28) | formalized |
| `Diffusive.e1`, `Diffusive.h`, `Diffusive.γ`, `Diffusive.cH`, `Diffusive.cstar`, `Diffusive.R24`, `Diffusive.Rr`, `Diffusive.cDiff` | Theorem5_1.lean | Theorem 5.1, the tuning and the constants | definition |
| `Diffusive.e1_bounds`, `Diffusive.γ_mul_h`, `Diffusive.β_eq`, `Diffusive.step_condition`, `Diffusive.b_sq_lt`, `Diffusive.cH_eq`, `Diffusive.cH_le`, `Diffusive.cH_lt_one` | Theorem5_1.lean | Theorem 5.1, tuning identities and the step condition of [LPW] | formalized |
| `Diffusive.max_a`, `Diffusive.wasserstein_const`, `Diffusive.sqrt_step` | Theorem5_1.lean | Theorem 5.1, the constant 147 kappa | formalized |
| `Diffusive.R24_eq`, `Diffusive.R24_le` | Theorem5_1.lean | Theorem 5.1, closed form of R_24 and R_24 <= 8.62 sqrt(kappa) | formalized |
| `Diffusive.cstar_bounds`, `Diffusive.cDiff_pos`, `Diffusive.cDiff_lt`, `Diffusive.exp_const_lt`, `Diffusive.final_constant`, `Diffusive.pow_bound` | Theorem5_1.lean | Theorem 5.1, the constant 143 and the exponent c | formalized |
| `Diffusive.small_n` | Theorem5_1.lean | Theorem 5.1, the case n <= 24 | formalized |
| `Diffusive.theorem_5_1_assembly` | Theorem5_1.lean | Theorem 5.1, assembly of the TV bound (5.1) | conditional on `hcontr` ([LPW, Theorem 5.2, Proposition 2.4]) and `hreg` ([BCS, Theorem 3.2, Corollary 3.3]) |
| `Section6.stepBAOAB`, `Section6.IsChainBAOAB`, `Section6.ζB` | Proposition6_2.lean | the BAOAB step (6.3) to (6.5), the chain, the noise (6.8) | definition |
| `Section6.eq_6_10`, `Section6.eq_6_11` | Proposition6_2.lean | (6.10), (6.11) | formalized |
| `Section6.prop_6_2`, `Section6.prop_6_2_first` | Proposition6_2.lean | Proposition 6.2, the recursion (6.7) with the noise (6.8), for k >= 1 and, under (6.6), for k = 0, as a pathwise identity | formalized |
| `Section6.covariance_scalars_BAOAB` | Proposition6_2.lean | (6.9), scalar form | formalized |
| `Section6.stepABOBA`, `Section6.IsChainABOBA`, `Section6.stepAOBOA`, `Section6.IsChainAOBOA`, `Section6.stepBOAOB`, `Section6.IsChainBOAOB`, `Section6.stepOABAO`, `Section6.IsChainOABAO`, `Section6.χ` | Proposition6_5.lean | the steps and chains of ABOBA, AOBOA, BOAOB and OABAO; the combined noise chi_m of Proposition 6.5(iv) | definition |
| `Section6.ABOBA_Y_diff`, `Section6.AOBOA_Y_diff` | Proposition6_5.lean | Proposition 6.5(i), (ii): Y_{m+1} - Y_m = h V_m for the force-evaluation points | formalized |
| `Section6.prop_6_5_i` | Proposition6_5.lean | Proposition 6.5(i), the recursion (6.13), as a pathwise identity | formalized |
| `Section6.prop_6_5_ii` | Proposition6_5.lean | Proposition 6.5(ii), the recursion (6.14), as a pathwise identity | formalized |
| `Section6.prop_6_5_iii`, `Section6.prop_6_5_iii_first` | Proposition6_5.lean | Proposition 6.5(iii), the recursion (6.16) for k >= 1 and, under (6.15), for k = 0, as a pathwise identity | formalized |
| `Section6.prop_6_5_iv` | Proposition6_5.lean | Proposition 6.5(iv), the recursion (6.17), as a pathwise identity | formalized |
| `Section6.covariance_scalar_ABOBA`, `Section6.covariance_scalar_AOBOA`, `Section6.covariance_scalars_BOAOB`, `Section6.covariance_scalars_OABAO` | Proposition6_5.lean | Proposition 6.5, the covariance scalars of the four noise sequences (including the cold-start covariance of (iii) and the covariances (6.9) for (iv)) | formalized |

## License

Apache License 2.0, see `LICENSE`.

## Citation

Tagged releases are archived on Zenodo under the concept DOI 10.5281/zenodo.22662612, which resolves to the latest archived version; each version carries its own DOI, listed on the Zenodo record.

Suggested citation:

N. Bou-Rabee, strang-nonacceleration-lean: Lean 4 companion to "Provable Non-Acceleration of Standard Strang Splittings of Kinetic Langevin Dynamics", version v1.2.0, Zenodo, 2026, doi:10.5281/zenodo.22662612

```bibtex
@software{BouRabee2026_strang_nonacceleration_lean,
  author    = {Bou-Rabee, Nawaf},
  title     = {strang-nonacceleration-lean: Lean 4 companion to ``Provable Non-Acceleration of Standard Strang Splittings of Kinetic Langevin Dynamics''},
  version   = {v1.2.0},
  year      = {2026},
  publisher = {Zenodo},
  doi       = {10.5281/zenodo.22662612},
  url       = {https://github.com/nawafbourabee/strang-nonacceleration-lean}
}
```
