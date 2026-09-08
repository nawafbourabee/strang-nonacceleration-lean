import StrangNonAcceleration
-- Every statement below should report only [propext, Classical.choice, Quot.sound].
-- Section1.lean
#print axioms OBABO.norm_root_le
#print axioms OBABO.exists_root_norm_eq
#print axioms OBABO.spectralRadius_Amat
#print axioms OBABO.rootRad_le_iff
#print axioms OBABO.sqrt_le_ρq
#print axioms OBABO.ρq_le_iff
#print axioms OBABO.ρq_facts
#print axioms OBABO.ell_ρq_le
#print axioms OBABO.rho_star_le_ρq
-- Corollary1_2.lean
#print axioms OBABO.log_ratio_le
#print axioms OBABO.log_inv_q_le
#print axioms OBABO.nstar_property
#print axioms OBABO.nstar_lower
-- Corollary1_3.lean
#print axioms OBABO.corollary_1_3_i
#print axioms OBABO.corollary_1_3_ii
-- Proposition2_1.lean
#print axioms OBABO.Section2.eq_2_5
#print axioms OBABO.Section2.eq_2_6
#print axioms OBABO.Section2.prop_2_1
#print axioms OBABO.Section2.prop_2_1_first
#print axioms OBABO.Section2.covariance_scalars
-- Lemma2_2.lean
#print axioms OBABO.lemma_2_2
#print axioms OBABO.step_size_form
#print axioms OBABO.real_root_le_neg_one
#print axioms OBABO.Section2.step_quadratic
#print axioms OBABO.Section2.trace_Mmat
#print axioms OBABO.Section2.det_Mmat
#print axioms OBABO.Section2.charpoly_Mmat
#print axioms OBABO.Section2.charpoly_Amat
#print axioms OBABO.Section2.mem_spectrum_Amat
#print axioms OBABO.Section2.spectrum_Mmat_eq
#print axioms OBABO.Section2.position_recursion_quadratic
#print axioms OBABO.Section2.lemma_2_2_Amat
#print axioms OBABO.Section2.lemma_2_2_OBABO
#print axioms OBABO.Section2.real_eigenvalue_Mmat
#print axioms OBABO.Section2.exists_left_eigenvector
#print axioms OBABO.Section2.det_Nmat
#print axioms OBABO.Section2.Nmat_transpose_mulVec_ne_zero
#print axioms OBABO.Section2.scalar_recursion
#print axioms OBABO.Section2.sum_sq_pow_ge
#print axioms OBABO.Section2.charfun_contradiction
-- Theorem3_1.lean
#print axioms OBABO.identity_3_11
#print axioms OBABO.sin_eq_one_sub_cos_mul_cot
#print axioms OBABO.b_neg
#print axioms OBABO.Section3.I0_eq
#print axioms OBABO.Section3.I0_eq_half
#print axioms OBABO.Section3.g_neg_of_g_neg
#print axioms OBABO.Section3.I0_neg_of_I0_one_neg
#print axioms OBABO.Section3.xc_ne_one
#print axioms OBABO.Section3.rmax_pos
#print axioms OBABO.Section3.projection_inequality
#print axioms OBABO.Section3.variational_inequality
#print axioms OBABO.Section3.nearest_point
#print axioms OBABO.Section3.nearest_unique
#print axioms OBABO.Section3.proj_const
#print axioms OBABO.Section3.theorem_3_1_ii
#print axioms OBABO.Section3.I0_one_neg_of_Pcyc_neg
#print axioms OBABO.Section3.theorem_3_1_ii_of_Pcyc
#print axioms OBABO.Section3.exists_isMetricProj
#print axioms OBABO.Section3.theorem_3_1_ii_projC
-- Lemma3_2.lean
#print axioms OBABO.lemma_3_2_m3'
#print axioms OBABO.lemma_3_2_identity
#print axioms OBABO.one_div_one_add_le
#print axioms OBABO.inv_cos_two_pi_div_five_add_two
#print axioms OBABO.Pcyc_eq_mul_roots
#print axioms OBABO.Disc_nonneg_of_βMinus_le
#print axioms OBABO.le_βMinus_of_Disc_nonpos
#print axioms OBABO.Disc_at_β0_nonpos
#print axioms OBABO.cos_θm_lt
#print axioms OBABO.sin_succ_ge
#print axioms OBABO.one_sub_cos_ratio
#print axioms OBABO.βMinus_ge
#print axioms OBABO.xi_bound
#print axioms OBABO.key_m3
#print axioms OBABO.add_inv_antitone
#print axioms OBABO.key_ge4
#print axioms OBABO.lemma_3_2
-- Lemma3_3.lean
#print axioms OBABO.u_small
#print axioms OBABO.frac_anti
#print axioms OBABO.frac_identity
#print axioms OBABO.ell_q
#print axioms OBABO.step1_numerics
#print axioms OBABO.ell_strictAnti
#print axioms OBABO.le_larger_root
#print axioms OBABO.P3_at_edge
#print axioms OBABO.P3_at_edge_nonpos
#print axioms OBABO.s_plus_3_ge
#print axioms OBABO.Section3.lemma33_step2
#print axioms OBABO.Section3.lemma33_step2_s_lower
#print axioms OBABO.Section3.lemma33_step3_m3
#print axioms OBABO.one_sub_cos_ratio_le
#print axioms OBABO.cos_θm_mono
#print axioms OBABO.exists_m0
#print axioms OBABO.βMinus_le_of
#print axioms OBABO.βMinus_le_of_ratio
#print axioms OBABO.sMinus_le_bound
#print axioms OBABO.lemma_3_3
-- Proposition3_4.lean
#print axioms OBABO.Section3.Mollify.hessian_bounds_of_mono_lip
#print axioms OBABO.Section3.Mollify.hasFDerivAt_id_of_affine
#print axioms OBABO.Section3.Mollify.integral_normed_smul_self
#print axioms OBABO.Section3.Mollify.moll_strongMono
#print axioms OBABO.Section3.Mollify.moll_lipschitz
#print axioms OBABO.Section3.Mollify.moll_local_affine
#print axioms OBABO.Section3.Mollify.moll_remainder
#print axioms OBABO.Section3.Mollify.moll_contDiff
#print axioms OBABO.Section3.Mollify.hasGradientAt_moll
#print axioms OBABO.Section3.cycle_equation
#print axioms OBABO.Section3.norm_gradPsi_sub_le
#print axioms OBABO.Section3.hasFDerivAt_hbUpdate
#print axioms OBABO.Section3.hasFDerivAt_hbUpdate_iterate
#print axioms OBABO.Section3.spectralRadius_Amat_pow
#print axioms OBABO.Section3.proposition_3_4
#print axioms OBABO.Section3.proposition_3_4_projC
-- Lemma4_4.lean
#print axioms OBABO.Section3.geometric_decay_of_spectralRadius_lt_one
#print axioms OBABO.Section3.duhamel
#print axioms OBABO.Section3.invariant_tube
#print axioms OBABO.Section3.error_recursion
-- Section4_5.lean
#print axioms OBABO.Cycle.hessian_bounds
#print axioms OBABO.Cycle.βstar_eq_exp
#print axioms OBABO.Cycle.s_star
#print axioms OBABO.Cycle.hstar_lt
-- Lemma4_6.lean
#print axioms OBABO.Cycle.cycle_steps
#print axioms OBABO.Cycle.p_exact
#print axioms OBABO.Cycle.grad_diff
#print axioms OBABO.Cycle.bound_4_25
#print axioms OBABO.Cycle.lemma_4_6
#print axioms OBABO.Cycle.lemma_4_6_cycle
-- Proposition4_7.lean
#print axioms OBABO.Cycle.lemma_4_6_origin
#print axioms OBABO.Cycle.tubes_disjoint
#print axioms OBABO.Cycle.eq_4_26
#print axioms OBABO.Cycle.eq_4_27
#print axioms OBABO.Cycle.tail_exponent
#print axioms OBABO.Cycle.rhs_4_28
#print axioms OBABO.Cycle.window_threshold
-- Theorem5_1.lean
#print axioms OBABO.Diffusive.γ_mul_h
#print axioms OBABO.Diffusive.β_eq
#print axioms OBABO.Diffusive.step_condition
#print axioms OBABO.Diffusive.b_sq_lt
#print axioms OBABO.Diffusive.cH_eq
#print axioms OBABO.Diffusive.max_a
#print axioms OBABO.Diffusive.wasserstein_const
#print axioms OBABO.Diffusive.R24_eq
#print axioms OBABO.Diffusive.R24_le
#print axioms OBABO.Diffusive.final_constant
#print axioms OBABO.Diffusive.pow_bound
#print axioms OBABO.Diffusive.small_n
#print axioms OBABO.Diffusive.sqrt_step
#print axioms OBABO.Diffusive.theorem_5_1_assembly
