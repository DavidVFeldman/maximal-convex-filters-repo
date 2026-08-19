/-
Axiom audit for the classification of maximal convex filters.

This file is part of the default build target, so the audit is compiled rather
than scripted over the sources. Each `#print axioms` below emits a line of the
form `'name' depends on axioms: [...]` into the build transcript, which the CI
workflow parses. The expected axiom set throughout is
`[propext, Classical.choice, Quot.sound]`.
-/
import ConvexFilters.Classification
import ConvexFilters.Primal
import ConvexFilters.PrimalSurj
import ConvexFilters.Realization
import ConvexFilters.Separation
import ConvexFilters.SeparationRel
import ConvexFilters.SigCounterexample
import ConvexFilters.SpaceTop
import ConvexFilters.LimitSep
import ConvexFilters.LimitRidge
import ConvexFilters.WedgeGen
import ConvexFilters.SigmaCont
import ConvexFilters.Quotient
import ConvexFilters.Fibres
import ConvexFilters.FibreCounterexample
import ConvexFilters.Boundary

-- Theorem 6.1, the classification by the pair (A, Q).
#print axioms ConvexFilter.classification
#print axioms ConvexFilter.classificationEquiv

-- Theorem 1.2, the classification by the triple (A, W, order).
#print axioms ConvexFilter.classification_primal_bijective
#print axioms ConvexFilter.classificationPrimalEquiv

-- Theorem 4.2, uniqueness.
#print axioms ConvexFilter.carrier_eq_of_Aset_Qset

-- Proposition 5.3, realization.
#print axioms ConvexFilter.exists_maximal_realizing

-- Lemma 2.2 and Lemma 4.1, separation.
#print axioms ConvexFilter.exists_separating
#print axioms ConvexFilter.exists_separating_of_subset_affine

-- Remark 8.1, the two filters with equal cone and unequal flat.
#print axioms ConvexFilter.not_carrier_eq_of_sig_Qset

-- WO-09, Section 9: the space of maximal filters.

-- Lemma 9.1, the covering criterion, and the separation relation it defines.
#print axioms ConvexFilter.Space.exists_mem_of_cover
#print axioms ConvexFilter.Space.cover_of_forall_mem
#print axioms ConvexFilter.Space.Separated.symm
#print axioms ConvexFilter.Space.not_separated_self

-- Section 9, the three filters over a line, and Lemma 9.3.
#print axioms ConvexFilter.Space.Fline_isMaximal
#print axioms ConvexFilter.Space.mem_Fline_iff
#print axioms ConvexFilter.Space.Fminus_isMaximal
#print axioms ConvexFilter.Space.wedge

-- Theorem 9.4 and Corollary 9.5.
#print axioms ConvexFilter.Space.not_separated_Fline_Ghyp
#print axioms ConvexFilter.Space.separated_Ghyp_Fminus
#print axioms ConvexFilter.Space.not_separated_Fline_Fminus
#print axioms ConvexFilter.Space.separated_not_transitive

-- Section 9, the topology: compact, T1, not Hausdorff.
#print axioms ConvexFilter.Space.separated_iff_disjoint_nhds
#print axioms ConvexFilter.Space.isCompact_univ
#print axioms ConvexFilter.Space.t1Space
#print axioms ConvexFilter.Space.not_t2Space

-- WO-10, Section 9: the general wedge and the continuity of the invariant.

-- Lemma 9.2, the homothety invariance, and the transport it rests on.
#print axioms ConvexFilter.Space.comapAffine_isMaximal
#print axioms ConvexFilter.Space.homothety_fixes

-- Lemma 9.1 in relative form, and the membership criterion of Proposition 2.8.
#print axioms ConvexFilter.Space.mem_of_forall_inter_nonempty
#print axioms ConvexFilter.Space.exists_mem_of_cover_of_mem

-- Lemma 9.3, the general wedge.
#print axioms ConvexFilter.Space.wedge_gen

-- Theorem 9.5, the two clauses, and its instance d = 1, n = 2.
#print axioms ConvexFilter.Space.not_separated_gen
#print axioms ConvexFilter.Space.separated_gen
#print axioms ConvexFilter.Space.not_separated_Fline_Ghyp_of_gen

-- Lemma 9.9, the continuity of the extended support value.
#print axioms ConvexFilter.Space.continuous_lev_indicator
#print axioms ConvexFilter.Space.sigma_continuous

-- Theorem 9.10, the clause within reach.
#print axioms ConvexFilter.Space.separated_of_levVal_ne
#print axioms ConvexFilter.Space.eq_of_sig_eq_of_not_separated

-- WO-11, Part A. Corollary 9.7: the collapse of the fibre in the Hausdorff quotient.
#print axioms ConvexFilter.Space.eq_of_continuous_of_not_separated
#print axioms ConvexFilter.Space.eq_of_continuous_FA_Fplus
#print axioms ConvexFilter.Space.eq_of_continuous_FA_Fminus
#print axioms ConvexFilter.Space.eq_of_continuous_Fplus_Fminus
#print axioms ConvexFilter.Space.t2Quotient_mk_eq_of_not_separated
#print axioms ConvexFilter.Space.t2Quotient_mk_eq_FA_Fplus
#print axioms ConvexFilter.Space.t2Quotient_mk_eq_FA_Fminus
#print axioms ConvexFilter.Space.t2Quotient_mk_eq_Fplus_Fminus

-- WO-11, Part B. Theorem 9.9, first clause: the invariants recorded by levVal.
#print axioms ConvexFilter.Space.Nset_eq_of_levVal_eq
#print axioms ConvexFilter.Space.Aset_eq_of_levVal_eq
#print axioms ConvexFilter.Space.Eset_eq_of_levVal_eq

-- WO-11, Part B. The filter of stratum (d, d) beneath a maximal filter.
#print axioms ConvexFilter.Space.isAdmissible_Aset_Eset
#print axioms ConvexFilter.Space.exists_maximal_flat

-- WO-11, Part B. The enumeration of the fibres in the plane.
#print axioms ConvexFilter.Space.eq_of_levVal_eq_of_dim_zero
#print axioms ConvexFilter.Space.fibre_of_line_flat
#print axioms ConvexFilter.Space.fibre_of_line
#print axioms ConvexFilter.Space.eq_of_levVal_eq_of_dim_two

-- WO-11, Part B. Theorem 9.9, first clause.
#print axioms ConvexFilter.Space.levVal_separates_quotient
#print axioms ConvexFilter.Space.levVal_eq_iff_forall_continuous_eq

-- WO-11, Part B. The refutation of the contract form of fibre_of_line.
#print axioms ConvexFilter.Space.FibreCounterexample.levVal_Grefl_eq
#print axioms ConvexFilter.Space.FibreCounterexample.separated_Ghyp_Grefl
#print axioms ConvexFilter.Space.FibreCounterexample.not_fibre_of_line

-- WO-12, Part A. The image of the plane is open and the boundary is compact.
#print axioms ConvexFilter.Space.denseRange_prin
#print axioms ConvexFilter.Space.isOpen_range_principal
#print axioms ConvexFilter.Space.isCompact_boundary

-- WO-12, Part B. The parametrization of the boundary.
#print axioms ConvexFilter.Space.boundaryMap
#print axioms ConvexFilter.Space.boundaryMap_eq_of_levVal_eq
#print axioms ConvexFilter.Space.escape_dir_unique
#print axioms ConvexFilter.Space.levVal_eq_of_dirOf_offOf_eq
#print axioms ConvexFilter.Space.boundaryMap_injective_on_quotient
#print axioms ConvexFilter.Space.boundaryMap_surjective

-- WO-12, Part B. The refutation of the continuity clause.
#print axioms ConvexFilter.Space.not_continuousOn_boundaryMap

-- WO-12, Part C. The refutation of the homeomorphism.
#print axioms ConvexFilter.Space.not_secondCountableTopology_boundarySet
#print axioms ConvexFilter.Space.not_injective_of_continuous_of_secondCountable
#print axioms ConvexFilter.Space.not_boundary_homeomorph

-- WO-13, the algebra of functions with limits along maximal filters
#print axioms ConvexFilter.Limits.Dset_eq_of_lim_eq
#print axioms ConvexFilter.Limits.Qset_eq_of_lim_eq
#print axioms ConvexFilter.Limits.continuous_ridge
#print axioms ConvexFilter.Limits.continuous_sepFun
#print axioms ConvexFilter.Limits.eq_of_lim_eq
#print axioms ConvexFilter.Limits.exists_mem_disjoint_band
#print axioms ConvexFilter.Limits.exists_mem_disjoint_of_not_principal
#print axioms ConvexFilter.Limits.exists_mem_relative_position
#print axioms ConvexFilter.Limits.injective_sepFun
#print axioms ConvexFilter.Limits.isBounded_inter_band_of_subset_below
#print axioms ConvexFilter.Limits.levVal_eq_of_lim_eq
#print axioms ConvexFilter.Limits.lim_add
#print axioms ConvexFilter.Limits.lim_const
#print axioms ConvexFilter.Limits.lim_indicator_table
#print axioms ConvexFilter.Limits.lim_mul
#print axioms ConvexFilter.Limits.lim_principal
#print axioms ConvexFilter.Limits.lim_ridge_eq_zero
#print axioms ConvexFilter.Limits.lim_smul
#print axioms ConvexFilter.Limits.mem_A_add
#print axioms ConvexFilter.Limits.mem_A_comp_functional
#print axioms ConvexFilter.Limits.mem_A_const
#print axioms ConvexFilter.Limits.mem_A_indicator_ge
#print axioms ConvexFilter.Limits.mem_A_indicator_gt
#print axioms ConvexFilter.Limits.mem_A_mul
#print axioms ConvexFilter.Limits.mem_A_of_tendsto_zero
#print axioms ConvexFilter.Limits.mem_A_ridge
#print axioms ConvexFilter.Limits.mem_A_smul
#print axioms ConvexFilter.Limits.mem_toFilter_iff
#print axioms ConvexFilter.Limits.neBot
#print axioms ConvexFilter.Limits.not_tendsto_cocompact_ridge
#print axioms ConvexFilter.Limits.ridge_eq_one
#print axioms ConvexFilter.Limits.tendsto_coe_levVal
#print axioms ConvexFilter.Limits.tendsto_lim
