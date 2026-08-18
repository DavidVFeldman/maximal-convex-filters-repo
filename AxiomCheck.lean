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
