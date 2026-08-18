# Maximal filters in the lattice of closed convex sets

**David Victor Feldman**, Department of Mathematics and Statistics, University of New Hampshire ([ORCID 0000-0001-6943-4833](https://orcid.org/0000-0001-6943-4833))

A paper and its Lean 4 formalization.

## The result

The closed convex subsets of $\mathbb{R}^n$ form a complete lattice under inclusion. Its maximal filters are classified: each is determined by an affine subspace $A$, a linear subspace $W$ containing the direction space of $A$, and a vector space order on $W$ in which that direction space is order-convex, subject to the single constraint that $W = 0$ when $A$ is a point, in which case the filter is principal.

Equivalently, in the dual form, a maximal filter is determined by the flat $A$ together with a convex cone $Q$ in the dual space whose exceptional set is a subspace.

The classifying space is therefore a finite disjoint union of bundles over flag manifolds. No continuous modulus records the rate at which a filter approaches the flat it hugs: two filters that hug the same flat from the same side at different rates coincide.

## Layout

```
paper/           the manuscript, LaTeX source and compiled PDF
ConvexFilters/   the Lean 4 development, 31 files
AxiomCheck.lean  the axiom audit, part of the default build target
notes/           conventions of the formalization that do not appear in the paper
```

## Building

Requires [elan](https://github.com/leanprover/elan). The toolchain is `leanprover/lean4:v4.28.0`; Mathlib is pinned by `lake-manifest.json`.

```
lake exe cache get
lake build
```

The default target includes `AxiomCheck`, so a successful build emits the axiom profile of the main results into the build transcript. CI parses that transcript and fails if any declaration depends on an axiom outside `{propext, Classical.choice, Quot.sound}`.

## Formalization scope

Sections 2 through 6 and Section 9 of the paper are formalized in full, together with all but one of the remarks: 564 declarations across 31 files, every one compiled, none using `sorry`, `native_decide`, or any additional axiom.

| Result | Lean name |
| --- | --- |
| Theorem 6.1, classification by $(A, Q)$ | `ConvexFilter.classification`, `ConvexFilter.classificationEquiv` |
| Theorem 1.2, classification by $(A, W, \prec)$ | `ConvexFilter.classificationPrimalEquiv` |
| Theorem 4.2, uniqueness | `ConvexFilter.carrier_eq_of_Aset_Qset` |
| Proposition 5.3, realization | `ConvexFilter.exists_maximal_realizing` |
| Lemma 2.2, separation | `ConvexFilter.exists_separating` |
| Lemma 4.1, relative separation | `ConvexFilter.exists_separating_of_subset_affine` |
| Lemma 9.1, the covering criterion | `ConvexFilter.Space.exists_mem_of_cover` |
| Proposition 9.2, compact and $T_1$ | `ConvexFilter.Space.isCompact_univ`, `ConvexFilter.Space.t1Space` |
| Theorem 9.4, inseparability | `ConvexFilter.Space.not_separated_Fline_Ghyp`, `ConvexFilter.Space.separated_Ghyp_Fminus` |
| Corollary 9.5, non-transitivity | `ConvexFilter.Space.separated_not_transitive` |

Sections 2 and 3, and hence the invariants, are formalized over an arbitrary real normed space. Finite dimensionality enters only from the construction of the flat onward, and this is certified by the absence of that hypothesis from the relevant files rather than by a theorem.

**Not formalized:** the passage to the maximal Hausdorff quotient in Corollary 9.6 and the conditional description that follows it, Question 9.8, the enumeration of strata in Corollary 6.2, the tables of Section 7, the failure of Lemma 2.2 in infinite dimensions (quoted from the literature), and Remark 8.9, whose saturation argument has no counterpart in Mathlib at the pinned revision. Appendix A of the paper states the boundary precisely.

Two results in the development are not in Mathlib at the pinned revision and may be of independent use: weak separation of two disjoint convex sets in finite dimensions with no topological hypothesis on either side, and its relative form controlling the separating functional on a prescribed affine subspace.

## Provenance

The Lean development was produced with [Aristotle](https://aristotle.harmonic.fun) (Harmonic) working from written specifications, each return audited against a compiled build and a clean axiom profile before acceptance. Three claims asserted in drafts were refuted during formalization and corrected: the proof of Theorem 4.2 no longer inducts on dimension, the generating family of Section 5 was reduced and its maximality claim corrected, and Corollary 6.2's assertion that the family generates the filter was weakened to what is proved.

## Licenses

The manuscript in `paper/` is under [CC BY 4.0](LICENSE). The Lean sources and build configuration are under [Apache 2.0](LICENSE-CODE).

## Citing

See `CITATION.cff`.
