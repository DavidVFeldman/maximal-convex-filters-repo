import ConvexFilters.Bridge
import ConvexFilters.Uniqueness
import ConvexFilters.Support
import ConvexFilters.Principal

/-!
# The classification of maximal convex filters

This file is Parts B and C of WO-06b: Theorem 6.1 of the paper and its packaging as a
bijection.

`IsAdmissible A Q` collects clauses (1)–(3) of Theorem 6.1 for a pair consisting of a
nonempty affine subspace `A ⊆ V` and a subset `Q` of the continuous dual, with the
exceptional submodule carried existentially.

## Main results

* `ConvexFilter.AsetAff` — the flat `Aset F` packaged as an affine subspace;
* `ConvexFilter.isAdmissible_invariants` — the invariants of a maximal filter are admissible;
* `ConvexFilter.exists_maximal_of_isAdmissible` — surjectivity: every admissible pair is
  realized;
* `ConvexFilter.classification` — existence and uniqueness;
* `ConvexFilter.classificationEquiv` — the classification as a bijection.
-/

open Module

namespace ConvexFilter

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {F : ConvexFilter V}

/-! ## Part B — admissibility -/

/-- Clauses (1)–(3) of Theorem 6.1: the data attached to a maximal convex filter, with the
exceptional submodule `M` of the dual carried existentially rather than as data. -/
structure IsAdmissible (A : AffineSubspace ℝ V) (Q : Set (V →L[ℝ] ℝ)) : Prop where
  A_nonempty : (A : Set V).Nonempty
  exceptional : ∃ M : Submodule ℝ (V →L[ℝ] ℝ),
      (∀ u, u ∈ (M : Set (V →L[ℝ] ℝ)) ↔ (u ∉ Q ∧ -u ∉ Q)) ∧
      Adapted.IsLexConeModOn ⊤ M Q ∧
      M ≤ annih A.direction
  orderConvex : IsOrderConvex Q (annih A.direction)
  degenerate : A.direction = ⊥ → Q = ∅

/-- The flat of a maximal convex filter, packaged as an affine subspace: the coset of
`dirA F` through a point of `Aset F`. This is the analogue for `Aset` of `SsetAff`. -/
noncomputable def AsetAff (F : ConvexFilter V) (hF : IsMaximal F) : AffineSubspace ℝ V :=
  AffineSubspace.mk' (Aset_nonempty hF).choose (dirA F)

theorem coe_AsetAff (hF : IsMaximal F) :
    ((AsetAff F hF : AffineSubspace ℝ V) : Set V) = Aset F := by
  have ha : (Aset_nonempty hF).choose ∈ Aset F := (Aset_nonempty hF).choose_spec
  ext x
  constructor
  · intro hx
    exact (mem_Aset_iff_sub_mem_dirA ha x).2 hx
  · intro hx
    exact (mem_Aset_iff_sub_mem_dirA ha x).1 hx

theorem direction_AsetAff (hF : IsMaximal F) : (AsetAff F hF).direction = dirA F :=
  AffineSubspace.direction_mk' _ _

theorem AsetAff_nonempty (hF : IsMaximal F) : ((AsetAff F hF : AffineSubspace ℝ V) : Set V).Nonempty := by
  rw [coe_AsetAff hF]
  exact Aset_nonempty hF

omit [FiniteDimensional ℝ V] in
/-- `Nset F` is order convex for the cone `Qset F`: this is the order-convexity clause of
Theorem 6.1 for the invariants of a maximal filter. -/
theorem isOrderConvex_Qset_Nset (hF : IsMaximal F) :
    IsOrderConvex (Qset F) (NsubmoduleOf F hF) := by
  intro w v hw hvw hv
  by_contra hwN
  have hwE : w ∈ Eset F := by
    rcases (Qset_eq_Eset_union_Dset hF ▸ hw : w ∈ Eset F ∪ Dset F) with h | h
    · exact h
    · exact absurd h.1 hwN
  have hnv : -v ∈ Nset F := Nset_neg hv
  have hsum : w + -v ∈ Eset F := Eset_add_Nset hF hwE hnv
  have : -(v - w) ∈ Qset F := by
    have hEQ : Eset F ⊆ Qset F := Eset_subset_Qset hF
    have : w + -v = -(v - w) := by abel
    exact hEQ (this ▸ hsum)
  exact Qset_not_neg hF hvw this

/-- If the direction of the flat is trivial then the positivity cone is empty: Proposition 2.7
in the form Theorem 6.1 needs. -/
theorem Qset_eq_empty_of_dirA_eq_bot (hF : IsMaximal F) (h : dirA F = ⊥) : Qset F = ∅ := by
  have hN : Nset F = Set.univ := by
    rw [Nset_eq_annihilator_dirA hF]
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    intro v hv
    rw [h] at hv
    rw [(Submodule.mem_bot ℝ).1 hv, map_zero]
  have hM : Mset F = Set.univ := Mset_univ_of_Nset_univ hF hN
  ext u
  simp only [Set.mem_empty_iff_false, iff_false]
  exact Mset_disjoint_Qset hF (by rw [hM]; trivial)

/-- Theorem 6.1, forward direction: the invariants of a maximal convex filter are
admissible. -/
theorem isAdmissible_invariants (hF : IsMaximal F) : IsAdmissible (AsetAff F hF) (Qset F) := by
  have hdir : (AsetAff F hF).direction = dirA F := direction_AsetAff hF
  have hann : annih (AsetAff F hF).direction = NsubmoduleOf F hF := by
    rw [hdir]; exact annih_dirA hF
  refine ⟨AsetAff_nonempty hF, ⟨MsubmoduleOf F hF, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro u
    change u ∈ Mset F ↔ _
    rw [Mset_eq_compl_Qset hF]
    exact Iff.rfl
  · exact
      { M_le := le_top
        mem_of_mem := fun _ _ => trivial
        add_mem := fun _ _ hx hy => Qset_add hF hx hy
        smul_mem := fun _ hc _ hx => Qset_smul hF hc hx
        trichotomy := fun x _ => by
          rcases mem_Qset_or_neg_or_Mset hF x with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
          · exact Or.inr (Or.inl h)
        notMem_M := fun _ hx hxM => Mset_disjoint_Qset hF hxM hx
        neg_notMem := fun _ hx => Qset_not_neg hF hx }
  · rw [hann]
    intro u hu
    exact Mset_subset_Nset hF hu
  · rw [hann]
    exact isOrderConvex_Qset_Nset hF
  · intro h
    rw [hdir] at h
    exact Qset_eq_empty_of_dirA_eq_bot hF h

/-! ## Part C — Theorem 6.1 -/

omit [FiniteDimensional ℝ V] in
/-- Membership in the span of the first `d` vectors of a basis, in coordinates. -/
theorem mem_span_basisAt_iff {n : ℕ} (b : Basis (Fin n) ℝ V) (d : ℕ) (v : V) :
    v ∈ Submodule.span ℝ (Set.range (fun i : Fin d => basisAt b (i : ℕ))) ↔
      ∀ j : Fin n, d ≤ (j : ℕ) → b.coord j v = 0 := by
  classical
  have hspan : Submodule.span ℝ (Set.range (fun i : Fin d => basisAt b (i : ℕ)))
      = Submodule.span ℝ (b '' {i : Fin n | (i : ℕ) < d}) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro x ⟨i, rfl⟩
      show basisAt b (i : ℕ) ∈ _
      by_cases hi : (i : ℕ) < n
      · refine Submodule.subset_span ⟨⟨(i : ℕ), hi⟩, ?_, ?_⟩
        · exact i.2
        · exact (basisAt_of_lt b hi).symm
      · rw [basisAt_of_le b (Nat.not_lt.1 hi)]
        exact Submodule.zero_mem _
    · rw [Submodule.span_le]
      rintro x ⟨j, hj, rfl⟩
      have hjd : (j : ℕ) < d := hj
      refine Submodule.subset_span ⟨⟨(j : ℕ), hjd⟩, ?_⟩
      simp
  rw [hspan, Basis.mem_span_image]
  constructor
  · intro h j hj
    by_contra hne
    have : j ∈ (b.repr v).support := Finsupp.mem_support_iff.2 (by simpa [Basis.coord] using hne)
    have := h this
    simp only [Set.mem_setOf_eq] at this
    omega
  · intro h j hj
    simp only [Finset.mem_coe, Finsupp.mem_support_iff] at hj
    simp only [Set.mem_setOf_eq]
    by_contra hlt
    exact hj (by simpa [Basis.coord] using h j (Nat.not_lt.1 hlt))

omit [FiniteDimensional ℝ V] in
/-- The flat cut out by the vanishing of the coordinates of index `≥ d` is `A` itself, when
`a ∈ A` and `A.direction` is the span of the first `d` basis vectors. -/
theorem A0_eq_coe {n : ℕ} (b : Basis (Fin n) ℝ V) {A : AffineSubspace ℝ V} {a : V}
    (ha : a ∈ A) {d : ℕ}
    (hdir : A.direction = Submodule.span ℝ (Set.range (fun i : Fin d => basisAt b (i : ℕ)))) :
    A0 b a d = (A : Set V) := by
  ext x
  have hkey : x ∈ A ↔ x - a ∈ A.direction := by
    rw [← AffineSubspace.vsub_right_mem_direction_iff_mem ha x]
    simp [vsub_eq_sub]
  rw [SetLike.mem_coe, hkey, hdir, mem_span_basisAt_iff]
  constructor
  · intro hx j hj
    have := hx (j : ℕ) hj
    rwa [coordAt_of_lt j.2] at this
  · intro hx j hj
    by_cases hjn : j < n
    · have := hx ⟨j, hjn⟩ hj
      rwa [coordAt_of_lt hjn]
    · exact coordAt_of_le (Nat.not_lt.1 hjn) x

/-- The positivity cone of a principal filter is empty. -/
theorem Qset_principal (p : V) : Qset (principal p) = ∅ := by
  have hM : Mset (principal p) = Set.univ :=
    Mset_univ_of_Nset_univ (principal_isMaximal p) (Nset_univ_of_principal p)
  ext u
  simp only [Set.mem_empty_iff_false, iff_false]
  exact Mset_disjoint_Qset (principal_isMaximal p) (by rw [hM]; trivial)

/-- Theorem 6.1, surjectivity: every admissible pair is the pair of invariants of a maximal
convex filter. -/
theorem exists_maximal_of_isAdmissible {A : AffineSubspace ℝ V} {Q : Set (V →L[ℝ] ℝ)}
    (h : IsAdmissible A Q) :
    ∃ F : ConvexFilter V, IsMaximal F ∧ Aset F = (A : Set V) ∧ Qset F = Q := by
  obtain ⟨a, ha⟩ := h.A_nonempty
  by_cases hbot : A.direction = ⊥
  · -- degenerate case: `A` is a point and `Q` is empty
    have hQ : Q = ∅ := h.degenerate hbot
    have hA : (A : Set V) = {a} := by
      ext x
      constructor
      · intro hx
        have : x - a ∈ A.direction := by
          rw [← vsub_eq_sub]
          exact AffineSubspace.vsub_mem_direction hx ha
        rw [hbot, Submodule.mem_bot, sub_eq_zero] at this
        exact this
      · rintro rfl
        exact ha
    refine ⟨principal a, principal_isMaximal a, ?_, ?_⟩
    · rw [Aset_principal, hA]
    · rw [Qset_principal, hQ]
  · -- main case
    obtain ⟨M, hMQ, hlex, hMN⟩ := h.exceptional
    have hpre : Adapted.preAnnih (annih A.direction) ≠ ⊥ := by
      rw [preAnnih_annih]
      exact hbot
    obtain ⟨b, d, m, hd, hdm, hmn, hQ0, hM0, hdir⟩ :=
      Adapted.exists_adapted_basis hlex hMN h.orderConvex hpre
    rw [preAnnih_annih] at hdir
    obtain ⟨F, hF, hAF, hQF, -⟩ := exists_maximal_realizing b a hd hdm hmn
    refine ⟨F, hF, ?_, ?_⟩
    · rw [hAF]
      exact A0_eq_coe b ha hdir
    · rw [hQF, hQ0]
      exact (Adapted.Q0_eq b m).symm

/-! ## The classification -/

omit [FiniteDimensional ℝ V] in
/-- A convex filter is determined by its carrier: all other fields are propositions. -/
theorem ext_of_carrier_eq {F F' : ConvexFilter V} (h : F.carrier = F'.carrier) : F = F' := by
  cases F
  cases F'
  subst h
  rfl

/-- Uniqueness: a maximal convex filter is determined by its flat and its positivity cone. -/
theorem eq_of_Aset_Qset {F F' : ConvexFilter V} (hF : IsMaximal F) (hF' : IsMaximal F')
    (hA : Aset F = Aset F') (hQ : Qset F = Qset F') : F = F' :=
  ext_of_carrier_eq (carrier_eq_of_Aset_Qset hF hF' hA hQ)

/-- Theorem 6.1: the maximal convex filters are in bijection with the admissible pairs;
here in existence-and-uniqueness form. -/
theorem classification :
    ∀ (A : AffineSubspace ℝ V) (Q : Set (V →L[ℝ] ℝ)), IsAdmissible A Q →
      ∃! F : {G : ConvexFilter V // IsMaximal G},
        Aset (F : ConvexFilter V) = (A : Set V) ∧ Qset (F : ConvexFilter V) = Q := by
  intro A Q h
  obtain ⟨F, hF, hA, hQ⟩ := exists_maximal_of_isAdmissible h
  refine ⟨⟨F, hF⟩, ⟨hA, hQ⟩, ?_⟩
  rintro ⟨G, hG⟩ ⟨hAG, hQG⟩
  exact Subtype.ext (eq_of_Aset_Qset hG hF (by rw [hAG, hA]) (by rw [hQG, hQ]))

/-- Theorem 6.1 as a bijection between maximal convex filters and admissible pairs. -/
noncomputable def classificationEquiv :
    {F : ConvexFilter V // IsMaximal F} ≃
      {p : AffineSubspace ℝ V × Set (V →L[ℝ] ℝ) // IsAdmissible p.1 p.2} where
  toFun F := ⟨(AsetAff (F : ConvexFilter V) F.2, Qset (F : ConvexFilter V)),
    isAdmissible_invariants F.2⟩
  invFun p := ((classification p.1.1 p.1.2 p.2).choose)
  left_inv := by
    rintro ⟨F, hF⟩
    obtain ⟨hspec, -⟩ :=
      (classification (AsetAff F hF) (Qset F) (isAdmissible_invariants hF)).choose_spec
    set G := (classification (AsetAff F hF) (Qset F) (isAdmissible_invariants hF)).choose with hG
    refine Subtype.ext (eq_of_Aset_Qset G.2 hF ?_ hspec.2)
    rw [hspec.1, coe_AsetAff hF]
  right_inv := by
    rintro ⟨⟨A, Q⟩, hAQ⟩
    obtain ⟨hspec, -⟩ := (classification A Q hAQ).choose_spec
    set G := (classification A Q hAQ).choose with hG
    refine Subtype.ext ?_
    have hA : ((AsetAff (G : ConvexFilter V) G.2 : AffineSubspace ℝ V) : Set V) = (A : Set V) := by
      rw [coe_AsetAff G.2, hspec.1]
    exact Prod.ext (SetLike.coe_injective hA) hspec.2

theorem classificationEquiv_apply (F : ConvexFilter V) (hF : IsMaximal F) :
    (classificationEquiv ⟨F, hF⟩ : AffineSubspace ℝ V × Set (V →L[ℝ] ℝ))
      = (AsetAff F hF, Qset F) := rfl

end ConvexFilter
