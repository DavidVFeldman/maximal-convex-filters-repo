import ConvexFilters.Uniqueness

/-!
# The affine trace of a maximal convex filter (Remark 8.8)

Remark 8.8 asks what a maximal convex filter looks like when one records only its affine
members. In finite dimensions the answer is that the affine members of `F` are exactly the
affine subspaces containing the support `Sset F` (`mem_affineTrace_iff`), so the trace is
the principal filter at `Sset F`, and it depends on nothing beyond the pair
`(Mset F, sig F |_{Mset F})` (`affineTrace_determined`).

The converse direction, which the order leaves optional, is also short and is proved here:
the trace determines `Sset F` — it has a least element — and `Sset F` in turn determines
`Mset F` and the restriction of `sig F` to it (`Mset_eq_of_affineTrace_eq`,
`sig_eq_of_affineTrace_eq`). So the trace sees exactly `(Mset F, sig F |_{Mset F})`.
-/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {F F' : ConvexFilter V}

namespace ConvexFilter

/-- The affine trace of `F`: the members of `F` which are affine subspaces. -/
def affineTrace (F : ConvexFilter V) : Set (Set V) :=
  {C ∈ F.carrier | ∃ T : AffineSubspace ℝ V, (T : Set V) = C}

omit [FiniteDimensional ℝ V] in
theorem mem_affineTrace_iff_of_mem {C : Set V} :
    C ∈ affineTrace F ↔ C ∈ F.carrier ∧ ∃ T : AffineSubspace ℝ V, (T : Set V) = C := Iff.rfl

/-- **Remark 8.8, finite-dimensional half.** An affine subspace belongs to a maximal convex
filter exactly when it contains the support: the affine trace is the principal filter at
`Sset F`.

The nonemptiness hypothesis `hT` turns out to be unnecessary, and is kept per WO-06b
§1.12. -/
theorem mem_affineTrace_iff (hF : IsMaximal F) {T : AffineSubspace ℝ V}
    (hT : ((T : Set V)).Nonempty) :
    (T : Set V) ∈ F.carrier ↔ Sset F ⊆ (T : Set V) := by
  constructor
  · exact fun h => Sset_subset_of_affine_mem hF h
  · intro h
    exact F.mem_of_superset (Sset_mem hF) (AffineSubspace.closed_of_finiteDimensional T)
      (AffineSubspace.convex T) h

/-- The support belongs to the affine trace. -/
theorem Sset_mem_affineTrace (hF : IsMaximal F) : Sset F ∈ affineTrace F :=
  ⟨Sset_mem hF, SsetAff F hF, coe_SsetAff hF⟩

/-- The support is the least member of the affine trace. -/
theorem Sset_subset_of_mem_affineTrace (hF : IsMaximal F) {C : Set V}
    (hC : C ∈ affineTrace F) : Sset F ⊆ C := by
  obtain ⟨hCmem, T, hT⟩ := hC
  subst hT
  exact Sset_subset_of_affine_mem hF hCmem

/-- **Remark 8.8.** The affine trace of a maximal convex filter depends only on `Mset F`
and the restriction of `sig F` to it. -/
theorem affineTrace_determined (hF : IsMaximal F) (hF' : IsMaximal F')
    (hM : Mset F = Mset F') (hsig : ∀ u ∈ Mset F, sig F u = sig F' u) :
    affineTrace F = affineTrace F' := by
  have hS : Sset F = Sset F' := by
    ext x
    simp only [mem_Sset_iff]
    constructor
    · intro hx u hu
      rw [← hsig u (hM ▸ hu), hx u (hM ▸ hu)]
    · intro hx u hu
      rw [hsig u hu, hx u (hM ▸ hu)]
  ext C
  simp only [mem_affineTrace_iff_of_mem]
  constructor
  · rintro ⟨hC, T, rfl⟩
    refine ⟨?_, T, rfl⟩
    rcases Set.eq_empty_or_nonempty ((T : Set V)) with hemp | hne
    · exact absurd (hemp ▸ hC) F.empty_not_mem
    · rw [mem_affineTrace_iff hF' hne, ← hS]
      exact Sset_subset_of_affine_mem hF hC
  · rintro ⟨hC, T, rfl⟩
    refine ⟨?_, T, rfl⟩
    rcases Set.eq_empty_or_nonempty ((T : Set V)) with hemp | hne
    · exact absurd (hemp ▸ hC) F'.empty_not_mem
    · rw [mem_affineTrace_iff hF hne, hS]
      exact Sset_subset_of_affine_mem hF' hC

/-! ### The converse: the trace determines `Mset` and `sig` on it -/

/-- A functional belongs to `Mset F` exactly when it is constant on the support. -/
theorem mem_Mset_iff_const_on_Sset (hF : IsMaximal F) {u : V →L[ℝ] ℝ} :
    u ∈ Mset F ↔ ∃ t : ℝ, Sset F ⊆ hyperplane u t := by
  constructor
  · intro hu
    exact ⟨sig F u, fun x hx => hx u hu⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, F.mem_of_superset (Sset_mem hF) (isClosed_hyperplane u t)
      (convex_hyperplane u t) ht⟩

/-- Two maximal convex filters with the same affine trace have the same support. -/
theorem Sset_eq_of_affineTrace_eq (hF : IsMaximal F) (hF' : IsMaximal F')
    (h : affineTrace F = affineTrace F') : Sset F = Sset F' :=
  subset_antisymm
    (Sset_subset_of_mem_affineTrace hF (h ▸ Sset_mem_affineTrace hF' : Sset F' ∈ affineTrace F))
    (Sset_subset_of_mem_affineTrace hF' (h ▸ Sset_mem_affineTrace hF))

/-- Two maximal convex filters with the same affine trace have the same `Mset`. -/
theorem Mset_eq_of_affineTrace_eq (hF : IsMaximal F) (hF' : IsMaximal F')
    (h : affineTrace F = affineTrace F') : Mset F = Mset F' := by
  have hS : Sset F = Sset F' := Sset_eq_of_affineTrace_eq hF hF' h
  ext u
  rw [mem_Mset_iff_const_on_Sset hF, mem_Mset_iff_const_on_Sset hF', hS]

/-- Two maximal convex filters with the same affine trace have the same support number on
`Mset`. -/
theorem sig_eq_of_affineTrace_eq (hF : IsMaximal F) (hF' : IsMaximal F')
    (h : affineTrace F = affineTrace F') : ∀ u ∈ Mset F, sig F u = sig F' u := by
  have hS : Sset F = Sset F' := Sset_eq_of_affineTrace_eq hF hF' h
  have hM : Mset F = Mset F' := Mset_eq_of_affineTrace_eq hF hF' h
  obtain ⟨a, ha⟩ := Aset_nonempty hF
  have haS : a ∈ Sset F := Aset_subset_Sset hF ha
  intro u hu
  rw [← ha u (Mset_subset_Nset hF hu), ← (hS ▸ haS : a ∈ Sset F') u (hM ▸ hu),
    ha u (Mset_subset_Nset hF hu)]

end ConvexFilter
