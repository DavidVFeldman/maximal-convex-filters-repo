import ConvexFilters.Flat

/-!
# Convex filters: the support `S`

This file is Proposition 2.6. For a maximal convex filter `F` on a finite-dimensional
real normed space, the set

`Sset F = {x | ∀ u ∈ Mset F, u x = sig F u}`

is a member of `F` containing the flat `Aset F`, and it is contained in every affine
subspace belonging to `F`.
-/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {F : ConvexFilter V}

namespace ConvexFilter

/-- The support of `F`: the set of points at which every functional of `Mset F` takes its
support value. -/
def Sset (F : ConvexFilter V) : Set V := {x : V | ∀ u ∈ Mset F, u x = sig F u}

omit [FiniteDimensional ℝ V] in
theorem mem_Sset_iff {x : V} : x ∈ Sset F ↔ ∀ u ∈ Mset F, u x = sig F u := Iff.rfl

omit [FiniteDimensional ℝ V] in
theorem sig_zero : sig F (0 : V →L[ℝ] ℝ) = 0 := by
  rw [sig, lev_zero]
  exact csInf_Ici

omit [FiniteDimensional ℝ V] in
/-- The level hyperplane of a functional of `Mset F` belongs to `F`. -/
theorem hyperplane_sig_mem {u : V →L[ℝ] ℝ} (hu : u ∈ Mset F) :
    hyperplane u (sig F u) ∈ F.carrier := by
  obtain ⟨t, ht⟩ := hu
  rw [sig_eq_of_hyperplane_mem ht]
  exact ht

omit [FiniteDimensional ℝ V] in
/-- A finite intersection of level hyperplanes of functionals of `Mset F` belongs to `F`. -/
theorem hyperplane_biInter_mem (s : Finset (V →L[ℝ] ℝ)) (hs : ∀ u ∈ s, u ∈ Mset F) :
    (⋂ u ∈ (s : Set (V →L[ℝ] ℝ)), hyperplane u (sig F u)) ∈ F.carrier := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using F.univ_mem
  | insert a s ha ih =>
      have hsplit : (⋂ u ∈ ((insert a s : Finset (V →L[ℝ] ℝ)) : Set (V →L[ℝ] ℝ)),
            hyperplane u (sig F u))
          = hyperplane a (sig F a) ∩ ⋂ u ∈ (s : Set (V →L[ℝ] ℝ)), hyperplane u (sig F u) := by
        rw [Finset.coe_insert, Set.biInter_insert]
      rw [hsplit]
      exact F.inter_mem (hyperplane_sig_mem (hs a (Finset.mem_insert_self a s)))
        (ih fun u hu => hs u (Finset.mem_insert_of_mem hu))

omit [FiniteDimensional ℝ V] in
theorem Aset_subset_Sset (hF : IsMaximal F) : Aset F ⊆ Sset F :=
  fun _ hx u hu => hx u (Mset_subset_Nset hF hu)

/-- Proposition 2.6: the support of a maximal convex filter belongs to the filter. -/
theorem Sset_mem (hF : IsMaximal F) : Sset F ∈ F.carrier := by
  classical
  -- `Mset F` is a finitely generated submodule of the dual.
  obtain ⟨s, hs⟩ : (MsubmoduleOf F hF).FG := IsNoetherian.noetherian _
  have hsM : ∀ u ∈ s, u ∈ Mset F := by
    intro u hu
    have : u ∈ MsubmoduleOf F hF := by
      rw [← hs]
      exact Submodule.subset_span hu
    exact this
  have hSeq : Sset F = ⋂ u ∈ (s : Set (V →L[ℝ] ℝ)), hyperplane u (sig F u) := by
    ext x
    simp only [Set.mem_iInter, mem_Sset_iff, hyperplane, Set.mem_setOf_eq]
    constructor
    · intro hx u hu
      exact hx u (hsM u hu)
    · intro hx v hv
      have hvspan : v ∈ Submodule.span ℝ (s : Set (V →L[ℝ] ℝ)) := by
        rw [hs]; exact hv
      induction hvspan using Submodule.span_induction with
      | mem w hw => exact hx w hw
      | zero => simpa using sig_zero.symm
      | add w y hw hy hwv hyv =>
          have hwM : w ∈ Mset F := by
            have h' : w ∈ MsubmoduleOf F hF := hs ▸ hw
            exact h'
          have hyM : y ∈ Mset F := by
            have h' : y ∈ MsubmoduleOf F hF := hs ▸ hy
            exact h'
          have := sig_add hF (Mset_subset_Nset hF hwM) (Mset_subset_Nset hF hyM)
          simp only [ContinuousLinearMap.add_apply]
          rw [hwv hwM, hyv hyM, this]
      | smul c w hw hwv =>
          have hwM : w ∈ Mset F := by
            have h' : w ∈ MsubmoduleOf F hF := hs ▸ hw
            exact h'
          have := sig_smul hF (Mset_subset_Nset hF hwM) c
          simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
          rw [hwv hwM, this]
  rw [hSeq]
  exact hyperplane_biInter_mem s hsM

/-- Proposition 2.6: the support is contained in every affine subspace belonging to `F`. -/
theorem Sset_subset_of_affine_mem (hF : IsMaximal F) {T : AffineSubspace ℝ V}
    (hT : (T : Set V) ∈ F.carrier) : Sset F ⊆ (T : Set V) := by
  intro x hx
  by_contra hxT
  obtain ⟨p, hp⟩ := nonempty_of_mem hT
  have hpT : p ∈ T := hp
  -- `x - p` is not in the direction of `T`
  have hdir : x - p ∉ T.direction := by
    intro hmem
    apply hxT
    have := AffineSubspace.vadd_mem_of_mem_direction hmem hpT
    simpa using this
  -- a linear functional vanishing on the direction and not at `x - p`
  obtain ⟨f, hfx, hfker⟩ := Submodule.exists_le_ker_of_notMem hdir
  set u : V →L[ℝ] ℝ := LinearMap.toContinuousLinearMap f
  have huf : ∀ y : V, u y = f y := fun y => rfl
  -- `T` is contained in the level hyperplane of `u` through `p`
  have hTsub : (T : Set V) ⊆ hyperplane u (u p) := by
    intro y hy
    have hyd : y - p ∈ T.direction := by
      have := AffineSubspace.vsub_mem_direction (s := T) hy hpT
      simpa using this
    have : f (y - p) = 0 := hfker hyd
    have hy' : f y - f p = 0 := by rwa [map_sub] at this
    show u y = u p
    rw [huf, huf]
    linarith
  have hhyp : hyperplane u (u p) ∈ F.carrier :=
    F.mem_of_superset hT (isClosed_hyperplane _ _) (convex_hyperplane _ _) hTsub
  have huM : u ∈ Mset F := ⟨u p, hhyp⟩
  have hsig : sig F u = u p := sig_eq_of_hyperplane_mem hhyp
  have hval : u x = sig F u := hx u huM
  rw [hsig, huf, huf] at hval
  exact hfx (by rw [map_sub, hval, sub_self])

end ConvexFilter
