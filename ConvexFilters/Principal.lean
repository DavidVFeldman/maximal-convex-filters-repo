import ConvexFilters.Support

/-!
# Convex filters: principal filters

This file is Proposition 2.7. The *principal* convex filter at a point `p` is the family
of closed convex sets containing `p`; it is maximal, and a maximal convex filter on a
finite-dimensional space whose invariant `Nset` is the whole dual is principal.
-/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {F : ConvexFilter V}

namespace ConvexFilter

/-- The principal convex filter at `p`: all closed convex sets containing `p`. -/
def principal (p : V) : ConvexFilter V where
  carrier := {C : Set V | IsClosed C ∧ Convex ℝ C ∧ p ∈ C}
  isClosed_of_mem := fun _ hC => hC.1
  convex_of_mem := fun _ hC => hC.2.1
  univ_mem := ⟨isClosed_univ, convex_univ, Set.mem_univ p⟩
  empty_not_mem := by rintro ⟨-, -, h⟩; exact h
  inter_mem := fun _ _ hC hD =>
    ⟨hC.1.inter hD.1, hC.2.1.inter hD.2.1, ⟨hC.2.2, hD.2.2⟩⟩
  mem_of_superset := fun _ _ hC hDcl hDcv hCD => ⟨hDcl, hDcv, hCD hC.2.2⟩

omit [FiniteDimensional ℝ V] in
theorem mem_principal_iff {p : V} {C : Set V} :
    C ∈ (principal p).carrier ↔ (IsClosed C ∧ Convex ℝ C ∧ p ∈ C) := Iff.rfl

omit [FiniteDimensional ℝ V] in
theorem principal_isMaximal (p : V) : IsMaximal (principal p) := by
  rw [isMaximal_iff]
  intro C hCcl hCcv hCF
  have hp : p ∉ C := fun hp => hCF ⟨hCcl, hCcv, hp⟩
  refine ⟨{p}, ⟨isClosed_singleton, convex_singleton p, rfl⟩, ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
    not_and]
  rintro hx rfl
  exact hp hx

omit [FiniteDimensional ℝ V] in
theorem lev_principal (p : V) (u : V →L[ℝ] ℝ) : lev (principal p) u = Set.Ici (u p) := by
  ext t
  simp only [mem_lev_iff, mem_principal_iff, Set.mem_Ici]
  constructor
  · rintro ⟨-, -, h⟩
    exact h
  · intro h
    exact ⟨isClosed_halfLE u t, convex_halfLE u t, h⟩

omit [FiniteDimensional ℝ V] in
theorem sig_principal (p : V) (u : V →L[ℝ] ℝ) : sig (principal p) u = u p := by
  rw [sig, lev_principal]
  exact csInf_Ici

omit [FiniteDimensional ℝ V] in
theorem Nset_univ_of_principal (p : V) : Nset (principal p) = Set.univ := by
  refine Set.eq_univ_of_forall fun u => ⟨?_, ?_⟩
  · rw [lev_principal]
    exact Set.nonempty_iff_ne_empty.mp ⟨u p, Set.self_mem_Ici⟩
  · rw [lev_principal]
    exact Set.nonempty_iff_ne_empty.mp ⟨(-u) p, Set.self_mem_Ici⟩

/-- Proposition 2.7: if every functional has finite support number, the filter contains a
singleton. -/
theorem singleton_mem_of_Nset_univ (hF : IsMaximal F) (h : Nset F = Set.univ) :
    ∃ p : V, ({p} : Set V) ∈ F.carrier := by
  obtain ⟨a, ha⟩ := exists_point_of_Nset hF
  have ha' : ∀ u : V →L[ℝ] ℝ, u a = sig F u := fun u => ha u (h ▸ Set.mem_univ u)
  refine ⟨a, ?_⟩
  by_contra hsing
  obtain ⟨C, hC, hdisj⟩ :=
    (isMaximal_iff F).mp hF (isClosed_singleton (x := a)) (convex_singleton a) hsing
  have haC : a ∉ C := by
    intro haC
    have : a ∈ ({a} : Set V) ∩ C := ⟨rfl, haC⟩
    rw [hdisj] at this
    exact this
  obtain ⟨f, t, hlt, hgt⟩ :=
    geometric_hahn_banach_closed_point (F.convex_of_mem hC) (F.isClosed_of_mem hC) haC
  have hmem : halfLE f t ∈ F.carrier :=
    F.mem_of_superset hC (isClosed_halfLE f t) (convex_halfLE f t) fun x hx => (hlt x hx).le
  have hNf : f ∈ Nset F := h ▸ Set.mem_univ f
  have := sig_le_of_mem_lev hF hNf hmem
  rw [← ha' f] at this
  linarith

/-- Proposition 2.7: such a filter is the principal filter at that point. -/
theorem eq_principal_of_Nset_univ (hF : IsMaximal F) (h : Nset F = Set.univ) :
    ∃ p : V, F.carrier = (principal p).carrier := by
  obtain ⟨p, hp⟩ := singleton_mem_of_Nset_univ hF h
  refine ⟨p, Set.Subset.antisymm (fun C hC => ?_) (fun C hC => ?_)⟩
  · refine ⟨F.isClosed_of_mem hC, F.convex_of_mem hC, ?_⟩
    obtain ⟨x, hx₁, hx₂⟩ := nonempty_of_mem (F.inter_mem hp hC)
    rw [Set.mem_singleton_iff] at hx₁
    exact hx₁ ▸ hx₂
  · obtain ⟨hcl, hcv, hpC⟩ := hC
    exact F.mem_of_superset hp hcl hcv (Set.singleton_subset_iff.mpr hpC)

theorem Mset_univ_of_Nset_univ (hF : IsMaximal F) (h : Nset F = Set.univ) :
    Mset F = Set.univ := by
  obtain ⟨p, hp⟩ := singleton_mem_of_Nset_univ hF h
  refine Set.eq_univ_of_forall fun u => ⟨u p, ?_⟩
  refine F.mem_of_superset hp (isClosed_hyperplane u (u p)) (convex_hyperplane u (u p)) ?_
  rintro x rfl
  rfl

omit [FiniteDimensional ℝ V] in
theorem Aset_principal (p : V) : Aset (principal p) = ({p} : Set V) := by
  ext x
  simp only [mem_Aset_iff, Set.mem_singleton_iff]
  constructor
  · intro hx
    have hzero : ∀ f : V →L[ℝ] ℝ, f (x - p) = 0 := by
      intro f
      have := hx f (by rw [Nset_univ_of_principal]; exact Set.mem_univ f)
      rw [sig_principal] at this
      rw [map_sub, this, sub_self]
    exact sub_eq_zero.mp (NormedSpace.eq_zero_of_forall_dual_eq_zero ℝ hzero)
  · rintro rfl u _
    rw [sig_principal]

end ConvexFilter
