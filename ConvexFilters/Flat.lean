import ConvexFilters.Invariants

/-!
# Convex filters: the flat `A`

For a maximal convex filter `F` on a finite-dimensional real normed space, the support
number `sig F` is linear on the subspace `Nset F` of the dual, hence is evaluation at a
point (`exists_point_of_Nset`). The set of all points realizing it,

`Aset F = {x | ∀ u ∈ Nset F, u x = sig F u}`,

is then a nonempty closed convex flat, a coset of the subspace

`dirA F = {v | ∀ u ∈ Nset F, u v = 0}`.
-/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {F : ConvexFilter V}

namespace ConvexFilter

/-- In finite dimensions the support number of a maximal convex filter is evaluation at a
point on the subspace `Nset F`. -/
theorem exists_point_of_Nset (hF : IsMaximal F) :
    ∃ a : V, ∀ u ∈ Nset F, u a = sig F u := by
  -- `sig F` is a linear functional on the submodule `Nset F` of the dual.
  let phi : (NsubmoduleOf F hF) →ₗ[ℝ] ℝ :=
    { toFun := fun u => sig F (u : V →L[ℝ] ℝ)
      map_add' := fun u v => sig_add hF u.2 v.2
      map_smul' := fun c u => by simpa using sig_smul hF u.2 c }
  -- Extend it to the whole dual.
  obtain ⟨Phi, hPhi⟩ := phi.exists_extend
  -- Read the extension as an element of the double dual of `V`, using that in finite
  -- dimensions every linear functional is continuous.
  let e : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V →L[ℝ] ℝ) := LinearMap.toContinuousLinearMap
  let Psi : Module.Dual ℝ (Module.Dual ℝ V) := Phi ∘ₗ (e : (V →ₗ[ℝ] ℝ) →ₗ[ℝ] (V →L[ℝ] ℝ))
  refine ⟨(Module.evalEquiv ℝ V).symm Psi, fun u hu => ?_⟩
  set a : V := (Module.evalEquiv ℝ V).symm Psi
  have heval : Module.evalEquiv ℝ V a = Psi := (Module.evalEquiv ℝ V).apply_symm_apply Psi
  have hkey : Psi (e.symm u) = (e.symm u) a := by rw [← heval]; rfl
  have hcoe : (e.symm u) a = u a := by
    simp [e, LinearMap.toContinuousLinearMap]
  have hPsi : Psi (e.symm u) = Phi u := by
    show Phi (e (e.symm u)) = Phi u
    rw [e.apply_symm_apply]
  have hval : Phi u = sig F u := LinearMap.congr_fun hPhi (⟨u, hu⟩ : NsubmoduleOf F hF)
  rw [← hcoe, ← hkey, hPsi, hval]

/-- The flat attached to `F`: the set of points at which every functional of `Nset F`
takes its support value. -/
def Aset (F : ConvexFilter V) : Set V := {x : V | ∀ u ∈ Nset F, u x = sig F u}

/-- The direction of the flat `Aset F`: the annihilator of `Nset F`. -/
def dirA (F : ConvexFilter V) : Submodule ℝ V where
  carrier := {v : V | ∀ u ∈ Nset F, u v = 0}
  add_mem' := fun hx hy u hu => by simp [hx u hu, hy u hu]
  zero_mem' := fun u _ => by simp
  smul_mem' := fun c _ hx u hu => by simp [hx u hu]

omit [FiniteDimensional ℝ V] in
theorem coe_dirA : ((dirA F : Submodule ℝ V) : Set V) = {v : V | ∀ u ∈ Nset F, u v = 0} := rfl

omit [FiniteDimensional ℝ V] in
theorem mem_dirA_iff {v : V} : v ∈ dirA F ↔ ∀ u ∈ Nset F, u v = 0 := Iff.rfl

omit [FiniteDimensional ℝ V] in
theorem mem_Aset_iff {x : V} : x ∈ Aset F ↔ ∀ u ∈ Nset F, u x = sig F u := Iff.rfl

theorem Aset_nonempty (hF : IsMaximal F) : (Aset F).Nonempty := by
  obtain ⟨a, ha⟩ := exists_point_of_Nset hF
  exact ⟨a, ha⟩

omit [FiniteDimensional ℝ V] in
theorem mem_Aset_iff_sub_mem_dirA {a : V} (ha : a ∈ Aset F) (x : V) :
    x ∈ Aset F ↔ x - a ∈ dirA F := by
  constructor
  · intro hx u hu
    rw [map_sub, hx u hu, ha u hu, sub_self]
  · intro hx u hu
    have h := hx u hu
    rw [map_sub, ha u hu, sub_eq_zero] at h
    exact h

omit [FiniteDimensional ℝ V] in
theorem convex_Aset : Convex ℝ (Aset F) := by
  intro x hx y hy a b ha hb hab u hu
  have hx' : u x = sig F u := hx u hu
  have hy' : u y = sig F u := hy u hu
  have : u (a • x + b • y) = a * u x + b * u y := by simp
  rw [this, hx', hy', ← add_mul, hab, one_mul]

omit [FiniteDimensional ℝ V] in
theorem Aset_eq_iInter : Aset F = ⋂ u ∈ Nset F, hyperplane u (sig F u) := by
  ext x
  simp only [Aset, Set.mem_setOf_eq, Set.mem_iInter, hyperplane]

omit [FiniteDimensional ℝ V] in
theorem isClosed_Aset : IsClosed (Aset F) := by
  rw [Aset_eq_iInter]
  exact isClosed_iInter fun u => isClosed_iInter fun _ => isClosed_hyperplane u _

end ConvexFilter
