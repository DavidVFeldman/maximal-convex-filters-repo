import ConvexFilters.Uniqueness

/-!
# Convex filters: the annihilator, and injectivity of the invariants in the paper's form

The classification records the flat `Aset F` rather than the support number `sig F`. This
file shows that the two carry the same information: `Nset F` is the annihilator of the
direction `dirA F` of the flat (`Nset_eq_annihilator_dirA`), so a maximal convex filter is
determined by the pair `(Aset F, Qset F)` (`carrier_eq_of_Aset_Qset`).

Search record for the double-annihilator step. `Submodule.dualAnnihilator`,
`Submodule.dualCoannihilator` and the finite-dimensional
`Subspace.dualCoannihilator_dualAnnihilator_eq` family were examined first. They are
stated for `Module.Dual R M = M →ₗ[R] R`, while the development works throughout with
`V →L[ℝ] ℝ`, so using them requires transporting the submodule `NsubmoduleOf F hF` along
the identification `(V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V →L[ℝ] ℝ)` used in `Flat.lean`, transporting
`dirA F` as well, and then unfolding the coannihilator back into the pointwise form of
`dirA`. The direct argument used below is shorter and needs no transport: a functional
outside the subspace `NsubmoduleOf F hF` of the dual is detached from it by a functional
on the dual (`Submodule.exists_le_ker_of_notMem`), which in finite dimensions is
evaluation at a vector `v` (`Module.evalEquiv`, exactly as in `exists_point_of_Nset`); that
`v` lies in `dirA F` and is not killed, which is the contrapositive of the inclusion
wanted.
-/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {F : ConvexFilter V}

namespace ConvexFilter

/-- `Nset F` is exactly the annihilator of the direction of the flat `Aset F`. -/
theorem Nset_eq_annihilator_dirA (hF : IsMaximal F) :
    Nset F = {u : V →L[ℝ] ℝ | ∀ v ∈ dirA F, u v = 0} := by
  ext u
  constructor
  · intro hu v hv
    exact hv u hu
  · intro hu
    by_contra hnot
    -- `u` lies outside the subspace `Nset F` of the dual, so some functional on the dual
    -- detaches it from that subspace
    have hnotN : u ∉ NsubmoduleOf F hF := hnot
    obtain ⟨f, hfu, hfker⟩ := Submodule.exists_le_ker_of_notMem hnotN
    -- in finite dimensions such a functional is evaluation at a vector
    let e : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V →L[ℝ] ℝ) := LinearMap.toContinuousLinearMap
    let Psi : Module.Dual ℝ (Module.Dual ℝ V) := f ∘ₗ (e : (V →ₗ[ℝ] ℝ) →ₗ[ℝ] (V →L[ℝ] ℝ))
    set v : V := (Module.evalEquiv ℝ V).symm Psi with hvdef
    have heval : Module.evalEquiv ℝ V v = Psi := (Module.evalEquiv ℝ V).apply_symm_apply Psi
    have hrepr : ∀ w : V →L[ℝ] ℝ, f w = w v := by
      intro w
      have hkey : Psi (e.symm w) = (e.symm w) v := by rw [← heval]; rfl
      have hPsi : Psi (e.symm w) = f w := by
        show f (e (e.symm w)) = f w
        rw [e.apply_symm_apply]
      have hcoe : (e.symm w) v = w v := by
        simp [e, LinearMap.toContinuousLinearMap]
      rw [← hPsi, hkey, hcoe]
    have hvdir : v ∈ dirA F := by
      intro w hw
      have hwN : w ∈ NsubmoduleOf F hF := hw
      have : f w = 0 := hfker hwN
      rw [hrepr w] at this
      exact this
    exact hfu (by rw [hrepr u]; exact hu v hvdir)

omit [FiniteDimensional ℝ V] in
/-- On `Nset F`, the support number is evaluation at any point of the flat. -/
theorem sig_eq_of_mem_Aset {a : V} (ha : a ∈ Aset F) {u : V →L[ℝ] ℝ} (hu : u ∈ Nset F) :
    sig F u = u a := (ha u hu).symm

omit [FiniteDimensional ℝ V] in
/-- Off `Nset F` the support number is the junk value `0`: the level set is either empty
or all of `ℝ`, and `sInf` of either is `0`. -/
theorem sig_eq_zero_of_notMem_Nset (hF : IsMaximal F) {u : V →L[ℝ] ℝ} (hu : u ∉ Nset F) :
    sig F u = 0 := by
  by_cases hE : lev F u = ∅
  · rw [sig, hE, Real.sInf_empty]
  · -- then the level set of `-u` is empty, so that of `u` is everything
    have hE' : lev F (-u) = ∅ := by
      by_contra hE'
      exact hu ⟨hE, hE'⟩
    have huniv : lev F u = Set.univ := by
      have := lev_univ_of_lev_empty hF hE'
      rwa [neg_neg] at this
    rw [sig, huniv, Real.sInf_univ]

/-- The flat determines the direction of the flat. -/
theorem dirA_eq_of_Aset_eq {F F' : ConvexFilter V}
    (hF : IsMaximal F) (hA : Aset F = Aset F') : dirA F = dirA F' := by
  obtain ⟨a, ha⟩ := Aset_nonempty hF
  have ha' : a ∈ Aset F' := hA ▸ ha
  ext v
  constructor
  · intro hv
    have hmem : a + v ∈ Aset F := by
      rw [mem_Aset_iff_sub_mem_dirA ha]
      simpa using hv
    have hmem' : a + v ∈ Aset F' := hA ▸ hmem
    rw [mem_Aset_iff_sub_mem_dirA ha'] at hmem'
    simpa using hmem'
  · intro hv
    have hmem' : a + v ∈ Aset F' := by
      rw [mem_Aset_iff_sub_mem_dirA ha']
      simpa using hv
    have hmem : a + v ∈ Aset F := hA ▸ hmem'
    rw [mem_Aset_iff_sub_mem_dirA ha] at hmem
    simpa using hmem

/-- Two maximal convex filters with the same flat have the same `Nset`. -/
theorem Nset_eq_of_Aset_eq {F F' : ConvexFilter V}
    (hF : IsMaximal F) (hF' : IsMaximal F') (hA : Aset F = Aset F') : Nset F = Nset F' := by
  rw [Nset_eq_annihilator_dirA hF, Nset_eq_annihilator_dirA hF', dirA_eq_of_Aset_eq hF hA]

/-- The invariants of the classification determine the support number. -/
theorem sig_eq_of_Aset_Qset {F F' : ConvexFilter V}
    (hF : IsMaximal F) (hF' : IsMaximal F')
    (hA : Aset F = Aset F') (hQ : Qset F = Qset F') :
    ∀ u : V →L[ℝ] ℝ, sig F u = sig F' u := by
  have hN : Nset F = Nset F' := Nset_eq_of_Aset_eq hF hF' hA
  obtain ⟨a, ha⟩ := Aset_nonempty hF
  have ha' : a ∈ Aset F' := hA ▸ ha
  intro u
  by_cases hu : u ∈ Nset F
  · rw [sig_eq_of_mem_Aset ha hu, sig_eq_of_mem_Aset ha' (hN ▸ hu)]
  · have hu' : u ∉ Nset F' := fun h => hu (hN ▸ h)
    rw [sig_eq_zero_of_notMem_Nset hF hu, sig_eq_zero_of_notMem_Nset hF' hu']

/-- **Injectivity of the invariants, in the paper's form.** A maximal convex filter is
determined by its flat `Aset` and its positivity cone `Qset`. -/
theorem carrier_eq_of_Aset_Qset {F F' : ConvexFilter V}
    (hF : IsMaximal F) (hF' : IsMaximal F')
    (hA : Aset F = Aset F') (hQ : Qset F = Qset F') : F.carrier = F'.carrier :=
  carrier_eq_of_sig_Qset hF hF' (Nset_eq_of_Aset_eq hF hF' hA)
    (sig_eq_of_Aset_Qset hF hF' hA hQ) hQ

end ConvexFilter
