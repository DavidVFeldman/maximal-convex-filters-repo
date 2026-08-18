import ConvexFilters.SeparationRel
import ConvexFilters.Support

/-!
# Convex filters: the support as an affine subspace, and uniqueness

Part B packages the support `Sset F` of a maximal convex filter as an affine subspace
`SsetAff F hF`, whose direction is the annihilator of `Mset F`.

Part C is Theorem 4.2 of the paper: a maximal convex filter is determined by its
invariants. See the discussion at `carrier_eq_of_sig_Qset` below: the statement of the
work order, which asks only for `sig F = sig F'` and `Qset F = Qset F'`, is **false** as
literally formalized, because the real-valued `sig` cannot distinguish an *infinite*
support value from a finite one which happens to be `0` (`sInf ∅ = sInf Set.univ = 0` in
`ℝ`). The theorem proved here adds the hypothesis `Nset F = Nset F'`, which is exactly the
information the paper's extended-real-valued `σ` carries and the real-valued `sig` drops.
Part D shows that the hypothesis is automatic in the form in which the classification uses
it, so the mathematical objective of the campaign — `carrier_eq_of_Aset_Qset` — is
delivered exactly as specified.
-/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {F : ConvexFilter V}

namespace ConvexFilter

/-! ### Part B: the support as an affine subspace -/

/-- The annihilator of `Mset F`, the prospective direction of the support. -/
def dirS (F : ConvexFilter V) : Submodule ℝ V where
  carrier := {v : V | ∀ u ∈ Mset F, u v = 0}
  add_mem' := fun hx hy u hu => by simp [hx u hu, hy u hu]
  zero_mem' := fun u _ => by simp
  smul_mem' := fun c _ hx u hu => by simp [hx u hu]

omit [FiniteDimensional ℝ V] in
theorem mem_dirS_iff {v : V} : v ∈ dirS F ↔ ∀ u ∈ Mset F, u v = 0 := Iff.rfl

/-- The support of a maximal convex filter, packaged as an affine subspace: the coset of
`dirS F` through any point of the flat `Aset F`. -/
noncomputable def SsetAff (F : ConvexFilter V) (hF : IsMaximal F) : AffineSubspace ℝ V :=
  AffineSubspace.mk' (Aset_nonempty hF).choose (dirS F)

theorem coe_SsetAff (hF : IsMaximal F) :
    ((SsetAff F hF : AffineSubspace ℝ V) : Set V) = Sset F := by
  have ha : (Aset_nonempty hF).choose ∈ Aset F := (Aset_nonempty hF).choose_spec
  have haS : (Aset_nonempty hF).choose ∈ Sset F := Aset_subset_Sset hF ha
  ext x
  constructor
  · intro hx u hu
    have hmem : x - (Aset_nonempty hF).choose ∈ dirS F := hx
    have := hmem u hu
    rw [map_sub, sub_eq_zero] at this
    rw [this]
    exact haS u hu
  · intro hx
    show x - (Aset_nonempty hF).choose ∈ dirS F
    intro u hu
    rw [map_sub, hx u hu, haS u hu, sub_self]

theorem direction_SsetAff (hF : IsMaximal F) :
    (SsetAff F hF).direction = {v : V | ∀ u ∈ Mset F, u v = 0} := by
  rw [SsetAff, AffineSubspace.direction_mk']
  rfl

omit [FiniteDimensional ℝ V] in
/-- A functional of `Mset F` is constant on the support of `F`. -/
theorem const_on_Sset_of_mem_Mset {u : V →L[ℝ] ℝ} (hu : u ∈ Mset F)
    {x y : V} (hx : x ∈ Sset F) (hy : y ∈ Sset F) : u x = u y := by
  rw [hx u hu, hy u hu]

/-! ### Auxiliary facts about level sets and half-spaces -/

omit [FiniteDimensional ℝ V] in
/-- If the half-space `{u ≥ t}` belongs to `F`, then no smaller level belongs to
`lev F u`. -/
theorem notMem_lev_of_halfGE_mem {u : V →L[ℝ] ℝ} {t s : ℝ}
    (ht : halfGE u t ∈ F.carrier) (hs : s < t) : s ∉ lev F u := by
  intro hmem
  have hinter : halfLE u s ∩ halfGE u t ∈ F.carrier := F.inter_mem hmem ht
  rw [disjoint_halfLE_halfGE hs u] at hinter
  exact F.empty_not_mem hinter

omit [FiniteDimensional ℝ V] in
/-- If the half-space `{u ≥ t}` belongs to `F` and `u ∈ Nset F`, then `t ≤ sig F u`.
This is the step recorded in WO-01 §5.4. -/
theorem le_sig_of_halfGE_mem {u : V →L[ℝ] ℝ} {t : ℝ}
    (hu : u ∈ Nset F) (ht : halfGE u t ∈ F.carrier) : t ≤ sig F u :=
  le_csInf (lev_nonempty_of_mem_Nset hu) fun _ hs =>
    not_lt.mp fun hlt => notMem_lev_of_halfGE_mem ht hlt hs

omit [FiniteDimensional ℝ V] in
/-- A functional of `Qset F` whose level set is nonempty lies in `Nset F` and has its
support number strictly below any of its levels. -/
theorem sig_lt_of_mem_Qset_of_mem_lev {u : V →L[ℝ] ℝ} (hF : IsMaximal F)
    (hu : u ∈ Qset F) {t : ℝ} (ht : t ∈ lev F u) : u ∈ Nset F ∧ sig F u < t := by
  have hne : lev F u ≠ ∅ := fun h => by rw [h] at ht; exact ht
  have hN : u ∈ Nset F := (mem_Nset_iff hF u).mpr ⟨hne, hu.1⟩
  obtain ⟨t', ht', hlt⟩ := hu.2 t ht
  exact ⟨hN, lt_of_le_of_lt (sig_le_of_mem_lev hF hN ht') hlt⟩

/-! ### Part C: uniqueness -/

omit [FiniteDimensional ℝ V] in
/-- The key step of Theorem 4.2: a functional separating a member of `F` from a member of
`F'`, when the two filters share their invariants, lies in `Mset F`. -/
theorem mem_Mset_of_halfLE_halfGE {F F' : ConvexFilter V}
    (hF : IsMaximal F) (hF' : IsMaximal F')
    (hN : Nset F = Nset F') (hsig : ∀ u : V →L[ℝ] ℝ, sig F u = sig F' u)
    (hQ : Qset F = Qset F') {u : V →L[ℝ] ℝ} {t : ℝ}
    (hle : halfLE u t ∈ F.carrier) (hge : halfGE u t ∈ F'.carrier) : u ∈ Mset F := by
  rcases mem_Qset_or_neg_or_Mset hF u with h | h | h
  · -- `u ∈ Qset F`: the support number of `u` is `< t` for `F` and `≥ t` for `F'`
    exfalso
    obtain ⟨huN, hlt⟩ := sig_lt_of_mem_Qset_of_mem_lev hF h hle
    have huN' : u ∈ Nset F' := hN ▸ huN
    have hge' : t ≤ sig F' u := le_sig_of_halfGE_mem huN' hge
    have := hsig u
    linarith
  · -- `-u ∈ Qset F`: the same argument with the roles of the two filters exchanged
    exfalso
    have hgeF' : (-t) ∈ lev F' (-u) := by
      rw [mem_lev_neg_iff, neg_neg]
      exact hge
    have h' : -u ∈ Qset F' := hQ ▸ h
    obtain ⟨huN', hlt⟩ := sig_lt_of_mem_Qset_of_mem_lev hF' h' hgeF'
    have huN : -u ∈ Nset F := hN ▸ huN'
    have hleF : halfGE (-u) (-t) ∈ F.carrier := by
      rw [halfGE_neg]
      exact hle
    have hge' : (-t) ≤ sig F (-u) := le_sig_of_halfGE_mem huN hleF
    have := hsig (-u)
    linarith
  · exact h

/-- **Theorem 4.2 (uniqueness).** A maximal convex filter is determined by the invariants
`Nset`, `sig` and `Qset`.

This is the statement of §5 of the work order with the extra hypothesis
`hN : Nset F = Nset F'`. That hypothesis is *not* redundant: see the counterexample
recorded in `reports/WO-03/REPORT.md`. In the paper the support function `σ` takes values
in the extended reals, so `σ_F = σ_{F'}` already records `Nset F = Nset F'` (the set where
`σ` is finite in both directions); the real-valued `sig` of `Defs.lean` returns the junk
value `sInf ∅ = 0` when the level set is empty and `sInf Set.univ = 0` when it is all of
`ℝ`, and therefore cannot distinguish an infinite support value from a finite one equal to
`0`. Part D (`carrier_eq_of_Aset_Qset`) shows that the extra hypothesis is automatic when
the invariants are recorded in the paper's form, by the flat `Aset F` rather than by
`sig`. -/
theorem carrier_eq_of_sig_Qset {F F' : ConvexFilter V}
    (hF : IsMaximal F) (hF' : IsMaximal F')
    (hN : Nset F = Nset F')
    (hsig : ∀ u : V →L[ℝ] ℝ, sig F u = sig F' u)
    (hQ : Qset F = Qset F') : F.carrier = F'.carrier := by
  -- the shared invariants determine `Mset` and hence the support
  have hM : Mset F = Mset F' := by
    rw [Mset_eq_compl_Qset hF, Mset_eq_compl_Qset hF', hQ]
  have hS : Sset F = Sset F' := by
    ext x
    simp only [mem_Sset_iff]
    constructor
    · intro hx u hu
      rw [← hsig u]
      exact hx u (hM ▸ hu)
    · intro hx u hu
      rw [hsig u]
      exact hx u (hM ▸ hu)
  have hSF : Sset F ∈ F.carrier := Sset_mem hF
  have hSF' : Sset F ∈ F'.carrier := hS ▸ Sset_mem hF'
  have hsub : F.carrier ⊆ F'.carrier := by
    intro C hC
    by_contra hCF'
    obtain ⟨C', hC', hdisj⟩ :=
      (isMaximal_iff F').mp hF' (F.isClosed_of_mem hC) (F.convex_of_mem hC) hCF'
    -- cut both members down to the common support
    set C₀ : Set V := C ∩ Sset F with hC₀def
    set C₀' : Set V := C' ∩ Sset F with hC₀'def
    have hC₀F : C₀ ∈ F.carrier := F.inter_mem hC hSF
    have hC₀'F' : C₀' ∈ F'.carrier := F'.inter_mem hC' hSF'
    have hC₀ne : C₀.Nonempty := nonempty_of_mem hC₀F
    have hC₀'ne : C₀'.Nonempty := nonempty_of_mem hC₀'F'
    have hC₀cv : Convex ℝ C₀ := F.convex_of_mem hC₀F
    have hC₀'cv : Convex ℝ C₀' := F'.convex_of_mem hC₀'F'
    have hdisj₀ : C₀ ∩ C₀' = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro x ⟨⟨hxC, -⟩, ⟨hxC', -⟩⟩
      have : x ∈ C ∩ C' := ⟨hxC, hxC'⟩
      rw [hdisj] at this
      exact this
    have hC₀T : C₀ ⊆ ((SsetAff F hF : AffineSubspace ℝ V) : Set V) := by
      rw [coe_SsetAff hF]
      exact Set.inter_subset_right
    have hC₀'T : C₀' ⊆ ((SsetAff F hF : AffineSubspace ℝ V) : Set V) := by
      rw [coe_SsetAff hF]
      exact Set.inter_subset_right
    -- relative separation inside the support
    obtain ⟨u, t, ⟨v, hv, hvu⟩, hle, hge⟩ :=
      exists_separating_of_subset_affine hC₀cv hC₀'cv hC₀ne hC₀'ne hdisj₀ hC₀T hC₀'T
    have hhalfLE : halfLE u t ∈ F.carrier :=
      F.mem_of_superset hC₀F (isClosed_halfLE u t) (convex_halfLE u t) hle
    have hhalfGE : halfGE u t ∈ F'.carrier :=
      F'.mem_of_superset hC₀'F' (isClosed_halfGE u t) (convex_halfGE u t) hge
    have huM : u ∈ Mset F :=
      mem_Mset_of_halfLE_halfGE hF hF' hN hsig hQ hhalfLE hhalfGE
    -- but every functional of `Mset F` kills the direction of the support
    have hv' : v ∈ (((SsetAff F hF).direction : Submodule ℝ V) : Set V) := hv
    rw [direction_SsetAff hF] at hv'
    exact hvu (hv' u huM)
  exact Set.Subset.antisymm hsub (hF F' hsub)

end ConvexFilter
