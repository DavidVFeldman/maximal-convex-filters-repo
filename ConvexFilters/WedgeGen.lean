import ConvexFilters.SpaceSep
import ConvexFilters.RemarkStrata

/-!
# The general wedge (Section 9, Lemmas 9.2, 9.3 and Theorem 9.5)

This file carries out Part A of WO-10: the general form, for a `d`-flat `A` inside a
`(d+1)`-flat `S` of a finite dimensional real normed space `V`, of the three results that
`ConvexFilters/SpaceCover.lean` and `ConvexFilters/SpaceSep.lean` proved for `d = 1`,
`n = 2`.

## Transport along an affine automorphism

`comapAffine` transports a convex filter along a continuous affine automorphism of `V`,
generalizing `comapEquiv`, which handles continuous *linear* automorphisms only.
`comapAffine_isMaximal` transports maximality.

## The setting

The paper's setting is an affine subspace `A`, an affine subspace `S ⊇ A` of one more
dimension, and a functional `u` with `A = S ∩ [u = c]`.  A maximal filter `G` of `C(A)`
with flat `A` is represented here by the maximal filter `FA` of `C(V)` it corresponds to
under Proposition 2.8: the datum is a maximal `FA` with `Aset FA = A` and `A ∈ FA`, and
then `E ∈ FA` is exactly the paper's `E ∩ A ∈ G`, because `A ∈ FA`.  This representation
makes Proposition 2.8 available without constructing the lattice `C(A)` separately; the
inverse assignment `G ↦ G^V` of the proposition is what the hypothesis `A ∈ FA.carrier`
records, and the compatibility of the invariants is the hypothesis `Aset FA = A`.

The filter `F₊` of stratum `(d, d+1)` is likewise described by its invariants: flat `A`
(`Aset Fplus = A`), support `S` (`S ∈ Fplus.carrier`), the escape data of `G`
(`Eset Fplus = Eset FA`), and approach from the side `u > c` (`halfLE u c ∉ Fplus`).

## Contents

* `homothety_fixes` (Lemma 9.2): a maximal filter is fixed by every homothety of positive
  ratio centred at a point of its flat;
* `mem_of_forall_inter_nonempty`: a closed convex set meeting every member of a maximal
  filter belongs to it;
* `exists_mem_of_cover_of_mem` (Lemma 9.1, relative form): a maximal filter containing a
  set `T` contains a member of every finite closed convex cover of `T`;
* `wedge_gen` (Lemma 9.3): the general wedge;
* `not_separated_gen`, `separated_gen` (Theorem 9.5);
* `not_separated_Fline_Ghyp_of_gen`: WO-09's Theorem 9.4, first clause, rederived as the
  instance `d = 1`, `n = 2`.
-/

namespace ConvexFilter

namespace Space

/-! ## Transport of a convex filter along a continuous affine automorphism -/

section AffineTransport

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The convex filter of sets whose preimage under a continuous affine automorphism `e`
belongs to `F`.  This generalizes `comapEquiv`, which is the case of a continuous linear
automorphism. -/
def comapAffine (e : V ≃ᵃ[ℝ] V) (he : Continuous e) (hes : Continuous e.symm)
    (F : ConvexFilter V) : ConvexFilter V where
  carrier := {C : Set V | (⇑e ⁻¹' C) ∈ F.carrier}
  isClosed_of_mem := by
    intro C hC
    have h : (⇑e.symm ⁻¹' (⇑e ⁻¹' C)) = C := by rw [Set.preimage_preimage]; simp
    rw [← h]
    exact (F.isClosed_of_mem hC).preimage hes
  convex_of_mem := by
    intro C hC
    have h : (⇑e.symm ⁻¹' (⇑e ⁻¹' C)) = C := by rw [Set.preimage_preimage]; simp
    rw [← h]
    exact (F.convex_of_mem hC).affine_preimage (e.symm : V →ᵃ[ℝ] V)
  univ_mem := by simpa using F.univ_mem
  empty_not_mem := by simpa using F.empty_not_mem
  inter_mem := by
    intro C D hC hD
    rw [Set.mem_setOf_eq, Set.preimage_inter]
    exact F.inter_mem hC hD
  mem_of_superset := by
    intro C D hC hDcl hDcv hCD
    exact F.mem_of_superset hC (hDcl.preimage he) (hDcv.affine_preimage (e : V →ᵃ[ℝ] V))
      (Set.preimage_mono hCD)

theorem mem_comapAffine_iff {e : V ≃ᵃ[ℝ] V} {he : Continuous e} {hes : Continuous e.symm}
    {F : ConvexFilter V} {C : Set V} :
    C ∈ (comapAffine e he hes F).carrier ↔ (⇑e ⁻¹' C) ∈ F.carrier := Iff.rfl

theorem comapAffine_isMaximal (e : V ≃ᵃ[ℝ] V) (he : Continuous e) (hes : Continuous e.symm)
    {F : ConvexFilter V} (hF : IsMaximal F) : IsMaximal (comapAffine e he hes F) := by
  rw [isMaximal_iff]
  intro C hCcl hCcv hC
  rw [mem_comapAffine_iff] at hC
  obtain ⟨D, hD, hdisj⟩ := (isMaximal_iff F).mp hF (hCcl.preimage he)
    (hCcv.affine_preimage (e : V →ᵃ[ℝ] V)) hC
  refine ⟨⇑e.symm ⁻¹' D, ?_, ?_⟩
  · show (⇑e ⁻¹' (⇑e.symm ⁻¹' D)) ∈ F.carrier
    have h : (⇑e ⁻¹' (⇑e.symm ⁻¹' D)) = D := by rw [Set.preimage_preimage]; simp
    rwa [h]
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_empty_iff_false, iff_false, not_and]
    intro hxC hxD
    have hmem : e.symm x ∈ (⇑e ⁻¹' C) ∩ D := ⟨by simpa using hxC, hxD⟩
    rw [hdisj] at hmem
    exact hmem

/-- The homothety of centre `p` and ratio `lam ≠ 0`, as an affine automorphism. -/
noncomputable def homothetyEquiv (p : V) (lam : ℝ) (hlam : lam ≠ 0) : V ≃ᵃ[ℝ] V :=
  AffineEquiv.homothetyUnitsMulHom p (Units.mk0 lam hlam)

theorem homothetyEquiv_apply (p : V) (lam : ℝ) (hlam : lam ≠ 0) (x : V) :
    homothetyEquiv p lam hlam x = lam • (x - p) + p := by
  simp [homothetyEquiv, AffineEquiv.homothetyUnitsMulHom, AffineMap.homothety_apply]

theorem continuous_homothetyEquiv (p : V) (lam : ℝ) (hlam : lam ≠ 0) :
    Continuous (homothetyEquiv p lam hlam) := by
  have h : ⇑(homothetyEquiv p lam hlam) = fun x : V => lam • (x - p) + p := by
    funext x; exact homothetyEquiv_apply p lam hlam x
  rw [h]
  fun_prop

theorem symm_homothetyEquiv_apply (p : V) (lam : ℝ) (hlam : lam ≠ 0) (x : V) :
    (homothetyEquiv p lam hlam).symm x = lam⁻¹ • (x - p) + p := by
  apply (AffineEquiv.injective (homothetyEquiv p lam hlam))
  rw [AffineEquiv.apply_symm_apply, homothetyEquiv_apply]
  simp [smul_smul, mul_inv_cancel₀ hlam]

theorem continuous_symm_homothetyEquiv (p : V) (lam : ℝ) (hlam : lam ≠ 0) :
    Continuous (homothetyEquiv p lam hlam).symm := by
  have h : ⇑(homothetyEquiv p lam hlam).symm = fun x : V => lam⁻¹ • (x - p) + p := by
    funext x; exact symm_homothetyEquiv_apply p lam hlam x
  rw [h]
  fun_prop

/-- The homothety of centre `p` and ratio `lam`, transported to half-spaces: the preimage
of `{f ≤ t}` is again a half-space of `f`. -/
theorem preimage_homothety_halfLE (p : V) {lam : ℝ} (hlam : 0 < lam) (f : V →L[ℝ] ℝ) (t : ℝ) :
    (⇑(homothetyEquiv p lam hlam.ne') ⁻¹' halfLE f t) = halfLE f ((t - f p) / lam + f p) := by
  ext x
  simp only [Set.mem_preimage, halfLE, Set.mem_setOf_eq, homothetyEquiv_apply, map_add, map_smul,
    map_sub, smul_eq_mul]
  rw [← sub_le_iff_le_add, le_div_iff₀ hlam]
  constructor <;> intro h <;> nlinarith

end AffineTransport

/-! ## Lemma 9.2: a maximal filter is fixed by the homotheties of its flat -/

section Homothety

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The level sets of a maximal filter are unchanged by a homothety of positive ratio
centred at a point of its flat. -/
theorem lev_comapAffine_homothety {F : ConvexFilter V} (hF : IsMaximal F) {p : V}
    (hp : p ∈ Aset F) {lam : ℝ} (hlam : 0 < lam) (f : V →L[ℝ] ℝ) :
    lev (comapAffine (homothetyEquiv p lam hlam.ne') (continuous_homothetyEquiv p lam hlam.ne')
      (continuous_symm_homothetyEquiv p lam hlam.ne') F) f = lev F f := by
  have hlt : ∀ s : ℝ, (f p < (s - f p) / lam + f p ↔ f p < s) := fun s => by
    rw [lt_add_iff_pos_left, div_pos_iff_of_pos_right hlam, sub_pos]
  have hle : ∀ s : ℝ, (f p ≤ (s - f p) / lam + f p ↔ f p ≤ s) := fun s => by
    rw [le_add_iff_nonneg_left, le_div_iff₀ hlam, zero_mul, sub_nonneg]
  ext t
  rw [mem_lev_iff, mem_comapAffine_iff, preimage_homothety_halfLE p hlam f t, ← mem_lev_iff]
  by_cases hfN : f ∈ Nset F
  · have hsig : sig F f = f p := sig_eq_of_mem_Aset hp hfN
    rcases lev_eq_of_mem_Nset hF hfN with h | h <;> rw [hsig] at h <;> rw [h]
    · simpa only [Set.mem_Ioi] using hlt t
    · simpa only [Set.mem_Ici] using hle t
  · rcases lev_shape (F := F) f with h | h | ⟨s, h⟩ | ⟨s, h⟩
    · rw [h]; simp
    · rw [h]; simp
    · exact absurd ((mem_Nset_iff hF f).mpr ⟨by rw [h]; exact (Set.nonempty_Ioi (a := s)).ne_empty,
        by rw [h]
           intro hcon
           have hmem : s ∈ Set.Ioi s := by rw [hcon]; exact Set.mem_univ s
           simp only [Set.mem_Ioi] at hmem
           exact lt_irrefl s hmem⟩) hfN
    · exact absurd ((mem_Nset_iff hF f).mpr ⟨by rw [h]; exact (Set.nonempty_Ici (a := s)).ne_empty,
        by rw [h]
           intro hcon
           have hmem : s - 1 ∈ Set.Ici s := by rw [hcon]; exact Set.mem_univ (s - 1)
           simp only [Set.mem_Ici] at hmem
           linarith⟩) hfN

/-- **Lemma 9.2.** A maximal convex filter is fixed by every homothety of positive ratio
whose centre lies on its flat. -/
theorem homothety_fixes {F : ConvexFilter V} (hF : IsMaximal F) {p : V} (hp : p ∈ Aset F)
    {lam : ℝ} (hlam : 0 < lam) :
    comapAffine (homothetyEquiv p lam hlam.ne') (continuous_homothetyEquiv p lam hlam.ne')
      (continuous_symm_homothetyEquiv p lam hlam.ne') F = F := by
  set Fh := comapAffine (homothetyEquiv p lam hlam.ne') (continuous_homothetyEquiv p lam hlam.ne')
    (continuous_symm_homothetyEquiv p lam hlam.ne') F with hFh
  have hlev : ∀ f : V →L[ℝ] ℝ, lev Fh f = lev F f := fun f =>
    lev_comapAffine_homothety hF hp hlam f
  have hFhmax : IsMaximal Fh :=
    comapAffine_isMaximal _ _ _ hF
  have hNset : Nset Fh = Nset F := by
    ext f
    simp only [Nset, Set.mem_setOf_eq, hlev]
  have hsig : ∀ f : V →L[ℝ] ℝ, sig Fh f = sig F f := fun f => by
    simp only [sig, hlev]
  have hAset : Aset Fh = Aset F := by
    ext x
    simp only [mem_Aset_iff, hNset, hsig]
  have hQset : Qset Fh = Qset F := by
    ext f
    simp only [Qset, Set.mem_setOf_eq, hlev]
  exact eq_of_carrier_eq (carrier_eq_of_Aset_Qset hFhmax hF hAset hQset)

end Homothety

/-! ## Two general principles -/

section Principles

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- A closed convex set meeting every member of a maximal convex filter belongs to it.

The hypothesis `Mset F = {0}` is the one under which the paper uses this principle (the
restriction of the filter to its support has vanishing `M`); it is kept, as required by
the conventions, although the maximality criterion `isMaximal_iff` gives the conclusion
without it. -/
theorem mem_of_forall_inter_nonempty {F : ConvexFilter V} (hF : IsMaximal F)
    (hM : Mset F = {0}) {C : Set V} (hcl : IsClosed C) (hcv : Convex ℝ C)
    (h : ∀ D ∈ F.carrier, (C ∩ D).Nonempty) : C ∈ F.carrier := by
  by_contra hC
  obtain ⟨D, hD, hdisj⟩ := (isMaximal_iff F).mp hF hcl hcv hC
  obtain ⟨x, hx⟩ := h D hD
  rw [hdisj] at hx
  exact hx

/-- **Lemma 9.1, relative form.** A maximal convex filter containing a set `T` contains a
member of every finite cover of `T` by closed convex sets.  For `T = Set.univ` this is
`exists_mem_of_cover`. -/
theorem exists_mem_of_cover_of_mem {s : Finset (Set V)}
    (hcl : ∀ E ∈ s, IsClosed E) (hcv : ∀ E ∈ s, Convex ℝ E)
    {F : ConvexFilter V} (hF : IsMaximal F) {T : Set V} (hT : T ∈ F.carrier)
    (hcover : T ⊆ ⋃ E ∈ s, E) :
    ∃ E ∈ s, E ∈ F.carrier := by
  classical
  by_contra hcon
  push_neg at hcon
  have havoid : ∀ E ∈ s, E ∩ avoid F E = ∅ := fun E hE =>
    inter_avoid_eq_empty ((isMaximal_iff F).mp hF (hcl E hE) (hcv E hE) (hcon E hE))
  obtain ⟨x, hxT, hx⟩ := nonempty_of_mem (F.inter_mem hT (iInter_avoid_mem F s))
  have hxcover : x ∈ (⋃ E ∈ s, E) := hcover hxT
  simp only [Set.mem_iUnion] at hxcover
  obtain ⟨E, hEs, hxE⟩ := hxcover
  have hxa : x ∈ avoid F E := by
    simp only [Set.mem_iInter] at hx
    exact hx E hEs
  have hmem : x ∈ E ∩ avoid F E := ⟨hxE, hxa⟩
  rw [havoid E hEs] at hmem
  exact hmem

end Principles

/-! ## The setting of Section 9 -/

section Wedge

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The direction of `A = S ∩ [u = c]` is the part of the direction of `S` killed by `u`. -/
theorem mem_direction_slice_iff {A S : AffineSubspace ℝ V} {u : V →L[ℝ] ℝ} {c : ℝ}
    (hAeq : (A : Set V) = (S : Set V) ∩ {x : V | u x = c}) (hne : ((A : Set V)).Nonempty)
    {v : V} : v ∈ A.direction ↔ (v ∈ S.direction ∧ u v = 0) := by
  obtain ⟨a, ha⟩ := hne
  have haA : a ∈ A := ha
  have haS : a ∈ S := by
    have := hAeq ▸ ha
    exact this.1
  have hac : u a = c := by
    have := hAeq ▸ ha
    exact this.2
  have hsub : v = (v + a) - a := by abel
  constructor
  · intro hv
    have hmem : v + a ∈ A := by
      have := AffineSubspace.vadd_mem_of_mem_direction hv haA
      simpa using this
    have hmem' : v + a ∈ (S : Set V) ∩ {x : V | u x = c} := by
      rw [← hAeq]; exact hmem
    refine ⟨?_, ?_⟩
    · rw [hsub]
      have := AffineSubspace.vsub_mem_direction hmem'.1 haS
      simpa using this
    · have h2 : u (v + a) = c := hmem'.2
      rw [map_add, hac] at h2
      linarith
  · rintro ⟨hvS, hv0⟩
    have hmem : v + a ∈ S := by
      have := AffineSubspace.vadd_mem_of_mem_direction hvS haS
      simpa using this
    have hmemA : v + a ∈ A := by
      have : v + a ∈ (S : Set V) ∩ {x : V | u x = c} := by
        refine ⟨hmem, ?_⟩
        show u (v + a) = c
        rw [map_add, hv0, hac, zero_add]
      rw [← hAeq] at this
      exact this
    rw [hsub]
    have := AffineSubspace.vsub_mem_direction hmemA haA
    simpa using this

/-- With `A = S ∩ [u = c]` of codimension one in `S`, the functional `u` does not vanish
on the direction of `S`. -/
theorem exists_mem_direction_apply_ne_zero {A S : AffineSubspace ℝ V} {u : V →L[ℝ] ℝ} {c : ℝ}
    (hAeq : (A : Set V) = (S : Set V) ∩ {x : V | u x = c}) (hne : ((A : Set V)).Nonempty)
    (hcodim : Module.finrank ℝ S.direction = Module.finrank ℝ A.direction + 1) :
    ∃ w ∈ S.direction, u w ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have heq : A.direction = S.direction := by
    refine le_antisymm ?_ ?_
    · intro v hv
      exact ((mem_direction_slice_iff hAeq hne).mp hv).1
    · intro v hv
      exact (mem_direction_slice_iff hAeq hne).mpr ⟨hv, hcon v hv⟩
  rw [heq] at hcodim
  omega

/-- A functional vanishing on the direction of `A` is a multiple of `u` on the direction
of `S`. -/
theorem exists_smul_eq_on_direction {A S : AffineSubspace ℝ V} {u : V →L[ℝ] ℝ} {c : ℝ}
    (hAeq : (A : Set V) = (S : Set V) ∩ {x : V | u x = c}) (hne : ((A : Set V)).Nonempty)
    (hcodim : Module.finrank ℝ S.direction = Module.finrank ℝ A.direction + 1)
    {f : V →L[ℝ] ℝ} (hf : ∀ v ∈ A.direction, f v = 0) :
    ∃ lam : ℝ, ∀ v ∈ S.direction, f v = lam * u v := by
  obtain ⟨w, hwS, hw⟩ := exists_mem_direction_apply_ne_zero hAeq hne hcodim
  refine ⟨f w / u w, fun v hv => ?_⟩
  set r : ℝ := u v / u w with hr
  have hvw : v - r • w ∈ A.direction := by
    refine (mem_direction_slice_iff hAeq hne).mpr ⟨S.direction.sub_mem hv (S.direction.smul_mem r hwS), ?_⟩
    rw [map_sub, map_smul, smul_eq_mul, hr, div_mul_cancel₀ _ hw, sub_self]
  have h0 : f (v - r • w) = 0 := hf _ hvw
  rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h0
  rw [h0, hr]
  field_simp

/-- The direction of the flat of a maximal filter, when that flat is the affine subspace
`A`, is the direction of `A`. -/
theorem mem_dirA_iff_mem_direction {F : ConvexFilter V} (hF : IsMaximal F)
    {A : AffineSubspace ℝ V} (hAset : Aset F = (A : Set V)) {v : V} :
    v ∈ dirA F ↔ v ∈ A.direction := by
  obtain ⟨a, ha⟩ := Aset_nonempty hF
  have haA : a ∈ A := by
    have : a ∈ (A : Set V) := by rw [← hAset]; exact ha
    exact this
  have hsub : v = (v + a) - a := by abel
  constructor
  · intro hv
    have hmem : v + a ∈ Aset F := by
      rw [mem_Aset_iff_sub_mem_dirA ha]
      simpa using hv
    rw [hAset] at hmem
    rw [hsub]
    have := AffineSubspace.vsub_mem_direction (hmem : v + a ∈ A) haA
    simpa using this
  · intro hv
    have hmem : v + a ∈ A := by
      have := AffineSubspace.vadd_mem_of_mem_direction hv haA
      simpa using this
    have hmem' : v + a ∈ Aset F := by rw [hAset]; exact hmem
    rw [mem_Aset_iff_sub_mem_dirA ha] at hmem'
    simpa using hmem'

/-- The functionals finite on a maximal filter with flat `A` are those vanishing on the
direction of `A`. -/
theorem mem_Nset_iff_direction {F : ConvexFilter V} (hF : IsMaximal F)
    {A : AffineSubspace ℝ V} (hAset : Aset F = (A : Set V)) {f : V →L[ℝ] ℝ} :
    f ∈ Nset F ↔ ∀ v ∈ A.direction, f v = 0 := by
  rw [Nset_eq_annihilator_dirA hF]
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h v hv
    exact h v ((mem_dirA_iff_mem_direction hF hAset).mpr hv)
  · intro h v hv
    exact h v ((mem_dirA_iff_mem_direction hF hAset).mp hv)

/-- In the setting of Section 9, the functional `u` cutting `A` out of `S` lies in the
positivity cone of a maximal filter with flat `A` which does not contain `[u ≤ c]`. -/
theorem mem_Qset_of_notMem_halfLE {A S : AffineSubspace ℝ V} {u : V →L[ℝ] ℝ} {c : ℝ}
    (hAeq : (A : Set V) = (S : Set V) ∩ {x : V | u x = c})
    {F : ConvexFilter V} (hF : IsMaximal F) (hAset : Aset F = (A : Set V))
    (hside : halfLE u c ∉ F.carrier) : u ∈ Nset F ∧ u ∈ Qset F := by
  have hAne : ((A : Set V)).Nonempty := by rw [← hAset]; exact Aset_nonempty hF
  obtain ⟨a, haA⟩ := hAne
  have hac : u a = c := by
    have := hAeq ▸ haA
    exact this.2
  have huN : u ∈ Nset F := by
    refine (mem_Nset_iff_direction hF hAset).mpr fun v hv => ?_
    exact ((mem_direction_slice_iff hAeq ⟨a, haA⟩).mp hv).2
  have hsig : sig F u = c := by
    have haF : a ∈ Aset F := by rw [hAset]; exact haA
    rw [sig_eq_of_mem_Aset haF huN, hac]
  have hlev : lev F u = Set.Ioi c := by
    rcases lev_eq_of_mem_Nset hF huN with h | h
    · rwa [hsig] at h
    · exfalso
      refine hside ?_
      have : c ∈ lev F u := by rw [h, hsig]; exact Set.self_mem_Ici
      exact this
  refine ⟨huN, ?_, ?_⟩
  · rw [hlev]
    intro hcon
    have : c ∈ Set.Ioi c := hcon ▸ Set.mem_univ c
    exact lt_irrefl c this
  · intro t ht
    rw [hlev] at ht ⊢
    exact ⟨(c + t) / 2, by simp only [Set.mem_Ioi] at *; linarith, by
      simp only [Set.mem_Ioi] at ht; linarith⟩

/-- **Lemma 9.3, the general wedge.** Let `A = S ∩ [u = c]` be a hyperplane of the affine
subspace `S`, let `FA` be a maximal filter with flat `A` containing `A` (the filter
attached to a maximal filter `G` of `C(A)` with flat `A` by Proposition 2.8), and let
`Fplus` be the maximal filter with flat `A`, support `S`, the escape data of `G`, and
approach from the side `u > c`.  A closed convex set `E` whose trace on `A` belongs to `G`
and which contains a point `q` of `S` with `u q > c` belongs to `Fplus`. -/
theorem wedge_gen {A S : AffineSubspace ℝ V} {u : V →L[ℝ] ℝ} {c : ℝ}
    (hAeq : (A : Set V) = (S : Set V) ∩ {x : V | u x = c})
    (hdA : 1 ≤ Module.finrank ℝ A.direction)
    (hcodim : Module.finrank ℝ S.direction = Module.finrank ℝ A.direction + 1)
    {FA Fplus : ConvexFilter V} (hFA : IsMaximal FA) (hFp : IsMaximal Fplus)
    (hAsetFA : Aset FA = (A : Set V)) (hAmem : (A : Set V) ∈ FA.carrier)
    (hAsetFp : Aset Fplus = (A : Set V)) (hSmem : (S : Set V) ∈ Fplus.carrier)
    (hEsc : Eset Fplus = Eset FA) (hside : halfLE u c ∉ Fplus.carrier)
    {E : Set V} (hcl : IsClosed E) (hcv : Convex ℝ E) (hEFA : E ∈ FA.carrier)
    {q : V} (hqE : q ∈ E) (hqS : q ∈ S) (hqu : c < u q) :
    E ∈ Fplus.carrier := by
  have hAne : ((A : Set V)).Nonempty := hAsetFA ▸ Aset_nonempty hFA
  obtain ⟨a, haA⟩ := hAne
  have haS : a ∈ (S : Set V) := by
    have := hAeq ▸ haA
    exact this.1
  have hac : u a = c := by
    have := hAeq ▸ haA
    exact this.2
  have hAS : (A : Set V) ⊆ (S : Set V) := by
    rw [hAeq]; exact Set.inter_subset_left
  have hN : Nset FA = Nset Fplus :=
    Nset_eq_of_Aset_eq hFA hFp (hAsetFA.trans hAsetFp.symm)
  have haFA : a ∈ Aset FA := by rw [hAsetFA]; exact haA
  have haFp : a ∈ Aset Fplus := by rw [hAsetFp]; exact haA
  obtain ⟨huN, huQ⟩ := mem_Qset_of_notMem_halfLE hAeq hFp hAsetFp hside
  -- the trace of `E` on `S`
  set C : Set V := E ∩ (S : Set V) with hC
  have hCcl : IsClosed C := hcl.inter S.closed_of_finiteDimensional
  have hCcv : Convex ℝ C := hcv.inter S.convex
  have hCS : C ⊆ (S : Set V) := Set.inter_subset_right
  have hCne : C.Nonempty := ⟨q, hqE, hqS⟩
  have hK : E ∩ (A : Set V) ∈ FA.carrier := FA.inter_mem hEFA hAmem
  have hKC : E ∩ (A : Set V) ⊆ C := fun x hx => ⟨hx.1, hAS hx.2⟩
  -- `C` meets every member of `Fplus`, hence belongs to it
  have hCmem : C ∈ Fplus.carrier := by
    by_contra hCnot
    obtain ⟨D, hD, hdisj⟩ := (isMaximal_iff Fplus).mp hFp hCcl hCcv hCnot
    set D' : Set V := D ∩ (S : Set V) with hD'def
    have hD'mem : D' ∈ Fplus.carrier := Fplus.inter_mem hD hSmem
    have hD'ne : D'.Nonempty := nonempty_of_mem hD'mem
    have hdisj' : C ∩ D' = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro x ⟨hxC, hxD, -⟩
      have : x ∈ C ∩ D := ⟨hxC, hxD⟩
      rw [hdisj] at this
      exact this
    obtain ⟨f, t, ⟨w, hwS, hfw⟩, hle, hge⟩ :=
      exists_separating_of_subset_affine hCcv (Fplus.convex_of_mem hD'mem) hCne hD'ne hdisj'
        hCS Set.inter_subset_right
    -- the two half-spaces produced by the separation
    have hhalfGE : halfGE f t ∈ Fplus.carrier :=
      Fplus.mem_of_superset hD'mem (isClosed_halfGE f t) (convex_halfGE f t)
        fun x hx => hge x hx
    have hhalfLE : halfLE f t ∈ FA.carrier :=
      FA.mem_of_superset hK (isClosed_halfLE f t) (convex_halfLE f t)
        fun x hx => hle x (hKC hx)
    have hlevneg : (-t) ∈ lev Fplus (-f) := by
      rw [mem_lev_neg_iff, neg_neg]
      exact hhalfGE
    -- in both cases `-f` lies in the positivity cone of `Fplus`, which is impossible
    have hQ : -f ∈ Qset Fplus := by
      by_cases hfN : f ∈ Nset FA
      · -- `f` is finite: it is a negative multiple of `u` modulo the annihilator of `S`
        have hfNp : f ∈ Nset Fplus := hN ▸ hfN
        have hsigFA : sig FA f = f a := sig_eq_of_mem_Aset haFA hfN
        have hsigFp : sig Fplus f = f a := sig_eq_of_mem_Aset haFp hfNp
        have h1 : f a ≤ t := by
          have := sig_le_of_mem_lev hFA hfN (hhalfLE : t ∈ lev FA f)
          rwa [hsigFA] at this
        have h2 : t ≤ f a := by
          have := le_sig_of_halfGE_mem hfNp hhalfGE
          rwa [hsigFp] at this
        have ht : t = f a := le_antisymm h2 h1
        obtain ⟨lam, hlam⟩ := exists_smul_eq_on_direction hAeq ⟨a, haA⟩ hcodim
          ((mem_Nset_iff_direction hFA hAsetFA).mp hfN)
        set m : V →L[ℝ] ℝ := f - lam • u with hm
        have hmzero : ∀ v ∈ S.direction, m v = 0 := by
          intro v hv
          show f v - lam * u v = 0
          rw [hlam v hv]
          ring
        have hmS : ∀ x ∈ (S : Set V), m x = m a := by
          intro x hx
          have hxa : x - a ∈ S.direction := by
            have := AffineSubspace.vsub_mem_direction (hx : x ∈ S) (haS : a ∈ S)
            simpa using this
          have := hmzero _ hxa
          rw [map_sub, sub_eq_zero] at this
          exact this
        have hmM : m ∈ Mset Fplus := by
          refine ⟨m a, Fplus.mem_of_superset hSmem (isClosed_hyperplane m (m a))
            (convex_hyperplane m (m a)) fun x hx => ?_⟩
          exact hmS x hx
        have hlamneg : lam < 0 := by
          have hqa : q - a ∈ S.direction := by
            have := AffineSubspace.vsub_mem_direction (hqS : q ∈ S) (haS : a ∈ S)
            simpa using this
          have hfq : f q - f a = lam * (u q - c) := by
            have := hlam _ hqa
            rw [map_sub, map_sub, hac] at this
            exact this
          have hfqle : f q ≤ t := hle q ⟨hqE, hqS⟩
          have hlamle : lam ≤ 0 := by nlinarith
          rcases lt_or_eq_of_le hlamle with h | h
          · exact h
          · exfalso
            apply hfw
            have := hlam w hwS
            rw [h] at this
            simpa using this
        have hdecomp : -f = (-lam) • u + (-m) := by
          rw [hm]
          ext x
          simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.add_apply,
            ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, smul_eq_mul]
          ring
        rw [hdecomp]
        exact Qset_add_Mset hFp (Qset_smul hFp (by linarith) huQ) (Mset_neg hmM)
      · -- `f` is infinite: `-f` escapes, and the escape data of the two filters agree
        have hlevne : lev FA f ≠ ∅ := by
          intro hempty
          have : t ∈ lev FA f := hhalfLE
          rw [hempty] at this
          exact this
        have hlevuniv : lev FA f = Set.univ := by
          by_contra hnu
          exact hfN ((mem_Nset_iff hFA f).mpr ⟨hlevne, hnu⟩)
        have hEsetFA : -f ∈ Eset FA := lev_empty_of_lev_univ hlevuniv
        have hEsetFp : -f ∈ Eset Fplus := by rw [hEsc]; exact hEsetFA
        exact Eset_subset_Qset hFp hEsetFp
    obtain ⟨hnfN, hlt⟩ := sig_lt_of_mem_Qset_of_mem_lev hFp hQ hlevneg
    -- `sig Fplus (-f) = -t`, contradicting strictness
    have hfNp : f ∈ Nset Fplus := by
      have := Nset_neg hnfN
      rwa [neg_neg] at this
    have hfNA : f ∈ Nset FA := by rw [hN]; exact hfNp
    have h1 : sig FA f ≤ t := sig_le_of_mem_lev hFA hfNA (hhalfLE : t ∈ lev FA f)
    have e1 : sig FA f = f a := sig_eq_of_mem_Aset haFA hfNA
    have e2 : sig Fplus f = f a := sig_eq_of_mem_Aset haFp hfNp
    rw [sig_neg hFp hfNp] at hlt
    linarith
  exact Fplus.mem_of_superset hCmem hcl hcv Set.inter_subset_left

/-- **Theorem 9.5, first clause.** The filter `FA` of stratum `(d, d)` and the filter
`Fplus` of stratum `(d, d+1)` approaching `A` inside `S` from the side `u > c` are not
separated. -/
theorem not_separated_gen {A S : AffineSubspace ℝ V} {u : V →L[ℝ] ℝ} {c : ℝ}
    (hAeq : (A : Set V) = (S : Set V) ∩ {x : V | u x = c})
    (hdA : 1 ≤ Module.finrank ℝ A.direction)
    (hcodim : Module.finrank ℝ S.direction = Module.finrank ℝ A.direction + 1)
    {FA Fplus : ConvexFilter V} (hFA : IsMaximal FA) (hFp : IsMaximal Fplus)
    (hAsetFA : Aset FA = (A : Set V)) (hAmem : (A : Set V) ∈ FA.carrier)
    (hAsetFp : Aset Fplus = (A : Set V)) (hSmem : (S : Set V) ∈ Fplus.carrier)
    (hEsc : Eset Fplus = Eset FA) (hside : halfLE u c ∉ Fplus.carrier) :
    ¬ Separated FA Fplus := by
  classical
  rintro ⟨s, hcl, hcv, hcover, hsep⟩
  have hAne : ((A : Set V)).Nonempty := by rw [← hAsetFA]; exact Aset_nonempty hFA
  have hAS : (A : Set V) ⊆ (S : Set V) := by rw [hAeq]; exact Set.inter_subset_left
  -- a direction of `S` on which `u` is positive
  obtain ⟨w, hwS, hw⟩ : ∃ w ∈ S.direction, 0 < u w := by
    obtain ⟨w₀, hw₀S, hw₀⟩ := exists_mem_direction_apply_ne_zero hAeq hAne hcodim
    rcases lt_or_gt_of_ne hw₀ with h | h
    · exact ⟨-w₀, S.direction.neg_mem hw₀S, by simpa using h⟩
    · exact ⟨w₀, hw₀S, h⟩
  -- the members of the cover whose trace on `A` does not lie in the filter of `A`
  set N : Finset (Set V) := s.filter (fun E => E ∉ FA.carrier) with hN
  have hclass1 : ∀ E ∈ s, E ∈ FA.carrier → ∀ x ∈ E, x ∈ (S : Set V) → u x ≤ c := by
    intro E hE hEFA x hxE hxS
    by_contra hcon
    push_neg at hcon
    exact hsep E hE ⟨hEFA, wedge_gen hAeq hdA hcodim hFA hFp hAsetFA hAmem hAsetFp hSmem
      hEsc hside (hcl E hE) (hcv E hE) hEFA hxE hxS hcon⟩
  have hcovN : {x : V | x ∈ (S : Set V) ∧ c < u x} ⊆ ⋃ E ∈ N, E := by
    rintro x ⟨hxS, hxu⟩
    have hxuniv : x ∈ (⋃ E ∈ s, E) := by rw [hcover]; exact Set.mem_univ x
    simp only [Set.mem_iUnion] at hxuniv
    obtain ⟨E, hEs, hxE⟩ := hxuniv
    have hnot : E ∉ FA.carrier := fun hEFA => absurd (hclass1 E hEs hEFA x hxE hxS) (not_le.mpr hxu)
    exact Set.mem_biUnion (Finset.mem_filter.mpr ⟨hEs, hnot⟩) hxE
  have hNcl : IsClosed (⋃ E ∈ N, E) := by
    refine Set.Finite.isClosed_biUnion N.finite_toSet fun E hE => ?_
    exact hcl E (Finset.mem_filter.mp hE).1
  -- the union of that class is closed, hence contains `A`
  have hAsub : (A : Set V) ⊆ ⋃ E ∈ N, E := by
    intro x hxA
    have hxS : x ∈ (S : Set V) := hAS hxA
    have hxc : u x = c := by
      have := hAeq ▸ hxA
      exact this.2
    refine hNcl.closure_subset (closure_mono hcovN ?_)
    have htend : Filter.Tendsto (fun n : ℕ => x + (1 / ((n : ℝ) + 1)) • w)
        Filter.atTop (nhds x) := by
      have h0 : Filter.Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1))) Filter.atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h1 := (h0.smul_const w).const_add x
      simpa using h1
    refine mem_closure_of_tendsto htend ?_
    filter_upwards with n
    have htpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    refine ⟨?_, ?_⟩
    · have := AffineSubspace.vadd_mem_of_mem_direction
        (S.direction.smul_mem (1 / ((n : ℝ) + 1)) hwS) (hxS : x ∈ S)
      have heq : (1 / ((n : ℝ) + 1)) • w +ᵥ x = x + (1 / ((n : ℝ) + 1)) • w := by
        simp [add_comm]
      rw [heq] at this
      exact this
    · show c < u (x + (1 / ((n : ℝ) + 1)) • w)
      rw [map_add, map_smul, smul_eq_mul, hxc]
      nlinarith
  obtain ⟨E, hEN, hEFA⟩ := exists_mem_of_cover_of_mem
    (fun E hE => hcl E (Finset.mem_filter.mp hE).1)
    (fun E hE => hcv E (Finset.mem_filter.mp hE).1) hFA hAmem hAsub
  exact (Finset.mem_filter.mp hEN).2 hEFA

/-- **Theorem 9.5, second clause.** The two filters of stratum `(d, d+1)` approaching `A`
inside `S` from opposite sides are separated, by the two closed half-spaces of `u`. -/
theorem separated_gen {u : V →L[ℝ] ℝ} {c : ℝ} {Fplus Fminus : ConvexFilter V}
    (hside : halfLE u c ∉ Fplus.carrier) (hside' : halfGE u c ∉ Fminus.carrier) :
    Separated Fplus Fminus := by
  classical
  refine ⟨{halfLE u c, halfGE u c}, ?_, ?_, ?_, ?_⟩
  · intro E hE
    rcases Finset.mem_insert.mp hE with rfl | hE
    · exact isClosed_halfLE u c
    · rw [Finset.mem_singleton.mp hE]; exact isClosed_halfGE u c
  · intro E hE
    rcases Finset.mem_insert.mp hE with rfl | hE
    · exact convex_halfLE u c
    · rw [Finset.mem_singleton.mp hE]; exact convex_halfGE u c
  · refine Set.eq_univ_of_forall fun p => ?_
    rcases le_total (u p) c with h | h
    · exact Set.mem_biUnion (Finset.mem_insert_self _ _) h
    · exact Set.mem_biUnion (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) h
  · intro E hE
    rcases Finset.mem_insert.mp hE with rfl | hE
    · rintro ⟨h, -⟩
      exact hside h
    · rw [Finset.mem_singleton.mp hE]
      rintro ⟨-, h⟩
      exact hside' h

end Wedge

/-! ## The case `d = 1`, `n = 2`: WO-09's theorem as an instance

The line filter `Fline` and the hyperbola filter `Ghyp` of `SpaceCover.lean` and
`SigCounterexample.lean` are the case `d = 1`, `n = 2` of the setting above, with `A` the
vertical axis, `S` the whole plane, `u = fstCLM` and `c = 0`.  This section reads off the
invariants of `Fline` (its level sets, `Nset`, `sig`, `Aset` and `Eset`) and derives
`Space.not_separated_Fline_Ghyp` of WO-09 again, as `not_separated_Fline_Ghyp_of_gen`, from
`not_separated_gen`.  The original proof in `SpaceSep.lean` is left untouched.
-/

section Plane

open SigCounterexample

theorem apply_of_mem_upRay {u : (ℝ × ℝ) →L[ℝ] ℝ} {k : ℕ} {p : ℝ × ℝ} (hp : p ∈ upRay k) :
    u p = u (0, 1) * p.2 := by
  rw [apply_eq u p, hp.2]
  ring

theorem lev_Fline_of_snd_pos {u : (ℝ × ℝ) →L[ℝ] ℝ} (hb : 0 < u (0, 1)) : lev Fline u = ∅ := by
  ext t
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hmem
  obtain ⟨k, hk⟩ :=
    (mem_Fline_iff (isClosed_halfLE u t) (convex_halfLE u t)).mp (mem_lev_iff.mp hmem)
  set y : ℝ := max (k : ℝ) (t / u (0, 1) + 1) with hy
  have hy1 : (k : ℝ) ≤ y := le_max_left _ _
  have hy2 : t / u (0, 1) + 1 ≤ y := le_max_right _ _
  have hp : ((0 : ℝ), y) ∈ upRay k := ⟨hy1, rfl⟩
  have hle : u ((0 : ℝ), y) ≤ t := hk hp
  rw [apply_of_mem_upRay hp] at hle
  have h3 : u (0, 1) * (t / u (0, 1) + 1) ≤ u (0, 1) * y := by nlinarith
  have h4 : u (0, 1) * (t / u (0, 1) + 1) = t + u (0, 1) := by field_simp
  simp only at hle
  linarith

theorem lev_Fline_of_snd_neg {u : (ℝ × ℝ) →L[ℝ] ℝ} (hb : u (0, 1) < 0) :
    lev Fline u = Set.univ := by
  ext t
  simp only [Set.mem_univ, iff_true]
  obtain ⟨k, hk⟩ := exists_nat_ge (t / u (0, 1))
  refine mem_lev_iff.mpr ((mem_Fline_iff (isClosed_halfLE u t) (convex_halfLE u t)).mpr ⟨k, ?_⟩)
  intro p hp
  have hne : u (0, 1) ≠ 0 := ne_of_lt hb
  have hkt : u (0, 1) * (k : ℝ) ≤ t := by
    have hcancel : t / u (0, 1) * u (0, 1) = t := div_mul_cancel₀ t hne
    nlinarith
  show u p ≤ t
  rw [apply_of_mem_upRay hp]
  nlinarith [hp.1]

theorem lev_Fline_of_snd_zero {u : (ℝ × ℝ) →L[ℝ] ℝ} (hb : u (0, 1) = 0) :
    lev Fline u = Set.Ici (0 : ℝ) := by
  ext t
  simp only [Set.mem_Ici]
  constructor
  · intro hmem
    obtain ⟨k, hk⟩ :=
      (mem_Fline_iff (isClosed_halfLE u t) (convex_halfLE u t)).mp (mem_lev_iff.mp hmem)
    have hp : ((0 : ℝ), (k : ℝ)) ∈ upRay k := ⟨le_rfl, rfl⟩
    have hle : u ((0 : ℝ), (k : ℝ)) ≤ t := hk hp
    rw [apply_of_mem_upRay hp, hb] at hle
    simpa using hle
  · intro ht
    refine mem_lev_iff.mpr ((mem_Fline_iff (isClosed_halfLE u t) (convex_halfLE u t)).mpr ⟨0, ?_⟩)
    intro p hp
    show u p ≤ t
    rw [apply_of_mem_upRay hp, hb]
    simpa using ht

theorem Nset_Fline : Nset Fline = {u : (ℝ × ℝ) →L[ℝ] ℝ | u (0, 1) = 0} := by
  ext u
  simp only [Set.mem_setOf_eq, Nset]
  constructor
  · rintro ⟨h1, h2⟩
    rcases lt_trichotomy (u (0, 1)) 0 with hb | hb | hb
    · exact absurd (lev_Fline_of_snd_pos (u := -u) (by rw [neg_apply_snd]; linarith)) h2
    · exact hb
    · exact absurd (lev_Fline_of_snd_pos hb) h1
  · intro hb
    refine ⟨?_, ?_⟩
    · rw [lev_Fline_of_snd_zero hb]
      exact (Set.nonempty_Ici (a := (0 : ℝ))).ne_empty
    · rw [lev_Fline_of_snd_zero (u := -u) (by simp [hb])]
      exact (Set.nonempty_Ici (a := (0 : ℝ))).ne_empty

theorem sig_Fline (u : (ℝ × ℝ) →L[ℝ] ℝ) : sig Fline u = 0 := by
  rcases lt_trichotomy (u (0, 1)) 0 with hb | hb | hb
  · exact sig_eq_zero_of_lev_eq_univ (lev_Fline_of_snd_neg hb)
  · exact sig_eq_zero_of_lev_eq_Ici_zero (lev_Fline_of_snd_zero hb)
  · exact sig_eq_zero_of_lev_eq_empty (lev_Fline_of_snd_pos hb)

theorem Aset_Fline : Aset Fline = {p : ℝ × ℝ | p.1 = 0} := by
  ext x
  simp only [mem_Aset_iff, Set.mem_setOf_eq]
  constructor
  · intro hx
    have hf : fstCLM ∈ Nset Fline := by
      rw [Nset_Fline]
      show fstCLM (0, 1) = 0
      simp
    have := hx fstCLM hf
    rw [sig_Fline] at this
    simpa using this
  · intro hx u hu
    rw [Nset_Fline] at hu
    have hb : u (0, 1) = 0 := hu
    rw [sig_Fline, apply_eq u x, hb, hx]
    ring

theorem Eset_Fline : Eset Fline = {u : (ℝ × ℝ) →L[ℝ] ℝ | 0 < u (0, 1)} := by
  ext u
  simp only [Eset, Set.mem_setOf_eq]
  constructor
  · intro h
    rcases lt_trichotomy (u (0, 1)) 0 with hb | hb | hb
    · rw [lev_Fline_of_snd_neg hb] at h
      exact absurd h (Set.univ_nonempty (α := ℝ)).ne_empty
    · rw [lev_Fline_of_snd_zero hb] at h
      exact absurd h (Set.nonempty_Ici (a := (0 : ℝ))).ne_empty
    · exact hb
  · exact lev_Fline_of_snd_pos

theorem Eset_Ghyp : Eset Ghyp = {u : (ℝ × ℝ) →L[ℝ] ℝ | 0 < u (0, 1)} := by
  ext u
  simp only [Eset, Set.mem_setOf_eq]
  constructor
  · intro h
    rcases lt_trichotomy (u (0, 1)) 0 with hb | hb | hb
    · rw [lev_Ghyp_of_snd_neg hb] at h
      exact absurd h (Set.univ_nonempty (α := ℝ)).ne_empty
    · rcases lt_or_ge 0 (u (1, 0)) with ha | ha
      · rw [lev_Ghyp_of_snd_zero_fst_pos hb ha] at h
        exact absurd h (Set.nonempty_Ioi (a := (0 : ℝ))).ne_empty
      · rw [lev_Ghyp_of_snd_zero_fst_nonpos hb ha] at h
        exact absurd h (Set.nonempty_Ici (a := (0 : ℝ))).ne_empty
    · exact hb
  · exact lev_Ghyp_of_snd_pos

/-- The vertical axis, as a linear subspace of the plane. -/
noncomputable def vertAxis : Submodule ℝ (ℝ × ℝ) :=
  LinearMap.ker (fstCLM : (ℝ × ℝ) →L[ℝ] ℝ).toLinearMap

theorem coe_vertAxis : (vertAxis : Set (ℝ × ℝ)) = {p : ℝ × ℝ | p.1 = 0} := by
  ext p
  simp [vertAxis, LinearMap.mem_ker]

theorem finrank_vertAxis : Module.finrank ℝ vertAxis = 1 := by
  have hr : LinearMap.range (fstCLM : (ℝ × ℝ) →L[ℝ] ℝ).toLinearMap = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact fun t => ⟨(t, 0), rfl⟩
  have h := LinearMap.finrank_range_add_finrank_ker (fstCLM : (ℝ × ℝ) →L[ℝ] ℝ).toLinearMap
  rw [hr] at h
  have h2 : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  have h3 : Module.finrank ℝ (⊤ : Submodule ℝ ℝ) = 1 := by simp
  rw [h2, h3] at h
  show Module.finrank ℝ (LinearMap.ker (fstCLM : (ℝ × ℝ) →L[ℝ] ℝ).toLinearMap) = 1
  omega

theorem isClosed_vertAxisSet : IsClosed {p : ℝ × ℝ | p.1 = 0} :=
  isClosed_eq continuous_fst continuous_const

theorem convex_vertAxisSet : Convex ℝ {p : ℝ × ℝ | p.1 = 0} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  simp [hx, hy]

theorem vertAxisSet_mem_Fline : {p : ℝ × ℝ | p.1 = 0} ∈ Fline.carrier := by
  refine (mem_Fline_iff isClosed_vertAxisSet convex_vertAxisSet).mpr ⟨0, ?_⟩
  intro p hp
  exact hp.2

theorem halfLE_fstCLM_eq_leftHalf : halfLE fstCLM 0 = leftHalf := rfl

theorem halfLE_fstCLM_notMem_Ghyp : halfLE fstCLM 0 ∉ Ghyp.carrier := by
  rw [halfLE_fstCLM_eq_leftHalf]
  exact leftHalf_notMem_Ghyp

/-- **WO-09's Theorem 9.4, first clause, rederived as the case `d = 1`, `n = 2` of
Theorem 9.5.** -/
theorem not_separated_Fline_Ghyp_of_gen : ¬ Separated Fline Ghyp := by
  have hAeq : ((vertAxis.toAffineSubspace : AffineSubspace ℝ (ℝ × ℝ)) : Set (ℝ × ℝ))
      = ((⊤ : AffineSubspace ℝ (ℝ × ℝ)) : Set (ℝ × ℝ)) ∩ {x : ℝ × ℝ | fstCLM x = 0} := by
    rw [AffineSubspace.top_coe, Set.univ_inter]
    rw [show ((vertAxis.toAffineSubspace : AffineSubspace ℝ (ℝ × ℝ)) : Set (ℝ × ℝ))
      = (vertAxis : Set (ℝ × ℝ)) from rfl, coe_vertAxis]
    ext p
    simp
  have hdir : (vertAxis.toAffineSubspace : AffineSubspace ℝ (ℝ × ℝ)).direction = vertAxis :=
    Submodule.toAffineSubspace_direction vertAxis
  have hdA : 1 ≤ Module.finrank ℝ (vertAxis.toAffineSubspace : AffineSubspace ℝ (ℝ × ℝ)).direction := by
    rw [hdir, finrank_vertAxis]
  have hcodim : Module.finrank ℝ (⊤ : AffineSubspace ℝ (ℝ × ℝ)).direction
      = Module.finrank ℝ (vertAxis.toAffineSubspace : AffineSubspace ℝ (ℝ × ℝ)).direction + 1 := by
    rw [hdir, finrank_vertAxis, AffineSubspace.direction_top]
    simp
  have hcoe : ((vertAxis.toAffineSubspace : AffineSubspace ℝ (ℝ × ℝ)) : Set (ℝ × ℝ))
      = {p : ℝ × ℝ | p.1 = 0} := coe_vertAxis
  refine not_separated_gen hAeq hdA hcodim Fline_isMaximal Ghyp_isMaximal ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hcoe]; exact Aset_Fline
  · rw [hcoe]; exact vertAxisSet_mem_Fline
  · rw [hcoe]; exact Aset_Ghyp
  · rw [AffineSubspace.top_coe]; exact Ghyp.univ_mem
  · rw [Eset_Ghyp, Eset_Fline]
  · exact halfLE_fstCLM_notMem_Ghyp

end Plane

end Space

end ConvexFilter
