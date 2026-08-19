import ConvexFilters.Fibres

/-!
# The boundary of the Hausdorff quotient in the plane (WO-12)

`hM(ℝ²)` is the maximal Hausdorff quotient `T2Quotient (MaxFilter (ℝ × ℝ))` of the space of
maximal convex filters of the plane.  This file studies its *boundary*: the complement of
the image of the plane, that image being the range of `p ↦ T2Quotient.mk (principal p)`.

## Part A — the boundary is closed

`denseRange_prin` is Proposition 9.2: the principal filters are dense.  `isOpen_range_prinQ`
and its contract form `isOpen_range_principal` show that the image of the plane in the
quotient is open, and `isCompact_boundary` that the boundary is therefore compact.  The
argument does not go through a general statement about dense locally compact subspaces:
the image of the plane is shown to be open directly, by exhibiting around each of its points
an open set of the quotient cut out by the continuous coordinates `levQ u`, `u` a
functional, on which every class is principal.

## Part B — the parametrization

For a non-principal maximal filter `F` of the plane, `dirOf F` is the primary escape
direction — the unique unit vector `v` such that `levVal F u = ⊤` for every functional `u`
with `u v > 0` (`exists_escape_direction`, `escape_dir_unique`) — and `offOf F` is the
extended support value at the normal `normalCLM (dirOf F)`.  Both are defined from `levVal`
alone, so `boundaryMap = (dirOf, offOf)` descends to the Hausdorff quotient
(`boundaryMap_eq_of_levVal_eq`).

* `levVal_eq_of_dirOf_offOf_eq`: the pair `(dirOf, offOf)` determines `levVal` on the
  non-principal filters, whence `boundaryMap_injective_on_quotient`;
* `boundaryMap_surjective`: every pair of a unit vector and an extended real is attained.
  The witnesses are transports: `vlineFilter c` for a finite offset, the parabola filter
  `Gpar` and its reflection for the offsets `∓∞`, carried to the direction `v` along the
  linear automorphism `dirEquiv v`.

## Parts B and C are false where they assert continuity

`not_secondCountableTopology_boundarySet`: the boundary is **not** second countable.  For
each direction of line the classes whose extended support value at the corresponding normal
functional is finite form a nonempty open subset of the boundary, and these sets are
pairwise disjoint over uncountably many directions (`finLocus_disjoint_of_ne`).  Hence

* `not_boundary_homeomorph`: the boundary is not homeomorphic to `S¹ × [-∞, +∞]`, which
  refutes Part C of the work order;
* `not_continuousOn_boundaryMap`: `boundaryMap` is not continuous on the non-principal
  locus, which refutes the continuity clause of Part B.  It is nonetheless a bijection onto
  `S¹ × [-∞, +∞]` after descent, by the injectivity and surjectivity above.
-/

open Module

namespace ConvexFilter

namespace Space

/-! ## The principal filters as points of the space and of the quotient -/

section Principal

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The principal filter at `p`, as a point of `MaxFilter V`. -/
def prin (p : V) : MaxFilter V := ⟨principal p, principal_isMaximal p⟩

omit [FiniteDimensional ℝ V] in
theorem levVal_prin (p : V) (u : V →L[ℝ] ℝ) : levVal (prin p).1 u = ((u p : ℝ) : EReal) := by
  have hu : u ∈ Nset (principal p) := by rw [Nset_univ_of_principal]; trivial
  rw [prin, levVal_of_mem_Nset (principal_isMaximal p) hu, sig_principal]

omit [FiniteDimensional ℝ V] in
/-- The map `p ↦ F_p` is continuous: the preimage of the subbasic open set `(Vset C)ᶜ` is
the complement of `C`. -/
theorem continuous_prin : Continuous (prin : V → MaxFilter V) := by
  refine continuous_generateFrom_iff.mpr ?_
  rintro s ⟨C, hcl, hcv, rfl⟩
  have hpre : (prin : V → MaxFilter V) ⁻¹' (Vset C)ᶜ = Cᶜ := by
    ext p
    show C ∉ (principal p).carrier ↔ p ∉ C
    rw [mem_principal_iff]
    exact ⟨fun h hp => h ⟨hcl, hcv, hp⟩, fun h hmem => h hmem.2.2⟩
  rw [hpre]
  exact hcl.isOpen_compl

/-- **Proposition 9.2, density.** The principal filters are dense in `MaxFilter V`: a
basic open set of the subbasis topology that avoided every principal filter would exhibit
a finite cover of `V` by closed convex sets no member of which lies in a given maximal
filter, contradicting the covering criterion `exists_mem_of_cover` (Lemma 9.1). -/
theorem denseRange_prin : DenseRange (prin : V → MaxFilter V) := by
  classical
  refine (TopologicalSpace.isTopologicalBasis_of_subbasis
    (topology_eq_generateFrom (V := V))).dense_iff.mpr ?_
  rintro o ⟨f, ⟨hfin, hsub⟩, rfl⟩ ⟨F, hF⟩
  have hex : ∀ s ∈ f, ∃ C : Set V, IsClosed C ∧ Convex ℝ C ∧ s = (Vset C)ᶜ := fun s hs =>
    hsub hs
  choose! C hCcl hCcv hCeq using hex
  by_cases hp : ∃ p : V, ∀ s ∈ f, p ∉ C s
  · obtain ⟨p, hp⟩ := hp
    refine ⟨prin p, ?_, Set.mem_range_self p⟩
    intro s hs
    rw [hCeq s hs]
    intro hmem
    exact hp s hs (mem_principal_iff.mp hmem).2.2
  · exfalso
    push_neg at hp
    set T : Finset (Set V) := hfin.toFinset.image C with hT
    have hcover : (⋃ E ∈ T, E) = Set.univ := by
      refine Set.eq_univ_of_forall fun p => ?_
      obtain ⟨s, hs, hps⟩ := hp p
      exact Set.mem_biUnion (Finset.mem_image_of_mem C (hfin.mem_toFinset.mpr hs)) hps
    have hclT : ∀ E ∈ T, IsClosed E := by
      intro E hE
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hE
      exact hCcl s (hfin.mem_toFinset.mp hs)
    have hcvT : ∀ E ∈ T, Convex ℝ E := by
      intro E hE
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hE
      exact hCcv s (hfin.mem_toFinset.mp hs)
    obtain ⟨E, hET, hEF⟩ := exists_mem_of_cover hclT hcvT hcover F.2
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hET
    have hsf : s ∈ f := hfin.mem_toFinset.mp hs
    have hFs : F ∈ s := hF s hsf
    rw [hCeq s hsf] at hFs
    exact hFs hEF

end Principal

/-! ## The invariant on the quotient -/

section Quot

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The image of a principal filter in the maximal Hausdorff quotient. -/
def prinQ (p : V) : T2Quotient (MaxFilter V) := T2Quotient.mk (prin p)

omit [FiniteDimensional ℝ V] in
theorem continuous_prinQ : Continuous (prinQ : V → T2Quotient (MaxFilter V)) :=
  (T2Quotient.continuous_mk _).comp continuous_prin

theorem denseRange_prinQ : DenseRange (prinQ : V → T2Quotient (MaxFilter V)) :=
  DenseRange.comp (T2Quotient.surjective_mk _).denseRange denseRange_prin
    (T2Quotient.continuous_mk _)

/-- The extended support value at `u`, as a continuous function on the maximal Hausdorff
quotient: it descends because it is continuous into the Hausdorff space `EReal`. -/
noncomputable def levQ (u : V →L[ℝ] ℝ) : T2Quotient (MaxFilter V) → EReal :=
  T2Quotient.lift (sigma_continuous u)

omit [FiniteDimensional ℝ V] in
theorem continuous_levQ (u : V →L[ℝ] ℝ) : Continuous (levQ u) :=
  T2Quotient.continuous_lift _

omit [FiniteDimensional ℝ V] in
theorem levQ_mk (u : V →L[ℝ] ℝ) (F : MaxFilter V) : levQ u (T2Quotient.mk F) = levVal F.1 u :=
  T2Quotient.lift_mk _ _

omit [FiniteDimensional ℝ V] in
theorem levQ_prinQ (u : V →L[ℝ] ℝ) (p : V) : levQ u (prinQ p) = ((u p : ℝ) : EReal) := by
  rw [prinQ, levQ_mk, levVal_prin]

instance : CompactSpace (MaxFilter V) := ⟨isCompact_univ⟩

instance : CompactSpace (T2Quotient (MaxFilter V)) := by
  constructor
  rw [← Set.image_univ_of_surjective (T2Quotient.surjective_mk (MaxFilter V))]
  exact isCompact_univ.image (T2Quotient.continuous_mk _)

end Quot

/-! ## Part A — the image of the plane is open and the boundary is compact -/

section PartA

/-- The first coordinate, as a continuous linear functional on the plane. -/
noncomputable abbrev fstCLM : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ

/-- The second coordinate, as a continuous linear functional on the plane. -/
noncomputable abbrev sndCLM : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ

/-- **Part A.** The image of the plane in the maximal Hausdorff quotient is open.

The two coordinate functionals give a continuous map
`x ↦ (levQ fst x, levQ snd x) : hM(ℝ²) → EReal × EReal` restricting to the identity on the
image of the plane.  The preimage `W` of an open square around `p` is therefore an open
neighbourhood of the class of `F_p` meeting the image of the plane inside the compact set
`K` of classes of principal filters at points of the closed square.  `K` is closed,
because the quotient is Hausdorff, and the image of the plane is dense
(`denseRange_prinQ`), so `W ⊆ closure (W ∩ image) ⊆ K ⊆ image`. -/
theorem isOpen_range_prinQ :
    IsOpen (Set.range (prinQ : (ℝ × ℝ) → T2Quotient (MaxFilter (ℝ × ℝ)))) := by
  refine isOpen_iff_forall_mem_open.mpr ?_
  rintro x ⟨p, rfl⟩
  set W : Set (T2Quotient (MaxFilter (ℝ × ℝ))) :=
    (levQ fstCLM) ⁻¹' (Set.Ioo ((p.1 - 1 : ℝ) : EReal) ((p.1 + 1 : ℝ) : EReal)) ∩
      (levQ sndCLM) ⁻¹' (Set.Ioo ((p.2 - 1 : ℝ) : EReal) ((p.2 + 1 : ℝ) : EReal)) with hW
  have hWopen : IsOpen W :=
    ((continuous_levQ _).isOpen_preimage _ isOpen_Ioo).inter
      ((continuous_levQ _).isOpen_preimage _ isOpen_Ioo)
  set box : Set (ℝ × ℝ) := Set.Icc (p.1 - 1) (p.1 + 1) ×ˢ Set.Icc (p.2 - 1) (p.2 + 1) with hbox
  have hboxcompact : IsCompact box := (isCompact_Icc).prod (isCompact_Icc)
  set K : Set (T2Quotient (MaxFilter (ℝ × ℝ))) := prinQ '' box with hK
  have hKcompact : IsCompact K := hboxcompact.image continuous_prinQ
  have hKclosed : IsClosed K := hKcompact.isClosed
  have hpW : prinQ p ∈ W := by
    constructor <;>
      simp only [Set.mem_preimage, levQ_prinQ, Set.mem_Ioo, EReal.coe_lt_coe_iff] <;>
      constructor <;> simp
  have hsub : W ∩ Set.range prinQ ⊆ K := by
    rintro y ⟨hyW, q, rfl⟩
    obtain ⟨h1, h2⟩ := hyW
    simp only [Set.mem_preimage, levQ_prinQ, Set.mem_Ioo, EReal.coe_lt_coe_iff] at h1 h2
    exact Set.mem_image_of_mem _ ⟨⟨h1.1.le, h1.2.le⟩, ⟨h2.1.le, h2.2.le⟩⟩
  have hWsub : W ⊆ Set.range prinQ := by
    refine (Dense.open_subset_closure_inter denseRange_prinQ hWopen).trans ?_
    refine (closure_mono hsub).trans ?_
    rw [hKclosed.closure_eq, hK]
    exact Set.image_subset_range _ _
  exact ⟨W, hWsub, hWopen, hpW⟩

/-- **Part A, contract form.** The image of the plane in the maximal Hausdorff quotient of
the space of maximal convex filters is open. -/
theorem isOpen_range_principal :
    IsOpen (Set.range (fun p : ℝ × ℝ =>
      T2Quotient.mk (X := MaxFilter (ℝ × ℝ)) ⟨principal p, principal_isMaximal p⟩)) :=
  isOpen_range_prinQ

/-- **Part A, contract form.** The boundary — the complement of the image of the plane in
the maximal Hausdorff quotient — is compact: it is closed in a compact space. -/
theorem isCompact_boundary :
    IsCompact ((Set.range (fun p : ℝ × ℝ =>
      T2Quotient.mk (X := MaxFilter (ℝ × ℝ)) ⟨principal p, principal_isMaximal p⟩))ᶜ) :=
  (isOpen_range_principal.isClosed_compl).isCompact

end PartA

/-! ## Lines in every direction: transport of the line filter -/

section Lines

open SigCounterexample

/-- The functional `(x, y) ↦ a x + b y` of the plane. -/
noncomputable def coCLM (a b : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ := a • fstCLM + b • sndCLM

@[simp] theorem coCLM_apply (a b : ℝ) (p : ℝ × ℝ) : coCLM a b p = a * p.1 + b * p.2 := rfl

/-- Transport of the extended support value along a linear automorphism. -/
theorem levVal_comapEquiv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (e : V ≃L[ℝ] V) (F : ConvexFilter V) (u : V →L[ℝ] ℝ) :
    levVal (comapEquiv e F) u = levVal F (u.comp (e : V →L[ℝ] V)) := by
  refine levVal_congr_of_lev_eq ?_
  ext t
  rfl

/-! ### The extended support value of the line filter

`Fline` is the filter of the upward tail-rays of the vertical axis: the filter of stratum
`(1, 1)` over the line `x = 0`, escaping upwards.  Its extended support value at `u` is
governed by the sign of `u (0, 1)`. -/

theorem lev_Fline_eq_empty {u : (ℝ × ℝ) →L[ℝ] ℝ} (h : 0 < u (0, 1)) : lev Fline u = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro t ht
  obtain ⟨k, hk⟩ := (mem_Fline_iff (isClosed_halfLE u t) (convex_halfLE u t)).mp ht
  obtain ⟨y, hy⟩ := exists_gt (max (k : ℝ) (t / u (0, 1)))
  have hyk : (k : ℝ) ≤ y := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hy)
  have hmem : ((0 : ℝ), y) ∈ upRay k := ⟨hyk, rfl⟩
  have hle : u ((0 : ℝ), y) ≤ t := hk hmem
  rw [apply_eq u ((0 : ℝ), y)] at hle
  have hyt : t / u (0, 1) < y := lt_of_le_of_lt (le_max_right _ _) hy
  rw [div_lt_iff₀ h] at hyt
  simp only at hle
  nlinarith

theorem lev_Fline_eq_univ {u : (ℝ × ℝ) →L[ℝ] ℝ} (h : u (0, 1) < 0) : lev Fline u = Set.univ := by
  refine Set.eq_univ_of_forall fun t => ?_
  obtain ⟨k, hk⟩ := exists_nat_ge (t / u (0, 1))
  refine (mem_Fline_iff (isClosed_halfLE u t) (convex_halfLE u t)).mpr ⟨k, ?_⟩
  rintro p ⟨hp1, hp2⟩
  show u p ≤ t
  rw [apply_eq u p, hp2]
  have hkt : u (0, 1) * (k : ℝ) ≤ t := by
    rw [div_le_iff_of_neg h] at hk
    linarith
  nlinarith

theorem lev_Fline_eq_Ici {u : (ℝ × ℝ) →L[ℝ] ℝ} (h : u (0, 1) = 0) :
    lev Fline u = Set.Ici (0 : ℝ) := by
  ext t
  simp only [Set.mem_Ici]
  rw [mem_lev_iff, mem_Fline_iff (isClosed_halfLE u t) (convex_halfLE u t)]
  constructor
  · rintro ⟨k, hk⟩
    have hle : u ((0 : ℝ), (k : ℝ)) ≤ t := hk ⟨le_rfl, rfl⟩
    rw [apply_eq u ((0 : ℝ), (k : ℝ))] at hle
    simp only [h] at hle
    simpa using hle
  · intro ht
    refine ⟨0, ?_⟩
    rintro p ⟨-, hp2⟩
    show u p ≤ t
    rw [apply_eq u p, hp2, h]
    simpa using ht

theorem levVal_Fline_of_pos {u : (ℝ × ℝ) →L[ℝ] ℝ} (h : 0 < u (0, 1)) : levVal Fline u = ⊤ :=
  levVal_of_lev_eq_empty (lev_Fline_eq_empty h)

theorem levVal_Fline_of_neg {u : (ℝ × ℝ) →L[ℝ] ℝ} (h : u (0, 1) < 0) : levVal Fline u = ⊥ :=
  levVal_of_lev_eq_univ (lev_Fline_eq_univ h)

theorem levVal_Fline_of_zero {u : (ℝ × ℝ) →L[ℝ] ℝ} (h : u (0, 1) = 0) :
    levVal Fline u = ((0 : ℝ) : EReal) := by
  classical
  have hIci := lev_Fline_eq_Ici h
  have h1 : lev Fline u ≠ ∅ := by
    rw [hIci]
    exact Set.nonempty_iff_ne_empty.mp ⟨(0 : ℝ), Set.self_mem_Ici⟩
  have h2 : lev Fline u ≠ Set.univ := by
    rw [hIci]
    intro hcon
    have hmem : (-1 : ℝ) ∈ Set.Ici (0 : ℝ) := by rw [hcon]; trivial
    rw [Set.mem_Ici] at hmem
    linarith
  rw [levVal, if_neg h1, if_neg h2, sig, hIci, csInf_Ici]

/-! ### The line filters in every non-vertical direction -/

/-- The linear automorphism of the plane taking `(0, 1)` to `(1, s)` and `(1, 0)` to
`(0, 1)`. -/
noncomputable def shear (s : ℝ) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  { toFun := fun p => (p.2, p.1 + s * p.2)
    invFun := fun p => (p.2 - s * p.1, p.1)
    map_add' := by intro p q; simp [Prod.ext_iff]; ring
    map_smul' := by intro c p; simp [Prod.ext_iff]; ring
    left_inv := by intro p; simp
    right_inv := by
      intro p
      have hp : p.2 - s * p.1 + s * p.1 = p.2 := by ring
      simp [hp]
    continuous_toFun := continuous_snd.prodMk (continuous_fst.add (continuous_const.mul
      continuous_snd))
    continuous_invFun := (continuous_snd.sub (continuous_const.mul continuous_fst)).prodMk
      continuous_fst }

@[simp] theorem shear_apply (s : ℝ) (p : ℝ × ℝ) : shear s p = (p.2, p.1 + s * p.2) := rfl

/-- The filter of stratum `(1, 1)` over the line through the origin with direction
`(1, s)`, escaping in the direction `(1, s)`: the transport of `Fline` along `shear s`. -/
noncomputable def lineFilter (s : ℝ) : ConvexFilter (ℝ × ℝ) := comapEquiv (shear s) Fline

theorem lineFilter_isMaximal (s : ℝ) : IsMaximal (lineFilter s) :=
  comapEquiv_isMaximal (shear s) Fline_isMaximal

/-- The extended support value of `lineFilter s` at `u` is governed by the sign of
`u (1, s)`. -/
theorem levVal_lineFilter (s : ℝ) (u : ((ℝ × ℝ) →L[ℝ] ℝ)) :
    levVal (lineFilter s) u =
      if 0 < u (1, s) then ⊤ else if u (1, s) < 0 then ⊥ else ((0 : ℝ) : EReal) := by
  rw [lineFilter, levVal_comapEquiv]
  have hval : (u.comp ((shear s) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))) (0, 1) = u (1, s) := by
    show u (shear s (0, 1)) = u (1, s)
    norm_num
  rcases lt_trichotomy (u (1, s)) 0 with h | h | h
  · rw [if_neg (by linarith), if_pos h]
    exact levVal_Fline_of_neg (by rw [hval]; exact h)
  · rw [if_neg (by rw [h]; exact lt_irrefl 0), if_neg (by rw [h]; exact lt_irrefl 0)]
    exact levVal_Fline_of_zero (by rw [hval, h])
  · rw [if_pos h]
    exact levVal_Fline_of_pos (by rw [hval]; exact h)

end Lines

/-! ## The boundary and its topology -/

section Boundary

open SigCounterexample

/-- The boundary of the maximal Hausdorff quotient of `MaxFilter (ℝ × ℝ)`: the complement
of the image of the plane. -/
def boundarySet : Set (T2Quotient (MaxFilter (ℝ × ℝ))) := (Set.range prinQ)ᶜ

/-- The classes at which the extended support value at `u` is finite: an open subset of the
quotient, being the preimage of the open set `ℝ ⊆ [-∞, +∞]`. -/
def finLocus (u : (ℝ × ℝ) →L[ℝ] ℝ) : Set (T2Quotient (MaxFilter (ℝ × ℝ))) :=
  (levQ u) ⁻¹' {z : EReal | z ≠ ⊤ ∧ z ≠ ⊥}

theorem isOpen_finLocus (u : (ℝ × ℝ) →L[ℝ] ℝ) : IsOpen (finLocus u) := by
  have hset : {z : EReal | z ≠ ⊤ ∧ z ≠ ⊥} = Set.Iio ⊤ ∩ Set.Ioi ⊥ := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi]
    exact ⟨fun h => ⟨lt_top_iff_ne_top.mpr h.1, bot_lt_iff_ne_bot.mpr h.2⟩,
      fun h => ⟨ne_of_lt h.1, ne_of_gt h.2⟩⟩
  rw [finLocus, hset]
  exact (continuous_levQ u).isOpen_preimage _ (isOpen_Iio.inter isOpen_Ioi)

/-- The unit normal-direction functional to the direction `(1, s)`. -/
noncomputable def normalAt (s : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ := coCLM (-s) 1

@[simp] theorem normalAt_apply (s : ℝ) (p : ℝ × ℝ) : normalAt s p = -s * p.1 + p.2 := by
  simp [normalAt]

/-- The class of the line filter in direction `(1, s)`, a point of the boundary at which
the extended support value at `normalAt s` is finite. -/
noncomputable def lineClass (s : ℝ) : T2Quotient (MaxFilter (ℝ × ℝ)) :=
  T2Quotient.mk ⟨lineFilter s, lineFilter_isMaximal s⟩

theorem levVal_lineFilter_normalAt (s : ℝ) :
    levVal (lineFilter s) (normalAt s) = ((0 : ℝ) : EReal) := by
  have h0 : normalAt s (1, s) = 0 := by simp
  rw [levVal_lineFilter, h0]
  norm_num

theorem levVal_lineFilter_dir (s : ℝ) : levVal (lineFilter s) (coCLM 1 s) = ⊤ := by
  have hpos : 0 < coCLM 1 s ((1 : ℝ), s) := by
    simp only [coCLM_apply]
    nlinarith [sq_nonneg s]
  rw [levVal_lineFilter, if_pos hpos]

/-- A class of the quotient at which some extended support value is infinite is not the
class of a principal filter: it lies in the boundary. -/
theorem mem_boundarySet_of_levVal_eq_top {G : MaxFilter (ℝ × ℝ)} {u : (ℝ × ℝ) →L[ℝ] ℝ}
    (h : levVal G.1 u = ⊤) : T2Quotient.mk G ∈ boundarySet := by
  rintro ⟨p, hp⟩
  have hval : levQ u (T2Quotient.mk G) = levQ u (prinQ p) := by rw [hp]
  rw [levQ_mk, levQ_prinQ, h] at hval
  exact EReal.top_ne_coe _ hval

theorem lineClass_mem_boundarySet (s : ℝ) : lineClass s ∈ boundarySet :=
  mem_boundarySet_of_levVal_eq_top (u := coCLM 1 s) (levVal_lineFilter_dir s)

theorem lineClass_mem_finLocus (s : ℝ) : lineClass s ∈ finLocus (normalAt s) := by
  show levQ (normalAt s) (lineClass s) ≠ ⊤ ∧ levQ (normalAt s) (lineClass s) ≠ ⊥
  rw [lineClass, levQ_mk, levVal_lineFilter_normalAt]
  exact ⟨EReal.coe_ne_top 0, EReal.coe_ne_bot 0⟩

/-- **The key disjointness.** A class of the boundary lies in at most one of the open sets
`finLocus (normalAt s)`: two independent functionals with finite extended support value
force `Nset` to be the whole dual, hence the filter to be principal (Proposition 2.7), and
principal classes are not in the boundary. -/
theorem finLocus_disjoint_of_ne {s s' : ℝ} (hss : s ≠ s') :
    Disjoint (boundarySet ∩ finLocus (normalAt s)) (boundarySet ∩ finLocus (normalAt s')) := by
  rw [Set.disjoint_left]
  rintro x ⟨hxb, hxs⟩ ⟨-, hxs'⟩
  obtain ⟨G, rfl⟩ := T2Quotient.surjective_mk _ x
  have hs : normalAt s ∈ Nset G.1 := by
    refine (mem_Nset_iff_levVal_ne G.2 _).mpr ?_
    have := hxs
    rw [finLocus, Set.mem_preimage, levQ_mk] at this
    exact this
  have hs' : normalAt s' ∈ Nset G.1 := by
    refine (mem_Nset_iff_levVal_ne G.2 _).mpr ?_
    have := hxs'
    rw [finLocus, Set.mem_preimage, levQ_mk] at this
    exact this
  -- the direction of the flat is trivial
  have hann := Nset_eq_annihilator_dirA G.2
  have hdir : ∀ v ∈ dirA G.1, v = 0 := by
    intro v hv
    have h1 : normalAt s v = 0 := by rw [hann] at hs; exact hs v hv
    have h2 : normalAt s' v = 0 := by rw [hann] at hs'; exact hs' v hv
    rw [normalAt_apply] at h1 h2
    have hv1 : v.1 = 0 := by
      have hsub : (s' - s) * v.1 = 0 := by linarith
      rcases mul_eq_zero.mp hsub with h | h
      · exact absurd (by linarith : s = s') hss
      · exact h
    have hv2 : v.2 = 0 := by rw [hv1] at h1; linarith
    exact Prod.ext hv1 hv2
  have hNuniv : Nset G.1 = Set.univ := by
    refine Set.eq_univ_of_forall fun u => ?_
    rw [hann]
    intro v hv
    rw [hdir v hv, map_zero]
  obtain ⟨p, hp⟩ := eq_principal_of_Nset_univ G.2 hNuniv
  exact hxb ⟨p, (MaxFilter.ext hp.symm : prin p = G) ▸ rfl⟩

/-! ### No continuous injection into a second countable space -/

instance : CompactSpace (↥boundarySet) :=
  isCompact_iff_compactSpace.mp isCompact_boundary

/-! ### The boundary is not second countable

The sets `boundarySet ∩ finLocus (normalAt s)`, for `s : ℝ`, are pairwise disjoint open
subsets of the boundary, each containing the class of the line filter in the direction
`(1, s)`.  An uncountable family of pairwise disjoint nonempty open sets is incompatible
with a countable basis. -/

/-- The point of the boundary given by the line filter in direction `(1, s)`. -/
noncomputable def lineBdry (s : ℝ) : (↥boundarySet) :=
  ⟨lineClass s, lineClass_mem_boundarySet s⟩

/-- The trace of `finLocus (normalAt s)` on the boundary, an open subset of the boundary. -/
def bdryLocus (s : ℝ) : Set (↥boundarySet) :=
  Subtype.val ⁻¹' (finLocus (normalAt s))

theorem isOpen_bdryLocus (s : ℝ) : IsOpen (bdryLocus s) :=
  (isOpen_finLocus (normalAt s)).preimage continuous_subtype_val

theorem lineBdry_mem_bdryLocus (s : ℝ) : lineBdry s ∈ bdryLocus s :=
  lineClass_mem_finLocus s

theorem bdryLocus_disjoint_of_ne {s s' : ℝ} (hss : s ≠ s') {x : (↥boundarySet)}
    (hx : x ∈ bdryLocus s) (hx' : x ∈ bdryLocus s') : False := by
  have h1 : (x : T2Quotient (MaxFilter (ℝ × ℝ))) ∈ boundarySet ∩ finLocus (normalAt s) :=
    ⟨x.2, hx⟩
  have h2 : (x : T2Quotient (MaxFilter (ℝ × ℝ))) ∈ boundarySet ∩ finLocus (normalAt s') :=
    ⟨x.2, hx'⟩
  exact Set.disjoint_left.mp (finLocus_disjoint_of_ne hss) h1 h2

/-- **The boundary is not second countable.** The uncountable family `bdryLocus s`,
`s : ℝ`, consists of pairwise disjoint nonempty open subsets of the boundary. -/
theorem not_secondCountableTopology_boundarySet :
    ¬ SecondCountableTopology (↥boundarySet) := by
  intro hsc
  obtain ⟨b, hbc, -, hbasis⟩ :=
    TopologicalSpace.exists_countable_basis (↥boundarySet)
  have hchoice : ∀ s : ℝ, ∃ v ∈ b, lineBdry s ∈ v ∧ v ⊆ bdryLocus s := fun s =>
    hbasis.exists_subset_of_mem_open (lineBdry_mem_bdryLocus s) (isOpen_bdryLocus s)
  choose v hvb hvmem hvsub using hchoice
  have hinj : Function.Injective v := by
    intro s s' hv
    by_contra hss
    refine bdryLocus_disjoint_of_ne hss (hvsub s (hvmem s)) ?_
    exact hvsub s' (hv ▸ hvmem s)
  have huniv : (Set.univ : Set ℝ) = v ⁻¹' b := by
    ext s
    simp only [Set.mem_univ, Set.mem_preimage, true_iff]
    exact hvb s
  exact Cardinal.not_countable_real (huniv ▸ hbc.preimage hinj)

/-- **No continuous injective invariant.** There is no continuous injection of the boundary
into a second countable Hausdorff space: such a map would be a topological embedding, the
boundary being compact and the target Hausdorff, and the boundary would inherit a countable
basis. -/
theorem not_injective_of_continuous_of_secondCountable {Y : Type*} [TopologicalSpace Y]
    [T2Space Y] [SecondCountableTopology Y]
    {f : (↥boundarySet) → Y} (hf : Continuous f) :
    ¬ Function.Injective f := by
  intro hinj
  exact not_secondCountableTopology_boundarySet
    (hf.isClosedEmbedding hinj).isEmbedding.secondCountableTopology

/-- **Part C is false.** The boundary of the maximal Hausdorff quotient of the plane is
*not* homeomorphic to `S¹ × [-∞, +∞]`.

The target is second countable, while the boundary is not
(`not_secondCountableTopology_boundarySet`): the classes of the filters of stratum `(1, 1)`
over the lines of a fixed direction form an open subset of the boundary, and there are
uncountably many directions.  Concretely, the topology the boundary inherits from the
quotient is strictly finer than the product topology of the parametrization: the extended
support value at a fixed functional is continuous on the quotient, and it is finite exactly
on the classes over lines normal to that functional, so a class over a line cannot be
approached by classes over lines of a different direction. -/
theorem not_boundary_homeomorph :
    ¬ Nonempty (((Set.range (fun p : ℝ × ℝ =>
        T2Quotient.mk (X := MaxFilter (ℝ × ℝ)) ⟨principal p, principal_isMaximal p⟩))ᶜ :
          Set (T2Quotient (MaxFilter (ℝ × ℝ)))) ≃ₜ
      (Metric.sphere (0 : ℝ × ℝ) 1 × EReal)) := by
  rintro ⟨h⟩
  exact not_secondCountableTopology_boundarySet (Homeomorph.secondCountableTopology h)

end Boundary

/-! ## Part B — the parametrization of the boundary -/

section PartB

open SigCounterexample

/-! ### The primary escape direction exists -/

section Escape

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The primary escape direction.**  A non-principal maximal convex filter has a nonzero
vector `v` such that every functional positive at `v` escapes: `levVal F u = ⊤`.

This is read off the normal form of the escape cone.  The pair `(Aset F, Eset F)` is
admissible (`isAdmissible_Aset_Eset`), so `Eset F` is a lexicographic cone modulo `Nset F`
for a family of functionals on the dual (`Adapted.exists_functionals_mod`); in finite
dimensions those are evaluations at points (`exists_point_of_dual_functional`), and the
first nonzero one is the required `v`.  It is nonzero because the filter is not
principal. -/
theorem exists_escape_direction {F : ConvexFilter V} (hF : IsMaximal F)
    (hnp : Nset F ≠ Set.univ) :
    ∃ v : V, v ≠ 0 ∧ ∀ u : V →L[ℝ] ℝ, 0 < u v → levVal F u = ⊤ := by
  classical
  obtain ⟨-, ⟨M, hM, hlex, -⟩, -, -⟩ := isAdmissible_Aset_Eset hF
  obtain ⟨k, l, -, -, hker, hEeq⟩ := Adapted.exists_functionals_mod hlex
  have hMtop : M ≠ ⊤ := by
    intro htop
    refine hnp (Set.eq_univ_of_forall fun u => ?_)
    have huM : u ∈ (M : Set (V →L[ℝ] ℝ)) := by rw [htop]; trivial
    exact (hM u).mp huM
  have hex : ∃ i : Fin k, l i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    refine hMtop (eq_top_iff.mpr fun u _ => hker u trivial fun i => ?_)
    rw [hcon i]
    rfl
  obtain ⟨i₀, hi₀⟩ := hex
  set S : Finset (Fin k) := Finset.univ.filter (fun i => l i ≠ 0) with hS
  have hSne : S.Nonempty := ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ i₀, hi₀⟩⟩
  set j := S.min' hSne with hj
  have hjne : l j ≠ 0 := (Finset.mem_filter.mp (S.min'_mem hSne)).2
  have hjlt : ∀ i : Fin k, i < j → l i = 0 := by
    intro i hi
    by_contra hne
    exact absurd (S.min'_le i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩)) (not_le.mpr hi)
  obtain ⟨v, hv⟩ := exists_point_of_dual_functional (l j)
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hjne (ContinuousLinearMap.ext fun u => by rw [hv u, map_zero]; rfl)
  refine ⟨v, hv0, fun u hu => ?_⟩
  have humem : u ∈ Eset F := by
    rw [hEeq]
    exact ⟨trivial, j, by rw [hv u]; exact hu, fun i hi => by rw [hjlt i hi]; rfl⟩
  exact levVal_of_lev_eq_empty humem

end Escape

/-! ### The direction and the offset, read off `levVal` -/

/-- The property of being a primary escape direction of the extended support value `g`: a
vector of norm one at which every positive functional has value `⊤`. -/
def IsEscapeDir (g : ((ℝ × ℝ) →L[ℝ] ℝ) → EReal) (v : ℝ × ℝ) : Prop :=
  ‖v‖ = 1 ∧ ∀ u : (ℝ × ℝ) →L[ℝ] ℝ, 0 < u v → g u = ⊤

open Classical in
/-- The primary escape direction attached to an extended support value, a vector of norm
one; the value `(1, 0)` is returned when there is no escape direction, which happens
exactly for the principal filters. -/
noncomputable def dirOfVal (g : ((ℝ × ℝ) →L[ℝ] ℝ) → EReal) : ℝ × ℝ :=
  if h : ∃ v : ℝ × ℝ, IsEscapeDir g v then h.choose else (1, 0)

/-- **The primary escape direction of a maximal filter**, defined from `levVal` alone, so
that it descends to the Hausdorff quotient. -/
noncomputable def dirOf (F : ConvexFilter (ℝ × ℝ)) : ℝ × ℝ := dirOfVal (levVal F)

/-- The functional dual to the unit normal of the direction `v`, oriented by the rotation
`v ↦ (-v.2, v.1)`. -/
noncomputable def normalCLM (v : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ := coCLM (-v.2) v.1

/-- **The offset of a maximal filter**: the extended support value at the normal to the
primary escape direction.  It is finite exactly on the strata `(1, 1)` and `(1, 2)`. -/
noncomputable def offOf (F : ConvexFilter (ℝ × ℝ)) : EReal := levVal F (normalCLM (dirOf F))

theorem norm_dirOfVal (g : ((ℝ × ℝ) →L[ℝ] ℝ) → EReal) : ‖dirOfVal g‖ = 1 := by
  classical
  rw [dirOfVal]
  split
  · rename_i h
    exact h.choose_spec.1
  · simp [Prod.norm_def]

theorem norm_dirOf (F : ConvexFilter (ℝ × ℝ)) : ‖dirOf F‖ = 1 := norm_dirOfVal _

/-- On a non-principal maximal filter, `dirOf` is an escape direction. -/
theorem isEscapeDir_dirOf {F : ConvexFilter (ℝ × ℝ)} (hF : IsMaximal F)
    (hnp : Nset F ≠ Set.univ) : IsEscapeDir (levVal F) (dirOf F) := by
  classical
  have hex : ∃ v : ℝ × ℝ, IsEscapeDir (levVal F) v := by
    obtain ⟨v, hv0, hv⟩ := exists_escape_direction hF hnp
    have hnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
    refine ⟨‖v‖⁻¹ • v, ?_, fun u hu => ?_⟩
    · rw [norm_smul]
      simp [inv_mul_cancel₀ hnorm]
    · refine hv u ?_
      rw [ContinuousLinearMap.map_smul, smul_eq_mul] at hu
      have hinv : 0 < ‖v‖⁻¹ := by positivity
      nlinarith
  rw [dirOf, dirOfVal, dif_pos hex]
  exact hex.choose_spec

/-- Two distinct vectors of norm one of the plane are strictly separated by a functional:
a functional is positive at the first and negative at the second. -/
theorem exists_functional_pos_neg {v v' : ℝ × ℝ} (hv : ‖v‖ = 1) (hv' : ‖v'‖ = 1)
    (hne : v ≠ v') : ∃ u : (ℝ × ℝ) →L[ℝ] ℝ, 0 < u v ∧ u v' < 0 := by
  have hv0 : v ≠ 0 := by
    intro hcon
    rw [hcon] at hv
    simp at hv
  have hsq : 0 < v.1 ^ 2 + v.2 ^ 2 := by
    rcases (by
      by_contra hcon
      push_neg at hcon
      exact hv0 (Prod.ext (by simpa using hcon.1) (by simpa using hcon.2)) :
        v.1 ≠ 0 ∨ v.2 ≠ 0) with h1 | h2
    · nlinarith [sq_nonneg v.2, sq_pos_of_ne_zero h1]
    · nlinarith [sq_nonneg v.1, sq_pos_of_ne_zero h2]
  by_cases hD : v.1 * v'.2 - v.2 * v'.1 = 0
  · -- the two vectors are proportional, hence opposite
    have hopp : v' = -v := by
      have hex : ∃ t : ℝ, v' = t • v := by
        by_cases h1 : v.1 = 0
        · have hv2 : v.2 ≠ 0 := by
            intro hcon
            exact hv0 (Prod.ext (by simpa using h1) (by simpa using hcon))
          have h1' : v'.1 = 0 := by
            rw [h1] at hD
            simp only [zero_mul, zero_sub, neg_eq_zero] at hD
            rcases mul_eq_zero.mp hD with h | h
            · exact absurd h hv2
            · exact h
          refine ⟨v'.2 / v.2, Prod.ext ?_ ?_⟩
          · simp [h1, h1']
          · simp [div_mul_cancel₀ _ hv2]
        · refine ⟨v'.1 / v.1, Prod.ext ?_ ?_⟩
          · simp [div_mul_cancel₀ _ h1]
          · show v'.2 = v'.1 / v.1 * v.2
            field_simp
            linarith [hD]
      obtain ⟨t, rfl⟩ := hex
      have habs : |t| = 1 := by
        rw [norm_smul, Real.norm_eq_abs, hv, mul_one] at hv'
        exact hv'
      rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.mp habs with rfl | rfl
      · exact absurd (one_smul ℝ v).symm hne
      · rw [neg_smul, one_smul]
    refine ⟨coCLM v.1 v.2, ?_, ?_⟩
    · show 0 < v.1 * v.1 + v.2 * v.2
      nlinarith
    · rw [hopp]
      show v.1 * (-v).1 + v.2 * (-v).2 < 0
      simp only [Prod.fst_neg, Prod.snd_neg]
      nlinarith
  · refine ⟨coCLM ((v'.2 + v.2) / (v.1 * v'.2 - v.2 * v'.1))
      (-(v.1 + v'.1) / (v.1 * v'.2 - v.2 * v'.1)), ?_, ?_⟩
    · have hval : (v'.2 + v.2) / (v.1 * v'.2 - v.2 * v'.1) * v.1 +
          -(v.1 + v'.1) / (v.1 * v'.2 - v.2 * v'.1) * v.2 = 1 := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD]
        ring
      show 0 < _
      rw [coCLM_apply, hval]
      norm_num
    · have hval : (v'.2 + v.2) / (v.1 * v'.2 - v.2 * v'.1) * v'.1 +
          -(v.1 + v'.1) / (v.1 * v'.2 - v.2 * v'.1) * v'.2 = -1 := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD]
        ring
      show _ < 0
      rw [coCLM_apply, hval]
      norm_num

/-- The escape direction is unique: two of them would make some functional and its negative
both escape. -/
theorem escape_dir_unique {F : ConvexFilter (ℝ × ℝ)} (hF : IsMaximal F) {v v' : ℝ × ℝ}
    (h : IsEscapeDir (levVal F) v) (h' : IsEscapeDir (levVal F) v') : v = v' := by
  by_contra hne
  obtain ⟨u, hu, hu'⟩ := exists_functional_pos_neg h.1 h'.1 hne
  have h1 : levVal F u = ⊤ := h.2 u hu
  have h2 : levVal F (-u) = ⊤ := by
    refine h'.2 (-u) ?_
    rw [ContinuousLinearMap.neg_apply]
    linarith
  have he1 : lev F u = ∅ := (mem_Eset_iff_levVal_eq_top hF u).mpr h1
  have he2 : lev F (-u) = ∅ := (mem_Eset_iff_levVal_eq_top hF (-u)).mpr h2
  rw [lev_univ_of_lev_empty hF he1] at he2
  exact absurd (he2 ▸ Set.mem_univ (0 : ℝ)) (Set.notMem_empty 0)

theorem dirOf_eq_of_isEscapeDir {F : ConvexFilter (ℝ × ℝ)} (hF : IsMaximal F)
    (hnp : Nset F ≠ Set.univ) {v : ℝ × ℝ} (h : IsEscapeDir (levVal F) v) : dirOf F = v :=
  escape_dir_unique hF (isEscapeDir_dirOf hF hnp) h

/-! ### The parametrization -/

/-- **The parametrization of the boundary**: the primary escape direction together with the
offset. -/
noncomputable def boundaryMap (F : MaxFilter (ℝ × ℝ)) : Metric.sphere (0 : ℝ × ℝ) 1 × EReal :=
  (⟨dirOf F.1, by simpa [Metric.mem_sphere, dist_zero_right] using norm_dirOf F.1⟩, offOf F.1)

/-- **`boundaryMap` descends to the Hausdorff quotient.**  Both components are defined from
`levVal`, so filters with the same extended support value have the same image. -/
theorem boundaryMap_eq_of_levVal_eq {F F' : MaxFilter (ℝ × ℝ)}
    (h : ∀ u, levVal F.1 u = levVal F'.1 u) : boundaryMap F = boundaryMap F' := by
  have hfun : levVal F.1 = levVal F'.1 := funext h
  have hdir : dirOf F.1 = dirOf F'.1 := by rw [dirOf, dirOf, hfun]
  have hoff : offOf F.1 = offOf F'.1 := by rw [offOf, offOf, hdir, hfun]
  rw [boundaryMap, boundaryMap]
  simp only [hoff, Prod.mk.injEq, and_true]
  exact Subtype.ext hdir

/-! ### Injectivity of the parametrization -/

section Injectivity

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The extended support value at the zero functional is zero. -/
theorem levVal_zero {F : ConvexFilter V} (hF : IsMaximal F) :
    levVal F (0 : V →L[ℝ] ℝ) = 0 := by
  rw [levVal_of_mem_Nset hF zero_mem_Nset, sig_zero]
  rfl

/-- Two maximal filters agreeing at `u` agree at `-u`. -/
theorem levVal_neg_eq_of_eq {F F' : ConvexFilter V} (hF : IsMaximal F) (hF' : IsMaximal F')
    {u : V →L[ℝ] ℝ} (h : levVal F u = levVal F' u) : levVal F (-u) = levVal F' (-u) := by
  rcases levVal_cases F hF u with ⟨he, hv⟩ | ⟨he, hv⟩ | ⟨hn, hv⟩
  · have he' : lev F' u = ∅ := (mem_Eset_iff_levVal_eq_top hF' u).mpr (by rw [← h, hv])
    rw [levVal_of_lev_eq_univ (lev_univ_of_lev_empty hF he),
      levVal_of_lev_eq_univ (lev_univ_of_lev_empty hF' he')]
  · have hv' : levVal F' u = ⊥ := by rw [← h, hv]
    have he' : lev F' u = Set.univ := by
      rcases levVal_cases F' hF' u with ⟨-, hx⟩ | ⟨hx, -⟩ | ⟨-, hx⟩
      · rw [hx] at hv'; exact absurd hv' (by simp)
      · exact hx
      · rw [hx] at hv'; exact absurd hv' (by simp)
    rw [levVal_of_lev_eq_empty (lev_empty_of_lev_univ he),
      levVal_of_lev_eq_empty (lev_empty_of_lev_univ he')]
  · have hn' : u ∈ Nset F' := by
      rw [mem_Nset_iff_levVal_ne hF', ← h]
      exact (mem_Nset_iff_levVal_ne hF u).mp hn
    have hsig : sig F u = sig F' u := by
      rw [levVal_of_mem_Nset hF hn, levVal_of_mem_Nset hF' hn'] at h
      exact_mod_cast h
    rw [levVal_of_mem_Nset hF (Nset_neg hn), levVal_of_mem_Nset hF' (Nset_neg hn'),
      sig_neg hF hn, sig_neg hF' hn', hsig]

/-- Two maximal filters agreeing at `u` agree at every positive multiple of `u`. -/
theorem levVal_smul_pos_eq_of_eq {F F' : ConvexFilter V} (hF : IsMaximal F) (hF' : IsMaximal F')
    {u : V →L[ℝ] ℝ} (h : levVal F u = levVal F' u) {c : ℝ} (hc : 0 < c) :
    levVal F (c • u) = levVal F' (c • u) := by
  have hemp : ∀ G : ConvexFilter V, lev G u = ∅ → lev G (c • u) = ∅ := by
    intro G hG
    rw [Set.eq_empty_iff_forall_notMem]
    intro t ht
    have hmem := (mem_lev_smul_iff hc).mp ht
    rw [hG] at hmem
    exact hmem
  have huniv : ∀ G : ConvexFilter V, lev G u = Set.univ → lev G (c • u) = Set.univ := by
    intro G hG
    refine Set.eq_univ_of_forall fun t => (mem_lev_smul_iff hc).mpr ?_
    rw [hG]
    trivial
  rcases levVal_cases F hF u with ⟨he, hv⟩ | ⟨he, hv⟩ | ⟨hn, hv⟩
  · have he' : lev F' u = ∅ := (mem_Eset_iff_levVal_eq_top hF' u).mpr (by rw [← h, hv])
    rw [levVal_of_lev_eq_empty (hemp F he), levVal_of_lev_eq_empty (hemp F' he')]
  · have hv' : levVal F' u = ⊥ := by rw [← h, hv]
    have he' : lev F' u = Set.univ := by
      rcases levVal_cases F' hF' u with ⟨-, hx⟩ | ⟨hx, -⟩ | ⟨-, hx⟩
      · rw [hx] at hv'; exact absurd hv' (by simp)
      · exact hx
      · rw [hx] at hv'; exact absurd hv' (by simp)
    rw [levVal_of_lev_eq_univ (huniv F he), levVal_of_lev_eq_univ (huniv F' he')]
  · have hn' : u ∈ Nset F' := by
      rw [mem_Nset_iff_levVal_ne hF', ← h]
      exact (mem_Nset_iff_levVal_ne hF u).mp hn
    have hsig : sig F u = sig F' u := by
      rw [levVal_of_mem_Nset hF hn, levVal_of_mem_Nset hF' hn'] at h
      exact_mod_cast h
    rw [levVal_of_mem_Nset hF (Nset_smul hn), levVal_of_mem_Nset hF' (Nset_smul hn'),
      sig_smul hF hn, sig_smul hF' hn', hsig]

/-- Two maximal filters agreeing at `u` agree at every real multiple of `u`. -/
theorem levVal_smul_eq_of_eq {F F' : ConvexFilter V} (hF : IsMaximal F) (hF' : IsMaximal F')
    {u : V →L[ℝ] ℝ} (h : levVal F u = levVal F' u) (c : ℝ) :
    levVal F (c • u) = levVal F' (c • u) := by
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · have hneg := levVal_neg_eq_of_eq hF hF' h
    have hpos := levVal_smul_pos_eq_of_eq hF hF' hneg (show (0 : ℝ) < -c by linarith)
    rwa [smul_neg_neg_eq] at hpos
  · rw [zero_smul, levVal_zero hF, levVal_zero hF']
  · exact levVal_smul_pos_eq_of_eq hF hF' h hc

end Injectivity

/-- Every functional of the plane is `coCLM` of its two coordinates. -/
theorem coCLM_coord (u : (ℝ × ℝ) →L[ℝ] ℝ) : coCLM (u (1, 0)) (u (0, 1)) = u := by
  refine ContinuousLinearMap.ext fun p => ?_
  rw [coCLM_apply, SigCounterexample.apply_eq u p]

theorem smul_coCLM (t a b : ℝ) : t • coCLM a b = coCLM (t * a) (t * b) := by
  refine ContinuousLinearMap.ext fun p => ?_
  rw [ContinuousLinearMap.smul_apply, coCLM_apply, coCLM_apply, smul_eq_mul]
  ring

/-- A functional of the plane vanishing at a nonzero vector `v` is a multiple of the normal
functional of `v`. -/
theorem exists_smul_normalCLM {v : ℝ × ℝ} (hv : v ≠ 0) {u : (ℝ × ℝ) →L[ℝ] ℝ} (h : u v = 0) :
    ∃ t : ℝ, u = t • normalCLM v := by
  set a := u (1, 0) with ha
  set b := u (0, 1) with hb
  have hab : a * v.1 + b * v.2 = 0 := by rw [ha, hb, ← SigCounterexample.apply_eq u v]; exact h
  by_cases h1 : v.1 = 0
  · have hv2 : v.2 ≠ 0 := by
      intro hcon
      exact hv (Prod.ext (by simpa using h1) (by simpa using hcon))
    have hb0 : b = 0 := by
      rw [h1, mul_zero, zero_add] at hab
      rcases mul_eq_zero.mp hab with hx | hx
      · exact hx
      · exact absurd hx hv2
    refine ⟨-a / v.2, ?_⟩
    rw [normalCLM, smul_coCLM, ← coCLM_coord u, ← ha, ← hb, hb0, h1]
    congr 1
    · field_simp
    · rw [mul_zero]
  · refine ⟨b / v.1, ?_⟩
    rw [normalCLM, smul_coCLM, ← coCLM_coord u, ← ha, ← hb]
    congr 1
    · field_simp
      linarith [hab]
    · field_simp

/-- **The pair `(dirOf, offOf)` determines `levVal`** on the non-principal maximal filters of
the plane: positive functionals on the escape direction have value `⊤`, negative ones `⊥`,
and the functionals vanishing on it are the multiples of the normal, where the value is read
off the offset. -/
theorem levVal_eq_of_dirOf_offOf_eq {F F' : ConvexFilter (ℝ × ℝ)} (hF : IsMaximal F)
    (hF' : IsMaximal F') (hnp : Nset F ≠ Set.univ) (hnp' : Nset F' ≠ Set.univ)
    (hdir : dirOf F = dirOf F') (hoff : offOf F = offOf F') (u : (ℝ × ℝ) →L[ℝ] ℝ) :
    levVal F u = levVal F' u := by
  have hv : IsEscapeDir (levVal F) (dirOf F) := isEscapeDir_dirOf hF hnp
  have hv' : IsEscapeDir (levVal F') (dirOf F) := by
    rw [hdir]; exact isEscapeDir_dirOf hF' hnp'
  have hv0 : dirOf F ≠ 0 := by
    intro hcon
    have := hv.1
    rw [hcon, norm_zero] at this
    exact zero_ne_one this
  rcases lt_trichotomy (u (dirOf F)) 0 with hlt | heq | hgt
  · have h1 : levVal F (-u) = ⊤ := hv.2 (-u) (by rw [ContinuousLinearMap.neg_apply]; linarith)
    have h2 : levVal F' (-u) = ⊤ := hv'.2 (-u) (by rw [ContinuousLinearMap.neg_apply]; linarith)
    have he1 : lev F (-u) = ∅ := (mem_Eset_iff_levVal_eq_top hF (-u)).mpr h1
    have he2 : lev F' (-u) = ∅ := (mem_Eset_iff_levVal_eq_top hF' (-u)).mpr h2
    have hu1 : lev F u = Set.univ := by
      have := lev_univ_of_lev_empty hF he1
      rwa [neg_neg] at this
    have hu2 : lev F' u = Set.univ := by
      have := lev_univ_of_lev_empty hF' he2
      rwa [neg_neg] at this
    rw [levVal_of_lev_eq_univ hu1, levVal_of_lev_eq_univ hu2]
  · obtain ⟨t, rfl⟩ := exists_smul_normalCLM hv0 heq
    refine levVal_smul_eq_of_eq hF hF' ?_ t
    rw [offOf, offOf, hdir] at hoff
    rw [hdir]
    exact hoff
  · rw [hv.2 u hgt, hv'.2 u hgt]

/-- **Part B, contract form: injectivity.** Two non-principal maximal filters of the plane
with the same direction and offset have the same image in the Hausdorff quotient. -/
theorem boundaryMap_injective_on_quotient {F F' : MaxFilter (ℝ × ℝ)}
    (hnp : Nset F.1 ≠ Set.univ) (hnp' : Nset F'.1 ≠ Set.univ)
    (h : boundaryMap F = boundaryMap F') : T2Quotient.mk F = T2Quotient.mk F' := by
  have hdir : dirOf F.1 = dirOf F'.1 := congrArg (fun z => ((z.1 : Metric.sphere (0 : ℝ × ℝ) 1) :
    ℝ × ℝ)) h
  have hoff : offOf F.1 = offOf F'.1 := congrArg Prod.snd h
  exact levVal_separates_quotient.mp
    (levVal_eq_of_dirOf_offOf_eq F.2 F'.2 hnp hnp' hdir hoff)

/-! ### Scaling of the extended support value -/

section Scaling

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {F : ConvexFilter V}

/-- The level set is all of `ℝ` exactly when the extended support value is `⊥`. -/
theorem lev_eq_univ_of_levVal_eq_bot (hF : IsMaximal F) {u : V →L[ℝ] ℝ}
    (h : levVal F u = ⊥) : lev F u = Set.univ := by
  rcases levVal_cases F hF u with ⟨-, hx⟩ | ⟨hx, -⟩ | ⟨-, hx⟩
  · rw [hx] at h; exact absurd h (by simp)
  · exact hx
  · rw [hx] at h; exact absurd h (by simp)

/-- The extended support value at `u` is `c` when the level set is the ray above `c`. -/
theorem levVal_of_lev_eq_Ici {u : V →L[ℝ] ℝ} {c : ℝ} (h : lev F u = Set.Ici c) :
    levVal F u = (c : EReal) := by
  classical
  have h1 : lev F u ≠ ∅ := by
    rw [h]
    exact Set.nonempty_iff_ne_empty.mp ⟨c, Set.self_mem_Ici⟩
  have h2 : lev F u ≠ Set.univ := by
    rw [h]
    intro hcon
    have hmem : c - 1 ∈ Set.Ici c := by rw [hcon]; trivial
    rw [Set.mem_Ici] at hmem
    linarith
  rw [levVal, if_neg h1, if_neg h2, sig, h, csInf_Ici]

theorem levVal_smul_pos_of_top (hF : IsMaximal F) {u : V →L[ℝ] ℝ} {c : ℝ} (hc : 0 < c)
    (h : levVal F u = ⊤) : levVal F (c • u) = ⊤ := by
  have he : lev F u = ∅ := (mem_Eset_iff_levVal_eq_top hF u).mpr h
  refine levVal_of_lev_eq_empty (Set.eq_empty_iff_forall_notMem.mpr fun t ht => ?_)
  have hmem := (mem_lev_smul_iff hc).mp ht
  rw [he] at hmem
  exact hmem

theorem levVal_smul_pos_of_bot (hF : IsMaximal F) {u : V →L[ℝ] ℝ} {c : ℝ} (hc : 0 < c)
    (h : levVal F u = ⊥) : levVal F (c • u) = ⊥ := by
  have he : lev F u = Set.univ := lev_eq_univ_of_levVal_eq_bot hF h
  refine levVal_of_lev_eq_univ (Set.eq_univ_of_forall fun t => (mem_lev_smul_iff hc).mpr ?_)
  rw [he]
  trivial

theorem levVal_smul_of_coe (hF : IsMaximal F) {u : V →L[ℝ] ℝ} {c x : ℝ}
    (h : levVal F u = (x : EReal)) : levVal F (c • u) = ((c * x : ℝ) : EReal) := by
  have hn : u ∈ Nset F := by
    rw [mem_Nset_iff_levVal_ne hF, h]
    exact ⟨EReal.coe_ne_top x, EReal.coe_ne_bot x⟩
  have hsig : sig F u = x := by
    rw [levVal_of_mem_Nset hF hn] at h
    exact_mod_cast h
  rw [levVal_of_mem_Nset hF (Nset_smul hn), sig_smul hF hn, hsig]

end Scaling

/-! ### Surjectivity of the parametrization -/

section Surjectivity

open SigCounterexample

/-- The translation by `a` of the plane, as an affine automorphism. -/
def transA (a : ℝ × ℝ) : (ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ) where
  toEquiv :=
    { toFun := fun p => p + a
      invFun := fun p => p - a
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  linear := LinearEquiv.refl ℝ (ℝ × ℝ)
  map_vadd' := by
    intro p w
    show w + p + a = w + (p + a)
    abel

@[simp] theorem transA_apply (a p : ℝ × ℝ) : transA a p = p + a := rfl

theorem continuous_transA (a : ℝ × ℝ) : Continuous (transA a) := by
  have h : ⇑(transA a) = fun p : ℝ × ℝ => p + a := rfl
  rw [h]
  fun_prop

theorem continuous_transA_symm (a : ℝ × ℝ) : Continuous (transA a).symm := by
  have h : ⇑(transA a).symm = fun p : ℝ × ℝ => p - a := rfl
  rw [h]
  fun_prop

/-- The translate by `a` of a convex filter of the plane. -/
def transFilter (a : ℝ × ℝ) (F : ConvexFilter (ℝ × ℝ)) : ConvexFilter (ℝ × ℝ) :=
  comapAffine (transA a) (continuous_transA a) (continuous_transA_symm a) F

theorem transFilter_isMaximal (a : ℝ × ℝ) {F : ConvexFilter (ℝ × ℝ)} (hF : IsMaximal F) :
    IsMaximal (transFilter a F) :=
  comapAffine_isMaximal (transA a) (continuous_transA a) (continuous_transA_symm a) hF

theorem lev_transFilter (a : ℝ × ℝ) (F : ConvexFilter (ℝ × ℝ)) (u : (ℝ × ℝ) →L[ℝ] ℝ) :
    lev (transFilter a F) u = {t : ℝ | t - u a ∈ lev F u} := by
  ext t
  have hpre : (⇑(transA a) ⁻¹' halfLE u t) = halfLE u (t - u a) := by
    ext p
    simp only [Set.mem_preimage, halfLE, Set.mem_setOf_eq, transA_apply, map_add]
    constructor <;> intro h <;> linarith
  rw [mem_lev_iff, Set.mem_setOf_eq, mem_lev_iff]
  show (⇑(transA a) ⁻¹' halfLE u t) ∈ F.carrier ↔ _
  rw [hpre]

/-- The filter of stratum `(1, 1)` over the vertical line `x = -c`, escaping upwards. -/
noncomputable def vlineFilter (c : ℝ) : ConvexFilter (ℝ × ℝ) := transFilter (-c, 0) Fline

theorem vlineFilter_isMaximal (c : ℝ) : IsMaximal (vlineFilter c) :=
  transFilter_isMaximal _ Fline_isMaximal

theorem levVal_vlineFilter_of_pos (c : ℝ) {u : (ℝ × ℝ) →L[ℝ] ℝ} (h : 0 < u (0, 1)) :
    levVal (vlineFilter c) u = ⊤ := by
  refine levVal_of_lev_eq_empty ?_
  rw [vlineFilter, lev_transFilter, lev_Fline_eq_empty h]
  rfl

/-- The offset of the vertical line filter over `x = -c` is `c`. -/
theorem levVal_vlineFilter_normal (c : ℝ) :
    levVal (vlineFilter c) (coCLM (-1) 0) = (c : EReal) := by
  have hzero : (coCLM (-1) 0) (0, 1) = 0 := by rw [coCLM_apply]; ring
  have hval : (coCLM (-1) 0) ((-c, 0) : ℝ × ℝ) = c := by rw [coCLM_apply]; ring
  refine levVal_of_lev_eq_Ici ?_
  rw [vlineFilter, lev_transFilter, lev_Fline_eq_Ici hzero, hval]
  ext t
  simp only [Set.mem_setOf_eq, Set.mem_Ici, sub_nonneg]

/-- The linear automorphism of the plane taking `(0, 1)` to `v` and `(1, 0)` to
`(v.2, -v.1)`. -/
noncomputable def dirEquiv (v : ℝ × ℝ) (hv : v ≠ 0) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  have hr : v.1 ^ 2 + v.2 ^ 2 ≠ 0 := by
    intro h
    exact hv (Prod.ext (by nlinarith [sq_nonneg v.1, sq_nonneg v.2] :  v.1 = 0)
      (by nlinarith [sq_nonneg v.1, sq_nonneg v.2] : v.2 = 0))
  { toFun := fun p => (p.1 * v.2 + p.2 * v.1, -(p.1 * v.1) + p.2 * v.2)
    invFun := fun q => ((q.1 * v.2 - q.2 * v.1) / (v.1 ^ 2 + v.2 ^ 2),
      (q.1 * v.1 + q.2 * v.2) / (v.1 ^ 2 + v.2 ^ 2))
    map_add' := by intro p q; simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk,
      Prod.ext_iff]; constructor <;> ring
    map_smul' := by intro c p; simp only [Prod.smul_fst, Prod.smul_snd, Prod.smul_mk,
      smul_eq_mul, RingHom.id_apply, Prod.ext_iff]; constructor <;> ring
    left_inv := by
      intro p
      simp only [Prod.ext_iff]
      constructor <;> field_simp <;> ring
    right_inv := by
      intro q
      simp only [Prod.ext_iff]
      constructor <;> field_simp <;> ring
    continuous_toFun := by
      apply Continuous.prodMk
      · fun_prop
      · fun_prop
    continuous_invFun := by
      apply Continuous.prodMk
      · fun_prop
      · fun_prop }

@[simp] theorem dirEquiv_apply (v : ℝ × ℝ) (hv : v ≠ 0) (p : ℝ × ℝ) :
    dirEquiv v hv p = (p.1 * v.2 + p.2 * v.1, -(p.1 * v.1) + p.2 * v.2) := rfl

/-- **The transport of a base filter to the direction `v`.**  If the base filter escapes
upwards, its transport along `dirEquiv v` escapes in the direction `v`, and its offset is
the value of the base at the positive multiple `(v.1 ^ 2 + v.2 ^ 2) • coCLM (-1) 0` of the
horizontal normal. -/
theorem exists_boundary_filter {F0 : ConvexFilter (ℝ × ℝ)} (hF0 : IsMaximal F0)
    (htop : ∀ u : (ℝ × ℝ) →L[ℝ] ℝ, 0 < u (0, 1) → levVal F0 u = ⊤)
    {v : ℝ × ℝ} (hv : ‖v‖ = 1) :
    ∃ F : MaxFilter (ℝ × ℝ), Nset F.1 ≠ Set.univ ∧ dirOf F.1 = v ∧
      offOf F.1 = levVal F0 ((v.1 ^ 2 + v.2 ^ 2) • coCLM (-1) 0) := by
  have hv0 : v ≠ 0 := by
    intro hcon
    rw [hcon, norm_zero] at hv
    exact zero_ne_one hv
  have hr : 0 < v.1 ^ 2 + v.2 ^ 2 := by
    rcases (by
      by_contra hcon
      push_neg at hcon
      exact hv0 (Prod.ext (by simpa using hcon.1) (by simpa using hcon.2)) :
        v.1 ≠ 0 ∨ v.2 ≠ 0) with h1 | h2
    · nlinarith [sq_nonneg v.2, sq_pos_of_ne_zero h1]
    · nlinarith [sq_nonneg v.1, sq_pos_of_ne_zero h2]
  set L := dirEquiv v hv0 with hL
  set G := comapEquiv L F0 with hG'
  have hG : IsMaximal G := comapEquiv_isMaximal L hF0
  have hcomp : ∀ u : (ℝ × ℝ) →L[ℝ] ℝ,
      (u.comp (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))) (0, 1) = u v := by
    intro u
    show u (L (0, 1)) = u v
    congr 1
    rw [hL, dirEquiv_apply]
    exact Prod.ext (by norm_num) (by norm_num)
  have hesc : IsEscapeDir (levVal G) v := by
    refine ⟨hv, fun u hu => ?_⟩
    rw [hG', levVal_comapEquiv]
    exact htop _ (by rw [hcomp]; exact hu)
  have hnp : Nset G ≠ Set.univ := by
    intro hcon
    have hu : coCLM v.1 v.2 ∈ Nset G := by rw [hcon]; trivial
    have hne := (mem_Nset_iff_levVal_ne hG _).mp hu
    refine hne.1 (hesc.2 _ ?_)
    rw [coCLM_apply]
    nlinarith
  have hdir : dirOf G = v := dirOf_eq_of_isEscapeDir hG hnp hesc
  refine ⟨⟨G, hG⟩, hnp, hdir, ?_⟩
  have hnorm : (normalCLM v).comp (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
      = (v.1 ^ 2 + v.2 ^ 2) • coCLM (-1) 0 := by
    refine ContinuousLinearMap.ext fun p => ?_
    show normalCLM v (L p) = _
    rw [normalCLM, ContinuousLinearMap.smul_apply, coCLM_apply, coCLM_apply, hL, dirEquiv_apply,
      smul_eq_mul]
    ring
  show offOf G = _
  rw [offOf, hdir, hG', levVal_comapEquiv, hnorm]

/-- **Part B, contract form: surjectivity.**  Every pair of a unit vector and an extended
real is the direction and offset of some non-principal maximal filter of the plane. -/
theorem boundaryMap_surjective (z : Metric.sphere (0 : ℝ × ℝ) 1 × EReal) :
    ∃ F : MaxFilter (ℝ × ℝ), Nset F.1 ≠ Set.univ ∧ boundaryMap F = z := by
  obtain ⟨⟨v, hvs⟩, e⟩ := z
  have hv : ‖v‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hvs
  have hv0 : v ≠ 0 := by
    intro hcon
    rw [hcon, norm_zero] at hv
    exact zero_ne_one hv
  have hr : 0 < v.1 ^ 2 + v.2 ^ 2 := by
    rcases (by
      by_contra hcon
      push_neg at hcon
      exact hv0 (Prod.ext (by simpa using hcon.1) (by simpa using hcon.2)) :
        v.1 ≠ 0 ∨ v.2 ≠ 0) with h1 | h2
    · nlinarith [sq_nonneg v.2, sq_pos_of_ne_zero h1]
    · nlinarith [sq_nonneg v.1, sq_pos_of_ne_zero h2]
  have hpack : ∀ (F : MaxFilter (ℝ × ℝ)), dirOf F.1 = v → offOf F.1 = e →
      boundaryMap F = ((⟨v, hvs⟩ : Metric.sphere (0 : ℝ × ℝ) 1), e) := by
    intro F h1 h2
    rw [boundaryMap, Prod.mk.injEq]
    exact ⟨Subtype.ext h1, h2⟩
  induction e using EReal.rec with
  | bot =>
      obtain ⟨F, hnp, hdir, hoff⟩ := exists_boundary_filter Gpar_isMaximal
        (fun u hu => levVal_of_lev_eq_empty (lev_Gpar_of_snd_pos hu)) hv
      refine ⟨F, hnp, hpack F hdir ?_⟩
      rw [hoff]
      refine levVal_smul_pos_of_bot Gpar_isMaximal hr ?_
      refine levVal_of_lev_eq_univ (lev_Gpar_of_snd_zero_fst_neg ?_ ?_)
      · rw [coCLM_apply]; ring
      · rw [coCLM_apply]; norm_num
  | top =>
      obtain ⟨F, hnp, hdir, hoff⟩ := exists_boundary_filter
        (comapEquiv_isMaximal reflCLM Gpar_isMaximal)
        (fun u hu => by
          rw [levVal_comapEquiv]
          refine levVal_of_lev_eq_empty (lev_Gpar_of_snd_pos ?_)
          show 0 < u (reflCLM (0, 1))
          rw [reflCLM_apply]
          simpa using hu) hv
      refine ⟨F, hnp, hpack F hdir ?_⟩
      rw [hoff]
      refine levVal_smul_pos_of_top (comapEquiv_isMaximal reflCLM Gpar_isMaximal) hr ?_
      rw [levVal_comapEquiv]
      refine levVal_of_lev_eq_empty (lev_Gpar_of_snd_zero_fst_pos ?_ ?_)
      · show (coCLM (-1) 0) (reflCLM (0, 1)) = 0
        rw [reflCLM_apply, coCLM_apply]
        norm_num
      · show 0 < (coCLM (-1) 0) (reflCLM (1, 0))
        rw [reflCLM_apply, coCLM_apply]
        norm_num
  | coe c =>
      obtain ⟨F, hnp, hdir, hoff⟩ := exists_boundary_filter
        (vlineFilter_isMaximal (c / (v.1 ^ 2 + v.2 ^ 2)))
        (fun u hu => levVal_vlineFilter_of_pos _ hu) hv
      refine ⟨F, hnp, hpack F hdir ?_⟩
      rw [hoff, levVal_smul_of_coe (vlineFilter_isMaximal _)
        (levVal_vlineFilter_normal (c / (v.1 ^ 2 + v.2 ^ 2)))]
      rw [mul_div_cancel₀ _ (ne_of_gt hr)]

end Surjectivity

/-! ### The continuity clause of Part B is false

The parametrization is a bijection from the boundary onto `S¹ × [-∞, +∞]`, but it is not
continuous on the non-principal locus: a continuous parametrization would descend to a
continuous injection of the boundary into a second countable space, which
`not_injective_of_continuous_of_secondCountable` forbids. -/

section Continuity

/-- The principal maximal filters of the plane. -/
def IsPrincipalFilter (F : MaxFilter (ℝ × ℝ)) : Prop := ∃ p : ℝ × ℝ, F = prin p

theorem not_isPrincipalFilter_iff {F : MaxFilter (ℝ × ℝ)} :
    ¬ IsPrincipalFilter F ↔ Nset F.1 ≠ Set.univ := by
  constructor
  · intro h hcon
    obtain ⟨p, hp⟩ := eq_principal_of_Nset_univ F.2 hcon
    exact h ⟨p, MaxFilter.ext hp⟩
  · intro h hp
    obtain ⟨p, rfl⟩ := hp
    exact h (Nset_univ_of_principal p)

/-- A class of the quotient lies in the boundary exactly when its filters are not
principal. -/
theorem mk_mem_boundarySet_iff {F : MaxFilter (ℝ × ℝ)} :
    T2Quotient.mk F ∈ boundarySet ↔ ¬ IsPrincipalFilter F := by
  constructor
  · intro h hp
    obtain ⟨p, rfl⟩ := hp
    exact h ⟨p, rfl⟩
  · intro h
    rw [not_isPrincipalFilter_iff] at h
    rintro ⟨p, hp⟩
    have hlev : ∀ u, levVal (prin p).1 u = levVal F.1 u := levVal_separates_quotient.mpr hp
    refine h (Set.eq_univ_of_forall fun u => ?_)
    rw [mem_Nset_iff_levVal_ne F.2, ← hlev u, levVal_prin]
    exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩

theorem isClosed_notPrincipal :
    IsClosed {F : MaxFilter (ℝ × ℝ) | ¬ IsPrincipalFilter F} := by
  have heq : {F : MaxFilter (ℝ × ℝ) | ¬ IsPrincipalFilter F}
      = T2Quotient.mk ⁻¹' boundarySet := by
    ext F
    exact mk_mem_boundarySet_iff.symm
  rw [heq]
  exact (isOpen_range_prinQ.isClosed_compl).preimage (T2Quotient.continuous_mk _)

/-- **The continuity clause of Part B is false.** The parametrization is not continuous on
the non-principal locus.

If it were, it would descend along the quotient map from the non-principal locus — compact,
because it is closed in the compact space of maximal filters — onto the boundary, giving a
continuous injection of the boundary into the second countable space
`S¹ × [-∞, +∞]`, which `not_injective_of_continuous_of_secondCountable` excludes. -/
theorem not_continuousOn_boundaryMap :
    ¬ ContinuousOn boundaryMap {F : MaxFilter (ℝ × ℝ) | ¬ IsPrincipalFilter F} := by
  intro hcont
  classical
  set S : Set (MaxFilter (ℝ × ℝ)) := {F : MaxFilter (ℝ × ℝ) | ¬ IsPrincipalFilter F} with hS
  have hScl : IsClosed S := isClosed_notPrincipal
  have hScompact : CompactSpace (↥S) := isCompact_iff_compactSpace.mp hScl.isCompact
  -- the quotient map from the non-principal locus onto the boundary
  have hmem : ∀ F : ↥S, T2Quotient.mk F.1 ∈ boundarySet := fun F =>
    mk_mem_boundarySet_iff.mpr F.2
  set q : (↥S) → (↥boundarySet) := fun F => ⟨T2Quotient.mk F.1, hmem F⟩ with hq
  have hqcont : Continuous q :=
    Continuous.subtype_mk ((T2Quotient.continuous_mk _).comp continuous_subtype_val) _
  have hqsurj : Function.Surjective q := by
    intro x
    obtain ⟨F, hF⟩ := T2Quotient.surjective_mk (MaxFilter (ℝ × ℝ)) x.1
    have hFS : F ∈ S := mk_mem_boundarySet_iff.mp (hF ▸ x.2)
    exact ⟨⟨F, hFS⟩, Subtype.ext hF⟩
  have hqquot : Topology.IsQuotientMap q :=
    (hqcont.isClosedMap).isQuotientMap hqcont hqsurj
  -- the parametrization, as a continuous map on the non-principal locus
  set g : (↥S) → Metric.sphere (0 : ℝ × ℝ) 1 × EReal := fun F => boundaryMap F.1 with hg
  have hgcont : Continuous g := continuousOn_iff_continuous_restrict.mp hcont
  -- it is constant on the fibres of `q`
  have hconst : ∀ F F' : ↥S, q F = q F' → g F = g F' := by
    intro F F' hFF
    have hmk : T2Quotient.mk F.1 = T2Quotient.mk F'.1 := congrArg Subtype.val hFF
    exact boundaryMap_eq_of_levVal_eq (levVal_separates_quotient.mpr hmk)
  set f : (↥boundarySet) → Metric.sphere (0 : ℝ × ℝ) 1 × EReal :=
    fun x => g (hqsurj x).choose with hf
  have hfq : ∀ F : ↥S, f (q F) = g F := by
    intro F
    exact hconst _ _ (hqsurj (q F)).choose_spec
  have hfcont : Continuous f := by
    rw [hqquot.continuous_iff]
    have : f ∘ q = g := funext hfq
    rw [this]
    exact hgcont
  refine not_injective_of_continuous_of_secondCountable hfcont ?_
  intro x y hxy
  obtain ⟨F, rfl⟩ := hqsurj x
  obtain ⟨F', rfl⟩ := hqsurj y
  rw [hfq, hfq] at hxy
  have hnp : Nset F.1.1 ≠ Set.univ := not_isPrincipalFilter_iff.mp F.2
  have hnp' : Nset F'.1.1 ≠ Set.univ := not_isPrincipalFilter_iff.mp F'.2
  exact Subtype.ext (boundaryMap_injective_on_quotient hnp hnp' hxy)

end Continuity

end PartB

end Space

end ConvexFilter
