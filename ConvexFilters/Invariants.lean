import ConvexFilters.Levels

/-!
# Convex filters: the invariants `Nset`, `Mset`, `Eset`, `Dset`, `Qset`

For a maximal convex filter `F`, the set `Nset F` of functionals with finite support
number is a linear subspace on which `sig F` is linear (Proposition 2.5(1),(3)), the set
`Mset F` is a subspace of `Nset F`, and `Qset F = Eset F ∪ Dset F` is a positivity cone
compatible with `Mset F` (Proposition 2.5(4)).
-/

namespace ConvexFilter

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {F : ConvexFilter V}

/-! ### Elementary closure properties -/

theorem halfLE_add_mem {u v : V →L[ℝ] ℝ} {s t : ℝ}
    (hu : halfLE u s ∈ F.carrier) (hv : halfLE v t ∈ F.carrier) :
    halfLE (u + v) (s + t) ∈ F.carrier :=
  F.mem_of_superset (F.inter_mem hu hv) (isClosed_halfLE _ _) (convex_halfLE _ _)
    (halfLE_inter_subset_add u v s t)

theorem mem_lev_add {u v : V →L[ℝ] ℝ} {s t : ℝ} (hu : s ∈ lev F u) (hv : t ∈ lev F v) :
    s + t ∈ lev F (u + v) :=
  halfLE_add_mem hu hv

theorem lev_neg_add (u v : V →L[ℝ] ℝ) : lev F (-(u + v)) = lev F (-u + -v) := by
  rw [neg_add]

/-! ### `Nset` is a subspace -/

theorem zero_mem_Nset : (0 : V →L[ℝ] ℝ) ∈ Nset F := by
  constructor
  · rw [lev_zero]
    intro h
    have : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr le_rfl
    rw [h] at this
    exact this
  · rw [neg_zero, lev_zero]
    intro h
    have : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr le_rfl
    rw [h] at this
    exact this

theorem Nset_add (hF : IsMaximal F) {u v : V →L[ℝ] ℝ}
    (hu : u ∈ Nset F) (hv : v ∈ Nset F) : u + v ∈ Nset F := by
  obtain ⟨s, hs⟩ := lev_nonempty_of_mem_Nset hu
  obtain ⟨t, ht⟩ := lev_nonempty_of_mem_Nset hv
  obtain ⟨s', hs'⟩ := lev_nonempty_of_mem_Nset (Nset_neg hu)
  obtain ⟨t', ht'⟩ := lev_nonempty_of_mem_Nset (Nset_neg hv)
  constructor
  · exact Set.nonempty_iff_ne_empty.mp ⟨s + t, mem_lev_add hs ht⟩
  · rw [lev_neg_add]
    exact Set.nonempty_iff_ne_empty.mp ⟨s' + t', mem_lev_add hs' ht'⟩

theorem mem_lev_smul_iff {c : ℝ} (hc : 0 < c) {u : V →L[ℝ] ℝ} {t : ℝ} :
    t ∈ lev F (c • u) ↔ t / c ∈ lev F u := by
  have h : halfLE (c • u) t = halfLE u (t / c) := by
    have := halfLE_smul hc u (t / c)
    rwa [mul_div_cancel₀ _ (ne_of_gt hc)] at this
  rw [mem_lev_iff, mem_lev_iff, h]

theorem smul_neg_neg_eq {c : ℝ} (u : V →L[ℝ] ℝ) : (-c) • (-u) = c • u := by
  rw [smul_neg, neg_smul, neg_neg]

theorem Nset_smul {c : ℝ} {u : V →L[ℝ] ℝ} (hu : u ∈ Nset F) : c • u ∈ Nset F := by
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · have hc' : 0 < -c := by linarith
    have hu' : -u ∈ Nset F := Nset_neg hu
    obtain ⟨s, hs⟩ := lev_nonempty_of_mem_Nset hu'
    obtain ⟨t, ht⟩ := lev_nonempty_of_mem_Nset (Nset_neg hu')
    constructor
    · refine Set.nonempty_iff_ne_empty.mp ⟨(-c) * s, ?_⟩
      rw [← smul_neg_neg_eq u, mem_lev_smul_iff hc', mul_div_cancel_left₀ _ (ne_of_gt hc')]
      exact hs
    · refine Set.nonempty_iff_ne_empty.mp ⟨(-c) * t, ?_⟩
      rw [← smul_neg_neg_eq u, ← smul_neg, mem_lev_smul_iff hc',
        mul_div_cancel_left₀ _ (ne_of_gt hc')]
      exact ht
  · simpa using (zero_mem_Nset : (0 : V →L[ℝ] ℝ) ∈ Nset F)
  · obtain ⟨s, hs⟩ := lev_nonempty_of_mem_Nset hu
    obtain ⟨t, ht⟩ := lev_nonempty_of_mem_Nset (Nset_neg hu)
    constructor
    · refine Set.nonempty_iff_ne_empty.mp ⟨c * s, ?_⟩
      rw [mem_lev_smul_iff hc, mul_div_cancel_left₀ _ (ne_of_gt hc)]
      exact hs
    · refine Set.nonempty_iff_ne_empty.mp ⟨c * t, ?_⟩
      rw [← smul_neg, mem_lev_smul_iff hc, mul_div_cancel_left₀ _ (ne_of_gt hc)]
      exact ht

/-- The subspace of functionals with finite support number. -/
noncomputable def NsubmoduleOf (F : ConvexFilter V) (hF : IsMaximal F) :
    Submodule ℝ (V →L[ℝ] ℝ) where
  carrier := Nset F
  add_mem' := fun hu hv => Nset_add hF hu hv
  zero_mem' := zero_mem_Nset
  smul_mem' := fun _ _ hu => Nset_smul hu

theorem coe_NsubmoduleOf (hF : IsMaximal F) :
    ((NsubmoduleOf F hF : Submodule ℝ (V →L[ℝ] ℝ)) : Set (V →L[ℝ] ℝ)) = Nset F := rfl

/-! ### `sig` is linear on `Nset` -/

theorem sig_add_le (hF : IsMaximal F) {u v : V →L[ℝ] ℝ}
    (hu : u ∈ Nset F) (hv : v ∈ Nset F) : sig F (u + v) ≤ sig F u + sig F v := by
  have huv : u + v ∈ Nset F := Nset_add hF hu hv
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have h₁ : sig F u + ε / 2 ∈ lev F u := mem_lev_of_sig_lt hF hu (by linarith)
  have h₂ : sig F v + ε / 2 ∈ lev F v := mem_lev_of_sig_lt hF hv (by linarith)
  have h₃ := mem_lev_add h₁ h₂
  have := sig_le_of_mem_lev hF huv h₃
  linarith

theorem sig_add (hF : IsMaximal F) {u v : V →L[ℝ] ℝ}
    (hu : u ∈ Nset F) (hv : v ∈ Nset F) : sig F (u + v) = sig F u + sig F v := by
  have huv : u + v ∈ Nset F := Nset_add hF hu hv
  refine le_antisymm (sig_add_le hF hu hv) ?_
  have hneg := sig_add_le hF (Nset_neg hu) (Nset_neg hv)
  rw [← neg_add] at hneg
  rw [sig_neg hF huv, sig_neg hF hu, sig_neg hF hv] at hneg
  linarith

theorem sig_smul_pos (hF : IsMaximal F) {u : V →L[ℝ] ℝ} (hu : u ∈ Nset F) {c : ℝ}
    (hc : 0 < c) : sig F (c • u) = c * sig F u := by
  have hcu : c • u ∈ Nset F := Nset_smul hu
  refine le_antisymm ?_ ?_
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have hεc : 0 < ε / c := div_pos hε hc
    have h₁ : sig F u + ε / c ∈ lev F u := mem_lev_of_sig_lt hF hu (by linarith)
    have h₂ : c * (sig F u + ε / c) ∈ lev F (c • u) := by
      rw [mem_lev_smul_iff hc, mul_div_cancel_left₀ _ (ne_of_gt hc)]
      exact h₁
    have h₃ := sig_le_of_mem_lev hF hcu h₂
    have heq : c * (sig F u + ε / c) = c * sig F u + ε := by field_simp
    rwa [heq] at h₃
  · by_contra hcon
    push_neg at hcon
    obtain ⟨t, ht₁, ht₂⟩ : ∃ t : ℝ, sig F (c • u) < t ∧ t < c * sig F u :=
      ⟨(sig F (c • u) + c * sig F u) / 2, by linarith, by linarith⟩
    have hmem : t ∈ lev F (c • u) := mem_lev_of_sig_lt hF hcu ht₁
    rw [mem_lev_smul_iff hc] at hmem
    have hlt : t / c < sig F u := by
      rw [div_lt_iff₀ hc]
      linarith [mul_comm c (sig F u)]
    exact not_mem_lev_of_lt_sig hF hu hlt hmem

theorem sig_smul (hF : IsMaximal F) {u : V →L[ℝ] ℝ} (hu : u ∈ Nset F) (c : ℝ) :
    sig F (c • u) = c * sig F u := by
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · have hc' : 0 < -c := by linarith
    have hu' : -u ∈ Nset F := Nset_neg hu
    rw [← smul_neg_neg_eq u, sig_smul_pos hF hu' hc', sig_neg hF hu]
    ring
  · rw [zero_smul, zero_mul, sig, lev_zero]
    exact csInf_Ici
  · exact sig_smul_pos hF hu hc

/-! ### `Mset` -/

theorem hyperplane_subset_halfLE (u : V →L[ℝ] ℝ) (t : ℝ) : hyperplane u t ⊆ halfLE u t :=
  fun _ hx => le_of_eq hx

theorem hyperplane_subset_halfGE (u : V →L[ℝ] ℝ) (t : ℝ) : hyperplane u t ⊆ halfGE u t :=
  fun _ hx => ge_of_eq hx

theorem halfLE_mem_of_hyperplane_mem {u : V →L[ℝ] ℝ} {t : ℝ} (h : hyperplane u t ∈ F.carrier) :
    halfLE u t ∈ F.carrier :=
  F.mem_of_superset h (isClosed_halfLE u t) (convex_halfLE u t) (hyperplane_subset_halfLE u t)

theorem halfGE_mem_of_hyperplane_mem {u : V →L[ℝ] ℝ} {t : ℝ} (h : hyperplane u t ∈ F.carrier) :
    halfGE u t ∈ F.carrier :=
  F.mem_of_superset h (isClosed_halfGE u t) (convex_halfGE u t) (hyperplane_subset_halfGE u t)

theorem sig_eq_of_hyperplane_mem {u : V →L[ℝ] ℝ} {t : ℝ} (h : hyperplane u t ∈ F.carrier) :
    sig F u = t := by
  have hle : halfLE u t ∈ F.carrier := halfLE_mem_of_hyperplane_mem h
  have hge : halfGE u t ∈ F.carrier := halfGE_mem_of_hyperplane_mem h
  have hlow : ∀ x ∈ lev F u, t ≤ x := by
    intro x hx
    by_contra hlt
    push_neg at hlt
    have hdisj : halfLE u x ∩ halfGE u t = ∅ := disjoint_halfLE_halfGE hlt u
    exact F.empty_not_mem (hdisj ▸ F.inter_mem hx hge)
  refine le_antisymm (csInf_le ⟨t, hlow⟩ hle) (le_csInf ⟨t, hle⟩ hlow)

theorem Mset_subset_Nset (hF : IsMaximal F) : Mset F ⊆ Nset F := by
  rintro u ⟨t, ht⟩
  constructor
  · exact Set.nonempty_iff_ne_empty.mp ⟨t, halfLE_mem_of_hyperplane_mem ht⟩
  · refine Set.nonempty_iff_ne_empty.mp ⟨-t, ?_⟩
    rw [mem_lev_neg_iff, neg_neg]
    exact halfGE_mem_of_hyperplane_mem ht

theorem Mset_eq (hF : IsMaximal F) :
    Mset F = {u : V →L[ℝ] ℝ | u ∈ Nset F ∧ hyperplane u (sig F u) ∈ F.carrier} := by
  ext u
  constructor
  · intro hu
    obtain ⟨t, ht⟩ := id hu
    have hsig : sig F u = t := sig_eq_of_hyperplane_mem ht
    exact ⟨Mset_subset_Nset hF hu, by rw [hsig]; exact ht⟩
  · rintro ⟨-, h⟩
    exact ⟨sig F u, h⟩

theorem Mset_neg {u : V →L[ℝ] ℝ} (hu : u ∈ Mset F) : -u ∈ Mset F := by
  obtain ⟨t, ht⟩ := hu
  exact ⟨-t, by rw [hyperplane_neg]; exact ht⟩

theorem Mset_add (hF : IsMaximal F) {u v : V →L[ℝ] ℝ}
    (hu : u ∈ Mset F) (hv : v ∈ Mset F) : u + v ∈ Mset F := by
  obtain ⟨s, hs⟩ := hu
  obtain ⟨t, ht⟩ := hv
  refine ⟨s + t, F.mem_of_superset (F.inter_mem hs ht) (isClosed_hyperplane _ _)
    (ConvexFilter.convex_hyperplane _ _) ?_⟩
  rintro x ⟨hx₁, hx₂⟩
  have h₁ : u x = s := hx₁
  have h₂ : v x = t := hx₂
  show (u + v) x = s + t
  simp [h₁, h₂]

theorem hyperplane_smul {c : ℝ} (hc : c ≠ 0) (u : V →L[ℝ] ℝ) (t : ℝ) :
    hyperplane (c • u) (c * t) = hyperplane u t := by
  ext x
  simp only [hyperplane, Set.mem_setOf_eq, ContinuousLinearMap.smul_apply, smul_eq_mul,
    mul_eq_mul_left_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h hc
  · intro h; exact Or.inl h

theorem Mset_smul (hF : IsMaximal F) {c : ℝ} {u : V →L[ℝ] ℝ} (hu : u ∈ Mset F) :
    c • u ∈ Mset F := by
  rcases eq_or_ne c 0 with rfl | hc
  · refine ⟨0, ?_⟩
    have : hyperplane (0 : V →L[ℝ] ℝ) 0 = (Set.univ : Set V) := by
      ext x; simp [hyperplane]
    rw [zero_smul, this]
    exact F.univ_mem
  · obtain ⟨t, ht⟩ := hu
    exact ⟨c * t, by rw [hyperplane_smul hc]; exact ht⟩

/-- The subspace `Mset F` of `V →L[ℝ] ℝ`. -/
noncomputable def MsubmoduleOf (F : ConvexFilter V) (hF : IsMaximal F) :
    Submodule ℝ (V →L[ℝ] ℝ) where
  carrier := Mset F
  add_mem' := fun hu hv => Mset_add hF hu hv
  zero_mem' := by
    refine ⟨0, ?_⟩
    have : hyperplane (0 : V →L[ℝ] ℝ) 0 = (Set.univ : Set V) := by
      ext x; simp [hyperplane]
    rw [this]
    exact F.univ_mem
  smul_mem' := fun _ _ hu => Mset_smul hF hu

theorem coe_MsubmoduleOf (hF : IsMaximal F) :
    ((MsubmoduleOf F hF : Submodule ℝ (V →L[ℝ] ℝ)) : Set (V →L[ℝ] ℝ)) = Mset F := rfl

theorem sig_mem_lev_of_mem_Mset {u : V →L[ℝ] ℝ} (hu : u ∈ Mset F) : sig F u ∈ lev F u := by
  obtain ⟨t, ht⟩ := hu
  rw [sig_eq_of_hyperplane_mem ht]
  exact halfLE_mem_of_hyperplane_mem ht

theorem not_mem_Dset_of_mem_Mset {u : V →L[ℝ] ℝ} (hu : u ∈ Mset F) : u ∉ Dset F := by
  rintro ⟨-, h⟩
  exact h (sig_mem_lev_of_mem_Mset hu)

/-! ### `Eset`, `Dset`, `Qset` -/

theorem Qset_eq_Eset_union_Dset (hF : IsMaximal F) : Qset F = Eset F ∪ Dset F := by
  ext u
  constructor
  · rintro ⟨hnu, hopen⟩
    rcases eq_or_ne (lev F u) ∅ with h | h
    · exact Or.inl h
    · have hN : u ∈ Nset F := (mem_Nset_iff hF u).mpr ⟨h, hnu⟩
      refine Or.inr ⟨hN, fun hmem => ?_⟩
      obtain ⟨t', ht', hlt⟩ := hopen _ hmem
      exact not_mem_lev_of_lt_sig hF hN hlt ht'
  · rintro (h | ⟨hN, hsig⟩)
    · refine ⟨?_, ?_⟩
      · rw [h]
        intro hcon
        have : (0 : ℝ) ∈ (∅ : Set ℝ) := hcon ▸ Set.mem_univ (0 : ℝ)
        exact this
      · intro t ht
        rw [h] at ht
        exact absurd ht (Set.notMem_empty t)
    · have hshape : lev F u = Set.Ioi (sig F u) := by
        rcases lev_eq_of_mem_Nset hF hN with h | h
        · exact h
        · exact absurd (h ▸ Set.self_mem_Ici) hsig
      refine ⟨?_, ?_⟩
      · rw [hshape]
        intro hcon
        have : sig F u ∈ Set.Ioi (sig F u) := hcon ▸ Set.mem_univ _
        exact absurd this (by simp)
      · intro t ht
        rw [hshape] at ht ⊢
        exact ⟨(sig F u + t) / 2, by simp only [Set.mem_Ioi]; linarith [Set.mem_Ioi.mp ht],
          by linarith [Set.mem_Ioi.mp ht]⟩

theorem zero_not_mem_Qset : (0 : V →L[ℝ] ℝ) ∉ Qset F := by
  rintro ⟨-, hopen⟩
  have h0 : (0 : ℝ) ∈ lev F 0 := by rw [lev_zero]; exact Set.mem_Ici.mpr le_rfl
  obtain ⟨t', ht', hlt⟩ := hopen 0 h0
  rw [lev_zero] at ht'
  exact absurd (Set.mem_Ici.mp ht') (not_le.mpr hlt)

theorem Eset_subset_Qset (hF : IsMaximal F) : Eset F ⊆ Qset F := by
  rw [Qset_eq_Eset_union_Dset hF]
  exact Set.subset_union_left

theorem Dset_subset_Qset (hF : IsMaximal F) : Dset F ⊆ Qset F := by
  rw [Qset_eq_Eset_union_Dset hF]
  exact Set.subset_union_right

theorem Qset_not_neg (hF : IsMaximal F) {u : V →L[ℝ] ℝ} (hu : u ∈ Qset F) :
    -u ∉ Qset F := by
  rw [Qset_eq_Eset_union_Dset hF] at hu ⊢
  intro hnu
  rcases hu with hE | ⟨hN, hsig⟩
  · have h1 : lev F (-u) = Set.univ := lev_univ_of_lev_empty hF hE
    rcases hnu with hE' | hD'
    · rw [hE'] at h1
      exact absurd h1 Set.empty_ne_univ
    · exact absurd h1 ((mem_Nset_iff hF (-u)).mp hD'.1).2
  · rcases hnu with hE' | hD'
    · exact (Nset_neg hN).1 hE'
    · refine hD'.2 ?_
      have hmem : (-(sig F u)) ∈ lev F (-u) := by
        rw [mem_lev_neg_iff, neg_neg]
        exact halfGE_of_not_halfLE hF hsig
      rwa [sig_neg hF hN]

theorem Eset_add (hF : IsMaximal F) {u v : V →L[ℝ] ℝ}
    (hu : u ∈ Eset F) (hv : v ∈ Eset F) : u + v ∈ Eset F := by
  have hu' : lev F (-u) = Set.univ := lev_univ_of_lev_empty hF hu
  have hv' : lev F (-v) = Set.univ := lev_univ_of_lev_empty hF hv
  show lev F (u + v) = ∅
  rw [Set.eq_empty_iff_forall_notMem]
  intro t ht
  have h₁ : (-t - 1) ∈ lev F (-u) := hu' ▸ Set.mem_univ _
  have h₂ : (0 : ℝ) ∈ lev F (-v) := hv' ▸ Set.mem_univ _
  have h₃ : (-t - 1) + 0 ∈ lev F (-u + -v) := mem_lev_add h₁ h₂
  rw [← lev_neg_add] at h₃
  have := add_nonneg_of_mem_lev ht h₃
  linarith

theorem Eset_add_Nset (hF : IsMaximal F) {u w : V →L[ℝ] ℝ}
    (hu : u ∈ Eset F) (hw : w ∈ Nset F) : u + w ∈ Eset F := by
  have hu' : lev F (-u) = Set.univ := lev_univ_of_lev_empty hF hu
  obtain ⟨b, hb⟩ := lev_nonempty_of_mem_Nset (Nset_neg hw)
  show lev F (u + w) = ∅
  rw [Set.eq_empty_iff_forall_notMem]
  intro t ht
  have h₁ : (-t - b - 1) ∈ lev F (-u) := hu' ▸ Set.mem_univ _
  have h₃ : (-t - b - 1) + b ∈ lev F (-u + -w) := mem_lev_add h₁ hb
  rw [← lev_neg_add] at h₃
  have := add_nonneg_of_mem_lev ht h₃
  linarith

theorem Dset_add (hF : IsMaximal F) {u v : V →L[ℝ] ℝ}
    (hu : u ∈ Dset F) (hv : v ∈ Dset F) : u + v ∈ Dset F := by
  obtain ⟨hNu, hsu⟩ := hu
  obtain ⟨hNv, hsv⟩ := hv
  refine ⟨Nset_add hF hNu hNv, fun hmem => ?_⟩
  -- the half-spaces above the support numbers belong to `F`
  have hgu : halfGE u (sig F u) ∈ F.carrier := halfGE_of_not_halfLE hF hsu
  have hgv : halfGE v (sig F v) ∈ F.carrier := halfGE_of_not_halfLE hF hsv
  have hle : halfLE (u + v) (sig F u + sig F v) ∈ F.carrier := by
    rw [← sig_add hF hNu hNv]
    exact hmem
  -- their intersection lies in a level hyperplane of `u`
  have hyp : hyperplane u (sig F u) ∈ F.carrier := by
    refine F.mem_of_superset (F.inter_mem (F.inter_mem hle hgu) hgv) (isClosed_hyperplane _ _)
      (ConvexFilter.convex_hyperplane _ _) ?_
    rintro x ⟨⟨hx₁, hx₂⟩, hx₃⟩
    have e₁ : u x + v x ≤ sig F u + sig F v := hx₁
    have e₂ : sig F u ≤ u x := hx₂
    have e₃ : sig F v ≤ v x := hx₃
    show u x = sig F u
    linarith
  exact not_mem_Dset_of_mem_Mset (⟨sig F u, hyp⟩ : u ∈ Mset F) ⟨hNu, hsu⟩

theorem Dset_add_Mset (hF : IsMaximal F) {u w : V →L[ℝ] ℝ}
    (hu : u ∈ Dset F) (hw : w ∈ Mset F) : u + w ∈ Dset F := by
  obtain ⟨hNu, hsu⟩ := hu
  have hNw : w ∈ Nset F := Mset_subset_Nset hF hw
  refine ⟨Nset_add hF hNu hNw, fun hmem => ?_⟩
  have hyp : hyperplane w (sig F w) ∈ F.carrier := by
    rw [Mset_eq hF] at hw
    exact hw.2
  have hle : halfLE (u + w) (sig F u + sig F w) ∈ F.carrier := by
    rw [← sig_add hF hNu hNw]
    exact hmem
  have : halfLE u (sig F u) ∈ F.carrier := by
    refine F.mem_of_superset (F.inter_mem hle hyp) (isClosed_halfLE _ _) (convex_halfLE _ _) ?_
    rintro x ⟨hx₁, hx₂⟩
    have e₁ : u x + w x ≤ sig F u + sig F w := hx₁
    have e₂ : w x = sig F w := hx₂
    show u x ≤ sig F u
    linarith
  exact hsu this

theorem Qset_add (hF : IsMaximal F) {u v : V →L[ℝ] ℝ}
    (hu : u ∈ Qset F) (hv : v ∈ Qset F) : u + v ∈ Qset F := by
  rw [Qset_eq_Eset_union_Dset hF] at hu hv ⊢
  rcases hu with hu | hu
  · rcases hv with hv | hv
    · exact Or.inl (Eset_add hF hu hv)
    · exact Or.inl (Eset_add_Nset hF hu hv.1)
  · rcases hv with hv | hv
    · rw [add_comm]
      exact Or.inl (Eset_add_Nset hF hv hu.1)
    · exact Or.inr (Dset_add hF hu hv)

theorem Qset_smul (hF : IsMaximal F) {c : ℝ} (hc : 0 < c) {u : V →L[ℝ] ℝ}
    (hu : u ∈ Qset F) : c • u ∈ Qset F := by
  rw [Qset_eq_Eset_union_Dset hF] at hu ⊢
  rcases hu with hu | ⟨hN, hsig⟩
  · refine Or.inl ?_
    show lev F (c • u) = ∅
    rw [Set.eq_empty_iff_forall_notMem]
    intro t ht
    rw [mem_lev_smul_iff hc] at ht
    rw [hu] at ht
    exact ht
  · refine Or.inr ⟨Nset_smul hN, fun hmem => ?_⟩
    rw [sig_smul hF hN c, mem_lev_smul_iff hc, mul_div_cancel_left₀ _ (ne_of_gt hc)] at hmem
    exact hsig hmem

theorem Qset_add_Mset (hF : IsMaximal F) {u w : V →L[ℝ] ℝ}
    (hu : u ∈ Qset F) (hw : w ∈ Mset F) : u + w ∈ Qset F := by
  rw [Qset_eq_Eset_union_Dset hF] at hu ⊢
  rcases hu with hu | hu
  · exact Or.inl (Eset_add_Nset hF hu (Mset_subset_Nset hF hw))
  · exact Or.inr (Dset_add_Mset hF hu hw)

/-! ### The decomposition of the dual (Proposition 2.5(4)) -/

/-- `Qset F` is exactly the set of functionals whose level set is open and proper.
This identifies the definition of `Qset` used here with the one used in the paper. -/
theorem Qset_eq_isOpen (hF : IsMaximal F) :
    Qset F = {u : V →L[ℝ] ℝ | IsOpen (lev F u) ∧ lev F u ≠ Set.univ} := by
  ext u
  simp only [Qset, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hnu, hop⟩
    refine ⟨?_, hnu⟩
    rcases lev_shape (F := F) u with h | h | ⟨s, h⟩ | ⟨s, h⟩
    · rw [h]; exact isOpen_empty
    · exact absurd h hnu
    · rw [h]; exact isOpen_Ioi
    · exfalso
      obtain ⟨t', ht', hlt⟩ := hop s (by rw [h]; exact Set.self_mem_Ici)
      rw [h] at ht'
      exact absurd (Set.mem_Ici.mp ht') (not_le.mpr hlt)
  · rintro ⟨hop, hnu⟩
    refine ⟨hnu, fun t ht => ?_⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hop t ht
    refine ⟨t - ε / 2, hball ?_, by linarith⟩
    rw [Metric.mem_ball, Real.dist_eq, show t - ε / 2 - t = -(ε / 2) by ring, abs_neg,
      abs_of_pos (by linarith)]
    linarith

/-- A functional whose level hyperplane belongs to `F` is not in the positivity cone. -/
theorem Mset_disjoint_Qset (hF : IsMaximal F) {u : V →L[ℝ] ℝ} (hu : u ∈ Mset F) :
    u ∉ Qset F := by
  rw [Qset_eq_Eset_union_Dset hF]
  rintro (hE | hD)
  · exact ((Mset_subset_Nset hF hu).1) hE
  · exact not_mem_Dset_of_mem_Mset hu hD

/-- Every functional lies in `Qset F`, in `-Qset F`, or in `Mset F`. -/
theorem mem_Qset_or_neg_or_Mset (hF : IsMaximal F) (u : V →L[ℝ] ℝ) :
    u ∈ Qset F ∨ -u ∈ Qset F ∨ u ∈ Mset F := by
  by_cases hu : u ∈ Qset F
  · exact Or.inl hu
  by_cases hnu : -u ∈ Qset F
  · exact Or.inr (Or.inl hnu)
  refine Or.inr (Or.inr ?_)
  rw [Qset_eq_Eset_union_Dset hF, Set.mem_union, not_or] at hu hnu
  obtain ⟨huE, huD⟩ := hu
  obtain ⟨hnuE, hnuD⟩ := hnu
  have hN : u ∈ Nset F := ⟨huE, hnuE⟩
  have hN' : -u ∈ Nset F := Nset_neg hN
  have hsig : sig F u ∈ lev F u := by
    by_contra hcon
    exact huD ⟨hN, hcon⟩
  have hsig' : sig F (-u) ∈ lev F (-u) := by
    by_contra hcon
    exact hnuD ⟨hN', hcon⟩
  rw [sig_neg hF hN, mem_lev_neg_iff, neg_neg] at hsig'
  refine ⟨sig F u, ?_⟩
  rw [← halfLE_inter_halfGE u (sig F u)]
  exact F.inter_mem hsig hsig'

/-- Proposition 2.5(4): `Mset F` is the complement of `Qset F ∪ -Qset F`. Together with
`Qset_not_neg` this is the decomposition of the dual into `Qset F`, `-Qset F` and
`Mset F`. -/
theorem Mset_eq_compl_Qset (hF : IsMaximal F) :
    Mset F = {u : V →L[ℝ] ℝ | u ∉ Qset F ∧ -u ∉ Qset F} := by
  ext u
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hu
    exact ⟨Mset_disjoint_Qset hF hu, Mset_disjoint_Qset hF (Mset_neg hu)⟩
  · rintro ⟨h₁, h₂⟩
    rcases mem_Qset_or_neg_or_Mset hF u with h | h | h
    · exact absurd h h₁
    · exact absurd h h₂
    · exact h

end ConvexFilter
