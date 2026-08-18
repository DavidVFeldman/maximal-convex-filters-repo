import ConvexFilters.Basic

/-!
# Convex filters: level sets, the dichotomy, and the support number

This file studies the level set `lev F u = {t | {u ≤ t} ∈ F}`. It is an upper set of `ℝ`,
hence of one of four shapes (`∅`, `univ`, `Set.Ioi s`, `Set.Ici s`). For maximal filters
the dichotomy `halfLE u t ∈ F ∨ halfGE u t ∈ F` holds (Lemma 2.3), and on `Nset F` the
support number `sig` is odd (Proposition 2.5(2)).
-/

namespace ConvexFilter

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {F : ConvexFilter V}

/-! ### Level sets -/

theorem mem_lev_iff {u : V →L[ℝ] ℝ} {t : ℝ} : t ∈ lev F u ↔ halfLE u t ∈ F.carrier := Iff.rfl

theorem mem_lev_neg_iff {u : V →L[ℝ] ℝ} {t : ℝ} :
    t ∈ lev F (-u) ↔ halfGE u (-t) ∈ F.carrier := by
  rw [mem_lev_iff, ← halfLE_neg u (-t), neg_neg]

theorem lev_isUpperSet (u : V →L[ℝ] ℝ) : IsUpperSet (lev F u) := by
  intro a b hab ha
  refine F.mem_of_superset ha (isClosed_halfLE u b) (convex_halfLE u b) ?_
  intro x hx
  exact le_trans hx hab

theorem lev_zero : lev F 0 = Set.Ici (0 : ℝ) := by
  ext t
  simp only [mem_lev_iff, Set.mem_Ici]
  constructor
  · intro ht
    by_contra hneg
    push_neg at hneg
    have : halfLE (0 : V →L[ℝ] ℝ) t = (∅ : Set V) := by
      ext x
      simp [halfLE, not_le.mpr hneg]
    exact F.empty_not_mem (this ▸ ht)
  · intro ht
    have : halfLE (0 : V →L[ℝ] ℝ) t = (Set.univ : Set V) := by
      ext x
      simp [halfLE, ht]
    exact this ▸ F.univ_mem

theorem lev_shape (u : V →L[ℝ] ℝ) :
    lev F u = ∅ ∨ lev F u = Set.univ ∨
      (∃ s : ℝ, lev F u = Set.Ioi s) ∨ (∃ s : ℝ, lev F u = Set.Ici s) := by
  rcases Set.eq_empty_or_nonempty (lev F u) with h | hne
  · exact Or.inl h
  rcases eq_or_ne (lev F u) Set.univ with h | hnu
  · exact Or.inr (Or.inl h)
  -- the level set is nonempty, bounded below, and an upper set
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r ∉ lev F u := by
    by_contra hcon
    push_neg at hcon
    exact hnu (Set.eq_univ_of_forall hcon)
  have hbdd : BddBelow (lev F u) := by
    refine ⟨r, fun x hx => ?_⟩
    by_contra hlt
    push_neg at hlt
    exact hr (lev_isUpperSet u hlt.le hx)
  set s : ℝ := sInf (lev F u) with hs
  have hsub : lev F u ⊆ Set.Ici s := fun x hx => csInf_le hbdd hx
  have hIoi : Set.Ioi s ⊆ lev F u := by
    intro t ht
    obtain ⟨x, hx, hxt⟩ := exists_lt_of_csInf_lt hne ht
    exact lev_isUpperSet u hxt.le hx
  by_cases hmem : s ∈ lev F u
  · refine Or.inr (Or.inr (Or.inr ⟨s, ?_⟩))
    refine Set.Subset.antisymm hsub ?_
    intro t ht
    rcases eq_or_lt_of_le (Set.mem_Ici.mp ht) with rfl | hlt
    · exact hmem
    · exact hIoi hlt
  · refine Or.inr (Or.inr (Or.inl ⟨s, ?_⟩))
    refine Set.Subset.antisymm (fun t ht => ?_) hIoi
    rcases eq_or_lt_of_le (Set.mem_Ici.mp (hsub ht)) with rfl | hlt
    · exact absurd ht hmem
    · exact hlt

/-! ### The dichotomy (Lemma 2.3) -/

theorem halfLE_or_halfGE (hF : IsMaximal F) (u : V →L[ℝ] ℝ) (t : ℝ) :
    halfLE u t ∈ F.carrier ∨ halfGE u t ∈ F.carrier := by
  by_cases h : halfLE u t ∈ F.carrier
  · exact Or.inl h
  refine Or.inr ?_
  obtain ⟨D, hD, hdisj⟩ := (isMaximal_iff F).mp hF (isClosed_halfLE u t) (convex_halfLE u t) h
  refine F.mem_of_superset hD (isClosed_halfGE u t) (convex_halfGE u t) ?_
  intro x hx
  by_contra hxg
  simp only [halfGE, Set.mem_setOf_eq, not_le] at hxg
  have : x ∈ halfLE u t ∩ D := ⟨hxg.le, hx⟩
  rw [hdisj] at this
  exact this

theorem halfGE_of_not_halfLE (hF : IsMaximal F) {u : V →L[ℝ] ℝ} {t : ℝ}
    (h : halfLE u t ∉ F.carrier) : halfGE u t ∈ F.carrier :=
  (halfLE_or_halfGE hF u t).resolve_left h

/-! ### Properness constraints on level sets -/

theorem add_nonneg_of_mem_lev {u : V →L[ℝ] ℝ} {t r : ℝ} (ht : t ∈ lev F u)
    (hr : r ∈ lev F (-u)) : 0 ≤ t + r := by
  obtain ⟨x, hx₁, hx₂⟩ := nonempty_of_mem (F.inter_mem ht hr)
  have h₁ : u x ≤ t := hx₁
  have h₂ : -u x ≤ r := hx₂
  linarith

theorem lev_empty_of_lev_univ {u : V →L[ℝ] ℝ} (h : lev F u = Set.univ) : lev F (-u) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro r hr
  have ht : (-r - 1) ∈ lev F u := h ▸ Set.mem_univ _
  have := add_nonneg_of_mem_lev ht hr
  linarith

theorem not_lev_univ_and_univ (u : V →L[ℝ] ℝ) :
    ¬(lev F u = Set.univ ∧ lev F (-u) = Set.univ) := by
  rintro ⟨h₁, h₂⟩
  have : lev F (-u) = ∅ := lev_empty_of_lev_univ h₁
  rw [h₂] at this
  exact absurd (this ▸ Set.mem_univ (0 : ℝ)) (Set.notMem_empty 0)

theorem lev_univ_of_lev_empty (hF : IsMaximal F) {u : V →L[ℝ] ℝ}
    (h : lev F u = ∅) : lev F (-u) = Set.univ := by
  refine Set.eq_univ_of_forall fun t => ?_
  rw [mem_lev_neg_iff]
  refine halfGE_of_not_halfLE hF ?_
  intro hmem
  have : (-t) ∈ lev F u := hmem
  rw [h] at this
  exact this

/-! ### The set `Nset` and the support number -/

theorem mem_Nset_iff (hF : IsMaximal F) (u : V →L[ℝ] ℝ) :
    u ∈ Nset F ↔ lev F u ≠ ∅ ∧ lev F u ≠ Set.univ := by
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨h₁, fun hu => h₂ (lev_empty_of_lev_univ hu)⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨h₁, ?_⟩
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t ∉ lev F u := by
      by_contra hcon
      push_neg at hcon
      exact h₂ (Set.eq_univ_of_forall hcon)
    intro hempty
    have : (-t) ∈ lev F (-u) := by
      rw [mem_lev_neg_iff, neg_neg]
      exact halfGE_of_not_halfLE hF ht
    exact absurd (hempty ▸ this) (Set.notMem_empty _)

theorem lev_nonempty_of_mem_Nset {u : V →L[ℝ] ℝ} (hu : u ∈ Nset F) : (lev F u).Nonempty :=
  Set.nonempty_iff_ne_empty.mpr hu.1

theorem lev_bddBelow_of_mem_Nset (hF : IsMaximal F) {u : V →L[ℝ] ℝ} (hu : u ∈ Nset F) :
    BddBelow (lev F u) := by
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t ∉ lev F u := by
    by_contra hcon
    push_neg at hcon
    exact ((mem_Nset_iff hF u).mp hu).2 (Set.eq_univ_of_forall hcon)
  refine ⟨t, fun x hx => ?_⟩
  by_contra hlt
  push_neg at hlt
  exact ht (lev_isUpperSet u hlt.le hx)

theorem lev_eq_of_mem_Nset (hF : IsMaximal F) {u : V →L[ℝ] ℝ} (hu : u ∈ Nset F) :
    lev F u = Set.Ioi (sig F u) ∨ lev F u = Set.Ici (sig F u) := by
  obtain ⟨hne, hnu⟩ := (mem_Nset_iff hF u).mp hu
  rcases lev_shape (F := F) u with h | h | ⟨s, h⟩ | ⟨s, h⟩
  · exact absurd h hne
  · exact absurd h hnu
  · left
    have : sig F u = s := by rw [sig, h, csInf_Ioi]
    rw [this, h]
  · right
    have : sig F u = s := by rw [sig, h, csInf_Ici]
    rw [this, h]

theorem mem_lev_of_sig_lt (hF : IsMaximal F) {u : V →L[ℝ] ℝ} (hu : u ∈ Nset F)
    {t : ℝ} (ht : sig F u < t) : t ∈ lev F u := by
  rcases lev_eq_of_mem_Nset hF hu with h | h
  · rw [h]; exact ht
  · rw [h]; exact ht.le

theorem not_mem_lev_of_lt_sig (hF : IsMaximal F) {u : V →L[ℝ] ℝ} (hu : u ∈ Nset F)
    {t : ℝ} (ht : t < sig F u) : t ∉ lev F u := by
  intro hmem
  rcases lev_eq_of_mem_Nset hF hu with h | h
  · rw [h] at hmem; exact absurd (Set.mem_Ioi.mp hmem) (not_lt.mpr ht.le)
  · rw [h] at hmem; exact absurd (Set.mem_Ici.mp hmem) (not_le.mpr ht)

theorem sig_le_of_mem_lev (hF : IsMaximal F) {u : V →L[ℝ] ℝ} (hu : u ∈ Nset F)
    {t : ℝ} (ht : t ∈ lev F u) : sig F u ≤ t :=
  csInf_le (lev_bddBelow_of_mem_Nset hF hu) ht

theorem Nset_neg {u : V →L[ℝ] ℝ} (hu : u ∈ Nset F) : -u ∈ Nset F := by
  refine ⟨hu.2, ?_⟩
  rw [neg_neg]
  exact hu.1

theorem sig_neg (hF : IsMaximal F) {u : V →L[ℝ] ℝ} (hu : u ∈ Nset F) :
    sig F (-u) = - sig F u := by
  have hu' : -u ∈ Nset F := Nset_neg hu
  have hne : (lev F u).Nonempty := lev_nonempty_of_mem_Nset hu
  have hne' : (lev F (-u)).Nonempty := lev_nonempty_of_mem_Nset hu'
  -- the sum of the two support numbers is nonnegative
  have hsum : 0 ≤ sig F u + sig F (-u) := by
    have hlow : ∀ t ∈ lev F u, -t ≤ sig F (-u) := by
      intro t ht
      refine le_csInf hne' fun r hr => ?_
      have := add_nonneg_of_mem_lev ht hr
      linarith
    have : -sig F (-u) ≤ sig F u := by
      refine le_csInf hne fun t ht => ?_
      have := hlow t ht
      linarith
    linarith
  -- if it were positive, an intermediate level would contradict the dichotomy
  by_contra hcon
  have hpos : 0 < sig F u + sig F (-u) := lt_of_le_of_ne hsum (by intro h; exact hcon (by linarith))
  obtain ⟨t, ht₁, ht₂⟩ : ∃ t : ℝ, -sig F (-u) < t ∧ t < sig F u :=
    ⟨(-sig F (-u) + sig F u) / 2, by linarith, by linarith⟩
  have hnot : halfLE u t ∉ F.carrier := not_mem_lev_of_lt_sig hF hu ht₂
  have hge : (-t) ∈ lev F (-u) := by
    rw [mem_lev_neg_iff, neg_neg]
    exact halfGE_of_not_halfLE hF hnot
  have := sig_le_of_mem_lev hF hu' hge
  linarith

end ConvexFilter
