import ConvexFilters.SigCounterexample
import ConvexFilters.Annihilator

/-!
# Where the two counterexample filters sit in the stratification (Remarks 8.1 and 8.5)

`ConvexFilters/SigCounterexample.lean` builds two maximal convex filters `Ghyp` and `Gpar`
on `ℝ × ℝ` with the same support number and the same positivity cone, and computes the
table of their level sets. This file reads the remaining invariants off that table:

* `Nset_Ghyp`, `Nset_Gpar` — the subspaces of functionals with finite support number;
* `Mset_Ghyp`, `Mset_Gpar` — both trivial: no level hyperplane belongs to either filter;
* `Aset_Ghyp`, `Aset_Gpar` — the flats, a line and the whole plane;
* `Aset_Ghyp_ne_Aset_Gpar` — the flats differ, which is the point of Remark 8.1: the two
  filters share a positivity cone and are separated by the flat.

Part D (Remark 8.5) is `strata_not_separated_by_Qset`: the two filters are the pair of
maximal convex filters on `ℝ × ℝ` that the naive recursion of the remark identifies, since
they have the same cone and different flats. Only that consequence is formalized; the
recursion itself and the spaces `M(n)` are not.
-/

namespace ConvexFilter

namespace SigCounterexample

/-! ### Level sets of `-u` -/

section Neg

variable {u : (ℝ × ℝ) →L[ℝ] ℝ}

theorem neg_apply_fst (u : (ℝ × ℝ) →L[ℝ] ℝ) : (-u) (1, 0) = -u (1, 0) := rfl

theorem neg_apply_snd (u : (ℝ × ℝ) →L[ℝ] ℝ) : (-u) (0, 1) = -u (0, 1) := rfl

end Neg

/-! ### Part A — `Nset` -/

/-- The functionals with finite support number for the hyperbola filter are exactly those
vanishing on the vertical direction. -/
theorem Nset_Ghyp : Nset Ghyp = {u : (ℝ × ℝ) →L[ℝ] ℝ | u (0, 1) = 0} := by
  ext u
  simp only [Set.mem_setOf_eq, Nset]
  constructor
  · rintro ⟨h1, h2⟩
    rcases lt_trichotomy (u (0, 1)) 0 with hb | hb | hb
    · exact absurd (lev_Ghyp_of_snd_pos (u := -u) (by rw [neg_apply_snd]; linarith)) h2
    · exact hb
    · exact absurd (lev_Ghyp_of_snd_pos hb) h1
  · intro hb
    constructor
    · rcases lt_or_ge 0 (u (1, 0)) with ha | ha
      · rw [lev_Ghyp_of_snd_zero_fst_pos hb ha]
        exact fun h => absurd (h ▸ Set.mem_Ioi.2 zero_lt_one : (1 : ℝ) ∈ (∅ : Set ℝ))
          (Set.notMem_empty 1)
      · rw [lev_Ghyp_of_snd_zero_fst_nonpos hb ha]
        exact fun h => absurd (h ▸ Set.self_mem_Ici : (0 : ℝ) ∈ (∅ : Set ℝ))
          (Set.notMem_empty 0)
    · have hb' : (-u) (0, 1) = 0 := by rw [neg_apply_snd, hb, neg_zero]
      rcases lt_or_ge 0 ((-u) (1, 0)) with ha | ha
      · rw [lev_Ghyp_of_snd_zero_fst_pos hb' ha]
        exact fun h => absurd (h ▸ Set.mem_Ioi.2 zero_lt_one : (1 : ℝ) ∈ (∅ : Set ℝ))
          (Set.notMem_empty 1)
      · rw [lev_Ghyp_of_snd_zero_fst_nonpos hb' ha]
        exact fun h => absurd (h ▸ Set.self_mem_Ici : (0 : ℝ) ∈ (∅ : Set ℝ))
          (Set.notMem_empty 0)

/-- The support number of the parabola filter is finite only at `0`. -/
theorem Nset_Gpar : Nset Gpar = {(0 : (ℝ × ℝ) →L[ℝ] ℝ)} := by
  ext u
  simp only [Set.mem_singleton_iff, Nset, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    have hb : u (0, 1) = 0 := by
      rcases lt_trichotomy (u (0, 1)) 0 with hb | hb | hb
      · exact absurd (lev_Gpar_of_snd_pos (u := -u) (by rw [neg_apply_snd]; linarith)) h2
      · exact hb
      · exact absurd (lev_Gpar_of_snd_pos hb) h1
    have hb' : (-u) (0, 1) = 0 := by rw [neg_apply_snd, hb, neg_zero]
    have ha : u (1, 0) = 0 := by
      rcases lt_trichotomy (u (1, 0)) 0 with ha | ha | ha
      · exact absurd (lev_Gpar_of_snd_zero_fst_pos (u := -u) hb'
          (by rw [neg_apply_fst]; linarith)) h2
      · exact ha
      · exact absurd (lev_Gpar_of_snd_zero_fst_pos hb ha) h1
    exact eq_zero_of_coords ha hb
  · rintro rfl
    rw [neg_zero]
    refine ⟨?_, ?_⟩ <;>
      · rw [lev_zero]
        exact fun h => absurd (h ▸ Set.self_mem_Ici : (0 : ℝ) ∈ (∅ : Set ℝ))
          (Set.notMem_empty 0)

/-! ### Part A — `Mset` -/

theorem zero_mem_Mset_of (G : ConvexFilter (ℝ × ℝ)) : (0 : (ℝ × ℝ) →L[ℝ] ℝ) ∈ Mset G := by
  refine ⟨0, ?_⟩
  have : hyperplane (0 : (ℝ × ℝ) →L[ℝ] ℝ) 0 = Set.univ := by
    ext p; simp [hyperplane]
  rw [this]
  exact G.univ_mem

/-- No level hyperplane belongs to the hyperbola filter, apart from the trivial one. -/
theorem Mset_Ghyp : Mset Ghyp = {(0 : (ℝ × ℝ) →L[ℝ] ℝ)} := by
  ext u
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨t, ht⟩
    have hN : u ∈ Nset Ghyp := Mset_subset_Nset Ghyp_isMaximal ⟨t, ht⟩
    rw [Nset_Ghyp] at hN
    have hb : u (0, 1) = 0 := hN
    have hb' : (-u) (0, 1) = 0 := by rw [neg_apply_snd, hb, neg_zero]
    have hle : t ∈ lev Ghyp u := halfLE_mem_of_hyperplane_mem ht
    have hge : (-t) ∈ lev Ghyp (-u) :=
      (mem_lev_neg_iff).2 (by simpa using halfGE_mem_of_hyperplane_mem ht)
    rcases lt_trichotomy (u (1, 0)) 0 with ha | ha | ha
    · rw [lev_Ghyp_of_snd_zero_fst_nonpos hb ha.le] at hle
      rw [lev_Ghyp_of_snd_zero_fst_pos hb' (by rw [neg_apply_fst]; linarith)] at hge
      simp only [Set.mem_Ici] at hle
      simp only [Set.mem_Ioi] at hge
      linarith
    · exact eq_zero_of_coords ha hb
    · rw [lev_Ghyp_of_snd_zero_fst_pos hb ha] at hle
      rw [lev_Ghyp_of_snd_zero_fst_nonpos hb' (by rw [neg_apply_fst]; linarith)] at hge
      simp only [Set.mem_Ioi] at hle
      simp only [Set.mem_Ici] at hge
      linarith
  · rintro rfl
    exact zero_mem_Mset_of Ghyp

/-- No level hyperplane belongs to the parabola filter, apart from the trivial one. -/
theorem Mset_Gpar : Mset Gpar = {(0 : (ℝ × ℝ) →L[ℝ] ℝ)} := by
  ext u
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hu
    have hN : u ∈ Nset Gpar := Mset_subset_Nset Gpar_isMaximal hu
    rw [Nset_Gpar] at hN
    exact hN
  · rintro rfl
    exact zero_mem_Mset_of Gpar

/-! ### Part A — `Aset` -/

/-- The first coordinate functional on the plane. -/
noncomputable def fstCLM : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ

@[simp] theorem fstCLM_apply (p : ℝ × ℝ) : fstCLM p = p.1 := rfl

/-- The flat of the hyperbola filter is the vertical axis: the filter approaches the line
`p.1 = 0` without reaching it. -/
theorem Aset_Ghyp : Aset Ghyp = {p : ℝ × ℝ | p.1 = 0} := by
  ext x
  simp only [mem_Aset_iff, Set.mem_setOf_eq]
  constructor
  · intro hx
    have hf : fstCLM ∈ Nset Ghyp := by
      rw [Nset_Ghyp]
      show fstCLM (0, 1) = 0
      simp
    have := hx fstCLM hf
    rw [sig_Ghyp] at this
    simpa using this
  · intro hx u hu
    rw [Nset_Ghyp] at hu
    have hb : u (0, 1) = 0 := hu
    rw [sig_Ghyp, apply_eq u x, hb, hx]
    ring

/-- The flat of the parabola filter is everything: the filter escapes to infinity in every
direction it sees. -/
theorem Aset_Gpar : Aset Gpar = Set.univ := by
  ext x
  simp only [mem_Aset_iff, Set.mem_univ, iff_true]
  intro u hu
  rw [Nset_Gpar] at hu
  have : u = 0 := hu
  subst this
  rw [sig_Gpar]
  simp

/-- **Remark 8.1.** The two filters of `SigCounterexample.lean` are separated by their
flats. -/
theorem Aset_Ghyp_ne_Aset_Gpar : Aset Ghyp ≠ Aset Gpar := by
  intro h
  rw [Aset_Ghyp, Aset_Gpar] at h
  have : ((1 : ℝ), (0 : ℝ)) ∈ {p : ℝ × ℝ | p.1 = 0} := h ▸ Set.mem_univ _
  simp only [Set.mem_setOf_eq] at this
  exact one_ne_zero this

/-! ### A second proof that `sig` and `Qset` do not determine a maximal convex filter -/

/-- The flat depends only on the carrier. -/
theorem Aset_eq_of_carrier_eq {F F' : ConvexFilter (ℝ × ℝ)} (h : F.carrier = F'.carrier) :
    Aset F = Aset F' := by
  have hlev : ∀ u : (ℝ × ℝ) →L[ℝ] ℝ, lev F u = lev F' u := by
    intro u; ext t; simp only [lev, Set.mem_setOf_eq, h]
  have hN : Nset F = Nset F' := by
    ext u; simp only [Nset, Set.mem_setOf_eq, hlev]
  have hsig : ∀ u : (ℝ × ℝ) →L[ℝ] ℝ, sig F u = sig F' u := by
    intro u; simp only [sig, hlev]
  ext x
  simp only [mem_Aset_iff, hN, hsig]

/-- The carriers of the two filters differ, proved from the flats rather than from a
disjointness of members: this is a second, independent proof of
`ConvexFilter.not_carrier_eq_of_sig_Qset`. -/
theorem carrier_Ghyp_ne_carrier_Gpar_of_Aset : Ghyp.carrier ≠ Gpar.carrier := fun h =>
  Aset_Ghyp_ne_Aset_Gpar (Aset_eq_of_carrier_eq h)

theorem Ghyp_ne_Gpar : Ghyp ≠ Gpar := by
  intro h
  exact carrier_Ghyp_ne_carrier_Gpar (congrArg ConvexFilter.carrier h)

end SigCounterexample

/-! ### Part D — Remark 8.5 -/

/-- **Remark 8.5.** The positivity cone does not separate the strata: there are two distinct
maximal convex filters on `ℝ × ℝ` with the same cone `Qset` and different flats `Aset`.
Peeling the leading ray therefore cannot be a well-defined operation on the moduli space,
since it forgets whether that ray is an escape or an approach direction. -/
theorem strata_not_separated_by_Qset :
    ∃ F F' : ConvexFilter (ℝ × ℝ), IsMaximal F ∧ IsMaximal F' ∧
      Qset F = Qset F' ∧ Aset F ≠ Aset F' ∧ F ≠ F' :=
  ⟨SigCounterexample.Ghyp, SigCounterexample.Gpar, SigCounterexample.Ghyp_isMaximal,
    SigCounterexample.Gpar_isMaximal, SigCounterexample.Qset_Ghyp_eq_Qset_Gpar,
    SigCounterexample.Aset_Ghyp_ne_Aset_Gpar, SigCounterexample.Ghyp_ne_Gpar⟩

end ConvexFilter
