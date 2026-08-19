import ConvexFilters.Fibres

/-!
# The contract form of `fibre_of_line` is false (WO-11, Part B)

The work order asks, for `V = ℝ × ℝ`, for

```
theorem fibre_of_line {F F' : ConvexFilter V} (hF : IsMaximal F) (hF' : IsMaximal F')
    (h : ∀ u, levVal F u = levVal F' u) (hdim : finrank ℝ (dirA F) = 1) :
    F = F' ∨ ¬ Separated F F'
```

This file refutes that statement.  The conclusion cannot be `¬ Separated F F'`, because the
fibre over a line contains the two filters of stratum `(1, 2)` approaching the line from
opposite sides, and Theorem 9.5, second clause (`separated_gen`) *separates* those two: the
two closed half-planes bounded by the line cover the plane and neither belongs to both.  The
collapse of the fibre is therefore a genuinely quotient-level phenomenon, obtained from
Corollary 9.7 by transitivity through the `(1, 1)` filter, and that is the form proved in
`ConvexFilters/Fibres.lean` (`fibre_of_line`, `levVal_separates_quotient`).

## The witnesses

`Ghyp` of `ConvexFilters/SigCounterexample.lean` is a maximal filter of the plane with flat
the vertical axis, escape cone `{u | u (0,1) > 0}`, and approach to the axis from the right;
`Grefl` is its image under the reflection `(x, y) ↦ (-x, y)`, which fixes the axis and the
escape cone and reverses the approach.  The reflection changes `lev Ghyp u` only through the
sign of `u (1,0)`, and only in the shape `Set.Ioi 0` versus `Set.Ici 0` of a level set whose
infimum is `0` either way, which `levVal` does not see: `levVal_Grefl_eq`.  The two filters
are separated by the two closed half-planes `[x ≤ 0]` and `[x ≥ 0]`: `separated_Ghyp_Grefl`.

* `not_fibre_of_line` is the refutation.
-/

open Module

namespace ConvexFilter

namespace Space

namespace FibreCounterexample

open SigCounterexample

/-! ### The reflection of the plane in the vertical axis -/

/-- The reflection `(x, y) ↦ (-x, y)` of the plane, as a linear automorphism. -/
noncomputable def reflL : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) where
  toFun := fun p => (-p.1, p.2)
  invFun := fun p => (-p.1, p.2)
  map_add' := by intro x y; simp; ring
  map_smul' := by intro c x; simp
  left_inv := by intro x; simp
  right_inv := by intro x; simp

/-- The reflection of the plane, as an affine automorphism. -/
noncomputable def reflA : (ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ) := reflL.toAffineEquiv

theorem reflA_apply (p : ℝ × ℝ) : reflA p = (-p.1, p.2) := rfl

theorem continuous_reflA : Continuous (reflA) := by
  have h : ⇑reflA = fun p : ℝ × ℝ => (-p.1, p.2) := rfl
  rw [h]
  fun_prop

theorem continuous_reflA_symm : Continuous (reflA.symm) := by
  have h : ⇑reflA.symm = fun p : ℝ × ℝ => (-p.1, p.2) := rfl
  rw [h]
  fun_prop

/-- The reflection of the plane, as a continuous linear map, for composing with a
functional. -/
noncomputable def reflCLM : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (-(ContinuousLinearMap.fst ℝ ℝ ℝ)).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem reflCLM_apply (p : ℝ × ℝ) : reflCLM p = (-p.1, p.2) := rfl

/-! ### The reflected filter -/

/-- The reflection of the hyperbola filter: a maximal filter with the same flat and the same
escape cone as `Ghyp`, approaching the vertical axis from the left instead of the right. -/
noncomputable def Grefl : ConvexFilter (ℝ × ℝ) :=
  comapAffine reflA continuous_reflA continuous_reflA_symm Ghyp

theorem Grefl_isMaximal : IsMaximal Grefl :=
  comapAffine_isMaximal reflA continuous_reflA continuous_reflA_symm Ghyp_isMaximal

theorem mem_Grefl_iff {C : Set (ℝ × ℝ)} :
    C ∈ Grefl.carrier ↔ (⇑reflA ⁻¹' C) ∈ Ghyp.carrier := Iff.rfl

theorem preimage_reflA_halfLE (u : (ℝ × ℝ) →L[ℝ] ℝ) (t : ℝ) :
    (⇑reflA ⁻¹' halfLE u t) = halfLE (u.comp reflCLM) t := by
  ext p
  simp only [Set.mem_preimage, halfLE, Set.mem_setOf_eq, ContinuousLinearMap.coe_comp',
    Function.comp_apply, reflA_apply, reflCLM_apply]

theorem lev_Grefl (u : (ℝ × ℝ) →L[ℝ] ℝ) : lev Grefl u = lev Ghyp (u.comp reflCLM) := by
  ext t
  rw [mem_lev_iff, mem_lev_iff, mem_Grefl_iff, preimage_reflA_halfLE]

/-! ### The reflection does not change the extended support value -/

theorem comp_reflCLM_snd (u : (ℝ × ℝ) →L[ℝ] ℝ) : (u.comp reflCLM) (0, 1) = u (0, 1) := by
  show u (reflCLM (0, 1)) = u (0, 1)
  rw [reflCLM_apply]
  norm_num

/-- The extended support value of `Ghyp` at a functional vanishing on the vertical direction
is `0`, whatever the sign of its horizontal coordinate: the level set is `Set.Ioi 0` or
`Set.Ici 0`, and both have infimum `0`. -/
theorem levVal_Ghyp_of_snd_zero {u : (ℝ × ℝ) →L[ℝ] ℝ} (hb : u (0, 1) = 0) :
    levVal Ghyp u = ((0 : ℝ) : EReal) := by
  have hne : lev Ghyp u ≠ ∅ ∧ lev Ghyp u ≠ Set.univ := by
    rcases lt_or_ge 0 (u (1, 0)) with ha | ha
    · rw [lev_Ghyp_of_snd_zero_fst_pos hb ha]
      refine ⟨(Set.nonempty_Ioi (a := (0 : ℝ))).ne_empty, ?_⟩
      intro hcon
      have h0 : (0 : ℝ) ∈ Set.Ioi (0 : ℝ) := by rw [hcon]; exact Set.mem_univ 0
      exact lt_irrefl (0 : ℝ) h0
    · rw [lev_Ghyp_of_snd_zero_fst_nonpos hb ha]
      refine ⟨(Set.nonempty_Ici (a := (0 : ℝ))).ne_empty, ?_⟩
      intro hcon
      have h0 : (-1 : ℝ) ∈ Set.Ici (0 : ℝ) := by rw [hcon]; exact Set.mem_univ _
      exact absurd (h0 : (0 : ℝ) ≤ -1) (by norm_num)
  rw [levVal_of_mem_Nset Ghyp_isMaximal ((mem_Nset_iff Ghyp_isMaximal u).mpr hne), sig_Ghyp]

/-- **The reflection is invisible to `levVal`.** -/
theorem levVal_Grefl_eq (u : (ℝ × ℝ) →L[ℝ] ℝ) : levVal Ghyp u = levVal Grefl u := by
  have hlev : lev Grefl u = lev Ghyp (u.comp reflCLM) := lev_Grefl u
  have hsnd : (u.comp reflCLM) (0, 1) = u (0, 1) := comp_reflCLM_snd u
  rcases lt_trichotomy (u (0, 1)) 0 with hb | hb | hb
  · rw [levVal_of_lev_eq_univ (lev_Ghyp_of_snd_neg hb),
      levVal_of_lev_eq_univ (show lev Grefl u = Set.univ by
        rw [hlev]; exact lev_Ghyp_of_snd_neg (by rw [hsnd]; exact hb))]
  · have h1 : levVal Ghyp u = ((0 : ℝ) : EReal) := levVal_Ghyp_of_snd_zero hb
    have h2 : levVal Grefl u = ((0 : ℝ) : EReal) := by
      rw [levVal_congr_of_lev_eq hlev]
      exact levVal_Ghyp_of_snd_zero (by rw [hsnd]; exact hb)
    rw [h1, h2]
  · rw [levVal_of_lev_eq_empty (lev_Ghyp_of_snd_pos hb),
      levVal_of_lev_eq_empty (show lev Grefl u = ∅ by
        rw [hlev]; exact lev_Ghyp_of_snd_pos (by rw [hsnd]; exact hb))]

/-! ### The two filters are separated, and the flat is a line -/

theorem halfGE_fstCLM_notMem_Grefl : halfGE fstCLM 0 ∉ Grefl.carrier := by
  rw [mem_Grefl_iff]
  have hpre : (⇑reflA ⁻¹' halfGE fstCLM 0) = halfLE fstCLM 0 := by
    ext p
    simp only [Set.mem_preimage, halfGE, halfLE, Set.mem_setOf_eq, reflA_apply]
    show (0 : ℝ) ≤ -p.1 ↔ p.1 ≤ 0
    constructor <;> intro h <;> linarith
  rw [hpre]
  exact halfLE_fstCLM_notMem_Ghyp

/-- **The two filters are separated**, by the two closed half-planes bounded by the vertical
axis: Theorem 9.5, second clause. -/
theorem separated_Ghyp_Grefl : Separated Ghyp Grefl :=
  separated_gen halfLE_fstCLM_notMem_Ghyp halfGE_fstCLM_notMem_Grefl

/-- The flat of `Ghyp` is the vertical axis, whose direction is the line `vertAxis`. -/
theorem dirA_Ghyp : dirA Ghyp = vertAxis := by
  refine SetLike.coe_injective ?_
  rw [coe_dirA, coe_vertAxis]
  ext v
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hv
    have hf : fstCLM ∈ Nset Ghyp := by
      rw [Nset_Ghyp]
      show fstCLM (0, 1) = 0
      simp
    exact hv fstCLM hf
  · intro hv u hu
    rw [Nset_Ghyp] at hu
    rw [apply_eq u v, (hu : u (0, 1) = 0), (hv : v.1 = 0)]
    ring

theorem finrank_dirA_Ghyp : finrank ℝ (dirA Ghyp) = 1 := by
  rw [dirA_Ghyp]
  exact finrank_vertAxis

/-! ### The refutation -/

/-- **The contract form of `fibre_of_line` is false.** Two maximal filters of the plane with
a one-dimensional flat and the same extended support value everywhere need be neither equal
nor inseparable: `Ghyp` and its reflection `Grefl` are separated by the two closed
half-planes bounded by the vertical axis.  What survives is the collapse in the maximal
Hausdorff quotient, `Space.fibre_of_line` and `Space.levVal_separates_quotient`. -/
theorem not_fibre_of_line :
    ¬ ∀ (F F' : ConvexFilter (ℝ × ℝ)), IsMaximal F → IsMaximal F' →
      (∀ u, levVal F u = levVal F' u) → finrank ℝ (dirA F) = 1 →
      F = F' ∨ ¬ Separated F F' := by
  intro hcon
  rcases hcon Ghyp Grefl Ghyp_isMaximal Grefl_isMaximal levVal_Grefl_eq finrank_dirA_Ghyp with
    heq | hsep
  · exact not_separated_self Grefl Grefl_isMaximal (heq ▸ separated_Ghyp_Grefl)
  · exact hsep separated_Ghyp_Grefl

end FibreCounterexample

end Space

end ConvexFilter
