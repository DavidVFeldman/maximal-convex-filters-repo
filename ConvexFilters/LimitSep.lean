import ConvexFilters.LimitMembers

/-!
# The characters separate the maximal convex filters

WO-13, Part D; Theorem 4.1 of `paper/limits-algebra-note.tex`, and the objective of the
order.

`eq_of_lim_eq`: two maximal convex filters at which every member of the algebra has the
same limit are equal.

The proof is the note's.  Proposition 3.2 (`mem_A_comp_functional`) applied to a
*continuous injective* `φ : EReal → ℝ` gives `levVal F = levVal F'`, hence `Nset`, `Aset`
and `Eset` agree; these three are `ConvexFilter.Space.Nset_eq_of_levVal_eq`,
`ConvexFilter.Space.Aset_eq_of_levVal_eq` and `ConvexFilter.Space.Eset_eq_of_levVal_eq`
of `ConvexFilters/Fibres.lean`.  The work order anticipated that those three would have to
be restated in a general ambient because `Fibres.lean` is about `ℝ × ℝ`; in fact they are
already stated and proved there for an arbitrary real normed space (they sit in the
`LevVal` section, whose only variables are `[NormedAddCommGroup V] [NormedSpace ℝ V]`), so
they are cited directly and nothing is restated.

Then Proposition 3.3 (`lim_indicator_table`) at each `u ∈ Nset F` identifies `Dset`, so
`Qset F = Eset F ∪ Dset F = Qset F'`, and `ConvexFilter.eq_of_Aset_Qset` (Theorem 6.1 of
the main paper) finishes.

## The separating function `φ`

Search record for a homeomorphism `EReal ≃ₜ Set.Icc (0:ℝ) 1` at the pinned revision:
`Mathlib.Topology.Instances.EReal.Lemmas` carries only `EReal.neBotTopHomeomorphReal`
(`({⊥, ⊤}ᶜ : Set EReal) ≃ₜ ℝ`); a grep for `≃ₜ`/`Homeomorph` in every file mentioning
`EReal` returns, besides that one, only the `ENNReal`/`EReal` logarithm pair
`ENNReal.logHomeomorph` and `EReal.expHomeomorph`.  There is no `EReal ≃ₜ Icc (0:ℝ) 1`.
What is available is `ENNReal.orderIsoUnitIntervalBirational : ℝ≥0∞ ≃o Set.Icc (0:ℝ) 1`,
whose `toHomeomorph` is used in Mathlib itself; composing it with `EReal.expHomeomorph`
gives a homeomorphism `EReal ≃ₜ Set.Icc (0:ℝ) 1`, and `sepFun` below is that composite
followed by the inclusion of `Set.Icc (0:ℝ) 1` in `ℝ`.  This is cleaner than the explicit
`x ↦ x.toReal / (1 + |x.toReal|)` extended by `±1` suggested by the order, whose
continuity at `⊥` and `⊤` would have to be proved by hand; only continuity and injectivity
of `φ` are used.
-/

open Filter Topology

namespace ConvexFilter

namespace Limits

open ConvexFilter.Space

/-! ### A continuous injection of the extended reals in the reals -/

/-- A continuous injection `[-∞, +∞] → ℝ`: the exponential homeomorphism onto `ℝ≥0∞`
followed by the birational order isomorphism of `ℝ≥0∞` with the unit interval. -/
noncomputable def sepFun : EReal → ℝ :=
  fun x => (ENNReal.orderIsoUnitIntervalBirational (EReal.exp x) : ℝ)

theorem continuous_sepFun : Continuous sepFun :=
  continuous_subtype_val.comp
    (ENNReal.orderIsoUnitIntervalBirational.toHomeomorph.continuous.comp
      EReal.expHomeomorph.continuous)

theorem injective_sepFun : Function.Injective sepFun := by
  intro a b hab
  have h1 : ENNReal.orderIsoUnitIntervalBirational (EReal.exp a)
      = ENNReal.orderIsoUnitIntervalBirational (EReal.exp b) := Subtype.ext hab
  exact EReal.expOrderIso.injective (ENNReal.orderIsoUnitIntervalBirational.injective h1)

/-! ### The proof of Theorem 4.1 -/

section Separation

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Equality of all the characters forces equality of the extended support values. -/
theorem levVal_eq_of_lim_eq {F F' : ConvexFilter V} (hF : IsMaximal F) (hF' : IsMaximal F')
    (h : ∀ f : V → ℝ, mem_A f → lim f F = lim f F') (u : V →L[ℝ] ℝ) :
    levVal F u = levVal F' u := by
  obtain ⟨hmem, hlim⟩ := mem_A_comp_functional (V := V) u continuous_sepFun
  have := h _ hmem
  rw [hlim F hF, hlim F' hF'] at this
  exact injective_sepFun this

/-- Equality of all the characters forces `Dset` to agree; one inclusion. -/
theorem Dset_subset_of_lim_eq {F F' : ConvexFilter V} (hF : IsMaximal F) (hF' : IsMaximal F')
    (h : ∀ f : V → ℝ, mem_A f → lim f F = lim f F') : Dset F ⊆ Dset F' := by
  classical
  intro u hu
  have hu0 : u ≠ 0 := fun h0 => zero_notMem_Dset F (h0 ▸ hu)
  set c : ℝ := sig F u with hc
  have hlev : levVal F u = (c : EReal) := levVal_of_mem_Nset hF hu.1
  have hlev' : levVal F' u = (c : EReal) := by
    rw [← levVal_eq_of_lim_eq hF hF' h u]; exact hlev
  have htab := lim_indicator_table hF u hu0 hlev
  have htab' := lim_indicator_table hF' u hu0 hlev'
  rw [if_pos hu] at htab
  by_contra hcon
  rw [if_neg hcon] at htab'
  have hfst : lim (Set.indicator {x : V | c < u x} (1 : V → ℝ)) F
      = lim (Set.indicator {x : V | c < u x} (1 : V → ℝ)) F' :=
    h _ (mem_A_indicator_gt u hu0 c)
  have h1 : lim (Set.indicator {x : V | c < u x} (1 : V → ℝ)) F = 1 := congrArg Prod.fst htab
  have h0 : lim (Set.indicator {x : V | c < u x} (1 : V → ℝ)) F' = 0 := by
    by_cases hM : u ∈ Mset F'
    · rw [if_pos hM] at htab'
      exact congrArg Prod.fst htab'
    · rw [if_neg hM] at htab'
      exact congrArg Prod.fst htab'
  rw [h1, h0] at hfst
  exact one_ne_zero hfst

/-- Equality of all the characters forces `Dset` to agree. -/
theorem Dset_eq_of_lim_eq {F F' : ConvexFilter V} (hF : IsMaximal F) (hF' : IsMaximal F')
    (h : ∀ f : V → ℝ, mem_A f → lim f F = lim f F') : Dset F = Dset F' :=
  Set.Subset.antisymm (Dset_subset_of_lim_eq hF hF' h)
    (Dset_subset_of_lim_eq hF' hF fun f hf => (h f hf).symm)

/-- Equality of all the characters forces `Qset` to agree. -/
theorem Qset_eq_of_lim_eq {F F' : ConvexFilter V} (hF : IsMaximal F) (hF' : IsMaximal F')
    (h : ∀ f : V → ℝ, mem_A f → lim f F = lim f F') : Qset F = Qset F' := by
  rw [Qset_eq_Eset_union_Dset hF, Qset_eq_Eset_union_Dset hF',
    Eset_eq_of_levVal_eq hF hF' (levVal_eq_of_lim_eq hF hF' h), Dset_eq_of_lim_eq hF hF' h]

end Separation

section Main

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Theorem 4.1 of the note.** The characters of the algebra separate the maximal convex
filters: two maximal convex filters along which every member of the algebra has the same
limit are equal. -/
theorem eq_of_lim_eq {F F' : ConvexFilter V} (hF : IsMaximal F) (hF' : IsMaximal F')
    (h : ∀ f : V → ℝ, mem_A f → lim f F = lim f F') : F = F' :=
  eq_of_Aset_Qset hF hF'
    (Aset_eq_of_levVal_eq hF hF' (levVal_eq_of_lim_eq hF hF' h))
    (Qset_eq_of_lim_eq hF hF' h)

end Main

end Limits

end ConvexFilter
