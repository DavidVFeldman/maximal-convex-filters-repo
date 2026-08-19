import ConvexFilters.SpaceTop

/-!
# Continuity of the support function (Section 9, Lemmas 9.9 and Theorem 9.10)

Parts B and C of WO-10.

## Part B — the extended support value and its continuity

`sig F u` is real-valued (see `notes/CONVENTIONS.md`, §1): the values `+∞` and `-∞` of the
paper's `σ_F(u)` are recorded in the *shape* of `lev F u`, which is `∅` in the first case
and `Set.univ` in the second.  A statement about convergence in `[-∞, +∞]` has to see
those two values, so this file introduces the `EReal`-valued

```
levVal F u = ⊤            if lev F u = ∅
           = ⊥            if lev F u = Set.univ
           = ↑(sig F u)   otherwise
```

and `levVal_of_mem_Nset` checks, against `mem_Nset_iff`, that the third case is exactly
`u ∈ Nset F`, where `sig F u` is meaningful.  `sigma_continuous` (Lemma 9.9) is the
continuity of `F ↦ levVal F u` on `MaxFilter V`.  The proof is the paper's, through the
two families of subbasic open sets
`{F | [u ≤ t] ∉ F}` and `{F | [u ≥ t] ∉ F}` (`continuous_lev_indicator`), and the
dichotomy `halfLE_or_halfGE` converts membership in the second into a bound.

## Part C — separation by the invariant

`separated_of_levVal_ne`: two maximal filters with different extended support values at
some functional are separated; `eq_of_sig_eq_of_not_separated` is its contrapositive on
`ℝ × ℝ`, the part of Theorem 9.10 that is within reach.  The converse enumeration of the
fibres, the maximal Hausdorff quotient and the identification of `hM(ℝ²)` are out of scope
for this file.
-/

namespace ConvexFilter

namespace Space

section LevVal

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

open Classical in
/-- The extended support value of `F` at `u`, in `[-∞, +∞]`: `⊤` when the level set is
empty, `⊥` when it is all of `ℝ`, and the real support number `sig F u` otherwise. -/
noncomputable def levVal (F : ConvexFilter V) (u : V →L[ℝ] ℝ) : EReal :=
  if lev F u = ∅ then ⊤ else if lev F u = Set.univ then ⊥ else (sig F u : EReal)

theorem levVal_of_lev_eq_empty {F : ConvexFilter V} {u : V →L[ℝ] ℝ} (h : lev F u = ∅) :
    levVal F u = ⊤ := by
  classical
  rw [levVal, if_pos h]

theorem levVal_of_lev_eq_univ {F : ConvexFilter V} {u : V →L[ℝ] ℝ} (h : lev F u = Set.univ) :
    levVal F u = ⊥ := by
  classical
  have hne : lev F u ≠ ∅ := by
    intro hcon
    rw [h] at hcon
    have h0 : (0 : ℝ) ∈ (∅ : Set ℝ) := by rw [← hcon]; exact Set.mem_univ 0
    exact h0
  rw [levVal, if_neg hne, if_pos h]

/-- The third case of `levVal` is exactly `u ∈ Nset F`, by `mem_Nset_iff`; there the value
is the real support number. -/
theorem levVal_of_mem_Nset {F : ConvexFilter V} (hF : IsMaximal F) {u : V →L[ℝ] ℝ}
    (hu : u ∈ Nset F) : levVal F u = (sig F u : EReal) := by
  classical
  obtain ⟨h1, h2⟩ := (mem_Nset_iff hF u).mp hu
  rw [levVal, if_neg h1, if_neg h2]

/-- The three cases of `levVal`. -/
theorem levVal_cases (F : ConvexFilter V) (hF : IsMaximal F) (u : V →L[ℝ] ℝ) :
    (lev F u = ∅ ∧ levVal F u = ⊤) ∨ (lev F u = Set.univ ∧ levVal F u = ⊥) ∨
      (u ∈ Nset F ∧ levVal F u = (sig F u : EReal)) := by
  rcases eq_or_ne (lev F u) ∅ with h | h1
  · exact Or.inl ⟨h, levVal_of_lev_eq_empty h⟩
  rcases eq_or_ne (lev F u) Set.univ with h | h2
  · exact Or.inr (Or.inl ⟨h, levVal_of_lev_eq_univ h⟩)
  have hu : u ∈ Nset F := (mem_Nset_iff hF u).mpr ⟨h1, h2⟩
  exact Or.inr (Or.inr ⟨hu, levVal_of_mem_Nset hF hu⟩)

/-- A level of `u` bounds the extended support value from above. -/
theorem levVal_le_of_mem_lev {F : ConvexFilter V} (hF : IsMaximal F) {u : V →L[ℝ] ℝ} {t : ℝ}
    (ht : t ∈ lev F u) : levVal F u ≤ (t : EReal) := by
  rcases levVal_cases F hF u with ⟨h, -⟩ | ⟨-, hval⟩ | ⟨hu, hval⟩
  · rw [h] at ht; exact absurd ht (Set.notMem_empty t)
  · rw [hval]; exact bot_le
  · rw [hval]
    exact_mod_cast sig_le_of_mem_lev hF hu ht

/-- A non-level of `u` bounds the extended support value from below. -/
theorem le_levVal_of_notMem_lev {F : ConvexFilter V} (hF : IsMaximal F) {u : V →L[ℝ] ℝ} {t : ℝ}
    (ht : t ∉ lev F u) : (t : EReal) ≤ levVal F u := by
  rcases levVal_cases F hF u with ⟨-, hval⟩ | ⟨h, -⟩ | ⟨hu, hval⟩
  · rw [hval]; exact le_top
  · rw [h] at ht; exact absurd (Set.mem_univ t) ht
  · rw [hval]
    have hle : t ≤ sig F u := by
      by_contra hcon
      push_neg at hcon
      exact ht (mem_lev_of_sig_lt hF hu hcon)
    exact_mod_cast hle

/-- Below the extended support value, the half-space `[u ≤ t]` is not in the filter. -/
theorem notMem_halfLE_of_lt_levVal {F : ConvexFilter V} (hF : IsMaximal F) {u : V →L[ℝ] ℝ}
    {t : ℝ} (ht : (t : EReal) < levVal F u) : halfLE u t ∉ F.carrier := by
  intro hmem
  exact absurd (levVal_le_of_mem_lev hF (hmem : t ∈ lev F u)) (not_le.mpr ht)

/-- Above the extended support value, the half-space `[u ≥ t]` is not in the filter. -/
theorem notMem_halfGE_of_levVal_lt {F : ConvexFilter V} (hF : IsMaximal F) {u : V →L[ℝ] ℝ}
    {t : ℝ} (ht : levVal F u < (t : EReal)) : halfGE u t ∉ F.carrier := by
  intro hmem
  obtain ⟨s, hs1, hs2⟩ := EReal.exists_between_coe_real ht
  have hsl : s ∈ lev F u := by
    by_contra hcon
    exact absurd (le_levVal_of_notMem_lev hF hcon) (not_le.mpr hs1)
  have hst : s < t := by exact_mod_cast hs2
  have hdisj := disjoint_halfLE_halfGE hst u
  have hempty : (∅ : Set V) ∈ F.carrier := by
    rw [← hdisj]
    exact F.inter_mem hsl hmem
  exact F.empty_not_mem hempty

/-- If `[u ≥ t]` is not in the filter, the extended support value is at most `t`. -/
theorem levVal_le_of_notMem_halfGE {F : ConvexFilter V} (hF : IsMaximal F) {u : V →L[ℝ] ℝ}
    {t : ℝ} (ht : halfGE u t ∉ F.carrier) : levVal F u ≤ (t : EReal) := by
  by_cases hmem : halfLE u t ∈ F.carrier
  · exact levVal_le_of_mem_lev hF (hmem : t ∈ lev F u)
  · exact absurd (halfGE_of_not_halfLE hF hmem) ht

end LevVal

/-! ## Lemma 9.9: continuity of the extended support value -/

section Continuity

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **The subbasic neighbourhoods used in Lemma 9.9.** For each functional `u` and each
level `t`, the set of maximal filters omitting `[u ≤ t]` and the set of maximal filters
omitting `[u ≥ t]` are open; these are the two families of subbasic open sets in which the
paper's three cases exhibit a neighbourhood. -/
theorem continuous_lev_indicator (u : V →L[ℝ] ℝ) (t : ℝ) :
    IsOpen {F : MaxFilter V | halfLE u t ∉ F.1.carrier} ∧
      IsOpen {F : MaxFilter V | halfGE u t ∉ F.1.carrier} := by
  constructor
  · exact isOpen_compl_Vset (isClosed_halfLE u t) (convex_halfLE u t)
  · exact isOpen_compl_Vset (isClosed_halfGE u t) (convex_halfGE u t)

/-- **Lemma 9.9.** The extended support value is a continuous function of the maximal
filter, with values in `[-∞, +∞]`. -/
theorem sigma_continuous (u : V →L[ℝ] ℝ) :
    Continuous (fun F : MaxFilter V => levVal F.1 u) := by
  refine continuous_iff_continuousAt.mpr fun F => ?_
  refine tendsto_order.mpr ⟨fun a ha => ?_, fun a ha => ?_⟩
  · -- below the value: the filters omitting `[u ≤ t]` for a suitable `t`
    obtain ⟨t, hat, htv⟩ := EReal.exists_between_coe_real ha
    have hopen : IsOpen {G : MaxFilter V | halfLE u t ∉ G.1.carrier} :=
      (continuous_lev_indicator u t).1
    have hFmem : F ∈ {G : MaxFilter V | halfLE u t ∉ G.1.carrier} :=
      notMem_halfLE_of_lt_levVal F.2 htv
    refine Filter.eventually_of_mem (hopen.mem_nhds hFmem) fun G hG => ?_
    exact lt_of_lt_of_le hat (le_levVal_of_notMem_lev G.2 (hG : halfLE u t ∉ G.1.carrier))
  · -- above the value: the filters omitting `[u ≥ t]` for a suitable `t`
    obtain ⟨t, hvt, hta⟩ := EReal.exists_between_coe_real ha
    have hopen : IsOpen {G : MaxFilter V | halfGE u t ∉ G.1.carrier} :=
      (continuous_lev_indicator u t).2
    have hFmem : F ∈ {G : MaxFilter V | halfGE u t ∉ G.1.carrier} :=
      notMem_halfGE_of_levVal_lt F.2 hvt
    refine Filter.eventually_of_mem (hopen.mem_nhds hFmem) fun G hG => ?_
    exact lt_of_le_of_lt (levVal_le_of_notMem_halfGE G.2 (hG : halfGE u t ∉ G.1.carrier)) hta

end Continuity

/-! ## Part C: separation by the extended support value -/

section Separation

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Two maximal convex filters whose extended support values differ at some functional are
separated.  This is Lemma 9.9 together with `separated_iff_disjoint_nhds`. -/
theorem separated_of_levVal_ne {F F' : MaxFilter V} {u : V →L[ℝ] ℝ}
    (h : levVal F.1 u ≠ levVal F'.1 u) : Separated F.1 F'.1 := by
  obtain ⟨U, W, hU, hW, hFU, hF'W, hdisj⟩ := t2_separation h
  refine separated_iff_disjoint_nhds.mpr
    ⟨(fun G : MaxFilter V => levVal G.1 u) ⁻¹' U, (fun G : MaxFilter V => levVal G.1 u) ⁻¹' W,
      hU.preimage (sigma_continuous u), hW.preimage (sigma_continuous u), hFU, hF'W, ?_⟩
  exact hdisj.preimage _

/-- **Theorem 9.10, the part within reach, on `ℝ × ℝ`.** Two maximal convex filters of the
plane that cannot be separated have the same extended support value at every functional;
equivalently, filters with different support values are separated.  The converse — that
the extended support value separates the points of the maximal Hausdorff quotient — is not
formalized. -/
theorem eq_of_sig_eq_of_not_separated {F F' : MaxFilter (ℝ × ℝ)}
    (h : ¬ Separated F.1 F'.1) (u : (ℝ × ℝ) →L[ℝ] ℝ) : levVal F.1 u = levVal F'.1 u := by
  by_contra hne
  exact h (separated_of_levVal_ne hne)

end Separation

end Space

end ConvexFilter
