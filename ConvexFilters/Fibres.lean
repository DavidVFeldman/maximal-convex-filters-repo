import ConvexFilters.Quotient
import ConvexFilters.SigmaCont
import ConvexFilters.Classification

/-!
# The fibres of the invariant in the plane: Theorem 9.9, first clause (WO-11, Part B)

`sigma_continuous` of `ConvexFilters/SigmaCont.lean` is the separating direction of
Theorem 9.9: filters with different extended support values are separated, hence have
different images in the maximal Hausdorff quotient.  This file supplies the converse for
`V = ℝ × ℝ`: two maximal convex filters of the plane on which `levVal` agrees everywhere
are equal, or lie in one collapsed fibre.

## Contents

* `Nset_eq_of_levVal_eq`, `Aset_eq_of_levVal_eq`, `Eset_eq_of_levVal_eq`: `levVal`
  determines the three invariants it visibly records — `Nset` is where `levVal` is finite,
  `sig` is its value there, and `Eset` is where it is `⊤`;
* `exists_maximal_flat`: the filter of stratum `(d, d)` beneath a maximal filter, obtained
  from the classification: the admissible pair `(Aset F, Eset F)`, that is, the same flat
  with the approach datum `Dset` discarded;
* `fibre_of_line_flat`: for a maximal filter of the plane whose flat is a line, the filter
  beneath it is either equal to it or inseparable from it;
* `eq_of_levVal_eq_of_dim_two`: over a flat of dimension two the fibre is a singleton;
* `eq_of_levVal_eq_of_dim_zero`: over a flat of dimension zero (a principal filter) the
  fibre is a singleton;
* `fibre_of_line`: over a line the fibre consists of filters all identified with one common
  filter — the corrected form of the contract statement, see below;
* `levVal_separates_quotient` and `levVal_eq_iff_forall_continuous_eq`: two maximal convex
  filters of the plane have the same image in the maximal Hausdorff quotient — equivalently,
  the same image under every continuous map to a Hausdorff space — **if and only if**
  `levVal` agrees on them.

## The contract form of `fibre_of_line` is false

The work order asks for

```
theorem fibre_of_line ... (h : ∀ u, levVal F u = levVal F' u)
    (hdim : finrank ℝ (dirA F) = 1) : F = F' ∨ ¬ Separated F F'
```

This is refuted by the pair `F₊`, `F₋` of stratum `(1, 2)` filters approaching a line from
the two sides: they have the same flat, the same `Nset`, the same `sig` and the same escape
cone, hence the same `levVal`, they are distinct, and they *are* separated — by the two
closed half-planes bounded by the line (`separated_gen`, Theorem 9.5, second clause).  The
refutation is formalized in `ConvexFilters/FibreCounterexample.lean` as
`not_fibre_of_line`.  What is true, and what Corollary 9.7 (`ConvexFilters/Quotient.lean`)
was proved for, is that the whole fibre is collapsed *in the Hausdorff quotient*: the three
filters over a line are pairwise identified there, though only the two pairs involving the
`(1, 1)` filter are inseparable.  `fibre_of_line` below is stated in that corrected form,
with the middle filter exhibited.
-/

open Module

namespace ConvexFilter

namespace Space

/-! ## What `levVal` records -/

section LevVal

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {F F' : ConvexFilter V}

/-- `Nset F` is exactly the set of functionals at which `levVal F` is finite. -/
theorem mem_Nset_iff_levVal_ne (hF : IsMaximal F) (u : V →L[ℝ] ℝ) :
    u ∈ Nset F ↔ levVal F u ≠ ⊤ ∧ levVal F u ≠ ⊥ := by
  constructor
  · intro hu
    rw [levVal_of_mem_Nset hF hu]
    exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩
  · rintro ⟨h1, h2⟩
    rcases levVal_cases F hF u with ⟨-, hv⟩ | ⟨-, hv⟩ | ⟨hu, -⟩
    · exact absurd hv h1
    · exact absurd hv h2
    · exact hu

/-- `Eset F` is exactly the set of functionals at which `levVal F` is `⊤`. -/
theorem mem_Eset_iff_levVal_eq_top (hF : IsMaximal F) (u : V →L[ℝ] ℝ) :
    u ∈ Eset F ↔ levVal F u = ⊤ := by
  constructor
  · intro hu
    exact levVal_of_lev_eq_empty hu
  · intro hu
    rcases levVal_cases F hF u with ⟨h, -⟩ | ⟨-, hv⟩ | ⟨-, hv⟩
    · exact h
    · rw [hv] at hu; exact absurd hu (by simp)
    · rw [hv] at hu; exact absurd hu (by simp)

/-- **Theorem 9.9, the invariant `Nset`.** Two maximal filters with the same extended support
value everywhere have the same `Nset`. -/
theorem Nset_eq_of_levVal_eq (hF : IsMaximal F) (hF' : IsMaximal F')
    (h : ∀ u, levVal F u = levVal F' u) : Nset F = Nset F' := by
  ext u
  rw [mem_Nset_iff_levVal_ne hF, mem_Nset_iff_levVal_ne hF', h u]

/-- On `Nset`, the extended support value is the real support number, so it is determined
too. -/
theorem sig_eq_of_levVal_eq (hF : IsMaximal F) (hF' : IsMaximal F')
    (h : ∀ u, levVal F u = levVal F' u) {u : V →L[ℝ] ℝ} (hu : u ∈ Nset F) :
    sig F u = sig F' u := by
  have hu' : u ∈ Nset F' := (Nset_eq_of_levVal_eq hF hF' h) ▸ hu
  have := h u
  rw [levVal_of_mem_Nset hF hu, levVal_of_mem_Nset hF' hu'] at this
  exact_mod_cast this

/-- **Theorem 9.9, the invariant `Aset`.** Two maximal filters with the same extended support
value everywhere have the same flat. -/
theorem Aset_eq_of_levVal_eq (hF : IsMaximal F) (hF' : IsMaximal F')
    (h : ∀ u, levVal F u = levVal F' u) : Aset F = Aset F' := by
  have hN : Nset F = Nset F' := Nset_eq_of_levVal_eq hF hF' h
  ext x
  simp only [mem_Aset_iff]
  constructor
  · intro hx u hu
    have huF : u ∈ Nset F := hN ▸ hu
    rw [← sig_eq_of_levVal_eq hF hF' h huF]
    exact hx u huF
  · intro hx u hu
    rw [sig_eq_of_levVal_eq hF hF' h hu]
    exact hx u (hN ▸ hu)

/-- **Theorem 9.9, the invariant `Eset`.** Two maximal filters with the same extended support
value everywhere have the same escape cone. -/
theorem Eset_eq_of_levVal_eq (hF : IsMaximal F) (hF' : IsMaximal F')
    (h : ∀ u, levVal F u = levVal F' u) : Eset F = Eset F' := by
  ext u
  rw [mem_Eset_iff_levVal_eq_top hF, mem_Eset_iff_levVal_eq_top hF', h u]

/-- Two filters with the same level set at two functionals have the same extended support
value there: `levVal` is a function of `lev` alone. -/
theorem levVal_congr_of_lev_eq {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {G : ConvexFilter W} {u : V →L[ℝ] ℝ} {u' : W →L[ℝ] ℝ} (h : lev F u = lev G u') :
    levVal F u = levVal G u' := by
  simp only [levVal, sig]
  rw [h]

/-- The zero functional never lies in `Dset`: its support number `0` is attained. -/
theorem zero_notMem_Dset (F : ConvexFilter V) : (0 : V →L[ℝ] ℝ) ∉ Dset F := by
  rintro ⟨-, h⟩
  have h0 : sig F 0 = 0 := by rw [sig, lev_zero]; exact csInf_Ici
  rw [h0, lev_zero] at h
  exact h Set.self_mem_Ici

end LevVal

/-! ## The filter of stratum `(d, d)` beneath a maximal filter

Discarding the approach datum — replacing the positivity cone `Qset F = Eset F ∪ Dset F` by
the escape cone `Eset F` alone — leaves an admissible pair, so the classification produces a
maximal filter with the same flat and no `Dset`.  For a filter of the plane whose flat is a
line this is the filter called `F_ℓ` in the paper. -/

section Flat

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {F G : ConvexFilter V}

/-- The pair consisting of the flat of a maximal filter and its escape cone is admissible:
the escape cone is a lex cone modulo `Nset F`, because a functional lies outside `Nset F`
exactly when it or its negative escapes. -/
theorem isAdmissible_Aset_Eset (hF : IsMaximal F) : IsAdmissible (AsetAff F hF) (Eset F) := by
  have hann : annih (AsetAff F hF).direction = NsubmoduleOf F hF := by
    rw [direction_AsetAff hF]; exact annih_dirA hF
  have hsmul : ∀ ⦃c : ℝ⦄, 0 < c → ∀ ⦃x : V →L[ℝ] ℝ⦄, x ∈ Eset F → c • x ∈ Eset F := by
    intro c hc x hx
    show lev F (c • x) = ∅
    rw [Set.eq_empty_iff_forall_notMem]
    intro t ht
    have hmem : t / c ∈ lev F x := (mem_lev_smul_iff hc).mp ht
    rw [(hx : lev F x = ∅)] at hmem
    exact hmem
  have htri : ∀ ⦃x : V →L[ℝ] ℝ⦄, x ∈ (⊤ : Submodule ℝ (V →L[ℝ] ℝ)) →
      x ∈ Eset F ∨ x ∈ NsubmoduleOf F hF ∨ -x ∈ Eset F := by
    intro x _
    by_cases hx : lev F x = ∅
    · exact Or.inl hx
    · by_cases hnx : lev F (-x) = ∅
      · exact Or.inr (Or.inr hnx)
      · exact Or.inr (Or.inl ⟨hx, hnx⟩)
  have hnegE : ∀ ⦃x : V →L[ℝ] ℝ⦄, x ∈ Eset F → -x ∉ Eset F := by
    intro x hx hnx
    have huniv : lev F (-x) = Set.univ := lev_univ_of_lev_empty hF hx
    have h0 : (0 : ℝ) ∈ (∅ : Set ℝ) := by
      rw [← (hnx : lev F (-x) = ∅), huniv]; exact Set.mem_univ 0
    exact h0
  refine ⟨AsetAff_nonempty hF, ⟨NsubmoduleOf F hF, fun u => Iff.rfl,
    { M_le := le_top
      mem_of_mem := fun _ _ => trivial
      add_mem := fun _ _ hx hy => Eset_add hF hx hy
      smul_mem := hsmul
      trichotomy := htri
      notMem_M := fun _ hx hxN => hxN.1 hx
      neg_notMem := hnegE }, ?_⟩, ?_, ?_⟩
  · rw [hann]
  · rw [hann]
    intro w v hw hvw hv
    exfalso
    have hsum : w + (v - w) ∈ Eset F := Eset_add hF hw hvw
    have hveq : w + (v - w) = v := by abel
    rw [hveq] at hsum
    exact (hv : v ∈ Nset F).1 hsum
  · intro hbot
    rw [direction_AsetAff hF] at hbot
    have hQ := Qset_eq_empty_of_dirA_eq_bot hF hbot
    exact Set.eq_empty_of_subset_empty (hQ ▸ Eset_subset_Qset hF)

/-- **The filter of stratum `(d, d)` beneath a maximal filter.** There is a maximal convex
filter with the same flat as `F` and with positivity cone the escape cone of `F`: the
approach datum `Dset` is discarded. -/
theorem exists_maximal_flat (hF : IsMaximal F) :
    ∃ G : ConvexFilter V, IsMaximal G ∧ Aset G = Aset F ∧ Qset G = Eset F := by
  obtain ⟨G, hG, hA, hQ⟩ := exists_maximal_of_isAdmissible (isAdmissible_Aset_Eset hF)
  exact ⟨G, hG, by rw [hA, coe_AsetAff hF], hQ⟩

/-- The filter beneath `F` has the same escape cone as `F`. -/
theorem Eset_eq_of_Qset_eq_Eset (hF : IsMaximal F) (hG : IsMaximal G)
    (hA : Aset G = Aset F) (hQ : Qset G = Eset F) : Eset G = Eset F := by
  have hN : Nset G = Nset F := Nset_eq_of_Aset_eq hG hF hA
  ext u
  constructor
  · intro hu
    rw [← hQ]
    exact Eset_subset_Qset hG hu
  · intro hu
    have huQ : u ∈ Qset G := by rw [hQ]; exact hu
    rcases (Qset_eq_Eset_union_Dset hG ▸ huQ : u ∈ Eset G ∪ Dset G) with h | h
    · exact h
    · exact absurd hu (fun hE => ((hN ▸ h.1 : u ∈ Nset F)).1 hE)

/-- The filter beneath `F` has no approach datum. -/
theorem Dset_eq_empty_of_Qset_eq_Eset (hF : IsMaximal F) (hG : IsMaximal G)
    (hA : Aset G = Aset F) (hQ : Qset G = Eset F) : Dset G = ∅ := by
  have hN : Nset G = Nset F := Nset_eq_of_Aset_eq hG hF hA
  rw [Set.eq_empty_iff_forall_notMem]
  intro u hu
  have huE : u ∈ Eset F := by rw [← hQ]; exact Dset_subset_Qset hG hu
  exact ((hN ▸ hu.1 : u ∈ Nset F)).1 huE

omit [FiniteDimensional ℝ V] in
/-- A maximal filter with no approach datum contains the level hyperplane of every
functional of its `Nset`: the support number is attained on both sides. -/
theorem hyperplane_mem_of_Dset_eq_empty (hG : IsMaximal G) (hD : Dset G = ∅)
    {u : V →L[ℝ] ℝ} (hu : u ∈ Nset G) : hyperplane u (sig G u) ∈ G.carrier := by
  have hle : halfLE u (sig G u) ∈ G.carrier := by
    by_contra hcon
    have hmem : u ∈ Dset G := ⟨hu, hcon⟩
    rw [hD] at hmem
    exact hmem
  have hu' : -u ∈ Nset G := Nset_neg hu
  have hle' : halfLE (-u) (sig G (-u)) ∈ G.carrier := by
    by_contra hcon
    have hmem : -u ∈ Dset G := ⟨hu', hcon⟩
    rw [hD] at hmem
    exact hmem
  rw [sig_neg hG hu, halfLE_neg] at hle'
  rw [← halfLE_inter_halfGE]
  exact G.inter_mem hle hle'

end Flat

/-! ## The plane -/

section Plane

open SigCounterexample

variable {F F' G : ConvexFilter (ℝ × ℝ)}

theorem finrank_plane : finrank ℝ (ℝ × ℝ) = 2 := by simp

/-- A functional of the plane vanishing on both basis vectors is zero. -/
theorem eq_zero_of_coords_eq_zero {u : (ℝ × ℝ) →L[ℝ] ℝ} (h1 : u (1, 0) = 0)
    (h2 : u (0, 1) = 0) : u = 0 := by
  refine ContinuousLinearMap.ext fun p => ?_
  rw [apply_eq u p, h1, h2]
  simp

/-- If the flat of a maximal filter of the plane is a line, then `Nset F` is the line of the
dual spanned by any of its nonzero elements. -/
theorem exists_smul_eq_of_mem_Nset (hF : IsMaximal F) (hdim : finrank ℝ (dirA F) = 1)
    {v u : (ℝ × ℝ) →L[ℝ] ℝ} (hv : v ∈ Nset F) (hv0 : v ≠ 0) (hu : u ∈ Nset F) :
    ∃ t : ℝ, u = t • v := by
  -- a nonzero direction of the flat
  have hne : dirA F ≠ ⊥ := by
    intro hbot
    rw [hbot] at hdim
    simp at hdim
  obtain ⟨w, hwmem, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hann := Nset_eq_annihilator_dirA hF
  have huw : u w = 0 := by rw [hann] at hu; exact hu w hwmem
  have hvw : v w = 0 := by rw [hann] at hv; exact hv w hwmem
  rw [apply_eq u w] at huw
  rw [apply_eq v w] at hvw
  -- the coordinates of `v` are not both zero
  have hvc : ¬ (v (1, 0) = 0 ∧ v (0, 1) = 0) := by
    rintro ⟨h1, h2⟩
    exact hv0 (eq_zero_of_coords_eq_zero h1 h2)
  have hwc : ¬ (w.1 = 0 ∧ w.2 = 0) := by
    rintro ⟨h1, h2⟩
    exact hw0 (Prod.ext h1 h2)
  -- the two functionals are proportional
  have hcross : u (1, 0) * v (0, 1) = u (0, 1) * v (1, 0) := by
    rcases not_and_or.mp hwc with hw1 | hw2
    · have hkey : w.1 * (u (1, 0) * v (0, 1) - u (0, 1) * v (1, 0)) = 0 := by
        linear_combination v (0, 1) * huw - u (0, 1) * hvw
      rcases mul_eq_zero.mp hkey with h | h
      · exact absurd h hw1
      · linarith
    · have hkey : w.2 * (u (1, 0) * v (0, 1) - u (0, 1) * v (1, 0)) = 0 := by
        linear_combination (-(v (1, 0))) * huw + u (1, 0) * hvw
      rcases mul_eq_zero.mp hkey with h | h
      · exact absurd h hw2
      · linarith
  have hpos : 0 < v (1, 0) ^ 2 + v (0, 1) ^ 2 := by
    rcases not_and_or.mp hvc with h | h
    · have hsq := sq_pos_of_ne_zero h
      nlinarith [sq_nonneg (v (0, 1))]
    · have hsq := sq_pos_of_ne_zero h
      nlinarith [sq_nonneg (v (1, 0))]
  have e1 : u (1, 0) * (v (1, 0) ^ 2 + v (0, 1) ^ 2)
      = (u (1, 0) * v (1, 0) + u (0, 1) * v (0, 1)) * v (1, 0) := by
    linear_combination v (0, 1) * hcross
  have e2 : u (0, 1) * (v (1, 0) ^ 2 + v (0, 1) ^ 2)
      = (u (1, 0) * v (1, 0) + u (0, 1) * v (0, 1)) * v (0, 1) := by
    linear_combination (-(v (1, 0))) * hcross
  refine ⟨(u (1, 0) * v (1, 0) + u (0, 1) * v (0, 1)) / (v (1, 0) ^ 2 + v (0, 1) ^ 2), ?_⟩
  refine ContinuousLinearMap.ext fun p => ?_
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul, apply_eq u p, apply_eq v p,
    div_mul_eq_mul_div, eq_div_iff (ne_of_gt hpos)]
  linear_combination p.1 * e1 + p.2 * e2

/-- If the flat of a maximal filter of the plane is a line, it is the level hyperplane of
any nonzero functional of `Nset F`. -/
theorem Aset_eq_hyperplane (hF : IsMaximal F) (hdim : finrank ℝ (dirA F) = 1)
    {v : (ℝ × ℝ) →L[ℝ] ℝ} (hv : v ∈ Nset F) (hv0 : v ≠ 0) :
    Aset F = hyperplane v (sig F v) := by
  ext x
  constructor
  · intro hx
    exact hx v hv
  · intro hx u hu
    obtain ⟨t, rfl⟩ := exists_smul_eq_of_mem_Nset hF hdim hv hv0 hu
    rw [sig_smul hF hv t]
    show t * v x = t * sig F v
    rw [(hx : v x = sig F v)]

/-- **The fibre over a line, the key step.** Let `F` be a maximal filter of the plane whose
flat is a line and let `G` be the filter of stratum `(1, 1)` beneath it, with the same flat
and with positivity cone the escape cone of `F`.  Then either `F = G`, or `F` is a filter of
stratum `(1, 2)` approaching the line from one side and is inseparable from `G`, by
Theorem 9.5. -/
theorem fibre_of_line_flat (hF : IsMaximal F) (hG : IsMaximal G)
    (hdim : finrank ℝ (dirA F) = 1) (hA : Aset G = Aset F) (hQ : Qset G = Eset F) :
    F = G ∨ ¬ Separated G F := by
  by_cases hD : Dset F = ∅
  · refine Or.inl (eq_of_Aset_Qset hF hG hA.symm ?_)
    rw [hQ, Qset_eq_Eset_union_Dset hF, hD, Set.union_empty]
  · right
    obtain ⟨v, hv⟩ := Set.nonempty_iff_ne_empty.mpr hD
    have hvN : v ∈ Nset F := hv.1
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact zero_notMem_Dset F hv
    set c : ℝ := sig F v with hc
    have hAF : Aset F = hyperplane v c := Aset_eq_hyperplane hF hdim hvN hv0
    -- the setting of Theorem 9.5: the line `A` inside the plane `S`
    have hAeq : ((AsetAff G hG : AffineSubspace ℝ (ℝ × ℝ)) : Set (ℝ × ℝ))
        = ((⊤ : AffineSubspace ℝ (ℝ × ℝ)) : Set (ℝ × ℝ)) ∩ {x : ℝ × ℝ | v x = c} := by
      rw [AffineSubspace.top_coe, Set.univ_inter, coe_AsetAff hG, hA, hAF]
      rfl
    have hdirG : (AsetAff G hG).direction = dirA G := direction_AsetAff hG
    have hdirGF : dirA G = dirA F := dirA_eq_of_Aset_eq hG hA
    have hdA : 1 ≤ finrank ℝ (AsetAff G hG).direction := by
      rw [hdirG, hdirGF, hdim]
    have hcodim : finrank ℝ (⊤ : AffineSubspace ℝ (ℝ × ℝ)).direction
        = finrank ℝ (AsetAff G hG).direction + 1 := by
      rw [hdirG, hdirGF, hdim, AffineSubspace.direction_top, finrank_top, finrank_plane]
    -- the invariants of the two filters
    have hAsetG : Aset G = ((AsetAff G hG : AffineSubspace ℝ (ℝ × ℝ)) : Set (ℝ × ℝ)) :=
      (coe_AsetAff hG).symm
    have hAsetF : Aset F = ((AsetAff G hG : AffineSubspace ℝ (ℝ × ℝ)) : Set (ℝ × ℝ)) := by
      rw [coe_AsetAff hG, hA]
    have hEsc : Eset F = Eset G := (Eset_eq_of_Qset_eq_Eset hF hG hA hQ).symm
    -- the flat belongs to the filter beneath, being a level hyperplane
    have hAmem : ((AsetAff G hG : AffineSubspace ℝ (ℝ × ℝ)) : Set (ℝ × ℝ)) ∈ G.carrier := by
      have hvG : v ∈ Nset G := (Nset_eq_of_Aset_eq hG hF hA) ▸ hvN
      have hsigG : sig G v = sig F v := by
        obtain ⟨a, ha⟩ := Aset_nonempty hG
        have ha' : a ∈ Aset F := hA ▸ ha
        rw [sig_eq_of_mem_Aset ha hvG, sig_eq_of_mem_Aset ha' hvN]
      have := hyperplane_mem_of_Dset_eq_empty hG
        (Dset_eq_empty_of_Qset_eq_Eset hF hG hA hQ) hvG
      rw [hsigG] at this
      rw [coe_AsetAff hG, hA, hAF]
      exact this
    -- the side condition: the support number of `v` is not attained on `F`
    have hside : halfLE v c ∉ F.carrier := hv.2
    exact not_separated_gen hAeq hdA hcodim hG hF hAsetG hAmem hAsetF
      (by rw [AffineSubspace.top_coe]; exact F.univ_mem) hEsc hside

/-- Over a flat of dimension two the fibre of `levVal` is a singleton: there is no approach
datum to discard, so the flat and the escape cone already determine the filter. -/
theorem Dset_eq_empty_of_dirA_eq_top (hF : IsMaximal F) (h : dirA F = ⊤) : Dset F = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro u hu
  have hu0 : u = 0 := by
    have hann := Nset_eq_annihilator_dirA hF
    have huN : u ∈ Nset F := hu.1
    rw [hann] at huN
    refine ContinuousLinearMap.ext fun x => ?_
    rw [huN x (by rw [h]; trivial)]
    rfl
  exact zero_notMem_Dset F (hu0 ▸ hu)

/-- **Theorem 9.9, the two-dimensional stratum.** Two maximal filters of the plane with the
same extended support value everywhere and with a two-dimensional flat are equal. -/
theorem eq_of_levVal_eq_of_dim_two (hF : IsMaximal F) (hF' : IsMaximal F')
    (h : ∀ u, levVal F u = levVal F' u) (hdim : finrank ℝ (dirA F) = 2) : F = F' := by
  have hA : Aset F = Aset F' := Aset_eq_of_levVal_eq hF hF' h
  have hdirF : dirA F = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [hdim, finrank_plane]
  have hdirF' : dirA F' = ⊤ := (dirA_eq_of_Aset_eq hF hA) ▸ hdirF
  have hQ : Qset F = Qset F' := by
    rw [Qset_eq_Eset_union_Dset hF, Qset_eq_Eset_union_Dset hF',
      Dset_eq_empty_of_dirA_eq_top hF hdirF, Dset_eq_empty_of_dirA_eq_top hF' hdirF',
      Eset_eq_of_levVal_eq hF hF' h]
  exact eq_of_Aset_Qset hF hF' hA hQ

/-- **Theorem 9.9, the principal stratum.** Two maximal filters of the plane with the same
extended support value everywhere and with a zero-dimensional flat are equal: both are
principal, at the same point. -/
theorem eq_of_levVal_eq_of_dim_zero (hF : IsMaximal F) (hF' : IsMaximal F')
    (h : ∀ u, levVal F u = levVal F' u) (hdim : finrank ℝ (dirA F) = 0) : F = F' := by
  have hA : Aset F = Aset F' := Aset_eq_of_levVal_eq hF hF' h
  have hdirF : dirA F = ⊥ := Submodule.finrank_eq_zero.mp hdim
  have hdirF' : dirA F' = ⊥ := (dirA_eq_of_Aset_eq hF hA) ▸ hdirF
  have hQ : Qset F = Qset F' := by
    rw [Qset_eq_empty_of_dirA_eq_bot hF hdirF, Qset_eq_empty_of_dirA_eq_bot hF' hdirF']
  exact eq_of_Aset_Qset hF hF' hA hQ

/-- **Theorem 9.9, the fibre over a line, corrected form.** Two maximal filters of the plane
with the same extended support value everywhere and with a one-dimensional flat are either
equal or both attached to one common filter — the filter of stratum `(1, 1)` over the same
line — from which each is either equal or inseparable.  The contract form of this statement,
with the conclusion `F = F' ∨ ¬ Separated F F'`, is false; see the module docstring and
`ConvexFilters/FibreCounterexample.lean`. -/
theorem fibre_of_line (hF : IsMaximal F) (hF' : IsMaximal F')
    (h : ∀ u, levVal F u = levVal F' u) (hdim : finrank ℝ (dirA F) = 1) :
    ∃ G : ConvexFilter (ℝ × ℝ), IsMaximal G ∧ (F = G ∨ ¬ Separated G F) ∧
      (F' = G ∨ ¬ Separated G F') := by
  obtain ⟨G, hG, hAG, hQG⟩ := exists_maximal_flat hF
  have hA : Aset F = Aset F' := Aset_eq_of_levVal_eq hF hF' h
  have hE : Eset F = Eset F' := Eset_eq_of_levVal_eq hF hF' h
  have hdim' : finrank ℝ (dirA F') = 1 := by
    rw [← dirA_eq_of_Aset_eq hF hA]; exact hdim
  refine ⟨G, hG, fibre_of_line_flat hF hG hdim hAG hQG, ?_⟩
  exact fibre_of_line_flat hF' hG hdim' (hAG.trans hA) (hQG.trans hE)

/-- A maximal convex filter, packaged as a point of `MaxFilter V`. -/
def toMax {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (G : ConvexFilter V)
    (hG : IsMaximal G) : MaxFilter V := ⟨G, hG⟩

/-- The three strata of the plane: the flat of a maximal filter of the plane has dimension
`0`, `1` or `2`. -/
theorem finrank_dirA_le_two (F : ConvexFilter (ℝ × ℝ)) : finrank ℝ (dirA F) ≤ 2 := by
  have := Submodule.finrank_le (dirA F)
  rwa [finrank_plane] at this

/-! ## Theorem 9.9, first clause -/

/-- **Theorem 9.9, first clause.** Two maximal convex filters of the plane have the same
image in the maximal Hausdorff quotient if and only if their extended support values agree
at every functional.

The direction from `levVal` to the quotient is the enumeration of the fibres: over a
zero- or two-dimensional flat the fibre is a singleton, and over a line it consists of
filters each identified in the quotient with the filter of stratum `(1, 1)` over that line,
by Corollary 9.7.  The converse is `sigma_continuous`, through the universal property of
the quotient. -/
theorem levVal_separates_quotient {F F' : MaxFilter (ℝ × ℝ)} :
    (∀ u, levVal F.1 u = levVal F'.1 u) ↔ T2Quotient.mk F = T2Quotient.mk F' := by
  constructor
  · intro h
    have hle := finrank_dirA_le_two F.1
    interval_cases hd : finrank ℝ (dirA F.1)
    · exact congrArg _ (Subtype.ext (eq_of_levVal_eq_of_dim_zero F.2 F'.2 h hd))
    · obtain ⟨G, hG, hFG, hF'G⟩ := fibre_of_line F.2 F'.2 h hd
      have h1 : T2Quotient.mk F = T2Quotient.mk (toMax G hG) := by
        rcases hFG with rfl | hsep
        · rfl
        · exact (t2Quotient_mk_eq_of_not_separated (F := toMax G hG) (F' := F) hsep).symm
      have h2 : T2Quotient.mk F' = T2Quotient.mk (toMax G hG) := by
        rcases hF'G with rfl | hsep
        · rfl
        · exact (t2Quotient_mk_eq_of_not_separated (F := toMax G hG) (F' := F') hsep).symm
      rw [h1, h2]
    · exact congrArg _ (Subtype.ext (eq_of_levVal_eq_of_dim_two F.2 F'.2 h hd))
  · intro h u
    have hcont : Continuous (fun G : MaxFilter (ℝ × ℝ) => levVal G.1 u) := sigma_continuous u
    have := congrArg (T2Quotient.lift hcont) h
    rwa [T2Quotient.lift_mk, T2Quotient.lift_mk] at this

/-- **Theorem 9.9, first clause, in elementary terms.** Two maximal convex filters of the
plane have the same image under every continuous map to a Hausdorff space if and only if
their extended support values agree at every functional. -/
theorem levVal_eq_iff_forall_continuous_eq {F F' : MaxFilter (ℝ × ℝ)} :
    (∀ u, levVal F.1 u = levVal F'.1 u) ↔
      ∀ (Y : Type) [TopologicalSpace Y] [T2Space Y] (f : MaxFilter (ℝ × ℝ) → Y),
        Continuous f → f F = f F' := by
  constructor
  · intro h Y _ _ f hf
    have hq : T2Quotient.mk F = T2Quotient.mk F' := levVal_separates_quotient.mp h
    have := congrArg (T2Quotient.lift hf) hq
    rwa [T2Quotient.lift_mk, T2Quotient.lift_mk] at this
  · intro h u
    exact h EReal (fun G : MaxFilter (ℝ × ℝ) => levVal G.1 u) (sigma_continuous u)

end Plane

end Space

end ConvexFilter
