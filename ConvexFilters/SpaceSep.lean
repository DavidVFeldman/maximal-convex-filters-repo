import ConvexFilters.SpaceCover
import ConvexFilters.RemarkFamily

/-!
# The space of maximal convex filters: separation (Section 9, Parts C and D)

Theorem 9.4 and Corollary 9.5 of the paper, stated combinatorially through the relation
`ConvexFilter.Space.Separated` of `ConvexFilters/SpaceCover.lean`.

* `not_separated_Fline_Ghyp` (Theorem 9.4, first clause): the line filter and the filter
  confined to the line from the right cannot be separated;
* `separated_Ghyp_Fminus` (Theorem 9.4, second clause): the two confined filters are
  separated, by the two closed half-planes;
* `not_separated_Fline_Fminus`: the first clause reflected in the `y`-axis;
* `separated_not_transitive` (Corollary 9.5): inseparability is not a transitive relation.
-/

namespace ConvexFilter

namespace Space

open SigCounterexample

/-! ## Part C — inseparability of the line filter and the confined filter -/

/-- The trace of a set on the vertical axis is bounded above, or it is not. -/
private def UnbddOnAxis (E : Set (ℝ × ℝ)) : Prop := ∀ b : ℝ, ∃ y : ℝ, b ≤ y ∧ ((0 : ℝ), y) ∈ E

/-- A choice of upper bound for the trace of `E` on the vertical axis, when there is one. -/
private noncomputable def axisBound (E : Set (ℝ × ℝ)) : ℝ := by
  classical
  exact if h : ∃ b : ℝ, ∀ y : ℝ, ((0 : ℝ), y) ∈ E → y ≤ b then h.choose else 0

private theorem le_axisBound {E : Set (ℝ × ℝ)} (h : ¬ UnbddOnAxis E) {y : ℝ}
    (hy : ((0 : ℝ), y) ∈ E) : y ≤ axisBound E := by
  classical
  have hex : ∃ b : ℝ, ∀ y : ℝ, ((0 : ℝ), y) ∈ E → y ≤ b := by
    unfold UnbddOnAxis at h
    push_neg at h
    obtain ⟨b, hb⟩ := h
    refine ⟨b, fun y hyE => ?_⟩
    by_contra hcon
    exact absurd hyE (hb y (le_of_lt (not_le.mp hcon))).elim
  unfold axisBound
  rw [dif_pos hex]
  exact hex.choose_spec y hy

/-- A closed convex set whose trace on the vertical axis is unbounded above and which
contains a point of positive first coordinate belongs to `Ghyp`. -/
theorem mem_Ghyp_of_unbdd_of_fst_pos {E : Set (ℝ × ℝ)} (hcl : IsClosed E) (hcv : Convex ℝ E)
    (hunb : ∀ b : ℝ, ∃ y : ℝ, b ≤ y ∧ ((0 : ℝ), y) ∈ E)
    {q : ℝ × ℝ} (hq : q ∈ E) (hq1 : 0 < q.1) : E ∈ Ghyp.carrier := by
  obtain ⟨k, hk⟩ := exists_upRay_subset hcv hunb
  refine wedge hcl hcv (a := (k : ℝ)) (x₀ := q.1) (y₀ := q.2) ?_ hq1 ?_
  · intro p hp
    exact hk ⟨hp.1, hp.2⟩
  · rwa [Prod.mk.eta]

/-- **Theorem 9.4, first clause.** The line filter and the filter confined to the line from
the right cannot be separated. -/
theorem not_separated_Fline_Ghyp : ¬ Separated Fline SigCounterexample.Ghyp := by
  classical
  rintro ⟨s, hcl, hcv, hcover, hsep⟩
  set N : Finset (Set (ℝ × ℝ)) := s.filter (fun E => ¬ UnbddOnAxis E) with hN
  -- members of `s` unbounded on the axis contain no point of positive first coordinate
  have hLhalf : ∀ E ∈ s, UnbddOnAxis E → ∀ q ∈ E, q.1 ≤ 0 := by
    intro E hE hunb q hq
    by_contra hcon
    push_neg at hcon
    have hGhyp : E ∈ Ghyp.carrier :=
      mem_Ghyp_of_unbdd_of_fst_pos (hcl E hE) (hcv E hE) hunb hq hcon
    obtain ⟨k, hk⟩ := exists_upRay_subset (hcv E hE) hunb
    have hFline : E ∈ Fline.carrier := (mem_Fline_iff (hcl E hE) (hcv E hE)).mpr ⟨k, hk⟩
    exact hsep E hE ⟨hFline, hGhyp⟩
  -- the open right half-plane is covered by the members with bounded trace
  have hcovN : {p : ℝ × ℝ | 0 < p.1} ⊆ ⋃ E ∈ N, E := by
    intro q hq
    have hquniv : q ∈ (⋃ E ∈ s, E) := by rw [hcover]; exact Set.mem_univ q
    simp only [Set.mem_iUnion] at hquniv
    obtain ⟨E, hEs, hqE⟩ := hquniv
    have hnot : ¬ UnbddOnAxis E := by
      intro hunb
      exact absurd (hLhalf E hEs hunb q hqE) (not_le.mpr hq)
    exact Set.mem_biUnion (Finset.mem_filter.mpr ⟨hEs, hnot⟩) hqE
  -- that union is closed, so it contains the whole vertical axis
  have hNcl : IsClosed (⋃ E ∈ N, E) := by
    refine Set.Finite.isClosed_biUnion N.finite_toSet fun E hE => ?_
    exact hcl E (Finset.mem_filter.mp hE).1
  obtain ⟨B, hB⟩ := (N.image axisBound).exists_le
  have haxis : ((0 : ℝ), B + 1) ∈ ⋃ E ∈ N, E := by
    refine hNcl.closure_subset (closure_mono hcovN ?_)
    have htend : Filter.Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1), B + 1) : ℝ × ℝ))
        Filter.atTop (nhds ((0 : ℝ), B + 1)) := by
      refine Filter.Tendsto.prodMk_nhds ?_ tendsto_const_nhds
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    refine mem_closure_of_tendsto htend ?_
    filter_upwards with n
    show (0 : ℝ) < 1 / ((n : ℝ) + 1)
    positivity
  simp only [Set.mem_iUnion] at haxis
  obtain ⟨E, hEN, hmem⟩ := haxis
  have hnot : ¬ UnbddOnAxis E := (Finset.mem_filter.mp hEN).2
  have h1 : B + 1 ≤ axisBound E := le_axisBound hnot hmem
  have h2 : axisBound E ≤ B := hB _ (Finset.mem_image_of_mem axisBound hEN)
  linarith

/-! ## Part D — separation of the two confined filters, and non-transitivity -/

/-- The closed left half-plane. -/
def leftHalf : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 ≤ 0}

/-- The closed right half-plane. -/
def rightHalf : Set (ℝ × ℝ) := {p : ℝ × ℝ | 0 ≤ p.1}

theorem isClosed_leftHalf : IsClosed leftHalf := isClosed_le continuous_fst continuous_const

theorem isClosed_rightHalf : IsClosed rightHalf := isClosed_le continuous_const continuous_fst

theorem convex_leftHalf : Convex ℝ leftHalf := by
  rintro x hx y hy a b ha hb hab
  show a * x.1 + b * y.1 ≤ 0
  have hx' : x.1 ≤ 0 := hx
  have hy' : y.1 ≤ 0 := hy
  nlinarith

theorem convex_rightHalf : Convex ℝ rightHalf := by
  rintro x hx y hy a b ha hb hab
  show 0 ≤ a * x.1 + b * y.1
  have hx' : 0 ≤ x.1 := hx
  have hy' : 0 ≤ y.1 := hy
  nlinarith

theorem preimage_reflCLM_rightHalf : (⇑reflCLM ⁻¹' rightHalf) = leftHalf := by
  ext p
  simp only [Set.mem_preimage, reflCLM_apply, rightHalf, leftHalf, Set.mem_setOf_eq]
  constructor
  · intro h; linarith
  · intro h; linarith

theorem leftHalf_notMem_Ghyp : leftHalf ∉ Ghyp.carrier := by
  refine notMem_carrier_of_base_disjoint hyp_mem_Ghyp (n := 0) ?_
  ext p
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hp hleft
  exact absurd (hleft : p.1 ≤ 0) (not_le.mpr (hyp_pos hp))

theorem rightHalf_notMem_Fminus : rightHalf ∉ Fminus.carrier := by
  rw [mem_Fminus_iff, preimage_reflCLM_rightHalf]
  exact leftHalf_notMem_Ghyp

/-- **Theorem 9.4, second clause.** The two filters confined to the line, from the right
and from the left, are separated by the two closed half-planes. -/
theorem separated_Ghyp_Fminus : Separated SigCounterexample.Ghyp Fminus := by
  classical
  refine ⟨{leftHalf, rightHalf}, ?_, ?_, ?_, ?_⟩
  · intro E hE
    rcases Finset.mem_insert.mp hE with rfl | hE
    · exact isClosed_leftHalf
    · rw [Finset.mem_singleton.mp hE]; exact isClosed_rightHalf
  · intro E hE
    rcases Finset.mem_insert.mp hE with rfl | hE
    · exact convex_leftHalf
    · rw [Finset.mem_singleton.mp hE]; exact convex_rightHalf
  · refine Set.eq_univ_of_forall fun p => ?_
    rcases le_total p.1 0 with h | h
    · exact Set.mem_biUnion (Finset.mem_insert_self _ _) h
    · exact Set.mem_biUnion (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) h
  · intro E hE
    rcases Finset.mem_insert.mp hE with rfl | hE
    · rintro ⟨h, -⟩
      exact leftHalf_notMem_Ghyp h
    · rw [Finset.mem_singleton.mp hE]
      rintro ⟨-, h⟩
      exact rightHalf_notMem_Fminus h

/-! ### The line filter is invariant under the reflection -/

theorem preimage_reflCLM_upRay (k : ℕ) : (⇑reflCLM ⁻¹' upRay k) = upRay k := by
  ext p
  simp only [Set.mem_preimage, reflCLM_apply, upRay, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [h2]; ring⟩

theorem comapEquiv_reflCLM_Fline : comapEquiv reflCLM Fline = Fline := by
  refine eq_of_carrier_eq ?_
  ext C
  constructor
  · intro hC
    have hpre : (⇑reflCLM ⁻¹' C) ∈ Fline.carrier := hC
    obtain ⟨hcl, hcv, k, hk⟩ := hpre
    refine ⟨?_, ?_, k, ?_⟩
    · have h : (⇑reflCLM ⁻¹' (⇑reflCLM ⁻¹' C)) = C := by ext x; simp
      rw [← h]
      exact hcl.preimage reflCLM.continuous
    · have h : (⇑reflCLM ⁻¹' (⇑reflCLM ⁻¹' C)) = C := by ext x; simp
      rw [← h]
      exact hcv.linear_preimage (reflCLM : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))
    · rw [← preimage_reflCLM_upRay k] at hk
      intro p hp
      have : reflCLM p ∈ ⇑reflCLM ⁻¹' C := by
        apply hk
        rw [Set.mem_preimage]
        have hinv : reflCLM (reflCLM p) = p := by
          simp
        rw [hinv]
        exact hp
      simpa using this
  · rintro ⟨hcl, hcv, k, hk⟩
    show (⇑reflCLM ⁻¹' C) ∈ Fline.carrier
    refine ⟨hcl.preimage reflCLM.continuous,
      hcv.linear_preimage (reflCLM : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)), k, ?_⟩
    rw [← preimage_reflCLM_upRay k]
    exact Set.preimage_mono hk

theorem comapEquiv_reflCLM_Fminus : comapEquiv reflCLM Fminus = Ghyp := by
  refine eq_of_carrier_eq ?_
  ext C
  show (⇑reflCLM ⁻¹' (⇑reflCLM ⁻¹' C)) ∈ Ghyp.carrier ↔ C ∈ Ghyp.carrier
  have h : (⇑reflCLM ⁻¹' (⇑reflCLM ⁻¹' C)) = C := by ext x; simp
  rw [h]

/-- **Theorem 9.4, first clause, reflected.** The line filter and the filter confined to
the line from the left cannot be separated either. -/
theorem not_separated_Fline_Fminus : ¬ Separated Fline Fminus := by
  intro h
  have h' := h.comapEquiv reflCLM
  rw [comapEquiv_reflCLM_Fline, comapEquiv_reflCLM_Fminus] at h'
  exact not_separated_Fline_Ghyp h'

/-- **Corollary 9.5.** Inseparability is not transitive: the filter confined to the line
from the right and the filter confined to it from the left are both inseparable from the
line filter, yet are separated from each other. -/
theorem separated_not_transitive :
    ∃ F G H : ConvexFilter (ℝ × ℝ), IsMaximal F ∧ IsMaximal G ∧ IsMaximal H ∧
      ¬ Separated F G ∧ ¬ Separated G H ∧ Separated F H := by
  refine ⟨SigCounterexample.Ghyp, Fline, Fminus, Ghyp_isMaximal, Fline_isMaximal,
    Fminus_isMaximal, ?_, not_separated_Fline_Fminus, separated_Ghyp_Fminus⟩
  intro h
  exact not_separated_Fline_Ghyp h.symm

end Space

end ConvexFilter
