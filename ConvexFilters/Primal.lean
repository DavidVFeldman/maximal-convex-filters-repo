import ConvexFilters.Classification

/-!
# Theorem 1.2, the primal form

This file is Part D of WO-06b. Theorem 6.1 classifies the maximal convex filters by the pair
`(A, Q)` consisting of the flat and the positivity cone in the *dual*. Theorem 1.2 of the
paper states the classification in the primal form `(A, W, ≺)`, with `W ⊆ V` a subspace
containing `dir A` and `≺` a vector space order on `W` in which `dir A` is order convex.

The order `≺` is presented by its positive cone, and the positive cone is defined
intrinsically from `Q`:

`primalCone Q W = {x ∈ W | ∃ u₀ ∈ Q, 0 < u₀ x ∧ ∀ u ∈ Q, u₀ - u ∈ Q → 0 ≤ u x}`.

The crux is `primalCone_eq_lexCone`: in an adapted basis, where `Q` is the cone `Q0` of
functionals whose *first* nonvanishing coordinate among the first `m` is positive, the primal
cone is the set of vectors of `W` whose *last* nonvanishing coordinate among the first `m` is
positive. The reversal is the content of the duality of Definition 3.3 of the paper.

## Main results

* `ConvexFilter.primalCone_eq_lexCone` — the computation in an adapted basis;
* `ConvexFilter.isLexConeOn_primalCone` — the primal cone is a vector space order on `W`;
* `ConvexFilter.isOrderConvex_primalCone` — `dir A` is order convex for it;
* `ConvexFilter.classification_primal` — Theorem 1.2.
-/

open Module

namespace ConvexFilter

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The positive cone of the primal order attached to a cone `Q` in the dual and a subspace
`W ⊆ V`: the `x ∈ W` on which some `u₀ ∈ Q` is positive and every `Q`-smaller member of `Q`
is nonnegative, where `u` is `Q`-smaller than `u₀` when `u₀ - u ∈ Q`. -/
def primalCone (Q : Set (V →L[ℝ] ℝ)) (W : Submodule ℝ V) : Set V :=
  {x | x ∈ W ∧ ∃ u₀ ∈ Q, 0 < u₀ x ∧ ∀ u ∈ Q, u₀ - u ∈ Q → 0 ≤ u x}

/-! ## The computation in an adapted basis -/

section Adapted

variable {n : ℕ} (b : Basis (Fin n) ℝ V)

theorem coordCLM_eq_coordAt {j : ℕ} (hj : j < n) (x : V) :
    coordCLM b ⟨j, hj⟩ x = coordAt b 0 j x := by
  rw [coordAt_of_lt hj, coordCLM_apply, sub_zero]

theorem coordCLM_basisAt {p : Fin n} {i : ℕ} (hi : i < n) :
    coordCLM b p (basisAt b i) = if i = (p : ℕ) then 1 else 0 := by
  rw [basisAt_of_lt b hi, coordCLM_apply, Basis.coord_apply, Basis.repr_self,
    Finsupp.single_apply]
  simp [Fin.ext_iff, eq_comm]

omit [FiniteDimensional ℝ V] in
/-- A functional evaluated on a vector of the span of the first `m` basis vectors is the
corresponding finite combination of its first `m` coordinates. -/
theorem apply_eq_sum_first {m : ℕ} (hmn : m ≤ n) (u : V →L[ℝ] ℝ) {x : V}
    (hx : x ∈ Submodule.span ℝ (Set.range (fun i : Fin m => basisAt b (i : ℕ)))) :
    u x = ∑ i ∈ Finset.range m, u (basisAt b i) * coordAt b 0 i x := by
  have hzero : ∀ i, m ≤ i → coordAt b 0 i x = 0 := by
    intro i hi
    by_cases hin : i < n
    · have := (mem_span_basisAt_iff b m x).1 hx ⟨i, hin⟩ hi
      rw [coordAt_of_lt hin, sub_zero]
      exact this
    · exact coordAt_of_le (Nat.not_lt.1 hin) x
  rw [apply_eq_sum_coordAt b 0 u x, map_zero, zero_add]
  have hsub : Finset.range m ⊆ Finset.range n := Finset.range_subset_range.2 hmn
  refine (Finset.sum_subset hsub ?_).symm
  intro i _ hi
  rw [hzero i (by simpa using hi), mul_zero]

end Adapted

section CoordAlgebra

variable {n : ℕ} {b : Basis (Fin n) ℝ V}

omit [FiniteDimensional ℝ V] in
theorem coordAt_zero_add (i : ℕ) (x y : V) :
    coordAt b 0 i (x + y) = coordAt b 0 i x + coordAt b 0 i y := by
  unfold coordAt
  split
  · simp [map_add]
  · simp

omit [FiniteDimensional ℝ V] in
theorem coordAt_zero_smul (c : ℝ) (i : ℕ) (x : V) :
    coordAt b 0 i (c • x) = c * coordAt b 0 i x := by
  unfold coordAt
  split
  · simp [map_smul]
  · simp

omit [FiniteDimensional ℝ V] in
theorem coordAt_zero_zero (i : ℕ) : coordAt b 0 i (0 : V) = 0 := coordAt_base b 0 i

omit [FiniteDimensional ℝ V] in
theorem coordAt_zero_sub (i : ℕ) (x y : V) :
    coordAt b 0 i (x - y) = coordAt b 0 i x - coordAt b 0 i y := by
  unfold coordAt
  split
  · simp [map_sub]
  · simp

omit [FiniteDimensional ℝ V] in
theorem coordAt_zero_neg (i : ℕ) (x : V) : coordAt b 0 i (-x) = -coordAt b 0 i x := by
  rw [show -x = (0 : V) - x by simp, coordAt_zero_sub, coordAt_zero_zero, zero_sub]

end CoordAlgebra

section Crux

variable {n : ℕ} {b : Basis (Fin n) ℝ V} {m : ℕ}

omit [FiniteDimensional ℝ V] in
/-- If the coordinates of `x` above `j` vanish and those of `u` below `k` vanish, with
`j < k`, then `u x = 0`. -/
theorem apply_eq_zero_of_gap (hmn : m ≤ n) {u : V →L[ℝ] ℝ} {x : V}
    (hx : x ∈ Submodule.span ℝ (Set.range (fun i : Fin m => basisAt b (i : ℕ))))
    {j k : ℕ} (hjk : j < k)
    (hxj : ∀ i, j < i → i < m → coordAt b 0 i x = 0)
    (huk : ∀ i, i < k → u (basisAt b i) = 0) :
    u x = 0 := by
  rw [apply_eq_sum_first b hmn u hx]
  refine Finset.sum_eq_zero fun i hi => ?_
  rcases lt_or_ge j i with h | h
  · rw [hxj i h (Finset.mem_range.1 hi), mul_zero]
  · rw [huk i (lt_of_le_of_lt h hjk), zero_mul]

omit [FiniteDimensional ℝ V] in
/-- If the coordinates of `x` above `j` vanish and those of `u` below `j` vanish, then `u x`
is the product of the two `j`-th coordinates. -/
theorem apply_eq_mul_of_match (hmn : m ≤ n) {u : V →L[ℝ] ℝ} {x : V}
    (hx : x ∈ Submodule.span ℝ (Set.range (fun i : Fin m => basisAt b (i : ℕ))))
    {j : ℕ} (hjm : j < m)
    (hxj : ∀ i, j < i → i < m → coordAt b 0 i x = 0)
    (huj : ∀ i, i < j → u (basisAt b i) = 0) :
    u x = u (basisAt b j) * coordAt b 0 j x := by
  rw [apply_eq_sum_first b hmn u hx]
  refine Finset.sum_eq_single j ?_ ?_
  · intro i hi hij
    rcases lt_or_gt_of_ne hij with h | h
    · rw [huj i h, zero_mul]
    · rw [hxj i h (Finset.mem_range.1 hi), mul_zero]
  · intro hj
    exact absurd (Finset.mem_range.2 hjm) hj

/-- **The crux of the duality.** In an adapted basis, the cone `Q0` of functionals whose first
nonvanishing coordinate among the first `m` is positive has as primal cone, on the span `W` of
the first `m` basis vectors, the set of vectors whose *last* nonvanishing coordinate among the
first `m` is positive. -/
theorem primalCone_eq_lexCone {n : ℕ} (b : Basis (Fin n) ℝ V) (m : ℕ) (hmn : m ≤ n) :
    primalCone (Q0 b m) (Submodule.span ℝ (Set.range (fun i : Fin m => basisAt b (i : ℕ))))
      = {x | x ∈ Submodule.span ℝ (Set.range (fun i : Fin m => basisAt b (i : ℕ))) ∧
             ∃ j < m, 0 < coordAt b 0 j x ∧ ∀ i, j < i → i < m → coordAt b 0 i x = 0} := by
  classical
  ext x
  constructor
  · rintro ⟨hxW, u₀, ⟨k, hkm, hk0, hklt⟩, hu₀x, hmin⟩
    refine ⟨hxW, ?_⟩
    -- the support of `x` among the first `m` coordinates is nonempty
    have hknm : k < n := lt_of_lt_of_le hkm hmn
    set S : Finset ℕ := (Finset.range m).filter (fun i => coordAt b 0 i x ≠ 0) with hS
    have hSne : S.Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      have hall : ∀ i, i < m → coordAt b 0 i x = 0 := by
        intro i hi
        by_contra hne
        have : i ∈ S := by rw [hS]; exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, hne⟩
        rw [hemp] at this
        exact absurd this (Finset.notMem_empty i)
      have : u₀ x = 0 := by
        rw [apply_eq_sum_first b hmn u₀ hxW]
        exact Finset.sum_eq_zero fun i hi => by
          rw [hall i (Finset.mem_range.1 hi), mul_zero]
      rw [this] at hu₀x
      exact lt_irrefl 0 hu₀x
    set j : ℕ := S.max' hSne with hj
    have hjS : j ∈ S := S.max'_mem hSne
    have hjm : j < m := Finset.mem_range.1 (Finset.mem_filter.1 hjS).1
    have hjne : coordAt b 0 j x ≠ 0 := (Finset.mem_filter.1 hjS).2
    have hjmax : ∀ i, j < i → i < m → coordAt b 0 i x = 0 := by
      intro i hji him
      by_contra hne
      have : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_range.2 him, hne⟩
      exact absurd (S.le_max' i this) (not_le.2 hji)
    have hjn : j < n := lt_of_lt_of_le hjm hmn
    -- the leading index of `u₀` is at most `j`
    have hkj : k ≤ j := by
      by_contra hlt
      push_neg at hlt
      have : u₀ x = 0 := apply_eq_zero_of_gap hmn hxW hlt hjmax hklt
      rw [this] at hu₀x
      exact lt_irrefl 0 hu₀x
    refine ⟨j, hjm, ?_, hjmax⟩
    rcases eq_or_lt_of_le hkj with rfl | hklt'
    · -- the leading index of `u₀` is exactly `j`
      have hval : u₀ x = u₀ (basisAt b j) * coordAt b 0 j x :=
        apply_eq_mul_of_match hmn hxW hjm hjmax hklt
      rw [hval] at hu₀x
      by_contra hcon
      push_neg at hcon
      nlinarith
    · -- the leading index of `u₀` is strictly below `j`: test against the `j`-th coordinate
      have hu : coordCLM b ⟨j, hjn⟩ ∈ Q0 b m := by
        refine ⟨j, hjm, ?_, ?_⟩
        · rw [coordCLM_basisAt b hjn]
          simp
        · intro i hij
          rw [coordCLM_basisAt b (lt_trans hij hjn)]
          simp only [ite_eq_right_iff]
          intro h
          exact absurd h (Nat.ne_of_lt hij)
      have hdiff : u₀ - coordCLM b ⟨j, hjn⟩ ∈ Q0 b m := by
        refine ⟨k, hkm, ?_, ?_⟩
        · rw [ContinuousLinearMap.sub_apply, coordCLM_basisAt b hknm]
          have : ¬ (k = j) := Nat.ne_of_lt hklt'
          simp only [this, if_false, sub_zero]
          exact hk0
        · intro i hik
          rw [ContinuousLinearMap.sub_apply, hklt i hik,
            coordCLM_basisAt b (lt_trans hik hknm)]
          have : ¬ (i = j) := Nat.ne_of_lt (lt_trans hik hklt')
          simp [this]
      have hnn := hmin _ hu hdiff
      rw [coordCLM_eq_coordAt b hjn] at hnn
      exact lt_of_le_of_ne hnn (Ne.symm hjne)
  · rintro ⟨hxW, j, hjm, hxj, hjmax⟩
    have hjn : j < n := lt_of_lt_of_le hjm hmn
    refine ⟨hxW, coordCLM b ⟨j, hjn⟩, ⟨j, hjm, ?_, ?_⟩, ?_, ?_⟩
    · rw [coordCLM_basisAt b hjn]; simp
    · intro i hij
      rw [coordCLM_basisAt b (lt_trans hij hjn)]
      simp only [ite_eq_right_iff]
      intro h
      exact absurd h (Nat.ne_of_lt hij)
    · rw [coordCLM_eq_coordAt b hjn]
      exact hxj
    · rintro u ⟨k, hkm, hk0, hklt⟩ hdiff
      rcases lt_trichotomy k j with hkj | rfl | hjk
      · -- impossible: `u₀ - u` would have a negative leading coordinate
        exfalso
        obtain ⟨p, hpm, hp0, hplt⟩ := hdiff
        have hknm : k < n := lt_of_lt_of_le hkm hmn
        have hukneg : (coordCLM b ⟨j, hjn⟩ - u) (basisAt b k) = -u (basisAt b k) := by
          rw [ContinuousLinearMap.sub_apply, coordCLM_basisAt b hknm]
          have : ¬ (k = j) := Nat.ne_of_lt hkj
          simp [this]
        rcases lt_trichotomy p k with hpk | rfl | hkp
        · have : (coordCLM b ⟨j, hjn⟩ - u) (basisAt b p) = 0 := by
            rw [ContinuousLinearMap.sub_apply, hklt p hpk,
              coordCLM_basisAt b (lt_trans hpk hknm)]
            have : ¬ (p = j) := Nat.ne_of_lt (lt_trans hpk hkj)
            simp [this]
          rw [this] at hp0
          exact lt_irrefl 0 hp0
        · rw [hukneg] at hp0
          linarith
        · have := hplt k hkp
          rw [hukneg] at this
          have : u (basisAt b k) = 0 := by linarith
          rw [this] at hk0
          exact lt_irrefl 0 hk0
      · -- the leading index of `u` is `j`: `u x` is a product of two positive numbers
        rw [apply_eq_mul_of_match hmn hxW hjm hjmax hklt]
        exact le_of_lt (mul_pos hk0 hxj)
      · -- the leading index of `u` is above `j`: `u x = 0`
        rw [apply_eq_zero_of_gap hmn hxW hjk hjmax hklt]

end Crux

/-! ## The reverse duality -/

/-- The cone in the dual attached to a cone `P` in `V`, by the same recipe as `primalCone`
with the roles of `V` and its dual exchanged. -/
def dualCone (P : Set V) : Set (V →L[ℝ] ℝ) :=
  {u | ∃ x₀ ∈ P, 0 < u x₀ ∧ ∀ x ∈ P, x₀ - x ∈ P → 0 ≤ u x}

section Reverse

variable {n : ℕ} {b : Basis (Fin n) ℝ V} {m : ℕ}

omit [FiniteDimensional ℝ V] in
theorem coordAt_basisAt {k : ℕ} (hk : k < n) (i : ℕ) :
    coordAt b 0 i (basisAt b k) = if i = k then 1 else 0 := by
  by_cases hi : i < n
  · rw [coordAt_of_lt hi, sub_zero, basisAt_of_lt b hk, Basis.coord_apply, Basis.repr_self,
      Finsupp.single_apply]
    simp [Fin.ext_iff, eq_comm]
  · rw [coordAt_of_le (Nat.not_lt.1 hi)]
    have : i ≠ k := fun h => absurd (h ▸ hk) hi
    simp [this]

omit [FiniteDimensional ℝ V] in
/-- A basis vector of index below `m` lies in the primal cone in coordinates. -/
theorem basisAt_mem_lastPos {k : ℕ} (hkm : k < m) (hmn : m ≤ n) :
    basisAt b k ∈ {x | x ∈ Submodule.span ℝ (Set.range (fun i : Fin m => basisAt b (i : ℕ))) ∧
      ∃ j < m, 0 < coordAt b 0 j x ∧ ∀ i, j < i → i < m → coordAt b 0 i x = 0} := by
  have hkn : k < n := lt_of_lt_of_le hkm hmn
  refine ⟨Submodule.subset_span ⟨⟨k, hkm⟩, rfl⟩, k, hkm, ?_, ?_⟩
  · rw [coordAt_basisAt hkn]
    simp
  · intro i hi _
    rw [coordAt_basisAt hkn]
    simp [Nat.ne_of_gt hi]

omit [FiniteDimensional ℝ V] in
/-- The reverse of the crux: the cone `Q0` is recovered from the primal cone. -/
theorem dualCone_lastPos (b : Basis (Fin n) ℝ V) (m : ℕ) (hmn : m ≤ n) :
    dualCone {x | x ∈ Submodule.span ℝ (Set.range (fun i : Fin m => basisAt b (i : ℕ))) ∧
        ∃ j < m, 0 < coordAt b 0 j x ∧ ∀ i, j < i → i < m → coordAt b 0 i x = 0}
      = Q0 b m := by
  classical
  ext u
  constructor
  · rintro ⟨x₀, ⟨hx₀W, j, hjm, hj, hjmax⟩, hux₀, hmin⟩
    -- the least index at which `u` does not vanish
    set S : Finset ℕ := (Finset.range m).filter (fun i => u (basisAt b i) ≠ 0) with hS
    have hSne : S.Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      have hall : ∀ i, i < m → u (basisAt b i) = 0 := by
        intro i hi
        by_contra hne
        have : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, hne⟩
        rw [hemp] at this
        exact absurd this (Finset.notMem_empty i)
      have : u x₀ = 0 := by
        rw [apply_eq_sum_first b hmn u hx₀W]
        exact Finset.sum_eq_zero fun i hi => by
          rw [hall i (Finset.mem_range.1 hi), zero_mul]
      rw [this] at hux₀
      exact lt_irrefl 0 hux₀
    set k : ℕ := S.min' hSne with hk
    have hkS : k ∈ S := S.min'_mem hSne
    have hkm : k < m := Finset.mem_range.1 (Finset.mem_filter.1 hkS).1
    have hkne : u (basisAt b k) ≠ 0 := (Finset.mem_filter.1 hkS).2
    have hkmin : ∀ i, i < k → u (basisAt b i) = 0 := by
      intro i hik
      by_contra hne
      have him : i < m := lt_trans hik hkm
      exact absurd (S.min'_le i (Finset.mem_filter.2 ⟨Finset.mem_range.2 him, hne⟩))
        (not_le.2 hik)
    have hkn : k < n := lt_of_lt_of_le hkm hmn
    -- the least index of `u` is at most the last index of `x₀`
    have hkj : k ≤ j := by
      by_contra hcon
      push_neg at hcon
      have : u x₀ = 0 := apply_eq_zero_of_gap hmn hx₀W hcon hjmax hkmin
      rw [this] at hux₀
      exact lt_irrefl 0 hux₀
    refine ⟨k, hkm, ?_, hkmin⟩
    rcases eq_or_lt_of_le hkj with rfl | hklt
    · have hval : u x₀ = u (basisAt b k) * coordAt b 0 k x₀ :=
        apply_eq_mul_of_match hmn hx₀W hjm hjmax hkmin
      rw [hval] at hux₀
      by_contra hcon
      push_neg at hcon
      nlinarith
    · -- test the hypothesis against the `k`-th basis vector
      have hbk := basisAt_mem_lastPos hkm hmn (b := b)
      have hdiff : x₀ - basisAt b k ∈
          {x | x ∈ Submodule.span ℝ (Set.range (fun i : Fin m => basisAt b (i : ℕ))) ∧
            ∃ j < m, 0 < coordAt b 0 j x ∧ ∀ i, j < i → i < m → coordAt b 0 i x = 0} := by
        refine ⟨Submodule.sub_mem _ hx₀W hbk.1, j, hjm, ?_, ?_⟩
        · rw [coordAt_zero_sub, coordAt_basisAt hkn]
          have : ¬ (j = k) := Nat.ne_of_gt hklt
          simp only [this, if_false, sub_zero]
          exact hj
        · intro i hi him
          rw [coordAt_zero_sub, coordAt_basisAt hkn, hjmax i hi him]
          have : ¬ (i = k) := Nat.ne_of_gt (lt_trans hklt hi)
          simp [this]
      have := hmin _ hbk hdiff
      exact lt_of_le_of_ne this (Ne.symm hkne)
  · rintro ⟨k, hkm, hk0, hklt⟩
    have hkn : k < n := lt_of_lt_of_le hkm hmn
    refine ⟨basisAt b k, basisAt_mem_lastPos hkm hmn, hk0, ?_⟩
    rintro x ⟨hxW, j, hjm, hj, hjmax⟩ ⟨-, p, hpm, hp, hpmax⟩
    rcases lt_trichotomy k j with hkj | rfl | hjk
    · -- impossible: `basisAt b k - x` would have a negative last coordinate
      exfalso
      have hcoord : coordAt b 0 j (basisAt b k - x) = -coordAt b 0 j x := by
        rw [coordAt_zero_sub, coordAt_basisAt hkn]
        have : ¬ (j = k) := Nat.ne_of_gt hkj
        simp [this]
      have habove : ∀ i, j < i → i < m → coordAt b 0 i (basisAt b k - x) = 0 := by
        intro i hi him
        rw [coordAt_zero_sub, coordAt_basisAt hkn, hjmax i hi him]
        have : ¬ (i = k) := Nat.ne_of_gt (lt_trans hkj hi)
        simp [this]
      rcases lt_trichotomy p j with h | h | h
      · rw [hpmax j h hjm] at hcoord
        have : coordAt b 0 j x = 0 := by linarith
        rw [this] at hj
        exact lt_irrefl 0 hj
      · subst h
        rw [hcoord] at hp
        linarith
      · rw [habove p h hpm] at hp
        exact lt_irrefl 0 hp
    · rw [apply_eq_mul_of_match hmn hxW hjm hjmax hklt]
      exact le_of_lt (mul_pos hk0 hj)
    · rw [apply_eq_zero_of_gap hmn hxW hjk hjmax hklt]

end Reverse

/-! ## The primal cone in coordinates is a vector space order -/

section Coordinates

variable {n : ℕ} {b : Basis (Fin n) ℝ V} {m : ℕ}

omit [FiniteDimensional ℝ V] in
/-- Membership in the span of the first `m` basis vectors, in coordinates. -/
theorem mem_span_iff_coordAt (x : V) :
    x ∈ Submodule.span ℝ (Set.range (fun i : Fin m => basisAt b (i : ℕ))) ↔
      ∀ i, m ≤ i → coordAt b 0 i x = 0 := by
  rw [mem_span_basisAt_iff]
  constructor
  · intro h i hi
    by_cases hin : i < n
    · rw [coordAt_of_lt hin, sub_zero]
      exact h ⟨i, hin⟩ hi
    · exact coordAt_of_le (Nat.not_lt.1 hin) x
  · intro h j hj
    have := h (j : ℕ) hj
    rwa [coordAt_of_lt j.2, sub_zero] at this

omit [FiniteDimensional ℝ V] in
/-- A vector of the span of the first `m` basis vectors whose first `m` coordinates vanish is
zero. -/
theorem eq_zero_of_coordAt_eq_zero {x : V}
    (hx : x ∈ Submodule.span ℝ (Set.range (fun i : Fin m => basisAt b (i : ℕ))))
    (h : ∀ i, i < m → coordAt b 0 i x = 0) : x = 0 := by
  refine (coordAt_eq_zero_iff (b := b) (a := 0) x).1 fun i => ?_
  rcases lt_or_ge i m with hi | hi
  · exact h i hi
  · exact (mem_span_iff_coordAt x).1 hx i hi

omit [FiniteDimensional ℝ V] in
/-- The primal cone in coordinates — the vectors whose last nonvanishing coordinate among the
first `m` is positive — is a vector space order on the span of the first `m` basis
vectors. -/
theorem isLexConeOn_lastPos :
    IsLexConeOn (Submodule.span ℝ (Set.range (fun i : Fin m => basisAt b (i : ℕ))))
      {x | x ∈ Submodule.span ℝ (Set.range (fun i : Fin m => basisAt b (i : ℕ))) ∧
             ∃ j < m, 0 < coordAt b 0 j x ∧ ∀ i, j < i → i < m → coordAt b 0 i x = 0} where
  mem_of_mem := fun _ hx => hx.1
  add_mem := by
    rintro x y ⟨hxW, jx, hjxm, hjx, hjxmax⟩ ⟨hyW, jy, hjym, hjy, hjymax⟩
    refine ⟨Submodule.add_mem _ hxW hyW, max jx jy, max_lt hjxm hjym, ?_, ?_⟩
    · rw [coordAt_zero_add]
      rcases lt_trichotomy jx jy with h | h | h
      · rw [max_eq_right h.le, hjxmax jy h hjym, zero_add]
        exact hjy
      · subst h
        rw [max_self]
        exact add_pos hjx hjy
      · rw [max_eq_left h.le, hjymax jx h hjxm, add_zero]
        exact hjx
    · intro i hi him
      rw [coordAt_zero_add, hjxmax i (lt_of_le_of_lt (le_max_left _ _) hi) him,
        hjymax i (lt_of_le_of_lt (le_max_right _ _) hi) him, add_zero]
  smul_mem := by
    rintro c hc x ⟨hxW, j, hjm, hj, hjmax⟩
    refine ⟨Submodule.smul_mem _ c hxW, j, hjm, ?_, ?_⟩
    · rw [coordAt_zero_smul]
      exact mul_pos hc hj
    · intro i hi him
      rw [coordAt_zero_smul, hjmax i hi him, mul_zero]
  trichotomy := by
    intro x hxW
    classical
    by_cases hzero : ∀ i, i < m → coordAt b 0 i x = 0
    · exact Or.inr (Or.inl (eq_zero_of_coordAt_eq_zero hxW hzero))
    push_neg at hzero
    obtain ⟨i₀, hi₀m, hi₀⟩ := hzero
    set S : Finset ℕ := (Finset.range m).filter (fun i => coordAt b 0 i x ≠ 0) with hS
    have hSne : S.Nonempty := ⟨i₀, Finset.mem_filter.2 ⟨Finset.mem_range.2 hi₀m, hi₀⟩⟩
    set j : ℕ := S.max' hSne with hj
    have hjS : j ∈ S := S.max'_mem hSne
    have hjm : j < m := Finset.mem_range.1 (Finset.mem_filter.1 hjS).1
    have hjne : coordAt b 0 j x ≠ 0 := (Finset.mem_filter.1 hjS).2
    have hjmax : ∀ i, j < i → i < m → coordAt b 0 i x = 0 := by
      intro i hji him
      by_contra hne
      exact absurd (S.le_max' i (Finset.mem_filter.2 ⟨Finset.mem_range.2 him, hne⟩))
        (not_le.2 hji)
    rcases lt_or_gt_of_ne hjne with hneg | hpos
    · refine Or.inr (Or.inr ⟨Submodule.neg_mem _ hxW, j, hjm, ?_, ?_⟩)
      · rw [coordAt_zero_neg]
        linarith
      · intro i hi him
        rw [coordAt_zero_neg, hjmax i hi him, neg_zero]
    · exact Or.inl ⟨hxW, j, hjm, hpos, hjmax⟩
  zero_notMem := by
    rintro ⟨-, j, -, hj, -⟩
    rw [coordAt_zero_zero] at hj
    exact lt_irrefl 0 hj
  neg_notMem := by
    rintro x ⟨-, j, hjm, hj, hjmax⟩ ⟨-, j', hj'm, hj', hj'max⟩
    have hneg : ∀ i, coordAt b 0 i (-x) = -coordAt b 0 i x := fun i => coordAt_zero_neg i x
    rw [hneg] at hj'
    rcases lt_trichotomy j j' with h | h | h
    · rw [hjmax j' h hj'm] at hj'
      simp at hj'
    · subst h
      linarith
    · have := hj'max j h hjm
      rw [hneg] at this
      have : coordAt b 0 j x = 0 := by linarith
      rw [this] at hj
      exact lt_irrefl 0 hj

omit [FiniteDimensional ℝ V] in
/-- The span of the first `d` basis vectors is order convex for the primal cone. No relation
between `d` and `m` is needed. -/
theorem isOrderConvex_lastPos {d : ℕ} :
    IsOrderConvex
      {x | x ∈ Submodule.span ℝ (Set.range (fun i : Fin m => basisAt b (i : ℕ))) ∧
             ∃ j < m, 0 < coordAt b 0 j x ∧ ∀ i, j < i → i < m → coordAt b 0 i x = 0}
      (Submodule.span ℝ (Set.range (fun i : Fin d => basisAt b (i : ℕ)))) := by
  rintro w v ⟨hwW, j, hjm, hj, hjmax⟩ ⟨hvwW, j', hj'm, hj', hj'max⟩ hv
  have hvco : ∀ i, d ≤ i → coordAt b 0 i v = 0 := (mem_span_iff_coordAt v).1 hv
  -- the leading index of `w` is below `d`
  have hjd : j < d := by
    by_contra hcon
    push_neg at hcon
    -- otherwise the last nonvanishing coordinate of `v - w` is negative
    have hcoord : coordAt b 0 j (v - w) = -coordAt b 0 j w := by
      rw [coordAt_zero_sub, hvco j hcon, zero_sub]
    have habove : ∀ i, j < i → i < m → coordAt b 0 i (v - w) = 0 := by
      intro i hi him
      rw [coordAt_zero_sub, hvco i (le_trans hcon hi.le), hjmax i hi him, sub_zero]
    rcases lt_trichotomy j' j with h | h | h
    · rw [hj'max j h hjm] at hcoord
      have : coordAt b 0 j w = 0 := by linarith
      rw [this] at hj
      exact lt_irrefl 0 hj
    · subst h
      rw [hcoord] at hj'
      linarith
    · rw [habove j' h hj'm] at hj'
      exact lt_irrefl 0 hj'
  refine (mem_span_iff_coordAt w).2 fun i hi => ?_
  rcases lt_or_ge i m with him | him
  · exact hjmax i (lt_of_lt_of_le hjd hi) him
  · exact (mem_span_iff_coordAt w).1 hwW i him

end Coordinates

/-! ## Transport to the invariants of an admissible pair -/

section Transport

/-- The exceptional set of a cone `Q` in the dual: the functionals `u` with neither `u` nor
`-u` in `Q`. For an admissible pair this is the submodule `M` of Theorem 6.1. -/
def excSet (Q : Set (V →L[ℝ] ℝ)) : Set (V →L[ℝ] ℝ) := {u | u ∉ Q ∧ -u ∉ Q}

/-- The subspace `W = M^⊥` of the primal form of the classification, defined directly from
`Q`. -/
def primalSpace (Q : Set (V →L[ℝ] ℝ)) : Submodule ℝ V where
  carrier := {v | ∀ u ∈ excSet Q, u v = 0}
  add_mem' := by
    intro x y hx hy u hu
    rw [map_add, hx u hu, hy u hu, add_zero]
  zero_mem' := by
    intro u _
    rw [map_zero]
  smul_mem' := by
    intro c x hx u hu
    rw [map_smul, hx u hu, smul_zero]

omit [FiniteDimensional ℝ V] in
theorem mem_primalSpace_iff {Q : Set (V →L[ℝ] ℝ)} {v : V} :
    v ∈ primalSpace Q ↔ ∀ u ∈ excSet Q, u v = 0 := Iff.rfl

omit [FiniteDimensional ℝ V] in
/-- If `M` is the exceptional submodule of `Q`, the primal subspace is its
pre-annihilator. -/
theorem primalSpace_eq_preAnnih {Q : Set (V →L[ℝ] ℝ)} {M : Submodule ℝ (V →L[ℝ] ℝ)}
    (hM : ∀ u, u ∈ (M : Set (V →L[ℝ] ℝ)) ↔ (u ∉ Q ∧ -u ∉ Q)) :
    primalSpace Q = Adapted.preAnnih M := by
  ext v
  rw [mem_primalSpace_iff, Adapted.mem_preAnnih_iff]
  exact ⟨fun h u hu => h u ((hM u).1 hu), fun h u hu => h u ((hM u).2 hu)⟩

omit [FiniteDimensional ℝ V] in
theorem annih_bot : annih (⊥ : Submodule ℝ V) = ⊤ := by
  ext u
  simp only [mem_annih_iff, Submodule.mem_top, iff_true]
  intro v hv
  rw [(Submodule.mem_bot ℝ).1 hv, map_zero]

/-- In the degenerate case the primal subspace is trivial. -/
theorem primalSpace_eq_bot_of_eq_empty {Q : Set (V →L[ℝ] ℝ)} (hQ : Q = ∅) :
    primalSpace Q = ⊥ := by
  have htop : primalSpace Q = Adapted.preAnnih (⊤ : Submodule ℝ (V →L[ℝ] ℝ)) := by
    ext v
    rw [mem_primalSpace_iff, Adapted.mem_preAnnih_iff]
    constructor
    · intro h u _
      exact h u (by simp [excSet, hQ])
    · intro h u _
      exact h u trivial
  rw [htop, ← annih_bot, preAnnih_annih]

omit [FiniteDimensional ℝ V] in
/-- In the degenerate case the primal cone is empty. -/
theorem primalCone_eq_empty_of_eq_empty {Q : Set (V →L[ℝ] ℝ)} (hQ : Q = ∅)
    (W : Submodule ℝ V) : primalCone Q W = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, u₀, hu₀, -⟩
  rw [hQ] at hu₀
  exact hu₀

omit [FiniteDimensional ℝ V] in
/-- The normal form `M0` of the exceptional submodule is the annihilator of the span of the
first `m` basis vectors. -/
theorem M0_eq_annih {n : ℕ} (b : Basis (Fin n) ℝ V) (m : ℕ) :
    M0 b m
      = (annih (Submodule.span ℝ (Set.range (fun i : Fin m => basisAt b (i : ℕ)))) :
          Set (V →L[ℝ] ℝ)) := by
  ext u
  constructor
  · intro hu
    rw [SetLike.mem_coe, mem_annih_iff]
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact hu (i : ℕ) i.2
    | zero => rw [map_zero]
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, hx, smul_zero]
  · intro hu i him
    exact hu _ (Submodule.subset_span ⟨⟨i, him⟩, rfl⟩)

variable {A : AffineSubspace ℝ V} {Q : Set (V →L[ℝ] ℝ)}

/-- The adapted basis of Theorem 6.1, with the primal subspace read off. -/
theorem exists_adapted_primal (h : IsAdmissible A Q) (hbot : A.direction ≠ ⊥) :
    ∃ (b : Basis (Fin (finrank ℝ V)) ℝ V) (d m : ℕ),
      1 ≤ d ∧ d ≤ m ∧ m ≤ finrank ℝ V ∧
      Q = Q0 b m ∧
      primalSpace Q
        = Submodule.span ℝ (Set.range (fun i : Fin m => basisAt b (i : ℕ))) ∧
      A.direction = Submodule.span ℝ (Set.range (fun i : Fin d => basisAt b (i : ℕ))) := by
  obtain ⟨M, hMQ, hlex, hMN⟩ := h.exceptional
  have hpre : Adapted.preAnnih (annih A.direction) ≠ ⊥ := by
    rw [preAnnih_annih]
    exact hbot
  obtain ⟨b, d, m, hd, hdm, hmn, hQ0, hM0, hdir⟩ :=
    Adapted.exists_adapted_basis hlex hMN h.orderConvex hpre
  rw [preAnnih_annih] at hdir
  refine ⟨b, d, m, hd, hdm, hmn, by rw [hQ0]; exact (Adapted.Q0_eq b m).symm, ?_, hdir⟩
  have hMeq : M = annih (Submodule.span ℝ (Set.range (fun i : Fin m => basisAt b (i : ℕ)))) := by
    refine SetLike.coe_injective ?_
    rw [hM0]
    exact (Adapted.M0_eq b m).trans (M0_eq_annih b m)
  rw [primalSpace_eq_preAnnih hMQ, hMeq, preAnnih_annih]

/-- The primal cone of an admissible pair is a vector space order on the primal subspace:
clause (3) of Theorem 1.2. -/
theorem isLexConeOn_primalCone (h : IsAdmissible A Q) :
    IsLexConeOn (primalSpace Q) (primalCone Q (primalSpace Q)) := by
  by_cases hbot : A.direction = ⊥
  · have hQ : Q = ∅ := h.degenerate hbot
    rw [primalSpace_eq_bot_of_eq_empty hQ, primalCone_eq_empty_of_eq_empty hQ]
    exact
      { mem_of_mem := fun _ hx => absurd hx (Set.notMem_empty _)
        add_mem := fun _ _ hx _ => absurd hx (Set.notMem_empty _)
        smul_mem := fun _ _ _ hx => absurd hx (Set.notMem_empty _)
        trichotomy := fun x hx => Or.inr (Or.inl ((Submodule.mem_bot ℝ).1 hx))
        zero_notMem := Set.notMem_empty _
        neg_notMem := fun _ hx => absurd hx (Set.notMem_empty _) }
  · obtain ⟨b, d, m, -, -, hmn, hQ0, hW, -⟩ := exists_adapted_primal h hbot
    rw [hW, hQ0, primalCone_eq_lexCone b m hmn]
    exact isLexConeOn_lastPos

/-- The direction of `A` is order convex for the primal cone: clause (3) of Theorem 1.2. -/
theorem isOrderConvex_primalCone (h : IsAdmissible A Q) :
    IsOrderConvex (primalCone Q (primalSpace Q)) A.direction := by
  by_cases hbot : A.direction = ⊥
  · have hQ : Q = ∅ := h.degenerate hbot
    rw [primalCone_eq_empty_of_eq_empty hQ]
    intro w v hw _ _
    exact absurd hw (Set.notMem_empty _)
  · obtain ⟨b, d, m, -, -, hmn, hQ0, hW, hdir⟩ := exists_adapted_primal h hbot
    rw [hW, hQ0, primalCone_eq_lexCone b m hmn, hdir]
    exact isOrderConvex_lastPos

/-- The direction of `A` is contained in the primal subspace: clause (2) of Theorem 1.2. -/
theorem direction_le_primalSpace (h : IsAdmissible A Q) : A.direction ≤ primalSpace Q := by
  by_cases hbot : A.direction = ⊥
  · rw [hbot]
    exact bot_le
  · obtain ⟨b, d, m, -, hdm, -, -, hW, hdir⟩ := exists_adapted_primal h hbot
    rw [hW, hdir]
    refine Submodule.span_mono ?_
    rintro x ⟨i, rfl⟩
    exact ⟨⟨(i : ℕ), lt_of_lt_of_le i.2 hdm⟩, rfl⟩

/-- The degeneracy constraint of Theorem 1.2: the primal subspace is trivial when the flat is
a point. -/
theorem primalSpace_eq_bot (h : IsAdmissible A Q) (hbot : A.direction = ⊥) :
    primalSpace Q = ⊥ :=
  primalSpace_eq_bot_of_eq_empty (h.degenerate hbot)

/-- The transport to primal data is reversible: the cone `Q` is recovered from its primal
cone. -/
theorem dualCone_primalCone (h : IsAdmissible A Q) :
    dualCone (primalCone Q (primalSpace Q)) = Q := by
  by_cases hbot : A.direction = ⊥
  · have hQ : Q = ∅ := h.degenerate hbot
    rw [primalCone_eq_empty_of_eq_empty hQ, hQ]
    ext u
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨x₀, hx₀, -⟩
    exact hx₀
  · obtain ⟨b, d, m, -, -, hmn, hQ0, hW, -⟩ := exists_adapted_primal h hbot
    rw [hW, hQ0, primalCone_eq_lexCone b m hmn, dualCone_lastPos b m hmn]

/-- The primal data of Theorem 1.2: a nonempty flat `A`, a subspace `W` containing its
direction, and a vector space order on `W` — presented by its positive cone `P` — in which
`dir A` is order convex, subject to `W = 0` when `A` is a point. -/
structure IsAdmissiblePrimal (A : AffineSubspace ℝ V) (W : Submodule ℝ V) (P : Set V) :
    Prop where
  A_nonempty : (A : Set V).Nonempty
  direction_le : A.direction ≤ W
  isLexCone : IsLexConeOn W P
  orderConvex : IsOrderConvex P A.direction
  degenerate : A.direction = ⊥ → W = ⊥

/-- The primal data attached to an admissible pair satisfies the clauses of Theorem 1.2. -/
theorem isAdmissiblePrimal_of_isAdmissible (h : IsAdmissible A Q) :
    IsAdmissiblePrimal A (primalSpace Q) (primalCone Q (primalSpace Q)) where
  A_nonempty := h.A_nonempty
  direction_le := direction_le_primalSpace h
  isLexCone := isLexConeOn_primalCone h
  orderConvex := isOrderConvex_primalCone h
  degenerate := primalSpace_eq_bot h

/-- A maximal convex filter is determined by its primal data: the flat together with the
primal cone (the equality of the primal subspaces is not needed, the cone already carrying
that information). -/
theorem eq_of_primal_data {F F' : ConvexFilter V} (hF : IsMaximal F) (hF' : IsMaximal F')
    (hA : Aset F = Aset F')
    (hP : primalCone (Qset F) (primalSpace (Qset F))
        = primalCone (Qset F') (primalSpace (Qset F'))) : F = F' := by
  have hQ : Qset F = Qset F' := by
    rw [← dualCone_primalCone (isAdmissible_invariants hF),
      ← dualCone_primalCone (isAdmissible_invariants hF'), hP]
  exact eq_of_Aset_Qset hF hF' hA hQ

/-- **Theorem 1.2, the primal form of the classification**, in existence-and-uniqueness shape:
an admissible pair `(A, Q)` determines the primal triple `(A, W, P)`, which satisfies the
clauses of Theorem 1.2; the transport is reversible, `Q` being recovered from `P` as
`dualCone P`; and there is exactly one maximal convex filter with these invariants. -/
theorem classification_primal :
    ∀ (A : AffineSubspace ℝ V) (Q : Set (V →L[ℝ] ℝ)), IsAdmissible A Q →
      IsAdmissiblePrimal A (primalSpace Q) (primalCone Q (primalSpace Q)) ∧
        dualCone (primalCone Q (primalSpace Q)) = Q ∧
        ∃! F : {G : ConvexFilter V // IsMaximal G},
          Aset (F : ConvexFilter V) = (A : Set V) ∧ Qset (F : ConvexFilter V) = Q :=
  fun A Q h => ⟨isAdmissiblePrimal_of_isAdmissible h, dualCone_primalCone h, classification A Q h⟩

end Transport

end ConvexFilter
