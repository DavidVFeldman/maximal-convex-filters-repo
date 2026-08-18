import ConvexFilters.Extension
import ConvexFilters.Uniqueness

/-!
# Two distinct maximal convex filters with the same `sig` and the same `Qset`

This file refutes the statement of §5 of the work order in its literal form: it exhibits
two maximal convex filters `F ≠ F'` on `ℝ × ℝ` with `sig F = sig F'` (as functions on the
dual) and `Qset F = Qset F'`.

The point is that the support number `sig F u = sInf (lev F u)` of `Defs.lean` is
real-valued, and returns the junk value `0` both when `lev F u = ∅` (support value `+∞`)
and when `lev F u = Set.univ` (support value `-∞`), which is also the genuine value when
the support number is finite and equal to `0`. The paper's `σ` is extended-real-valued and
therefore also records the set `Nset F` on which it is finite; adding `Nset F = Nset F'`
as a hypothesis restores the theorem, which is how `carrier_eq_of_sig_Qset` is stated in
`ConvexFilters/Uniqueness.lean`, and that hypothesis is automatic for the invariants in
the paper's form (`carrier_eq_of_Aset_Qset`).

The two filters are maximal extensions of

* the *hyperbola germ* `hyp n = {p | 0 ≤ p.1, 0 ≤ p.2, 1 ≤ p.1 * p.2, p.1 * (n+1) ≤ 1}`,
  which approaches the line `p.1 = 0` without reaching it, and
* the *parabola tail* `par n = {p | n ≤ p.1, p.1 ^ 2 ≤ p.2}`, which escapes to infinity.

For a functional `u` with `a = u (1,0)`, `b = u (0,1)` the level sets are

| | `b > 0` | `b < 0` | `b = 0 < a` | `b = 0`, `a < 0` | `u = 0` |
|---|---|---|---|---|---|
| hyperbola | `∅` | `univ` | `Ioi 0` | `Ici 0` | `Ici 0` |
| parabola | `∅` | `univ` | `∅` | `univ` | `Ici 0` |

Each of `sInf ∅`, `sInf univ`, `sInf (Ioi 0)`, `sInf (Ici 0)` is `0`, so both filters have
`sig ≡ 0`; and `∅` and `Ioi 0` are the open proper level sets while `univ` and `Ici 0` are
not, so both filters have the same `Qset`. But the hyperbola germ belongs to the first
filter and is disjoint from a parabola tail, so it does not belong to the second.
-/

namespace ConvexFilter

namespace SigCounterexample

/-! ### The two families of closed convex sets -/

/-- The hyperbola germ: points of the first quadrant above the hyperbola `p.1 * p.2 = 1`
with `p.1 ≤ 1 / (n + 1)`. -/
def hyp (n : ℕ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ 1 ≤ p.1 * p.2 ∧ p.1 * ((n : ℝ) + 1) ≤ 1}

/-- The parabola tail: points above the parabola `p.2 = p.1 ^ 2` with `p.1 ≥ n`. -/
def par (n : ℕ) : Set (ℝ × ℝ) := {p : ℝ × ℝ | (n : ℝ) ≤ p.1 ∧ p.1 ^ 2 ≤ p.2}

theorem hyp_pos {n : ℕ} {p : ℝ × ℝ} (hp : p ∈ hyp n) : 0 < p.1 := by
  obtain ⟨h1, h2, h3, -⟩ := hp
  rcases h1.lt_or_eq with h | h
  · exact h
  · exfalso; rw [← h] at h3; simp at h3; linarith

theorem hyp_fst_le_one {n : ℕ} {p : ℝ × ℝ} (hp : p ∈ hyp n) : p.1 ≤ 1 := by
  obtain ⟨h1, -, -, h4⟩ := hp
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem hyp_snd_ge {n : ℕ} {p : ℝ × ℝ} (hp : p ∈ hyp n) : (n : ℝ) + 1 ≤ p.2 := by
  have hpos := hyp_pos hp
  obtain ⟨-, -, h3, h4⟩ := hp
  nlinarith

theorem hyp_nonempty (n : ℕ) : (hyp n).Nonempty := by
  refine ⟨(1 / ((n : ℝ) + 1), (n : ℝ) + 1), ?_, ?_, ?_, ?_⟩
  · positivity
  · positivity
  · rw [one_div, inv_mul_cancel₀ (by positivity)]
  · rw [one_div, inv_mul_cancel₀ (by positivity)]

theorem par_nonempty (n : ℕ) : (par n).Nonempty := ⟨((n : ℝ), (n : ℝ) ^ 2), le_rfl, le_rfl⟩

theorem hyp_isClosed (n : ℕ) : IsClosed (hyp n) := by
  have h1 : IsClosed {p : ℝ × ℝ | 0 ≤ p.1} := isClosed_le continuous_const continuous_fst
  have h2 : IsClosed {p : ℝ × ℝ | 0 ≤ p.2} := isClosed_le continuous_const continuous_snd
  have h3 : IsClosed {p : ℝ × ℝ | 1 ≤ p.1 * p.2} :=
    isClosed_le continuous_const (continuous_fst.mul continuous_snd)
  have h4 : IsClosed {p : ℝ × ℝ | p.1 * ((n : ℝ) + 1) ≤ 1} :=
    isClosed_le (continuous_fst.mul continuous_const) continuous_const
  have : hyp n = ({p : ℝ × ℝ | 0 ≤ p.1} ∩ {p : ℝ × ℝ | 0 ≤ p.2}) ∩
      ({p : ℝ × ℝ | 1 ≤ p.1 * p.2} ∩ {p : ℝ × ℝ | p.1 * ((n : ℝ) + 1) ≤ 1}) := by
    ext p
    simp [hyp, and_assoc]
  rw [this]
  exact (h1.inter h2).inter (h3.inter h4)

theorem par_isClosed (n : ℕ) : IsClosed (par n) := by
  have h1 : IsClosed {p : ℝ × ℝ | (n : ℝ) ≤ p.1} := isClosed_le continuous_const continuous_fst
  have h2 : IsClosed {p : ℝ × ℝ | p.1 ^ 2 ≤ p.2} :=
    isClosed_le (continuous_fst.pow 2) continuous_snd
  have : par n = {p : ℝ × ℝ | (n : ℝ) ≤ p.1} ∩ {p : ℝ × ℝ | p.1 ^ 2 ≤ p.2} := rfl
  rw [this]
  exact h1.inter h2

theorem hyp_convex (n : ℕ) : Convex ℝ (hyp n) := by
  rintro x ⟨hx1, hx2, hx3, hx4⟩ y ⟨hy1, hy2, hy3, hy4⟩ a b ha hb hab
  have hsum : 2 ≤ x.1 * y.2 + x.2 * y.1 := by
    have hprod : 1 ≤ (x.1 * y.2) * (x.2 * y.1) := by nlinarith
    have hn1 : 0 ≤ x.1 * y.2 := mul_nonneg hx1 hy2
    have hn2 : 0 ≤ x.2 * y.1 := mul_nonneg hx2 hy1
    nlinarith [sq_nonneg (x.1 * y.2 - x.2 * y.1)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using by positivity
  · simpa using by positivity
  · have : (a • x + b • y).1 * (a • x + b • y).2
        = a * a * (x.1 * x.2) + a * b * (x.1 * y.2 + x.2 * y.1) + b * b * (y.1 * y.2) := by
      simp [Prod.fst_add, Prod.snd_add]
      ring
    rw [this]
    nlinarith [mul_nonneg ha hb, sq_nonneg (a + b)]
  · have : (a • x + b • y).1 * ((n : ℝ) + 1) = a * (x.1 * ((n : ℝ) + 1)) + b * (y.1 * ((n : ℝ) + 1)) := by
      simp [Prod.fst_add]
      ring
    rw [this]
    nlinarith

theorem par_convex (n : ℕ) : Convex ℝ (par n) := by
  rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ a b ha hb hab
  constructor
  · have : (a • x + b • y).1 = a * x.1 + b * y.1 := by simp
    rw [this]
    nlinarith
  · have h1 : (a • x + b • y).1 = a * x.1 + b * y.1 := by simp
    have h2 : (a • x + b • y).2 = a * x.2 + b * y.2 := by simp
    rw [h1, h2]
    nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x.1 - y.1)),
      mul_le_mul_of_nonneg_left hx2 ha, mul_le_mul_of_nonneg_left hy2 hb]

theorem hyp_antitone : Antitone hyp := by
  intro m n hmn p hp
  obtain ⟨h1, h2, h3, h4⟩ := hp
  refine ⟨h1, h2, h3, ?_⟩
  have hcast : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hmn
  nlinarith

theorem par_antitone : Antitone par := by
  intro m n hmn p hp
  obtain ⟨h1, h2⟩ := hp
  exact ⟨le_trans (Nat.cast_le.mpr hmn) h1, h2⟩

/-! ### The two maximal filters -/

/-- The convex filter generated by the hyperbola germs. -/
noncomputable def hypBase : ConvexFilter (ℝ × ℝ) :=
  ofAntitoneBase hyp hyp_nonempty hyp_antitone

/-- The convex filter generated by the parabola tails. -/
noncomputable def parBase : ConvexFilter (ℝ × ℝ) :=
  ofAntitoneBase par par_nonempty par_antitone

/-- A maximal convex filter containing all hyperbola germs. -/
noncomputable def Ghyp : ConvexFilter (ℝ × ℝ) :=
  (exists_isMaximal_extension hypBase).choose

/-- A maximal convex filter containing all parabola tails. -/
noncomputable def Gpar : ConvexFilter (ℝ × ℝ) :=
  (exists_isMaximal_extension parBase).choose

theorem Ghyp_isMaximal : IsMaximal Ghyp := (exists_isMaximal_extension hypBase).choose_spec.2

theorem Gpar_isMaximal : IsMaximal Gpar := (exists_isMaximal_extension parBase).choose_spec.2

theorem hyp_mem_Ghyp (n : ℕ) : hyp n ∈ Ghyp.carrier :=
  (exists_isMaximal_extension hypBase).choose_spec.1
    (base_mem_ofAntitoneBase (hyp_isClosed n) (hyp_convex n))

theorem par_mem_Gpar (n : ℕ) : par n ∈ Gpar.carrier :=
  (exists_isMaximal_extension parBase).choose_spec.1
    (base_mem_ofAntitoneBase (par_isClosed n) (par_convex n))

/-! ### Membership criteria -/

theorem mem_carrier_of_base_subset {G : ConvexFilter (ℝ × ℝ)} {B : ℕ → Set (ℝ × ℝ)}
    (hB : ∀ n, B n ∈ G.carrier) {C : Set (ℝ × ℝ)} (hcl : IsClosed C) (hcv : Convex ℝ C)
    {n : ℕ} (h : B n ⊆ C) : C ∈ G.carrier :=
  G.mem_of_superset (hB n) hcl hcv h

theorem notMem_carrier_of_base_disjoint {G : ConvexFilter (ℝ × ℝ)} {B : ℕ → Set (ℝ × ℝ)}
    (hB : ∀ n, B n ∈ G.carrier) {C : Set (ℝ × ℝ)} {n : ℕ} (h : B n ∩ C = ∅) :
    C ∉ G.carrier := by
  intro hC
  have := G.inter_mem (hB n) hC
  rw [h] at this
  exact G.empty_not_mem this

/-! ### Coordinates of a functional -/

theorem apply_eq (u : (ℝ × ℝ) →L[ℝ] ℝ) (p : ℝ × ℝ) :
    u p = u (1, 0) * p.1 + u (0, 1) * p.2 := by
  have hp : p = p.1 • ((1 : ℝ), (0 : ℝ)) + p.2 • ((0 : ℝ), (1 : ℝ)) := by
    simp
  rw [hp, map_add, map_smul, map_smul]
  simp [mul_comm]

theorem eq_zero_of_coords {u : (ℝ × ℝ) →L[ℝ] ℝ} (ha : u (1, 0) = 0) (hb : u (0, 1) = 0) :
    u = 0 := by
  refine ContinuousLinearMap.ext fun p => ?_
  rw [apply_eq u p, ha, hb]
  simp

/-! ### Level sets of the hyperbola filter -/

section Hyp

variable {u : (ℝ × ℝ) →L[ℝ] ℝ}

/-- If `u (0,1) > 0` then `u` is unbounded above on the hyperbola germs. -/
theorem hyp_disjoint_of_snd_pos (hb : 0 < u (0, 1)) (t : ℝ) :
    ∃ n : ℕ, hyp n ∩ halfLE u t = ∅ := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((t + |u (1, 0)|) / u (0, 1))
  have hn' : t + |u (1, 0)| < u (0, 1) * (n : ℝ) := by
    rw [div_lt_iff₀ hb] at hn
    linarith [hn]
  refine ⟨n, ?_⟩
  rw [Set.eq_empty_iff_forall_notMem]
  rintro p ⟨hp, hple⟩
  have hp1 : 0 < p.1 := hyp_pos hp
  have hp1' : p.1 ≤ 1 := hyp_fst_le_one hp
  have hp2 : (n : ℝ) + 1 ≤ p.2 := hyp_snd_ge hp
  have hle : u p ≤ t := hple
  rw [apply_eq u p] at hle
  have habs : -|u (1, 0)| ≤ u (1, 0) := neg_abs_le _
  have h1 : -|u (1, 0)| ≤ u (1, 0) * p.1 := by
    nlinarith [abs_nonneg (u (1, 0))]
  have h2 : u (0, 1) * ((n : ℝ) + 1) ≤ u (0, 1) * p.2 := by nlinarith
  nlinarith

/-- If `u (0,1) < 0` then `u` is bounded above by any `t` on a small hyperbola germ. -/
theorem hyp_subset_of_snd_neg (hb : u (0, 1) < 0) (t : ℝ) :
    ∃ n : ℕ, hyp n ⊆ halfLE u t := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((|u (1, 0)| - t) / (-u (0, 1)))
  have hn' : |u (1, 0)| - t < -u (0, 1) * (n : ℝ) := by
    rw [div_lt_iff₀ (by linarith)] at hn
    linarith [hn]
  refine ⟨n, fun p hp => ?_⟩
  have hp1 : 0 < p.1 := hyp_pos hp
  have hp1' : p.1 ≤ 1 := hyp_fst_le_one hp
  have hp2 : (n : ℝ) + 1 ≤ p.2 := hyp_snd_ge hp
  show u p ≤ t
  rw [apply_eq u p]
  have habs : u (1, 0) ≤ |u (1, 0)| := le_abs_self _
  have h1 : u (1, 0) * p.1 ≤ |u (1, 0)| := by
    nlinarith [abs_nonneg (u (1, 0))]
  have h2 : u (0, 1) * p.2 ≤ u (0, 1) * ((n : ℝ) + 1) := by nlinarith
  nlinarith

/-- If `u (0,1) = 0` and `u (1,0) > 0`, then `u ≤ t` holds on a small hyperbola germ for
every positive `t`. -/
theorem hyp_subset_of_snd_zero_fst_pos (hb : u (0, 1) = 0) (ha : 0 < u (1, 0)) {t : ℝ}
    (ht : 0 < t) : ∃ n : ℕ, hyp n ⊆ halfLE u t := by
  obtain ⟨n, hn⟩ := exists_nat_gt (u (1, 0) / t)
  have hn' : u (1, 0) < t * (n : ℝ) := by
    rw [div_lt_iff₀ ht] at hn
    linarith [hn]
  refine ⟨n, fun p hp => ?_⟩
  have hp1 : 0 < p.1 := hyp_pos hp
  have hp4 : p.1 * ((n : ℝ) + 1) ≤ 1 := hp.2.2.2
  show u p ≤ t
  rw [apply_eq u p, hb]
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith

/-- If `u (0,1) = 0` and `u (1,0) > 0`, then `u > t` on every hyperbola germ for `t ≤ 0`. -/
theorem hyp_disjoint_of_snd_zero_fst_pos (hb : u (0, 1) = 0) (ha : 0 < u (1, 0)) {t : ℝ}
    (ht : t ≤ 0) : hyp 0 ∩ halfLE u t = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro p ⟨hp, hple⟩
  have hp1 : 0 < p.1 := hyp_pos hp
  have hle : u p ≤ t := hple
  rw [apply_eq u p, hb] at hle
  nlinarith

/-- If `u (0,1) = 0` and `u (1,0) ≤ 0`, then `u ≤ t` on every hyperbola germ for `t ≥ 0`. -/
theorem hyp_subset_of_snd_zero_fst_nonpos (hb : u (0, 1) = 0) (ha : u (1, 0) ≤ 0) {t : ℝ}
    (ht : 0 ≤ t) : hyp 0 ⊆ halfLE u t := by
  intro p hp
  have hp1 : 0 < p.1 := hyp_pos hp
  show u p ≤ t
  rw [apply_eq u p, hb]
  nlinarith

/-- If `u (0,1) = 0` and `u (1,0) ≤ 0`, then `u > t` on a small hyperbola germ for `t < 0`. -/
theorem hyp_disjoint_of_snd_zero_fst_nonpos (hb : u (0, 1) = 0) (ha : u (1, 0) ≤ 0) {t : ℝ}
    (ht : t < 0) : ∃ n : ℕ, hyp n ∩ halfLE u t = ∅ := by
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · -- `u = 0`, so `u p = 0 > t`
    refine ⟨0, ?_⟩
    rw [Set.eq_empty_iff_forall_notMem]
    rintro p ⟨-, hple⟩
    have hle : u p ≤ t := hple
    rw [eq_zero_of_coords ha0 hb] at hle
    simp only [ContinuousLinearMap.zero_apply] at hle
    linarith
  · obtain ⟨n, hn⟩ := exists_nat_gt (u (1, 0) / t)
    have hn' : t * (n : ℝ) < u (1, 0) := by
      rw [div_lt_iff_of_neg ht] at hn
      linarith [hn]
    refine ⟨n, ?_⟩
    rw [Set.eq_empty_iff_forall_notMem]
    rintro p ⟨hp, hple⟩
    have hp1 : 0 < p.1 := hyp_pos hp
    have hp4 : p.1 * ((n : ℝ) + 1) ≤ 1 := hp.2.2.2
    have hle : u p ≤ t := hple
    rw [apply_eq u p, hb] at hle
    nlinarith

theorem lev_Ghyp_of_snd_pos (hb : 0 < u (0, 1)) : lev Ghyp u = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro t ht
  obtain ⟨n, hn⟩ := hyp_disjoint_of_snd_pos hb t
  exact notMem_carrier_of_base_disjoint hyp_mem_Ghyp hn ht

theorem lev_Ghyp_of_snd_neg (hb : u (0, 1) < 0) : lev Ghyp u = Set.univ := by
  refine Set.eq_univ_of_forall fun t => ?_
  obtain ⟨n, hn⟩ := hyp_subset_of_snd_neg hb t
  exact mem_carrier_of_base_subset hyp_mem_Ghyp (isClosed_halfLE u t) (convex_halfLE u t) hn

theorem lev_Ghyp_of_snd_zero_fst_pos (hb : u (0, 1) = 0) (ha : 0 < u (1, 0)) :
    lev Ghyp u = Set.Ioi 0 := by
  ext t
  simp only [Set.mem_Ioi]
  constructor
  · intro ht
    by_contra hcon
    push_neg at hcon
    exact notMem_carrier_of_base_disjoint hyp_mem_Ghyp
      (hyp_disjoint_of_snd_zero_fst_pos hb ha hcon) ht
  · intro ht
    obtain ⟨n, hn⟩ := hyp_subset_of_snd_zero_fst_pos hb ha ht
    exact mem_carrier_of_base_subset hyp_mem_Ghyp (isClosed_halfLE u t) (convex_halfLE u t) hn

theorem lev_Ghyp_of_snd_zero_fst_nonpos (hb : u (0, 1) = 0) (ha : u (1, 0) ≤ 0) :
    lev Ghyp u = Set.Ici 0 := by
  ext t
  simp only [Set.mem_Ici]
  constructor
  · intro ht
    by_contra hcon
    push_neg at hcon
    obtain ⟨n, hn⟩ := hyp_disjoint_of_snd_zero_fst_nonpos hb ha hcon
    exact notMem_carrier_of_base_disjoint hyp_mem_Ghyp hn ht
  · intro ht
    exact mem_carrier_of_base_subset hyp_mem_Ghyp (isClosed_halfLE u t) (convex_halfLE u t)
      (hyp_subset_of_snd_zero_fst_nonpos hb ha ht)

end Hyp

/-! ### Level sets of the parabola filter -/

section Par

variable {u : (ℝ × ℝ) →L[ℝ] ℝ}

/-- If `u (0,1) > 0` then `u` is unbounded above on the parabola tails. -/
theorem par_disjoint_of_snd_pos (hb : 0 < u (0, 1)) (t : ℝ) :
    ∃ n : ℕ, par n ∩ halfLE u t = ∅ := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max ((1 - u (1, 0)) / u (0, 1)) (max t 0))
  have hn1 : (1 - u (1, 0)) / u (0, 1) < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  have hnt : t < (n : ℝ) := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hn
  have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hn
  have hlin : 1 < u (1, 0) + u (0, 1) * (n : ℝ) := by
    rw [div_lt_iff₀ hb] at hn1
    linarith
  refine ⟨n, ?_⟩
  rw [Set.eq_empty_iff_forall_notMem]
  rintro p ⟨⟨hp1, hp2⟩, hple⟩
  have hpos : 0 < p.1 := lt_of_lt_of_le hn0 hp1
  have hle : u p ≤ t := hple
  rw [apply_eq u p] at hle
  have h1 : u (0, 1) * p.1 ^ 2 ≤ u (0, 1) * p.2 := by nlinarith
  have hbn : u (0, 1) * (n : ℝ) ≤ u (0, 1) * p.1 := by nlinarith
  have k1 : p.1 * (u (1, 0) + u (0, 1) * (n : ℝ)) ≤ p.1 * (u (1, 0) + u (0, 1) * p.1) :=
    mul_le_mul_of_nonneg_left (by linarith) hpos.le
  have k2 : p.1 * 1 ≤ p.1 * (u (1, 0) + u (0, 1) * (n : ℝ)) := by nlinarith
  nlinarith

/-- If `u (0,1) < 0` then `u` is bounded above by any `t` on a far parabola tail. -/
theorem par_subset_of_snd_neg (hb : u (0, 1) < 0) (t : ℝ) :
    ∃ n : ℕ, par n ⊆ halfLE u t := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max ((u (1, 0) + 1) / (-u (0, 1))) (max (-t) 0))
  have hn1 : (u (1, 0) + 1) / (-u (0, 1)) < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  have hnt : -t < (n : ℝ) := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hn
  have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hn
  have hlin : u (1, 0) + u (0, 1) * (n : ℝ) < -1 := by
    rw [div_lt_iff₀ (by linarith)] at hn1
    linarith
  refine ⟨n, fun p hp => ?_⟩
  obtain ⟨hp1, hp2⟩ := hp
  have hpos : 0 < p.1 := lt_of_lt_of_le hn0 hp1
  show u p ≤ t
  rw [apply_eq u p]
  have h1 : u (0, 1) * p.2 ≤ u (0, 1) * p.1 ^ 2 := by nlinarith
  have hbn : u (0, 1) * p.1 ≤ u (0, 1) * (n : ℝ) := by nlinarith
  have k1 : p.1 * (u (1, 0) + u (0, 1) * p.1) ≤ p.1 * (u (1, 0) + u (0, 1) * (n : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) hpos.le
  have k2 : p.1 * (u (1, 0) + u (0, 1) * (n : ℝ)) ≤ p.1 * (-1) := by nlinarith
  nlinarith

/-- If `u (0,1) = 0` and `u (1,0) > 0` then `u` is unbounded above on the parabola tails. -/
theorem par_disjoint_of_snd_zero_fst_pos (hb : u (0, 1) = 0) (ha : 0 < u (1, 0)) (t : ℝ) :
    ∃ n : ℕ, par n ∩ halfLE u t = ∅ := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max (t / u (1, 0)) 0)
  have hn1 : t / u (1, 0) < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  have hlin : t < u (1, 0) * (n : ℝ) := by
    rw [div_lt_iff₀ ha] at hn1
    linarith
  refine ⟨n, ?_⟩
  rw [Set.eq_empty_iff_forall_notMem]
  rintro p ⟨⟨hp1, -⟩, hple⟩
  have hle : u p ≤ t := hple
  rw [apply_eq u p, hb] at hle
  nlinarith

/-- If `u (0,1) = 0` and `u (1,0) < 0` then `u` is bounded above by any `t` on a far
parabola tail. -/
theorem par_subset_of_snd_zero_fst_neg (hb : u (0, 1) = 0) (ha : u (1, 0) < 0) (t : ℝ) :
    ∃ n : ℕ, par n ⊆ halfLE u t := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max (t / u (1, 0)) 0)
  have hn1 : t / u (1, 0) < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  have hlin : u (1, 0) * (n : ℝ) < t := by
    rw [div_lt_iff_of_neg ha] at hn1
    linarith
  refine ⟨n, fun p hp => ?_⟩
  obtain ⟨hp1, -⟩ := hp
  show u p ≤ t
  rw [apply_eq u p, hb]
  nlinarith

theorem lev_Gpar_of_snd_pos (hb : 0 < u (0, 1)) : lev Gpar u = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro t ht
  obtain ⟨n, hn⟩ := par_disjoint_of_snd_pos hb t
  exact notMem_carrier_of_base_disjoint par_mem_Gpar hn ht

theorem lev_Gpar_of_snd_neg (hb : u (0, 1) < 0) : lev Gpar u = Set.univ := by
  refine Set.eq_univ_of_forall fun t => ?_
  obtain ⟨n, hn⟩ := par_subset_of_snd_neg hb t
  exact mem_carrier_of_base_subset par_mem_Gpar (isClosed_halfLE u t) (convex_halfLE u t) hn

theorem lev_Gpar_of_snd_zero_fst_pos (hb : u (0, 1) = 0) (ha : 0 < u (1, 0)) :
    lev Gpar u = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro t ht
  obtain ⟨n, hn⟩ := par_disjoint_of_snd_zero_fst_pos hb ha t
  exact notMem_carrier_of_base_disjoint par_mem_Gpar hn ht

theorem lev_Gpar_of_snd_zero_fst_neg (hb : u (0, 1) = 0) (ha : u (1, 0) < 0) :
    lev Gpar u = Set.univ := by
  refine Set.eq_univ_of_forall fun t => ?_
  obtain ⟨n, hn⟩ := par_subset_of_snd_zero_fst_neg hb ha t
  exact mem_carrier_of_base_subset par_mem_Gpar (isClosed_halfLE u t) (convex_halfLE u t) hn

end Par

/-! ### Reading off `sig` and `Qset` from the shape of the level set -/

section Shapes

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {F : ConvexFilter V}
variable {u : V →L[ℝ] ℝ}

theorem mem_Qset_of_lev_eq_empty (h : lev F u = ∅) : u ∈ Qset F := by
  refine ⟨?_, ?_⟩
  · rw [h]
    exact fun hc => (Set.empty_ne_univ hc)
  · intro t ht
    rw [h] at ht
    exact absurd ht (Set.notMem_empty t)

theorem mem_Qset_of_lev_eq_Ioi_zero (h : lev F u = Set.Ioi (0 : ℝ)) : u ∈ Qset F := by
  refine ⟨?_, ?_⟩
  · rw [h]
    intro hc
    have : (0 : ℝ) ∈ Set.Ioi (0 : ℝ) := hc ▸ Set.mem_univ 0
    exact absurd this (by simp)
  · intro t ht
    rw [h] at ht ⊢
    refine ⟨t / 2, ?_, ?_⟩
    · simp only [Set.mem_Ioi] at ht ⊢
      linarith
    · simp only [Set.mem_Ioi] at ht
      linarith

theorem notMem_Qset_of_lev_eq_univ (h : lev F u = Set.univ) : u ∉ Qset F := by
  intro hu
  exact hu.1 h

theorem notMem_Qset_of_lev_eq_Ici_zero (h : lev F u = Set.Ici (0 : ℝ)) : u ∉ Qset F := by
  intro hu
  have h0 : (0 : ℝ) ∈ lev F u := by rw [h]; exact Set.self_mem_Ici
  obtain ⟨t', ht', hlt⟩ := hu.2 0 h0
  rw [h] at ht'
  simp only [Set.mem_Ici] at ht'
  linarith

theorem sig_eq_zero_of_lev_eq_empty (h : lev F u = ∅) : sig F u = 0 := by
  rw [sig, h, Real.sInf_empty]

theorem sig_eq_zero_of_lev_eq_univ (h : lev F u = Set.univ) : sig F u = 0 := by
  rw [sig, h, Real.sInf_univ]

theorem sig_eq_zero_of_lev_eq_Ioi_zero (h : lev F u = Set.Ioi (0 : ℝ)) : sig F u = 0 := by
  rw [sig, h, csInf_Ioi]

theorem sig_eq_zero_of_lev_eq_Ici_zero (h : lev F u = Set.Ici (0 : ℝ)) : sig F u = 0 := by
  rw [sig, h, csInf_Ici]

end Shapes

/-! ### The invariants of the two filters agree -/

theorem sig_Ghyp (u : (ℝ × ℝ) →L[ℝ] ℝ) : sig Ghyp u = 0 := by
  rcases lt_trichotomy (u (0, 1)) 0 with hb | hb | hb
  · exact sig_eq_zero_of_lev_eq_univ (lev_Ghyp_of_snd_neg hb)
  · rcases lt_or_ge 0 (u (1, 0)) with ha | ha
    · exact sig_eq_zero_of_lev_eq_Ioi_zero (lev_Ghyp_of_snd_zero_fst_pos hb ha)
    · exact sig_eq_zero_of_lev_eq_Ici_zero (lev_Ghyp_of_snd_zero_fst_nonpos hb ha)
  · exact sig_eq_zero_of_lev_eq_empty (lev_Ghyp_of_snd_pos hb)

theorem sig_Gpar (u : (ℝ × ℝ) →L[ℝ] ℝ) : sig Gpar u = 0 := by
  rcases lt_trichotomy (u (0, 1)) 0 with hb | hb | hb
  · exact sig_eq_zero_of_lev_eq_univ (lev_Gpar_of_snd_neg hb)
  · rcases lt_trichotomy (u (1, 0)) 0 with ha | ha | ha
    · exact sig_eq_zero_of_lev_eq_univ (lev_Gpar_of_snd_zero_fst_neg hb ha)
    · have hu : u = 0 := eq_zero_of_coords ha hb
      rw [hu]
      exact sig_eq_zero_of_lev_eq_Ici_zero lev_zero
    · exact sig_eq_zero_of_lev_eq_empty (lev_Gpar_of_snd_zero_fst_pos hb ha)
  · exact sig_eq_zero_of_lev_eq_empty (lev_Gpar_of_snd_pos hb)

theorem sig_Ghyp_eq_sig_Gpar (u : (ℝ × ℝ) →L[ℝ] ℝ) : sig Ghyp u = sig Gpar u := by
  rw [sig_Ghyp, sig_Gpar]

/-- The common positivity cone of the two filters: the lexicographic cone with the second
coordinate dominant. -/
def lexCone : Set ((ℝ × ℝ) →L[ℝ] ℝ) :=
  {u : (ℝ × ℝ) →L[ℝ] ℝ | 0 < u (0, 1) ∨ (u (0, 1) = 0 ∧ 0 < u (1, 0))}

theorem Qset_Ghyp : Qset Ghyp = lexCone := by
  ext u
  simp only [lexCone, Set.mem_setOf_eq]
  constructor
  · intro hu
    rcases lt_trichotomy (u (0, 1)) 0 with hb | hb | hb
    · exact absurd hu (notMem_Qset_of_lev_eq_univ (lev_Ghyp_of_snd_neg hb))
    · rcases lt_or_ge 0 (u (1, 0)) with ha | ha
      · exact Or.inr ⟨hb, ha⟩
      · exact absurd hu (notMem_Qset_of_lev_eq_Ici_zero (lev_Ghyp_of_snd_zero_fst_nonpos hb ha))
    · exact Or.inl hb
  · rintro (hb | ⟨hb, ha⟩)
    · exact mem_Qset_of_lev_eq_empty (lev_Ghyp_of_snd_pos hb)
    · exact mem_Qset_of_lev_eq_Ioi_zero (lev_Ghyp_of_snd_zero_fst_pos hb ha)

theorem Qset_Gpar : Qset Gpar = lexCone := by
  ext u
  simp only [lexCone, Set.mem_setOf_eq]
  constructor
  · intro hu
    rcases lt_trichotomy (u (0, 1)) 0 with hb | hb | hb
    · exact absurd hu (notMem_Qset_of_lev_eq_univ (lev_Gpar_of_snd_neg hb))
    · rcases lt_trichotomy (u (1, 0)) 0 with ha | ha | ha
      · exact absurd hu (notMem_Qset_of_lev_eq_univ (lev_Gpar_of_snd_zero_fst_neg hb ha))
      · refine absurd hu ?_
        have hu0 : u = 0 := eq_zero_of_coords ha hb
        rw [hu0]
        exact notMem_Qset_of_lev_eq_Ici_zero lev_zero
      · exact Or.inr ⟨hb, ha⟩
    · exact Or.inl hb
  · rintro (hb | ⟨hb, ha⟩)
    · exact mem_Qset_of_lev_eq_empty (lev_Gpar_of_snd_pos hb)
    · exact mem_Qset_of_lev_eq_empty (lev_Gpar_of_snd_zero_fst_pos hb ha)

theorem Qset_Ghyp_eq_Qset_Gpar : Qset Ghyp = Qset Gpar := by
  rw [Qset_Ghyp, Qset_Gpar]

/-! ### The two filters are different -/

theorem hyp_zero_inter_par_two : hyp 0 ∩ par 2 = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro p ⟨hp, hq⟩
  have h1 : p.1 * ((0 : ℕ) + 1 : ℝ) ≤ 1 := hp.2.2.2
  have h2 : ((2 : ℕ) : ℝ) ≤ p.1 := hq.1
  norm_num at h1 h2
  linarith

theorem hyp_zero_notMem_Gpar : hyp 0 ∉ Gpar.carrier := by
  intro hmem
  have : hyp 0 ∩ par 2 ∈ Gpar.carrier := Gpar.inter_mem hmem (par_mem_Gpar 2)
  rw [hyp_zero_inter_par_two] at this
  exact Gpar.empty_not_mem this

theorem carrier_Ghyp_ne_carrier_Gpar : Ghyp.carrier ≠ Gpar.carrier := by
  intro h
  exact hyp_zero_notMem_Gpar (h ▸ hyp_mem_Ghyp 0)

end SigCounterexample

/-- **The statement of §5 of the work order, without the hypothesis `Nset F = Nset F'`, is
false.** There are two distinct maximal convex filters on `ℝ × ℝ` with the same support
number `sig` and the same positivity cone `Qset`. -/
theorem exists_maximal_pair_sig_Qset_eq_carrier_ne :
    ∃ F F' : ConvexFilter (ℝ × ℝ), IsMaximal F ∧ IsMaximal F' ∧
      (∀ u : (ℝ × ℝ) →L[ℝ] ℝ, sig F u = sig F' u) ∧ Qset F = Qset F' ∧
      F.carrier ≠ F'.carrier :=
  ⟨SigCounterexample.Ghyp, SigCounterexample.Gpar, SigCounterexample.Ghyp_isMaximal,
    SigCounterexample.Gpar_isMaximal, SigCounterexample.sig_Ghyp_eq_sig_Gpar,
    SigCounterexample.Qset_Ghyp_eq_Qset_Gpar, SigCounterexample.carrier_Ghyp_ne_carrier_Gpar⟩

/-- The same statement in negated form: `sig` and `Qset` alone do not determine a maximal
convex filter. -/
theorem not_carrier_eq_of_sig_Qset :
    ¬ ∀ F F' : ConvexFilter (ℝ × ℝ), IsMaximal F → IsMaximal F' →
        (∀ u : (ℝ × ℝ) →L[ℝ] ℝ, sig F u = sig F' u) → Qset F = Qset F' →
        F.carrier = F'.carrier := by
  intro hcon
  obtain ⟨F, F', hF, hF', hsig, hQ, hne⟩ := exists_maximal_pair_sig_Qset_eq_carrier_ne
  exact hne (hcon F F' hF hF' hsig hQ)

end ConvexFilter
