import ConvexFilters.LimitMembers

/-!
# The ridge: a member of the algebra that is not in `C₀`

WO-13, Part E; Lemma 5.1 of `paper/limits-algebra-note.tex`, on `V = ℝ × ℝ`.

`ridge (x, y) = max 0 (1 - |y - x²|)` is continuous, equals `1` at every point of the
parabola, lies in the algebra `mem_A`, has limit `0` along every non-principal maximal
convex filter, and does not tend to `0` along the cocompact filter.  So the algebra
contains a bounded continuous function that is invisible to every non-principal maximal
filter yet visible at infinity; this is the obstruction behind Theorem 5.2 of the note
(which is out of scope, see WO-13 §8).

## The argument

The note proposes a case analysis over the escape data of `F`.  The argument used here is
uniform and needs no case analysis, and rests on the strict convexity of the parabola:

* `isBounded_inter_band_of_subset_below`: a convex set staying strictly below the parabola
  `y = x² + 2` meets the band `|y - x²| ≤ 1` in a bounded set.  Indeed if two band points
  `p`, `q` of the set had `(p.1 - q.1)² ≥ 12`, their midpoint — which lies in the set —
  would have `y - x² ≥ (p.1 - q.1)²/4 - 1 ≥ 2`.
* `exists_mem_disjoint_band`: hence *every* maximal convex filter which is not principal
  has a member disjoint from the band.  Either the convex set `{y ≥ x² + 2}` is a member,
  and it misses the band outright, or by the maximality criterion some member `E` is
  disjoint from it, so `E` stays below the parabola, meets the band in a bounded set, and
  Proposition 2.3 (`exists_mem_disjoint_of_not_principal`) removes that bounded remainder.

`ridge` vanishes off the band, so it is constant — and zero — on such a member.
-/

open Filter Topology

namespace ConvexFilter

namespace Limits

/-! ### The band and the region above the parabola -/

/-- The band `|y - x²| ≤ 1`, outside which the ridge vanishes. -/
def band : Set (ℝ × ℝ) := {p : ℝ × ℝ | |p.2 - p.1 ^ 2| ≤ 1}

/-- The closed convex region `y ≥ x² + 2`, which misses the band. -/
def aboveParabola : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 ^ 2 + 2 ≤ p.2}

theorem isClosed_aboveParabola : IsClosed aboveParabola := by
  have h : Continuous fun p : ℝ × ℝ => p.1 ^ 2 + 2 := by fun_prop
  exact isClosed_le h continuous_snd

theorem convex_aboveParabola : Convex ℝ aboveParabola := by
  rintro p hp q hq a b ha hb hab
  have hp' : p.1 ^ 2 + 2 ≤ p.2 := hp
  have hq' : q.1 ^ 2 + 2 ≤ q.2 := hq
  show (a • p + b • q).1 ^ 2 + 2 ≤ (a • p + b • q).2
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have hkey : a * p.1 ^ 2 + b * q.1 ^ 2 - (a * p.1 + b * q.1) ^ 2 = a * b * (p.1 - q.1) ^ 2 := by
    have hb' : b = 1 - a := by linarith
    subst hb'; ring
  have h1 : a * (p.1 ^ 2 + 2) ≤ a * p.2 := mul_le_mul_of_nonneg_left hp' ha
  have h2 : b * (q.1 ^ 2 + 2) ≤ b * q.2 := mul_le_mul_of_nonneg_left hq' hb
  have h3 : 0 ≤ a * b * (p.1 - q.1) ^ 2 :=
    mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)
  nlinarith

theorem disjoint_aboveParabola_band : aboveParabola ∩ band = ∅ := by
  ext p
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hp hband
  have h1 : p.1 ^ 2 + 2 ≤ p.2 := hp
  have h2 : |p.2 - p.1 ^ 2| ≤ 1 := hband
  have h3 : p.2 - p.1 ^ 2 ≤ 1 := le_trans (le_abs_self _) h2
  linarith

/-- **Strict convexity of the parabola.** A convex set staying strictly below the parabola
`y = x² + 2` meets the band in a bounded set. -/
theorem isBounded_inter_band_of_subset_below {E : Set (ℝ × ℝ)} (hE : Convex ℝ E)
    (hbelow : ∀ p ∈ E, p.2 < p.1 ^ 2 + 2) : Bornology.IsBounded (E ∩ band) := by
  rcases Set.eq_empty_or_nonempty (E ∩ band) with hempty | ⟨p₀, hp₀E, hp₀b⟩
  · rw [hempty]; exact Bornology.isBounded_empty
  -- two band points of `E` have close first coordinates
  have hclose : ∀ p ∈ E ∩ band, (p.1 - p₀.1) ^ 2 < 12 := by
    rintro p ⟨hpE, hpb⟩
    have hmid : ((1 : ℝ) / 2) • p + ((1 : ℝ) / 2) • p₀ ∈ E :=
      hE hpE hp₀E (by norm_num) (by norm_num) (by norm_num)
    have hmid' := hbelow _ hmid
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hmid'
    have h1 : p.1 ^ 2 - 1 ≤ p.2 := by
      have : |p.2 - p.1 ^ 2| ≤ 1 := hpb
      have := neg_le_of_abs_le this
      linarith
    have h2 : p₀.1 ^ 2 - 1 ≤ p₀.2 := by
      have : |p₀.2 - p₀.1 ^ 2| ≤ 1 := hp₀b
      have := neg_le_of_abs_le this
      linarith
    nlinarith
  -- hence the whole intersection lies in a ball
  set M : ℝ := |p₀.1| + 4 with hM
  have hMnonneg : 0 ≤ M := by positivity
  refine Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := (0 : ℝ × ℝ))
    (r := max M (M ^ 2 + 1))) ?_
  intro p hp
  have hx : |p.1| ≤ M := by
    have h := hclose p hp
    have habs : |p.1 - p₀.1| < 4 := by
      by_contra hcon
      push_neg at hcon
      nlinarith [abs_nonneg (p.1 - p₀.1), sq_abs (p.1 - p₀.1)]
    have := abs_sub_abs_le_abs_sub p.1 p₀.1
    rw [hM]
    linarith
  have hy : |p.2| ≤ M ^ 2 + 1 := by
    have hpb : |p.2 - p.1 ^ 2| ≤ 1 := hp.2
    have h1 : p.2 - p.1 ^ 2 ≤ 1 := le_trans (le_abs_self _) hpb
    have h2 : -(1 : ℝ) ≤ p.2 - p.1 ^ 2 := neg_le_of_abs_le hpb
    have hsq : p.1 ^ 2 ≤ M ^ 2 := by
      have := abs_nonneg p.1
      nlinarith [sq_abs p.1]
    have hsq0 : (0 : ℝ) ≤ p.1 ^ 2 := sq_nonneg _
    rw [abs_le]
    constructor <;> nlinarith
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
  simp only [Real.norm_eq_abs]
  exact max_le (le_trans hx (le_max_left _ _)) (le_trans hy (le_max_right _ _))

/-- Every non-principal maximal convex filter of the plane has a member disjoint from the
band. -/
theorem exists_mem_disjoint_band {F : ConvexFilter (ℝ × ℝ)} (hF : IsMaximal F)
    (hnp : ∀ p, F.carrier ≠ (principal p).carrier) : ∃ C ∈ F.carrier, C ∩ band = ∅ := by
  by_cases hmem : aboveParabola ∈ F.carrier
  · exact ⟨aboveParabola, hmem, disjoint_aboveParabola_band⟩
  · obtain ⟨E, hE, hEdisj⟩ :=
      (isMaximal_iff F).mp hF isClosed_aboveParabola convex_aboveParabola hmem
    have hbelow : ∀ p ∈ E, p.2 < p.1 ^ 2 + 2 := by
      intro p hp
      by_contra hcon
      push_neg at hcon
      have : p ∈ aboveParabola ∩ E := ⟨hcon, hp⟩
      rw [hEdisj] at this
      exact this
    have hbdd := isBounded_inter_band_of_subset_below (F.convex_of_mem hE) hbelow
    obtain ⟨C, hC, hCdisj⟩ := exists_mem_disjoint_of_not_principal hF hnp _ hbdd
    refine ⟨E ∩ C, F.inter_mem hE hC, ?_⟩
    ext p
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    rintro ⟨hpE, hpC⟩ hpb
    have : p ∈ C ∩ (E ∩ band) := ⟨hpC, hpE, hpb⟩
    rw [hCdisj] at this
    exact this

/-! ### The ridge -/

/-- The ridge of Lemma 5.1: a continuous bump of height `1` along the parabola. -/
def ridge : ℝ × ℝ → ℝ := fun p => max 0 (1 - |p.2 - p.1 ^ 2|)

theorem continuous_ridge : Continuous ridge := by
  unfold ridge
  fun_prop

theorem ridge_eq_one (x : ℝ) : ridge (x, x ^ 2) = 1 := by
  simp [ridge]

/-- The ridge vanishes off the band. -/
theorem ridge_eq_zero_of_notMem_band {p : ℝ × ℝ} (hp : p ∉ band) : ridge p = 0 := by
  have h : 1 < |p.2 - p.1 ^ 2| := lt_of_not_ge hp
  simp only [ridge, max_eq_left_iff]
  linarith

/-- **Lemma 5.1, the limits.** The ridge has limit `0` along every non-principal maximal
convex filter. -/
theorem lim_ridge_eq_zero {F : ConvexFilter (ℝ × ℝ)} (hF : IsMaximal F)
    (hnp : ∀ p, F.carrier ≠ (principal p).carrier) : lim ridge F = 0 := by
  obtain ⟨C, hC, hCdisj⟩ := exists_mem_disjoint_band hF hnp
  refine (hasLim_and_lim_of_eqOn hC fun p hp => ridge_eq_zero_of_notMem_band ?_).2
  intro hpb
  have : p ∈ C ∩ band := ⟨hp, hpb⟩
  rw [hCdisj] at this
  exact this

/-- **Lemma 5.1, membership.** The ridge lies in the algebra. -/
theorem mem_A_ridge : mem_A ridge := by
  intro F hF
  by_cases hnp : ∀ p, F.carrier ≠ (principal p).carrier
  · obtain ⟨C, hC, hCdisj⟩ := exists_mem_disjoint_band hF hnp
    refine (hasLim_and_lim_of_eqOn hC fun p hp => ridge_eq_zero_of_notMem_band ?_).1
    intro hpb
    have : p ∈ C ∩ band := ⟨hp, hpb⟩
    rw [hCdisj] at this
    exact this
  · push_neg at hnp
    obtain ⟨p, hp⟩ := hnp
    have hFp : F = principal p := ext_of_carrier_eq hp
    subst hFp
    exact hasLim_principal ridge p

/-- **Lemma 5.1, the ridge is not in `C₀`.** -/
theorem not_tendsto_cocompact_ridge :
    ¬ Filter.Tendsto ridge (Filter.cocompact (ℝ × ℝ)) (nhds 0) := by
  intro hcon
  have hmem : {p : ℝ × ℝ | dist (ridge p) 0 < 1 / 2} ∈ Filter.cocompact (ℝ × ℝ) :=
    hcon (Metric.ball_mem_nhds (0 : ℝ) (by norm_num))
  obtain ⟨K, hKcomp, hKsub⟩ := Filter.mem_cocompact.mp hmem
  obtain ⟨r, hr⟩ := hKcomp.isBounded.subset_closedBall (0 : ℝ × ℝ)
  set x : ℝ := |r| + 1 with hx
  have hnotK : ((x, x ^ 2) : ℝ × ℝ) ∉ K := by
    intro hK
    have := hr hK
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def] at this
    simp only [Real.norm_eq_abs] at this
    have h1 : |x| ≤ r := le_trans (le_max_left _ _) this
    have h2 : r ≤ |r| := le_abs_self r
    have h3 : |x| = x := abs_of_nonneg (by positivity)
    rw [h3, hx] at h1
    linarith
  have := hKsub hnotK
  simp only [Set.mem_setOf_eq, ridge_eq_one x, Real.dist_eq, sub_zero] at this
  rw [abs_one] at this
  linarith

end Limits

end ConvexFilter
