import ConvexFilters.Coords
import ConvexFilters.Extension
import ConvexFilters.Flat

/-!
# Realization: the generating family and the forcing of the invariants

This file formalizes Section 5 of the paper. Fix `1 ≤ d ≤ m ≤ n`, a basis `b` of `V` indexed
by `Fin n`, and a base point `a`. Writing `xᵢ = coordAt b a i x`, the generating family is

`gen b a d m K M c = {x | xⱼ = 0 (j ≥ m), x_{d-1} ≥ K, xᵢ ≥ M x_{i+1} + M (i+1 < d),`
`  x_d ≤ c, xⱼ ≤ c x_{j-1} (d < j < m), xⱼ x_{d-1} ≥ 1 (d ≤ j < m)}`

— the paper's constraints (5.1)–(5.5) with the indices shifted to be `0`-based, so that the
escape block is `0 ≤ i < d`, the approach block is `d ≤ j < m`, and the killed block is
`m ≤ j < n`. The paper's `x_d`, the last escape coordinate, is `coordAt b a (d - 1)`.

Part C establishes the positivity and bound lemmas on `gen`, its convexity, closedness,
nonemptiness and monotonicity in the parameters. Part D shows that a maximal filter
containing every `gen b a d m k k (1/k)`, `k ≥ 1`, has the invariants

`Mset F = M0 b m`, `Qset F = Q0 b m`, `Aset F = A0 b a d`.

Part E puts the two together with the antitone-base machinery of
`ConvexFilters/Extension.lean` to produce such a maximal filter.
-/

open Module

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

namespace ConvexFilter

/-! ## Part C — the generators -/

/-- The generating family of Section 5: the paper's constraints (5.1)–(5.5) in `0`-based
indices. The escape block is `0 ≤ i < d`, the approach block is `d ≤ j < m` and the killed
block is `m ≤ j`. -/
def gen {n : ℕ} (b : Basis (Fin n) ℝ V) (a : V) (d m : ℕ) (K M c : ℝ) : Set V :=
  {x | (∀ j, m ≤ j → coordAt b a j x = 0)
     ∧ K ≤ coordAt b a (d - 1) x
     ∧ (∀ i, i + 1 < d → M * coordAt b a (i + 1) x + M ≤ coordAt b a i x)
     ∧ (d < m → coordAt b a d x ≤ c)
     ∧ (∀ j, d < j → j < m → coordAt b a j x ≤ c * coordAt b a (j - 1) x)
     ∧ (∀ j, d ≤ j → j < m → 1 ≤ coordAt b a j x * coordAt b a (d - 1) x)}

section Gen

variable {n : ℕ} {b : Basis (Fin n) ℝ V} {a : V} {d m : ℕ} {K M c : ℝ} {x : V}

omit [FiniteDimensional ℝ V]

theorem mem_gen_iff :
    x ∈ gen b a d m K M c ↔
      ((∀ j, m ≤ j → coordAt b a j x = 0)
     ∧ K ≤ coordAt b a (d - 1) x
     ∧ (∀ i, i + 1 < d → M * coordAt b a (i + 1) x + M ≤ coordAt b a i x)
     ∧ (d < m → coordAt b a d x ≤ c)
     ∧ (∀ j, d < j → j < m → coordAt b a j x ≤ c * coordAt b a (j - 1) x)
     ∧ (∀ j, d ≤ j → j < m → 1 ≤ coordAt b a j x * coordAt b a (d - 1) x)) := Iff.rfl

theorem gen_killed (hx : x ∈ gen b a d m K M c) : ∀ j, m ≤ j → coordAt b a j x = 0 := hx.1

theorem gen_le_last (hx : x ∈ gen b a d m K M c) : K ≤ coordAt b a (d - 1) x := hx.2.1

theorem gen_step (hx : x ∈ gen b a d m K M c) :
    ∀ i, i + 1 < d → M * coordAt b a (i + 1) x + M ≤ coordAt b a i x := hx.2.2.1

theorem gen_first_approach (hx : x ∈ gen b a d m K M c) (h : d < m) :
    coordAt b a d x ≤ c := hx.2.2.2.1 h

theorem gen_ratio (hx : x ∈ gen b a d m K M c) :
    ∀ j, d < j → j < m → coordAt b a j x ≤ c * coordAt b a (j - 1) x := hx.2.2.2.2.1

theorem gen_hyperbola (hx : x ∈ gen b a d m K M c) :
    ∀ j, d ≤ j → j < m → 1 ≤ coordAt b a j x * coordAt b a (d - 1) x := hx.2.2.2.2.2

/-! ### Positivity and bounds -/

/-- On a generator every escape coordinate is positive. -/
theorem gen_pos_escape (hd : 1 ≤ d) (hK : 1 ≤ K) (hM : 1 ≤ M) (hx : x ∈ gen b a d m K M c) :
    ∀ i, i < d → 0 < coordAt b a i x := by
  have hlast : 0 < coordAt b a (d - 1) x := lt_of_lt_of_le (by linarith) (gen_le_last hx)
  have key : ∀ k i : ℕ, i < d → d - 1 - i ≤ k → 0 < coordAt b a i x := by
    intro k
    induction k with
    | zero =>
        intro i hi h0
        have : i = d - 1 := by omega
        rw [this]; exact hlast
    | succ k ih =>
        intro i hi hk
        by_cases hid : i = d - 1
        · rw [hid]; exact hlast
        · have hi1 : i + 1 < d := by omega
          have hpos := ih (i + 1) (by omega) (by omega)
          have hstep := gen_step hx i hi1
          nlinarith
  intro i hi
  exact key (d - 1 - i) i hi le_rfl

/-- On a generator the escape coordinates decrease. -/
theorem gen_antitone_coord (hd : 1 ≤ d) (hK : 1 ≤ K) (hM : 1 ≤ M) (hx : x ∈ gen b a d m K M c) :
    ∀ i, i + 1 < d → coordAt b a (i + 1) x ≤ coordAt b a i x := by
  intro i hi
  have hpos := gen_pos_escape hd hK hM hx (i + 1) (by omega)
  have hstep := gen_step hx i hi
  nlinarith

/-- The escape coordinates decrease along the whole block. -/
theorem gen_le_of_le_escape (hd : 1 ≤ d) (hK : 1 ≤ K) (hM : 1 ≤ M)
    (hx : x ∈ gen b a d m K M c) :
    ∀ i j, i ≤ j → j < d → coordAt b a j x ≤ coordAt b a i x := by
  intro i j hij hjd
  induction j with
  | zero =>
      have : i = 0 := by omega
      rw [this]
  | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h | h
      · have h1 : coordAt b a (j + 1) x ≤ coordAt b a j x :=
          gen_antitone_coord hd hK hM hx j hjd
        exact h1.trans (ih (by omega) (by omega))
      · have : i = j + 1 := by omega
        rw [this]

/-- On a generator every approach coordinate is positive. -/
theorem gen_pos_approach (hK : 1 ≤ K) (hx : x ∈ gen b a d m K M c) :
    ∀ j, d ≤ j → j < m → 0 < coordAt b a j x := by
  intro j hj hjm
  have hlast : 0 < coordAt b a (d - 1) x := lt_of_lt_of_le (by linarith) (gen_le_last hx)
  have hprod := gen_hyperbola hx j hj hjm
  nlinarith

/-- On a generator the approach coordinates decrease. -/
theorem gen_antitone_approach (hK : 1 ≤ K) (hc1 : c ≤ 1)
    (hx : x ∈ gen b a d m K M c) :
    ∀ i j, d ≤ i → i ≤ j → j < m → coordAt b a j x ≤ coordAt b a i x := by
  intro i j hdi hij hjm
  induction j with
  | zero =>
      have : i = 0 := by omega
      rw [this]
  | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h | h
      · have hdj : d < j + 1 := by omega
        have hr := gen_ratio hx (j + 1) hdj hjm
        simp only [Nat.add_sub_cancel] at hr
        have hpos := gen_pos_approach hK hx j (by omega) (by omega)
        have : coordAt b a (j + 1) x ≤ coordAt b a j x := by nlinarith
        exact this.trans (ih (by omega) (by omega))
      · have : i = j + 1 := by omega
        rw [this]

/-- On a generator every approach coordinate is at most `c`. -/
theorem gen_le_c (hK : 1 ≤ K) (hc1 : c ≤ 1) (hx : x ∈ gen b a d m K M c) :
    ∀ j, d ≤ j → j < m → coordAt b a j x ≤ c := by
  intro j hj hjm
  have hfirst : coordAt b a d x ≤ c := gen_first_approach hx (by omega)
  exact (gen_antitone_approach hK hc1 hx d j le_rfl hj hjm).trans hfirst

/-- Beyond the first, each approach coordinate is at most `c` times an earlier one. -/
theorem gen_le_c_mul (hK : 1 ≤ K) (hc1 : c ≤ 1) (hx : x ∈ gen b a d m K M c) :
    ∀ k j, d ≤ k → k < j → j < m → coordAt b a j x ≤ c * coordAt b a k x := by
  intro k j hk hkj hjm
  have hstep : coordAt b a (k + 1) x ≤ c * coordAt b a k x := by
    have := gen_ratio hx (k + 1) (by omega) (by omega)
    simpa using this
  exact (gen_antitone_approach hK hc1 hx (k + 1) j (by omega) (by omega) hjm).trans hstep

/-! ### Convexity, closedness, nonemptiness, monotonicity -/

/-- The convexity of the hyperbolic region `{(p, q) : p, q > 0, p q ≥ 1}`; this is the
argument used for the hyperbola family of `ConvexFilters/SigCounterexample.lean`. -/
theorem hyperbola_combo {p q p' q' s r : ℝ} (hp : 0 < p) (hq : 0 < q) (hp' : 0 < p')
    (hq' : 0 < q') (h1 : 1 ≤ p * q) (h2 : 1 ≤ p' * q') (hs : 0 ≤ s) (hr : 0 ≤ r)
    (hsr : s + r = 1) : 1 ≤ (s * p + r * p') * (s * q + r * q') := by
  have hcross : 2 ≤ p * q' + p' * q := by
    have hprod : 1 ≤ (p * q') * (p' * q) := by nlinarith
    nlinarith [sq_nonneg (p * q' - p' * q), mul_pos hp hq', mul_pos hp' hq]
  have e1 : s * s ≤ s * s * (p * q) := by nlinarith [mul_nonneg hs hs]
  have e2 : r * r ≤ r * r * (p' * q') := by nlinarith [mul_nonneg hr hr]
  have e3 : s * r * 2 ≤ s * r * (p * q' + p' * q) := by
    have := mul_nonneg hs hr
    nlinarith
  have hexp : (s * p + r * p') * (s * q + r * q')
      = s * s * (p * q) + s * r * (p * q' + p' * q) + r * r * (p' * q') := by ring
  have hone : s * s + s * r * 2 + r * r = 1 := by nlinarith
  rw [hexp]
  linarith

theorem gen_convex (hd : 1 ≤ d) (hK : 1 ≤ K) (hM : 1 ≤ M) :
    Convex ℝ (gen b a d m K M c) := by
  intro x hx y hy s r hs hr hsr
  have hxpos := gen_pos_escape hd hK hM hx
  have hypos := gen_pos_escape hd hK hM hy
  have hxap := gen_pos_approach hK hx
  have hyap := gen_pos_approach hK hy
  have hcoord : ∀ i : ℕ, coordAt b a i (s • x + r • y)
      = s * coordAt b a i x + r * coordAt b a i y := fun i => coordAt_combo b a i hsr x y
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rw [hcoord j, gen_killed hx j hj, gen_killed hy j hj]
    ring
  · rw [hcoord (d - 1)]
    have h1 := gen_le_last hx
    have h2 := gen_le_last hy
    nlinarith
  · intro i hi
    rw [hcoord i, hcoord (i + 1)]
    have h1 := gen_step hx i hi
    have h2 := gen_step hy i hi
    nlinarith
  · intro hdm
    rw [hcoord d]
    have h1 := gen_first_approach hx hdm
    have h2 := gen_first_approach hy hdm
    have hcc : s * c + r * c = c := by rw [← add_mul, hsr, one_mul]
    linarith [mul_le_mul_of_nonneg_left h1 hs, mul_le_mul_of_nonneg_left h2 hr]
  · intro j hj hjm
    rw [hcoord j, hcoord (j - 1)]
    have h1 := gen_ratio hx j hj hjm
    have h2 := gen_ratio hy j hj hjm
    nlinarith
  · intro j hj hjm
    rw [hcoord j, hcoord (d - 1)]
    refine hyperbola_combo (hxap j hj hjm) ?_ (hyap j hj hjm) ?_
      (gen_hyperbola hx j hj hjm) (gen_hyperbola hy j hj hjm) hs hr hsr
    · exact lt_of_lt_of_le (by linarith) (gen_le_last hx)
    · exact lt_of_lt_of_le (by linarith) (gen_le_last hy)

end Gen

section GenClosed

variable {n : ℕ} {b : Basis (Fin n) ℝ V} {a : V} {d m : ℕ} {K M c : ℝ}

theorem isClosed_gen : IsClosed (gen b a d m K M c) := by
  have hset : gen b a d m K M c =
      (⋂ j, ⋂ (_ : m ≤ j), {x : V | coordAt b a j x = 0}) ∩
      ({x : V | K ≤ coordAt b a (d - 1) x} ∩
      ((⋂ i, ⋂ (_ : i + 1 < d),
          {x : V | M * coordAt b a (i + 1) x + M ≤ coordAt b a i x}) ∩
      ((⋂ (_ : d < m), {x : V | coordAt b a d x ≤ c}) ∩
      ((⋂ j, ⋂ (_ : d < j), ⋂ (_ : j < m),
          {x : V | coordAt b a j x ≤ c * coordAt b a (j - 1) x}) ∩
      (⋂ j, ⋂ (_ : d ≤ j), ⋂ (_ : j < m),
          {x : V | 1 ≤ coordAt b a j x * coordAt b a (d - 1) x}))))) := by
    ext z
    simp only [gen, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [hset]
  refine IsClosed.inter (isClosed_iInter fun j => isClosed_iInter fun _ => ?_) ?_
  · exact isClosed_coordAt_eq j 0
  refine IsClosed.inter (isClosed_coordAt_ge (d - 1) K) ?_
  refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun _ => ?_) ?_
  · exact isClosed_le ((continuous_const.mul (continuous_coordAt b a (i + 1))).add
      continuous_const) (continuous_coordAt b a i)
  refine IsClosed.inter (isClosed_iInter fun _ => isClosed_coordAt_le d c) ?_
  refine IsClosed.inter (isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_iInter fun _ => ?_) ?_
  · exact isClosed_le (continuous_coordAt b a j)
      (continuous_const.mul (continuous_coordAt b a (j - 1)))
  · exact isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_le continuous_const
        ((continuous_coordAt b a j).mul (continuous_coordAt b a (d - 1)))

end GenClosed

section Nonempty

variable {n : ℕ} (b : Basis (Fin n) ℝ V) (a : V) {d m : ℕ} {K M c : ℝ}

/-- The escape coordinates of the explicit point of `gen_nonempty`, indexed by their distance
to the last escape index `d - 1`. -/
noncomputable def escVal (T M : ℝ) : ℕ → ℝ
  | 0 => T
  | (s + 1) => M * escVal T M s + M

theorem escVal_pos {T : ℝ} (hT : 0 < T) (hM : 1 ≤ M) : ∀ s, 0 < escVal T M s := by
  intro s
  induction s with
  | zero => exact hT
  | succ s ih => have : 0 < M := by linarith
                 simp only [escVal]
                 nlinarith

/-- The coordinate function of the explicit point of `gen_nonempty`. -/
noncomputable def genPointCoord (d m : ℕ) (T M c : ℝ) (i : ℕ) : ℝ :=
  if i < d then escVal T M (d - 1 - i) else if i < m then c ^ (i - d + 1) else 0

omit [FiniteDimensional ℝ V] in
theorem gen_nonempty (hd : 1 ≤ d) (hdm : d ≤ m) (hmn : m ≤ n) (hK : 1 ≤ K)
    (hc : 0 < c) (hc1 : c ≤ 1) : (gen b a d m K M c).Nonempty := by
  classical
  set T : ℝ := max K ((c⁻¹) ^ (m - d)) with hT
  have hTK : K ≤ T := le_max_left _ _
  have hTpos : 0 < T := lt_of_lt_of_le (by linarith) hTK
  have hcpow : (0:ℝ) < c ^ (m - d) := pow_pos hc _
  have hTc : 1 ≤ T * c ^ (m - d) := by
    have h1 : (c⁻¹) ^ (m - d) ≤ T := le_max_right _ _
    have h2 : (c⁻¹) ^ (m - d) * c ^ (m - d) = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt hc), one_pow]
    nlinarith
  set f : ℕ → ℝ := genPointCoord d m T M c with hf
  set p : V := a + ∑ j : Fin n, f (j : ℕ) • b j with hp
  have hcoord : ∀ i : ℕ, i < n → coordAt b a i p = f i := by
    intro i hi
    have := coordAt_point b a (fun j : Fin n => f (j : ℕ)) hi
    simpa using this
  have hcoordAll : ∀ i : ℕ, coordAt b a i p = f i := by
    intro i
    by_cases hi : i < n
    · exact hcoord i hi
    · rw [coordAt_of_le (Nat.not_lt.1 hi)]
      have : ¬ i < d := by omega
      have h2 : ¬ i < m := by omega
      simp [hf, genPointCoord, this, h2]
  -- values of `f`
  have hf_esc : ∀ i, i < d → f i = escVal T M (d - 1 - i) := by
    intro i hi; simp [hf, genPointCoord, hi]
  have hf_app : ∀ j, d ≤ j → j < m → f j = c ^ (j - d + 1) := by
    intro j hj hjm
    have : ¬ j < d := by omega
    simp [hf, genPointCoord, this, hjm]
  have hf_zero : ∀ j, m ≤ j → f j = 0 := by
    intro j hj
    have h1 : ¬ j < d := by omega
    have h2 : ¬ j < m := by omega
    simp [hf, genPointCoord, h1, h2]
  refine ⟨p, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj; rw [hcoordAll j, hf_zero j hj]
  · rw [hcoordAll (d - 1), hf_esc (d - 1) (by omega)]
    simpa using hTK
  · intro i hi
    rw [hcoordAll i, hcoordAll (i + 1), hf_esc i (by omega), hf_esc (i + 1) (by omega)]
    have : d - 1 - i = (d - 1 - (i + 1)) + 1 := by omega
    rw [this]
    simp [escVal]
  · intro hdm'
    rw [hcoordAll d, hf_app d le_rfl hdm']
    simp
  · intro j hj hjm
    rw [hcoordAll j, hcoordAll (j - 1), hf_app j (by omega) hjm, hf_app (j - 1) (by omega)
      (by omega)]
    have : j - d + 1 = (j - 1 - d + 1) + 1 := by omega
    rw [this, pow_succ]
    ring_nf
    rw [mul_comm]
  · intro j hj hjm
    rw [hcoordAll j, hcoordAll (d - 1), hf_app j hj hjm, hf_esc (d - 1) (by omega)]
    have hsub : d - 1 - (d - 1) = 0 := by omega
    rw [hsub]
    show 1 ≤ c ^ (j - d + 1) * escVal T M 0
    have hesc0 : escVal T M 0 = T := rfl
    rw [hesc0]
    have hle : c ^ (m - d) ≤ c ^ (j - d + 1) :=
      pow_le_pow_of_le_one (le_of_lt hc) hc1 (by omega)
    nlinarith

end Nonempty

section Mono

variable {n : ℕ} {b : Basis (Fin n) ℝ V} {a : V} {d m : ℕ}

omit [FiniteDimensional ℝ V]

theorem gen_mono {K K' M M' c c' : ℝ} (hd : 1 ≤ d) (hK' : 1 ≤ K') (hM' : 1 ≤ M')
    (hK : K ≤ K') (hM : M ≤ M') (hc : c' ≤ c) :
    gen b a d m K' M' c' ⊆ gen b a d m K M c := by
  intro x hx
  have hesc := gen_pos_escape hd hK' hM' hx
  have happ := gen_pos_approach hK' hx
  refine ⟨gen_killed hx, le_trans hK (gen_le_last hx), ?_, ?_, ?_, gen_hyperbola hx⟩
  · intro i hi
    have h := gen_step hx i hi
    have hpos := hesc (i + 1) (by omega)
    nlinarith
  · intro hdm
    exact le_trans (gen_first_approach hx hdm) hc
  · intro j hj hjm
    have h := gen_ratio hx j hj hjm
    have hpos := happ (j - 1) (by omega) (by omega)
    nlinarith

end Mono


/-! ## Part D — forcing

`Q0 b m` is the set of functionals whose first nonvanishing coordinate among the first `m` is
positive, `M0 b m` the set of those with no nonvanishing coordinate among the first `m`, and
`A0 b a d` the flat `a + span (b 0, …, b (d-1))`. The auxiliary set `N0 b d` collects the
functionals vanishing on the escape block; it is the set on which the support number of a
filter containing all the generators is finite.
-/

/-- The cone `Q₀` of Section 5: the functionals whose first nonvanishing coordinate among the
first `m` is positive. -/
def Q0 {n : ℕ} (b : Basis (Fin n) ℝ V) (m : ℕ) : Set (V →L[ℝ] ℝ) :=
  {u | ∃ j, j < m ∧ 0 < u (basisAt b j) ∧ ∀ i, i < j → u (basisAt b i) = 0}

/-- The subspace `M₀` of Section 5: the functionals with no nonvanishing coordinate among the
first `m`. -/
def M0 {n : ℕ} (b : Basis (Fin n) ℝ V) (m : ℕ) : Set (V →L[ℝ] ℝ) :=
  {u | ∀ i, i < m → u (basisAt b i) = 0}

/-- The subspace `N₀` of Section 5: the functionals with no nonvanishing coordinate among the
first `d`. -/
def N0 {n : ℕ} (b : Basis (Fin n) ℝ V) (d : ℕ) : Set (V →L[ℝ] ℝ) :=
  {u | ∀ i, i < d → u (basisAt b i) = 0}

/-- The flat `A₀ = a + span (b 0, …, b (d-1))`, described by the vanishing of the coordinates
of index at least `d`. -/
def A0 {n : ℕ} (b : Basis (Fin n) ℝ V) (a : V) (d : ℕ) : Set V :=
  {x | ∀ j, d ≤ j → coordAt b a j x = 0}

/-- The sum of the absolute values of the first `m` coordinates of a functional. -/
noncomputable def coefAbsSum {n : ℕ} (b : Basis (Fin n) ℝ V) (m : ℕ) (u : V →L[ℝ] ℝ) : ℝ :=
  ∑ i ∈ Finset.range m, |u (basisAt b i)|

section Estimates

variable {n : ℕ} {b : Basis (Fin n) ℝ V} {a : V} {d m : ℕ} {K M c : ℝ} {u : V →L[ℝ] ℝ}

omit [FiniteDimensional ℝ V]

theorem coefAbsSum_nonneg : 0 ≤ coefAbsSum b m u :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- The value of a functional at a point of a generator, in coordinates: the killed block
contributes nothing. -/
theorem gen_apply_eq (hmn : m ≤ n) {x : V} (hx : x ∈ gen b a d m K M c) (u : V →L[ℝ] ℝ) :
    u x = u a + ∑ i ∈ Finset.range m, u (basisAt b i) * coordAt b a i x := by
  rw [apply_eq_sum_coordAt b a u x]
  congr 1
  refine (Finset.sum_subset (s₁ := Finset.range m) (s₂ := Finset.range n)
    (fun i hi => Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hi) hmn)) ?_).symm
  intro i _ hnot
  rw [gen_killed hx i (by simpa using hnot), mul_zero]

/-- A crude bound for a partial sum of coordinates against a uniform bound on them. -/
theorem abs_sum_coord_le {s : Finset ℕ} (hs : s ⊆ Finset.range m) (u : V →L[ℝ] ℝ) {B : ℝ}
    (hB : 0 ≤ B) {x : V} (hbd : ∀ i ∈ s, |coordAt b a i x| ≤ B) :
    |∑ i ∈ s, u (basisAt b i) * coordAt b a i x| ≤ coefAbsSum b m u * B := by
  calc |∑ i ∈ s, u (basisAt b i) * coordAt b a i x|
      ≤ ∑ i ∈ s, |u (basisAt b i) * coordAt b a i x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, |u (basisAt b i)| * B := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hbd i hi) (abs_nonneg _)
    _ = (∑ i ∈ s, |u (basisAt b i)|) * B := by rw [Finset.sum_mul]
    _ ≤ coefAbsSum b m u * B :=
        mul_le_mul_of_nonneg_right
          (Finset.sum_le_sum_of_subset_of_nonneg hs fun i _ _ => abs_nonneg _) hB

/-- Splitting off the first nonvanishing coordinate. -/
theorem sum_split_at (u : V →L[ℝ] ℝ) {k : ℕ} (hk : k < m)
    (hzero : ∀ i, i < k → u (basisAt b i) = 0) (x : V) :
    ∑ i ∈ Finset.range m, u (basisAt b i) * coordAt b a i x
      = u (basisAt b k) * coordAt b a k x
        + ∑ i ∈ Finset.Ico (k + 1) m, u (basisAt b i) * coordAt b a i x := by
  have h1 := Finset.sum_range_add_sum_Ico
    (fun i => u (basisAt b i) * coordAt b a i x) (show k + 1 ≤ m by omega)
  have hz : ∑ i ∈ Finset.range k, u (basisAt b i) * coordAt b a i x = 0 :=
    Finset.sum_eq_zero fun i hi => by rw [hzero i (Finset.mem_range.1 hi), zero_mul]
  rw [← h1, Finset.sum_range_succ, hz, zero_add]

/-- Discarding the vanishing coordinates before the first nonvanishing one. -/
theorem sum_split_from (u : V →L[ℝ] ℝ) {k : ℕ} (hk : k ≤ m)
    (hzero : ∀ i, i < k → u (basisAt b i) = 0) (x : V) :
    ∑ i ∈ Finset.range m, u (basisAt b i) * coordAt b a i x
      = ∑ i ∈ Finset.Ico k m, u (basisAt b i) * coordAt b a i x := by
  have h1 := Finset.sum_range_add_sum_Ico
    (fun i => u (basisAt b i) * coordAt b a i x) hk
  have hz : ∑ i ∈ Finset.range k, u (basisAt b i) * coordAt b a i x = 0 :=
    Finset.sum_eq_zero fun i hi => by rw [hzero i (Finset.mem_range.1 hi), zero_mul]
  rw [← h1, hz, zero_add]

/-- A functional of `M₀` is constant on every generator. -/
theorem gen_subset_hyperplane (hmn : m ≤ n) (hu : u ∈ M0 b m) :
    gen b a d m K M c ⊆ hyperplane u (u a) := by
  intro x hx
  have hux := gen_apply_eq hmn hx u
  have hz : ∑ i ∈ Finset.range m, u (basisAt b i) * coordAt b a i x = 0 :=
    Finset.sum_eq_zero fun i hi => by rw [hu i (Finset.mem_range.1 hi), zero_mul]
  show u x = u a
  rw [hux, hz, add_zero]

/-- Escape case: for every level `t` some generator lies in the half-space `{u ≥ t}`. -/
theorem exists_gen_subset_halfGE (hd : 1 ≤ d) (hdm : d ≤ m) (hmn : m ≤ n) {k : ℕ}
    (hkd : k < d) (hpos : 0 < u (basisAt b k)) (hzero : ∀ i, i < k → u (basisAt b i) = 0)
    (t : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ gen b a d m (N : ℝ) (N : ℝ) (1 / (N : ℝ)) ⊆ halfGE u t := by
  classical
  set A : ℝ := u (basisAt b k) with hA
  set S : ℝ := coefAbsSum b m u with hS
  have hS0 : 0 ≤ S := coefAbsSum_nonneg
  obtain ⟨N, hN⟩ := exists_nat_ge (max 1 ((S + |t - u a|) / A))
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := le_trans (le_max_left _ _) hN
  have hNnat : 1 ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hAN : S + |t - u a| ≤ A * (N : ℝ) := by
    have h := le_trans (le_max_right _ _) hN
    have := mul_le_mul_of_nonneg_left h (le_of_lt hpos)
    calc S + |t - u a| = A * ((S + |t - u a|) / A) := by field_simp
      _ ≤ A * (N : ℝ) := this
  have habs : 0 ≤ |t - u a| := abs_nonneg _
  have hAS : S ≤ A * (N : ℝ) := by linarith
  have hta : t - u a ≤ A * (N : ℝ) - S := by
    have := le_abs_self (t - u a)
    linarith
  refine ⟨N, hNnat, ?_⟩
  intro x hx
  have hc : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  have hc1 : 1 / (N : ℝ) ≤ 1 := by
    rw [div_le_one hNpos]; exact hN1
  have hkm : k < m := lt_of_lt_of_le hkd hdm
  have hux := gen_apply_eq hmn hx u
  rw [sum_split_at u hkm hzero x] at hux
  -- the approach block contributes at most `S`
  have htail2 : ∀ (s : Finset ℕ), s ⊆ Finset.Ico d m →
      |∑ i ∈ s, u (basisAt b i) * coordAt b a i x| ≤ S := by
    intro s hs
    have hsub : s ⊆ Finset.range m := hs.trans (by
      intro i hi; exact Finset.mem_range.2 (Finset.mem_Ico.1 hi).2)
    have hbd : ∀ i ∈ s, |coordAt b a i x| ≤ 1 / (N : ℝ) := by
      intro i hi
      obtain ⟨hdi, him⟩ := Finset.mem_Ico.1 (hs hi)
      have hpos' := gen_pos_approach hN1 hx i hdi him
      have hle := gen_le_c hN1 hc1 hx i hdi him
      rw [abs_of_pos hpos']
      exact hle
    have := abs_sum_coord_le hsub u (le_of_lt hc) hbd
    calc |∑ i ∈ s, u (basisAt b i) * coordAt b a i x| ≤ S * (1 / (N : ℝ)) := this
      _ ≤ S * 1 := mul_le_mul_of_nonneg_left hc1 hS0
      _ = S := by ring
  show t ≤ u x
  by_cases hkd1 : k + 1 = d
  · -- `k` is the last escape index
    have hxk : (N : ℝ) ≤ coordAt b a k x := by
      have := gen_le_last hx
      have hk1 : k = d - 1 := by omega
      rwa [← hk1] at this
    have htail : |∑ i ∈ Finset.Ico (k + 1) m, u (basisAt b i) * coordAt b a i x| ≤ S := by
      refine htail2 _ ?_
      rw [hkd1]
    have h1 : A * (N : ℝ) ≤ A * coordAt b a k x :=
      mul_le_mul_of_nonneg_left hxk (le_of_lt hpos)
    have h2 := neg_abs_le (∑ i ∈ Finset.Ico (k + 1) m, u (basisAt b i) * coordAt b a i x)
    rw [hux]
    linarith
  · -- there is a further escape index
    have hk1d : k + 1 < d := by omega
    have hy : 0 < coordAt b a (k + 1) x := gen_pos_escape hd hN1 hN1 hx (k + 1) hk1d
    have hsplit := (Finset.sum_Ico_consecutive
      (fun i => u (basisAt b i) * coordAt b a i x) (show k + 1 ≤ d by omega) hdm).symm
    have hT1 : |∑ i ∈ Finset.Ico (k + 1) d, u (basisAt b i) * coordAt b a i x|
        ≤ S * coordAt b a (k + 1) x := by
      have hsub : Finset.Ico (k + 1) d ⊆ Finset.range m := by
        intro i hi
        exact Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_Ico.1 hi).2 hdm)
      refine abs_sum_coord_le hsub u (le_of_lt hy) ?_
      intro i hi
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hi
      have hposi := gen_pos_escape hd hN1 hN1 hx i h2
      rw [abs_of_pos hposi]
      exact gen_le_of_le_escape hd hN1 hN1 hx (k + 1) i h1 h2
    have hT2 : |∑ i ∈ Finset.Ico d m, u (basisAt b i) * coordAt b a i x| ≤ S :=
      htail2 _ (subset_refl _)
    have hstep := gen_step hx k hk1d
    have h1 : A * ((N : ℝ) * coordAt b a (k + 1) x + (N : ℝ)) ≤ A * coordAt b a k x :=
      mul_le_mul_of_nonneg_left hstep (le_of_lt hpos)
    have e1 := neg_abs_le (∑ i ∈ Finset.Ico (k + 1) d, u (basisAt b i) * coordAt b a i x)
    have e2 := neg_abs_le (∑ i ∈ Finset.Ico d m, u (basisAt b i) * coordAt b a i x)
    have hcoef : 0 ≤ (A * (N : ℝ) - S) * coordAt b a (k + 1) x := by
      have : 0 ≤ A * (N : ℝ) - S := by linarith
      positivity
    rw [hux, hsplit]
    nlinarith

/-- Approach case, first estimate: every generator with `c` small misses the half-space
`{u ≤ u a}`. -/
theorem gen_apply_gt (hmn : m ≤ n) {k : ℕ} (hdk : d ≤ k) (hkm : k < m)
    (hzero : ∀ i, i < k → u (basisAt b i) = 0)
    (hK : 1 ≤ K) (hc : 0 < c) (hc1 : c ≤ 1) (hcS : coefAbsSum b m u * c < u (basisAt b k))
    {x : V} (hx : x ∈ gen b a d m K M c) : u a < u x := by
  set A : ℝ := u (basisAt b k) with hA
  set S : ℝ := coefAbsSum b m u with hS
  have hS0 : 0 ≤ S := coefAbsSum_nonneg
  have hxk : 0 < coordAt b a k x := gen_pos_approach hK hx k hdk hkm
  have hux := gen_apply_eq hmn hx u
  rw [sum_split_at u hkm hzero x] at hux
  have hsub : Finset.Ico (k + 1) m ⊆ Finset.range m := by
    intro i hi
    exact Finset.mem_range.2 (Finset.mem_Ico.1 hi).2
  have hBnn : 0 ≤ c * coordAt b a k x := le_of_lt (mul_pos hc hxk)
  have htail : |∑ i ∈ Finset.Ico (k + 1) m, u (basisAt b i) * coordAt b a i x|
      ≤ S * (c * coordAt b a k x) := by
    refine abs_sum_coord_le hsub u hBnn ?_
    intro i hi
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hi
    have hposi := gen_pos_approach hK hx i (by omega) h2
    rw [abs_of_pos hposi]
    exact gen_le_c_mul hK hc1 hx k i hdk (by omega) h2
  have e1 := neg_abs_le (∑ i ∈ Finset.Ico (k + 1) m, u (basisAt b i) * coordAt b a i x)
  have hgap : 0 < (A - S * c) * coordAt b a k x :=
    mul_pos (by linarith) hxk
  rw [hux]
  nlinarith

/-- Approach case, second estimate: for every `ε > 0` some generator lies in the half-space
`{u ≤ u a + ε}`. -/
theorem exists_gen_subset_halfLE (hmn : m ≤ n) {k : ℕ}
    (hdk : d ≤ k) (hkm : k < m) (hzero : ∀ i, i < k → u (basisAt b i) = 0) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ N ∧ gen b a d m (N : ℝ) (N : ℝ) (1 / (N : ℝ)) ⊆ halfLE u (u a + ε) := by
  classical
  set S : ℝ := coefAbsSum b m u with hS
  have hS0 : 0 ≤ S := coefAbsSum_nonneg
  obtain ⟨N, hN⟩ := exists_nat_ge (max 1 (S / ε))
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := le_trans (le_max_left _ _) hN
  have hNnat : 1 ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hSN : S ≤ ε * (N : ℝ) := by
    have h := le_trans (le_max_right _ _) hN
    rw [div_le_iff₀ hε] at h
    linarith [h]
  refine ⟨N, hNnat, ?_⟩
  intro x hx
  have hc : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  have hc1 : 1 / (N : ℝ) ≤ 1 := by rw [div_le_one hNpos]; exact hN1
  have hux := gen_apply_eq hmn hx u
  rw [sum_split_from u (le_of_lt hkm) hzero x] at hux
  have hsub : Finset.Ico k m ⊆ Finset.range m := by
    intro i hi
    exact Finset.mem_range.2 (Finset.mem_Ico.1 hi).2
  have htail : |∑ i ∈ Finset.Ico k m, u (basisAt b i) * coordAt b a i x|
      ≤ S * (1 / (N : ℝ)) := by
    refine abs_sum_coord_le hsub u (le_of_lt hc) ?_
    intro i hi
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hi
    have hposi := gen_pos_approach hN1 hx i (by omega) h2
    rw [abs_of_pos hposi]
    exact gen_le_c hN1 hc1 hx i (by omega) h2
  have e1 := le_abs_self (∑ i ∈ Finset.Ico k m, u (basisAt b i) * coordAt b a i x)
  have hfin : S * (1 / (N : ℝ)) ≤ ε := by
    rw [mul_one_div, div_le_iff₀ hNpos]
    linarith
  show u x ≤ u a + ε
  rw [hux]
  linarith

end Estimates

section Forcing

variable {n : ℕ} {b : Basis (Fin n) ℝ V} {a : V} {d m : ℕ} {F : ConvexFilter V}
  {u : V →L[ℝ] ℝ}

omit [FiniteDimensional ℝ V]

/-- The dual splits into `M0`, `Q0` and `-Q0`, according to the sign of the first
nonvanishing coordinate among the first `m`. -/
theorem mem_M0_or_Q0_or_neg_Q0 (u : V →L[ℝ] ℝ) :
    u ∈ M0 b m ∨ u ∈ Q0 b m ∨ -u ∈ Q0 b m := by
  classical
  by_cases h : ∃ i, i < m ∧ u (basisAt b i) ≠ 0
  · obtain ⟨hkm, hkne⟩ := Nat.find_spec h
    set k := Nat.find h with hk
    have hmin : ∀ i, i < k → u (basisAt b i) = 0 := by
      intro i hi
      have hni := Nat.find_min h (m := i) (by omega)
      push_neg at hni
      exact hni (by omega)
    rcases lt_trichotomy (u (basisAt b k)) 0 with hneg | hzero | hpos
    · refine Or.inr (Or.inr ⟨k, hkm, ?_, fun i hi => ?_⟩)
      · simpa using hneg
      · simp [hmin i hi]
    · exact absurd hzero hkne
    · exact Or.inr (Or.inl ⟨k, hkm, hpos, hmin⟩)
  · push_neg at h
    exact Or.inl fun i hi => h i hi

/-- A functional of `Q0` has its witness at the first nonvanishing coordinate. -/
theorem Q0_witness_le {j : ℕ} (hj : ∀ i, i < j → u (basisAt b i) = 0) {i : ℕ}
    (hi : u (basisAt b i) ≠ 0) : j ≤ i := by
  by_contra hcon
  exact hi (hj i (by omega))

/-! ### The filter-level consequences -/

/-- A generator is a member of the filter, so any closed convex superset of one is. -/
theorem mem_carrier_of_gen_subset
    (hgen : ∀ k : ℕ, 1 ≤ k → gen b a d m (k : ℝ) (k : ℝ) (1 / (k : ℝ)) ∈ F.carrier)
    {N : ℕ} (hN : 1 ≤ N) {C : Set V} (hC : IsClosed C) (hCc : Convex ℝ C)
    (hsub : gen b a d m (N : ℝ) (N : ℝ) (1 / (N : ℝ)) ⊆ C) : C ∈ F.carrier :=
  F.mem_of_superset (hgen N hN) hC hCc hsub

/-- Case `u ∈ M0`: the hyperplane `{u = u a}` belongs to the filter. -/
theorem hyperplane_mem_of_M0 (hmn : m ≤ n)
    (hgen : ∀ k : ℕ, 1 ≤ k → gen b a d m (k : ℝ) (k : ℝ) (1 / (k : ℝ)) ∈ F.carrier)
    (hu : u ∈ M0 b m) : hyperplane u (u a) ∈ F.carrier :=
  mem_carrier_of_gen_subset hgen le_rfl (isClosed_hyperplane u _) (convex_hyperplane u _)
    (gen_subset_hyperplane hmn hu)

theorem mem_Mset_of_M0 (hmn : m ≤ n)
    (hgen : ∀ k : ℕ, 1 ≤ k → gen b a d m (k : ℝ) (k : ℝ) (1 / (k : ℝ)) ∈ F.carrier)
    (hu : u ∈ M0 b m) : u ∈ Mset F :=
  ⟨u a, hyperplane_mem_of_M0 hmn hgen hu⟩

theorem sig_eq_of_M0 (hmn : m ≤ n)
    (hgen : ∀ k : ℕ, 1 ≤ k → gen b a d m (k : ℝ) (k : ℝ) (1 / (k : ℝ)) ∈ F.carrier)
    (hu : u ∈ M0 b m) : sig F u = u a :=
  sig_eq_of_hyperplane_mem (hyperplane_mem_of_M0 hmn hgen hu)

/-- Escape case: the level set of `u` is empty, i.e. the support value is `+∞`. -/
theorem lev_eq_empty_of_escape (hd : 1 ≤ d) (hdm : d ≤ m) (hmn : m ≤ n)
    (hgen : ∀ k : ℕ, 1 ≤ k → gen b a d m (k : ℝ) (k : ℝ) (1 / (k : ℝ)) ∈ F.carrier)
    {k : ℕ} (hkd : k < d) (hpos : 0 < u (basisAt b k))
    (hzero : ∀ i, i < k → u (basisAt b i) = 0) : lev F u = ∅ := by
  ext t
  simp only [Set.mem_empty_iff_false, iff_false]
  intro ht
  obtain ⟨N, hN, hsub⟩ := exists_gen_subset_halfGE hd hdm hmn hkd hpos hzero (t + 1)
  have hGE : halfGE u (t + 1) ∈ F.carrier :=
    mem_carrier_of_gen_subset hgen hN (isClosed_halfGE u _) (convex_halfGE u _) hsub
  have hinter := F.inter_mem ht hGE
  rw [disjoint_halfLE_halfGE (by linarith) u] at hinter
  exact F.empty_not_mem hinter

/-- Approach case: a generator on which `u` is everywhere `> u a`. -/
theorem exists_gen_apply_gt (hmn : m ≤ n) {k : ℕ} (hdk : d ≤ k) (hkm : k < m)
    (hpos : 0 < u (basisAt b k)) (hzero : ∀ i, i < k → u (basisAt b i) = 0) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ x ∈ gen b a d m (N : ℝ) (N : ℝ) (1 / (N : ℝ)), u a < u x := by
  classical
  set S : ℝ := coefAbsSum b m u with hS
  set A : ℝ := u (basisAt b k) with hA
  have hS0 : 0 ≤ S := coefAbsSum_nonneg
  obtain ⟨N, hN⟩ := exists_nat_ge (max 1 ((S + 1) / A))
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := le_trans (le_max_left _ _) hN
  have hNnat : 1 ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hSA : S + 1 ≤ A * (N : ℝ) := by
    have h := le_trans (le_max_right _ _) hN
    have h2 := mul_le_mul_of_nonneg_left h (le_of_lt hpos)
    calc S + 1 = A * ((S + 1) / A) := by field_simp
      _ ≤ A * (N : ℝ) := h2
  have hc : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  have hc1 : 1 / (N : ℝ) ≤ 1 := by rw [div_le_one hNpos]; exact hN1
  have hSc : S * (1 / (N : ℝ)) < A := by
    rw [mul_one_div, div_lt_iff₀ hNpos]
    linarith
  exact ⟨N, hNnat, fun x hx => gen_apply_gt hmn hdk hkm hzero hN1 hc hc1 hSc hx⟩

/-- Approach case: the half-space `{u ≤ u a}` does not belong to the filter. -/
theorem halfLE_not_mem_of_approach (hmn : m ≤ n)
    (hgen : ∀ k : ℕ, 1 ≤ k → gen b a d m (k : ℝ) (k : ℝ) (1 / (k : ℝ)) ∈ F.carrier)
    {k : ℕ} (hdk : d ≤ k) (hkm : k < m) (hpos : 0 < u (basisAt b k))
    (hzero : ∀ i, i < k → u (basisAt b i) = 0) : halfLE u (u a) ∉ F.carrier := by
  intro hmem
  obtain ⟨N, hN, hgt⟩ := exists_gen_apply_gt hmn hdk hkm hpos hzero
  have hdisj : gen b a d m (N : ℝ) (N : ℝ) (1 / (N : ℝ)) ∩ halfLE u (u a) = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hx hxle
    exact absurd (hgt x hx) (not_lt.2 hxle)
  have hinter := F.inter_mem (hgen N hN) hmem
  rw [hdisj] at hinter
  exact F.empty_not_mem hinter

/-- Approach case: `-(u a)` is a level of `-u`. -/
theorem neg_mem_lev_of_approach (hmn : m ≤ n)
    (hgen : ∀ k : ℕ, 1 ≤ k → gen b a d m (k : ℝ) (k : ℝ) (1 / (k : ℝ)) ∈ F.carrier)
    {k : ℕ} (hdk : d ≤ k) (hkm : k < m) (hpos : 0 < u (basisAt b k))
    (hzero : ∀ i, i < k → u (basisAt b i) = 0) : -(u a) ∈ lev F (-u) := by
  obtain ⟨N, hN, hgt⟩ := exists_gen_apply_gt hmn hdk hkm hpos hzero
  refine mem_carrier_of_gen_subset hgen hN (isClosed_halfLE _ _) (convex_halfLE _ _) ?_
  intro x hx
  have := hgt x hx
  show (-u) x ≤ -(u a)
  simp only [ContinuousLinearMap.neg_apply]
  linarith

/-- Approach case: every level above `u a` is attained. -/
theorem mem_lev_of_approach (hmn : m ≤ n)
    (hgen : ∀ k : ℕ, 1 ≤ k → gen b a d m (k : ℝ) (k : ℝ) (1 / (k : ℝ)) ∈ F.carrier)
    {k : ℕ} (hdk : d ≤ k) (hkm : k < m) (hzero : ∀ i, i < k → u (basisAt b i) = 0)
    {ε : ℝ} (hε : 0 < ε) : u a + ε ∈ lev F u := by
  obtain ⟨N, hN, hsub⟩ := exists_gen_subset_halfLE hmn hdk hkm hzero hε
  exact mem_carrier_of_gen_subset hgen hN (isClosed_halfLE _ _) (convex_halfLE _ _) hsub

/-- Approach case: every level of `u` is `> u a`. -/
theorem lt_of_mem_lev_of_approach (hmn : m ≤ n)
    (hgen : ∀ k : ℕ, 1 ≤ k → gen b a d m (k : ℝ) (k : ℝ) (1 / (k : ℝ)) ∈ F.carrier)
    {k : ℕ} (hdk : d ≤ k) (hkm : k < m) (hpos : 0 < u (basisAt b k))
    (hzero : ∀ i, i < k → u (basisAt b i) = 0) {t : ℝ} (ht : t ∈ lev F u) : u a < t := by
  by_contra hcon
  push_neg at hcon
  have : halfLE u (u a) ∈ F.carrier :=
    F.mem_of_superset ht (isClosed_halfLE _ _) (convex_halfLE _ _)
      (fun x hx => le_trans hx hcon)
  exact halfLE_not_mem_of_approach hmn hgen hdk hkm hpos hzero this

/-- Approach case: `u` has finite support number `u a`, and lies in the positivity cone. -/
theorem approach_invariants (hF : IsMaximal F) (hmn : m ≤ n)
    (hgen : ∀ k : ℕ, 1 ≤ k → gen b a d m (k : ℝ) (k : ℝ) (1 / (k : ℝ)) ∈ F.carrier)
    {k : ℕ} (hdk : d ≤ k) (hkm : k < m) (hpos : 0 < u (basisAt b k))
    (hzero : ∀ i, i < k → u (basisAt b i) = 0) :
    u ∈ Nset F ∧ sig F u = u a ∧ u ∈ Qset F := by
  have hup : ∀ ε : ℝ, 0 < ε → u a + ε ∈ lev F u := fun ε hε =>
    mem_lev_of_approach hmn hgen hdk hkm hzero hε
  have hlow : ∀ t ∈ lev F u, u a < t := fun t ht =>
    lt_of_mem_lev_of_approach hmn hgen hdk hkm hpos hzero ht
  have hne : (lev F u).Nonempty := ⟨u a + 1, hup 1 one_pos⟩
  have hnu : lev F (-u) ≠ ∅ :=
    Set.nonempty_iff_ne_empty.1 ⟨-(u a), neg_mem_lev_of_approach hmn hgen hdk hkm hpos hzero⟩
  have hN : u ∈ Nset F := ⟨Set.nonempty_iff_ne_empty.1 hne, hnu⟩
  refine ⟨hN, ?_, ?_⟩
  · refine le_antisymm ?_ ?_
    · refine le_of_forall_gt_imp_ge_of_dense fun r hr => ?_
      have : u a + (r - u a) ∈ lev F u := hup _ (by linarith)
      have hle := sig_le_of_mem_lev hF hN this
      linarith
    · exact le_csInf hne fun t ht => le_of_lt (hlow t ht)
  · refine ⟨?_, ?_⟩
    · intro hcon
      have : u a ∈ lev F u := by rw [hcon]; trivial
      exact absurd (hlow _ this) (lt_irrefl _)
    · intro t ht
      have hgt := hlow t ht
      refine ⟨u a + (t - u a) / 2, hup _ (by linarith), by linarith⟩

/-- `Q0` is contained in the positivity cone of the filter. -/
theorem Q0_subset_Qset (hF : IsMaximal F) (hd : 1 ≤ d) (hdm : d ≤ m) (hmn : m ≤ n)
    (hgen : ∀ k : ℕ, 1 ≤ k → gen b a d m (k : ℝ) (k : ℝ) (1 / (k : ℝ)) ∈ F.carrier) :
    Q0 b m ⊆ Qset F := by
  rintro u ⟨j, hjm, hpos, hzero⟩
  rcases Nat.lt_or_ge j d with hjd | hjd
  · have hlev := lev_eq_empty_of_escape hd hdm hmn hgen hjd hpos hzero
    exact Eset_subset_Qset hF hlev
  · exact (approach_invariants hF hmn hgen hjd hjm hpos hzero).2.2

/-- Functionals vanishing on the escape block have finite support number `u a`. -/
theorem N0_invariants (hF : IsMaximal F) (hmn : m ≤ n)
    (hgen : ∀ k : ℕ, 1 ≤ k → gen b a d m (k : ℝ) (k : ℝ) (1 / (k : ℝ)) ∈ F.carrier)
    (hu : u ∈ N0 b d) : u ∈ Nset F ∧ sig F u = u a := by
  rcases mem_M0_or_Q0_or_neg_Q0 (b := b) (m := m) u with hM | hQ | hQ
  · exact ⟨Mset_subset_Nset hF (mem_Mset_of_M0 hmn hgen hM), sig_eq_of_M0 hmn hgen hM⟩
  · obtain ⟨j, hjm, hpos, hzero⟩ := hQ
    have hjd : d ≤ j := by
      by_contra hcon
      push_neg at hcon
      exact absurd (hu j hcon) (ne_of_gt hpos)
    obtain ⟨h1, h2, -⟩ := approach_invariants hF hmn hgen hjd hjm hpos hzero
    exact ⟨h1, h2⟩
  · obtain ⟨j, hjm, hpos, hzero⟩ := hQ
    have hjd : d ≤ j := by
      by_contra hcon
      push_neg at hcon
      have : (-u) (basisAt b j) = 0 := by simp [hu j hcon]
      exact absurd this (ne_of_gt hpos)
    obtain ⟨h1, h2, -⟩ := approach_invariants hF hmn hgen hjd hjm hpos hzero
    have hN : u ∈ Nset F := by
      have := Nset_neg h1
      rwa [neg_neg] at this
    refine ⟨hN, ?_⟩
    have hsig := sig_neg hF hN
    have : (-u) a = -(u a) := by simp
    rw [this] at h2
    linarith [hsig, h2]

/-- Functionals not vanishing on the escape block have infinite support number. -/
theorem not_mem_Nset_of_not_N0 (hd : 1 ≤ d) (hdm : d ≤ m) (hmn : m ≤ n)
    (hgen : ∀ k : ℕ, 1 ≤ k → gen b a d m (k : ℝ) (k : ℝ) (1 / (k : ℝ)) ∈ F.carrier)
    (hu : u ∉ N0 b d) : u ∉ Nset F := by
  have hex : ∃ i, i < d ∧ u (basisAt b i) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hu fun i hi => hcon i hi
  obtain ⟨i0, hi0d, hi0⟩ := hex
  rcases mem_M0_or_Q0_or_neg_Q0 (b := b) (m := m) u with hM | hQ | hQ
  · exact absurd (hM i0 (by omega)) hi0
  · obtain ⟨j, hjm, hpos, hzero⟩ := hQ
    have hjd : j < d := lt_of_le_of_lt (Q0_witness_le hzero hi0) hi0d
    intro hN
    exact hN.1 (lev_eq_empty_of_escape hd hdm hmn hgen hjd hpos hzero)
  · obtain ⟨j, hjm, hpos, hzero⟩ := hQ
    have hi0' : (-u) (basisAt b i0) ≠ 0 := by simpa using hi0
    have hjd : j < d := lt_of_le_of_lt (Q0_witness_le hzero hi0') hi0d
    intro hN
    exact hN.2 (lev_eq_empty_of_escape hd hdm hmn hgen hjd hpos hzero)

/-- The set on which the support number of `F` is finite is `N0`. -/
theorem Nset_eq_N0 (hF : IsMaximal F) (hd : 1 ≤ d) (hdm : d ≤ m) (hmn : m ≤ n)
    (hgen : ∀ k : ℕ, 1 ≤ k → gen b a d m (k : ℝ) (k : ℝ) (1 / (k : ℝ)) ∈ F.carrier) :
    Nset F = N0 b d := by
  ext w
  constructor
  · intro hw
    by_contra hcon
    exact not_mem_Nset_of_not_N0 hd hdm hmn hgen hcon hw
  · intro hw
    exact (N0_invariants hF hmn hgen hw).1

/-! ### The three contract theorems -/

theorem forcing_Mset (hF : IsMaximal F) (hd : 1 ≤ d) (hdm : d ≤ m) (hmn : m ≤ n)
    (hgen : ∀ k : ℕ, 1 ≤ k → gen b a d m (k : ℝ) (k : ℝ) (1 / (k : ℝ)) ∈ F.carrier) :
    Mset F = M0 b m := by
  ext w
  constructor
  · intro hw
    rcases mem_M0_or_Q0_or_neg_Q0 (b := b) (m := m) w with hM | hQ | hQ
    · exact hM
    · exact absurd (Q0_subset_Qset hF hd hdm hmn hgen hQ) (Mset_disjoint_Qset hF hw)
    · exact absurd (Q0_subset_Qset hF hd hdm hmn hgen hQ)
        (Mset_disjoint_Qset hF (Mset_neg hw))
  · intro hw
    exact mem_Mset_of_M0 hmn hgen hw

theorem forcing_Qset (hF : IsMaximal F) (hd : 1 ≤ d) (hdm : d ≤ m) (hmn : m ≤ n)
    (hgen : ∀ k : ℕ, 1 ≤ k → gen b a d m (k : ℝ) (k : ℝ) (1 / (k : ℝ)) ∈ F.carrier) :
    Qset F = Q0 b m := by
  ext w
  constructor
  · intro hw
    rcases mem_M0_or_Q0_or_neg_Q0 (b := b) (m := m) w with hM | hQ | hQ
    · exact absurd hw (Mset_disjoint_Qset hF (mem_Mset_of_M0 hmn hgen hM))
    · exact hQ
    · exact absurd (Q0_subset_Qset hF hd hdm hmn hgen hQ) (Qset_not_neg hF hw)
  · exact fun hw => Q0_subset_Qset hF hd hdm hmn hgen hw

end Forcing

section ForcingAset

variable {n : ℕ} {b : Basis (Fin n) ℝ V} {a : V} {d m : ℕ} {F : ConvexFilter V}

/-- The `j`-th dual basis functional vanishes on the escape block when `d ≤ j`. -/
theorem coordCLM_mem_N0 {j : ℕ} (hj : d ≤ j) (hjn : j < n) :
    coordCLM b ⟨j, hjn⟩ ∈ N0 b d := by
  intro i hi
  have hin : i < n := by omega
  rw [basisAt_of_lt b hin]
  have hne : (⟨j, hjn⟩ : Fin n) ≠ ⟨i, hin⟩ := by
    simp only [ne_eq, Fin.mk.injEq]
    omega
  simp [coordCLM_apply, Basis.coord_apply, Basis.repr_self, hne]

theorem forcing_Aset (hF : IsMaximal F) (hd : 1 ≤ d) (hdm : d ≤ m) (hmn : m ≤ n)
    (hgen : ∀ k : ℕ, 1 ≤ k → gen b a d m (k : ℝ) (k : ℝ) (1 / (k : ℝ)) ∈ F.carrier) :
    Aset F = A0 b a d := by
  have hNset := Nset_eq_N0 hF hd hdm hmn hgen
  ext x
  constructor
  · intro hx j hj
    by_cases hjn : j < n
    · set w : V →L[ℝ] ℝ := coordCLM b ⟨j, hjn⟩ with hw
      have hwN : w ∈ Nset F := by
        rw [hNset]
        exact coordCLM_mem_N0 hj hjn
      have hsig : sig F w = w a := (N0_invariants hF hmn hgen (hNset ▸ hwN)).2
      have hxa : w x = sig F w := hx w hwN
      rw [coordAt_eq_sub b a hjn x, hxa, hsig]
      simp [hw, Basis.coord_apply]
    · exact coordAt_of_le (by omega) x
  · intro hx w hw
    have hwN0 : w ∈ N0 b d := hNset ▸ hw
    have hsig : sig F w = w a := (N0_invariants hF hmn hgen hwN0).2
    rw [hsig, apply_eq_sum_coordAt b a w x]
    have hz : ∑ i ∈ Finset.range n, w (basisAt b i) * coordAt b a i x = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rcases Nat.lt_or_ge i d with hid | hid
      · rw [hwN0 i hid, zero_mul]
      · rw [hx i hid, mul_zero]
    rw [hz, add_zero]

end ForcingAset

/-! ## Part E — existence -/

section Existence

variable {n : ℕ}

/-- For all `1 ≤ d ≤ m ≤ n`, every basis and every base point, there is a maximal convex
filter with the invariants `A0`, `Q0` and `M0` of Section 5. -/
theorem exists_maximal_realizing (b : Basis (Fin n) ℝ V) (a : V) {d m : ℕ}
    (hd : 1 ≤ d) (hdm : d ≤ m) (hmn : m ≤ n) :
    ∃ F : ConvexFilter V, IsMaximal F ∧
      Aset F = A0 b a d ∧ Qset F = Q0 b m ∧ Mset F = M0 b m := by
  classical
  have hone : ∀ k : ℕ, (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    intro k
    have : (1 : ℕ) ≤ k + 1 := by omega
    exact_mod_cast this
  have hcpos : ∀ k : ℕ, (0 : ℝ) < 1 / ((k + 1 : ℕ) : ℝ) := by
    intro k
    have := hone k
    positivity
  have hcle : ∀ k : ℕ, 1 / ((k + 1 : ℕ) : ℝ) ≤ 1 := by
    intro k
    rw [div_le_one (by linarith [hone k])]
    exact hone k
  set B : ℕ → Set V :=
    fun k => gen b a d m ((k + 1 : ℕ) : ℝ) ((k + 1 : ℕ) : ℝ) (1 / ((k + 1 : ℕ) : ℝ)) with hB
  have hne : ∀ k, (B k).Nonempty := fun k =>
    gen_nonempty b a hd hdm hmn (hone k) (hcpos k) (hcle k)
  have hanti : Antitone B := by
    intro k l hkl
    have hKK : ((k + 1 : ℕ) : ℝ) ≤ ((l + 1 : ℕ) : ℝ) := by
      have : k + 1 ≤ l + 1 := by omega
      exact_mod_cast this
    have hcc : 1 / ((l + 1 : ℕ) : ℝ) ≤ 1 / ((k + 1 : ℕ) : ℝ) :=
      one_div_le_one_div_of_le (by linarith [hone k]) hKK
    exact gen_mono hd (hone l) (hone l) hKK hKK hcc
  set F0 : ConvexFilter V := ofAntitoneBase B hne hanti with hF0
  obtain ⟨G, hFG, hGmax⟩ := exists_isMaximal_extension F0
  have hgen : ∀ k : ℕ, 1 ≤ k →
      gen b a d m (k : ℝ) (k : ℝ) (1 / (k : ℝ)) ∈ G.carrier := by
    intro k hk
    have hbase : B (k - 1) ∈ F0.carrier :=
      base_mem_ofAntitoneBase isClosed_gen (gen_convex hd (hone _) (hone _))
    have hkk : ((k - 1 : ℕ) + 1 : ℕ) = k := by omega
    rw [hB] at hbase
    simp only [hkk] at hbase
    exact hFG hbase
  exact ⟨G, hGmax, forcing_Aset hGmax hd hdm hmn hgen, forcing_Qset hGmax hd hdm hmn hgen,
    forcing_Mset hGmax hd hdm hmn hgen⟩

end Existence

end ConvexFilter
