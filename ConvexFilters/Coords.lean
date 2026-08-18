import ConvexFilters.Defs

/-!
# Natural-number-indexed coordinates relative to a basis and a base point

Section 5 of the paper is written in coordinates: a basis `f₁, …, f_n` of `V`, a base point
`a ∈ V`, and the coordinates `xᵢ = uⁱ (x - a)` of a point `x`. The constraints cutting out the
generating family relate coordinates of neighbouring indices, and shifting indices inside
`Fin n` is unpleasant. This file therefore packages the coordinates as functions of a natural
number index, junk (namely `0`) outside the range:

* `coordAt b a i x` — the `i`-th coordinate of `x - a`, or `0` when `n ≤ i`;
* `basisAt b i` — the `i`-th basis vector, or `0` when `n ≤ i`;
* `coordCLM b i` — the `i`-th dual basis functional as a continuous linear map.

Besides the evaluation lemmas, the file records what the later parts consume: that `coordAt`
behaves affinely under convex combinations (`coordAt_combo`), that it is continuous, that each
of the constraint sets `{coordAt ≤ t}`, `{t ≤ coordAt}`, `{coordAt = t}` is closed and convex,
that a point is `a` exactly when all its coordinates vanish, and that a functional is its value
at the base point plus the corresponding combination of coordinates
(`apply_eq_sum_coordAt`).
-/

open Module

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

namespace ConvexFilter

/-- The `i`-th dual basis functional of `b`, as a continuous linear map. -/
noncomputable def coordCLM {n : ℕ} (b : Basis (Fin n) ℝ V) (i : Fin n) : V →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (b.coord i)

@[simp] theorem coordCLM_apply {n : ℕ} (b : Basis (Fin n) ℝ V) (i : Fin n) (x : V) :
    coordCLM b i x = b.coord i x := rfl

/-- The `i`-th vector of the basis `b`, with junk value `0` for `n ≤ i`. -/
noncomputable def basisAt {n : ℕ} (b : Basis (Fin n) ℝ V) (i : ℕ) : V :=
  if h : i < n then b ⟨i, h⟩ else 0

omit [FiniteDimensional ℝ V] in
theorem basisAt_of_lt {n : ℕ} (b : Basis (Fin n) ℝ V) {i : ℕ} (h : i < n) :
    basisAt b i = b ⟨i, h⟩ := dif_pos h

omit [FiniteDimensional ℝ V] in
@[simp] theorem basisAt_coe {n : ℕ} (b : Basis (Fin n) ℝ V) (i : Fin n) :
    basisAt b (i : ℕ) = b i := by
  rw [basisAt_of_lt b i.2]

omit [FiniteDimensional ℝ V] in
theorem basisAt_of_le {n : ℕ} (b : Basis (Fin n) ℝ V) {i : ℕ} (h : n ≤ i) :
    basisAt b i = 0 := dif_neg (Nat.not_lt.2 h)

/-- The `i`-th coordinate of `x` relative to the basis `b` and the base point `a`, with junk
value `0` for `n ≤ i`. -/
noncomputable def coordAt {n : ℕ} (b : Basis (Fin n) ℝ V) (a : V) (i : ℕ) (x : V) : ℝ :=
  if h : i < n then b.coord ⟨i, h⟩ (x - a) else 0

omit [FiniteDimensional ℝ V] in
theorem coordAt_of_lt {n : ℕ} {b : Basis (Fin n) ℝ V} {a : V} {i : ℕ} (h : i < n) (x : V) :
    coordAt b a i x = b.coord ⟨i, h⟩ (x - a) := dif_pos h

omit [FiniteDimensional ℝ V] in
theorem coordAt_of_le {n : ℕ} {b : Basis (Fin n) ℝ V} {a : V} {i : ℕ} (h : n ≤ i) (x : V) :
    coordAt b a i x = 0 := dif_neg (Nat.not_lt.2 h)

omit [FiniteDimensional ℝ V] in
@[simp] theorem coordAt_base {n : ℕ} (b : Basis (Fin n) ℝ V) (a : V) (i : ℕ) :
    coordAt b a i a = 0 := by
  unfold coordAt; split <;> simp

/-- `coordAt b a i` is the difference of two continuous linear evaluations, hence affine. -/
theorem coordAt_eq_sub {n : ℕ} (b : Basis (Fin n) ℝ V) (a : V) {i : ℕ} (h : i < n) (x : V) :
    coordAt b a i x = coordCLM b ⟨i, h⟩ x - coordCLM b ⟨i, h⟩ a := by
  rw [coordAt_of_lt h]
  simp [map_sub]

omit [FiniteDimensional ℝ V] in
/-- `coordAt b a i` respects convex combinations. -/
theorem coordAt_combo {n : ℕ} (b : Basis (Fin n) ℝ V) (a : V) (i : ℕ) {s t : ℝ}
    (hst : s + t = 1) (x y : V) :
    coordAt b a i (s • x + t • y) = s * coordAt b a i x + t * coordAt b a i y := by
  unfold coordAt
  split
  · next h =>
      have hsub : s • x + t • y - a = s • (x - a) + t • (y - a) := by
        rw [smul_sub, smul_sub]
        rw [show s • x - s • a + (t • y - t • a) = s • x + t • y - (s • a + t • a) by abel]
        rw [← add_smul, hst, one_smul]
      rw [hsub, map_add, map_smul, map_smul]
      simp
  · ring

theorem continuous_coordAt {n : ℕ} (b : Basis (Fin n) ℝ V) (a : V) (i : ℕ) :
    Continuous fun x : V => coordAt b a i x := by
  by_cases h : i < n
  · simpa [coordAt_eq_sub b a h] using (coordCLM b ⟨i, h⟩).continuous.sub continuous_const
  · simp only [coordAt_of_le (Nat.not_lt.1 h)]
    exact continuous_const

omit [FiniteDimensional ℝ V] in
/-- A point all of whose coordinates vanish is the base point. -/
theorem coordAt_eq_zero_iff {n : ℕ} {b : Basis (Fin n) ℝ V} {a : V} (x : V) :
    (∀ i, coordAt b a i x = 0) ↔ x = a := by
  constructor
  · intro h
    have hrepr : ∀ i : Fin n, b.repr (x - a) i = 0 := by
      intro i
      have hi := h (i : ℕ)
      rwa [coordAt_of_lt i.2, Basis.coord_apply, Fin.eta] at hi
    have hzero : b.repr (x - a) = 0 := by
      ext i
      simpa using hrepr i
    have hxa : x - a = 0 := by
      have := congrArg b.repr.symm hzero
      simpa using this
    exact sub_eq_zero.1 hxa
  · rintro rfl
    intro i
    simp

/-! ### Convexity and closedness of the constraint sets -/

omit [FiniteDimensional ℝ V] in
theorem convex_coordAt_le {n : ℕ} {b : Basis (Fin n) ℝ V} {a : V} (i : ℕ) (t : ℝ) :
    Convex ℝ {x | coordAt b a i x ≤ t} := by
  intro x hx y hy s r hs hr hsr
  have hx' : coordAt b a i x ≤ t := hx
  have hy' : coordAt b a i y ≤ t := hy
  show coordAt b a i (s • x + r • y) ≤ t
  rw [coordAt_combo b a i hsr]
  have hsum := add_le_add (mul_le_mul_of_nonneg_left hx' hs) (mul_le_mul_of_nonneg_left hy' hr)
  have hst : s * t + r * t = t := by rw [← add_mul, hsr, one_mul]
  linarith

omit [FiniteDimensional ℝ V] in
theorem convex_coordAt_ge {n : ℕ} {b : Basis (Fin n) ℝ V} {a : V} (i : ℕ) (t : ℝ) :
    Convex ℝ {x | t ≤ coordAt b a i x} := by
  intro x hx y hy s r hs hr hsr
  have hx' : t ≤ coordAt b a i x := hx
  have hy' : t ≤ coordAt b a i y := hy
  show t ≤ coordAt b a i (s • x + r • y)
  rw [coordAt_combo b a i hsr]
  have hsum := add_le_add (mul_le_mul_of_nonneg_left hx' hs) (mul_le_mul_of_nonneg_left hy' hr)
  have hst : s * t + r * t = t := by rw [← add_mul, hsr, one_mul]
  linarith

omit [FiniteDimensional ℝ V] in
theorem convex_coordAt_eq {n : ℕ} {b : Basis (Fin n) ℝ V} {a : V} (i : ℕ) (t : ℝ) :
    Convex ℝ {x | coordAt b a i x = t} := by
  intro x hx y hy s r hs hr hsr
  have hx' : coordAt b a i x = t := hx
  have hy' : coordAt b a i y = t := hy
  show coordAt b a i (s • x + r • y) = t
  rw [coordAt_combo b a i hsr, hx', hy', ← add_mul, hsr, one_mul]

theorem isClosed_coordAt_le {n : ℕ} {b : Basis (Fin n) ℝ V} {a : V} (i : ℕ) (t : ℝ) :
    IsClosed {x : V | coordAt b a i x ≤ t} :=
  isClosed_le (continuous_coordAt b a i) continuous_const

theorem isClosed_coordAt_ge {n : ℕ} {b : Basis (Fin n) ℝ V} {a : V} (i : ℕ) (t : ℝ) :
    IsClosed {x : V | t ≤ coordAt b a i x} :=
  isClosed_le continuous_const (continuous_coordAt b a i)

theorem isClosed_coordAt_eq {n : ℕ} {b : Basis (Fin n) ℝ V} {a : V} (i : ℕ) (t : ℝ) :
    IsClosed {x : V | coordAt b a i x = t} :=
  isClosed_eq (continuous_coordAt b a i) continuous_const

/-! ### Coordinates of an explicit point, and functionals in coordinates -/

omit [FiniteDimensional ℝ V] in
theorem coordAt_point {n : ℕ} (b : Basis (Fin n) ℝ V) (a : V) (f : Fin n → ℝ) {i : ℕ}
    (h : i < n) : coordAt b a i (a + ∑ j, f j • b j) = f ⟨i, h⟩ := by
  rw [coordAt_of_lt h, add_sub_cancel_left, Basis.coord_apply, b.repr_sum_self]

omit [FiniteDimensional ℝ V] in
/-- A continuous linear functional is its value at the base point plus the corresponding
combination of coordinates. -/
theorem apply_eq_sum_coordAt {n : ℕ} (b : Basis (Fin n) ℝ V) (a : V) (u : V →L[ℝ] ℝ) (x : V) :
    u x = u a + ∑ i ∈ Finset.range n, u (basisAt b i) * coordAt b a i x := by
  have hx : x - a = ∑ j : Fin n, b.coord j (x - a) • b j := by
    simpa [Basis.coord_apply] using (b.sum_repr (x - a)).symm
  have h1 : u (x - a) = ∑ j : Fin n, b.coord j (x - a) * u (b j) := by
    conv_lhs => rw [hx]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul]
  have h2 : ∑ j : Fin n, b.coord j (x - a) * u (b j)
      = ∑ i ∈ Finset.range n, u (basisAt b i) * coordAt b a i x := by
    rw [← Fin.sum_univ_eq_sum_range fun i => u (basisAt b i) * coordAt b a i x]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [basisAt_coe, coordAt_of_lt j.2, Fin.eta, mul_comm]
  rw [← h2, ← h1, map_sub]
  ring

end ConvexFilter
