import ConvexFilters.LexCone

/-!
# Flags and order-convex subspaces

This file is Part C of WO-04, the second half of Lemma 3.2 of the paper.

For a family `l : Fin k → (U →L[ℝ] ℝ)` of functionals separating the points of a submodule
`W`, the *flags* are the submodules

`flag W l m = {x ∈ W | l i x = 0 for all i < m}`,

a decreasing chain from `flag W l 0 = W` down to `flag W l k = ⊥`. A subspace `W' ≤ W` is
*order-convex* for a cone `P` when it is closed under passing from a point `v` to a point
`w` with `0 < w < v` in the induced order. The main results are

* `ConvexFilter.isOrderConvex_flag`: every flag is order-convex for `lexCone W l`;
* `ConvexFilter.exists_eq_flag`: conversely, every order-convex subspace of `W` is a flag;
* `ConvexFilter.isOrderConvex_total`: the order-convex subspaces of a lex cone on `W` form a
  chain.
-/

variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]

namespace ConvexFilter

/-- The `m`-th flag of a family of functionals on `W`: the points of `W` annihilated by the
first `m` functionals. -/
def flag (W : Submodule ℝ U) {k : ℕ} (l : Fin k → (U →L[ℝ] ℝ)) (m : ℕ) : Submodule ℝ U where
  carrier := {x | x ∈ W ∧ ∀ i : Fin k, (i : ℕ) < m → l i x = 0}
  add_mem' := by
    rintro x y ⟨hxW, hx⟩ ⟨hyW, hy⟩
    exact ⟨W.add_mem hxW hyW, fun i hi => by rw [map_add, hx i hi, hy i hi, add_zero]⟩
  zero_mem' := ⟨W.zero_mem, fun i _ => by simp⟩
  smul_mem' := by
    rintro c x ⟨hxW, hx⟩
    exact ⟨W.smul_mem c hxW, fun i hi => by rw [map_smul, hx i hi, smul_zero]⟩

omit [FiniteDimensional ℝ U] in
theorem mem_flag_iff {W : Submodule ℝ U} {k : ℕ} {l : Fin k → (U →L[ℝ] ℝ)} {m : ℕ} {x : U} :
    x ∈ flag W l m ↔ x ∈ W ∧ ∀ i : Fin k, (i : ℕ) < m → l i x = 0 := Iff.rfl

/-- Order-convexity of a subspace `W'` for a cone `P`: if `0 < w < v` in the order induced
by `P` and `v ∈ W'`, then `w ∈ W'`. -/
def IsOrderConvex (P : Set U) (W' : Submodule ℝ U) : Prop :=
  ∀ ⦃w v : U⦄, w ∈ P → v - w ∈ P → v ∈ W' → w ∈ W'

omit [FiniteDimensional ℝ U] in
theorem flag_zero {W : Submodule ℝ U} {k : ℕ} {l : Fin k → (U →L[ℝ] ℝ)} : flag W l 0 = W := by
  ext x
  simp [mem_flag_iff]

omit [FiniteDimensional ℝ U] in
theorem flag_antitone {W : Submodule ℝ U} {k : ℕ} {l : Fin k → (U →L[ℝ] ℝ)} :
    Antitone (flag W l) := by
  intro a b hab x hx
  exact ⟨hx.1, fun i hi => hx.2 i (lt_of_lt_of_le hi hab)⟩

omit [FiniteDimensional ℝ U] in
theorem flag_le {W : Submodule ℝ U} {k : ℕ} {l : Fin k → (U →L[ℝ] ℝ)} (m : ℕ) :
    flag W l m ≤ W := fun _ hx => hx.1

omit [FiniteDimensional ℝ U] in
/-- The flag `flag W l m` is order-convex for the lexicographic cone of `l`.

The separation hypothesis `hsep`, part of the contract statement, is not needed for this
implication. -/
theorem isOrderConvex_flag {W : Submodule ℝ U} {k : ℕ} {l : Fin k → (U →L[ℝ] ℝ)}
    (hsep : ∀ x ∈ W, (∀ i, l i x = 0) → x = 0) (m : ℕ) :
    IsOrderConvex (lexCone W l) (flag W l m) := by
  rintro w v ⟨hwW, jw, hjw, hjw0⟩ ⟨-, j₂, hj₂, hj₂0⟩ ⟨-, hv0⟩
  refine ⟨hwW, fun i hi => ?_⟩
  -- the first nonvanishing coordinate of `w` occurs at index `jw ≥ m`
  have hjwm : m ≤ (jw : ℕ) := by
    by_contra hlt
    push_neg at hlt
    -- `l jw (v - w) = - l jw w < 0`, so the witness `j₂` for `v - w` is at most `jw`
    have hvjw : l jw v = 0 := hv0 jw hlt
    have hsub : l jw (v - w) = - l jw w := by rw [map_sub, hvjw, zero_sub]
    have hj₂le : ¬ jw < j₂ := by
      intro hlt'
      have := hj₂0 jw hlt'
      rw [hsub] at this
      have : l jw w = 0 := by linarith [neg_eq_zero.1 this]
      rw [this] at hjw
      exact lt_irrefl 0 hjw
    rcases lt_trichotomy j₂ jw with hlt' | heq | hgt
    · -- both `v` and `w` vanish at `j₂`, contradicting `0 < l j₂ (v - w)`
      have h1 : l j₂ w = 0 := hjw0 j₂ hlt'
      have h2 : l j₂ v = 0 := hv0 j₂ (lt_trans hlt' hlt)
      rw [map_sub, h1, h2, sub_zero] at hj₂
      exact lt_irrefl 0 hj₂
    · subst heq
      rw [hsub] at hj₂
      linarith
    · exact hj₂le hgt
  exact hjw0 i (by simp only [Fin.lt_def]; omega)

omit [FiniteDimensional ℝ U] in
/-- Conversely, every order-convex subspace of `W` is one of the flags. -/
theorem exists_eq_flag {W : Submodule ℝ U} {k : ℕ} {l : Fin k → (U →L[ℝ] ℝ)}
    (hsep : ∀ x ∈ W, (∀ i, l i x = 0) → x = 0) {W' : Submodule ℝ U} (hW' : W' ≤ W)
    (hoc : IsOrderConvex (lexCone W l) W') :
    ∃ m ≤ k, W' = flag W l m := by
  classical
  by_cases hbot : W' = ⊥
  · -- the zero subspace is the last flag
    refine ⟨k, le_refl k, ?_⟩
    subst hbot
    ext x
    constructor
    · intro hx
      have hx0 : x = 0 := by simpa using hx
      exact ⟨hx0 ▸ W.zero_mem, fun i _ => by simp [hx0]⟩
    · rintro ⟨hxW, hz⟩
      have hx0 : x = 0 := hsep x hxW fun i => hz i i.isLt
      simp [hx0]
  · -- the least index at which some functional does not vanish identically on `W'`
    obtain ⟨x₀, hx₀W', hx₀0⟩ := (Submodule.ne_bot_iff W').1 hbot
    set S : Finset (Fin k) := Finset.univ.filter (fun i => ∃ x ∈ W', l i x ≠ 0) with hS
    have hSne : S.Nonempty := by
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty] at hcon
      have hall : ∀ i : Fin k, l i x₀ = 0 := by
        intro i
        by_contra hne
        have : i ∈ S := by
          simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨x₀, hx₀W', hne⟩
        rw [hcon] at this
        exact absurd this (Finset.notMem_empty i)
      exact hx₀0 (hsep x₀ (hW' hx₀W') hall)
    set j : Fin k := S.min' hSne with hj
    refine ⟨(j : ℕ), le_of_lt j.isLt, ?_⟩
    -- minimality gives one inclusion
    have hforward : W' ≤ flag W l (j : ℕ) := by
      intro w hw
      refine ⟨hW' hw, fun i hi => ?_⟩
      by_contra hne
      have hiS : i ∈ S := by
        simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨w, hw, hne⟩
      have := S.min'_le i hiS
      rw [← hj, Fin.le_def] at this
      omega
    refine le_antisymm hforward ?_
    -- a point of `W'` positive at index `j`
    obtain ⟨x, hxW', hxpos⟩ : ∃ x ∈ W', 0 < l j x := by
      have hjS : j ∈ S := S.min'_mem hSne
      rw [hS, Finset.mem_filter] at hjS
      obtain ⟨-, x, hxW', hxne⟩ := hjS
      rcases lt_or_gt_of_ne hxne with hneg | hpos
      · exact ⟨-x, W'.neg_mem hxW', by rw [map_neg]; linarith⟩
      · exact ⟨x, hxW', hpos⟩
    intro y hy
    obtain ⟨hyW, hy0⟩ := hy
    have hxflag := hforward hxW'
    set a : ℝ := l j x with ha
    set b : ℝ := l j y with hb
    set mu : ℝ := (|b| + 1) / a with hmu
    have hmupos : 0 < mu := div_pos (by positivity) hxpos
    have hmua : mu * a = |b| + 1 := by
      rw [hmu, div_mul_cancel₀ _ (ne_of_gt hxpos)]
    -- the two points `mu • x + y` and `mu • x - y` lie in the cone
    have hlow : ∀ i : Fin k, i < j → l i x = 0 ∧ l i y = 0 := by
      intro i hi
      have hi' : (i : ℕ) < (j : ℕ) := hi
      exact ⟨hxflag.2 i hi', hy0 i hi'⟩
    have hplus : mu • x + y ∈ lexCone W l := by
      refine ⟨W.add_mem (W.smul_mem mu (hW' hxW')) hyW, j, ?_, ?_⟩
      · rw [map_add, map_smul, smul_eq_mul, ← ha, ← hb, hmua]
        cases abs_cases b with
        | inl h => linarith [h.1]
        | inr h => linarith [h.1]
      · intro i hi
        rw [map_add, map_smul, (hlow i hi).1, (hlow i hi).2, smul_zero, add_zero]
    have hminus : mu • x - y ∈ lexCone W l := by
      refine ⟨W.sub_mem (W.smul_mem mu (hW' hxW')) hyW, j, ?_, ?_⟩
      · rw [map_sub, map_smul, smul_eq_mul, ← ha, ← hb, hmua]
        cases abs_cases b with
        | inl h => linarith [h.1]
        | inr h => linarith [h.1]
      · intro i hi
        rw [map_sub, map_smul, (hlow i hi).1, (hlow i hi).2, smul_zero, sub_zero]
    -- order-convexity squeezes `mu • x + y` between `0` and `(2 * mu) • x ∈ W'`
    have hv : (2 * mu) • x ∈ W' := W'.smul_mem _ hxW'
    have hdiff : (2 * mu) • x - (mu • x + y) = mu • x - y := by
      rw [two_mul, add_smul]
      abel
    have hmem : mu • x + y ∈ W' := hoc hplus (by rw [hdiff]; exact hminus) hv
    have : y = (mu • x + y) - mu • x := by abel
    rw [this]
    exact W'.sub_mem hmem (W'.smul_mem mu hxW')

/-! ### Ranks of the flags -/

/-- Cutting a submodule by the kernel of a functional drops its rank by at most one. -/
theorem finrank_inf_ker_ge {S : Submodule ℝ U} {f : U →L[ℝ] ℝ} :
    Module.finrank ℝ S
      ≤ Module.finrank ℝ (S ⊓ LinearMap.ker (f : U →ₗ[ℝ] ℝ) : Submodule ℝ U) + 1 := by
  by_cases hex : ∃ v ∈ S, f v ≠ 0
  · obtain ⟨v, hv, hfv⟩ := hex
    exact le_of_eq (finrank_inf_ker_add_one hv hfv).symm
  · push_neg at hex
    have heq : S ⊓ LinearMap.ker (f : U →ₗ[ℝ] ℝ) = S :=
      le_antisymm inf_le_left fun x hx => ⟨hx, hex x hx⟩
    rw [heq]
    omega

omit [FiniteDimensional ℝ U] in
/-- Passing from the `m`-th to the `(m+1)`-st flag cuts by the kernel of the `m`-th
functional. -/
theorem flag_succ_eq {W : Submodule ℝ U} {k : ℕ} {l : Fin k → (U →L[ℝ] ℝ)} {m : ℕ}
    (hm : m < k) :
    flag W l (m + 1) = flag W l m ⊓ LinearMap.ker ((l ⟨m, hm⟩ : U →L[ℝ] ℝ) : U →ₗ[ℝ] ℝ) := by
  ext x
  constructor
  · rintro ⟨hxW, hx⟩
    exact ⟨⟨hxW, fun i hi => hx i (by omega)⟩, hx ⟨m, hm⟩ (by simp)⟩
  · rintro ⟨⟨hxW, hx⟩, hker⟩
    refine ⟨hxW, fun i hi => ?_⟩
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 hi) with h' | h'
    · exact hx i h'
    · have hi' : i = ⟨m, hm⟩ := Fin.ext h'
      rw [hi']
      exact hker

omit [FiniteDimensional ℝ U] in
/-- Beyond index `k` the flags are constant. -/
theorem flag_eq_of_le {W : Submodule ℝ U} {k : ℕ} {l : Fin k → (U →L[ℝ] ℝ)} {m : ℕ}
    (hm : k ≤ m) : flag W l m = flag W l k := by
  refine le_antisymm (flag_antitone hm) ?_
  rintro x ⟨hxW, hx⟩
  exact ⟨hxW, fun i _ => hx i i.isLt⟩

/-- Consecutive flags differ in rank by at most one. -/
theorem finrank_flag_step {W : Submodule ℝ U} {k : ℕ} {l : Fin k → (U →L[ℝ] ℝ)} (m : ℕ) :
    Module.finrank ℝ (flag W l m) ≤ Module.finrank ℝ (flag W l (m + 1)) + 1 := by
  by_cases hm : m < k
  · rw [flag_succ_eq hm]
    exact finrank_inf_ker_ge
  · rw [flag_eq_of_le (by omega : k ≤ m + 1), flag_eq_of_le (by omega : k ≤ m)]
    omega

/-- Iterating `finrank_flag_step`. -/
theorem finrank_flag_le_add {W : Submodule ℝ U} {k : ℕ} {l : Fin k → (U →L[ℝ] ℝ)} (m j : ℕ) :
    Module.finrank ℝ (flag W l m) ≤ Module.finrank ℝ (flag W l (m + j)) + j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hstep := finrank_flag_step (W := W) (l := l) (m + j)
    have hidx : m + (j + 1) = (m + j) + 1 := by omega
    rw [hidx]
    omega

omit [FiniteDimensional ℝ U] in
/-- With separating functionals, the last flag is trivial. -/
theorem flag_eq_bot {W : Submodule ℝ U} {k : ℕ} {l : Fin k → (U →L[ℝ] ℝ)}
    (hsep : ∀ x ∈ W, (∀ i, l i x = 0) → x = 0) : flag W l k = ⊥ := by
  ext x
  constructor
  · rintro ⟨hxW, hx⟩
    have hx0 : x = 0 := hsep x hxW fun i => hx i i.isLt
    simp [hx0]
  · intro hx
    have hx0 : x = 0 := by simpa using hx
    exact ⟨hx0 ▸ W.zero_mem, fun i _ => by simp [hx0]⟩

/-- The ranks of the flags: each of the first `k` functionals cuts the rank by exactly
one. -/
theorem finrank_flag {W : Submodule ℝ U} {k : ℕ} {l : Fin k → (U →L[ℝ] ℝ)}
    (hsep : ∀ x ∈ W, (∀ i, l i x = 0) → x = 0) (hk : k = Module.finrank ℝ W) (m : ℕ) :
    Module.finrank ℝ (flag W l m) = Module.finrank ℝ W - min m k := by
  have hd0 : Module.finrank ℝ (flag W l 0) = Module.finrank ℝ W := by rw [flag_zero]
  have hdk : Module.finrank ℝ (flag W l k) = 0 := by
    rw [flag_eq_bot hsep, finrank_bot]
  rcases le_total m k with hmk | hmk
  · have h1 := finrank_flag_le_add (W := W) (l := l) 0 m
    have h2 := finrank_flag_le_add (W := W) (l := l) m (k - m)
    rw [Nat.zero_add] at h1
    rw [show m + (k - m) = k by omega] at h2
    rw [min_eq_left hmk]
    omega
  · rw [flag_eq_of_le hmk, hdk, min_eq_right hmk]
    omega

/-- The order-convex subspaces of a lex cone on `W` are totally ordered by inclusion. -/
theorem isOrderConvex_total {W : Submodule ℝ U} {P : Set U} (h : IsLexConeOn W P)
    {W' W'' : Submodule ℝ U} (h1 : W' ≤ W) (h2 : W'' ≤ W)
    (ho1 : IsOrderConvex P W') (ho2 : IsOrderConvex P W'') :
    W' ≤ W'' ∨ W'' ≤ W' := by
  obtain ⟨k, l, -, hsep, rfl⟩ := exists_functionals h
  obtain ⟨m, -, rfl⟩ := exists_eq_flag hsep h1 ho1
  obtain ⟨m', -, rfl⟩ := exists_eq_flag hsep h2 ho2
  rcases le_total m m' with hle | hle
  · exact Or.inr (flag_antitone hle)
  · exact Or.inl (flag_antitone hle)

end ConvexFilter
