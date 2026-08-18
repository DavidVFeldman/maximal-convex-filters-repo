import ConvexFilters.LexCone

/-!
# Lex cones modulo a subspace

This file is Parts A and B of WO-06a. It relativizes WO-04's `ConvexFilter.IsLexConeOn` a
second time: the exceptional set of the trichotomy is no longer `{0}` but a prescribed
submodule `M ≤ W`.

The point of the generalization is Theorem 6.1 of the paper, where the invariant `Q ⊆ V*`
decomposes as `V* = Q ⊔ (-Q) ⊔ M` with `M` a generally nonzero submodule. Threading `M`
through the definitions and through the induction of Lemma 3.2 keeps the whole development
inside `V*` and avoids quotient normed spaces.

The generalization subsumes WO-04: `isLexConeModOn_bot_iff` identifies `IsLexConeModOn W ⊥ P`
with `ConvexFilter.IsLexConeOn W P`.

## Main results

* `ConvexFilter.Adapted.IsLexConeModOn.add_M` — the identity `P + M = P`;
* `ConvexFilter.Adapted.IsLexConeModOn.exists_nonneg_functional` — a functional which is
  nonzero somewhere on `W`, annihilates `M`, and is nonnegative on `P`;
* `ConvexFilter.Adapted.exists_functionals_mod` — the normal form modulo `M`: every such `P`
  is the lexicographic cone `lexConeMod W M l` of a family of `finrank W - finrank M`
  functionals whose joint kernel inside `W` is exactly `M`.

## A false contract statement

The contract form of `IsLexConeModOn.mem_of_pos` (no hypothesis relating `f` to `M`) is
false; the degenerate configuration `M = W`, `P = ∅` refutes it. The refutation is
`ConvexFilter.Adapted.mem_of_pos_counterexample`, and the delivered `mem_of_pos` carries the
extra hypothesis that `f` annihilates `M`, which is exactly what the induction of Part B
supplies.
-/

variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]

namespace ConvexFilter.Adapted

open ConvexFilter

/-! ## Part A — lex cones modulo a subspace -/

/-- A lex cone on `W` modulo the submodule `M ≤ W`: the positive cone of a
translation-invariant total order on `W` whose zero class is `M`. -/
structure IsLexConeModOn (W M : Submodule ℝ U) (P : Set U) : Prop where
  M_le : M ≤ W
  mem_of_mem : ∀ ⦃x⦄, x ∈ P → x ∈ W
  add_mem : ∀ ⦃x y⦄, x ∈ P → y ∈ P → x + y ∈ P
  smul_mem : ∀ ⦃c : ℝ⦄, 0 < c → ∀ ⦃x⦄, x ∈ P → c • x ∈ P
  trichotomy : ∀ ⦃x⦄, x ∈ W → x ∈ P ∨ x ∈ M ∨ -x ∈ P
  notMem_M : ∀ ⦃x⦄, x ∈ P → x ∉ M
  neg_notMem : ∀ ⦃x⦄, x ∈ P → -x ∉ P

namespace IsLexConeModOn

variable {W M : Submodule ℝ U} {P : Set U}

omit [FiniteDimensional ℝ U] in
/-- A lex cone modulo `M` is convex. -/
theorem convex (h : IsLexConeModOn W M P) : Convex ℝ P := by
  intro x hx y hy a b ha hb hab
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · have hb1 : b = 1 := by linarith [ha0 ▸ hab]
    simpa [← ha0, hb1] using hy
  rcases eq_or_lt_of_le hb with hb0 | hb0
  · have ha1 : a = 1 := by linarith [hb0 ▸ hab]
    simpa [← hb0, ha1] using hx
  exact h.add_mem (h.smul_mem ha0 hx) (h.smul_mem hb0 hy)

omit [FiniteDimensional ℝ U] in
/-- Proposition 2.5(4) in the abstract: `P + M = P`. -/
theorem add_M (h : IsLexConeModOn W M P) {x w : U} (hx : x ∈ P) (hw : w ∈ M) : x + w ∈ P := by
  have hxW : x ∈ W := h.mem_of_mem hx
  have hwW : w ∈ W := h.M_le hw
  rcases h.trichotomy (W.add_mem hxW hwW) with hP | hM | hnP
  · exact hP
  · -- `x = (x + w) - w ∈ M` contradicts `notMem_M`
    exact absurd (by simpa using M.sub_mem hM hw : x ∈ M) (h.notMem_M hx)
  · -- adding `x ∈ P` gives `-w ∈ P`, again contradicting `notMem_M`
    have hneg : -w ∈ P := by
      have := h.add_mem hnP hx
      have heq : -(x + w) + x = -w := by abel
      rwa [heq] at this
    exact absurd (M.neg_mem hw) (h.notMem_M hneg)

omit [FiniteDimensional ℝ U] in
/-- A lex cone modulo a proper submodule is nonempty. -/
theorem nonempty_of_lt (h : IsLexConeModOn W M P) (hlt : M < W) : P.Nonempty := by
  obtain ⟨x, hxW, hxM⟩ : ∃ x ∈ W, x ∉ M := by
    by_contra hcon
    push_neg at hcon
    exact absurd (le_antisymm h.M_le hcon) (ne_of_lt hlt)
  rcases h.trichotomy hxW with hP | hM | hnP
  · exact ⟨x, hP⟩
  · exact absurd hM hxM
  · exact ⟨-x, hnP⟩

/-- A lex cone modulo a proper submodule admits a continuous linear functional which is
nonzero somewhere on `W`, annihilates `M`, and is nonnegative on the cone. -/
theorem exists_nonneg_functional (h : IsLexConeModOn W M P) (hlt : M < W) :
    ∃ f : U →L[ℝ] ℝ, (∃ v ∈ W, f v ≠ 0) ∧ (∀ w ∈ M, f w = 0) ∧ ∀ x ∈ P, 0 ≤ f x := by
  classical
  set T : AffineSubspace ℝ U := AffineSubspace.mk' (0 : U) W with hT
  have hmemT : ∀ x : U, x ∈ T ↔ x ∈ W := by
    intro x
    rw [hT, AffineSubspace.mem_mk']
    simp
  have hPT : P ⊆ (T : Set U) := fun x hx => (hmemT x).2 (h.mem_of_mem hx)
  have hDT : ({0} : Set U) ⊆ (T : Set U) := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    exact (hmemT x).2 (hx ▸ W.zero_mem)
  have hdisj : P ∩ ({0} : Set U) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hxP, hx0⟩
    rw [Set.mem_singleton_iff] at hx0
    exact h.notMem_M hxP (hx0 ▸ M.zero_mem)
  obtain ⟨u, t, ⟨v, hvT, hv⟩, hle, hge⟩ :=
    exists_separating_of_subset_affine h.convex (convex_singleton (0 : U))
      (h.nonempty_of_lt hlt) ⟨0, rfl⟩ hdisj hPT hDT
  have ht0 : t ≤ 0 := by simpa using hge 0 rfl
  have hnonneg : ∀ x ∈ P, 0 ≤ (-u) x := by
    intro x hx
    have := hle x hx
    simp only [ContinuousLinearMap.neg_apply]
    linarith
  refine ⟨-u, ⟨v, ?_, ?_⟩, ?_, hnonneg⟩
  · rw [hT, AffineSubspace.direction_mk'] at hvT
    exact hvT
  · simpa using hv
  · -- `x + c • w ∈ P` for every real `c`, so `f x + c * f w ≥ 0` for every `c`
    intro w hw
    obtain ⟨x, hx⟩ := h.nonempty_of_lt hlt
    by_contra hne
    set c : ℝ := (-(-u) x - 1) / (-u) w with hc
    have hmem : x + c • w ∈ P := h.add_M hx (M.smul_mem c hw)
    have hval := hnonneg _ hmem
    rw [map_add, map_smul, smul_eq_mul, hc, div_mul_cancel₀ _ hne] at hval
    linarith

omit [FiniteDimensional ℝ U] in
/-- If `f` annihilates `M` and is nonnegative on `P`, then every point of `W` on which `f` is
positive lies in `P`.

The contract form of this statement omits `hfM`, and is false: see
`ConvexFilter.Adapted.mem_of_pos_counterexample`. -/
theorem mem_of_pos (h : IsLexConeModOn W M P) {f : U →L[ℝ] ℝ} (hfM : ∀ w ∈ M, f w = 0)
    (hf : ∀ x ∈ P, 0 ≤ f x) {x : U} (hx : x ∈ W) (hfx : 0 < f x) : x ∈ P := by
  by_contra hxP
  rcases h.trichotomy hx with hP | hM | hnP
  · exact hxP hP
  · rw [hfM x hM] at hfx
    exact lt_irrefl 0 hfx
  · have := hf _ hnP
    rw [map_neg] at this
    linarith

omit [FiniteDimensional ℝ U] in
/-- Restricting to the kernel of a functional annihilating `M` gives a lex cone modulo `M` on
the corresponding smaller submodule. -/
theorem restrict (h : IsLexConeModOn W M P) {f : U →L[ℝ] ℝ} (hfM : ∀ w ∈ M, f w = 0) :
    IsLexConeModOn (W ⊓ LinearMap.ker (f : U →ₗ[ℝ] ℝ)) M (P ∩ {x | f x = 0}) where
  M_le := fun w hw => ⟨h.M_le hw, hfM w hw⟩
  mem_of_mem := by
    rintro x ⟨hxP, hx0⟩
    exact ⟨h.mem_of_mem hxP, hx0⟩
  add_mem := by
    rintro x y ⟨hxP, hx0⟩ ⟨hyP, hy0⟩
    refine ⟨h.add_mem hxP hyP, ?_⟩
    simp only [Set.mem_setOf_eq] at hx0 hy0 ⊢
    rw [map_add, hx0, hy0, add_zero]
  smul_mem := by
    rintro c hc x ⟨hxP, hx0⟩
    refine ⟨h.smul_mem hc hxP, ?_⟩
    simp only [Set.mem_setOf_eq] at hx0 ⊢
    rw [map_smul, hx0, smul_zero]
  trichotomy := by
    rintro x ⟨hxW, hxk⟩
    have hfx : f x = 0 := hxk
    rcases h.trichotomy hxW with hP | hM | hnP
    · exact Or.inl ⟨hP, hfx⟩
    · exact Or.inr (Or.inl hM)
    · refine Or.inr (Or.inr ⟨hnP, ?_⟩)
      simp only [Set.mem_setOf_eq, map_neg, hfx, neg_zero]
  notMem_M := fun _ hx => h.notMem_M hx.1
  neg_notMem := by
    rintro x ⟨hxP, -⟩ ⟨hnP, -⟩
    exact h.neg_notMem hxP hnP

end IsLexConeModOn

omit [FiniteDimensional ℝ U] in
/-- The generalization subsumes WO-04: modulo `⊥` it is `ConvexFilter.IsLexConeOn`. -/
theorem isLexConeModOn_bot_iff {W : Submodule ℝ U} {P : Set U} :
    IsLexConeModOn W ⊥ P ↔ ConvexFilter.IsLexConeOn W P := by
  constructor
  · intro h
    refine ⟨h.mem_of_mem, h.add_mem, h.smul_mem, ?_, ?_, h.neg_notMem⟩
    · intro x hx
      rcases h.trichotomy hx with hP | hM | hnP
      · exact Or.inl hP
      · exact Or.inr (Or.inl (by simpa using hM))
      · exact Or.inr (Or.inr hnP)
    · intro h0
      exact h.notMem_M h0 (Submodule.mem_bot ℝ |>.2 rfl)
  · intro h
    refine ⟨bot_le, h.mem_of_mem, h.add_mem, h.smul_mem, ?_, ?_, h.neg_notMem⟩
    · intro x hx
      rcases h.trichotomy hx with hP | h0 | hnP
      · exact Or.inl hP
      · exact Or.inr (Or.inl (by simp [h0]))
      · exact Or.inr (Or.inr hnP)
    · intro x hx hM
      have hx0 : x = 0 := by simpa using hM
      exact h.zero_notMem (hx0 ▸ hx)

/-- The contract form of `IsLexConeModOn.mem_of_pos`, without a hypothesis relating `f` to
`M`, is false. The degenerate configuration `W = M = ⊤`, `P = ∅` on `U = ℝ` refutes it: the
cone axioms hold vacuously, the nonnegativity hypothesis holds vacuously, and `f = id` is
positive at `1 ∈ W`, which is not in `P`. -/
theorem mem_of_pos_counterexample :
    ∃ (W M : Submodule ℝ ℝ) (P : Set ℝ) (f : ℝ →L[ℝ] ℝ) (x : ℝ),
      IsLexConeModOn W M P ∧ (∀ y ∈ P, 0 ≤ f y) ∧ x ∈ W ∧ 0 < f x ∧ x ∉ P := by
  refine ⟨⊤, ⊤, ∅, ContinuousLinearMap.id ℝ ℝ, 1, ⟨le_refl _, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_,
    Submodule.mem_top, by norm_num, by simp⟩
  · exact fun x hx => absurd hx (Set.notMem_empty x)
  · exact fun x y hx => absurd hx (Set.notMem_empty x)
  · exact fun c _ x hx => absurd hx (Set.notMem_empty x)
  · exact fun x _ => Or.inr (Or.inl Submodule.mem_top)
  · exact fun x hx => absurd hx (Set.notMem_empty x)
  · exact fun x hx => absurd hx (Set.notMem_empty x)
  · exact fun y hy => absurd hy (Set.notMem_empty y)

/-! ## Part B — the normal form modulo `M` -/

/-- The lexicographic cone of a family of functionals, relativized to `W` and taken modulo
`M`: the points of `W` whose first nonvanishing coordinate is positive. The submodule `M`
does not enter the body; it is carried so that the statements of Part B and Part C read as
statements about the pair `(W, M)`. -/
def lexConeMod (W M : Submodule ℝ U) {k : ℕ} (l : Fin k → (U →L[ℝ] ℝ)) : Set U :=
  {x | x ∈ W ∧ ∃ j : Fin k, 0 < l j x ∧ ∀ i : Fin k, i < j → l i x = 0}

omit [FiniteDimensional ℝ U] in
theorem mem_lexConeMod_iff {W M : Submodule ℝ U} {k : ℕ} {l : Fin k → (U →L[ℝ] ℝ)} {x : U} :
    x ∈ lexConeMod W M l ↔
      x ∈ W ∧ ∃ j : Fin k, 0 < l j x ∧ ∀ i : Fin k, i < j → l i x = 0 :=
  Iff.rfl

omit [FiniteDimensional ℝ U] in
/-- Modulo `⊥`, `lexConeMod` is WO-04's `ConvexFilter.lexCone`. -/
theorem lexConeMod_eq_lexCone {W M : Submodule ℝ U} {k : ℕ} {l : Fin k → (U →L[ℝ] ℝ)} :
    lexConeMod W M l = ConvexFilter.lexCone W l := rfl

omit [FiniteDimensional ℝ U] in
/-- A lexicographic cone modulo `M` is a lex cone modulo `M`, provided the functionals
annihilate `M` and their joint kernel inside `W` is contained in `M`. -/
theorem isLexConeModOn_lexConeMod {W M : Submodule ℝ U} {k : ℕ} {l : Fin k → (U →L[ℝ] ℝ)}
    (hML : M ≤ W) (hMker : ∀ i, ∀ w ∈ M, l i w = 0)
    (hsep : ∀ x ∈ W, (∀ i, l i x = 0) → x ∈ M) :
    IsLexConeModOn W M (lexConeMod W M l) where
  M_le := hML
  mem_of_mem := fun _ hx => hx.1
  add_mem := by
    rintro x y ⟨hxW, jx, hjx, hjx0⟩ ⟨hyW, jy, hjy, hjy0⟩
    refine ⟨W.add_mem hxW hyW, ?_⟩
    rcases lt_trichotomy jx jy with hlt | heq | hgt
    · refine ⟨jx, ?_, ?_⟩
      · rw [map_add, hjy0 jx hlt, add_zero]; exact hjx
      · intro i hi
        rw [map_add, hjx0 i hi, hjy0 i (hi.trans hlt), add_zero]
    · subst heq
      refine ⟨jx, ?_, ?_⟩
      · rw [map_add]
        linarith
      · intro i hi
        rw [map_add, hjx0 i hi, hjy0 i hi, add_zero]
    · refine ⟨jy, ?_, ?_⟩
      · rw [map_add, hjx0 jy hgt, zero_add]; exact hjy
      · intro i hi
        rw [map_add, hjx0 i (hi.trans hgt), hjy0 i hi, add_zero]
  smul_mem := by
    rintro c hc x ⟨hxW, j, hj, hj0⟩
    refine ⟨W.smul_mem c hxW, j, ?_, ?_⟩
    · rw [map_smul, smul_eq_mul]
      exact mul_pos hc hj
    · intro i hi
      rw [map_smul, hj0 i hi, smul_zero]
  trichotomy := by
    intro x hxW
    by_cases hall : ∀ i, l i x = 0
    · exact Or.inr (Or.inl (hsep x hxW hall))
    · push_neg at hall
      obtain ⟨i₀, hi₀⟩ := hall
      obtain ⟨j, hj, hj0⟩ := ConvexFilter.exists_least_ne_zero (l := l) (x := x) hi₀
      rcases lt_or_gt_of_ne hj with hneg | hpos
      · refine Or.inr (Or.inr ⟨W.neg_mem hxW, j, ?_, ?_⟩)
        · rw [map_neg]; linarith
        · intro i hi
          rw [map_neg, hj0 i hi, neg_zero]
      · exact Or.inl ⟨hxW, j, hpos, hj0⟩
  notMem_M := by
    rintro x ⟨-, j, hj, -⟩ hxM
    rw [hMker j x hxM] at hj
    exact lt_irrefl 0 hj
  neg_notMem := by
    rintro x ⟨-, j, hj, hj0⟩ ⟨-, j', hj', hj'0⟩
    rcases lt_trichotomy j j' with hlt | heq | hgt
    · have := hj'0 j hlt
      rw [map_neg, neg_eq_zero] at this
      rw [this] at hj
      exact lt_irrefl 0 hj
    · rw [heq] at hj
      rw [map_neg] at hj'
      linarith
    · have hz := hj0 j' hgt
      rw [map_neg, hz, neg_zero] at hj'
      exact lt_irrefl 0 hj'

/-- Auxiliary form of the normal form modulo `M`, set up for strong induction on the rank of
`W`. The submodule `M` is universally quantified inside the induction only because `W` is;
it is carried unchanged through the recursive call. -/
theorem exists_functionals_mod_aux (n : ℕ) : ∀ (W M : Submodule ℝ U) (P : Set U),
    Module.finrank ℝ W = n → IsLexConeModOn W M P →
    ∃ (k : ℕ) (l : Fin k → (U →L[ℝ] ℝ)),
      k + Module.finrank ℝ M = Module.finrank ℝ W ∧
      (∀ i, ∀ w ∈ M, l i w = 0) ∧
      (∀ x ∈ W, (∀ i, l i x = 0) → x ∈ M) ∧
      P = lexConeMod W M l := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W M P hn h
    by_cases hMW : M = W
    · -- base case: `M = W`, so `P` is empty and no functional is needed
      subst hMW
      refine ⟨0, Fin.elim0, by simp, fun i => i.elim0, fun x hx _ => hx, ?_⟩
      ext x
      simp only [lexConeMod, Set.mem_setOf_eq]
      constructor
      · intro hxP
        exact absurd (h.mem_of_mem hxP) (h.notMem_M hxP)
      · rintro ⟨-, j, -⟩
        exact j.elim0
    · have hlt : M < W := lt_of_le_of_ne h.M_le hMW
      obtain ⟨f, ⟨v, hvW, hfv⟩, hfM, hf⟩ := h.exists_nonneg_functional hlt
      set W' : Submodule ℝ U := W ⊓ LinearMap.ker (f : U →ₗ[ℝ] ℝ) with hW'
      have hrank : Module.finrank ℝ W' + 1 = Module.finrank ℝ W :=
        ConvexFilter.finrank_inf_ker_add_one hvW hfv
      obtain ⟨k', l', hk', hMker', hsep', hP'⟩ :=
        ih (Module.finrank ℝ W') (by omega) W' M (P ∩ {x | f x = 0}) rfl (h.restrict hfM)
      refine ⟨k' + 1, Fin.cons f l', by omega, ?_, ?_, ?_⟩
      · intro i w hw
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
        · rw [Fin.cons_zero]; exact hfM w hw
        · rw [Fin.cons_succ]; exact hMker' i' w hw
      · intro x hxW hall
        have hf0 : f x = 0 := by
          have := hall 0
          rwa [Fin.cons_zero] at this
        refine hsep' x ⟨hxW, hf0⟩ ?_
        intro i
        have := hall i.succ
        rwa [Fin.cons_succ] at this
      · ext x
        constructor
        · intro hxP
          have hxW : x ∈ W := h.mem_of_mem hxP
          rcases eq_or_lt_of_le (hf x hxP) with h0 | hpos
          · have hx' : x ∈ P ∩ {x | f x = 0} := ⟨hxP, h0.symm⟩
            rw [hP'] at hx'
            obtain ⟨-, j', hj'pos, hj'0⟩ := hx'
            refine ⟨hxW, j'.succ, ?_, ?_⟩
            · rwa [Fin.cons_succ]
            · intro i hi
              rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
              · rw [Fin.cons_zero]; exact h0.symm
              · rw [Fin.cons_succ]
                exact hj'0 i' (Fin.succ_lt_succ_iff.1 hi)
          · refine ⟨hxW, 0, ?_, ?_⟩
            · rwa [Fin.cons_zero]
            · intro i hi
              simp only [Fin.lt_def, Fin.val_zero, Nat.not_lt_zero] at hi
        · rintro ⟨hxW, j, hjpos, hj0⟩
          rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
          · rw [Fin.cons_zero] at hjpos
            exact h.mem_of_pos hfM hf hxW hjpos
          · have hf0 : f x = 0 := by
              have := hj0 0 (Fin.succ_pos j')
              rwa [Fin.cons_zero] at this
            have hmem : x ∈ lexConeMod W' M l' := by
              refine ⟨⟨hxW, hf0⟩, j', ?_, ?_⟩
              · rwa [Fin.cons_succ] at hjpos
              · intro i' hi'
                have := hj0 i'.succ (Fin.succ_lt_succ_iff.2 hi')
                rwa [Fin.cons_succ] at this
            rw [← hP'] at hmem
            exact hmem.1

/-- The normal form modulo `M`, Lemma 3.2 relativized: every lex cone on `W` modulo `M` is
the lexicographic cone of a family of `finrank ℝ W - finrank ℝ M` functionals annihilating
`M`, whose joint kernel inside `W` is exactly `M`. -/
theorem exists_functionals_mod {W M : Submodule ℝ U} {P : Set U} (h : IsLexConeModOn W M P) :
    ∃ (k : ℕ) (l : Fin k → (U →L[ℝ] ℝ)),
      k + Module.finrank ℝ M = Module.finrank ℝ W ∧
      (∀ i, ∀ w ∈ M, l i w = 0) ∧
      (∀ x ∈ W, (∀ i, l i x = 0) → x ∈ M) ∧
      P = lexConeMod W M l :=
  exists_functionals_mod_aux (Module.finrank ℝ W) W M P rfl h

end ConvexFilter.Adapted
