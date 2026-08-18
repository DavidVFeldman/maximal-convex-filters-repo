import ConvexFilters.SeparationRel

/-!
# Lex cones and the induced order

This file is Section 3 of the paper, Parts A and B of WO-04.

A *lex cone on a submodule* `W` of a finite-dimensional real normed space `U` is a subset
`P ⊆ W` closed under addition and positive scaling, satisfying trichotomy on `W`
(`x ∈ P`, `x = 0` or `-x ∈ P`) and containing neither `0` nor a pair `x`, `-x`. Such a `P`
is the positive cone of a translation-invariant total order on `W`.

Everything is relativized to the submodule `W`, so that the induction of `exists_functionals`
stays inside `U` and never passes to the subtype `↥W`.

The main results are

* `ConvexFilter.IsLexConeOn.exists_nonneg_functional`: a lex cone on a nonzero `W` admits a
  functional, nonvanishing on `W`, which is nonnegative on the cone. This is proved from the
  project-local relative separation lemma `exists_separating_of_subset_affine`, replacing the
  topological argument of the paper.
* `ConvexFilter.exists_functionals` (Lemma 3.2): every lex cone on `W` is the lexicographic
  cone `lexCone W l` of a family `l : Fin k → (U →L[ℝ] ℝ)` of `k = finrank ℝ W` functionals
  separating the points of `W`.
-/

variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]

namespace ConvexFilter

/-! ## Part A — lex cones and the induced order -/

/-- A lex cone on the submodule `W`: the positive cone of a translation-invariant total
order on `W`. -/
structure IsLexConeOn (W : Submodule ℝ U) (P : Set U) : Prop where
  mem_of_mem : ∀ ⦃x⦄, x ∈ P → x ∈ W
  add_mem : ∀ ⦃x y⦄, x ∈ P → y ∈ P → x + y ∈ P
  smul_mem : ∀ ⦃c : ℝ⦄, 0 < c → ∀ ⦃x⦄, x ∈ P → c • x ∈ P
  trichotomy : ∀ ⦃x⦄, x ∈ W → x ∈ P ∨ x = 0 ∨ -x ∈ P
  zero_notMem : (0 : U) ∉ P
  neg_notMem : ∀ ⦃x⦄, x ∈ P → -x ∉ P

namespace IsLexConeOn

omit [FiniteDimensional ℝ U] in
/-- A lex cone is convex. -/
theorem convex {W : Submodule ℝ U} {P : Set U} (h : IsLexConeOn W P) : Convex ℝ P := by
  intro x hx y hy a b ha hb hab
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · have hb1 : b = 1 := by linarith [ha0 ▸ hab]
    simpa [← ha0, hb1] using hy
  rcases eq_or_lt_of_le hb with hb0 | hb0
  · have ha1 : a = 1 := by linarith [hb0 ▸ hab]
    simpa [← hb0, ha1] using hx
  exact h.add_mem (h.smul_mem ha0 hx) (h.smul_mem hb0 hy)

omit [FiniteDimensional ℝ U] in
/-- A lex cone on a nonzero submodule is nonempty. -/
theorem nonempty_of_ne_bot {W : Submodule ℝ U} {P : Set U} (h : IsLexConeOn W P)
    (hW : W ≠ ⊥) : P.Nonempty := by
  obtain ⟨x, hxW, hx0⟩ := (Submodule.ne_bot_iff W).1 hW
  rcases h.trichotomy hxW with hP | h0 | hnP
  · exact ⟨x, hP⟩
  · exact absurd h0 hx0
  · exact ⟨-x, hnP⟩

omit [FiniteDimensional ℝ U] in
/-- A lex cone on `W` spans `W`. -/
theorem span_eq {W : Submodule ℝ U} {P : Set U} (h : IsLexConeOn W P) :
    Submodule.span ℝ P = W := by
  refine le_antisymm (Submodule.span_le.2 fun x hx => h.mem_of_mem hx) ?_
  intro x hx
  rcases h.trichotomy hx with hP | h0 | hnP
  · exact Submodule.subset_span hP
  · simp [h0]
  · have : -x ∈ Submodule.span ℝ P := Submodule.subset_span hnP
    simpa using (Submodule.span ℝ P).neg_mem this

omit [FiniteDimensional ℝ U] in
/-- If `f` is nonnegative on the lex cone `P`, then every point of `W` on which `f` is
positive lies in `P`. -/
theorem mem_of_pos {W : Submodule ℝ U} {P : Set U} (h : IsLexConeOn W P) {f : U →L[ℝ] ℝ}
    (hf : ∀ x ∈ P, 0 ≤ f x) {x : U} (hx : x ∈ W) (hfx : 0 < f x) : x ∈ P := by
  by_contra hxP
  rcases h.trichotomy hx with hP | h0 | hnP
  · exact hxP hP
  · rw [h0] at hfx; simp at hfx
  · have := hf _ hnP
    rw [map_neg] at this
    linarith

/-- A lex cone on a nonzero submodule admits a continuous linear functional, nonvanishing
somewhere on `W`, which is nonnegative on the cone.

This is where the paper's topological argument would go; it is replaced by the relative
separation lemma `exists_separating_of_subset_affine`. -/
theorem exists_nonneg_functional {W : Submodule ℝ U} {P : Set U} (h : IsLexConeOn W P)
    (hW : W ≠ ⊥) :
    ∃ f : U →L[ℝ] ℝ, (∃ v ∈ W, f v ≠ 0) ∧ ∀ x ∈ P, 0 ≤ f x := by
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
    exact h.zero_notMem (hx0 ▸ hxP)
  obtain ⟨u, t, ⟨v, hvT, hv⟩, hle, hge⟩ :=
    exists_separating_of_subset_affine h.convex (convex_singleton (0 : U))
      (h.nonempty_of_ne_bot hW) ⟨0, rfl⟩ hdisj hPT hDT
  have ht0 : t ≤ 0 := by simpa using hge 0 rfl
  refine ⟨-u, ⟨v, ?_, ?_⟩, ?_⟩
  · rw [hT, AffineSubspace.direction_mk'] at hvT
    exact hvT
  · simpa using hv
  · intro x hx
    have := hle x hx
    simp only [ContinuousLinearMap.neg_apply]
    linarith

omit [FiniteDimensional ℝ U] in
/-- Restricting a lex cone to the kernel of a functional nonnegative on it gives a lex cone
on the corresponding smaller submodule. -/
theorem restrict {W : Submodule ℝ U} {P : Set U} (h : IsLexConeOn W P) {f : U →L[ℝ] ℝ}
    (hf : ∀ x ∈ P, 0 ≤ f x) :
    IsLexConeOn (W ⊓ LinearMap.ker (f : U →ₗ[ℝ] ℝ)) (P ∩ {x | f x = 0}) where
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
    rcases h.trichotomy hxW with hP | h0 | hnP
    · exact Or.inl ⟨hP, hfx⟩
    · exact Or.inr (Or.inl h0)
    · refine Or.inr (Or.inr ⟨hnP, ?_⟩)
      simp only [Set.mem_setOf_eq, map_neg, hfx, neg_zero]
  zero_notMem := fun hc => h.zero_notMem hc.1
  neg_notMem := by
    rintro x ⟨hxP, _⟩ ⟨hnP, _⟩
    exact h.neg_notMem hxP hnP

end IsLexConeOn

/-! ### The induced order -/

/-- The strict order induced by a cone `P`: `x < y` when `y - x ∈ P`. -/
def lexLT (P : Set U) (x y : U) : Prop := y - x ∈ P

omit [FiniteDimensional ℝ U] in
theorem lexLT_irrefl {W : Submodule ℝ U} {P : Set U} (h : IsLexConeOn W P) (x : U) :
    ¬ lexLT P x x := by
  intro hx
  rw [lexLT, sub_self] at hx
  exact h.zero_notMem hx

omit [FiniteDimensional ℝ U] in
theorem lexLT_trans {W : Submodule ℝ U} {P : Set U} (h : IsLexConeOn W P) {x y z : U} :
    lexLT P x y → lexLT P y z → lexLT P x z := by
  intro hxy hyz
  have hz : z - x = (z - y) + (y - x) := by abel
  rw [lexLT, hz]
  exact h.add_mem hyz hxy

omit [FiniteDimensional ℝ U] in
theorem lexLT_trichotomy {W : Submodule ℝ U} {P : Set U} (h : IsLexConeOn W P) {x y : U}
    (hx : x ∈ W) (hy : y ∈ W) : lexLT P x y ∨ x = y ∨ lexLT P y x := by
  rcases h.trichotomy (W.sub_mem hy hx) with hP | h0 | hnP
  · exact Or.inl hP
  · exact Or.inr (Or.inl (sub_eq_zero.1 h0).symm)
  · refine Or.inr (Or.inr ?_)
    rw [lexLT]
    simpa using hnP

omit [NormedSpace ℝ U] [FiniteDimensional ℝ U] in
theorem lexLT_add_right {P : Set U} {x y : U} (z : U) :
    lexLT P x y → lexLT P (x + z) (y + z) := by
  intro hxy
  have hz : y + z - (x + z) = y - x := by abel
  rw [lexLT, hz]
  exact hxy

omit [FiniteDimensional ℝ U] in
theorem lexLT_smul {W : Submodule ℝ U} {P : Set U} (h : IsLexConeOn W P) {c : ℝ}
    (hc : 0 < c) {x y : U} : lexLT P x y → lexLT P (c • x) (c • y) := by
  intro hxy
  rw [lexLT] at hxy ⊢
  rw [← smul_sub]
  exact h.smul_mem hc hxy

/-! ## Part B — the normal form -/

/-- The lexicographic cone of a family of functionals, relativized to `W`: the points of `W`
whose first nonvanishing coordinate is positive. -/
def lexCone (W : Submodule ℝ U) {k : ℕ} (l : Fin k → (U →L[ℝ] ℝ)) : Set U :=
  {x | x ∈ W ∧ ∃ j : Fin k, 0 < l j x ∧ ∀ i : Fin k, i < j → l i x = 0}

omit [FiniteDimensional ℝ U] in
theorem mem_lexCone_iff {W : Submodule ℝ U} {k : ℕ} {l : Fin k → (U →L[ℝ] ℝ)} {x : U} :
    x ∈ lexCone W l ↔ x ∈ W ∧ ∃ j : Fin k, 0 < l j x ∧ ∀ i : Fin k, i < j → l i x = 0 :=
  Iff.rfl

omit [FiniteDimensional ℝ U] in
/-- If some functional of the family does not vanish at `x`, there is a least such index. -/
theorem exists_least_ne_zero {k : ℕ} {l : Fin k → (U →L[ℝ] ℝ)} {x : U} {i₀ : Fin k}
    (hi₀ : l i₀ x ≠ 0) :
    ∃ j : Fin k, l j x ≠ 0 ∧ ∀ i : Fin k, i < j → l i x = 0 := by
  classical
  set S : Finset (Fin k) := Finset.univ.filter (fun j => l j x ≠ 0) with hS
  have hne : S.Nonempty := ⟨i₀, by simp [hS, hi₀]⟩
  refine ⟨S.min' hne, ?_, ?_⟩
  · have := S.min'_mem hne
    simpa [hS] using this
  · intro i hi
    by_contra hne'
    have hiS : i ∈ S := by simp [hS, hne']
    exact absurd (S.min'_le i hiS) (not_le.2 hi)

omit [FiniteDimensional ℝ U] in
/-- A lexicographic cone is a lex cone, provided the functionals separate the points of `W`. -/
theorem isLexConeOn_lexCone {W : Submodule ℝ U} {k : ℕ} {l : Fin k → (U →L[ℝ] ℝ)}
    (hsep : ∀ x ∈ W, (∀ i, l i x = 0) → x = 0) :
    IsLexConeOn W (lexCone W l) where
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
      obtain ⟨j, hj, hj0⟩ := exists_least_ne_zero (l := l) (x := x) hi₀
      rcases lt_or_gt_of_ne hj with hneg | hpos
      · refine Or.inr (Or.inr ⟨W.neg_mem hxW, j, ?_, ?_⟩)
        · rw [map_neg]; linarith
        · intro i hi
          rw [map_neg, hj0 i hi, neg_zero]
      · exact Or.inl ⟨hxW, j, hpos, hj0⟩
  zero_notMem := by
    rintro ⟨-, j, hj, -⟩
    simp at hj
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

/-- Rank-nullity for a functional not vanishing on `W`: cutting `W` by the kernel drops the
rank by exactly one. -/
theorem finrank_inf_ker_add_one {W : Submodule ℝ U} {f : U →L[ℝ] ℝ} {v : U} (hv : v ∈ W)
    (hfv : f v ≠ 0) :
    Module.finrank ℝ (W ⊓ LinearMap.ker (f : U →ₗ[ℝ] ℝ) : Submodule ℝ U) + 1
      = Module.finrank ℝ W := by
  classical
  set g : (↑W : Type _) →ₗ[ℝ] ℝ := (f : U →ₗ[ℝ] ℝ).comp W.subtype with hg
  have hrk : Module.finrank ℝ (LinearMap.range g) + Module.finrank ℝ (LinearMap.ker g)
      = Module.finrank ℝ W := LinearMap.finrank_range_add_finrank_ker g
  -- the range is all of `ℝ`, hence of rank one
  have hrange_ne : LinearMap.range g ≠ ⊥ := by
    intro hbot
    have : g ⟨v, hv⟩ = 0 := by
      have : g ⟨v, hv⟩ ∈ LinearMap.range g := LinearMap.mem_range_self _ _
      rw [hbot] at this
      simpa using this
    exact hfv this
  have hrange_le : Module.finrank ℝ (LinearMap.range g) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range g)
    simpa using this
  have hrange_pos : Module.finrank ℝ (LinearMap.range g) ≠ 0 := by
    intro h0
    exact hrange_ne (Submodule.finrank_eq_zero.1 h0)
  have hrange_one : Module.finrank ℝ (LinearMap.range g) = 1 := by omega
  -- the kernel corresponds to `W ⊓ ker f`
  have hker : Module.finrank ℝ (LinearMap.ker g)
      = Module.finrank ℝ (W ⊓ LinearMap.ker (f : U →ₗ[ℝ] ℝ) : Submodule ℝ U) := by
    have hkg : LinearMap.ker g = Submodule.comap W.subtype (LinearMap.ker (f : U →ₗ[ℝ] ℝ)) := by
      rw [hg, LinearMap.ker_comp]
    rw [← Submodule.finrank_map_subtype_eq W (LinearMap.ker g), hkg,
      Submodule.map_comap_subtype]
  omega

/-- Auxiliary form of Lemma 3.2, set up for strong induction on the rank of `W`. -/
theorem exists_functionals_aux (n : ℕ) : ∀ (W : Submodule ℝ U) (P : Set U),
    Module.finrank ℝ W = n → IsLexConeOn W P →
    ∃ (k : ℕ) (l : Fin k → (U →L[ℝ] ℝ)),
      k = Module.finrank ℝ W ∧
      (∀ x ∈ W, (∀ i, l i x = 0) → x = 0) ∧
      P = lexCone W l := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W P hn h
    by_cases hW : W = ⊥
    · subst hW
      refine ⟨0, Fin.elim0, by simp, ?_, ?_⟩
      · intro x hx _
        simpa using hx
      · ext x
        simp only [lexCone, Set.mem_setOf_eq]
        constructor
        · intro hxP
          have hx0 : x = 0 := by simpa using h.mem_of_mem hxP
          exact absurd (hx0 ▸ hxP) h.zero_notMem
        · rintro ⟨-, j, -⟩
          exact j.elim0
    · obtain ⟨f, ⟨v, hvW, hfv⟩, hf⟩ := h.exists_nonneg_functional hW
      set W' : Submodule ℝ U := W ⊓ LinearMap.ker (f : U →ₗ[ℝ] ℝ) with hW'
      have hrank : Module.finrank ℝ W' + 1 = Module.finrank ℝ W :=
        finrank_inf_ker_add_one hvW hfv
      obtain ⟨k', l', hk', hsep', hP'⟩ :=
        ih (Module.finrank ℝ W') (by omega) W' (P ∩ {x | f x = 0}) rfl (h.restrict hf)
      refine ⟨k' + 1, Fin.cons f l', by omega, ?_, ?_⟩
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
            exact h.mem_of_pos hf hxW hjpos
          · have hf0 : f x = 0 := by
              have := hj0 0 (Fin.succ_pos j')
              rwa [Fin.cons_zero] at this
            have hmem : x ∈ lexCone W' l' := by
              refine ⟨⟨hxW, hf0⟩, j', ?_, ?_⟩
              · rwa [Fin.cons_succ] at hjpos
              · intro i' hi'
                have := hj0 i'.succ (Fin.succ_lt_succ_iff.2 hi')
                rwa [Fin.cons_succ] at this
            rw [← hP'] at hmem
            exact hmem.1

/-- Lemma 3.2: every lex cone on `W` is a lexicographic cone of `finrank ℝ W` functionals
separating the points of `W`. -/
theorem exists_functionals {W : Submodule ℝ U} {P : Set U} (h : IsLexConeOn W P) :
    ∃ (k : ℕ) (l : Fin k → (U →L[ℝ] ℝ)),
      k = Module.finrank ℝ W ∧
      (∀ x ∈ W, (∀ i, l i x = 0) → x = 0) ∧
      P = lexCone W l :=
  exists_functionals_aux (Module.finrank ℝ W) W P rfl h

end ConvexFilter
