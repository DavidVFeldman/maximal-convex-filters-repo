import ConvexFilters.Primal

/-!
# Primal surjectivity, and Theorem 1.2 as a bijection

WO-06b established Theorem 1.2 in existence-and-uniqueness shape: an admissible pair
`(A, Q)` determines a primal triple `(A, W, P)` satisfying `IsAdmissiblePrimal`, and the
transport is reversible. This file supplies the missing step, that the map from admissible
pairs to primal triples is *onto* the abstract triples satisfying `IsAdmissiblePrimal`, and
packages Theorem 1.2 as a bijection.

## Part A — the reversal

`ConvexFilter.exists_functionals` presents a lex cone on `W` as `lexCone W l`, which is
**first**-nonzero-positive in `l`, while `ConvexFilter.primalCone_eq_lexCone` speaks of the
**last**-nonzero-positive cone in the coordinates of an adapted basis (see
`notes/CONVENTIONS.md` §7). `exists_dual_family` produces the basis of `W` dual to `l`, and
`exists_reversing_basis` reindexes it by `Fin.rev` and extends it to a basis of `V` in which
the two presentations agree.

* `ConvexFilter.exists_dual_family`;
* `ConvexFilter.exists_reversing_basis_coord` — the reversal with the coordinate identity
  `coordAt b 0 i x = l i.rev x` on `W`, which is what the later parts consume;
* `ConvexFilter.exists_reversing_basis`;
* `ConvexFilter.flag_eq_span_of_reversing` — under the reversal the `r`-th flag of `l` is the
  span of the first `m - r` basis vectors.

## Part B — the construction

* `ConvexFilter.isLexConeModOn_Q0` — the coordinate cone `Q0 b m` is a lex cone on the whole
  dual modulo the annihilator of the span of the first `m` basis vectors;
* `ConvexFilter.exists_admissible_of_isAdmissiblePrimal` — every abstract primal triple comes
  from an admissible pair.

## Part C — the bijection

* `ConvexFilter.classification_primal_bijective`;
* `ConvexFilter.classificationPrimalEquiv`.
-/

open Module

namespace ConvexFilter

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-! ## Part A — the reversal -/

section PartA

/-- The basis of `W` dual to a separating family `l` of functionals of the right cardinality:
`l i (w j) = δᵢⱼ`. -/
theorem exists_dual_family {W : Submodule ℝ V} {m : ℕ} {l : Fin m → (V →L[ℝ] ℝ)}
    (hm : m = Module.finrank ℝ W) (hsep : ∀ x ∈ W, (∀ i, l i x = 0) → x ∈ (⊥ : Submodule ℝ V)) :
    ∃ w : Fin m → V, (∀ i, w i ∈ W) ∧ LinearIndependent ℝ w ∧
      (∀ i j, l i (w j) = if i = j then 1 else 0) ∧
      Submodule.span ℝ (Set.range w) = W := by
  classical
  -- the family `l`, read as a linear map from `W` to `Fin m → ℝ`, is injective, hence
  -- bijective by equality of ranks
  set T : W →ₗ[ℝ] (Fin m → ℝ) :=
    { toFun := fun x i => l i (x : V)
      map_add' := by intro x y; funext i; simp
      map_smul' := by intro c x; funext i; simp } with hT
  have hker : LinearMap.ker T = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hx' : ∀ i, l i (x : V) = 0 := by
      intro i
      have hx0 : T x = 0 := hx
      calc l i (x : V) = T x i := rfl
        _ = 0 := by rw [hx0]; rfl
    have := hsep (x : V) x.2 hx'
    exact Subtype.ext (by simpa using this)
  have hinj : Function.Injective T := LinearMap.ker_eq_bot.1 hker
  have hrk : finrank ℝ W = finrank ℝ (Fin m → ℝ) := by simp [← hm]
  have hsurj : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrk).1 hinj
  choose ww hww using fun j : Fin m => hsurj (Pi.single j 1)
  have hdual : ∀ i j : Fin m, l i ((ww j : V)) = if i = j then 1 else 0 := by
    intro i j
    have h1 : T (ww j) = Pi.single j 1 := hww j
    have h2 : l i ((ww j : V)) = Pi.single (M := fun _ : Fin m => ℝ) j 1 i := by
      rw [← h1]; rfl
    rw [h2, Pi.single_apply]
  have hli : LinearIndependent ℝ (fun j => (ww j : V)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hgi := congrArg (l i) hg
    rw [map_sum, map_zero] at hgi
    simp only [map_smul, smul_eq_mul, hdual] at hgi
    simpa using hgi
  refine ⟨fun j => (ww j : V), fun j => (ww j).2, hli, hdual, ?_⟩
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [Submodule.span_le]
    rintro x ⟨j, rfl⟩
    exact (ww j).2
  · rw [finrank_span_eq_card hli]
    simp [← hm]

/-- The reversing basis, with the coordinate identity that drives Part A: for `x ∈ W` the
`i`-th coordinate of `x` in the new basis is `l (Fin.rev i) x`. -/
theorem exists_reversing_basis_coord {W : Submodule ℝ V} {m : ℕ} {l : Fin m → (V →L[ℝ] ℝ)}
    (hm : m = Module.finrank ℝ W) (hsep : ∀ x ∈ W, (∀ i, l i x = 0) → x ∈ (⊥ : Submodule ℝ V)) :
    ∃ b : Basis (Fin (Module.finrank ℝ V)) ℝ V,
      Submodule.span ℝ (Set.range (fun i : Fin m => basisAt b (i : ℕ))) = W ∧
      ∀ x ∈ W, ∀ i : Fin m, coordAt b 0 (i : ℕ) x = l i.rev x := by
  classical
  obtain ⟨w, hwW, hli, hdual, hspanw⟩ := exists_dual_family hm hsep
  have hmn : m ≤ finrank ℝ V := by
    rw [hm]; exact Submodule.finrank_le W
  have hlirev : LinearIndependent ℝ (fun i : Fin m => w i.rev) :=
    hli.comp _ Fin.rev_injective
  obtain ⟨b, hb⟩ := Adapted.exists_basis_extending (fun i : Fin m => w i.rev) hlirev
  have hbb : ∀ i : Fin m, basisAt b (i : ℕ) = w i.rev := fun i =>
    (Adapted.basisAt_eq b (i : ℕ)).symm.trans (hb i)
  have hrange : Set.range (fun i : Fin m => basisAt b (i : ℕ)) = Set.range w := by
    have h1 : (fun i : Fin m => basisAt b (i : ℕ)) = w ∘ Fin.rev := by
      funext i; exact hbb i
    rw [h1]
    exact Function.Surjective.range_comp Fin.rev_surjective w
  have hspan : Submodule.span ℝ (Set.range (fun i : Fin m => basisAt b (i : ℕ))) = W := by
    rw [hrange, hspanw]
  refine ⟨b, hspan, ?_⟩
  intro x hx i
  rw [← hspan] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      have hjn : (j : ℕ) < finrank ℝ V := lt_of_lt_of_le j.2 hmn
      show coordAt b 0 (i : ℕ) (basisAt b (j : ℕ)) = l i.rev (basisAt b (j : ℕ))
      rw [coordAt_basisAt hjn, hbb j, hdual i.rev j.rev]
      simp [Fin.rev_inj, Fin.val_eq_val]
  | zero => rw [coordAt_zero_zero, map_zero]
  | add y z _ _ hy hz => rw [coordAt_zero_add, hy, hz, map_add]
  | smul c y _ hy => rw [coordAt_zero_smul, hy, map_smul, smul_eq_mul]

omit [FiniteDimensional ℝ V] in
/-- The reversal, as an identity of sets: in the coordinates of a reversing basis, the
first-nonzero-positive cone of `l` is the last-nonzero-positive cone of the coordinates. -/
theorem lexCone_eq_lastPos_of_reversing {W : Submodule ℝ V} {m : ℕ} {l : Fin m → (V →L[ℝ] ℝ)}
    {b : Basis (Fin (Module.finrank ℝ V)) ℝ V}
    (hcoord : ∀ x ∈ W, ∀ i : Fin m, coordAt b 0 (i : ℕ) x = l i.rev x) :
    lexCone W l = {x | x ∈ W ∧ ∃ j < m, 0 < coordAt b 0 j x ∧
                ∀ i, j < i → i < m → coordAt b 0 i x = 0} := by
  ext x
  constructor
  · rintro ⟨hxW, j, hj, hj0⟩
    refine ⟨hxW, (j.rev : ℕ), j.rev.2, ?_, ?_⟩
    · rw [hcoord x hxW j.rev, Fin.rev_rev]
      exact hj
    · intro i hji him
      rw [hcoord x hxW ⟨i, him⟩]
      refine hj0 _ ?_
      have hlt : j.rev < (⟨i, him⟩ : Fin m) := by
        simp only [Fin.lt_def]
        exact hji
      have := (Fin.rev_lt_rev (i := (⟨i, him⟩ : Fin m)) (j := j.rev)).2 hlt
      rwa [Fin.rev_rev] at this
  · rintro ⟨hxW, j, hjm, hj, hjmax⟩
    refine ⟨hxW, (⟨j, hjm⟩ : Fin m).rev, ?_, ?_⟩
    · have hh : coordAt b 0 j x = l (⟨j, hjm⟩ : Fin m).rev x := hcoord x hxW ⟨j, hjm⟩
      rw [← hh]
      exact hj
    · intro i hi
      have hli : l i x = coordAt b 0 (i.rev : ℕ) x := by
        rw [hcoord x hxW i.rev, Fin.rev_rev]
      rw [hli]
      refine hjmax _ ?_ i.rev.2
      have h := (Fin.rev_lt_rev (i := (⟨j, hjm⟩ : Fin m).rev) (j := i)).2 hi
      rw [Fin.rev_rev] at h
      exact h

/-- **Part A.** A lex cone presented as `lexCone W l`, first-nonzero-positive in `l`, is the
last-nonzero-positive cone in the coordinates of a suitable basis of `V` whose first `m`
vectors span `W`. -/
theorem exists_reversing_basis {W : Submodule ℝ V} {P : Set V} {m : ℕ}
    {l : Fin m → (V →L[ℝ] ℝ)}
    (hm : m = Module.finrank ℝ W) (hsep : ∀ x ∈ W, (∀ i, l i x = 0) → x ∈ (⊥ : Submodule ℝ V))
    (hP : P = lexCone W l) :
    ∃ (b : Basis (Fin (Module.finrank ℝ V)) ℝ V),
      Submodule.span ℝ (Set.range (fun i : Fin m => basisAt b (i : ℕ))) = W ∧
      P = {x | x ∈ W ∧ ∃ j < m, 0 < coordAt b 0 j x ∧
                ∀ i, j < i → i < m → coordAt b 0 i x = 0} := by
  obtain ⟨b, hspan, hcoord⟩ := exists_reversing_basis_coord hm hsep
  exact ⟨b, hspan, by rw [hP, lexCone_eq_lastPos_of_reversing hcoord]⟩

omit [FiniteDimensional ℝ V] in
/-- Under the reversal, the `r`-th flag of `l` is the span of the first `m - r` basis
vectors. -/
theorem flag_eq_span_of_reversing {W : Submodule ℝ V} {m : ℕ} {l : Fin m → (V →L[ℝ] ℝ)}
    {b : Basis (Fin (Module.finrank ℝ V)) ℝ V}
    (hspan : Submodule.span ℝ (Set.range (fun i : Fin m => basisAt b (i : ℕ))) = W)
    (hcoord : ∀ x ∈ W, ∀ i : Fin m, coordAt b 0 (i : ℕ) x = l i.rev x)
    {r : ℕ} (hr : r ≤ m) :
    flag W l r
      = Submodule.span ℝ (Set.range (fun i : Fin (m - r) => basisAt b (i : ℕ))) := by
  have hsub : Submodule.span ℝ (Set.range (fun i : Fin (m - r) => basisAt b (i : ℕ))) ≤ W := by
    rw [← hspan]
    refine Submodule.span_mono ?_
    rintro y ⟨i, rfl⟩
    exact ⟨⟨(i : ℕ), lt_of_lt_of_le i.2 (Nat.sub_le m r)⟩, rfl⟩
  ext x
  constructor
  · rintro ⟨hxW, hx0⟩
    rw [mem_span_iff_coordAt]
    intro i hi
    rcases lt_or_ge i m with him | him
    · rw [hcoord x hxW ⟨i, him⟩]
      refine hx0 _ ?_
      have hval : ((⟨i, him⟩ : Fin m).rev : ℕ) = m - (i + 1) := by simp [Fin.val_rev]
      rw [hval]
      omega
    · have hxs : x ∈ Submodule.span ℝ (Set.range (fun i : Fin m => basisAt b (i : ℕ))) := by
        rw [hspan]; exact hxW
      exact (mem_span_iff_coordAt x).1 hxs i him
  · intro hx
    have hxW : x ∈ W := hsub hx
    refine ⟨hxW, fun i hi => ?_⟩
    have hli : l i x = coordAt b 0 (i.rev : ℕ) x := by
      rw [hcoord x hxW i.rev, Fin.rev_rev]
    rw [hli]
    refine (mem_span_iff_coordAt x).1 hx _ ?_
    have hval : ((i.rev : Fin m) : ℕ) = m - ((i : ℕ) + 1) := by simp [Fin.val_rev]
    rw [hval]
    omega

end PartA

/-! ## Part B — the construction -/

section PartB

variable {n : ℕ} {b : Basis (Fin n) ℝ V} {m : ℕ}

omit [FiniteDimensional ℝ V] in
/-- Membership in the annihilator of the span of the first `k` basis vectors, in
coordinates. -/
theorem mem_annih_span_basisAt_iff {k : ℕ} (u : V →L[ℝ] ℝ) :
    u ∈ annih (Submodule.span ℝ (Set.range (fun i : Fin k => basisAt b (i : ℕ)))) ↔
      ∀ i, i < k → u (basisAt b i) = 0 := by
  rw [← SetLike.mem_coe, ← M0_eq_annih b k]
  exact Iff.rfl

omit [FiniteDimensional ℝ V] in
/-- The exceptional submodule of `Q0 b m`, in the annihilator form: a functional is
exceptional for `Q0 b m` exactly when it annihilates the span of the first `m` basis
vectors. -/
theorem mem_annih_span_iff_notMem_Q0 (u : V →L[ℝ] ℝ) :
    u ∈ (annih (Submodule.span ℝ (Set.range (fun i : Fin m => basisAt b (i : ℕ)))) :
        Set (V →L[ℝ] ℝ)) ↔ (u ∉ Q0 b m ∧ -u ∉ Q0 b m) := by
  rw [SetLike.mem_coe, mem_annih_span_basisAt_iff]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rintro ⟨j, hjm, hj, -⟩
      rw [h j hjm] at hj
      exact lt_irrefl 0 hj
    · rintro ⟨j, hjm, hj, -⟩
      rw [ContinuousLinearMap.neg_apply, h j hjm] at hj
      simp at hj
  · rintro ⟨h1, h2⟩
    rcases mem_M0_or_Q0_or_neg_Q0 (b := b) (m := m) u with h | h | h
    · exact h
    · exact absurd h h1
    · exact absurd h h2

omit [FiniteDimensional ℝ V] in
/-- The cone `Q0 b m` is a lex cone on the whole dual modulo the annihilator of the span of
the first `m` basis vectors. This is the coordinate statement that `Q0` is a lex cone modulo
`M0`. -/
theorem isLexConeModOn_Q0 :
    Adapted.IsLexConeModOn ⊤
      (annih (Submodule.span ℝ (Set.range (fun i : Fin m => basisAt b (i : ℕ))))) (Q0 b m) where
  M_le := le_top
  mem_of_mem := fun _ _ => trivial
  add_mem := by
    rintro u u' ⟨j, hjm, hj, hj0⟩ ⟨j', hj'm, hj', hj'0⟩
    rcases lt_trichotomy j j' with h | h | h
    · refine ⟨j, hjm, ?_, ?_⟩
      · rw [ContinuousLinearMap.add_apply, hj'0 j h, add_zero]; exact hj
      · intro i hi
        rw [ContinuousLinearMap.add_apply, hj0 i hi, hj'0 i (hi.trans h), add_zero]
    · subst h
      refine ⟨j, hjm, ?_, ?_⟩
      · rw [ContinuousLinearMap.add_apply]; linarith
      · intro i hi
        rw [ContinuousLinearMap.add_apply, hj0 i hi, hj'0 i hi, add_zero]
    · refine ⟨j', hj'm, ?_, ?_⟩
      · rw [ContinuousLinearMap.add_apply, hj0 j' h, zero_add]; exact hj'
      · intro i hi
        rw [ContinuousLinearMap.add_apply, hj0 i (hi.trans h), hj'0 i hi, add_zero]
  smul_mem := by
    rintro c hc u ⟨j, hjm, hj, hj0⟩
    refine ⟨j, hjm, ?_, ?_⟩
    · rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
      exact mul_pos hc hj
    · intro i hi
      rw [ContinuousLinearMap.smul_apply, hj0 i hi, smul_zero]
  trichotomy := by
    intro u _
    rcases mem_M0_or_Q0_or_neg_Q0 (b := b) (m := m) u with h | h | h
    · exact Or.inr (Or.inl ((mem_annih_span_basisAt_iff u).2 h))
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  notMem_M := by
    rintro u ⟨j, hjm, hj, -⟩ hu
    rw [(mem_annih_span_basisAt_iff u).1 hu j hjm] at hj
    exact lt_irrefl 0 hj
  neg_notMem := by
    rintro u ⟨j, hjm, hj, hj0⟩ ⟨j', hj'm, hj', hj'0⟩
    rcases lt_trichotomy j j' with h | h | h
    · have hneg := hj'0 j h
      rw [ContinuousLinearMap.neg_apply] at hneg
      have hz : u (basisAt b j) = 0 := by linarith [neg_eq_zero.1 hneg]
      rw [hz] at hj
      exact lt_irrefl 0 hj
    · subst h
      rw [ContinuousLinearMap.neg_apply] at hj'
      linarith
    · have hz := hj0 j' h
      rw [ContinuousLinearMap.neg_apply, hz] at hj'
      simp at hj'

omit [FiniteDimensional ℝ V] in
/-- The annihilator of the span of the first `d` basis vectors is order convex for
`Q0 b m`. No relation between `d` and `m` is needed. -/
theorem isOrderConvex_Q0 {d : ℕ} :
    IsOrderConvex (Q0 b m)
      (annih (Submodule.span ℝ (Set.range (fun i : Fin d => basisAt b (i : ℕ))))) := by
  rintro w v ⟨j, hjm, hj, hj0⟩ ⟨j', hj'm, hj', hj'0⟩ hv
  have hvco : ∀ i, i < d → v (basisAt b i) = 0 := (mem_annih_span_basisAt_iff v).1 hv
  refine (mem_annih_span_basisAt_iff w).2 fun i hi => ?_
  -- the leading index of `w` is at least `d`
  have hjd : d ≤ j := by
    by_contra hcon
    push_neg at hcon
    have hsub : (v - w) (basisAt b j) = -w (basisAt b j) := by
      rw [ContinuousLinearMap.sub_apply, hvco j hcon, zero_sub]
    rcases lt_trichotomy j' j with h | h | h
    · have h1 : w (basisAt b j') = 0 := hj0 j' h
      have h2 : v (basisAt b j') = 0 := hvco j' (lt_trans h hcon)
      rw [ContinuousLinearMap.sub_apply, h1, h2, sub_zero] at hj'
      exact lt_irrefl 0 hj'
    · subst h
      rw [hsub] at hj'
      linarith
    · have hzz := hj'0 j h
      rw [hsub] at hzz
      have hz : w (basisAt b j) = 0 := by linarith [neg_eq_zero.1 hzz]
      rw [hz] at hj
      exact lt_irrefl 0 hj
  exact hj0 i (lt_of_lt_of_le hi hjd)

/-- **Part B: surjectivity of the primal transport.** Every abstract primal triple satisfying
the clauses of Theorem 1.2 is the primal triple of an admissible pair. -/
theorem exists_admissible_of_isAdmissiblePrimal
    {A : AffineSubspace ℝ V} {W : Submodule ℝ V} {P : Set V}
    (h : IsAdmissiblePrimal A W P) :
    ∃ Q : Set (V →L[ℝ] ℝ), IsAdmissible A Q ∧
      primalSpace Q = W ∧ primalCone Q (primalSpace Q) = P := by
  by_cases hbot : A.direction = ⊥
  · -- degenerate case: `A` is a point, `W` is trivial and `P` is empty
    have hW : W = ⊥ := h.degenerate hbot
    have hP : P = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hx
      have hxW := h.isLexCone.mem_of_mem hx
      rw [hW, Submodule.mem_bot] at hxW
      rw [hxW] at hx
      exact h.isLexCone.zero_notMem hx
    refine ⟨∅, ?_, ?_, ?_⟩
    · refine ⟨h.A_nonempty, ⟨⊤, ?_, ?_, ?_⟩, ?_, fun _ => rfl⟩
      · intro u
        simp
      · exact
          { M_le := le_top
            mem_of_mem := fun _ hx => absurd hx (Set.notMem_empty _)
            add_mem := fun _ _ hx _ => absurd hx (Set.notMem_empty _)
            smul_mem := fun _ _ _ hx => absurd hx (Set.notMem_empty _)
            trichotomy := fun _ _ => Or.inr (Or.inl trivial)
            notMem_M := fun _ hx => absurd hx (Set.notMem_empty _)
            neg_notMem := fun _ hx => absurd hx (Set.notMem_empty _) }
      · rw [hbot, annih_bot]
      · intro w v hw _ _
        exact absurd hw (Set.notMem_empty _)
    · rw [primalSpace_eq_bot_of_eq_empty rfl, hW]
    · rw [primalCone_eq_empty_of_eq_empty rfl, hP]
  · -- main case
    obtain ⟨m, l, hm, hsep', hPl⟩ := exists_functionals h.isLexCone
    have hsep : ∀ x ∈ W, (∀ i, l i x = 0) → x ∈ (⊥ : Submodule ℝ V) := by
      intro x hx h0
      simpa using hsep' x hx h0
    obtain ⟨b, hspan, hcoord⟩ := exists_reversing_basis_coord hm hsep
    have hmn : m ≤ finrank ℝ V := by
      rw [hm]; exact Submodule.finrank_le W
    -- the flag position of `A.direction`
    have hocl : IsOrderConvex (lexCone W l) A.direction := by
      rw [← hPl]; exact h.orderConvex
    obtain ⟨r, hrm, hflag⟩ := exists_eq_flag hsep' h.direction_le hocl
    have hdir : A.direction
        = Submodule.span ℝ (Set.range (fun i : Fin (m - r) => basisAt b (i : ℕ))) := by
      rw [hflag]
      exact flag_eq_span_of_reversing hspan hcoord hrm
    have hMle : annih (Submodule.span ℝ (Set.range (fun i : Fin m => basisAt b (i : ℕ))))
        ≤ annih A.direction := by
      intro u hu v hv
      exact hu v (by rw [hspan]; exact h.direction_le hv)
    have hPS : primalSpace (Q0 b m) = W := by
      rw [primalSpace_eq_preAnnih (M := annih
          (Submodule.span ℝ (Set.range (fun i : Fin m => basisAt b (i : ℕ)))))
        (fun u => mem_annih_span_iff_notMem_Q0 u), preAnnih_annih, hspan]
    refine ⟨Q0 b m, ⟨h.A_nonempty, ⟨_, fun u => mem_annih_span_iff_notMem_Q0 u,
      isLexConeModOn_Q0, hMle⟩, ?_, fun hcon => absurd hcon hbot⟩, hPS, ?_⟩
    · rw [hdir]
      exact isOrderConvex_Q0
    · rw [hPS, ← hspan, primalCone_eq_lexCone b m hmn, hspan, hPl,
        lexCone_eq_lastPos_of_reversing hcoord]

end PartB

/-! ## Part C — the bijection -/

section PartC

/-- **Theorem 1.2 as a bijection**, in existence-and-uniqueness shape: for every abstract
primal triple there is exactly one maximal convex filter with that flat, primal subspace and
primal cone. -/
theorem classification_primal_bijective :
    ∀ (A : AffineSubspace ℝ V) (W : Submodule ℝ V) (P : Set V), IsAdmissiblePrimal A W P →
      ∃! F : {G : ConvexFilter V // IsMaximal G},
        Aset (F : ConvexFilter V) = (A : Set V) ∧
        primalSpace (Qset (F : ConvexFilter V)) = W ∧
        primalCone (Qset (F : ConvexFilter V)) (primalSpace (Qset (F : ConvexFilter V))) = P := by
  intro A W P h
  obtain ⟨Q, hQ, hW, hP⟩ := exists_admissible_of_isAdmissiblePrimal h
  obtain ⟨F, hFspec, -⟩ := classification A Q hQ
  refine ⟨F, ⟨hFspec.1, by rw [hFspec.2, hW], by rw [hFspec.2, hP]⟩, ?_⟩
  rintro G ⟨hAG, -, hPG⟩
  refine Subtype.ext (eq_of_primal_data G.2 F.2 ?_ ?_)
  · rw [hAG, hFspec.1]
  · rw [hPG, hFspec.2, hP]

/-- **Theorem 1.2 as a bijection**: the maximal convex filters are in bijection with the
admissible primal triples `(A, W, P)`. -/
noncomputable def classificationPrimalEquiv :
    {F : ConvexFilter V // IsMaximal F} ≃
      {t : AffineSubspace ℝ V × Submodule ℝ V × Set V // IsAdmissiblePrimal t.1 t.2.1 t.2.2} where
  toFun F := ⟨(AsetAff (F : ConvexFilter V) F.2, primalSpace (Qset (F : ConvexFilter V)),
      primalCone (Qset (F : ConvexFilter V)) (primalSpace (Qset (F : ConvexFilter V)))),
    isAdmissiblePrimal_of_isAdmissible (isAdmissible_invariants F.2)⟩
  invFun t := (classification_primal_bijective t.1.1 t.1.2.1 t.1.2.2 t.2).choose
  left_inv := by
    rintro ⟨F, hF⟩
    obtain ⟨hspec, -⟩ := (classification_primal_bijective (AsetAff F hF)
      (primalSpace (Qset F)) (primalCone (Qset F) (primalSpace (Qset F)))
      (isAdmissiblePrimal_of_isAdmissible (isAdmissible_invariants hF))).choose_spec
    set G := (classification_primal_bijective (AsetAff F hF)
      (primalSpace (Qset F)) (primalCone (Qset F) (primalSpace (Qset F)))
      (isAdmissiblePrimal_of_isAdmissible (isAdmissible_invariants hF))).choose with hG
    refine Subtype.ext (eq_of_primal_data G.2 hF ?_ hspec.2.2)
    rw [hspec.1, coe_AsetAff hF]
  right_inv := by
    rintro ⟨⟨A, W, P⟩, hAWP⟩
    obtain ⟨hspec, -⟩ := (classification_primal_bijective A W P hAWP).choose_spec
    set G := (classification_primal_bijective A W P hAWP).choose with hG
    refine Subtype.ext ?_
    have hA : ((AsetAff (G : ConvexFilter V) G.2 : AffineSubspace ℝ V) : Set V) = (A : Set V) := by
      rw [coe_AsetAff G.2, hspec.1]
    exact Prod.ext (SetLike.coe_injective hA) (Prod.ext hspec.2.1 hspec.2.2)

theorem classificationPrimalEquiv_apply (F : ConvexFilter V) (hF : IsMaximal F) :
    (classificationPrimalEquiv ⟨F, hF⟩ : AffineSubspace ℝ V × Submodule ℝ V × Set V)
      = (AsetAff F hF, primalSpace (Qset F), primalCone (Qset F) (primalSpace (Qset F))) := rfl

end PartC

end ConvexFilter
