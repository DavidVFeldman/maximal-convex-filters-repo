import ConvexFilters.Separation

/-!
# Convex filters: relative separation

This file is Lemma 4.1 of the paper. It strengthens `exists_separating` by controlling the
separating functional on a prescribed affine subspace containing both sets: if `C` and `D`
are disjoint nonempty convex subsets of an affine subspace `T`, then they are separated by
a functional which is *nonconstant on `T`*, i.e. does not vanish on `T.direction`.

The proof does not repeat the work of `Separation.lean`. Writing `W = T.direction` and
choosing a linear complement `U` of `W`, the thickened sets `C + U` and `D + U` are still
disjoint, convex and nonempty, so `exists_separating` applies to them and produces a
nonzero `u`. Boundedness of `u` on `C + U` forces `u` to vanish on `U`
(`eq_zero_on_of_bddAbove_add`), and as `W ⊔ U = ⊤` and `u ≠ 0`, the functional `u` cannot
vanish on `W` as well.
-/

open Pointwise

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

namespace ConvexFilter

omit [FiniteDimensional ℝ V] in
/-- A functional bounded above on a set of the form `E + U`, with `E` nonempty and `U` a
submodule, vanishes on `U`. -/
theorem eq_zero_on_of_bddAbove_add {u : V →L[ℝ] ℝ} {U : Submodule ℝ V} {E : Set V}
    (hEne : E.Nonempty) {t : ℝ} (hb : ∀ x ∈ E + (U : Set V), u x ≤ t) :
    ∀ v ∈ U, u v = 0 := by
  intro v hv
  by_contra hne
  obtain ⟨x, hx⟩ := hEne
  -- a suitable multiple of `v` pushes `u` above `t`
  set c : ℝ := (t + 1 - u x) / u v with hc
  have hmem : x + c • v ∈ E + (U : Set V) := ⟨x, hx, c • v, U.smul_mem c hv, rfl⟩
  have hval : u (x + c • v) = u x + c * u v := by
    simp [map_add, map_smul, smul_eq_mul]
  have hcv : c * u v = t + 1 - u x := div_mul_cancel₀ _ hne
  have := hb _ hmem
  rw [hval, hcv] at this
  linarith

/-- Lemma 4.1 (relative separation): two disjoint nonempty convex subsets of an affine
subspace `T` are separated by a continuous linear functional which is nonconstant on `T`,
i.e. does not vanish identically on `T.direction`. -/
theorem exists_separating_of_subset_affine {T : AffineSubspace ℝ V} {C D : Set V}
    (hC : Convex ℝ C) (hD : Convex ℝ D) (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hdisj : C ∩ D = ∅) (hCT : C ⊆ (T : Set V)) (hDT : D ⊆ (T : Set V)) :
    ∃ (u : V →L[ℝ] ℝ) (t : ℝ),
      (∃ v ∈ T.direction, u v ≠ 0) ∧
      (∀ x ∈ C, u x ≤ t) ∧ (∀ x ∈ D, t ≤ u x) := by
  classical
  obtain ⟨U, hU⟩ := Submodule.exists_isCompl T.direction
  -- the thickened sets
  have hCU : Convex ℝ (C + (U : Set V)) := hC.add U.convex
  have hDU : Convex ℝ (D + (U : Set V)) := hD.add U.convex
  obtain ⟨c₀, hc₀⟩ := id hCne
  obtain ⟨d₀, hd₀⟩ := id hDne
  have hCUne : (C + (U : Set V)).Nonempty := ⟨c₀ + 0, ⟨c₀, hc₀, 0, U.zero_mem, rfl⟩⟩
  have hDUne : (D + (U : Set V)).Nonempty := ⟨d₀ + 0, ⟨d₀, hd₀, 0, U.zero_mem, rfl⟩⟩
  have hsubC : C ⊆ C + (U : Set V) := by
    intro x hx
    exact ⟨x, hx, 0, U.zero_mem, by simp⟩
  have hsubD : D ⊆ D + (U : Set V) := by
    intro x hx
    exact ⟨x, hx, 0, U.zero_mem, by simp⟩
  -- the thickened sets are still disjoint
  have hdisjU : (C + (U : Set V)) ∩ (D + (U : Set V)) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨⟨c, hc, u₁, hu₁, rfl⟩, ⟨d, hd, u₂, hu₂, hz⟩⟩
    have hcd : c - d = u₂ - u₁ := by
      have h : c + u₁ = d + u₂ := hz.symm
      rw [sub_eq_sub_iff_add_eq_add]
      exact h.trans (add_comm d u₂)
    have hW : c - d ∈ T.direction := by
      have := AffineSubspace.vsub_mem_direction (hCT hc) (hDT hd)
      simpa using this
    have hUmem : c - d ∈ U := by
      rw [hcd]
      exact U.sub_mem hu₂ hu₁
    have hbot : c - d ∈ (⊥ : Submodule ℝ V) := by
      rw [← hU.inf_eq_bot]
      exact ⟨hW, hUmem⟩
    have hcd0 : c = d := sub_eq_zero.mp (Submodule.mem_bot ℝ |>.mp hbot)
    have : c ∈ C ∩ D := ⟨hc, hcd0 ▸ hd⟩
    rw [hdisj] at this
    exact this
  obtain ⟨u, t, hu0, hle, hge⟩ := exists_separating hCU hDU hCUne hDUne hdisjU
  -- `u` vanishes on the complement `U`
  have hUzero : ∀ v ∈ U, u v = 0 := eq_zero_on_of_bddAbove_add hCne hle
  -- hence it cannot vanish on the direction of `T`
  refine ⟨u, t, ?_, fun x hx => hle x (hsubC hx), fun x hx => hge x (hsubD hx)⟩
  obtain ⟨y, hy⟩ : ∃ y : V, u y ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hu0 (by ext y; simpa using hcon y)
  have hy' : y ∈ (⊤ : Submodule ℝ V) := Submodule.mem_top
  rw [← hU.sup_eq_top, Submodule.mem_sup] at hy'
  obtain ⟨w, hw, z, hz, hwz⟩ := hy'
  refine ⟨w, hw, ?_⟩
  intro hw0
  apply hy
  rw [← hwz, map_add, hw0, hUzero z hz, add_zero]

end ConvexFilter
