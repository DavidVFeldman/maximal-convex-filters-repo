import ConvexFilters.Principal

/-!
# Convex filters: separation of disjoint convex sets

This file is Lemma 2.2: two disjoint nonempty convex subsets of a finite-dimensional real
normed space can be separated weakly by a nonzero continuous linear functional. No
closedness or compactness hypothesis is needed, and equality is permitted on both sides.

The proof reduces to separating the origin from the convex set `C - D`, which is done by a
case split on whether that set has full affine span: if it does it has nonempty interior
and Mathlib's geometric Hahn–Banach theorem for an open convex set applies, and if it does
not, a nonzero functional constant on its affine hull does the job.
-/

open Pointwise

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

namespace ConvexFilter

/-- A nonempty convex set omitting the origin admits a nonzero functional which is
nonpositive on it. -/
theorem exists_functional_nonpos_of_zero_notMem {E : Set V} (hE : Convex ℝ E)
    (hEne : E.Nonempty) (h0 : (0 : V) ∉ E) :
    ∃ u : V →L[ℝ] ℝ, u ≠ 0 ∧ ∀ x ∈ E, u x ≤ 0 := by
  by_cases hspan : affineSpan ℝ E = ⊤
  · -- `E` has full affine span, hence nonempty interior.
    have hint : (interior E).Nonempty :=
      (hE.interior_nonempty_iff_affineSpan_eq_top).mpr hspan
    obtain ⟨f, s, hlt, hge⟩ :=
      geometric_hahn_banach_open hE.interior isOpen_interior (convex_singleton (0 : V))
        (Set.disjoint_singleton_right.mpr fun h => h0 (interior_subset h))
    have hs0 : s ≤ 0 := by simpa using hge 0 rfl
    obtain ⟨a, ha⟩ := hint
    refine ⟨f, ?_, fun x hx => ?_⟩
    · intro hf
      have := hlt a ha
      rw [hf] at this
      simp only [ContinuousLinearMap.zero_apply] at this
      linarith
    · have hclos : E ⊆ closure (interior E) := by
        rw [hE.closure_interior_eq_closure_of_nonempty_interior ⟨a, ha⟩]
        exact subset_closure
      have hle : closure (interior E) ⊆ {y : V | f y ≤ s} :=
        closure_minimal (fun y hy => (hlt y hy).le)
          (isClosed_le f.continuous continuous_const)
      exact le_trans (hle (hclos hx)) hs0
  · -- `E` lies in a proper affine subspace; a functional constant on it works.
    obtain ⟨e, he⟩ := hEne
    have heT : e ∈ affineSpan ℝ E := subset_affineSpan ℝ E he
    have hTne : ((affineSpan ℝ E : AffineSubspace ℝ V) : Set V).Nonempty := ⟨e, heT⟩
    have hdir : (affineSpan ℝ E).direction < ⊤ :=
      lt_of_le_of_ne le_top fun h =>
        hspan ((AffineSubspace.direction_eq_top_iff_of_nonempty hTne).mp h)
    obtain ⟨f, hf0, hfker⟩ := Submodule.exists_le_ker_of_lt_top _ hdir
    have hconst : ∀ x ∈ E, f x = f e := by
      intro x hx
      have hxT : x ∈ affineSpan ℝ E := subset_affineSpan ℝ E hx
      have hmem : x - e ∈ (affineSpan ℝ E).direction := by
        have := AffineSubspace.vsub_mem_direction hxT heT
        simpa using this
      have : f (x - e) = 0 := hfker hmem
      rw [map_sub, sub_eq_zero] at this
      exact this
    have hne : ∀ g : V →ₗ[ℝ] ℝ, g ≠ 0 →
        (LinearMap.toContinuousLinearMap g : V →L[ℝ] ℝ) ≠ 0 := by
      intro g hg h
      refine hg ?_
      ext x
      have : (LinearMap.toContinuousLinearMap g : V →L[ℝ] ℝ) x = 0 := by rw [h]; rfl
      exact this
    rcases le_or_gt (f e) 0 with hc | hc
    · refine ⟨LinearMap.toContinuousLinearMap f, hne f hf0, fun x hx => ?_⟩
      show f x ≤ 0
      rw [hconst x hx]
      exact hc
    · refine ⟨LinearMap.toContinuousLinearMap (-f), hne (-f) (neg_ne_zero.mpr hf0),
        fun x hx => ?_⟩
      show (-f) x ≤ 0
      simp only [LinearMap.neg_apply, neg_nonpos]
      rw [hconst x hx]
      exact hc.le

/-- Lemma 2.2: two disjoint nonempty convex sets in a finite-dimensional real normed space
are separated weakly by a nonzero continuous linear functional. -/
theorem exists_separating {C D : Set V} (hC : Convex ℝ C) (hD : Convex ℝ D)
    (hCne : C.Nonempty) (hDne : D.Nonempty) (hdisj : C ∩ D = ∅) :
    ∃ (u : V →L[ℝ] ℝ) (t : ℝ), u ≠ 0 ∧ (∀ x ∈ C, u x ≤ t) ∧ (∀ x ∈ D, t ≤ u x) := by
  obtain ⟨d₀, hd₀⟩ := hDne
  obtain ⟨c₀, hc₀⟩ := hCne
  -- the difference set is convex, nonempty and omits the origin
  have hEconv : Convex ℝ (C - D) := hC.sub hD
  have hEne : (C - D).Nonempty := ⟨c₀ - d₀, ⟨c₀, hc₀, d₀, hd₀, rfl⟩⟩
  have h0 : (0 : V) ∉ C - D := by
    rintro ⟨c, hc, d, hd, hcd⟩
    have : c = d := by
      have := sub_eq_zero.mp hcd
      exact this
    have hmem : c ∈ C ∩ D := ⟨hc, this ▸ hd⟩
    rw [hdisj] at hmem
    exact hmem
  obtain ⟨u, hu0, hule⟩ := exists_functional_nonpos_of_zero_notMem hEconv hEne h0
  -- `u` is bounded above on `C` by its values on `D`
  have hsep : ∀ c ∈ C, ∀ d ∈ D, u c ≤ u d := by
    intro c hc d hd
    have := hule (c - d) ⟨c, hc, d, hd, rfl⟩
    rw [map_sub, sub_nonpos] at this
    exact this
  have hbdd : BddAbove (u '' C) := by
    refine ⟨u d₀, ?_⟩
    rintro y ⟨c, hc, rfl⟩
    exact hsep c hc d₀ hd₀
  refine ⟨u, sSup (u '' C), hu0, fun x hx => ?_, fun x hx => ?_⟩
  · exact le_csSup hbdd ⟨x, hx, rfl⟩
  · refine csSup_le ⟨u c₀, ⟨c₀, hc₀, rfl⟩⟩ ?_
    rintro y ⟨c, hc, rfl⟩
    exact hsep c hc x hx

end ConvexFilter
