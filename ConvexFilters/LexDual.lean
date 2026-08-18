import ConvexFilters.LexCone

/-!
# The normal form of a lex cone in a dual

This file is Part D of WO-04. Section 6 of the paper applies the normal form of Lemma 3.2 to
a lex cone living in the dual `V →L[ℝ] ℝ`. The functionals furnished by `exists_functionals`
are then functionals on the dual, and in finite dimensions these are exactly the evaluations
at points of `V`. This file records that translation, so that Section 6 never handles a
double dual.

The bridge `exists_point_of_dual_functional` is the route already used for
`ConvexFilter.exists_point_of_Nset` in `ConvexFilters/Flat.lean`:
`LinearMap.toContinuousLinearMap` together with `Module.evalEquiv ℝ V`.
-/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

namespace ConvexFilter

/-- In finite dimensions, every continuous linear functional on the dual is evaluation at a
point. -/
theorem exists_point_of_dual_functional (L : (V →L[ℝ] ℝ) →L[ℝ] ℝ) :
    ∃ x : V, ∀ u : V →L[ℝ] ℝ, L u = u x := by
  let e : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V →L[ℝ] ℝ) := LinearMap.toContinuousLinearMap
  let Psi : Module.Dual ℝ (Module.Dual ℝ V) :=
    (L : (V →L[ℝ] ℝ) →ₗ[ℝ] ℝ) ∘ₗ (e : (V →ₗ[ℝ] ℝ) →ₗ[ℝ] (V →L[ℝ] ℝ))
  refine ⟨(Module.evalEquiv ℝ V).symm Psi, fun u => ?_⟩
  set a : V := (Module.evalEquiv ℝ V).symm Psi with ha
  have heval : Module.evalEquiv ℝ V a = Psi := (Module.evalEquiv ℝ V).apply_symm_apply Psi
  have hkey : Psi (e.symm u) = (e.symm u) a := by rw [← heval]; rfl
  have hcoe : (e.symm u) a = u a := by
    simp [e, LinearMap.toContinuousLinearMap]
  have hPsi : Psi (e.symm u) = L u := by
    show L (e (e.symm u)) = L u
    rw [e.apply_symm_apply]
  rw [← hcoe, ← hkey, hPsi]

/-- Part B in a dual: a lex cone on a submodule `M` of the dual of `V` is the lexicographic
cone of `finrank ℝ M` evaluations at points of `V`. -/
theorem exists_points_of_isLexConeOn {M : Submodule ℝ (V →L[ℝ] ℝ)} {Q : Set (V →L[ℝ] ℝ)}
    (h : IsLexConeOn M Q) :
    ∃ (k : ℕ) (x : Fin k → V),
      k = Module.finrank ℝ M ∧
      (∀ u ∈ M, (∀ i, u (x i) = 0) → u = 0) ∧
      Q = {u | u ∈ M ∧ ∃ j : Fin k, 0 < u (x j) ∧ ∀ i : Fin k, i < j → u (x i) = 0} := by
  obtain ⟨k, L, hk, hsep, hQ⟩ := exists_functionals h
  choose x hx using fun i : Fin k => exists_point_of_dual_functional (L i)
  refine ⟨k, x, hk, ?_, ?_⟩
  · intro u hu hall
    refine hsep u hu fun i => ?_
    rw [hx i u]
    exact hall i
  · rw [hQ]
    ext u
    simp only [lexCone, Set.mem_setOf_eq, hx _ u]

end ConvexFilter
