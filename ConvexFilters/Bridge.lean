import ConvexFilters.Adapted
import ConvexFilters.Realization
import ConvexFilters.Annihilator

/-!
# The bridge between the two halves of the classification

This file is Part A of WO-06b. The tree it sits on is the merge of two concurrent returns,
WO-05 (`ConvexFilters/Coords.lean`, `ConvexFilters/Realization.lean`) and WO-06a
(`ConvexFilters/LexConeMod.lean`, `ConvexFilters/Adapted.lean`). Each of the two returns
independently introduced `basisAt`, `Q0` and `M0`, one in the namespace `ConvexFilter` and
one in `ConvexFilter.Adapted`. The three theorems `Adapted.basisAt_eq`, `Adapted.Q0_eq` and
`Adapted.M0_eq` identify the two copies; all three are definitional (`rfl` after unfolding
the bounded existential, which is notation for the same proposition).

The file also supplies the annihilator of a submodule of `V` inside the continuous dual,
`annih`, which is the direction opposite to `ConvexFilter.Adapted.preAnnih`, and the two
double-annihilator identities in finite dimension.

## Main results

* `ConvexFilter.Adapted.basisAt_eq`, `ConvexFilter.Adapted.Q0_eq`, `ConvexFilter.Adapted.M0_eq`;
* `ConvexFilter.annih`, `ConvexFilter.annih_preAnnih`, `ConvexFilter.preAnnih_annih`;
* `ConvexFilter.annih_dirA`.
-/

open Module

namespace ConvexFilter

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-! ## The two copies of the normal-form data -/

omit [FiniteDimensional ℝ V] in
/-- The two definitions of `basisAt`, from WO-05 (`Coords.lean`) and WO-06a (`Adapted.lean`),
agree; the bodies are textually identical. -/
theorem Adapted.basisAt_eq {n : ℕ} (b : Basis (Fin n) ℝ V) (i : ℕ) :
    Adapted.basisAt b i = basisAt b i := rfl

omit [FiniteDimensional ℝ V] in
/-- The two definitions of `Q0` agree: `∃ j < m, …` and `∃ j, j < m ∧ …` are the same
proposition. -/
theorem Adapted.Q0_eq {n : ℕ} (b : Basis (Fin n) ℝ V) (m : ℕ) :
    Adapted.Q0 b m = Q0 b m := rfl

omit [FiniteDimensional ℝ V] in
/-- The two definitions of `M0` agree. -/
theorem Adapted.M0_eq {n : ℕ} (b : Basis (Fin n) ℝ V) (m : ℕ) :
    Adapted.M0 b m = M0 b m := rfl

/-! ## The annihilator in the continuous dual -/

/-- The annihilator of a submodule `W` of `V` inside the continuous dual: the functionals
vanishing on `W`. This is the direction opposite to `ConvexFilter.Adapted.preAnnih`. -/
def annih (W : Submodule ℝ V) : Submodule ℝ (V →L[ℝ] ℝ) where
  carrier := {u | ∀ v ∈ W, u v = 0}
  add_mem' := by
    intro u u' hu hu' v hv
    rw [ContinuousLinearMap.add_apply, hu v hv, hu' v hv, add_zero]
  zero_mem' := by
    intro v _
    rfl
  smul_mem' := by
    intro c u hu v hv
    rw [ContinuousLinearMap.smul_apply, hu v hv, smul_zero]

omit [FiniteDimensional ℝ V] in
theorem mem_annih_iff {W : Submodule ℝ V} {u : V →L[ℝ] ℝ} :
    u ∈ annih W ↔ ∀ v ∈ W, u v = 0 := Iff.rfl

/-- The linear equivalence between the algebraic and the continuous dual of a
finite-dimensional space. -/
noncomputable abbrev dualEquiv (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap

/-- `annih`, pulled back to the algebraic dual, is Mathlib's `dualAnnihilator`. -/
theorem comap_annih (W : Submodule ℝ V) :
    Submodule.comap (dualEquiv V : (V →ₗ[ℝ] ℝ) →ₗ[ℝ] (V →L[ℝ] ℝ)) (annih W)
      = W.dualAnnihilator := by
  ext f
  simp only [Submodule.mem_comap, mem_annih_iff, Submodule.mem_dualAnnihilator]
  rfl

/-- `preAnnih` is Mathlib's `dualCoannihilator` of the pullback to the algebraic dual. -/
theorem preAnnih_eq_dualCoannihilator (S : Submodule ℝ (V →L[ℝ] ℝ)) :
    Adapted.preAnnih S
      = (Submodule.comap (dualEquiv V : (V →ₗ[ℝ] ℝ) →ₗ[ℝ] (V →L[ℝ] ℝ)) S).dualCoannihilator := by
  ext v
  rw [Adapted.mem_preAnnih_iff, Submodule.mem_dualCoannihilator]
  constructor
  · intro h f hf
    exact h _ hf
  · intro h u hu
    exact h ((dualEquiv V).symm u) (by simpa using hu)

/-- The finite-dimensional double annihilator, starting from the dual side. -/
theorem annih_preAnnih (S : Submodule ℝ (V →L[ℝ] ℝ)) : annih (Adapted.preAnnih S) = S := by
  have hsurj : Function.Surjective (dualEquiv V : (V →ₗ[ℝ] ℝ) →ₗ[ℝ] (V →L[ℝ] ℝ)) :=
    (dualEquiv V).surjective
  have hcomap :
      Submodule.comap (dualEquiv V : (V →ₗ[ℝ] ℝ) →ₗ[ℝ] (V →L[ℝ] ℝ)) (annih (Adapted.preAnnih S))
        = Submodule.comap (dualEquiv V : (V →ₗ[ℝ] ℝ) →ₗ[ℝ] (V →L[ℝ] ℝ)) S := by
    rw [comap_annih, preAnnih_eq_dualCoannihilator]
    exact Subspace.dualCoannihilator_dualAnnihilator_eq
  have := congrArg (Submodule.map (dualEquiv V : (V →ₗ[ℝ] ℝ) →ₗ[ℝ] (V →L[ℝ] ℝ))) hcomap
  rwa [Submodule.map_comap_eq_of_surjective hsurj,
    Submodule.map_comap_eq_of_surjective hsurj] at this

/-- The finite-dimensional double annihilator, starting from the primal side. -/
theorem preAnnih_annih (W : Submodule ℝ V) : Adapted.preAnnih (annih W) = W := by
  rw [preAnnih_eq_dualCoannihilator, comap_annih]
  exact Subspace.dualAnnihilator_dualCoannihilator_eq

/-! ## The annihilator of the direction of `Aset` -/

variable {F : ConvexFilter V}

/-- The annihilator of `dirA F` is the submodule `Nset F`. This is
`ConvexFilter.Nset_eq_annihilator_dirA` repackaged as an equality of submodules. -/
theorem annih_dirA (hF : IsMaximal F) : annih (dirA F) = NsubmoduleOf F hF := by
  ext u
  rw [mem_annih_iff]
  change _ ↔ u ∈ Nset F
  rw [Nset_eq_annihilator_dirA hF]
  exact Iff.rfl

end ConvexFilter
