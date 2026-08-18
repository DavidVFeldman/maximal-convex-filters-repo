import Mathlib

/-!
# Convex filters: basic definitions

This file sets up the basic objects of the theory of filters in the lattice of
closed convex subsets of a real normed space `V`:

* `ConvexFilter V` — a proper filter of closed convex subsets of `V`;
* `IsMaximal F` — maximality of such a filter;
* `halfLE`, `halfGE`, `hyperplane` — the closed half-spaces and hyperplanes
  attached to a continuous linear functional;
* `lev F u` — the level set `{t | {u ≤ t} ∈ F}`, an upper set in `ℝ`, playing
  the role of the (extended-real valued) support function of `F`;
* `sig F u` — the real number `sInf (lev F u)`, the support function where finite;
* `Nset F`, `Mset F`, `Eset F`, `Dset F`, `Qset F` — the invariants attached
  to `F`.

No extended reals and no separation theorem are used anywhere in this development.
-/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A *convex filter* on a real normed space `V` is a proper filter in the lattice of
closed convex subsets of `V`: a family of closed convex sets containing `Set.univ`,
not containing `∅`, stable under binary intersections and under passing to closed
convex supersets. -/
structure ConvexFilter (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  /-- The family of sets belonging to the filter. -/
  carrier : Set (Set V)
  /-- Members of a convex filter are closed. -/
  isClosed_of_mem : ∀ ⦃C : Set V⦄, C ∈ carrier → IsClosed C
  /-- Members of a convex filter are convex. -/
  convex_of_mem : ∀ ⦃C : Set V⦄, C ∈ carrier → Convex ℝ C
  /-- The whole space belongs to a convex filter. -/
  univ_mem : Set.univ ∈ carrier
  /-- A convex filter is proper: the empty set does not belong to it. -/
  empty_not_mem : ∅ ∉ carrier
  /-- A convex filter is stable under binary intersections. -/
  inter_mem : ∀ ⦃C D : Set V⦄, C ∈ carrier → D ∈ carrier → C ∩ D ∈ carrier
  /-- A convex filter is stable under closed convex supersets. -/
  mem_of_superset : ∀ ⦃C D : Set V⦄, C ∈ carrier → IsClosed D → Convex ℝ D → C ⊆ D →
    D ∈ carrier

namespace ConvexFilter

/-- A convex filter is *maximal* if no convex filter properly contains it. -/
def IsMaximal (F : ConvexFilter V) : Prop :=
  ∀ G : ConvexFilter V, F.carrier ⊆ G.carrier → G.carrier ⊆ F.carrier

/-- The closed half-space `{x | u x ≤ t}`. -/
def halfLE (u : V →L[ℝ] ℝ) (t : ℝ) : Set V := {x : V | u x ≤ t}

/-- The closed half-space `{x | t ≤ u x}`. -/
def halfGE (u : V →L[ℝ] ℝ) (t : ℝ) : Set V := {x : V | t ≤ u x}

/-- The hyperplane `{x | u x = t}`. -/
def hyperplane (u : V →L[ℝ] ℝ) (t : ℝ) : Set V := {x : V | u x = t}

/-- The level set of `F` at `u`: the set of `t` such that the half-space `{u ≤ t}`
belongs to `F`. It is an upper set of `ℝ`, and encodes the (possibly infinite)
value of the support function of `F` at `u`. -/
def lev (F : ConvexFilter V) (u : V →L[ℝ] ℝ) : Set ℝ := {t : ℝ | halfLE u t ∈ F.carrier}

/-- The support number of `F` at `u`: the infimum of the level set `lev F u`.
It is mathematically meaningful exactly when `u ∈ Nset F`. -/
noncomputable def sig (F : ConvexFilter V) (u : V →L[ℝ] ℝ) : ℝ := sInf (lev F u)

/-- The set of functionals on which the support function of `F` is finite in both
directions. -/
def Nset (F : ConvexFilter V) : Set (V →L[ℝ] ℝ) :=
  {u : V →L[ℝ] ℝ | lev F u ≠ ∅ ∧ lev F (-u) ≠ ∅}

/-- The set of functionals `u` such that some level hyperplane of `u` belongs to `F`. -/
def Mset (F : ConvexFilter V) : Set (V →L[ℝ] ℝ) :=
  {u : V →L[ℝ] ℝ | ∃ t : ℝ, hyperplane u t ∈ F.carrier}

/-- The set of functionals whose support function is `+∞`, i.e. whose level set is empty. -/
def Eset (F : ConvexFilter V) : Set (V →L[ℝ] ℝ) := {u : V →L[ℝ] ℝ | lev F u = ∅}

/-- The set of functionals with finite support number which is not attained. -/
def Dset (F : ConvexFilter V) : Set (V →L[ℝ] ℝ) :=
  {u : V →L[ℝ] ℝ | u ∈ Nset F ∧ sig F u ∉ lev F u}

/-- The positivity cone of `F`: functionals whose level set is a proper open upper set,
i.e. does not contain its infimum and is not all of `ℝ`. -/
def Qset (F : ConvexFilter V) : Set (V →L[ℝ] ℝ) :=
  {u : V →L[ℝ] ℝ | lev F u ≠ Set.univ ∧ ∀ t ∈ lev F u, ∃ t' ∈ lev F u, t' < t}

end ConvexFilter
