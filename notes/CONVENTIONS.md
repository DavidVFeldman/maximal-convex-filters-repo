# Conventions of the formalization

Choices made in the Lean development that do not appear in the paper, and the
pitfalls each creates. Read §1 before writing any statement that mentions
`sig`, §5 before relativizing any definition, and §7 before moving between a
dual and a primal lexicographic presentation.

---

## 1. `sig` is real-valued; the paper's `σ` is not

The paper's support function takes values in `[-∞, +∞]`. It is not represented
as an `EReal` here, because subadditivity and homogeneity would then have to be
stated in an arithmetic where `⊤ + ⊥` arises. The representation is a pair:

- `lev F u : Set ℝ`, the levels `t` with `halfLE u t ∈ F.carrier`, carrying the
  full extended-real information in its shape (`∅`, `Set.univ`, `Set.Ioi s`,
  `Set.Ici s`);
- `sig F u : ℝ`, defined as `sInf (lev F u)`, meaningful only on `Nset F`.

In Mathlib's `Real`, `sInf ∅ = 0` and `sInf Set.univ = 0`. So `sig F u = 0` is
returned in three distinct situations: support value `+∞`, support value `-∞`,
and a finite value equal to `0`. Consequently `∀ u, sig F u = sig F' u` is
strictly weaker than `σ_F = σ_{F'}`, the difference being exactly `Nset`.

**Rule.** Wherever the paper writes `σ_F = σ_{F'}` as a hypothesis, the Lean
statement carries `Nset F = Nset F'` alongside `∀ u, sig F u = sig F' u`.
Preferably the hypothesis is stated in terms of `Aset` and `Qset`, which
determine both: `carrier_eq_of_Aset_Qset` needs no such extra hypothesis, while
`carrier_eq_of_sig_Qset` does. `SigCounterexample.not_carrier_eq_of_sig_Qset`
refutes the version without it, on `ℝ × ℝ`, with maximal extensions of the
hyperbola germs and the parabola tails: same `Qset`, same `sig`, distinct
carriers.

Before writing a hypothesis that mentions `sig`, ask which of `+∞`, `-∞`, `0`
the statement must distinguish, and whether `lev` or `Nset` must appear to do
it. A statement quantified over all `u` that mentions `sig` and not `Nset` is
suspect until checked.

## 2. Namespace

Everything except the structure `ConvexFilter` lives in `namespace
ConvexFilter`; the structure is at root so its name does not double. Dot
notation (`F.lev u`, `F.Nset`) is therefore available. Results relativized
modulo a subspace live in `ConvexFilter.Adapted`.

`ConvexFilter.convex_hyperplane` shadows a Mathlib lemma of the same base name
inside the namespace; the Mathlib one is `_root_.convex_hyperplane`.

## 3. Finite dimensionality

`Defs.lean`, `Basic.lean`, `Levels.lean` and `Invariants.lean` hold over an
arbitrary real normed space, as does `Extension.lean`. `[FiniteDimensional ℝ V]`
enters at `Flat.lean` and is assumed from there onward, with
`omit [FiniteDimensional ℝ V] in` on individual results that do not need it.

`Aset` is defined in `Flat.lean` and therefore carries the hypothesis. In an
infinite-dimensional ambient the flat must be written out as
`{x | ∀ u ∈ Nset F, u x = sig F u}`; `RemarkInfinite.lean` does this.

## 4. Separation is project-local

Weak separation of two disjoint convex sets, with no topological hypothesis on
either side, is not in Mathlib at the pinned revision: every
`geometric_hahn_banach_*` variant requires one side open, or one side compact
and the other closed, and yields strict inequality on one side. The
project-local statements are `exists_separating` (`Separation.lean`) and its
relative form `exists_separating_of_subset_affine` (`SeparationRel.lean`). Do
not assume a Mathlib replacement exists.

## 5. Hypotheses do not survive relativization by themselves

`IsLexConeModOn W M P` generalizes `IsLexConeOn W P` by replacing the
exceptional set `{0}` of the trichotomy with a submodule `M`. Statements whose
proofs used the old degeneracy need a replacement hypothesis, and not only those
where the need is visible in the conclusion.

`IsLexConeOn.mem_of_pos` reads: if `f ≥ 0` on `P` and `f x > 0` for `x ∈ W`,
then `x ∈ P`. Its proof takes the middle branch of the trichotomy, `x = 0`, and
observes `f 0 = 0`. Modulo `M` that branch gives only `x ∈ M`, and nothing
contradicts `f x > 0` unless `f` annihilates `M`. The unrepaired form is refuted
by `M = W`, where `P = ∅` makes the nonnegativity hypothesis vacuous and leaves
`f` free; `Adapted.mem_of_pos_counterexample` is that refutation on `U = ℝ`.

**Rule.** Enumerate the consumers of a degeneracy condition before writing the
relativized contract, and check each one.

## 6. Unnecessary hypotheses are kept

Where a hypothesis turns out to be unnecessary it stays in the statement, with
the observation recorded in the docstring. A hypothesis that later turns out to
be needed is cheaper to have kept than to reinstate across call sites, and §5 is
the reason to expect that case.

## 7. First-nonzero on the dual, last-nonzero on the primal

Two lexicographic conventions coexist and are not interchangeable.

- `Adapted.lexCone W l` is **first**-nonzero-positive in the functionals `l`:
  `x ∈ P` when the least `j` with `l j x ≠ 0` has `l j x > 0`. This is what
  `exists_functionals` produces, and what `Q0` uses on the dual side.
- The primal cone of `Primal.lean` is **last**-nonzero-positive in the
  coordinates of an adapted basis.

They describe the same order only after reversing the index range,
`i ↦ m - 1 - i`. This is the content of the duality of Definition 3.3 in the
paper, which is why `primalCone_eq_lexCone` is a theorem with a real proof
rather than a definitional unfolding. The dominant direction of the order on `W`
is the last basis vector; the dominant direction of the order on the dual is the
first functional; the flag member cut out by the vanishing of the first `r`
functionals corresponds to the span of the first `m - r` basis vectors.

**Rule.** Any statement moving between a `lexCone`/`Q0` presentation and a
primal coordinate presentation must reverse the index order. When a proof
unexpectedly needs `<` where `>` was expected, or a flag index `r` where `m - r`
was expected, check the convention before adjusting the statement.
