import ConvexFilters.LexConeMod
import ConvexFilters.Flag
import ConvexFilters.LexDual

/-!
# Order-convex submodules above `M`, and the adapted basis

This file is Parts C and D of WO-06a.

Part C repeats `ConvexFilters/Flag.lean` with the exceptional submodule `M` threaded through:
the flags of a family of functionals, their order-convexity for `lexConeMod W M l`, and the
converse that every order-convex submodule between `M` and `W` is a flag. The degenerate flag
is now `flagMod W M l k = M` rather than `⊥`.

Part D is the surjectivity paragraph of Theorem 6.1, up to but not including the appeal to
realization: from a lex cone `Q` modulo `Mq` on the whole dual of `V`, together with an
order-convex submodule `Nq` above `Mq` whose pre-annihilator is nonzero, it produces a basis
of `V` in which `Q`, `Mq` and `preAnnih Nq` all take normal form.

## Main results

* `ConvexFilter.Adapted.isOrderConvex_flagMod`, `ConvexFilter.Adapted.exists_eq_flagMod`;
* `ConvexFilter.Adapted.exists_adapted_basis`.
-/

open Module

namespace ConvexFilter.Adapted

open ConvexFilter

/-! ## Part C — order-convex submodules above `M` -/

section PartC

variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]

/-- The `r`-th flag of a family of functionals on `W`, in the presence of an exceptional
submodule `M`: the points of `W` annihilated by the first `r` functionals. As with
`lexConeMod`, the submodule `M` does not enter the body. -/
def flagMod (W M : Submodule ℝ U) {k : ℕ} (l : Fin k → (U →L[ℝ] ℝ)) (r : ℕ) :
    Submodule ℝ U where
  carrier := {x | x ∈ W ∧ ∀ i : Fin k, (i : ℕ) < r → l i x = 0}
  add_mem' := by
    rintro x y ⟨hxW, hx⟩ ⟨hyW, hy⟩
    exact ⟨W.add_mem hxW hyW, fun i hi => by rw [map_add, hx i hi, hy i hi, add_zero]⟩
  zero_mem' := ⟨W.zero_mem, fun i _ => by simp⟩
  smul_mem' := by
    rintro c x ⟨hxW, hx⟩
    exact ⟨W.smul_mem c hxW, fun i hi => by rw [map_smul, hx i hi, smul_zero]⟩

omit [FiniteDimensional ℝ U] in
theorem mem_flagMod_iff {W M : Submodule ℝ U} {k : ℕ} {l : Fin k → (U →L[ℝ] ℝ)} {r : ℕ}
    {x : U} : x ∈ flagMod W M l r ↔ x ∈ W ∧ ∀ i : Fin k, (i : ℕ) < r → l i x = 0 := Iff.rfl

omit [FiniteDimensional ℝ U] in
theorem flagMod_zero {W M : Submodule ℝ U} {k : ℕ} {l : Fin k → (U →L[ℝ] ℝ)} :
    flagMod W M l 0 = W := by
  ext x
  simp [mem_flagMod_iff]

omit [FiniteDimensional ℝ U] in
theorem flagMod_antitone {W M : Submodule ℝ U} {k : ℕ} {l : Fin k → (U →L[ℝ] ℝ)} :
    Antitone (flagMod W M l) := by
  intro a b hab x hx
  exact ⟨hx.1, fun i hi => hx.2 i (lt_of_lt_of_le hi hab)⟩

omit [FiniteDimensional ℝ U] in
theorem flagMod_le {W M : Submodule ℝ U} {k : ℕ} {l : Fin k → (U →L[ℝ] ℝ)} (r : ℕ) :
    flagMod W M l r ≤ W := fun _ hx => hx.1

omit [FiniteDimensional ℝ U] in
/-- The last flag is the exceptional submodule `M` itself. -/
theorem flagMod_top_eq {W M : Submodule ℝ U} {k : ℕ} {l : Fin k → (U →L[ℝ] ℝ)}
    (hML : M ≤ W) (hMker : ∀ i, ∀ w ∈ M, l i w = 0)
    (hsep : ∀ x ∈ W, (∀ i, l i x = 0) → x ∈ M) :
    flagMod W M l k = M := by
  ext x
  constructor
  · rintro ⟨hxW, hx⟩
    exact hsep x hxW fun i => hx i i.isLt
  · intro hx
    exact ⟨hML hx, fun i _ => hMker i x hx⟩

omit [FiniteDimensional ℝ U] in
/-- The flag `flagMod W M l r` is order-convex for the lexicographic cone of `l`.

As in WO-04, neither `hMker` nor `hsep` is needed for this implication; the contract
prescribes them and they are kept. -/
theorem isOrderConvex_flagMod {W M : Submodule ℝ U} {k : ℕ} {l : Fin k → (U →L[ℝ] ℝ)}
    (hMker : ∀ i, ∀ w ∈ M, l i w = 0) (hsep : ∀ x ∈ W, (∀ i, l i x = 0) → x ∈ M) (r : ℕ) :
    ConvexFilter.IsOrderConvex (lexConeMod W M l) (flagMod W M l r) := by
  rintro w v ⟨hwW, jw, hjw, hjw0⟩ ⟨-, j₂, hj₂, hj₂0⟩ ⟨-, hv0⟩
  refine ⟨hwW, fun i hi => ?_⟩
  -- the first nonvanishing coordinate of `w` occurs at index `jw ≥ r`
  have hjwm : r ≤ (jw : ℕ) := by
    by_contra hlt
    push_neg at hlt
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
    · have h1 : l j₂ w = 0 := hjw0 j₂ hlt'
      have h2 : l j₂ v = 0 := hv0 j₂ (lt_trans hlt' hlt)
      rw [map_sub, h1, h2, sub_zero] at hj₂
      exact lt_irrefl 0 hj₂
    · subst heq
      rw [hsub] at hj₂
      linarith
    · exact hj₂le hgt
  exact hjw0 i (by simp only [Fin.lt_def]; omega)

omit [FiniteDimensional ℝ U] in
/-- Conversely, every order-convex submodule between `M` and `W` is one of the flags. The
degenerate case is `N = M`, which is the last flag. -/
theorem exists_eq_flagMod {W M : Submodule ℝ U} {k : ℕ} {l : Fin k → (U →L[ℝ] ℝ)}
    (hMker : ∀ i, ∀ w ∈ M, l i w = 0) (hsep : ∀ x ∈ W, (∀ i, l i x = 0) → x ∈ M)
    {N : Submodule ℝ U} (hMN : M ≤ N) (hNW : N ≤ W)
    (hoc : ConvexFilter.IsOrderConvex (lexConeMod W M l) N) :
    ∃ r ≤ k, N = flagMod W M l r := by
  classical
  by_cases hNM : N = M
  · -- the exceptional submodule is the last flag
    exact ⟨k, le_refl k, by rw [hNM, flagMod_top_eq (hMN.trans hNW) hMker hsep]⟩
  · -- the least index at which some functional does not vanish identically on `N`
    obtain ⟨x₀, hx₀N, hx₀M⟩ : ∃ x ∈ N, x ∉ M := by
      by_contra hcon
      push_neg at hcon
      exact hNM (le_antisymm hcon hMN)
    set S : Finset (Fin k) := Finset.univ.filter (fun i => ∃ x ∈ N, l i x ≠ 0) with hS
    have hSne : S.Nonempty := by
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty] at hcon
      have hall : ∀ i : Fin k, l i x₀ = 0 := by
        intro i
        by_contra hne
        have : i ∈ S := by
          simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨x₀, hx₀N, hne⟩
        rw [hcon] at this
        exact absurd this (Finset.notMem_empty i)
      exact hx₀M (hsep x₀ (hNW hx₀N) hall)
    set j : Fin k := S.min' hSne with hj
    refine ⟨(j : ℕ), le_of_lt j.isLt, ?_⟩
    have hforward : N ≤ flagMod W M l (j : ℕ) := by
      intro w hw
      refine ⟨hNW hw, fun i hi => ?_⟩
      by_contra hne
      have hiS : i ∈ S := by
        simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨w, hw, hne⟩
      have := S.min'_le i hiS
      rw [← hj, Fin.le_def] at this
      omega
    refine le_antisymm hforward ?_
    -- a point of `N` positive at index `j`
    obtain ⟨x, hxN, hxpos⟩ : ∃ x ∈ N, 0 < l j x := by
      have hjS : j ∈ S := S.min'_mem hSne
      rw [hS, Finset.mem_filter] at hjS
      obtain ⟨-, x, hxN, hxne⟩ := hjS
      rcases lt_or_gt_of_ne hxne with hneg | hpos
      · exact ⟨-x, N.neg_mem hxN, by rw [map_neg]; linarith⟩
      · exact ⟨x, hxN, hpos⟩
    intro y hy
    obtain ⟨hyW, hy0⟩ := hy
    have hxflag := hforward hxN
    set a : ℝ := l j x with ha
    set bb : ℝ := l j y with hb
    set mu : ℝ := (|bb| + 1) / a with hmu
    have hmupos : 0 < mu := div_pos (by positivity) hxpos
    have hmua : mu * a = |bb| + 1 := by
      rw [hmu, div_mul_cancel₀ _ (ne_of_gt hxpos)]
    have hlow : ∀ i : Fin k, i < j → l i x = 0 ∧ l i y = 0 := by
      intro i hi
      have hi' : (i : ℕ) < (j : ℕ) := hi
      exact ⟨hxflag.2 i hi', hy0 i hi'⟩
    have hplus : mu • x + y ∈ lexConeMod W M l := by
      refine ⟨W.add_mem (W.smul_mem mu (hNW hxN)) hyW, j, ?_, ?_⟩
      · rw [map_add, map_smul, smul_eq_mul, ← ha, ← hb, hmua]
        cases abs_cases bb with
        | inl h => linarith [h.1]
        | inr h => linarith [h.1]
      · intro i hi
        rw [map_add, map_smul, (hlow i hi).1, (hlow i hi).2, smul_zero, add_zero]
    have hminus : mu • x - y ∈ lexConeMod W M l := by
      refine ⟨W.sub_mem (W.smul_mem mu (hNW hxN)) hyW, j, ?_, ?_⟩
      · rw [map_sub, map_smul, smul_eq_mul, ← ha, ← hb, hmua]
        cases abs_cases bb with
        | inl h => linarith [h.1]
        | inr h => linarith [h.1]
      · intro i hi
        rw [map_sub, map_smul, (hlow i hi).1, (hlow i hi).2, smul_zero, sub_zero]
    have hv : (2 * mu) • x ∈ N := N.smul_mem _ hxN
    have hdiff : (2 * mu) • x - (mu • x + y) = mu • x - y := by
      rw [two_mul, add_smul]
      abel
    have hmem : mu • x + y ∈ N := hoc hplus (by rw [hdiff]; exact hminus) hv
    have hyeq : y = (mu • x + y) - mu • x := by abel
    rw [hyeq]
    exact N.sub_mem hmem (N.smul_mem mu hxN)

end PartC

/-! ## Part D — the adapted basis -/

section PartD

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The `i`-th vector of a basis indexed by `Fin n`, as a function of a natural number, with
the junk value `0` outside the range. -/
noncomputable def basisAt {n : ℕ} (b : Basis (Fin n) ℝ V) (i : ℕ) : V :=
  if h : i < n then b ⟨i, h⟩ else 0

/-- The normal form of the invariant `Q` in an adapted basis. -/
def Q0 {n : ℕ} (b : Basis (Fin n) ℝ V) (m : ℕ) : Set (V →L[ℝ] ℝ) :=
  {u | ∃ j < m, 0 < u (basisAt b j) ∧ ∀ i < j, u (basisAt b i) = 0}

/-- The normal form of the exceptional submodule in an adapted basis. -/
def M0 {n : ℕ} (b : Basis (Fin n) ℝ V) (m : ℕ) : Set (V →L[ℝ] ℝ) :=
  {u | ∀ i < m, u (basisAt b i) = 0}

/-- The pre-annihilator in `V` of a submodule of the dual. -/
def preAnnih (S : Submodule ℝ (V →L[ℝ] ℝ)) : Submodule ℝ V where
  carrier := {v | ∀ u ∈ S, u v = 0}
  add_mem' := by
    intro x y hx hy u hu
    rw [map_add, hx u hu, hy u hu, add_zero]
  zero_mem' := by
    intro u _
    rw [map_zero]
  smul_mem' := by
    intro c x hx u hu
    rw [map_smul, hx u hu, smul_zero]

omit [FiniteDimensional ℝ V] in
theorem mem_preAnnih_iff {S : Submodule ℝ (V →L[ℝ] ℝ)} {v : V} :
    v ∈ preAnnih S ↔ ∀ u ∈ S, u v = 0 := Iff.rfl

/-- Bookkeeping for step 5 of the route: a linearly independent family indexed by `Fin k`
extends to a basis of `V` whose first `k` vectors are that family. -/
theorem exists_basis_extending {k : ℕ} (x : Fin k → V) (hx : LinearIndependent ℝ x) :
    ∃ b : Basis (Fin (finrank ℝ V)) ℝ V, ∀ i : Fin k, basisAt b (i : ℕ) = x i := by
  classical
  set S : Submodule ℝ V := Submodule.span ℝ (Set.range x) with hS
  obtain ⟨T, hT⟩ := Submodule.exists_isCompl S
  set bS : Basis (Fin k) ℝ S := Basis.span hx with hbS
  set t : ℕ := finrank ℝ T with ht
  set bT : Basis (Fin t) ℝ T := finBasis ℝ T with hbT
  set b0 : Basis (Fin k ⊕ Fin t) ℝ V :=
    (bS.prod bT).map (Submodule.prodEquivOfIsCompl S T hT) with hb0
  have hcard : k + t = finrank ℝ V := by
    have := Module.finrank_eq_card_basis b0
    simp [this]
  set e : Fin k ⊕ Fin t ≃ Fin (finrank ℝ V) := finSumFinEquiv.trans (finCongr hcard) with he
  refine ⟨b0.reindex e, fun i => ?_⟩
  have hlt : (i : ℕ) < finrank ℝ V := by omega
  have hei : e (Sum.inl i) = ⟨(i : ℕ), hlt⟩ := by
    apply Fin.ext
    simp [he]
  have hb : (b0.reindex e) ⟨(i : ℕ), hlt⟩ = b0 (Sum.inl i) := by
    rw [← hei]
    simp [Basis.reindex_apply]
  rw [basisAt, dif_pos hlt, hb, hb0]
  simp only [Basis.map_apply, Basis.prod_apply, Sum.elim_inl, Function.comp_apply,
    LinearMap.coe_inl, Submodule.coe_prodEquivOfIsCompl', Submodule.coe_zero, add_zero]
  rw [hbS]
  exact Basis.span_apply hx i

/-- Step 3 of the route: if the joint kernel of the evaluations at `x 0, …, x (k-1)` is
exactly `Mq`, and the ranks match, then the `x i` are linearly independent. -/
theorem linearIndependent_of_eval {k : ℕ} {x : Fin k → V} {Mq : Submodule ℝ (V →L[ℝ] ℝ)}
    (hMker : ∀ i, ∀ u ∈ Mq, u (x i) = 0)
    (hsep : ∀ u : V →L[ℝ] ℝ, (∀ i, u (x i) = 0) → u ∈ Mq)
    (hk : k + finrank ℝ Mq = finrank ℝ V) :
    LinearIndependent ℝ x := by
  classical
  -- the evaluation map from the dual to `Fin k → ℝ`
  set T : (V →L[ℝ] ℝ) →ₗ[ℝ] (Fin k → ℝ) :=
    { toFun := fun u i => u (x i)
      map_add' := by intro u v; funext i; simp
      map_smul' := by intro c u; funext i; simp } with hT
  have hker : LinearMap.ker T = Mq := by
    ext u
    constructor
    · intro hu
      refine hsep u fun i => ?_
      have : T u = 0 := hu
      calc u (x i) = T u i := rfl
        _ = 0 := by rw [this]; rfl
    · intro hu
      show T u = 0
      funext i
      exact hMker i u hu
  have hdual : finrank ℝ (V →L[ℝ] ℝ) = finrank ℝ V := by
    have e : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V →L[ℝ] ℝ) := LinearMap.toContinuousLinearMap
    rw [← e.finrank_eq]
    exact Subspace.dual_finrank_eq
  have hrk : finrank ℝ (LinearMap.range T) + finrank ℝ (LinearMap.ker T)
      = finrank ℝ (V →L[ℝ] ℝ) := LinearMap.finrank_range_add_finrank_ker T
  have hrange : LinearMap.range T = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    have hfk : finrank ℝ (Fin k → ℝ) = k := by simp
    rw [hker, hdual] at hrk
    rw [hfk]
    omega
  -- surjectivity produces the dual family, whence independence
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  obtain ⟨u, hu⟩ : ∃ u : V →L[ℝ] ℝ, T u = fun i => if i = j then (1 : ℝ) else 0 := by
    have : (fun i => if i = j then (1 : ℝ) else 0) ∈ LinearMap.range T := by
      rw [hrange]; trivial
    exact this
  have hval : ∀ i, u (x i) = if i = j then (1 : ℝ) else 0 := by
    intro i
    have : T u i = (fun i => if i = j then (1 : ℝ) else 0) i := by rw [hu]
    exact this
  have := congrArg u hg
  rw [map_sum, map_zero] at this
  simp only [map_smul, smul_eq_mul, hval] at this
  simpa using this

/-- The surjectivity paragraph of Theorem 6.1: a lex cone `Q` modulo `Mq` on the whole dual
of `V`, together with an order-convex submodule `Nq` above `Mq` with nonzero
pre-annihilator, is put into normal form by a suitable basis of `V`. -/
theorem exists_adapted_basis
    {Q : Set (V →L[ℝ] ℝ)} {Mq Nq : Submodule ℝ (V →L[ℝ] ℝ)}
    (hQ : IsLexConeModOn ⊤ Mq Q)
    (hMN : Mq ≤ Nq)
    (hoc : ConvexFilter.IsOrderConvex Q Nq)
    (hd : preAnnih Nq ≠ ⊥) :
    ∃ (b : Basis (Fin (finrank ℝ V)) ℝ V) (d m : ℕ),
      1 ≤ d ∧ d ≤ m ∧ m ≤ finrank ℝ V ∧
      Q = Q0 b m ∧
      (Mq : Set (V →L[ℝ] ℝ)) = M0 b m ∧
      preAnnih Nq = Submodule.span ℝ (Set.range (fun i : Fin d => basisAt b (i : ℕ))) := by
  classical
  -- Step 1: the normal form of `Q` in the dual
  obtain ⟨k, l, hk, hlM, hlsep, hQeq⟩ := exists_functionals_mod hQ
  have hdual : finrank ℝ (V →L[ℝ] ℝ) = finrank ℝ V := by
    have e : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V →L[ℝ] ℝ) := LinearMap.toContinuousLinearMap
    rw [← e.finrank_eq]
    exact Subspace.dual_finrank_eq
  have hktop : k + finrank ℝ Mq = finrank ℝ V := by
    rw [hk, finrank_top, hdual]
  -- Step 2: the functionals are evaluations at points of `V`
  choose x hx using fun i : Fin k => ConvexFilter.exists_point_of_dual_functional (l i)
  have hMker : ∀ i, ∀ u ∈ Mq, u (x i) = 0 := by
    intro i u hu
    rw [← hx i u]
    exact hlM i u hu
  have hsep : ∀ u : V →L[ℝ] ℝ, (∀ i, u (x i) = 0) → u ∈ Mq := by
    intro u hu
    refine hlsep u Submodule.mem_top fun i => ?_
    rw [hx i u]
    exact hu i
  -- Step 3: the points are linearly independent
  have hli : LinearIndependent ℝ x := linearIndependent_of_eval hMker hsep hktop
  -- Step 5: extend them to a basis
  obtain ⟨b, hb⟩ := exists_basis_extending x hli
  have hbnat : ∀ (i : ℕ) (h : i < k), basisAt b i = x ⟨i, h⟩ := fun i h => hb ⟨i, h⟩
  -- Step 4: `Nq` is a flag
  have hocl : ConvexFilter.IsOrderConvex (lexConeMod ⊤ Mq l) Nq := by
    rw [← hQeq]; exact hoc
  obtain ⟨r, hrk, hNq⟩ := exists_eq_flagMod hlM hlsep hMN le_top hocl
  -- the pre-annihilator of the flag is the span of the first `r` points
  have hpre : preAnnih Nq = Submodule.span ℝ (Set.range (fun i : Fin r => basisAt b (i : ℕ))) := by
    have hkn : k ≤ finrank ℝ V := by omega
    apply le_antisymm
    · intro v hv
      rw [← b.sum_repr v]
      refine Submodule.sum_mem _ fun i _ => ?_
      by_cases hi : (i : ℕ) < r
      · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨(i : ℕ), hi⟩, ?_⟩)
        show basisAt b (i : ℕ) = b i
        rw [basisAt, dif_pos i.isLt]
      · -- the coordinate functional at `i` lies in `Nq`, so the coordinate vanishes
        have hcoord : LinearMap.toContinuousLinearMap (b.coord i) ∈ Nq := by
          rw [hNq]
          refine ⟨Submodule.mem_top, fun jj hjj => ?_⟩
          have hjn : (jj : ℕ) < finrank ℝ V := lt_of_lt_of_le jj.isLt hkn
          have hxjj : x jj = b ⟨(jj : ℕ), hjn⟩ := by
            have h1 := hb jj
            rw [basisAt, dif_pos hjn] at h1
            exact h1.symm
          have hij : (⟨(jj : ℕ), hjn⟩ : Fin (finrank ℝ V)) ≠ i := by
            intro hcon
            have hval : (i : ℕ) = (jj : ℕ) := by rw [← hcon]
            omega
          rw [hx jj, hxjj]
          show (b.coord i) (b ⟨(jj : ℕ), hjn⟩) = 0
          rw [Basis.coord_apply, Basis.repr_self_apply, if_neg hij]
        have hzero : (b.repr v) i = 0 := by
          have := mem_preAnnih_iff.1 hv _ hcoord
          simpa [Basis.coord_apply] using this
        rw [hzero, zero_smul]
        exact Submodule.zero_mem _
    · rw [Submodule.span_le]
      rintro w ⟨i, rfl⟩
      refine mem_preAnnih_iff.2 fun u hu => ?_
      rw [hNq] at hu
      have hik : (i : ℕ) < k := lt_of_lt_of_le i.isLt hrk
      show u (basisAt b (i : ℕ)) = 0
      rw [hbnat (i : ℕ) hik, ← hx ⟨(i : ℕ), hik⟩ u]
      exact hu.2 ⟨(i : ℕ), hik⟩ i.isLt
  -- `1 ≤ r`
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with rfl | hpos
    · exfalso
      apply hd
      rw [hpre]
      simp
    · exact hpos
  refine ⟨b, r, k, hr1, hrk, by omega, ?_, ?_, hpre⟩
  · -- `Q = Q0 b k`
    rw [hQeq]
    ext u
    constructor
    · rintro ⟨-, j, hj, hj0⟩
      refine ⟨(j : ℕ), j.isLt, ?_, ?_⟩
      · rw [hbnat (j : ℕ) j.isLt, ← hx j u]
        simpa using hj
      · intro i hi
        have hik : i < k := lt_trans hi j.isLt
        rw [hbnat i hik, ← hx ⟨i, hik⟩ u]
        exact hj0 ⟨i, hik⟩ (by simpa [Fin.lt_def] using hi)
    · rintro ⟨j, hjk, hj, hj0⟩
      refine ⟨Submodule.mem_top, ⟨j, hjk⟩, ?_, ?_⟩
      · rw [hx ⟨j, hjk⟩ u, ← hbnat j hjk]
        exact hj
      · intro i hi
        have hi' : (i : ℕ) < j := by simpa [Fin.lt_def] using hi
        rw [hx i u, ← hbnat (i : ℕ) i.isLt]
        exact hj0 (i : ℕ) hi'
  · -- `Mq = M0 b k`
    ext u
    constructor
    · intro hu i hi
      rw [hbnat i hi]
      exact hMker ⟨i, hi⟩ u hu
    · intro hu
      refine hsep u fun i => ?_
      have := hu (i : ℕ) i.isLt
      rwa [hbnat (i : ℕ) i.isLt] at this

end PartD

end ConvexFilter.Adapted
