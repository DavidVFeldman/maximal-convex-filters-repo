import ConvexFilters.SpaceTop
import ConvexFilters.WedgeGen

/-!
# The Hausdorff quotient: Corollary 9.7 (WO-11, Part A)

Corollary 9.7 of the paper says that, in the maximal Hausdorff quotient `hM(V)`, the filter
`F_A` of stratum `(d, d)` is identified with both filters `F₊`, `F₋` of stratum `(d, d+1)`
over the pair `A ⊆ S`.  Its content, and the form proved first here, is that nothing
Hausdorff can tell the three apart:

* `eq_of_continuous_of_not_separated`: two maximal filters that are not `Separated` have the
  same image under every continuous map to a Hausdorff space.

The three instances of the corollary, for the general `(d, d)` and `(d, d+1)` filters of
`ConvexFilters/WedgeGen.lean`, are then

* `eq_of_continuous_FA_Fplus`,
* `eq_of_continuous_FA_Fminus`,
* `eq_of_continuous_Fplus_Fminus`,

the third by transitivity of equality — which is the formal content of the remark that the
collapse is forced even though `Fplus` and `Fminus` are *themselves* separated, by
`separated_gen`.

## The quotient in Mathlib's language

Mathlib at the pinned revision does have the maximal Hausdorff quotient: `t2Setoid X` is
the smallest equivalence relation with Hausdorff quotient, `T2Quotient X` the quotient,
`T2Quotient.mk` the projection, and `T2Quotient.lift`, `T2Quotient.lift_mk`,
`T2Quotient.mk_eq` its universal property (`Mathlib/Topology/Separation/Hausdorff.lean`).
The search is recorded in `reports/WO-11/REPORT.md`.  Corollary 9.7 is therefore also
stated verbatim in that language:

* `t2Quotient_mk_eq_of_not_separated`,
* `t2Quotient_mk_eq_FA_Fplus`, `t2Quotient_mk_eq_FA_Fminus`, `t2Quotient_mk_eq_Fplus_Fminus`.
-/

namespace ConvexFilter

namespace Space

section Quotient

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Corollary 9.7, the underlying statement.** Two maximal convex filters that cannot be
separated by disjoint neighbourhoods have the same image under every continuous map to a
Hausdorff space: if the images differed, disjoint neighbourhoods of them would pull back to
disjoint open sets separating the two filters, contradicting `h` through
`separated_iff_disjoint_nhds`. -/
theorem eq_of_continuous_of_not_separated {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {F F' : MaxFilter V} (h : ¬ Separated F.1 F'.1) (f : MaxFilter V → Y)
    (hf : Continuous f) : f F = f F' := by
  by_contra hne
  obtain ⟨U, W, hU, hW, hFU, hF'W, hdisj⟩ := t2_separation hne
  exact h (separated_iff_disjoint_nhds.mpr
    ⟨f ⁻¹' U, f ⁻¹' W, hU.preimage hf, hW.preimage hf, hFU, hF'W, hdisj.preimage f⟩)

/-- Corollary 9.7 in the language of Mathlib's maximal Hausdorff quotient: two maximal
convex filters that cannot be separated have the same image in `T2Quotient (MaxFilter V)`. -/
theorem t2Quotient_mk_eq_of_not_separated {F F' : MaxFilter V} (h : ¬ Separated F.1 F'.1) :
    T2Quotient.mk F = T2Quotient.mk F' := by
  rw [T2Quotient.mk_eq]
  intro s hs
  have hcont : Continuous (Quotient.mk s) := continuous_quotient_mk'
  exact Quotient.eq.mp (eq_of_continuous_of_not_separated h (Quotient.mk s) hcont)

/-! ### The three instances of Corollary 9.7

The hypotheses are those of `not_separated_gen` (Theorem 9.5, first clause): a `d`-flat `A`
cut out inside a `(d+1)`-flat `S` by `u = c`, the filter `FA` of stratum `(d, d)` with flat
`A` containing `A`, and the filters `Fplus`, `Fminus` of stratum `(d, d+1)` with flat `A`,
support `S`, the escape data of `FA`, and approach from the sides `u > c` and `u < c`
respectively. -/

section Instances

variable {A S : AffineSubspace ℝ V} {u : V →L[ℝ] ℝ} {c : ℝ}
variable {FA Fplus Fminus : MaxFilter V}

/-- **Corollary 9.7, first instance.** The filter `FA` of stratum `(d, d)` and the filter
`Fplus` of stratum `(d, d+1)` approaching `A` inside `S` from the side `u > c` have the same
image under every continuous map to a Hausdorff space. -/
theorem eq_of_continuous_FA_Fplus
    (hAeq : (A : Set V) = (S : Set V) ∩ {x : V | u x = c})
    (hdA : 1 ≤ Module.finrank ℝ A.direction)
    (hcodim : Module.finrank ℝ S.direction = Module.finrank ℝ A.direction + 1)
    (hAsetFA : Aset FA.1 = (A : Set V)) (hAmem : (A : Set V) ∈ FA.1.carrier)
    (hAsetFp : Aset Fplus.1 = (A : Set V)) (hSmem : (S : Set V) ∈ Fplus.1.carrier)
    (hEsc : Eset Fplus.1 = Eset FA.1) (hside : halfLE u c ∉ Fplus.1.carrier)
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] (f : MaxFilter V → Y) (hf : Continuous f) :
    f FA = f Fplus :=
  eq_of_continuous_of_not_separated
    (not_separated_gen hAeq hdA hcodim FA.2 Fplus.2 hAsetFA hAmem hAsetFp hSmem hEsc hside) f hf

/-- **Corollary 9.7, second instance.** The filter `FA` of stratum `(d, d)` and the filter
`Fminus` of stratum `(d, d+1)` approaching `A` inside `S` from the side `u < c` have the
same image under every continuous map to a Hausdorff space.  This is the first instance
applied to the functional `-u` and the level `-c`. -/
theorem eq_of_continuous_FA_Fminus
    (hAeq : (A : Set V) = (S : Set V) ∩ {x : V | u x = c})
    (hdA : 1 ≤ Module.finrank ℝ A.direction)
    (hcodim : Module.finrank ℝ S.direction = Module.finrank ℝ A.direction + 1)
    (hAsetFA : Aset FA.1 = (A : Set V)) (hAmem : (A : Set V) ∈ FA.1.carrier)
    (hAsetFm : Aset Fminus.1 = (A : Set V)) (hSmem : (S : Set V) ∈ Fminus.1.carrier)
    (hEsc : Eset Fminus.1 = Eset FA.1) (hside : halfGE u c ∉ Fminus.1.carrier)
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] (f : MaxFilter V → Y) (hf : Continuous f) :
    f FA = f Fminus := by
  refine eq_of_continuous_FA_Fplus (u := -u) (c := -c) ?_ hdA hcodim hAsetFA hAmem hAsetFm
    hSmem hEsc ?_ f hf
  · rw [hAeq]
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, ContinuousLinearMap.neg_apply, neg_inj]
  · rwa [halfLE_neg]

/-- **Corollary 9.7, third instance.** The two filters of stratum `(d, d+1)` approaching `A`
inside `S` from opposite sides have the same image under every continuous map to a Hausdorff
space, by transitivity of equality through `FA`.  This is the formal content of the remark
that the collapse is forced even though `Fplus` and `Fminus` are themselves separated, by
`separated_gen`. -/
theorem eq_of_continuous_Fplus_Fminus
    (hAeq : (A : Set V) = (S : Set V) ∩ {x : V | u x = c})
    (hdA : 1 ≤ Module.finrank ℝ A.direction)
    (hcodim : Module.finrank ℝ S.direction = Module.finrank ℝ A.direction + 1)
    (hAsetFA : Aset FA.1 = (A : Set V)) (hAmem : (A : Set V) ∈ FA.1.carrier)
    (hAsetFp : Aset Fplus.1 = (A : Set V)) (hSmemp : (S : Set V) ∈ Fplus.1.carrier)
    (hEscp : Eset Fplus.1 = Eset FA.1) (hsidep : halfLE u c ∉ Fplus.1.carrier)
    (hAsetFm : Aset Fminus.1 = (A : Set V)) (hSmemm : (S : Set V) ∈ Fminus.1.carrier)
    (hEscm : Eset Fminus.1 = Eset FA.1) (hsidem : halfGE u c ∉ Fminus.1.carrier)
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] (f : MaxFilter V → Y) (hf : Continuous f) :
    f Fplus = f Fminus :=
  (eq_of_continuous_FA_Fplus hAeq hdA hcodim hAsetFA hAmem hAsetFp hSmemp hEscp hsidep
      f hf).symm.trans
    (eq_of_continuous_FA_Fminus hAeq hdA hcodim hAsetFA hAmem hAsetFm hSmemm hEscm hsidem f hf)

/-- Corollary 9.7, first instance, in the language of the maximal Hausdorff quotient. -/
theorem t2Quotient_mk_eq_FA_Fplus
    (hAeq : (A : Set V) = (S : Set V) ∩ {x : V | u x = c})
    (hdA : 1 ≤ Module.finrank ℝ A.direction)
    (hcodim : Module.finrank ℝ S.direction = Module.finrank ℝ A.direction + 1)
    (hAsetFA : Aset FA.1 = (A : Set V)) (hAmem : (A : Set V) ∈ FA.1.carrier)
    (hAsetFp : Aset Fplus.1 = (A : Set V)) (hSmem : (S : Set V) ∈ Fplus.1.carrier)
    (hEsc : Eset Fplus.1 = Eset FA.1) (hside : halfLE u c ∉ Fplus.1.carrier) :
    T2Quotient.mk FA = T2Quotient.mk Fplus :=
  eq_of_continuous_FA_Fplus hAeq hdA hcodim hAsetFA hAmem hAsetFp hSmem hEsc hside
    T2Quotient.mk (T2Quotient.continuous_mk _)

/-- Corollary 9.7, second instance, in the language of the maximal Hausdorff quotient. -/
theorem t2Quotient_mk_eq_FA_Fminus
    (hAeq : (A : Set V) = (S : Set V) ∩ {x : V | u x = c})
    (hdA : 1 ≤ Module.finrank ℝ A.direction)
    (hcodim : Module.finrank ℝ S.direction = Module.finrank ℝ A.direction + 1)
    (hAsetFA : Aset FA.1 = (A : Set V)) (hAmem : (A : Set V) ∈ FA.1.carrier)
    (hAsetFm : Aset Fminus.1 = (A : Set V)) (hSmem : (S : Set V) ∈ Fminus.1.carrier)
    (hEsc : Eset Fminus.1 = Eset FA.1) (hside : halfGE u c ∉ Fminus.1.carrier) :
    T2Quotient.mk FA = T2Quotient.mk Fminus :=
  eq_of_continuous_FA_Fminus hAeq hdA hcodim hAsetFA hAmem hAsetFm hSmem hEsc hside
    T2Quotient.mk (T2Quotient.continuous_mk _)

/-- **Corollary 9.7 in the language of the maximal Hausdorff quotient.** The three filters
`FA`, `Fplus`, `Fminus` have the same image in `T2Quotient (MaxFilter V)`. -/
theorem t2Quotient_mk_eq_Fplus_Fminus
    (hAeq : (A : Set V) = (S : Set V) ∩ {x : V | u x = c})
    (hdA : 1 ≤ Module.finrank ℝ A.direction)
    (hcodim : Module.finrank ℝ S.direction = Module.finrank ℝ A.direction + 1)
    (hAsetFA : Aset FA.1 = (A : Set V)) (hAmem : (A : Set V) ∈ FA.1.carrier)
    (hAsetFp : Aset Fplus.1 = (A : Set V)) (hSmemp : (S : Set V) ∈ Fplus.1.carrier)
    (hEscp : Eset Fplus.1 = Eset FA.1) (hsidep : halfLE u c ∉ Fplus.1.carrier)
    (hAsetFm : Aset Fminus.1 = (A : Set V)) (hSmemm : (S : Set V) ∈ Fminus.1.carrier)
    (hEscm : Eset Fminus.1 = Eset FA.1) (hsidem : halfGE u c ∉ Fminus.1.carrier) :
    T2Quotient.mk Fplus = T2Quotient.mk Fminus :=
  eq_of_continuous_Fplus_Fminus hAeq hdA hcodim hAsetFA hAmem hAsetFp hSmemp hEscp hsidep
    hAsetFm hSmemm hEscm hsidem T2Quotient.mk (T2Quotient.continuous_mk _)

end Instances

end Quotient

end Space

end ConvexFilter
