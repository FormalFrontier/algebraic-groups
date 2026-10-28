/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Coalgebra
public import AlgebraicGroups.Algebra.Coalgebra.FiniteSubcoalgebra
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite subcoalgebra containment and exhaustion over a field

The fundamental theorem of coalgebras gives a finite-dimensional subcoalgebra containing
any finitely generated subspace of a coalgebra over a field. Here finiteness is expressed
by `Module.Finite` on the subcoalgebra subtype, equipped with its restricted coalgebra.
The ambient coalgebra need not be finite-dimensional.

`Coalgebra.exists_finite_subcoalgebra` packages the finite submodule supplied by
`Coalgebra.exists_fg_submodule_comul_closed_of_finite` using `Subcoalgebra.mk'`.
`Coalgebra.exists_finite_subcoalgebra_of_finite` applies it to the span of a finite set.
These are existence statements: no least or uniquely determined finite subcoalgebra is
asserted.

The finite-dimensional subcoalgebras form a directed family under containment of
underlying submodules, and their union is the whole coalgebra. The same family has
supremum `⊤` in the submodule lattice. These statements use the subtype of
subcoalgebras equipped with a proof of `Module.Finite`.

## References

* J. S. Milne, *Algebraic Groups*, for the fundamental theorem of coalgebras over a field
  (bibliographic credit).
* M. E. Sweedler, *Hopf Algebras*, W. A. Benjamin, 1969, for the coefficient-coalgebra
  method used by the finite-submodule theorem.
* `AlgebraicGroups.Algebra.Coalgebra.FiniteSubcoalgebra`, for finite tensor-square-closed
  submodule containment. Its proof first uses a projective free-presentation splitting
  for a finite right coideal, then field coordinates for closure in both tensor factors.
* Mathlib's `Submodule.FG`, `Submodule.span_le`, `Submodule.fg_span` and
  `Module.Finite.iff_fg` for finite generation and the span-to-module-finiteness bridge;
  its field freeness and projectivity instances supply the finite-submodule theorem's
  projective step without an additional hypothesis.
* `AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Coalgebra`, for the restricted
  comultiplication, counit and coalgebra laws on a subcoalgebra subtype.
-/

@[expose] public section

universe u v

namespace Coalgebra

variable {K : Type u} {C : Type v}
variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

/-- The fundamental theorem of coalgebras over a field: every finitely generated subspace
is contained in a finite-dimensional subcoalgebra. This is the fundamental statement in
Milne's *Algebraic Groups*, obtained here from the finite-submodule coefficient-coalgebra
theorem and the restricted coalgebra construction. -/
theorem exists_finite_subcoalgebra (M : Submodule K C) (hM : M.FG) :
    ∃ D : Subcoalgebra K C, M ≤ D.toSubmodule ∧ Module.Finite K D := by
  obtain ⟨t, ht⟩ := hM
  obtain ⟨S, htS, hSfg, hSclosed⟩ :=
    exists_fg_submodule_comul_closed_of_finite (K := K) t.finite_toSet
  have hMS : M ≤ S := by
    rw [← ht]
    exact Submodule.span_le.mpr htS
  refine ⟨Subcoalgebra.mk' S (fun {x} hx => hSclosed x hx), ?_, ?_⟩
  · simpa only [Subcoalgebra.toSubmodule_mk'] using hMS
  · exact (Module.Finite.iff_fg.mpr hSfg : Module.Finite K S)

/-- Every finite subset of a coalgebra over a field lies in a finite-dimensional
subcoalgebra, by applying the fundamental theorem of coalgebras to its span. -/
theorem exists_finite_subcoalgebra_of_finite {s : Set C} (hs : s.Finite) :
    ∃ D : Subcoalgebra K C, s ⊆ (D : Set C) ∧ Module.Finite K D := by
  obtain ⟨D, hD, hfinite⟩ :=
    exists_finite_subcoalgebra (Submodule.span K s) (Submodule.fg_span hs)
  refine ⟨D, ?_, hfinite⟩
  intro x hx
  exact Subcoalgebra.mem_toSubmodule.mp (hD (Submodule.subset_span hx))

end Coalgebra

namespace Subcoalgebra

variable {K : Type u} {C : Type v}
variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

/-- The underlying submodules of finite-dimensional subcoalgebras of a coalgebra over a
field form a directed family. -/
theorem directed_finite_toSubmodule :
    Directed (· ≤ ·)
      (fun D : {D : Subcoalgebra K C // Module.Finite K D} => D.val.toSubmodule) := by
  intro D E
  have hfg : (D.val.toSubmodule ⊔ E.val.toSubmodule).FG :=
    (Module.Finite.iff_fg.mp D.property).sup (Module.Finite.iff_fg.mp E.property)
  obtain ⟨F, hF, hfinite⟩ :=
    Coalgebra.exists_finite_subcoalgebra (D.val.toSubmodule ⊔ E.val.toSubmodule) hfg
  exact ⟨⟨F, hfinite⟩, le_sup_left.trans hF, le_sup_right.trans hF⟩

/-- Every element of a coalgebra over a field belongs to a finite-dimensional
subcoalgebra. -/
theorem iUnion_finite_eq_univ :
    (⋃ D : {D : Subcoalgebra K C // Module.Finite K D}, (D.val : Set C)) = Set.univ := by
  apply Set.iUnion_eq_univ_iff.mpr
  intro c
  obtain ⟨D, hcD, hfinite⟩ :=
    Coalgebra.exists_finite_subcoalgebra_of_finite (K := K) (Set.finite_singleton c)
  exact ⟨⟨D, hfinite⟩, hcD (Set.mem_singleton c)⟩

/-- The directed family of finite-dimensional subcoalgebras exhausts the ambient
coalgebra at the level of underlying submodules. -/
theorem iSup_finite_toSubmodule_eq_top :
    (⨆ D : {D : Subcoalgebra K C // Module.Finite K D}, D.val.toSubmodule) = ⊤ := by
  have : Nonempty {D : Subcoalgebra K C // Module.Finite K D} := by
    obtain ⟨D, _⟩ := Set.iUnion_eq_univ_iff.mp
      (iUnion_finite_eq_univ (K := K) (C := C)) (0 : C)
    exact ⟨D⟩
  apply SetLike.coe_injective
  rw [Submodule.coe_iSup_of_directed _
    (directed_finite_toSubmodule (K := K) (C := C))]
  exact iUnion_finite_eq_univ

end Subcoalgebra
