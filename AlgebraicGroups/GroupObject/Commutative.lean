/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Commutativity and inversion of group objects

For a group object in a Cartesian monoidal category, commutativity is equivalent to inversion
being a monoid morphism. Mathlib supplies the forward implication as an instance.

The braiding dictionary is explicit because `IsCommMonObj` uses it. Cartesian braidings are
unique, and the canonical one is supplied by
`BraidedCategory.ofCartesianMonoidalCategory`.

## References

* J. S. Milne, *Abelian Varieties*, version 2.0 (March 16, 2008), proof of Corollary 1.4,
  printed p. 9, for the inversion criterion motivating this categorical extension.
* Mathlib, `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`, for group objects and the instance
  making inversion on a commutative group object a monoid morphism.
* Mathlib, `Mathlib.CategoryTheory.Monoidal.Cartesian.Basic`, for the canonical Cartesian
  braiding and its uniqueness.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open scoped MonObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]

/-- A group object in a Cartesian monoidal category is commutative if and only if its inversion
is a monoid morphism. This extends the inversion criterion used in the proof of Milne,
*Abelian Varieties*, Corollary 1.4 to Cartesian group objects. Mathlib supplies the forward
implication as an instance for inversion on a commutative group object. -/
theorem isCommMonObj_iff_isMonHom_inv (X : C) [GrpObj X] :
    IsCommMonObj X ↔ IsMonHom (GrpObj.inv (X := X)) := by
  constructor
  · intro h
    let := h
    infer_instance
  · intro h
    let := h
    apply (isCommMonObj_iff_isMulCommutative X).2
    intro T
    refine ⟨⟨fun f g ↦ ?_⟩⟩
    -- On every Hom group, postcomposition by inversion preserves multiplication.
    -- Comparing with the usual inverse-product identity forces commutativity.
    apply inv_injective
    calc
      (f * g)⁻¹ = f⁻¹ * g⁻¹ := by
        simpa only [Hom.inv_def] using (MonObj.mul_comp f g (GrpObj.inv (X := X)))
      _ = (g * f)⁻¹ := (mul_inv_rev g f).symm

end CategoryTheory
