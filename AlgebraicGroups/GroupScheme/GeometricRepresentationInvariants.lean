/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.AffineRepresentation

/-!
# Invariants of geometric representations

The invariants of a geometric representation on `V` form a submodule of `V`:
a vector is invariant if its image `1 ⊗ v` is fixed by every scheme point over
every coefficient algebra. This is an intersection of linear kernels and does
not require the group scheme to be affine or the module to be finite-dimensional.

`GeometricRepresentation.mem_invariants_iff` characterizes this submodule.
`GeometricRepresentation.apply_subtype_baseChange_invariants` shows that every
point fixes the image of its scalar-extended subtype inclusion.

## Implementation notes

The test algebras range over all objects of `CommAlgCat.{u, u} K`, with no
finite-generation restriction. The universe of `V` is independent of `u`.
The construction and its fixedness results require only a commutative base ring.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 4, Proposition 4.31,
  for invariants and further scalar extension over a field.
* Mathlib's submodule intersections, linear kernels and tensor products.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct CategoryTheory.GrpObj

universe u v

namespace AlgebraicGeometry
namespace GeometricRepresentation

variable {K : Type u} [CommRing K] {G : Scheme.{u}}
  [G.Over (Spec (.of K))] [GrpObj (G.asOver (Spec (.of K)))]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- The submodule of vectors whose images `1 ⊗ v` are fixed by all scheme points
over all coefficient algebras. No finite-generation restriction is imposed on
the coefficient algebras. -/
noncomputable def invariants (η : GeometricRepresentation (K := K) G V) : Submodule K V :=
  ⨅ (S : CommAlgCat.{u, u} K)
    (g : (Spec (.of S)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))),
    LinearMap.ker
      (((η.operator S g).val.restrictScalars K - LinearMap.id).comp
        (TensorProduct.mk K S V (1 : S)))

/-- A vector is invariant if and only if every scheme point fixes its image
after every coefficient extension. -/
@[simp] theorem mem_invariants_iff (η : GeometricRepresentation (K := K) G V) (v : V) :
    v ∈ η.invariants ↔
      ∀ (S : CommAlgCat.{u, u} K)
        (g : (Spec (.of S)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))),
        (η.operator S g).val (1 ⊗ₜ[K] v) = 1 ⊗ₜ[K] v := by
  simp only [invariants, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply,
    LinearMap.sub_apply, LinearMap.restrictScalars_apply, LinearMap.id_apply,
    TensorProduct.mk_apply, sub_eq_zero]

/-- Every point fixes a pure tensor with an invariant second factor. -/
theorem apply_tmul_of_mem_invariants (η : GeometricRepresentation (K := K) G V)
    {v : V} (hv : v ∈ η.invariants) (S : CommAlgCat.{u, u} K)
    (g : (Spec (.of S)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) (s : S) :
    (η.operator S g).val (s ⊗ₜ[K] v) = s ⊗ₜ[K] v := by
  calc
    (η.operator S g).val (s ⊗ₜ[K] v) =
        (η.operator S g).val (s • (1 ⊗ₜ[K] v)) :=
      congrArg _ (TensorProduct.tmul_eq_smul_one_tmul s v)
    _ = s • (η.operator S g).val (1 ⊗ₜ[K] v) := map_smul _ _ _
    _ = s • (1 ⊗ₜ[K] v) :=
      congrArg (s • ·) ((η.mem_invariants_iff v).mp hv S g)
    _ = s ⊗ₜ[K] v := (TensorProduct.tmul_eq_smul_one_tmul s v).symm

/-- Every point fixes the image of the scalar-extended inclusion of the
invariant submodule. -/
theorem apply_subtype_baseChange_invariants (η : GeometricRepresentation (K := K) G V)
    (S : CommAlgCat.{u, u} K)
    (g : (Spec (.of S)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K)))
    (z : S ⊗[K] η.invariants) :
    (η.operator S g).val (η.invariants.subtype.baseChange S z) =
      η.invariants.subtype.baseChange S z := by
  induction z using TensorProduct.inductionOn with
  | tmul s v =>
    simpa only [LinearMap.baseChange_tmul, Submodule.subtype_apply] using
      η.apply_tmul_of_mem_invariants v.property S g s
  | add x y hx hy => simp only [map_add, hx, hy]

end GeometricRepresentation
end AlgebraicGeometry
