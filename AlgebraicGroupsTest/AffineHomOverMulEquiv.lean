/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.GroupScheme.AffineHomOverConvolution
import Mathlib.Algebra.Group.Nat.Hom
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra

/-!
# Global-sections convolution for integer points of multiplicative affine one-space

The stock monoid-algebra lift constructs integer-valued points, and `Spec.mapMulEquiv`
turns them into scheme points with source `Spec ℤ`. The global-sections equivalence
preserves their product and unit. Its affine specialization identifies the coordinates
of the point with generator value `2` only after applying `ΓSpecIso ℤ` to the coefficients.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.MultiplicativeAffineLine

private abbrev coordinateRing := MonoidAlgebra ℤ (Multiplicative ℕ)

private abbrev base : Over (Spec (.of ℤ)) :=
  (Spec (.of ℤ)).asOver (Spec (.of ℤ))

private def integerPoint (k : ℤ) : WithConv (coordinateRing →ₐ[ℤ] ℤ) :=
  MonoidAlgebra.liftMulEquiv (R := ℤ) (A := ℤ) (M := Multiplicative ℕ)
    (powersMulHom ℤ k)

private def schemePoint (k : ℤ) :
    base ⟶ (Spec (.of coordinateRing)).asOver (Spec (.of ℤ)) :=
  Spec.mapMulEquiv (R := ℤ) (S := coordinateRing) (T := ℤ) (integerPoint k)

private abbrev Φ :
    (base ⟶ (Spec (.of coordinateRing)).asOver (Spec (.of ℤ))) ≃*
      WithConv (coordinateRing →ₐ[ℤ] ((algΓ (.of ℤ)).obj base).unop) :=
  TauCeti.CommHopfAlgCat.schemePointsAlgΓMulEquiv (R := ℤ) coordinateRing base

-- Pointwise multiplication of the points with generator values `2` and `3` is convolution.
private theorem point_map_mul : Φ (schemePoint 2 * schemePoint 3) =
    Φ (schemePoint 2) * Φ (schemePoint 3) :=
  map_mul Φ (schemePoint 2) (schemePoint 3)

-- The coefficients live in global sections, not definitionally in `ℤ`.
private theorem point_toRingHom :
    (Scheme.ΓSpecIso (.of ℤ)).hom.hom.comp (Φ (schemePoint 2)).ofConv.toRingHom =
      (integerPoint 2).ofConv.toRingHom := by
  exact (schemePointsAlgΓMulEquiv_spec ℤ coordinateRing ℤ (schemePoint 2)).trans
    (congrArg (fun q : WithConv (coordinateRing →ₐ[ℤ] ℤ) ↦ q.ofConv.toRingHom)
      ((Spec.mapMulEquiv (R := ℤ) (S := coordinateRing) (T := ℤ)).symm_apply_apply
        (integerPoint 2)))

private theorem point_map_one : Φ 1 = 1 := map_one Φ

end AlgebraicGeometry.MultiplicativeAffineLine
