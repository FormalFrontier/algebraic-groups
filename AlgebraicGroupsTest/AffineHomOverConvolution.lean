/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.GroupScheme.AffineHomOver
import AlgebraicGroupsTest.AffineHomOver
import Mathlib.Algebra.Group.Nat.Hom
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.Tactic.NormNum

/-!
# Integer-valued points of multiplicative affine one-space

The coordinate bialgebra is the monoid algebra `ℤ[Multiplicative ℕ]`, with its
stock group-like comultiplication. The test scheme is the countable coproduct
of `Spec ℤ`, over `Spec ℤ` by the component identities.

The points with generator values `2`, `3`, and `6` are constructed using the
monoid-algebra lift and affine `Spec.mapMulEquiv`, followed by precomposition
with the structure map. Their coordinate maps into the canonical bundled
global-sections algebra are separately constructed by scalar postcomposition.
The two stock multiplications give `2 * 3 = 6`, and restriction to component
zero distinguishes the points with values `2` and `3`. The plain affine-target
adjunction identifies these geometric and algebraic constructions.
-/

noncomputable section

open CategoryTheory Limits
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.AffineHomOverConvolutionModel

private abbrev coordinateRing := MonoidAlgebra ℤ (Multiplicative ℕ)

private abbrev affineBase : Over (Spec (.of ℤ)) :=
  (algSpec (.of ℤ)).obj (.op (CommAlgCat.of ℤ ℤ))

private abbrev affineTarget : Over (Spec (.of ℤ)) :=
  (Spec (.of coordinateRing)).asOver (Spec (.of ℤ))

private abbrev components (_ : ℕ) : Scheme.{0} := Spec (.of ℤ)

private def testSource : Over (Spec (.of ℤ)) :=
  Over.mk (Sigma.desc (f := components) (fun _ ↦ 𝟙 _))

private def structureMap : testSource ⟶ affineBase :=
  Over.homMk testSource.hom (by
    change testSource.hom ≫ Spec.map (𝟙 (CommRingCat.of ℤ)) = testSource.hom
    simp)

private def componentZero : affineBase ⟶ testSource :=
  Over.homMk (Sigma.ι components 0) (by
    let p : (n : ℕ) → components n ⟶ Spec (.of ℤ) :=
      fun _ ↦ 𝟙 (Spec (.of ℤ))
    calc
      Sigma.ι components 0 ≫ Sigma.desc p = 𝟙 (Spec (.of ℤ)) :=
        Sigma.ι_desc p 0
      _ = Spec.map (𝟙 (CommRingCat.of ℤ)) :=
        (Spec.map_id (CommRingCat.of ℤ)).symm)

private theorem componentZero_structureMap :
    componentZero ≫ structureMap = 𝟙 affineBase := by
  apply Over.OverMorphism.ext
  change Sigma.ι components 0 ≫
      Sigma.desc (f := components) (fun _ ↦ 𝟙 _) = 𝟙 _
  exact Sigma.ι_desc _ _

private def integerPoints : ℤ ≃* WithConv (coordinateRing →ₐ[ℤ] ℤ) :=
  (powersMulHom ℤ).trans
    (MonoidAlgebra.liftMulEquiv (R := ℤ) (A := ℤ) (M := Multiplicative ℕ))

private theorem integerPoints_mul :
    integerPoints 2 * integerPoints 3 = integerPoints 6 := by
  have h : (2 : ℤ) * 3 = 6 := by norm_num
  rw [← map_mul, h]

private def affinePoint (k : ℤ) : affineBase ⟶ affineTarget :=
  Spec.mapMulEquiv (R := ℤ) (S := coordinateRing) (T := ℤ) (integerPoints k)

private def geometricPoint (k : ℤ) : testSource ⟶ affineTarget :=
  structureMap ≫ affinePoint k

private theorem geometricPoint_mul :
    geometricPoint 2 * geometricPoint 3 = geometricPoint 6 := by
  have hAffine : affinePoint 2 * affinePoint 3 = affinePoint 6 :=
    (map_mul (Spec.mapMulEquiv (R := ℤ) (S := coordinateRing) (T := ℤ))
      (integerPoints 2) (integerPoints 3)).symm.trans
        (congrArg (Spec.mapMulEquiv (R := ℤ) (S := coordinateRing) (T := ℤ))
          integerPoints_mul)
  exact
    (MonObj.comp_mul structureMap (affinePoint 2) (affinePoint 3)).symm.trans
      (congrArg (fun f : affineBase ⟶ affineTarget ↦ structureMap ≫ f) hAffine)

private theorem geometricPoint_ne : geometricPoint 2 ≠ geometricPoint 3 := by
  intro h
  have hAffine : affinePoint 2 = affinePoint 3 := by
    simpa only [geometricPoint, ← Category.assoc, componentZero_structureMap,
      Category.id_comp] using
      congrArg (fun f : testSource ⟶ affineTarget ↦ componentZero ≫ f) h
  have hInt :=
    (Spec.mapMulEquiv (R := ℤ) (S := coordinateRing) (T := ℤ)).injective hAffine
  have h23 : (2 : ℤ) = 3 := integerPoints.injective hInt
  norm_num at h23

private abbrev globalSections := ((algΓ (.of ℤ)).obj testSource).unop

private def coordinatePoint (k : ℤ) : WithConv (coordinateRing →ₐ[ℤ] globalSections) :=
  WithConv.toConv ((Algebra.ofId ℤ globalSections).comp (integerPoints k).ofConv)

private theorem coordinatePoint_mul :
    coordinatePoint 2 * coordinatePoint 3 = coordinatePoint 6 := by
  apply WithConv.ofConv_injective
  change
    (WithConv.toConv ((Algebra.ofId ℤ globalSections).comp (integerPoints 2).ofConv) *
      WithConv.toConv ((Algebra.ofId ℤ globalSections).comp (integerPoints 3).ofConv)).ofConv =
      (Algebra.ofId ℤ globalSections).comp (integerPoints 6).ofConv
  rw [← AlgHom.comp_convMul_distrib, integerPoints_mul]

private theorem geometricPoint_coordinates (k : ℤ) :
    WithConv.toConv
      (affineSpecHomOverEquiv ℤ testSource coordinateRing (geometricPoint k)) =
      coordinatePoint k := by
  have hAffine : affinePoint k =
      (algSpec (.of ℤ)).map (CommAlgCat.ofHom (integerPoints k).ofConv).op := by
    apply Over.OverMorphism.ext
    rfl
  have hScalar : affineSpecHomOverEquiv ℤ testSource ℤ structureMap =
      Algebra.ofId ℤ globalSections := Subsingleton.elim _ _
  apply WithConv.ofConv_injective
  change affineSpecHomOverEquiv ℤ testSource coordinateRing
      (structureMap ≫ affinePoint k) =
    (Algebra.ofId ℤ globalSections).comp (integerPoints k).ofConv
  rw [hAffine, affineSpecHomOverEquiv_comp, hScalar]

private theorem coordinatePoint_ne : coordinatePoint 2 ≠ coordinatePoint 3 := by
  intro h
  apply geometricPoint_ne
  apply (affineSpecHomOverEquiv ℤ testSource coordinateRing).injective
  apply WithConv.toConv_injective
  rw [geometricPoint_coordinates 2, geometricPoint_coordinates 3, h]

private theorem product_coordinates :
    WithConv.toConv
      (affineSpecHomOverEquiv ℤ testSource coordinateRing
        (geometricPoint 2 * geometricPoint 3)) =
      coordinatePoint 2 * coordinatePoint 3 := by
  rw [geometricPoint_mul, geometricPoint_coordinates 6, coordinatePoint_mul]

end AlgebraicGeometry.AffineHomOverConvolutionModel
