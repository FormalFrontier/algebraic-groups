/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.GeneralLinearCoordinateRing
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import TauCeti.AlgebraicGeometry.GroupScheme.Points

/-!
# The finite general linear group scheme

The determinant localization represents invertible square matrices over every
commutative algebra. Its Hopf structure induces a finite-type group scheme whose
affine points agree naturally, as groups, with invertible matrices. The group
law is matrix multiplication, realized by convolution on coordinate evaluations;
the represented points are morphisms from `Spec R`, not functions on field-valued
points.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2, item 2.8, p. 41: the finite
  general linear group represented by determinant localization over a field.
* Mathlib, `AlgebraicGeometry/Group/Affine`: Hopf-algebra `Spec`, the algebraic
  group of affine points, and `Spec.mapMulEquiv`.
* Mathlib, `RingTheory/Bialgebra/Convolution` and
  `CategoryTheory/Monoidal/Cartesian/Grp`: convolution multiplication of
  algebra maps and the group-valued Yoneda functor.
* Mathlib, `LinearAlgebra/Matrix/GeneralLinearGroup/Defs`,
  `AlgebraicGeometry/Morphisms/FiniteType`, and
  `AlgebraicGeometry/Morphisms/Affine`: coefficient change for invertible
  matrices, finite-type `Spec` morphisms, and quasi-compact affine morphisms.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

/-- Invertible matrices, functorial in every `K`-algebra. -/
def generalLinearIndexedFunctor : CommAlgCat K ⥤ GrpCat where
  obj R := GrpCat.of (Matrix.GeneralLinearGroup n R)
  map f := GrpCat.ofHom (Matrix.GeneralLinearGroup.map f.hom.toRingHom)
  map_id R := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rfl
  map_comp f g := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro matrix
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rfl


/-- The native general linear functor with arbitrary finite indices is
represented by the canonical coordinate Hopf algebra in the same rank. -/
def generalLinearIndexedPointsIso :
    generalLinearIndexedFunctor K n ≅
      TauCeti.GroupScheme.algebraPointsFunctor K
        (TauCeti.GeneralLinear.groupScheme K (Fintype.card n)) :=
  NatIso.ofComponents
    (fun R => ((TauCeti.GeneralLinear.reindexedPointsMulEquiv K n R).symm.trans
      (TauCeti.GeneralLinear.groupSchemePointMulEquiv
        (R := K) (Fintype.card n) R)).toGrpIso)
    (fun {R S} f => by
      ext s
      apply Over.OverMorphism.ext
      change ((TauCeti.GeneralLinear.groupSchemePointMulEquiv
        (R := K) (Fintype.card n) S)
          ((TauCeti.GeneralLinear.reindexedPointsMulEquiv K n S).symm
            (Matrix.GeneralLinearGroup.map f.hom.toRingHom s))).left =
        ((algSpec (.of K)).map f.op).left ≫
          ((TauCeti.GeneralLinear.groupSchemePointMulEquiv
            (R := K) (Fintype.card n) R)
            ((TauCeti.GeneralLinear.reindexedPointsMulEquiv K n R).symm s)).left
      rw [TauCeti.GeneralLinear.groupSchemePointMulEquiv_apply_left,
        TauCeti.GeneralLinear.groupSchemePointMulEquiv_apply_left]
      change Spec.map (CommRingCat.ofHom
        ((TauCeti.GeneralLinear.reindexedPointsMulEquiv K n S).symm
          (Matrix.GeneralLinearGroup.map f.hom.toRingHom s)).ofConv.toRingHom) ≫ _ =
        Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫ _ ≫ _
      rw [← Category.assoc, ← Spec.map_comp]
      congr 2
      have h :=
        TauCeti.GeneralLinear.mapValue_reindexedPointsMulEquiv_symm_apply K n f.hom s
      rw [AlgHom.mapValue_apply] at h
      exact congrArg (fun q => CommRingCat.ofHom q.ofConv.toRingHom) h.symm)

end AlgebraicGeometry
