/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Scheme
public import TauCeti.AlgebraicGeometry.GroupScheme.Points
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.RingTheory.FiniteType

/-!
# The additive group scheme

This file packages the affine group scheme over an arbitrary commutative base
represented by the symmetric algebra on a free module of rank one. Its affine
points are naturally the additive groups of the test algebras, expressed through
`Multiplicative` so that they are objects of `GrpCat`. The distinguished coordinate
is primitive, has zero counit, and is negated by the antipode.

## Main definitions

- `TauCeti.AdditiveGroup.groupScheme`
- `TauCeti.AdditiveGroup.gaPointsMulEquiv`
- `TauCeti.AdditiveGroup.schemePointsMulEquiv`
- `AlgebraicGeometry.additiveGroupPointsIso`
- `AlgebraicGeometry.additiveGroupCoordinateAlgEquiv`

Milne's item 2.1 describes the field-base additive group by `k[T]`, its
algebra-valued points and the primitive coproduct of `T`. The rank-one
symmetric-algebra presentation here extends the base to any commutative ring;
its identification with `Polynomial K` uses Mathlib's basis equivalence and
does not assert a separate polynomial Hopf-algebra equivalence.

## References

- J. S. Milne, *Algebraic Groups* (2017), item 2.1 (additive group and
  coordinate coproduct).
- Mathlib, `Mathlib.RingTheory.Bialgebra.SymmetricAlgebra`,
  `Mathlib.LinearAlgebra.SymmetricAlgebra.Basis` (polynomial coordinates),
  `Mathlib.Algebra.MvPolynomial.Equiv` (one variable), and
  `Mathlib.Algebra.WithConv` (`WithConv.equiv`),
  `Mathlib.RingTheory.Bialgebra.Convolution` (`AlgHom.convMul_apply`), and
  `Mathlib.AlgebraicGeometry.Group.Affine` (`Spec.mapMulEquiv` and affine points).
-/

public section

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

/-- The standard polynomial presentation of the additive-group coordinate ring. -/
@[expose] def additiveGroupCoordinateAlgEquiv
  (K : Type u) [CommRing K] :
    (SymmetricAlgebra K K) ≃ₐ[K] Polynomial K :=
  (SymmetricAlgebra.equivMvPolynomial (Module.Basis.singleton Unit K)).trans
    (MvPolynomial.uniqueAlgEquiv K Unit)

/-- The universal coordinate is sent to `Polynomial.X` by the standard polynomial
presentation. -/
@[simp]
theorem additiveGroupCoordinateAlgEquiv_coordinate
    (K : Type u) [CommRing K] :
    additiveGroupCoordinateAlgEquiv K ((SymmetricAlgebra.ι K K 1)) = Polynomial.X := by
  change (MvPolynomial.uniqueAlgEquiv K Unit)
    ((SymmetricAlgebra.equivMvPolynomial (Module.Basis.singleton Unit K))
      (SymmetricAlgebra.ι K K 1)) = Polynomial.X
  have h := SymmetricAlgebra.equivMvPolynomial_ι_apply
    (Module.Basis.singleton Unit K) default
  simp only [Module.Basis.singleton_apply] at h
  rw [h]
  simp

/-- The group-valued functor sending a `K`-algebra to its additive group.
`Multiplicative` changes only the operation tag required by `GrpCat`. -/
@[expose] def additiveGroupFunctor
    (K : Type u) [CommRing K] : CommAlgCat K ⥤ GrpCat where
  obj R := GrpCat.of (Multiplicative R)
  map f := GrpCat.ofHom (AddMonoidHom.toMultiplicative f.hom.toAddMonoidHom)
  map_id _ := by
    apply GrpCat.hom_ext
    rfl
  map_comp _ _ := by
    apply GrpCat.hom_ext
    rfl

/-- The affine additive group scheme represents the additive-group functor.
This extends the field-base additive group of Milne, *Algebraic Groups*
(2017), item 2.1, to an arbitrary commutative base ring. -/
@[expose] def additiveGroupPointsIso
    (K : Type u) [CommRing K] :
    additiveGroupFunctor K ≅
      TauCeti.GroupScheme.algebraPointsFunctor K (TauCeti.AdditiveGroup.groupScheme K) :=
  NatIso.ofComponents
    (fun R ↦ ((TauCeti.AdditiveGroup.schemePointsMulEquiv (R := K) R).symm).toGrpIso)
    (fun {R S} f ↦ by
      ext r
      change Multiplicative R at r
      change (TauCeti.AdditiveGroup.schemePointsMulEquiv (R := K) S).symm
        (.ofAdd (f.hom r.toAdd)) =
        (Spec.map (CommRingCat.ofHom f.hom.toRingHom)).asOver (Spec (.of K)) ≫
          (TauCeti.AdditiveGroup.schemePointsMulEquiv (R := K) R).symm r
      apply (TauCeti.AdditiveGroup.schemePointsMulEquiv (R := K) S).injective
      rw [MulEquiv.apply_symm_apply]
      rw [TauCeti.AdditiveGroup.schemePointsMulEquiv_mapValue]
      rw [MulEquiv.apply_symm_apply])

end AlgebraicGeometry
