/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Points
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Basic
public import TauCeti.AlgebraicGeometry.GroupScheme.Points
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.SchemePoints

/-!
# The units functor represented by the canonical multiplicative group

The coordinate algebra, convolution points, group scheme and point equivalences
are provided by Tau Ceti. This file gives the natural isomorphism with the
units-valued functor. The standard Laurent-polynomial algebra remains available
through Mathlib and Tau Ceti's Laurent evaluation API.

## References

J. S. Milne, Algebraic Groups (2017), item 2.2; Mathlib's spectrum-points API;
Tau Ceti's MultiplicativeGroup.Basic and DiagonalizableGroup.Scheme.Points.
-/

public section
noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj
universe u
namespace AlgebraicGeometry

/-- The group-valued functor sending a `K`-algebra to its group of units. -/
@[expose] def multiplicativeGroupFunctor
    (K : Type u) [CommRing K] : CommAlgCat K ⥤ GrpCat where
  obj R := GrpCat.of ((R : Type u)ˣ)
  map f := GrpCat.ofHom (Units.map f.hom)
  map_id R := by
    ext u
    rfl
  map_comp f g := by
    ext u
    rfl

/-- The canonical multiplicative group scheme represents the units functor. -/
def multiplicativeGroupPointsIso (K : Type u) [CommRing K] :
    multiplicativeGroupFunctor K ≅ TauCeti.GroupScheme.algebraPointsFunctor K
      (TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K) :=
  NatIso.ofComponents
    (fun A => (TauCeti.DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv
      (R := K) (A := A)).symm.toGrpIso)
    (fun {A B} f => by
      ext x
      change Aˣ at x
      change (TauCeti.DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv
        (R := K) (A := B)).symm (Units.map f.hom x) =
          (Spec.map (CommRingCat.ofHom f.hom.toRingHom)).asOver (Spec (.of K)) ≫
            (TauCeti.DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv
              (R := K) (A := A)).symm x
      apply (TauCeti.DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv
        (R := K) (A := B)).injective
      rw [MulEquiv.apply_symm_apply]
      rw [TauCeti.DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv_mapValue]
      rw [MulEquiv.apply_symm_apply]
      rfl)

/-- Maps from any base scheme to the canonical multiplicative group are its global units. -/
@[expose] def multiplicativeGroupHomUnits (K : Type u) [CommRing K]
    (X : Over (Spec (.of K))) :
    (X ⟶ (TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K).X) ≃*
      ((algΓ (.of K)).obj X).unopˣ := by
  change (X ⟶ (Spec (.of (MonoidAlgebra K
    (ULift.{u} (Multiplicative ℤ))))).asOver (Spec (.of K))) ≃* _
  exact (TauCeti.CommHopfAlgCat.schemePointsAlgΓMulEquiv (R := K)
    (MonoidAlgebra K (ULift.{u} (Multiplicative ℤ))) X).trans
      ((TauCeti.DiagonalizableGroup.pointsMulEquiv).trans
        (TauCeti.DiagonalizableGroup.uliftZPowersMulEquiv
          (((algΓ (.of K)).obj X).unopˣ)).symm)

end AlgebraicGeometry
