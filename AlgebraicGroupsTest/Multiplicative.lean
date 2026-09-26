/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import AlgebraicGroups.GroupScheme.Multiplicative

set_option warningAsError true

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

universe u

variable (K R : Type u)
variable [CommRing K] [CommRing R] [Algebra K R]

private theorem persistentTestMultiplicative001 : Algebra.FiniteType K (multiplicativeGroupCoordinateRing K) :=
  inferInstance

private theorem persistentTestMultiplicative002 : LocallyOfFiniteType (multiplicativeGroupUnderlyingScheme K).hom :=
  inferInstance

private theorem persistentTestMultiplicative003 : QuasiCompact (multiplicativeGroupUnderlyingScheme K).hom :=
  inferInstance

private noncomputable def persistentTestMultiplicative004 : Rˣ ≃* WithConv (multiplicativeGroupCoordinateRing K →ₐ[K] R) :=
  multiplicativeGroupMulEquivAlgHom K R

private noncomputable def persistentTestMultiplicative005 : Rˣ ≃* ((Spec (.of R)).asOver (Spec (.of K)) ⟶
    multiplicativeGroupUnderlyingScheme K) :=
  multiplicativeGroupMulEquivPoints K R

private theorem persistentTestMultiplicative006 (u : Rˣ) :
    (multiplicativeGroupMulEquivAlgHom K R u).ofConv
        (multiplicativeGroupCoordinate K) = u :=
  multiplicativeGroupMulEquivAlgHom_coordinate K R u

private theorem persistentTestMultiplicative007 {S : Type u} [CommRing S] [Algebra K S]
    (f : R →ₐ[K] S) (u : Rˣ) :
    (multiplicativeGroupMulEquivAlgHom K S (Units.map f u)).ofConv =
      f.comp (multiplicativeGroupMulEquivAlgHom K R u).ofConv :=
  multiplicativeGroupMulEquivAlgHom_naturality K R f u

private theorem persistentTestMultiplicative008 (u : Rˣ) :
    (multiplicativeGroupMulEquivPoints K R u).left =
      Spec.map (CommRingCat.ofHom
        (multiplicativeGroupMulEquivAlgHom K R u).ofConv.toRingHom) :=
  multiplicativeGroupMulEquivPoints_apply_left K R u

private theorem persistentTestMultiplicative009 :
    CoalgebraStruct.comul (multiplicativeGroupCoordinate K) =
      multiplicativeGroupCoordinate K ⊗ₜ[K] multiplicativeGroupCoordinate K :=
  multiplicativeGroupCoordinate_comul K

-- The entire API remains available when the target algebra is the zero ring.
private noncomputable def persistentTestMultiplicative010 [Subsingleton R] :
    Rˣ ≃* ((Spec (.of R)).asOver (Spec (.of K)) ⟶
      multiplicativeGroupUnderlyingScheme K) :=
  multiplicativeGroupMulEquivPoints K R

private noncomputable def persistentTestMultiplicative011 :
    (ZMod 1)ˣ ≃* WithConv
      (multiplicativeGroupCoordinateRing (ZMod 1) →ₐ[ZMod 1] ZMod 1) :=
  multiplicativeGroupMulEquivAlgHom (ZMod 1) (ZMod 1)

end AlgebraicGeometry
