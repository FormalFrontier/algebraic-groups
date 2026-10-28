/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.UnitriangularBaseChange
public import Mathlib.Data.ZMod.Basic

/-!
# Scalar-extended unitriangular group-scheme clients

The rank-three client multiplies points of the actual pulled-back group,
maps their product through the native group isomorphism, and reads its
upper-right matrix entry. The cross term distinguishes this group law from
the additive law on the underlying affine space.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry UnitriangularCoordinateRing
open scoped CategoryTheory.MonObj TensorProduct

universe u

example (R S T : Type) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T]
    (a b : TauCeti.upperUnitriangularGroup (Fin 3) T)
    (p q : (Spec (.of T)).asOver (Spec (.of S)) ⟶
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp.obj
        ((TauCeti.UpperUnitriangular.groupScheme R (Fin 3)))).X)
    (hp : p ≫ (unitriangularGroupSchemeBaseChangeIso R S (Fin 3)).hom.hom.hom =
      (TauCeti.UpperUnitriangular.schemePointsMulEquiv (R := S) (A := T) (Fin 3)).symm a)
    (hq : q ≫ (unitriangularGroupSchemeBaseChangeIso R S (Fin 3)).hom.hom.hom =
      (TauCeti.UpperUnitriangular.schemePointsMulEquiv (R := S) (A := T) (Fin 3)).symm b) :
    (Spec.preimage (((p * q) ≫
      (unitriangularGroupSchemeBaseChangeIso R S (Fin 3)).hom.hom.hom).left)).hom
        ((TauCeti.UpperUnitriangular.coordinateHopfAlgebraAlgEquiv S (Fin 3)
          (TauCeti.UpperUnitriangular.genericMatrix S (Fin 3) 0 2))) =
      a.1 0 2 + b.1 0 2 + a.1 0 1 * b.1 1 2 := by
  have hproduct : (p * q) ≫
        (unitriangularGroupSchemeBaseChangeIso R S (Fin 3)).hom.hom.hom =
      (TauCeti.UpperUnitriangular.schemePointsMulEquiv (R := S) (A := T) (Fin 3)).symm (a * b) := by
    erw [MonObj.mul_comp, hp, hq, map_mul]
  rw [hproduct, TauCeti.UpperUnitriangular.schemePointsMulEquiv_symm_apply,
    TauCeti.UpperUnitriangular.groupSchemePointMulEquiv_apply_left]
  change (Spec.preimage (Spec.map (CommRingCat.ofHom
    ((TauCeti.UpperUnitriangular.pointsMulEquiv S (Fin 3) (A := T)).symm
      (a * b)).ofConv.toRingHom))).hom
        (TauCeti.UpperUnitriangular.coordinateHopfAlgebraAlgEquiv S (Fin 3)
          (TauCeti.UpperUnitriangular.genericMatrix S (Fin 3) 0 2)) = _
  rw [Spec.preimage_map, TauCeti.UpperUnitriangular.pointsMulEquiv_symm_apply]
  change (TauCeti.UpperUnitriangular.upperUnitriangularToPoint S (Fin 3) (a * b)).ofConv
    (TauCeti.UpperUnitriangular.coordinateHopfAlgebraAlgEquiv S (Fin 3)
      (TauCeti.UpperUnitriangular.genericMatrix S (Fin 3) 0 2)) = _
  rw [TauCeti.UpperUnitriangular.genericMatrix_apply_of_lt S (Fin 3) (by decide),
    TauCeti.UpperUnitriangular.upperUnitriangularToPoint_apply]
  change ((a.1 : Matrix (Fin 3) (Fin 3) T) * (b.1 : Matrix (Fin 3) (Fin 3) T)) 0 2 = _
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  simp
  ring

example (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (n : Type u) [Fintype n] [LinearOrder n] :
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp.obj
      ((TauCeti.UpperUnitriangular.groupScheme R n))) ≅
        (TauCeti.UpperUnitriangular.groupScheme S n) :=
  unitriangularGroupSchemeBaseChangeIso R S n

example :
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (ZMod 1) (ZMod 1))))).mapGrp.obj
      ((TauCeti.UpperUnitriangular.groupScheme (ZMod 1) (Fin 0)))) ≅
        (TauCeti.UpperUnitriangular.groupScheme (ZMod 1) (Fin 0)) :=
  unitriangularGroupSchemeBaseChangeIso (ZMod 1) (ZMod 1) (Fin 0)

example :
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (ZMod 1) (ZMod 1))))).mapGrp.obj
      ((TauCeti.UpperUnitriangular.groupScheme (ZMod 1) (Fin 1)))) ≅
        (TauCeti.UpperUnitriangular.groupScheme (ZMod 1) (Fin 1)) :=
  unitriangularGroupSchemeBaseChangeIso (ZMod 1) (ZMod 1) (Fin 1)
