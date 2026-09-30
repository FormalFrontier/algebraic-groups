module

public import AlgebraicGroups.GroupScheme.UnitriangularBaseChangeCoherence
public import Mathlib.Data.ZMod.Basic

/-!
# Native scalar-tower coherence for unitriangular group-scheme points
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry UnitriangularCoordinateRing
open scoped CategoryTheory.MonObj TensorProduct

universe u

set_option maxHeartbeats 1000000 in
example (R S T U : Type)
    [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra T U]
    (a : Matrix.UnitriangularGroup (Fin 2) U)
    (p : (Spec (.of U)).asOver (Spec (.of T)) ⟶
      ((Over.pullback (unitriangularBaseMap R T)).mapGrp.obj
        (unitriangularGroupScheme R (Fin 2))).X)
    (hp : p ≫ (unitriangularGroupSchemeBaseChangeIso R T (Fin 2)).hom.hom.hom =
      unitriangularGroupMulEquivPoints T (Fin 2) U a) :
    (Spec.preimage (((p⁻¹) ≫
      (unitriangularGroupSchemeBaseChangeIso R T (Fin 2)).hom.hom.hom).left)).hom
        (quotient T (Fin 2) (GeneralLinearCoordinateRing.matrix T (Fin 2) 0 1)) =
      (Spec.preimage (((p⁻¹) ≫
        (unitriangularGroupSchemeBaseChangeTowerIso R S T (Fin 2)).hom.hom.hom ≫
        ((Over.pullback (unitriangularBaseMap S T)).mapGrp.map
          (unitriangularGroupSchemeBaseChangeIso R S (Fin 2)).hom).hom.hom ≫
        (unitriangularGroupSchemeBaseChangeIso S T (Fin 2)).hom.hom.hom).left)).hom
          (quotient T (Fin 2) (GeneralLinearCoordinateRing.matrix T (Fin 2) 0 1)) := by
  have hInverse :
      (p⁻¹) ≫ (unitriangularGroupSchemeBaseChangeIso R T (Fin 2)).hom.hom.hom =
        unitriangularGroupMulEquivPoints T (Fin 2) U (a⁻¹) := by
    rw [GrpObj.inv_comp, hp, map_inv]
  have hDirect :
      (Spec.preimage (((p⁻¹) ≫
        (unitriangularGroupSchemeBaseChangeIso R T (Fin 2)).hom.hom.hom).left)).hom
          (quotient T (Fin 2) (GeneralLinearCoordinateRing.matrix T (Fin 2) 0 1)) =
        (a⁻¹).1 0 1 := by
    rw [hInverse, unitriangularGroupPoint_preimage_entry]
  have hIterated :
      (p⁻¹) ≫ (unitriangularGroupSchemeBaseChangeTowerIso R S T (Fin 2)).hom.hom.hom ≫
        ((Over.pullback (unitriangularBaseMap S T)).mapGrp.map
          (unitriangularGroupSchemeBaseChangeIso R S (Fin 2)).hom).hom.hom ≫
        (unitriangularGroupSchemeBaseChangeIso S T (Fin 2)).hom.hom.hom =
          unitriangularGroupMulEquivPoints T (Fin 2) U (a⁻¹) := by
    rw [unitriangularGroupSchemeBaseChangeIso_tower R S T (Fin 2)] at hInverse
    simpa only [Grp.comp_hom_hom, Over.comp_left, Category.assoc] using hInverse
  rw [hIterated, unitriangularGroupPoint_preimage_entry]
  exact hDirect

example (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (indices : Type u) [Fintype indices] [LinearOrder indices] :
    (unitriangularGroupSchemeBaseChangeIso R T indices).hom =
      (unitriangularGroupSchemeBaseChangeTowerIso R S T indices).hom ≫
        (Over.pullback (unitriangularBaseMap S T)).mapGrp.map
          (unitriangularGroupSchemeBaseChangeIso R S indices).hom ≫
        (unitriangularGroupSchemeBaseChangeIso S T indices).hom :=
  unitriangularGroupSchemeBaseChangeIso_tower R S T indices

example (R : Type u) [CommRing R]
    (indices : Type u) [Fintype indices] [LinearOrder indices] :
    (unitriangularGroupSchemeBaseChangeIso R R indices).hom =
      (unitriangularGroupSchemeBaseChangeSelfIso R indices).hom :=
  unitriangularGroupSchemeBaseChangeIso_self R indices

example :
    (unitriangularGroupSchemeBaseChangeIso (ZMod 1) (ZMod 1) (Fin 0)).hom =
      (unitriangularGroupSchemeBaseChangeSelfIso (ZMod 1) (Fin 0)).hom :=
  unitriangularGroupSchemeBaseChangeIso_self (ZMod 1) (Fin 0)

example :
    (unitriangularGroupSchemeBaseChangeIso (ZMod 1) (ZMod 1) (Fin 1)).hom =
      (unitriangularGroupSchemeBaseChangeSelfIso (ZMod 1) (Fin 1)).hom :=
  unitriangularGroupSchemeBaseChangeIso_self (ZMod 1) (Fin 1)
