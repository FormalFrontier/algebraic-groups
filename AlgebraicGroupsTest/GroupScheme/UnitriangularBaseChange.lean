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
    (a b : Matrix.UnitriangularGroup (Fin 3) T)
    (p q : (Spec (.of T)).asOver (Spec (.of S)) ⟶
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp.obj
        (unitriangularGroupScheme R (Fin 3))).X)
    (hp : p ≫ (unitriangularGroupSchemeBaseChangeIso R S (Fin 3)).hom.hom.hom =
      unitriangularGroupMulEquivPoints S (Fin 3) T a)
    (hq : q ≫ (unitriangularGroupSchemeBaseChangeIso R S (Fin 3)).hom.hom.hom =
      unitriangularGroupMulEquivPoints S (Fin 3) T b) :
    (Spec.preimage (((p * q) ≫
      (unitriangularGroupSchemeBaseChangeIso R S (Fin 3)).hom.hom.hom).left)).hom
        (quotient S (Fin 3) (GeneralLinearCoordinateRing.matrix S (Fin 3) 0 2)) =
      a.1 0 2 + b.1 0 2 + a.1 0 1 * b.1 1 2 := by
  have hproduct : (p * q) ≫
        (unitriangularGroupSchemeBaseChangeIso R S (Fin 3)).hom.hom.hom =
      unitriangularGroupMulEquivPoints S (Fin 3) T (a * b) := by
    rw [MonObj.mul_comp, hp, hq, map_mul]
  rw [hproduct, unitriangularGroupPoint_preimage_entry]
  change ((a.1 : Matrix (Fin 3) (Fin 3) T) * (b.1 : Matrix (Fin 3) (Fin 3) T)) 0 2 = _
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  simp [a.2.2 0, b.2.2 2]
  ring

example (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (n : Type u) [Fintype n] [LinearOrder n] :
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp.obj
      (unitriangularGroupScheme R n)) ≅ unitriangularGroupScheme S n :=
  unitriangularGroupSchemeBaseChangeIso R S n

example :
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (ZMod 1) (ZMod 1))))).mapGrp.obj
      (unitriangularGroupScheme (ZMod 1) (Fin 0))) ≅
        unitriangularGroupScheme (ZMod 1) (Fin 0) :=
  unitriangularGroupSchemeBaseChangeIso (ZMod 1) (ZMod 1) (Fin 0)

example :
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (ZMod 1) (ZMod 1))))).mapGrp.obj
      (unitriangularGroupScheme (ZMod 1) (Fin 1))) ≅
        unitriangularGroupScheme (ZMod 1) (Fin 1) :=
  unitriangularGroupSchemeBaseChangeIso (ZMod 1) (ZMod 1) (Fin 1)
