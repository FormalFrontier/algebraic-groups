/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.UnitriangularHopfBaseChange
public import AlgebraicGroups.GroupScheme.Unitriangular
public import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# Base change of the unitriangular group scheme

Scalar extension of the native group object agrees with the group scheme
represented by the scalar-extended unitriangular Hopf algebra. The affine
pullback comparison uses its existing monoid-morphism instance; the Hopf
equivalence is the independently established coordinate-ring base change.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits UnitriangularCoordinateRing
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (ι : Type u) [Fintype ι] [LinearOrder ι]

/-- The native pullback of the unitriangular group scheme along `Spec S ⟶ Spec R`
is the unitriangular group scheme over `S`, including at zero rings and empty indices. -/
def unitriangularGroupSchemeBaseChangeIso :
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp.obj
      (unitriangularGroupScheme R ι)) ≅ unitriangularGroupScheme S ι := by
  letI : HopfAlgebra S (S ⊗[R] CoordinateRing R ι) := inferInstance
  let affine :
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp.obj
        (unitriangularGroupScheme R ι)).X ≅
          (Spec (.of (S ⊗[R] CoordinateRing R ι))).asOver
            (Spec (.of S)) :=
    Over.isoMk (pullbackSymmetry .. ≪≫
      pullbackSpecIso' R S (CoordinateRing R ι)) (by
        exact (inferInstance :
          (pullbackSymmetry .. ≪≫
            pullbackSpecIso' R S (CoordinateRing R ι)).hom.IsOver (Spec (.of S))).comp_over)
  let algebraIso : CommHopfAlgCat.of S (S ⊗[R] CoordinateRing R ι) ≅
      CommHopfAlgCat.of S (CoordinateRing S ι) :=
    CommHopfAlgCat.isoMk (baseChangeBialgEquiv R S ι)
  haveI : IsMonHom affine.hom := by
    change IsMonHom ((pullbackSymmetry .. ≪≫
      pullbackSpecIso' R S (CoordinateRing R ι)).hom.asOver (Spec (.of S)))
    infer_instance
  exact (Grp.mkIso' affine).trans ((hopfSpec (.of S)).mapIso algebraIso.symm.op)

/-- The forward scheme map is symmetry followed by the affine pullback comparison
and `Spec` of the *inverse* scalar-extension bialgebra map. -/
theorem unitriangularGroupSchemeBaseChangeIso_hom_left :
    (unitriangularGroupSchemeBaseChangeIso R S ι).hom.hom.hom.left =
      (pullbackSymmetry .. ≪≫ pullbackSpecIso' R S (CoordinateRing R ι)).hom ≫
        Spec.map (CommRingCat.ofHom
          (baseChangeBialgEquiv R S ι).symm.toBialgHom.toAlgHom.toRingHom) := by
  rfl

/-- The canonical comparison respects the projection to the new base. -/
theorem unitriangularGroupSchemeBaseChangeIso_hom_over :
    (unitriangularGroupSchemeBaseChangeIso R S ι).hom.hom.hom.left ≫
      Spec.map (CommRingCat.ofHom (algebraMap S (CoordinateRing S ι))) =
        pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap R (CoordinateRing R ι))))
          (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  exact (unitriangularGroupSchemeBaseChangeIso R S ι).hom.hom.hom.w

end AlgebraicGeometry
