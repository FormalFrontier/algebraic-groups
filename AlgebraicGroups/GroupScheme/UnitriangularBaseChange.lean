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

The affine fibre-product description is the published `Spec`-of-tensor-product
case of the Stacks Project. Milne describes the field-case `U_n` coordinate
presentation; the arbitrary-commutative-base group-object comparison uses
Mathlib's affine pullback and Hopf-algebra-to-group-scheme formalizations,
as well as Christian Merten's polynomial scalar-extension equivalence through
the coordinate-ring comparison. That equivalence is implemented using Yaël
Dillies's `AddMonoidAlgebra.scalarTensorEquiv`; Antoine Chambert-Loir provided
a related earlier polynomial scalar-extension equivalence.

## References

* James S. Milne, *Algebraic Groups* (2017), item 2.9 (the field-case `U_n`
  coordinate presentation).
* The Stacks Project, Section 26.17, Lemma 26.17.2 (affine fibre products).
* Andrew Yang, Mathlib, `Mathlib.AlgebraicGeometry.Pullbacks`
  (`pullbackSpecIso` and its projection laws).
* Yaël Dillies, Mathlib, `Mathlib.AlgebraicGeometry.Group.Affine`
  (`hopfSpec`, `algSpec`, `pullbackSpecIso'` and its monoid-homomorphism instance).
  Christian Merten, Michał Mrugała and Andrew Yang contributed to the wider
  affine group-scheme formalization.
* Antoine Chambert-Loir, Mathlib, `Mathlib.RingTheory.TensorProduct.MvPolynomial`
  (the related earlier `MvPolynomial.scalarRTensorAlgEquiv`).
* Christian Merten, Mathlib, `Mathlib.RingTheory.TensorProduct.MvPolynomial`
  (`MvPolynomial.algebraTensorAlgEquiv` used by the coordinate comparison).
* Yaël Dillies, Mathlib, `Mathlib.RingTheory.TensorProduct.MonoidAlgebra`
  (`AddMonoidAlgebra.scalarTensorEquiv` implementing the polynomial equivalence).
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
is the unitriangular group scheme over `S`, including at zero rings and empty indices.
The affine pullback uses the `Spec`-of-tensor-product antecedent in the Stacks
Project, Lemma 26.17.2, formalized by Mathlib's `pullbackSpecIso`; the Hopf
comparison ultimately uses Christian Merten's Mathlib
`MvPolynomial.algebraTensorAlgEquiv`, implemented using Yaël Dillies's
`AddMonoidAlgebra.scalarTensorEquiv`, with Antoine Chambert-Loir's
`MvPolynomial.scalarRTensorAlgEquiv` as a related earlier formalization.
Milne, *Algebraic Groups*, item 2.9 describes the underlying `U_n` coordinates
over a field, not this arbitrary-base group-object isomorphism. -/
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
